// libdivide.h - Optimized integer division
// https://libdivide.com
//
// Copyright (C) 2010 - 2021 ridiculous_fish, <libdivide@ridiculousfish.com>
// Copyright (C) 2016 - 2021 Kim Walisch, <kim.walisch@gmail.com>
//
// libdivide is dual-licensed under the Boost or zlib licenses.
// You may use libdivide under the terms of either of these.
// See LICENSE.txt for more details.

// Port from 4.0.0

use num_integer::Integer;
use num_traits::{PrimInt, Unsigned, WrappingShr};
use std::convert::TryInto;

#[repr(C, packed)]
pub struct Divider<T: PrimInt> {
    magic: T,
    more: u8,
}

#[repr(C, packed)]
pub struct BranchFreeDivider<T> {
    magic: T,
    more: u8,
}

// Explanation of the "more" field:
//
// * _BITS 0-5 is the shift value (for shift path or mult path).
// * Bit 6 is the add indicator for mult path.
// * Bit 7 is set if the divisor is negative. We use bit 7 as the negative
//   divisor indicator so that we can efficiently use sign extension to
//   create a bitmask with all _BITS set to 1 (if the divisor is negative)
//   or 0 (if the divisor is positive).
//
// u32: [0-4] shift value
//      [5] ignored
//      [6] add indicator
//      magic number of 0 indicates shift path
//
// s32: [0-4] shift value
//      [5] ignored
//      [6] add indicator
//      [7] indicates negative divisor
//      magic number of 0 indicates shift path
//
// u64: [0-5] shift value
//      [6] add indicator
//      magic number of 0 indicates shift path
//
// s64: [0-5] shift value
//      [6] add indicator
//      [7] indicates negative divisor
//      magic number of 0 indicates shift path
//
// In s32 and s64 branchfree modes, the magic number is negated according to
// whether the divisor is negated. In branchfree strategy, it is not negated.

const SHIFT_MASK_32: u8 = 0x1F;
const SHIFT_MASK_64: u8 = 0x3F;
const ADD_MARKER: u8 = 0x40;
const NEGATIVE_DIVISOR: u8 = 0x80;

#[derive(thiserror::Error, Debug)]
pub enum DividerError {
    #[error("divider must be != 0")]
    Zero,
    #[error("branchfree divider must be != 1")]
    BranchFreeOne,
}

pub trait DividerInt: PrimInt {
    const SHIFT_MASK: u8;
    const _BITS: u32; // TODO: rename to BITS after 1.53
    const SIGNED: bool;
    type Double: PrimInt + From<Self> + TryInto<Self>;
    type Unsigned: PrimInt + Unsigned;
    type UnsignedDouble: PrimInt + Unsigned;

    #[inline]
    fn mullhi(x: Self, y: Self) -> Self {
        let x = Self::Double::from(x);
        let y = Self::Double::from(y);
        let r = x * y;
        (r >> Self::_BITS as usize)
            .try_into()
            .unwrap_or_else(|_| unsafe { std::hint::unreachable_unchecked() })
    }
    fn internal_gen(self, branchfree: bool) -> Result<(Self, u8), DividerError>;
    fn gen(self) -> Result<Divider<Self>, DividerError> {
        let (magic, more) = self.internal_gen(false)?;
        Ok(Divider { magic, more })
    }
    fn branchfree_gen(self) -> Result<BranchFreeDivider<Self>, DividerError> {
        let (magic, more) = if Self::SIGNED {
            self.internal_gen(true)?
        } else {
            if self == Self::one() {
                return Err(DividerError::BranchFreeOne);
            }
            let (magic, more) = self.internal_gen(true)?;
            (magic, more & Self::SHIFT_MASK)
        };
        Ok(BranchFreeDivider { magic, more })
    }
    fn recover(denom: &Divider<Self>) -> Self;
    fn branchfree_recover(denom: &BranchFreeDivider<Self>) -> Self;

    fn unsigned_div_by(self, denom: &Divider<Self>) -> Self {
        let numer = self;
        let magic = denom.magic;
        let more = denom.more;
        if magic.is_zero() {
            numer.shr(more as usize)
        } else {
            let q = Self::mullhi(denom.magic, numer);
            if (more & ADD_MARKER) != 0 {
                let t = ((numer - q) >> 1) + q;
                t.shr((more & Self::SHIFT_MASK) as usize)
            } else {
                // All upper _BITS are 0,
                // don't need to mask them off.
                q.shr(more as usize)
            }
        }
    }

    fn unsigned_branchfree_div_by(self, denom: &BranchFreeDivider<Self>) -> Self
    where
        Self: WrappingShr,
    {
        let numer = self;
        let q = Self::mullhi(denom.magic, numer);
        let t = ((numer - q) >> 1) + q;
        t.wrapping_shr(denom.more as u32)
    }
}

impl DividerInt for u32 {
    const SHIFT_MASK: u8 = SHIFT_MASK_32;
    const _BITS: u32 = 32;
    const SIGNED: bool = false;
    type Double = u64;
    type Unsigned = Self;
    type UnsignedDouble = Self::Double;

    fn internal_gen(self, branchfree: bool) -> Result<(Self, u8), DividerError> {
        let d = self;
        if d == 0 {
            return Err(DividerError::Zero);
        }

        let floor_log_2_d = (Self::_BITS as u32 - 1) - d.leading_zeros();

        // Power of 2
        Ok(if (d & (d - 1)) == 0 {
            // We need to subtract 1 from the shift value in case of an unsigned
            // branchfree divider because there is a hardcoded right shift by 1
            // in its division algorithm. Because of this we also need to add back
            // 1 in its recovery algorithm.
            (0, (floor_log_2_d - u32::from(branchfree)) as u8)
        } else {
            let (proposed_m, rem) = (1u64 << (floor_log_2_d + 32)).div_rem(&(d as u64));
            let mut proposed_m = proposed_m as u32;
            let rem = rem as u32;
            assert!(rem > 0 && rem < d);

            let e = d - rem;

            // This power works if e < 2**floor_log_2_d.
            let more = if !branchfree && (e < (1 << floor_log_2_d)) {
                // This power works
                floor_log_2_d as u8
            } else {
                // We have to use the general 33-bit algorithm.  We need to compute
                // (2**power) / d. However, we already have (2**(power-1))/d and
                // its remainder.  By doubling both, and then correcting the
                // remainder, we can compute the larger division.
                // don't care about overflow here - in fact, we expect it
                proposed_m = proposed_m.wrapping_add(proposed_m);
                let twice_rem = rem.wrapping_add(rem);
                if twice_rem >= d || twice_rem < rem {
                    proposed_m += 1;
                }
                (floor_log_2_d as u8) | ADD_MARKER
            };
            (1 + proposed_m, more)
            // result.more's shift should in general be ceil_log_2_d. But if we
            // used the smaller power, we subtract one from the shift because we're
            // using the smaller power. If we're using the larger power, we
            // subtract one from the shift because it's taken care of by the add
            // indicator. So floor_log_2_d happens to be correct in both cases.
        })
    }

    fn recover(denom: &Divider<Self>) -> Self {
        let more = denom.more;
        let shift = more & Self::SHIFT_MASK;

        if 0 == denom.magic {
            1 << shift
        } else if 0 == (more & ADD_MARKER) {
            // We compute q = n/d = n*m / 2^(32 + shift)
            // Therefore we have d = 2^(32 + shift) / m
            // We need to ceil it.
            // We know d is not a power of 2, so m is not a power of 2,
            // so we can just add 1 to the floor
            let dividend: Self::Double = 1 << (shift as u32 + Self::_BITS);
            1 + (dividend / denom.magic as Self::Double) as Self
        } else {
            // Here we wish to compute d = 2^(32+shift+1)/(m+2^32).
            // Notice (m + 2^32) is a 33 bit number. Use 64 bit division for now
            // Also note that shift may be as high as 31, so shift + 1 will
            // overflow. So we have to compute it as 2^(32+shift)/(m+2^32), and
            // then double the quotient and remainder.
            let half_n: Self::Double = 1 << (32 + shift);
            let d = (1 << 32) | denom.magic as Self::Double;
            // Note that the quotient is guaranteed <= 32 _BITS, but the remainder
            // may need 33!
            let (half_q, rem) = half_n.div_rem(&d);
            let half_q = half_q as Self;
            // We computed 2^(32+shift)/(m+2^32)
            // Need to double it, and then add 1 to the quotient if doubling th
            // remainder would increase the quotient.
            // Note that rem<<1 cannot overflow, since rem < d and d is 33 _BITS
            let full_q = half_q + half_q + Self::from((rem << 1) >= d);

            // We rounded down in gen (hence +1)
            return full_q + 1;
        }
    }

    fn branchfree_recover(denom: &BranchFreeDivider<Self>) -> Self {
        let more = denom.more;
        let shift = more & Self::SHIFT_MASK;

        if 0 == denom.magic {
            1 << (shift + 1)
        } else {
            // Here we wish to compute d = 2^(32+shift+1)/(m+2^32).
            // Notice (m + 2^32) is a 33 bit number. Use 64 bit division for now
            // Also note that shift may be as high as 31, so shift + 1 will
            // overflow. So we have to compute it as 2^(32+shift)/(m+2^32), and
            // then double the quotient and remainder.
            let half_n: Self::Double = 1 << (Self::_BITS + shift as u32);
            let d = (1 << Self::_BITS) | denom.magic as Self::Double;
            // Note that the quotient is guaranteed <= 32 bits, but the remainder
            // may need 33!
            let (half_q, rem) = half_n.div_rem(&d);
            let half_q = half_q as Self;
            // We computed 2^(32+shift)/(m+2^32)
            // Need to double it, and then add 1 to the quotient if doubling th
            // remainder would increase the quotient.
            // Note that rem<<1 cannot overflow, since rem < d and d is 33 bits
            let full_q = half_q + half_q + Self::from((rem << 1) >= d);

            // We rounded down in gen (hence +1)
            return full_q + 1;
        }
    }
}

impl DividerInt for i32 {
    const SHIFT_MASK: u8 = SHIFT_MASK_32;
    const _BITS: u32 = 32;
    const SIGNED: bool = true;
    type Double = i64;
    type Unsigned = u32;
    type UnsignedDouble = u64;

    fn internal_gen(self, branchfree: bool) -> Result<(Self, u8), DividerError> {
        let d = self;

        if d == 0 {
            return Err(DividerError::Zero);
        }

        // If d is a power of 2, or negative a power of 2, we have to use a shift.
        // This is especially important because the magic algorithm fails for -1.
        // To check if d is a power of 2 or its inverse, it suffices to check
        // whether its absolute value has exactly one bit set. This works even for
        // INT_MIN, because abs(INT_MIN) == INT_MIN, and INT_MIN has one bit set
        // and is a power of 2.
        let abs_d = (if d < 0 { d.wrapping_neg() } else { d }) as Self::Unsigned;
        let floor_log_2_d = (Self::_BITS - 1) - abs_d.leading_zeros();
        // check if exactly one bit is set,
        // don't care if abs_d is 0 since that's divide by zero
        Ok(if (abs_d & (abs_d - 1)) == 0 {
            // Branchfree and normal paths are exactly the same
            (
                0,
                floor_log_2_d as u8 | if d < 0 { NEGATIVE_DIVISOR } else { 0 },
            )
        } else {
            assert!(floor_log_2_d >= 1);

            // the dividend here is 2**(floor_log_2_d + 31), so the low 32 bit word
            // is 0 and the high word is floor_log_2_d - 1
            let (proposed_m, rem) =
                (1u64 << (floor_log_2_d - 1 + Self::_BITS)).div_rem(&(abs_d as u64));
            let mut proposed_m = proposed_m as Self::Unsigned;
            let rem = rem as Self::Unsigned;
            let e = abs_d - rem;

            // We are going to start with a power of floor_log_2_d - 1.
            // This works if works if e < 2**floor_log_2_d.
            let mut more = if !branchfree && e < (1 << floor_log_2_d) {
                // This power works
                (floor_log_2_d - 1) as u8
            } else {
                // We need to go one higher. This should not make proposed_m
                // overflow, but it will make it negative when interpreted as an
                // int32_t.
                proposed_m = proposed_m.wrapping_add(proposed_m);
                let twice_rem = rem.wrapping_add(rem);
                if twice_rem >= abs_d || twice_rem < rem {
                    proposed_m += 1;
                }
                floor_log_2_d as u8 | ADD_MARKER
            };

            proposed_m += 1;
            let mut magic = proposed_m as Self;

            // Mark if we are negative. Note we only negate the magic number in the
            // branchfull case.
            if d < 0 {
                more |= NEGATIVE_DIVISOR;
                if !branchfree {
                    magic = -magic;
                }
            }
            (magic, more)
        })
    }

    fn recover(denom: &Divider<Self>) -> Self {
        let more = denom.more;
        let shift = more & Self::SHIFT_MASK;
        if 0 == denom.magic {
            let mut abs_d: Self = 1 << shift;
            if 0 != (more & NEGATIVE_DIVISOR) {
                abs_d = abs_d.wrapping_neg();
            }
            abs_d
        } else {
            // Unsigned math is much easier
            // We negate the magic number only in the branchfull case, and we don't
            // know which case we're in. However we have enough information to
            // determine the correct sign of the magic number. The divisor was
            // negative if LIBDIVIDE_NEGATIVE_DIVISOR is set. If ADD_MARKER is set,
            // the magic number's sign is opposite that of the divisor.
            // We want to compute the positive magic number.
            let negative_divisor = 0 != (more & NEGATIVE_DIVISOR);
            let magic_was_negated = if 0 != (more & ADD_MARKER) {
                denom.magic > 0
            } else {
                denom.magic < 0
            };

            // Handle the power of 2 case (including branchfree)
            let result = if denom.magic == 0 {
                1 << shift
            } else {
                let d = (if magic_was_negated {
                    -denom.magic
                } else {
                    denom.magic
                }) as Self::Unsigned;
                let n = 1u64 << (32 + shift); // this shift cannot exceed 30
                let q = (n / d as u64) as Self::Unsigned;
                q as Self + 1
            };
            if negative_divisor {
                -result
            } else {
                result
            }
        }
    }

    fn branchfree_recover(denom: &BranchFreeDivider<Self>) -> Self {
        Self::recover(unsafe { &*(denom as *const _ as *const Divider<Self>) })
    }
}

impl DividerInt for u64 {
    const SHIFT_MASK: u8 = SHIFT_MASK_64;
    const _BITS: u32 = 64;
    const SIGNED: bool = false;
    type Double = u128;
    type Unsigned = Self;
    type UnsignedDouble = Self::Double;

    fn internal_gen(self, branchfree: bool) -> Result<(Self, u8), DividerError> {
        let d = self;

        if d == 0 {
            return Err(DividerError::Zero);
        }
        let floor_log_2_d: u32 = 63 - d.leading_zeros();

        // Power of 2
        Ok(if (d & (d - 1)) == 0 {
            // We need to subtract 1 from the shift value in case of an unsigned
            // branchfree divider because there is a hardcoded right shift by 1
            // in its division algorithm. Because of this we also need to add back
            // 1 in its recovery algorithm.
            (0, (floor_log_2_d - u32::from(branchfree)) as u8)
        } else {
            // (1 << (64 + floor_log_2_d)) / d
            let (proposed_m, rem) = (1u128 << (floor_log_2_d + 64)).div_rem(&(d as u128));
            let mut proposed_m = proposed_m as u64;
            let rem = rem as u64;
            assert!(rem > 0 && rem < d);

            let e = d - rem;

            // This power works if e < 2**floor_log_2_d.
            let more = if !branchfree && e < (1 << floor_log_2_d) {
                // This power works
                floor_log_2_d as u8
            } else {
                // We have to use the general 65-bit algorithm.  We need to compute
                // (2**power) / d. However, we already have (2**(power-1))/d and
                // its remainder. By doubling both, and then correcting the
                // remainder, we can compute the larger division.
                // don't care about overflow here - in fact, we expect it
                proposed_m = proposed_m.wrapping_add(proposed_m);
                let twice_rem = rem.wrapping_add(rem);
                if twice_rem >= d || twice_rem < rem {
                    proposed_m += 1;
                }
                (floor_log_2_d as u8) | ADD_MARKER
            };

            (1 + proposed_m, more)
            // result.more's shift should in general be ceil_log_2_d. But if we
            // used the smaller power, we subtract one from the shift because we're
            // using the smaller power. If we're using the larger power, we
            // subtract one from the shift because it's taken care of by the add
            // indicator. So floor_log_2_d happens to be correct in both cases,
            // which is why we do it outside of the if statement.
        })
    }

    fn recover(denom: &Divider<Self>) -> Self {
        let more = denom.more;
        let shift = more & Self::SHIFT_MASK;

        if 0 == denom.magic {
            1 << shift
        } else if 0 == (more & ADD_MARKER) {
            // We compute q = n/d = n*m / 2^(64 + shift)
            // Therefore we have d = 2^(64 + shift) / m
            // We need to ceil it.
            // We know d is not a power of 2, so m is not a power of 2,
            // so we can just add 1 to the floor
            let dividend = 1u128 << (shift + 64);
            1 + (dividend / denom.magic as u128) as u64
        } else {
            // Here we wish to compute d = 2^(64+shift+1)/(m+2^64).
            // Notice (m + 2^64) is a 65 bit number. This gets hairy. See
            // libdivide_u32_recover for more on what we do here.
            // TODO: do something better than 128 bit math

            // Full n is a (potentially) 129 bit value
            // half_n is a 128 bit value
            // Compute the hi half of half_n. Low half is 0.
            let half_n = 1u128 << (shift + 64);
            // d is a 65 bit value. The high bit is always set to 1.
            let d = (1 << 64) | denom.magic as u128;
            // Note that the quotient is guaranteed <= 64 _BITS,
            // but the remainder may need 65!
            let (half_q, r) = half_n.div_rem(&d);
            let half_q = half_q as u64;
            // We computed 2^(64+shift)/(m+2^64)
            // Double the remainder ('dr') and check if that is larger than d
            // Note that d is a 65 bit value, so r1 is small and so r1 + r1
            // cannot overflow
            let dr = r.wrapping_add(r);
            let dr_exceeds_d = dr > d;
            let full_q = half_q + half_q + u64::from(dr_exceeds_d);
            full_q + 1
        }
    }

    fn branchfree_recover(denom: &BranchFreeDivider<Self>) -> Self {
        let more = denom.more;
        let shift = more & Self::SHIFT_MASK;
        if denom.magic == 0 {
            1 << (shift + 1)
        } else {
            // Here we wish to compute d = 2^(64+shift+1)/(m+2^64).
            // Notice (m + 2^64) is a 65 bit number. This gets hairy. See
            // libdivide_u32_recover for more on what we do here.
            // TODO: do something better than 128 bit math

            // Full n is a (potentially) 129 bit value
            // half_n is a 128 bit value
            // Compute the hi half of half_n. Low half is 0.
            let half_n = 1u128 << (shift + 64);
            // d is a 65 bit value. The high bit is always set to 1.
            let d = (1 << 64) + denom.magic as u128;
            // Note that the quotient is guaranteed <= 64 _BITS,
            // but the remainder may need 65!
            let (half_q, r) = half_n.div_rem(&d);
            let half_q = half_q as u64;
            // We computed 2^(64+shift)/(m+2^64)
            // Double the remainder ('dr') and check if that is larger than d
            // Note that d is a 65 bit value, so r1 is small and so r1 + r1
            // cannot overflow
            let dr = r.wrapping_add(r);
            let dr_exceeds_d = dr > d;
            let full_q = half_q + half_q + u64::from(dr_exceeds_d);
            full_q + 1
        }
    }
}

impl DividerInt for i64 {
    const SHIFT_MASK: u8 = SHIFT_MASK_64;
    const _BITS: u32 = 64;
    const SIGNED: bool = true;
    type Double = i128;
    type Unsigned = u64;
    type UnsignedDouble = u128;

    fn internal_gen(self, branchfree: bool) -> Result<(Self, u8), DividerError> {
        let d = self;

        if d == 0 {
            return Err(DividerError::Zero);
        }

        // If d is a power of 2, or negative a power of 2, we have to use a shift.
        // This is especially important because the magic algorithm fails for -1.
        // To check if d is a power of 2 or its inverse, it suffices to check
        // whether its absolute value has exactly one bit set. This works even for
        // INT_MIN, because abs(INT_MIN) == INT_MIN, and INT_MIN has one bit set
        // and is a power of 2.
        let abs_d = (if d < 0 { d.wrapping_neg() } else { d }) as Self::Unsigned;
        let floor_log_2_d = (Self::_BITS - 1) - abs_d.leading_zeros();
        // check if exactly one bit is set,
        // don't care if abs_d is 0 since that's divide by zero
        Ok(if (abs_d & (abs_d - 1)) == 0 {
            // Branchfree and normal paths are exactly the same
            (
                0,
                floor_log_2_d as u8 | if d < 0 { NEGATIVE_DIVISOR } else { 0 },
            )
        } else {
            assert!(floor_log_2_d >= 1);

            // the dividend here is 2**(floor_log_2_d + 31), so the low 32 bit word
            // is 0 and the high word is floor_log_2_d - 1
            let (proposed_m, rem) =
                (1u128 << (floor_log_2_d - 1 + Self::_BITS)).div_rem(&(abs_d as u128));
            let mut proposed_m = proposed_m as Self::Unsigned;
            let rem = rem as Self::Unsigned;
            let e = abs_d - rem;

            // We are going to start with a power of floor_log_2_d - 1.
            // This works if works if e < 2**floor_log_2_d.
            let mut more = if !branchfree && e < (1 << floor_log_2_d) {
                // This power works
                (floor_log_2_d - 1) as u8
            } else {
                // We need to go one higher. This should not make proposed_m
                // overflow, but it will make it negative when interpreted as an
                // int32_t.
                proposed_m = proposed_m.wrapping_add(proposed_m);
                let twice_rem = rem.wrapping_add(rem);
                if twice_rem >= abs_d || twice_rem < rem {
                    proposed_m += 1;
                }
                floor_log_2_d as u8 | ADD_MARKER
            };

            proposed_m += 1;
            let mut magic = proposed_m as Self;

            // Mark if we are negative. Note we only negate the magic number in the
            // branchfull case.
            if d < 0 {
                more |= NEGATIVE_DIVISOR;
                if !branchfree {
                    magic = -magic;
                }
            }
            (magic, more)
        })
    }

    fn recover(denom: &Divider<Self>) -> Self {
        let more = denom.more;
        let shift = more & Self::SHIFT_MASK;
        if 0 == denom.magic {
            let mut abs_d = 1i64 << shift;
            if 0 != (more & NEGATIVE_DIVISOR) {
                abs_d = abs_d.wrapping_neg();
            }
            abs_d
        } else {
            // Unsigned math is much easier
            let negative_divisor = 0 != (more & NEGATIVE_DIVISOR);
            let magic_was_negated = if 0 != (more & ADD_MARKER) {
                denom.magic > 0
            } else {
                denom.magic < 0
            };

            let d = if magic_was_negated {
                -denom.magic
            } else {
                denom.magic
            } as Self::Unsigned;
            let n = 1u128 << (shift as u32 + Self::_BITS);
            let q = (n / d as u128) as u64;
            let mut result = (q + 1) as Self;
            if negative_divisor {
                result = -result;
            }
            result
        }
    }

    fn branchfree_recover(denom: &BranchFreeDivider<Self>) -> Self {
        Self::recover(unsafe { &*(denom as *const _ as *const Divider<Self>) })
    }
}

impl<T: DividerInt> From<T> for Divider<T> {
    fn from(d: T) -> Self {
        d.gen().unwrap()
    }
}

impl<T: DividerInt> Divider<T> {
    pub fn new(d: T) -> Result<Self, DividerError> {
        d.gen()
    }

    pub fn recover(&self) -> T {
        T::recover(self)
    }
}

impl<T: DividerInt> From<T> for BranchFreeDivider<T> {
    fn from(d: T) -> Self {
        d.branchfree_gen().unwrap()
    }
}

impl<T: DividerInt> BranchFreeDivider<T> {
    pub fn new(d: T) -> Result<Self, DividerError> {
        d.branchfree_gen()
    }

    pub fn recover(&self) -> T {
        T::branchfree_recover(self)
    }
}

impl std::ops::Div<&Divider<Self>> for u32 {
    type Output = Self;

    fn div(self, denom: &Divider<Self>) -> Self::Output {
        self.unsigned_div_by(denom)
    }
}

impl std::ops::Div<&BranchFreeDivider<Self>> for u32 {
    type Output = Self;

    fn div(self, denom: &BranchFreeDivider<Self>) -> Self::Output {
        self.unsigned_branchfree_div_by(denom)
    }
}

impl std::ops::Div<&Divider<Self>> for i32 {
    type Output = Self;

    fn div(self, denom: &Divider<Self>) -> Self::Output {
        let numer = self;
        let more = denom.more;
        let shift = more & Self::SHIFT_MASK;

        if 0 == denom.magic {
            let sign = (more as i8 >> 7) as u32;
            let mask = (1u32 << shift) - 1;
            let uq = (numer as u32).wrapping_add((numer >> 31) as u32 & mask);
            let mut q = uq as Self;
            q >>= shift;
            q = (q as u32 ^ sign).wrapping_sub(sign) as Self;
            q
        } else {
            let mut uq = Self::mullhi(denom.magic, numer) as u32;
            if 0 != (more & ADD_MARKER) {
                // must be arithmetic shift and then sign extend
                let sign = (more as i8 >> 7) as Self;
                // q += (more < 0 ? -numer : numer)
                // cast required to avoid UB
                uq = uq.wrapping_add(((numer as u32) ^ (sign as u32)).wrapping_sub(sign as u32));
            }
            let mut q = uq as Self;
            q >>= shift;
            q += Self::from(q < 0);
            q
        }
    }
}

impl std::ops::Div<&BranchFreeDivider<Self>> for i32 {
    type Output = Self;

    fn div(self, denom: &BranchFreeDivider<Self>) -> Self::Output {
        let numer = self;
        let more = denom.more;
        let shift = more & Self::SHIFT_MASK;
        // must be arithmetic shift and then sign extend
        let sign = (more as i8 >> 7) as Self;
        let magic = denom.magic;
        let mut q = Self::mullhi(magic, numer);
        q += numer;

        // If q is non-negative, we have nothing to do
        // If q is negative, we want to add either (2**shift)-1 if d is a power of
        // 2, or (2**shift) if it is not a power of 2
        let is_power_of_2 = u32::from(magic == 0);
        let q_sign = (q >> 31) as u32;
        q += (q_sign & ((1 << shift) - is_power_of_2)) as Self;

        // Now arithmetic right shift
        q >>= shift;
        // Negate if needed
        q = (q ^ sign).wrapping_sub(sign);

        return q;
    }
}

impl std::ops::Div<&Divider<Self>> for u64 {
    type Output = Self;

    fn div(self, denom: &Divider<Self>) -> Self::Output {
        self.unsigned_div_by(denom)
    }
}

impl std::ops::Div<&BranchFreeDivider<Self>> for u64 {
    type Output = Self;

    fn div(self, denom: &BranchFreeDivider<Self>) -> Self::Output {
        self.unsigned_branchfree_div_by(denom)
    }
}

impl std::ops::Div<&Divider<Self>> for i64 {
    type Output = Self;

    fn div(self, denom: &Divider<Self>) -> Self::Output {
        let numer = self;
        let more = denom.more;
        let shift = more & Self::SHIFT_MASK;

        if 0 == denom.magic {
            let sign = (more as i8 >> 7) as u64;
            let mask = (1u64 << shift) - 1;
            let uq = (numer as u64).wrapping_add((numer >> 63) as u64 & mask);
            let mut q = uq as Self;
            q >>= shift;
            q = (q as u64 ^ sign).wrapping_sub(sign) as Self;
            q
        } else {
            let mut uq = Self::mullhi(denom.magic, numer) as u64;
            if 0 != (more & ADD_MARKER) {
                // must be arithmetic shift and then sign extend
                let sign = (more as i8 >> 7) as Self;
                // q += (more < 0 ? -numer : numer)
                // cast required to avoid UB
                uq = uq.wrapping_add(((numer as u64) ^ (sign as u64)).wrapping_sub(sign as u64));
            }
            let mut q = uq as Self;
            q >>= shift;
            q += Self::from(q < 0);
            q
        }
    }
}

impl std::ops::Div<&BranchFreeDivider<Self>> for i64 {
    type Output = Self;

    fn div(self, denom: &BranchFreeDivider<Self>) -> Self::Output {
        let numer = self;
        let more = denom.more;
        let shift = more & Self::SHIFT_MASK;
        // must be arithmetic shift and then sign extend
        let sign = (more as i8 >> 7) as Self;
        let magic = denom.magic;
        let mut q = Self::mullhi(magic, numer);
        q += numer;

        // If q is non-negative, we have nothing to do
        // If q is negative, we want to add either (2**shift)-1 if d is a power of
        // 2, or (2**shift) if it is not a power of 2
        let is_power_of_2 = u64::from(magic == 0);
        let q_sign = (q >> 63) as u64;
        q += (q_sign & ((1 << shift) - is_power_of_2)) as Self;

        // Now arithmetic right shift
        q >>= shift;
        // Negate if needed
        q = (q ^ sign).wrapping_sub(sign);

        return q;
    }
}
