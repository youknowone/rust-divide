use libdivide::{BranchFreeDivider, Divider, DividerError};
use proptest::prelude::*;

// Property test for u32 Divider
proptest! {
    #[test]
    fn test_u32_divider_vs_naive(dividend in any::<u32>(), divisor in 1..=u32::MAX) {
        let divider = Divider::<u32>::new(divisor).unwrap();
        let optimized_result = dividend / &divider;
        let naive_result = dividend / divisor;
        prop_assert_eq!(optimized_result, naive_result);
    }

    #[test]
    fn test_u32_branchfree_divider_vs_naive(dividend in any::<u32>(), divisor in 2..=u32::MAX) {
        // BranchFreeDivider cannot handle divisor = 1
        let branchfree_divider = BranchFreeDivider::<u32>::new(divisor).unwrap();
        let optimized_result = dividend / &branchfree_divider;
        let naive_result = dividend / divisor;
        prop_assert_eq!(optimized_result, naive_result);
    }

    #[test]
    fn test_i32_divider_vs_naive(dividend in any::<i32>(), divisor in i32::MIN..=i32::MAX) {
        prop_assume!(divisor != 0);
        let divider = match Divider::<i32>::new(divisor) {
            Ok(d) => d,
            Err(_) => return Ok(()),
        };
        let optimized_result = dividend / &divider;
        let naive_result = dividend / divisor;
        prop_assert_eq!(optimized_result, naive_result);
    }

    #[test]
    fn test_i32_branchfree_divider_vs_naive(dividend in any::<i32>(), divisor in i32::MIN..=i32::MAX) {
        prop_assume!(divisor != 0);
        let branchfree_divider = BranchFreeDivider::<i32>::new(divisor).unwrap();
        let optimized_result = dividend / &branchfree_divider;
        let naive_result = dividend / divisor;
        prop_assert_eq!(optimized_result, naive_result);
    }

    #[test]
    fn test_u64_divider_vs_naive(dividend in any::<u64>(), divisor in 1..=u64::MAX) {
        let divider = Divider::<u64>::new(divisor).unwrap();
        let optimized_result = dividend / &divider;
        let naive_result = dividend / divisor;
        prop_assert_eq!(optimized_result, naive_result);
    }

    #[test]
    fn test_u64_branchfree_divider_vs_naive(dividend in any::<u64>(), divisor in 2..=u64::MAX) {
        // BranchFreeDivider cannot handle divisor = 1
        let branchfree_divider = BranchFreeDivider::<u64>::new(divisor).unwrap();
        let optimized_result = dividend / &branchfree_divider;
        let naive_result = dividend / divisor;
        prop_assert_eq!(optimized_result, naive_result);
    }

    #[test]
    fn test_i64_divider_vs_naive(dividend in any::<i64>(), divisor in i64::MIN..=i64::MAX) {
        prop_assume!(divisor != 0);
        let divider = match Divider::<i64>::new(divisor) {
            Ok(d) => d,
            Err(_) => return Ok(()),
        };
        let optimized_result = dividend / &divider;
        let naive_result = dividend / divisor;
        prop_assert_eq!(optimized_result, naive_result);
    }

    #[test]
    fn test_i64_branchfree_divider_vs_naive(dividend in any::<i64>(), divisor in i64::MIN..=i64::MAX) {
        prop_assume!(divisor != 0);
        let branchfree_divider = BranchFreeDivider::<i64>::new(divisor).unwrap();
        let optimized_result = dividend / &branchfree_divider;
        let naive_result = dividend / divisor;
        prop_assert_eq!(optimized_result, naive_result);
    }

    #[test]
    fn test_u32_recover(divisor in 1u32..=u32::MAX) {
        let d = Divider::<u32>::new(divisor).unwrap();
        prop_assert_eq!(d.recover(), divisor);
        let bf = BranchFreeDivider::<u32>::new(divisor).unwrap();
        prop_assert_eq!(bf.recover(), divisor);
    }
}

mod edge_case_tests {
    use super::*;

    #[test]
    fn test_divider_error_zero() {
        assert!(matches!(Divider::<u32>::new(0), Err(DividerError::Zero)));
        assert!(matches!(Divider::<i32>::new(0), Err(DividerError::Zero)));
        assert!(matches!(Divider::<u64>::new(0), Err(DividerError::Zero)));
        assert!(matches!(Divider::<i64>::new(0), Err(DividerError::Zero)));
    }

    #[test]
    fn test_branchfree_divider_error_one() {
        assert!(matches!(
            BranchFreeDivider::<u32>::new(1),
            Err(DividerError::BranchFreeOne)
        ));
        assert!(matches!(
            BranchFreeDivider::<u64>::new(1),
            Err(DividerError::BranchFreeOne)
        ));
        // i32 and i64 BranchFreeDivider can handle 1
        assert!(BranchFreeDivider::<i32>::new(1).is_ok());
        assert!(BranchFreeDivider::<i64>::new(1).is_ok());
    }

    #[test]
    fn test_power_of_two_divisors() {
        // Test various powers of 2
        for shift in 1..=31 {
            let divisor = 1u32 << shift;
            let divider = Divider::<u32>::new(divisor).unwrap();
            let branchfree_divider = BranchFreeDivider::<u32>::new(divisor).unwrap();

            for dividend in [0, 1, divisor - 1, divisor, divisor + 1, u32::MAX] {
                assert_eq!(dividend / &divider, dividend / divisor);
                assert_eq!(dividend / &branchfree_divider, dividend / divisor);
            }
        }
    }

    #[test]
    fn test_min_max_values() {
        // Test with extreme values
        let test_cases = [
            (u32::MAX, u32::MAX),
            (u32::MAX - 1, u32::MAX),
            (0, u32::MAX),
            (1, u32::MAX),
        ];

        for (dividend, divisor) in test_cases {
            let divider = Divider::<u32>::new(divisor).unwrap();
            let branchfree_divider = BranchFreeDivider::<u32>::new(divisor).unwrap();

            assert_eq!(dividend / &divider, dividend / divisor);
            assert_eq!(dividend / &branchfree_divider, dividend / divisor);
        }
    }
}
