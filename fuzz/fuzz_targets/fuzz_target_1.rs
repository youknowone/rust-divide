#![no_main]
use libfuzzer_sys::fuzz_target;
use libdivide::{Divider, BranchFreeDivider};

fuzz_target!(|items: Vec<u64>| {
    // fuzzed code goes here
    // println!("items: {:?}", &items);
    let d = items[0];
    macro_rules! run {
        ($num_type:ty) => {{
            let d = d as $num_type;
            if let Ok(divider) = Divider::new(d) {
                assert_eq!(divider.recover(), d);
                for item in items.iter() {
                    let item = *item as $num_type;
                    if <$num_type>::MIN != 0 && item == <$num_type>::MIN && d == -1 {
                        continue; // divide with overflow
                    }
                    // println!("{} {}", item, d);
                    assert_eq!(item / &divider, item / d, "branchfull {} {} / {}", stringify!($num_type), item, d);
                }
            }
            if let Ok(divider) = BranchFreeDivider::new(d) {
                assert_eq!(divider.recover(), d);
                for item in items.iter() {
                    let item = *item as $num_type;
                    if <$num_type>::MIN != 0 && item == <$num_type>::MIN && d == -1 {
                        continue; // divide with overflow
                    }
                    assert_eq!(item / &divider, item / d, "branchless {} {} / {}", stringify!($num_type), item, d);
                }
            }
        }}
    }
    // run!(u64);
    run!(i64);
    // run!(u32);
    run!(i32);
});
