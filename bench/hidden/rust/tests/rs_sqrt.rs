use num_integer::Roots;
use proptest::prelude::*;

fn holds(n: u64) -> bool {
    let r = u128::from(n.sqrt());
    let n = u128::from(n);
    r * r <= n && n < (r + 1) * (r + 1)
}

proptest! {
    #[test]
    fn property(n in any::<u64>()) {
        prop_assert!(holds(n));
    }

    #[test]
    fn near_squares(r in 0u64..=u64::from(u32::MAX), d in 0u64..3) {
        let square = r * r;
        prop_assert!(holds(square));
        prop_assert!(holds(square.saturating_add(d)));
        prop_assert!(holds(square.saturating_sub(d)));
    }
}
