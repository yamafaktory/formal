use num_integer::Roots;
use proptest::prelude::*;

fn is_root(n: u128, r: u128) -> bool {
    let below = r.checked_mul(r).is_some_and(|square| square <= n);
    let above = (r + 1).checked_mul(r + 1).is_none_or(|square| n < square);
    below && above
}

proptest! {
    #[test]
    fn property(n in any::<u128>()) {
        prop_assert!(is_root(n, n.sqrt()));
    }

    #[test]
    fn around_squares(k in (1u128 << 32)..=(u64::MAX as u128), offset in 0u128..3) {
        let n = k * k + offset - 1;
        prop_assert!(is_root(n, n.sqrt()));
    }

    #[test]
    fn small(n in 0u128..10_000) {
        prop_assert!(is_root(n, n.sqrt()));
    }
}
