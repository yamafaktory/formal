use num_integer::Integer;
use proptest::prelude::*;

const BOUND: i64 = 1 << 62;

fn euclid(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

proptest! {
    #[test]
    fn property(a in -BOUND + 1..BOUND, b in -BOUND + 1..BOUND) {
        prop_assert_eq!(i128::from(a.gcd(&b)), euclid(a.into(), b.into()));
    }

    #[test]
    fn small(a in -30i64..30, b in -30i64..30) {
        prop_assert_eq!(i128::from(a.gcd(&b)), euclid(a.into(), b.into()));
    }
}
