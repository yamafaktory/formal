use num_integer::Integer;
use proptest::prelude::*;

const BOUND: i64 = 1 << 31;

fn euclid(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

fn lcm(a: i128, b: i128) -> i128 {
    if a == 0 || b == 0 { 0 } else { (a * b).abs() / euclid(a, b) }
}

proptest! {
    #[test]
    fn property(a in -BOUND + 1..BOUND, b in -BOUND + 1..BOUND) {
        prop_assert_eq!(i128::from(a.lcm(&b)), lcm(a.into(), b.into()));
    }

    #[test]
    fn small(a in -30i64..30, b in -30i64..30) {
        prop_assert_eq!(i128::from(a.lcm(&b)), lcm(a.into(), b.into()));
    }
}
