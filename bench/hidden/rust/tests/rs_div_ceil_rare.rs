use num_integer::Integer;
use proptest::prelude::*;

fn ceil(a: i128, b: i128) -> i128 {
    let q = a / b;
    if (a % b != 0) && ((a < 0) == (b < 0)) { q + 1 } else { q }
}

proptest! {
    #[test]
    fn property(a in any::<i64>(), b in any::<i64>().prop_filter("b != 0", |b| *b != 0)) {
        prop_assume!(!(a == i64::MIN && b == -1));
        prop_assert_eq!(i128::from(Integer::div_ceil(&a, &b)), ceil(a.into(), b.into()));
    }

    #[test]
    fn small(a in -50i64..50, b in (-9i64..9).prop_filter("b != 0", |b| *b != 0)) {
        prop_assert_eq!(i128::from(Integer::div_ceil(&a, &b)), ceil(a.into(), b.into()));
    }

    #[test]
    fn extremes(a in prop_oneof![Just(i64::MIN), Just(i64::MIN + 1), Just(i64::MAX)], b in any::<i64>().prop_filter("b != 0", |b| *b != 0)) {
        prop_assume!(!(a == i64::MIN && b == -1));
        prop_assert_eq!(i128::from(Integer::div_ceil(&a, &b)), ceil(a.into(), b.into()));
    }
}
