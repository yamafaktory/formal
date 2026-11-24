use num_integer::binomial;
use proptest::prelude::*;

fn pascal(n: u64, k: u64) -> u128 {
    if k > n {
        return 0;
    }
    let mut row = vec![1u128];
    for _ in 0..n {
        let mut next = vec![1u128; row.len() + 1];
        for i in 1..row.len() {
            next[i] = row[i - 1] + row[i];
        }
        row = next;
    }
    row[usize::try_from(k).expect("k fits")]
}

proptest! {
    #[test]
    fn property(n in 0u64..=60, k in 0u64..=70) {
        prop_assert_eq!(u128::from(binomial(n, k)), pascal(n, k));
    }
}
