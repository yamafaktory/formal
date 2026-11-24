from hypothesis import given, strategies as st


@given(st.lists(st.one_of(st.integers(-1000, 1000), st.integers(-2**52, 2**52)), min_size=1))
def test_property(load, data):
    ordered = sorted(data)
    n = len(ordered)
    middle = n // 2
    if n % 2 == 1:
        expected = ordered[middle]
    else:
        lower, upper = ordered[middle - 1], ordered[middle]
        expected = (lower + upper) / 2
    assert load("statistics.py").median(data) == expected
