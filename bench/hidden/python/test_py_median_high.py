from hypothesis import given, strategies as st


@given(st.lists(st.integers(-1000, 1000), min_size=1))
def test_property(load, data):
    ordered = sorted(data)
    n = len(ordered)
    middle = n // 2
    if n % 2 == 1:
        expected = ordered[middle]
    else:
        lower, upper = ordered[middle - 1], ordered[middle]
        expected = upper
    assert load("statistics.py").median_high(data) == expected
