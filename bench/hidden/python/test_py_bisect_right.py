from hypothesis import given, strategies as st


@given(st.lists(st.integers(-20, 20)), st.integers(-25, 25))
def test_property(load, a, x):
    a = sorted(a)
    i = load("bisect.py").bisect_right(a, x)
    assert all(e <= x for e in a[:i])
    assert all(e > x for e in a[i:])
