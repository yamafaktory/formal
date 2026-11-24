from hypothesis import given, strategies as st


@given(st.integers(-3000, 3000), st.integers(0, 900))
def test_property(load, y1, span):
    calendar = load("calendar.py")
    y2 = y1 + span
    expected = sum(1 for y in range(y1, y2) if calendar.isleap(y))
    assert calendar.leapdays(y1, y2) == expected
