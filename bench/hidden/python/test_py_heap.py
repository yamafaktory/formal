from hypothesis import given, strategies as st

operations = st.lists(st.one_of(st.integers(-20, 20), st.none()), max_size=40)


@given(operations)
def test_property(load, steps):
    heapq = load("heapq.py")
    heap, held = [], []
    for step in steps:
        if step is None:
            if held:
                smallest = min(held)
                held.remove(smallest)
                assert heapq.heappop(heap) == smallest
        else:
            heapq.heappush(heap, step)
            held.append(step)
