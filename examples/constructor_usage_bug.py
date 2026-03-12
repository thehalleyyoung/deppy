class Counter:
    value: int

    def __init__(self, value: int) -> None:
        self.value = value

def takes_counter(counter: Counter) -> int:
    return counter.value

def bad() -> int:
    return takes_counter("not-a-counter")
