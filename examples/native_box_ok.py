class Box:
    value: int

    def __init__(self, value: int) -> None:
        self.value = value

    def get(self) -> int:
        return self.value
