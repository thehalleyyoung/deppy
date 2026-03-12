from typing import Protocol


class Reader(Protocol):
    def read(self) -> int:
        ...


class CachingReader:
    cached: int

    def __init__(self, value: int, replay: bool) -> None:
        current = value
        self.cached = current
        if replay:
            self.cached = "stale"
        self.shadow = current

    def read(self) -> str:
        return self.cached


def consume(reader: Reader) -> int:
    return reader.read()


def bad(flag: bool) -> int:
    reader = CachingReader(0, flag)
    return consume(reader)
