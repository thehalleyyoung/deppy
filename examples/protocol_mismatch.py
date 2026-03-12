from typing import Protocol

class Reader(Protocol):
    def read(self) -> int:
        ...

class Box:
    def read(self) -> str:
        return "oops"

def consume(r: Reader) -> int:
    return r.read()

def bad(box: Box) -> int:
    return consume(box)
