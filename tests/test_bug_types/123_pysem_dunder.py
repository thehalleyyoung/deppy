"""Python semantics: dunder methods — INDEX_OOB, KEY_ERROR, TYPE_ERROR."""

BUG_TYPE = "INDEX_OOB"
BUG_DESC = "Custom __getitem__ with unchecked bounds"

EXAMPLES = [
    (
        "custom_getitem_oob",
        # buggy: custom container, no bounds check in usage
        '''\
class Ring:
    def __init__(self, items):
        self._items = items
    def __getitem__(self, idx):
        return self._items[idx]
    def __len__(self):
        return len(self._items)

def access(r):
    data = list(r._items)
    return data[len(data)]
''',
        # safe: guard non-empty + last valid index
        '''\
class Ring:
    def __init__(self, items):
        self._items = items
    def __getitem__(self, idx):
        return self._items[idx % len(self._items)]
    def __len__(self):
        return len(self._items)

def access(r):
    data = list(r._items)
    if data:
        return data[len(data) - 1]
    return None
''',
        "data[len(data)] is always OOB",
    ),
    (
        "iter_protocol_oob",
        # buggy: manual iteration past end
        '''\
class Countdown:
    def __init__(self, start):
        self.n = start
    def __iter__(self):
        return self
    def __next__(self):
        if self.n <= 0:
            raise StopIteration
        self.n -= 1
        return self.n

def collect(start):
    c = Countdown(start)
    items = list(c)
    return items[start]
''',
        # safe: guard non-empty + access valid index
        '''\
class Countdown:
    def __init__(self, start):
        self.n = start
    def __iter__(self):
        return self
    def __next__(self):
        if self.n <= 0:
            raise StopIteration
        self.n -= 1
        return self.n

def collect(start):
    c = Countdown(start)
    items = list(c)
    if items:
        return items[start - 1]
    return None
''',
        "Countdown yields start items; items[start] is OOB",
    ),
    (
        "contains_no_protect",
        # buggy: __contains__ doesn't guard index access
        '''\
class SortedList:
    def __init__(self, data):
        self.data = sorted(data)
    def __contains__(self, item):
        return item in self.data

def first_and_last(items):
    sl = SortedList(items)
    data = sl.data
    return data[len(data)]
''',
        # safe: proper index
        '''\
class SortedList:
    def __init__(self, data):
        self.data = sorted(data)
    def __contains__(self, item):
        return item in self.data

def first_and_last(items):
    sl = SortedList(items)
    data = sl.data
    if len(data) > 0:
        return data[len(data) - 1]
    return None
''',
        "data[len(data)] is OOB",
    ),
]
