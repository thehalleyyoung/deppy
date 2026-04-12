"""Interpretation of Python io module in the motive framework."""

from __future__ import annotations

from deppy.motive.sorts import Sort
from deppy.motive.operations import Effect, Refinement

IO_OPS = {
    # StringIO
    'StringIO': ('IO.string_buffer', (), Sort.TOP, frozenset(), Effect.ALLOCATE),
    'BytesIO': ('IO.bytes_buffer', (), Sort.TOP, frozenset(), Effect.ALLOCATE),

    # Reading
    'read': ('IO.read', (Sort.TOP,), Sort.STR, frozenset(), Effect.IO),
    'readline': ('IO.readline', (Sort.TOP,), Sort.STR, frozenset(), Effect.IO),
    'readlines': ('IO.readlines', (Sort.TOP,), Sort.SEQ, frozenset(), Effect.IO),

    # Writing
    'write': ('IO.write', (Sort.TOP, Sort.STR), Sort.NUM, frozenset(), Effect.IO),
    'writelines': ('IO.writelines', (Sort.TOP, Sort.SEQ), Sort.NONE, frozenset(), Effect.IO),

    # Seeking
    'seek': ('IO.seek', (Sort.TOP, Sort.NUM), Sort.NUM, frozenset(), Effect.IO),
    'tell': ('IO.tell', (Sort.TOP,), Sort.NUM, frozenset(), Effect.IO),
    'truncate': ('IO.truncate', (Sort.TOP,), Sort.NUM, frozenset(), Effect.IO),

    # Management
    'close': ('IO.close', (Sort.TOP,), Sort.NONE, frozenset(), Effect.IO),
    'flush': ('IO.flush', (Sort.TOP,), Sort.NONE, frozenset(), Effect.IO),
    'fileno': ('IO.fileno', (Sort.TOP,), Sort.NUM, frozenset(), Effect.IO),
    'isatty': ('IO.isatty', (Sort.TOP,), Sort.BOOL, frozenset(), Effect.IO),
    'readable': ('IO.readable', (Sort.TOP,), Sort.BOOL, frozenset(), Effect.PURE),
    'writable': ('IO.writable', (Sort.TOP,), Sort.BOOL, frozenset(), Effect.PURE),
    'seekable': ('IO.seekable', (Sort.TOP,), Sort.BOOL, frozenset(), Effect.PURE),

    # getvalue (StringIO/BytesIO)
    'getvalue': ('IO.getvalue', (Sort.TOP,), Sort.STR, frozenset(), Effect.PURE),
}
