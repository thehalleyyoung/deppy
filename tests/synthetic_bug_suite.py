"""Synthetic bug suite: 20 bug types × {buggy, safe} = 40 functions.

Each pair exercises a specific sheaf-theoretic obstruction pattern against
Python's operational semantics.  The BUGGY variant has a gluing obstruction
(the local type sections at overlapping sites are incompatible).  The SAFE
variant provides a guard site whose section refines the available type,
making the restriction map total and eliminating the obstruction.

Sheaf-theoretic type theory framing
====================================

Python's evaluation semantics defines a presheaf F over the site cover C:

  F : C^op → RefinementType

At each observation site U, F(U) = {v : τ | φ(v)} is a refinement type.
A bug exists when the cocycle condition fails at an overlap U ∩ V:

  ρ_{UV} : F(U) → F(V)   is NOT total

i.e., there exist values in F(U) that cannot be restricted to F(V).

Each bug type below corresponds to a specific failure mode of this
restriction map, grounded in Python's concrete operational semantics:

  - REFINEMENT_GAP: φ_available ⊬ φ_required (predicate gap)
  - CARRIER_MISMATCH: τ_available ≠ τ_required (base type gap)
  - BINDING_GAP: Γ(U) ⊬ x ∈ dom(Γ) (variable not in binding presheaf)
  - LIFECYCLE_GAP: state(U) ≠ ALIVE (resource lifecycle presheaf)
  - CONCURRENCY_GAP: lock_set(U) ⊬ required_locks (synchronization presheaf)
  - INFORMATION_FLOW_GAP: output ⊬ independent_of(secret) (secrecy presheaf)
  - RANKING_GAP: ∄ r : State → ℕ with r decreasing (well-foundedness presheaf)
"""

# ═══════════════════════════════════════════════════════════════════════════════
# 1. DIV_ZERO — Refinement gap: {divisor : int | divisor ≠ 0}
#
# Python operational semantics: BINARY_OP dispatches to __truediv__ which
# raises ZeroDivisionError when the right operand is zero.  The presheaf
# section at the division site requires the divisor's refinement to exclude 0.
# ═══════════════════════════════════════════════════════════════════════════════

def div_zero_buggy(total, count):
    """Obstruction: unconstrained count flows to division site.
    Available section: {count : int | True}
    Required section:  {count : int | count ≠ 0}
    Gap: count = 0 is SAT."""
    average = total / count          # Gluing obstruction
    return round(average, 2)

def div_zero_safe(total, count):
    """Guard site refines the section: early-return on count == 0
    provides restriction map from {int|True} → {int|≠0}."""
    if count == 0:
        return 0.0
    average = total / count          # Obstruction resolved by guard
    return round(average, 2)


# ═══════════════════════════════════════════════════════════════════════════════
# 2. NULL_PTR — Refinement gap: {obj : T | obj is not None}
#
# Python's attribute lookup (__getattribute__) dereferences the object;
# if the object is None, the MRO walk fails with AttributeError.
# The presheaf section at the attribute site requires non-None carrier.
# ═══════════════════════════════════════════════════════════════════════════════

def null_ptr_buggy(mapping, key):
    """Obstruction: dict.get returns Optional[V], but .strip() requires V.
    Available section: {result : Optional[str] | True}
    Required section:  {result : str | result is not None}
    Gap: result = None is SAT (key might not exist)."""
    result = mapping.get(key)
    return result.strip()            # Gluing obstruction

def null_ptr_safe(mapping, key):
    """Guard site provides restriction: if result is not None.
    The BRANCH_GUARD site's section refines Optional[str] → str."""
    result = mapping.get(key)
    if result is not None:
        return result.strip()        # Obstruction resolved
    return ""


# ═══════════════════════════════════════════════════════════════════════════════
# 3. INDEX_OOB — Refinement gap: {i : int | 0 ≤ i < len(seq)}
#
# Python's BINARY_SUBSCR opcode calls __getitem__.  For list/tuple,
# this checks 0 ≤ (i if i >= 0 else i + len) < len.
# The presheaf section at the subscript site requires a bounded index.
# ═══════════════════════════════════════════════════════════════════════════════

def index_oob_buggy(items, position):
    """Obstruction: unconstrained position used as index.
    Available section: {position : int | True}
    Required section:  {position : int | 0 ≤ position < len(items)}
    Gap: position = len(items) is SAT."""
    return items[position]           # Gluing obstruction

def index_oob_safe(items, position):
    """Guard site provides bounds refinement via early return."""
    if position < 0 or position >= len(items):
        raise IndexError("position out of range")
    return items[position]           # Obstruction resolved


# ═══════════════════════════════════════════════════════════════════════════════
# 4. KEY_ERROR — Refinement gap: {k : K | k ∈ keys(d)}
#
# Python's dict.__getitem__ raises KeyError when the key is absent.
# The presheaf section at the subscript site requires membership in keys().
# The restriction map from the available section (arbitrary K) to the
# required section (K ∩ keys(d)) is only total if the key is known to exist.
# ═══════════════════════════════════════════════════════════════════════════════

def key_error_buggy(config, setting):
    """Obstruction: setting may not be in config.
    Available section: {setting : str | True}
    Required section:  {setting : str | setting ∈ keys(config)}
    Gap: setting ∉ config is SAT."""
    return config[setting]           # Gluing obstruction

def key_error_safe(config, setting):
    """Guard site provides membership refinement."""
    if setting in config:
        return config[setting]       # Obstruction resolved
    return None


# ═══════════════════════════════════════════════════════════════════════════════
# 5. TYPE_ERROR — Carrier mismatch: τ_left ⊕-compatible τ_right
#
# Python's BINARY_ADD first tries left.__add__(right), then right.__radd__(left).
# If both return NotImplemented, TypeError is raised.  The presheaf section at
# the addition site requires carrier compatibility across the overlap.
# ═══════════════════════════════════════════════════════════════════════════════

def type_error_buggy(name, age):
    """Obstruction: str + int has no __add__ match.
    Available sections: {name : str}, {age : int}
    Required section: carrier(name) ⊕-compatible carrier(age)
    Gap: str.__add__(int) returns NotImplemented, int.__radd__(str) too."""
    greeting = "Hello " + name + " age " + age  # Gluing obstruction
    return greeting

def type_error_safe(name, age):
    """Guard: isinstance check refines carrier to str, then str + str is valid."""
    if not isinstance(age, str):
        age = str(age)
    greeting = "Hello " + name + " age " + age  # Obstruction resolved
    return greeting


# ═══════════════════════════════════════════════════════════════════════════════
# 6. ASSERT_FAIL — Refinement gap: {cond : bool | cond is True}
#
# Python's RAISE_VARARGS opcode when the assert condition is false.
# The presheaf section at the assert site requires the condition to hold.
# In sheaf terms: the section at the assert site IS the assertion predicate,
# and the available section must imply it.
# ═══════════════════════════════════════════════════════════════════════════════

def assert_fail_buggy(items):
    """Obstruction: assert depends on items being non-empty, but no guard.
    Available section: {items : list | True}
    Required section:  {items : list | len(items) > 0}
    Gap: items = [] is SAT."""
    assert len(items) > 0            # Gluing obstruction
    return items[0]

def assert_fail_safe(items):
    """Guard: early return prevents reaching assert with empty list."""
    if not items:
        return None
    assert len(items) > 0            # Obstruction resolved (early return guards)
    return items[0]


# ═══════════════════════════════════════════════════════════════════════════════
# 7. UNBOUND_VAR — Binding presheaf gap: x ∉ dom(Γ(U))
#
# Python's LEGB scoping model defines a presheaf of binding environments:
# Γ : Sites → Env, where Env maps names to types.  A Name reference at site U
# requires x ∈ dom(Γ(U)).  If x is only bound on some branches, the presheaf
# has a gap at the join point: the sections from the two branches cannot be
# glued because one lacks the binding for x.
# ═══════════════════════════════════════════════════════════════════════════════

def unbound_var_buggy(flag):
    """Obstruction: x is only bound when flag is True.
    At the print site, Γ requires x ∈ dom, but the else-branch section
    of Γ has no binding for x.  The sections cannot glue at the join."""
    if flag:
        x = 42
    return x                         # Gluing obstruction: x unbound if not flag

def unbound_var_safe(flag):
    """Guard: x is unconditionally bound before use.
    Γ(U) = {x ↦ int} at ALL sites, so gluing succeeds."""
    x = 0
    if flag:
        x = 42
    return x                         # Obstruction resolved: x always bound


# ═══════════════════════════════════════════════════════════════════════════════
# 8. INTEGER_OVERFLOW — Refinement gap: {x : int | MIN_I32 ≤ x ≤ MAX_I32}
#
# Python ints are arbitrary-precision, but conversion to fixed-width types
# (struct.pack, ctypes, numpy) has bounded range.  The presheaf section at
# the pack site requires the value to lie in [MIN, MAX] for the format.
# ═══════════════════════════════════════════════════════════════════════════════

def integer_overflow_buggy(value):
    """Obstruction: value may exceed signed 32-bit range.
    Available section: {value : int | True}
    Required section:  {value : int | -2^31 ≤ value < 2^31}
    Gap: value = 2^31 is SAT."""
    import struct
    return struct.pack('i', value)   # Gluing obstruction

def integer_overflow_safe(value):
    """Guard: clamp provides restriction map to bounded range."""
    import struct
    clamped = max(-2**31, min(value, 2**31 - 1))
    return struct.pack('i', clamped) # Obstruction resolved


# ═══════════════════════════════════════════════════════════════════════════════
# 9. NON_TERMINATION — Ranking presheaf gap: ∄ r : State → ℕ, r decreasing
#
# A while loop defines a LOOP_HEADER_INVARIANT site.  Termination requires
# a ranking function r such that r(state) decreases on each iteration.
# The presheaf section at the loop header must carry {r : ℕ | r(state') < r(state)}.
# If no such section exists, the loop may not terminate.
# ═══════════════════════════════════════════════════════════════════════════════

def non_termination_buggy(n):
    """Obstruction: loop body does not decrease any ranking function.
    The loop header site requires a section carrying a decreasing measure,
    but n is never modified — no ranking function exists."""
    while n > 0:
        pass                         # Gluing obstruction: no ranking function
    return n

def non_termination_safe(n):
    """Guard: explicit decrease provides the ranking section.
    Ranking function r(state) = n; r(state') = n - 1 < n."""
    while n > 0:
        n -= 1                       # Obstruction resolved: ranking = n
    return n


# ═══════════════════════════════════════════════════════════════════════════════
# 10. MEMORY_LEAK — Resource lifecycle presheaf gap
#
# Python's resource lifecycle is a presheaf of states:
# S : Sites → {UNINITIALIZED, OPEN, CLOSED}.  An OPEN site must have a
# corresponding CLOSE site on ALL paths to the function exit.
# A memory leak is a gap: the section at the RETURN site says OPEN,
# but no close site's section transitions it to CLOSED.
# ═══════════════════════════════════════════════════════════════════════════════

def memory_leak_buggy(path):
    """Obstruction: file opened but not closed on exception path.
    Resource presheaf: open_site → OPEN, return_site → OPEN (leaked).
    The lifecycle section cannot glue to a valid global section because
    there is no CLOSE site on the exception path."""
    f = open(path, 'r')
    data = f.read()                  # If this raises, f is never closed
    f.close()
    return data                      # Gluing obstruction: exception path leaks

def memory_leak_safe(path):
    """Guard: context manager guarantees CLOSE on ALL paths.
    Resource presheaf: __enter__ → OPEN, __exit__ → CLOSED on every path."""
    with open(path, 'r') as f:
        data = f.read()              # Obstruction resolved: with-statement
    return data


# ═══════════════════════════════════════════════════════════════════════════════
# 11. USE_AFTER_FREE — Lifecycle presheaf gap: state(U) ≠ ALIVE
#
# Python's generator protocol defines a lifecycle:
# CREATED → RUNNING → SUSPENDED → CLOSED.  Calling send() on a CLOSED
# generator raises StopIteration/RuntimeError.  The presheaf section at
# the send site requires lifecycle(gen) = SUSPENDED, but after close()
# the available section says lifecycle(gen) = CLOSED.
# ═══════════════════════════════════════════════════════════════════════════════

def use_after_free_buggy():
    """Obstruction: file read after close.
    Available section at read site: {f : File | lifecycle(f) = CLOSED}
    Required section at read site:  {f : File | lifecycle(f) = OPEN}
    Gap: CLOSED ≠ OPEN."""
    f = open('/dev/null', 'r')
    f.close()
    return f.read()                  # Gluing obstruction: use after close

def use_after_free_safe():
    """Guard: no use after close — read precedes close.
    Lifecycle presheaf: open → OPEN, read → OPEN, close → CLOSED.
    All use-sites have lifecycle = OPEN."""
    f = open('/dev/null', 'r')
    data = f.read()                  # lifecycle = OPEN here
    f.close()
    return data                      # Obstruction resolved


# ═══════════════════════════════════════════════════════════════════════════════
# 12. DOUBLE_FREE — Lifecycle presheaf gap: second close on CLOSED resource
#
# The lifecycle presheaf must be a valid state machine: each site's section
# is a state in {OPEN, CLOSED}, and transitions are monotone (OPEN → CLOSED).
# A double-close means two CLOSE transitions, but the second has
# Available section: {f : File | lifecycle(f) = CLOSED}
# Required section:  {f : File | lifecycle(f) = OPEN}
# ═══════════════════════════════════════════════════════════════════════════════

def double_free_buggy(path):
    """Obstruction: file closed twice.
    Second close site requires OPEN but available section says CLOSED."""
    f = open(path, 'r')
    f.close()
    f.close()                        # Gluing obstruction: already CLOSED
    return True

def double_free_safe(path):
    """Guard: boolean flag tracks lifecycle state, preventing double close."""
    f = open(path, 'r')
    closed = False
    if not closed:
        f.close()
        closed = True
    # No second close attempted
    return True                      # Obstruction resolved


# ═══════════════════════════════════════════════════════════════════════════════
# 13. DATA_RACE — Synchronization presheaf gap
#
# Python's GIL protects against C-level data corruption, but NOT against
# logical races on compound operations.  The presheaf of synchronization:
# L : Sites → P(Locks) maps each site to the set of held locks.
# A shared mutable access at site U requires lock(obj) ∈ L(U).
# If no lock acquisition site's section covers U, the access is unprotected.
# ═══════════════════════════════════════════════════════════════════════════════

def data_race_buggy(shared_list):
    """Obstruction: shared list modified without lock in thread body.
    Available section at append site: {lock_set : P(Lock) | lock_set = ∅}
    Required section: {lock_set : P(Lock) | list_lock ∈ lock_set}
    Gap: ∅ does not contain list_lock."""
    import threading
    def worker():
        shared_list.append(1)        # Gluing obstruction: no lock held
    t = threading.Thread(target=worker)
    t.start()
    shared_list.append(2)            # Also unprotected
    t.join()
    return shared_list

def data_race_safe(shared_list):
    """Guard: lock acquisition site provides the required section."""
    import threading
    lock = threading.Lock()
    def worker():
        with lock:
            shared_list.append(1)    # Obstruction resolved: lock held
    t = threading.Thread(target=worker)
    t.start()
    with lock:
        shared_list.append(2)        # Obstruction resolved
    t.join()
    return shared_list


# ═══════════════════════════════════════════════════════════════════════════════
# 14. DEADLOCK — Lock ordering presheaf: cyclic acquisition
#
# The lock ordering presheaf O : Sites → ℕ assigns each lock acquisition
# a rank.  For the sections to glue, the ordering must be acyclic:
# if site U acquires lock A then lock B, O(A) < O(B).
# A deadlock is a cycle: thread 1 does A→B, thread 2 does B→A.
# ═══════════════════════════════════════════════════════════════════════════════

def deadlock_buggy():
    """Obstruction: two threads acquire locks in opposite order.
    Thread 1 section: O(a) = 0, O(b) = 1  (a before b)
    Thread 2 section: O(b) = 0, O(a) = 1  (b before a)
    These sections cannot glue: O(a) < O(b) and O(b) < O(a) is contradictory."""
    import threading
    a = threading.Lock()
    b = threading.Lock()
    def thread1():
        with a:
            with b:                  # a → b
                pass
    def thread2():
        with b:
            with a:                  # b → a: cyclic, gluing obstruction
                pass
    return thread1, thread2

def deadlock_safe():
    """Guard: consistent lock ordering eliminates the cycle.
    Global ordering O(a) = 0, O(b) = 1.  Both threads acquire a then b."""
    import threading
    a = threading.Lock()
    b = threading.Lock()
    def thread1():
        with a:
            with b:                  # a → b
                pass
    def thread2():
        with a:
            with b:                  # a → b (same order): obstruction resolved
                pass
    return thread1, thread2


# ═══════════════════════════════════════════════════════════════════════════════
# 15. TIMING_CHANNEL — Secrecy presheaf: branch depends on secret
#
# The secrecy presheaf S : Sites → {PUBLIC, SECRET} classifies data.
# A BRANCH_GUARD site requires its condition to be PUBLIC:
# {cond : bool | secrecy(cond) = PUBLIC}.  If the condition depends on
# a SECRET input, the restriction map from SECRET to PUBLIC is undefined.
# Timing channels arise because branch timing reveals the secret.
# ═══════════════════════════════════════════════════════════════════════════════

def timing_channel_buggy(stored_password, user_input):
    """Obstruction: early-exit comparison leaks password length/content via timing.
    Branch condition secrecy: SECRET (depends on stored_password).
    Required section: {cond : bool | secrecy(cond) = PUBLIC}
    Gap: the branch timing is a function of the secret."""
    if len(stored_password) != len(user_input):
        return False
    for i in range(len(stored_password)):
        if stored_password[i] != user_input[i]:
            return False             # Gluing obstruction: timing leak
    return True

def timing_channel_safe(stored_password, user_input):
    """Guard: constant-time comparison eliminates timing dependence.
    All branches execute in data-independent time, so secrecy = PUBLIC."""
    import hmac
    return hmac.compare_digest(stored_password, user_input)  # Obstruction resolved


# ═══════════════════════════════════════════════════════════════════════════════
# 16. INFO_LEAK — Secrecy presheaf: secret flows to public output
#
# The information flow presheaf I : Sites → Level tracks secrecy levels.
# An output site (return, print, log) requires Level = PUBLIC.
# If a SECRET input flows to the output without declassification, the
# restriction map from SECRET to PUBLIC is undefined — obstruction.
# ═══════════════════════════════════════════════════════════════════════════════

def info_leak_buggy(user_data):
    """Obstruction: exception includes sensitive data in its message.
    Available section at raise site: {msg : str | secrecy(msg) = SECRET}
    Required section at raise site:  {msg : str | secrecy(msg) = PUBLIC}
    Gap: SECRET ≠ PUBLIC."""
    try:
        result = process(user_data)
    except Exception as e:
        raise RuntimeError(f"Failed for user data: {user_data}") from e  # Obstruction
    return result

def info_leak_safe(user_data):
    """Guard: scrub sensitive data before including in error message."""
    try:
        result = process(user_data)
    except Exception as e:
        raise RuntimeError("Processing failed") from e  # Obstruction resolved
    return result


# ═══════════════════════════════════════════════════════════════════════════════
# 17. BOUNDS — Refinement gap: {i : int | lo ≤ i < hi}
#
# Python's slice/subscript on bytes/array.array/memoryview enforces bounds.
# The presheaf section at the access site requires the index to be in range.
# Unlike INDEX_OOB (which is about list[i]), BOUNDS is about lower-level
# buffer access where negative indexing may not be supported.
# ═══════════════════════════════════════════════════════════════════════════════

def bounds_buggy(data, offset, length):
    """Obstruction: explicit element reads raise IndexError when OOB.
    Available section: {offset : int | True}, {length : int | True}
    Required section:  {offset : int, length : int | 0 ≤ offset+i < len(data) for all i < length}
    Gap: offset + length > len(data) is SAT."""
    return [data[offset + i] for i in range(length)]  # IndexError when OOB

def bounds_safe(data, offset, length):
    """Guard: bounds check ensures all accesses are within range."""
    if offset < 0 or length < 0 or offset + length > len(data):
        raise ValueError("out of bounds")
    return [data[offset + i] for i in range(length)]  # Obstruction resolved


# ═══════════════════════════════════════════════════════════════════════════════
# 18. RUNTIME_ERROR — Operational semantics violation
#
# Python's call stack has a configurable recursion limit (sys.getrecursionlimit).
# The presheaf section at a recursive call site requires
# {depth : int | depth < limit}.  Unbounded recursion means the depth
# section grows without bound — no ranking function for the call stack.
# ═══════════════════════════════════════════════════════════════════════════════

def runtime_error_buggy(n):
    """Obstruction: no base case → unbounded recursion → RecursionError.
    The call site's section requires {depth < limit}, but no termination
    condition restricts the depth.  The ranking presheaf has no section."""
    return runtime_error_buggy(n - 1)  # Gluing obstruction: no base case

def runtime_error_safe(n):
    """Guard: base case provides a termination section.
    Ranking function r(n) = n; base case at n <= 0 bounds the depth."""
    if n <= 0:
        return 0
    return runtime_error_safe(n - 1)  # Obstruction resolved


# ═══════════════════════════════════════════════════════════════════════════════
# 19. TYPE_CONFUSION — Carrier mismatch at downcast
#
# Python's dynamic dispatch means a variable's carrier type may be wider
# than expected.  A method call site requires the carrier to support that
# method.  If the actual carrier is a supertype that lacks the method,
# the restriction map from the supertype to the required subtype fails.
# ═══════════════════════════════════════════════════════════════════════════════

def type_confusion_buggy(obj):
    """Obstruction: obj may be int; iterating int raises TypeError.
    Available section: {obj : Union[int, Iterable] | True}
    Required section:  {obj : Iterable | has_protocol(obj, '__iter__')}
    Gap: obj = 42 (int) has no __iter__ → TypeError: 'int' object is not iterable."""
    return list(obj)                 # Gluing obstruction: TypeError if obj is int

def type_confusion_safe(obj):
    """Guard: isinstance check narrows carrier to Iterable before conversion."""
    if isinstance(obj, (list, tuple, str, set)):
        return list(obj)             # Obstruction resolved
    return [obj]


# ═══════════════════════════════════════════════════════════════════════════════
# 20. OVERFLOW — Refinement gap on bounded arithmetic
#
# Python's native int is unbounded, but numpy/ctypes use fixed-width types.
# Arithmetic on these types can silently wrap around.  The presheaf section
# at an arithmetic site on a bounded type requires the result to be in range.
# ═══════════════════════════════════════════════════════════════════════════════

def overflow_buggy(a, b):
    """Obstruction: multiplication may exceed 64-bit range.
    Available section: {a : int | True}, {b : int | True}
    Required section:  {a*b : int | -2^63 ≤ a*b < 2^63}  (for C interop)
    Gap: a=2^32, b=2^32 gives 2^64 which overflows int64."""
    import struct
    product = a * b
    return struct.pack('q', product)  # Gluing obstruction

def overflow_safe(a, b):
    """Guard: range check provides restriction map to bounded domain."""
    import struct
    product = a * b
    if product < -2**63 or product >= 2**63:
        raise OverflowError("product exceeds int64 range")
    return struct.pack('q', product)  # Obstruction resolved


# ═══════════════════════════════════════════════════════════════════════════════
# Helpers referenced by examples
# ═══════════════════════════════════════════════════════════════════════════════

def process(data):
    """Stub for info_leak examples."""
    if not data:
        raise ValueError("empty data")
    return data


# ═══════════════════════════════════════════════════════════════════════════════
# EXTENDED PAIRS — 2 additional buggy/safe pairs per bug type
# (3 pairs total per type × 20 types = 60 pairs = 120 functions)
# ═══════════════════════════════════════════════════════════════════════════════

# ─── DIV_ZERO extra pairs ─────────────────────────────────────────────────────

def div_zero_2_buggy(values: list) -> int:
    """Floor-div by len([]) when list is empty."""
    return sum(values) // len(values)   # len([]) == 0 → ZeroDivisionError

def div_zero_2_safe(values: list) -> int:
    if not values:
        return 0
    return sum(values) // len(values)

def div_zero_3_buggy(n: int, modulus: int) -> int:
    """Modulo by potentially-zero modulus."""
    return n % modulus                  # modulus == 0 → ZeroDivisionError

def div_zero_3_safe(n: int, modulus: int) -> int:
    if modulus == 0:
        raise ValueError("modulus cannot be zero")
    return n % modulus


# ─── NULL_PTR extra pairs ─────────────────────────────────────────────────────

def null_ptr_2_buggy(text: str, pattern: str) -> str:
    """re.search may return None; calling .group(0) on None is AttributeError."""
    import re
    m = re.search(pattern, text)
    return m.group(0)                   # m might be None → AttributeError

def null_ptr_2_safe(text: str, pattern: str) -> str:
    import re
    m = re.search(pattern, text)
    if m is None:
        return ""
    return m.group(0)

def null_ptr_3_buggy(data: dict, key: str) -> str:
    """data.get() returns None; indexing None raises TypeError."""
    node = data.get(key)
    return node["value"]                # node might be None → TypeError

def null_ptr_3_safe(data: dict, key: str) -> str:
    node = data.get(key)
    if node is None:
        return ""
    return node.get("value", "")


# ─── INDEX_OOB extra pairs ────────────────────────────────────────────────────

def index_oob_2_buggy(items: list) -> object:
    """Access first element of potentially empty list."""
    return items[0]                     # empty list → IndexError

def index_oob_2_safe(items: list) -> object:
    if not items:
        return None
    return items[0]

def index_oob_3_buggy(items: list, n: int) -> object:
    """Negative index may exceed list length."""
    return items[-(n + 1)]              # n+1 > len(items) → IndexError

def index_oob_3_safe(items: list, n: int) -> object:
    if n < 0 or n + 1 > len(items):
        return None
    return items[-(n + 1)]


# ─── KEY_ERROR extra pairs ────────────────────────────────────────────────────

def key_error_2_buggy(data: dict, user_id: str) -> str:
    """Nested dict lookup with no guard on intermediate key."""
    return data["users"][user_id]["email"]  # any level may raise KeyError

def key_error_2_safe(data: dict, user_id: str) -> str:
    users = data.get("users", {})
    user = users.get(user_id, {})
    return user.get("email", "")

def key_error_3_buggy(counter: dict, key: str) -> int:
    """Direct subscript on counter dict; key may be absent."""
    return counter[key]                 # missing key → KeyError

def key_error_3_safe(counter: dict, key: str) -> int:
    return counter.get(key, 0)


# ─── TYPE_ERROR extra pairs ───────────────────────────────────────────────────

def type_error_2_buggy(items: list) -> str:
    """str.join requires all elements to be strings."""
    return ", ".join(items)             # non-str element → TypeError

def type_error_2_safe(items: list) -> str:
    return ", ".join(str(x) for x in items)

def type_error_3_buggy(x) -> int:
    """len() requires a sequence; int has no __len__."""
    return len(x)                       # x might be int → TypeError

def type_error_3_safe(x) -> int:
    if not hasattr(x, "__len__"):
        return 0
    return len(x)


# ─── ASSERT_FAIL extra pairs ──────────────────────────────────────────────────

def assert_fail_2_buggy(ratio: float) -> float:
    """ratio may be outside [0, 1] — assertion fails."""
    assert 0.0 <= ratio <= 1.0, "ratio out of range"  # fails if ratio > 1 or < 0
    return ratio * 100.0

def assert_fail_2_safe(ratio: float) -> float:
    ratio = max(0.0, min(1.0, ratio))
    return ratio * 100.0

def assert_fail_3_buggy(value) -> int:
    """isinstance assertion may fail for non-int input."""
    assert isinstance(value, int), f"expected int, got {type(value).__name__}"
    return value + 1                    # AssertionError if value is not int

def assert_fail_3_safe(value) -> int:
    if not isinstance(value, int):
        raise TypeError(f"expected int, got {type(value).__name__}")
    return value + 1


# ─── UNBOUND_VAR extra pairs ──────────────────────────────────────────────────

def unbound_var_2_buggy(n: int) -> int:
    """Loop variable 'last' is unbound when n == 0."""
    for i in range(n):
        last = i * 2
    return last                         # UnboundLocalError if n == 0

def unbound_var_2_safe(n: int) -> int:
    last = 0
    for i in range(n):
        last = i * 2
    return last

def unbound_var_3_buggy(mode: str) -> str:
    """'result' is unbound when mode is not 'fast' or 'slow'."""
    if mode == "fast":
        result = "quick"
    elif mode == "slow":
        result = "thorough"
    return result                       # UnboundLocalError if mode is anything else

def unbound_var_3_safe(mode: str) -> str:
    if mode == "fast":
        result = "quick"
    elif mode == "slow":
        result = "thorough"
    else:
        result = "default"
    return result


# ─── INTEGER_OVERFLOW extra pairs ─────────────────────────────────────────────

def integer_overflow_2_buggy(a: int, b: int) -> bytes:
    """Sum of two ints packed as int32; sum may exceed range."""
    import struct
    return struct.pack("i", a + b)      # OverflowError if a+b outside [-2^31, 2^31)

def integer_overflow_2_safe(a: int, b: int) -> bytes:
    import struct
    s = a + b
    if not (-(2**31) <= s < 2**31):
        raise OverflowError("sum overflows int32")
    return struct.pack("i", s)

def integer_overflow_3_buggy(x: int, shift: int) -> bytes:
    """Left-shift result packed as int32; may overflow."""
    import struct
    return struct.pack("i", x << shift) # OverflowError if result outside int32

def integer_overflow_3_safe(x: int, shift: int) -> bytes:
    import struct
    result = x << shift
    if not (-(2**31) <= result < 2**31):
        raise OverflowError("shift result overflows int32")
    return struct.pack("i", result)


# ─── NON_TERMINATION extra pairs ──────────────────────────────────────────────

def non_termination_2_buggy(x: int) -> int:
    """Loop variable grows toward condition, never away — diverges."""
    while x > 0:
        x += 1                          # x grows: condition never becomes False
    return x

def non_termination_2_safe(x: int) -> int:
    while x > 0:
        x -= 1
    return x

def non_termination_3_buggy(counter: int) -> int:
    """Counter only moves toward 0 when even; odd values cycle."""
    while counter != 0:
        if counter % 2 == 0:
            counter //= 2
        else:
            counter += 1               # odd: increments, never reaches 0 if start is odd
    return counter

def non_termination_3_safe(counter: int) -> int:
    steps = 0
    max_steps = abs(counter) * 4 + 10  # ranking: guaranteed finite
    while counter != 0 and steps < max_steps:
        if counter % 2 == 0:
            counter //= 2
        else:
            counter += 1
        steps += 1
    return counter


# ─── MEMORY_LEAK extra pairs ──────────────────────────────────────────────────

def memory_leak_2_buggy(host: str, port: int) -> bytes:
    """Socket opened but not closed if recv() raises."""
    import socket
    s = socket.socket()
    s.connect((host, port))
    data = s.recv(1024)                 # if this raises, s is never closed
    s.close()
    return data

def memory_leak_2_safe(host: str, port: int) -> bytes:
    import socket
    with socket.socket() as s:
        s.connect((host, port))
        return s.recv(1024)

def memory_leak_3_buggy(shared: list) -> list:
    """Lock acquired but not released if append raises."""
    import threading
    lock = threading.Lock()
    lock.acquire()
    shared.append(1)                    # if this raises, lock is never released
    lock.release()
    return shared

def memory_leak_3_safe(shared: list) -> list:
    import threading
    lock = threading.Lock()
    with lock:
        shared.append(1)
    return shared


# ─── USE_AFTER_FREE extra pairs ───────────────────────────────────────────────

def use_after_free_2_buggy() -> str:
    """Read from StringIO buffer after it has been closed."""
    import io
    buf = io.StringIO("hello")
    buf.close()
    return buf.read()                   # use after close → ValueError

def use_after_free_2_safe() -> str:
    import io
    with io.StringIO("hello") as buf:
        return buf.read()

def use_after_free_3_buggy(items: list) -> list:
    """Iterator invalidated by modifying the list during iteration."""
    it = iter(items)
    items.clear()                       # invalidates iterator
    return list(it)                     # use after structural change

def use_after_free_3_safe(items: list) -> list:
    snapshot = list(items)
    return list(iter(snapshot))


# ─── DOUBLE_FREE extra pairs ──────────────────────────────────────────────────

def double_free_2_buggy(path: str) -> str:
    """File closed in finally AND again after the try block."""
    f = open(path, "r")
    try:
        data = f.read()
    finally:
        f.close()
    f.close()                           # already closed → double close
    return data

def double_free_2_safe(path: str) -> str:
    with open(path, "r") as f:
        return f.read()

def double_free_3_buggy(path: str, extra_close: bool) -> str:
    """Conditional second close creates double-free on one branch."""
    f = open(path, "r")
    data = f.read()
    f.close()
    if extra_close:
        f.close()                       # double close when extra_close=True
    return data

def double_free_3_safe(path: str, extra_close: bool) -> str:
    with open(path, "r") as f:
        return f.read()


# ─── DATA_RACE extra pairs ────────────────────────────────────────────────────

def data_race_2_buggy(n: int) -> int:
    """Shared counter incremented by 4 threads without any lock."""
    import threading
    counter = [0]
    def increment():
        for _ in range(n):
            counter[0] += 1             # read-modify-write not atomic
    threads = [threading.Thread(target=increment) for _ in range(4)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    return counter[0]

def data_race_2_safe(n: int) -> int:
    import threading
    counter = [0]
    lock = threading.Lock()
    def increment():
        for _ in range(n):
            with lock:
                counter[0] += 1
    threads = [threading.Thread(target=increment) for _ in range(4)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    return counter[0]

def data_race_3_buggy(d: dict, key: str, value: object) -> None:
    """Check-then-act TOCTOU: key check and assignment not atomic."""
    if key not in d:
        d[key] = value                  # another thread may have set d[key]

def data_race_3_safe(d: dict, key: str, value: object) -> None:
    import threading
    lock = threading.Lock()
    with lock:
        if key not in d:
            d[key] = value


# ─── DEADLOCK extra pairs ─────────────────────────────────────────────────────

def deadlock_2_buggy(data: list) -> int:
    """Non-reentrant lock acquired twice on the same thread → deadlock."""
    import threading
    lock = threading.Lock()             # NOT RLock
    def process(item):
        with lock:
            with lock:                  # inner acquire blocks forever
                return item * 2
    return sum(process(x) for x in data)

def deadlock_2_safe(data: list) -> int:
    import threading
    lock = threading.RLock()            # reentrant lock
    def process(item):
        with lock:
            with lock:
                return item * 2
    return sum(process(x) for x in data)

def deadlock_3_buggy() -> tuple:
    """Three threads with cyclic lock order: a→b→c, b→c→a, c→a→b."""
    import threading
    a, b, c = threading.Lock(), threading.Lock(), threading.Lock()
    def t1():
        with a:
            with b:
                pass
    def t2():
        with b:
            with c:
                pass
    def t3():
        with c:
            with a:             # cycle: c→a while t1 holds a waiting for b
                pass
    return t1, t2, t3

def deadlock_3_safe() -> tuple:
    import threading
    a, b, c = threading.Lock(), threading.Lock(), threading.Lock()
    def t1():
        with a:
            with b:
                pass
    def t2():
        with a:
            with c:
                pass
    def t3():
        with b:
            with c:
                pass
    return t1, t2, t3


# ─── TIMING_CHANNEL extra pairs ───────────────────────────────────────────────

def timing_channel_2_buggy(secret_token: str, user_token: str) -> bool:
    """Direct string equality leaks length via early-exit semantics."""
    return secret_token == user_token   # non-constant-time comparison

def timing_channel_2_safe(secret_token: str, user_token: str) -> bool:
    import hmac
    return hmac.compare_digest(
        secret_token.encode(), user_token.encode()
    )

def timing_channel_3_buggy(key: bytes, provided: bytes) -> bool:
    """Byte-by-byte loop with early return leaks key content via timing."""
    if len(key) != len(provided):
        return False
    result = True
    for a, b in zip(key, provided):
        if a != b:
            return False                # early exit: timing leaks key bits
    return result

def timing_channel_3_safe(key: bytes, provided: bytes) -> bool:
    import hmac
    return hmac.compare_digest(key, provided)


# ─── INFO_LEAK extra pairs ────────────────────────────────────────────────────

def info_leak_2_buggy(username: str, password: str) -> bool:
    """Password included verbatim in log message."""
    import logging
    logging.info(
        "Login attempt: username=%s password=%s", username, password
    )                                   # password flows to public log output
    return True

def info_leak_2_safe(username: str, password: str) -> bool:
    import logging
    logging.info("Login attempt: username=%s", username)
    return True

def info_leak_3_buggy(api_key: str, endpoint: str) -> str:
    """API key embedded in exception message that propagates to caller."""
    try:
        raise ConnectionError("refused")
    except ConnectionError as e:
        raise RuntimeError(
            f"Request to {endpoint} failed (key={api_key})"
        ) from e                        # secret flows to exception message

def info_leak_3_safe(api_key: str, endpoint: str) -> str:
    try:
        raise ConnectionError("refused")
    except ConnectionError as e:
        raise RuntimeError(f"Request to {endpoint} failed") from e


# ─── BOUNDS extra pairs ───────────────────────────────────────────────────────

def bounds_2_buggy(buf: bytearray, index: int, value: int) -> bytearray:
    """Direct bytearray subscript; index may be out of range."""
    buf[index] = value                  # IndexError if index >= len(buf)
    return buf

def bounds_2_safe(buf: bytearray, index: int, value: int) -> bytearray:
    if 0 <= index < len(buf):
        buf[index] = value
    return buf

def bounds_3_buggy(data: list, start: int, window: int) -> list:
    """Explicit element reads with unchecked start — IndexError when start OOB."""
    if start < 0:
        raise ValueError("negative start")
    return [data[start + i] for i in range(window)]  # IndexError if start >= len(data)

def bounds_3_safe(data: list, start: int, window: int) -> list:
    if start < 0 or window < 0 or start + window > len(data):
        return []
    return [data[start + i] for i in range(window)]


# ─── RUNTIME_ERROR extra pairs ────────────────────────────────────────────────

def runtime_error_2_buggy(n: int) -> int:
    """Mutual recursion with no base case — guaranteed RecursionError."""
    def _a(x: int) -> int:
        return _b(x)
    def _b(x: int) -> int:
        return _a(x)
    return _a(n)

def runtime_error_2_safe(n: int) -> int:
    def _a(x: int) -> int:
        if x <= 0:
            return 0
        return _b(x - 1)
    def _b(x: int) -> int:
        if x <= 0:
            return 0
        return _a(x - 1)
    return _a(n)

def runtime_error_3_buggy(nested: list) -> list:
    """Deep recursive flattener with no depth limit — RecursionError on deep input."""
    result = []
    for item in nested:
        if isinstance(item, list):
            result.extend(runtime_error_3_buggy(item))
        else:
            result.append(item)
    return result

def runtime_error_3_safe(nested: list, _depth: int = 0) -> list:
    if _depth > 500:
        raise RecursionError("nesting too deep")
    result = []
    for item in nested:
        if isinstance(item, list):
            result.extend(runtime_error_3_safe(item, _depth + 1))
        else:
            result.append(item)
    return result


# ─── TYPE_CONFUSION extra pairs ───────────────────────────────────────────────

def type_confusion_2_buggy(obj) -> int:
    """len() requires a sized object; int has no __len__ → TypeError."""
    return len(obj)                     # TypeError: object of type 'int' has no len()

def type_confusion_2_safe(obj) -> int:
    if hasattr(obj, "__len__"):
        return len(obj)
    return 0

def type_confusion_3_buggy(value) -> list:
    """sorted() requires an iterable; int has no __iter__ → TypeError."""
    return sorted(value)                # TypeError: 'int' object is not iterable

def type_confusion_3_safe(value) -> list:
    if isinstance(value, (list, tuple, str, set, dict)):
        return sorted(value)
    return [value]


# ─── OVERFLOW extra pairs ─────────────────────────────────────────────────────

def overflow_2_buggy(values: list) -> bytes:
    """Sum of list elements packed as int32; sum may exceed range."""
    import struct
    return struct.pack("i", sum(values))  # OverflowError if sum outside int32

def overflow_2_safe(values: list) -> bytes:
    import struct
    s = sum(values)
    if not (-(2**31) <= s < 2**31):
        raise OverflowError("sum exceeds int32 range")
    return struct.pack("i", s)

def overflow_3_buggy(x: int, n_bits: int) -> bytes:
    """Left-shift result packed as int64; may overflow."""
    import struct
    return struct.pack("q", x << n_bits)  # OverflowError if outside int64

def overflow_3_safe(x: int, n_bits: int) -> bytes:
    import struct
    result = x << n_bits
    if not (-(2**63) <= result < 2**63):
        raise OverflowError("shift overflows int64")
    return struct.pack("q", result)


# ═══════════════════════════════════════════════════════════════════════════════
# Suite registry — 3 pairs per bug type × 20 types = 60 pairs = 120 functions
# ═══════════════════════════════════════════════════════════════════════════════

SUITE = [
    # (bug_type, buggy_func, safe_func, description)
    # ── Original pairs (pair 1) ──
    ("DIV_ZERO",          div_zero_buggy,              div_zero_safe,              "Refinement gap: divisor ≠ 0"),
    ("NULL_PTR",          null_ptr_buggy,              null_ptr_safe,              "Refinement gap: obj is not None"),
    ("INDEX_OOB",         index_oob_buggy,             index_oob_safe,             "Refinement gap: 0 ≤ i < len"),
    ("KEY_ERROR",         key_error_buggy,             key_error_safe,             "Refinement gap: k ∈ keys(d)"),
    ("TYPE_ERROR",        type_error_buggy,            type_error_safe,            "Carrier mismatch: ⊕-compatible"),
    ("ASSERT_FAIL",       assert_fail_buggy,           assert_fail_safe,           "Refinement gap: assertion predicate"),
    ("UNBOUND_VAR",       unbound_var_buggy,           unbound_var_safe,           "Binding presheaf gap: x ∈ dom(Γ)"),
    ("INTEGER_OVERFLOW",  integer_overflow_buggy,      integer_overflow_safe,      "Refinement gap: bounded range"),
    ("NON_TERMINATION",   non_termination_buggy,       non_termination_safe,       "Ranking presheaf gap: ∄ decreasing r"),
    ("MEMORY_LEAK",       memory_leak_buggy,           memory_leak_safe,           "Lifecycle presheaf gap: unclosed resource"),
    ("USE_AFTER_FREE",    use_after_free_buggy,        use_after_free_safe,        "Lifecycle presheaf gap: state ≠ ALIVE"),
    ("DOUBLE_FREE",       double_free_buggy,           double_free_safe,           "Lifecycle presheaf gap: double close"),
    ("DATA_RACE",         data_race_buggy,             data_race_safe,             "Synchronization presheaf gap: no lock"),
    ("DEADLOCK",          deadlock_buggy,              deadlock_safe,              "Lock ordering presheaf: cyclic order"),
    ("TIMING_CHANNEL",    timing_channel_buggy,        timing_channel_safe,        "Secrecy presheaf: secret-dependent branch"),
    ("INFO_LEAK",         info_leak_buggy,             info_leak_safe,             "Secrecy presheaf: secret → public output"),
    ("BOUNDS",            bounds_buggy,                bounds_safe,                "Refinement gap: lo ≤ i < hi"),
    ("RUNTIME_ERROR",     runtime_error_buggy,         runtime_error_safe,         "Ranking presheaf: unbounded recursion"),
    ("TYPE_CONFUSION",    type_confusion_buggy,        type_confusion_safe,        "Carrier mismatch: method dispatch"),
    ("OVERFLOW",          overflow_buggy,              overflow_safe,              "Refinement gap: bounded arithmetic"),
    # ── Extended pairs (pair 2) ──
    ("DIV_ZERO",          div_zero_2_buggy,            div_zero_2_safe,            "Refinement gap: divisor ≠ 0 (floor-div on empty list)"),
    ("NULL_PTR",          null_ptr_2_buggy,            null_ptr_2_safe,            "Refinement gap: re.search result may be None"),
    ("INDEX_OOB",         index_oob_2_buggy,           index_oob_2_safe,           "Refinement gap: first element of possibly-empty list"),
    ("KEY_ERROR",         key_error_2_buggy,           key_error_2_safe,           "Refinement gap: nested dict access"),
    ("TYPE_ERROR",        type_error_2_buggy,          type_error_2_safe,          "Carrier mismatch: join requires all-str elements"),
    ("ASSERT_FAIL",       assert_fail_2_buggy,         assert_fail_2_safe,         "Refinement gap: ratio must be in [0,1]"),
    ("UNBOUND_VAR",       unbound_var_2_buggy,         unbound_var_2_safe,         "Binding gap: loop variable unbound when n=0"),
    ("INTEGER_OVERFLOW",  integer_overflow_2_buggy,    integer_overflow_2_safe,    "Refinement gap: sum may overflow int32"),
    ("NON_TERMINATION",   non_termination_2_buggy,     non_termination_2_safe,     "Ranking gap: loop variable grows instead of shrinks"),
    ("MEMORY_LEAK",       memory_leak_2_buggy,         memory_leak_2_safe,         "Lifecycle gap: socket not closed on exception path"),
    ("USE_AFTER_FREE",    use_after_free_2_buggy,      use_after_free_2_safe,      "Lifecycle gap: StringIO read after close"),
    ("DOUBLE_FREE",       double_free_2_buggy,         double_free_2_safe,         "Lifecycle gap: finally + explicit close = double-close"),
    ("DATA_RACE",         data_race_2_buggy,           data_race_2_safe,           "Sync gap: counter incremented by 4 threads sans lock"),
    ("DEADLOCK",          deadlock_2_buggy,            deadlock_2_safe,            "Lock ordering gap: non-reentrant lock acquired twice"),
    ("TIMING_CHANNEL",    timing_channel_2_buggy,      timing_channel_2_safe,      "Secrecy gap: direct string equality is non-constant-time"),
    ("INFO_LEAK",         info_leak_2_buggy,           info_leak_2_safe,           "Secrecy gap: password in log message"),
    ("BOUNDS",            bounds_2_buggy,              bounds_2_safe,              "Refinement gap: bytearray subscript OOB"),
    ("RUNTIME_ERROR",     runtime_error_2_buggy,       runtime_error_2_safe,       "Ranking gap: mutual recursion with no base case"),
    ("TYPE_CONFUSION",    type_confusion_2_buggy,      type_confusion_2_safe,      "Carrier mismatch: bit_length() is int-only"),
    ("OVERFLOW",          overflow_2_buggy,            overflow_2_safe,            "Refinement gap: list sum may overflow int32"),
    # ── Extended pairs (pair 3) ──
    ("DIV_ZERO",          div_zero_3_buggy,            div_zero_3_safe,            "Refinement gap: modulo by possibly-zero modulus"),
    ("NULL_PTR",          null_ptr_3_buggy,            null_ptr_3_safe,            "Refinement gap: chained dict.get() subscript on None"),
    ("INDEX_OOB",         index_oob_3_buggy,           index_oob_3_safe,           "Refinement gap: negative index beyond list length"),
    ("KEY_ERROR",         key_error_3_buggy,           key_error_3_safe,           "Refinement gap: counter subscript on absent key"),
    ("TYPE_ERROR",        type_error_3_buggy,          type_error_3_safe,          "Carrier mismatch: len() on non-sequence"),
    ("ASSERT_FAIL",       assert_fail_3_buggy,         assert_fail_3_safe,         "Refinement gap: isinstance assertion on wrong type"),
    ("UNBOUND_VAR",       unbound_var_3_buggy,         unbound_var_3_safe,         "Binding gap: result unbound when mode is unrecognized"),
    ("INTEGER_OVERFLOW",  integer_overflow_3_buggy,    integer_overflow_3_safe,    "Refinement gap: left-shift may overflow int32"),
    ("NON_TERMINATION",   non_termination_3_buggy,     non_termination_3_safe,     "Ranking gap: odd counter diverges from zero"),
    ("MEMORY_LEAK",       memory_leak_3_buggy,         memory_leak_3_safe,         "Lifecycle gap: lock not released on exception path"),
    ("USE_AFTER_FREE",    use_after_free_3_buggy,      use_after_free_3_safe,      "Lifecycle gap: iterator used after list.clear()"),
    ("DOUBLE_FREE",       double_free_3_buggy,         double_free_3_safe,         "Lifecycle gap: conditional second close"),
    ("DATA_RACE",         data_race_3_buggy,           data_race_3_safe,           "Sync gap: TOCTOU check-then-act on dict"),
    ("DEADLOCK",          deadlock_3_buggy,            deadlock_3_safe,            "Lock ordering gap: 3-thread cyclic acquisition"),
    ("TIMING_CHANNEL",    timing_channel_3_buggy,      timing_channel_3_safe,      "Secrecy gap: byte-loop with early-exit leaks key bits"),
    ("INFO_LEAK",         info_leak_3_buggy,           info_leak_3_safe,           "Secrecy gap: API key in exception message"),
    ("BOUNDS",            bounds_3_buggy,              bounds_3_safe,              "Refinement gap: slice start may be >= len(data)"),
    ("RUNTIME_ERROR",     runtime_error_3_buggy,       runtime_error_3_safe,       "Ranking gap: recursive flatten with no depth limit"),
    ("TYPE_CONFUSION",    type_confusion_3_buggy,      type_confusion_3_safe,      "Carrier mismatch: split() called on non-str"),
    ("OVERFLOW",          overflow_3_buggy,            overflow_3_safe,            "Refinement gap: left-shift may overflow int64"),
]
