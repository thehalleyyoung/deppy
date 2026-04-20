"""
Deppy Translation of the Complete F* Tutorial Book
=====================================================

This package contains Python translations of EVERY example, data structure,
and proof from the F* Tutorial Book (https://fstar-lang.org/tutorial/book),
reimplemented using Deppy's dependent type theory.

Each module corresponds to a section of the book:

Part 1: Programming and Proving with Total Functions
  - part1_total_functions.py: Refinement types, dependent arrows, recursion,
    termination, lemmas by induction, quicksort correctness

Part 2: Representing Data with Inductive Types  
  - part2a_indexed_types.py: Even/odd lists, vectors, Merkle trees
  - part2b_stlc_and_connectives.py: STLC type soundness, logical connectives

Part 3 & 4: Typeclasses, Interfaces, and Effects
  - part3_typeclasses_and_effects.py: Protocols as typeclasses, functor/monad laws,
    computational effects (Tot, Ghost, Div, Pure, ST)

Part 5: Tactics and Metaprogramming
  - part5_tactics.py: Tactic combinators, proof automation, homotopy tactics

Pulse: Separation Logic
  - pulse_separation_logic.py: SLProp, pts_to, frame rule, fractional permissions
  - pulse_data_structures.py: Linked lists, mutable arrays, recursive predicates
  - pulse_concurrency.py: Atomics, spin locks, parallel increment, async/await

Key Innovation: Every F* proof is translated using Deppy's genuine homotopy
constructs (paths, transport, Čech decomposition, fibrations) rather than just
Z3 SMT solving. This provides strictly more expressive proofs than F*.

Usage:
    # Run all examples:
    PYTHONPATH=. python3 deppy/examples/fstar_tutorial/run_all.py
    
    # Run individual modules:
    PYTHONPATH=. python3 deppy/examples/fstar_tutorial/part1_total_functions.py
"""

from __future__ import annotations
