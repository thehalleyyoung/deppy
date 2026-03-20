"""Deprecated modules — superseded by deppy.refinement_engine.

- dependent.py: Partial Verus-style API (30% complete). Replaced by
  deppy.refinement_engine which routes through the canonical
  contracts/ → surface/ → kernel/ → solver/ pipeline.

- verification_spectrum.py: Aspirational 5-level filtration design
  (40% complete). The spectrum concept is now implemented as the
  VerificationLevel parameter in deppy.refinement_engine.verify().
"""
