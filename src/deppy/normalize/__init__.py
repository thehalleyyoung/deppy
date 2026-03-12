"""deppy.normalize -- Normalization passes for sheaf-descent semantics.

Provides expression, predicate, and contract normalization, plus
fragment classification, symbol elimination, and section normalization.
"""

from deppy.normalize.normalizer import (
    ContractNormalizer,
    ExpressionNormalizer,
    PredicateNormalizer,
)
from deppy.normalize.fragment_classifier import (
    Fragment,
    FragmentClassifier,
    FragmentInfo,
)
from deppy.normalize.symbol_eliminator import (
    EliminationResult,
    SymbolEliminator,
)
from deppy.normalize.section_normalizer import (
    NormalizationResult,
    SectionNormalizer,
)

__all__ = [
    # normalizer
    "ContractNormalizer",
    "ExpressionNormalizer",
    "PredicateNormalizer",
    # fragment classifier
    "Fragment",
    "FragmentClassifier",
    "FragmentInfo",
    # symbol eliminator
    "EliminationResult",
    "SymbolEliminator",
    # section normalizer
    "NormalizationResult",
    "SectionNormalizer",
]
