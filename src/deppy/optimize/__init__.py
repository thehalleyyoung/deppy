"""deppy.optimize -- Optimization, frontier search, repair guidance, and ranking.

Phase 10 (optimize) of the sheaf-descent semantic typing pipeline.  This
package provides:

- **FrontierSearch**: Pareto-optimal input/output refinement frontier search.
- **RepairGuidance**: Actionable code repair suggestions for obstructions.
- **ObstructionRanker**: Rank obstructions by resolution power and impact.
- **SeedRecommender**: Recommend annotations/proofs/theory activations.
- **IncrementalUpdater**: Incremental re-analysis on code edits.

Typical usage::

    from deppy.optimize import (
        FrontierSearch,
        RepairGuidance,
        ObstructionRanker,
        SeedRecommender,
        IncrementalUpdater,
    )

    # Frontier search
    searcher = FrontierSearch()
    input_frontier = searcher.search_input_frontier(cover, sections)
    output_frontier = searcher.search_output_frontier(cover, sections)
    summary = searcher.search_full_frontier(cover, sections, obstructions)

    # Repair guidance
    guidance = RepairGuidance()
    repairs = guidance.suggest_repairs(obstructions)

    # Obstruction ranking
    ranker = ObstructionRanker()
    ranked = ranker.rank(obstructions, cover)

    # Seed recommendations
    recommender = SeedRecommender()
    recommendations = recommender.recommend(residuals, cover)

    # Incremental update
    updater = IncrementalUpdater()
    delta = updater.compute_delta(old_cover, new_cover)
    invalid = updater.invalidated_sites(delta, new_cover)
    reusable = updater.reuse_sections(old_sections, delta, new_cover)
"""

from deppy.optimize.frontier_search import FrontierSearch
from deppy.optimize.repair_guidance import (
    RepairGuidance,
    RepairSuggestion,
    SourceLocation as RepairLocation,
)
from deppy.optimize.obstruction_ranker import (
    ObstructionRanker,
    RankedObstruction,
)
from deppy.optimize.seed_recommender import (
    Recommendation,
    RecommendationKind,
    SeedRecommender,
)
from deppy.optimize.incremental_update import (
    CoverDelta,
    IncrementalUpdater,
)

__all__ = [
    "CoverDelta",
    "FrontierSearch",
    "IncrementalUpdater",
    "ObstructionRanker",
    "RankedObstruction",
    "Recommendation",
    "RecommendationKind",
    "RepairGuidance",
    "RepairLocation",
    "RepairSuggestion",
    "SeedRecommender",
]
