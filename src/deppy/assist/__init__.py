"""deppy.assist -- User assistance and interactive query support.

Phase 10 (assist) of the sheaf-descent semantic typing pipeline.  This
package provides:

- **ExplanationEngine**: Generate explanations for type diagnostics.
- **RecommendationEngine**: Recommend actions to resolve type errors.
- **QueryHandler**: Handle interactive queries about sites and sections.

Typical usage::

    from deppy.assist import (
        ExplanationEngine,
        RecommendationEngine,
        QueryHandler,
    )

    # Explanation generation
    engine = ExplanationEngine()
    explanation = engine.explain(diagnostic, cover, sections)
    print(explanation.summary)

    # Action recommendations
    rec_engine = RecommendationEngine()
    recs = rec_engine.recommend(diagnostics, cover)
    for r in recs:
        print(f"[{r.kind}] {r.title}")

    # Interactive queries
    handler = QueryHandler(cover, sections)
    info = handler.query_site(site_id)
    why = handler.query_why(site_a, site_b)
"""

from deppy.assist.explanation_engine import (
    Explanation,
    ExplanationEngine,
    ExplanationStep,
)
from deppy.assist.recommendation_engine import (
    Recommendation,
    RecommendationEngine,
)
from deppy.assist.query_handler import (
    QueryHandler,
    SectionInfo,
    SiteInfo,
    WhyExplanation,
)

__all__ = [
    "Explanation",
    "ExplanationEngine",
    "ExplanationStep",
    "QueryHandler",
    "Recommendation",
    "RecommendationEngine",
    "SectionInfo",
    "SiteInfo",
    "WhyExplanation",
]
