"""Public incremental workspace API."""

from deppy.incremental.differ import AffectedStalk, WorkspaceDiffer, compute_impact_set
from deppy.incremental.models import (
    ChangeNotice,
    ImpactSet,
    IncrementalAnalysisReport,
    SectionSnapshot,
    WorkspaceConfig,
    WorkspaceConfigurationError,
)
from deppy.incremental.propagator import IncrementalPropagator, PropagatorRunReport
from deppy.incremental.section_cache import CacheKey, CachedSectionRecord, SectionCache
from deppy.incremental.workspace import Workspace

__all__ = [
    "AffectedStalk",
    "CacheKey",
    "CachedSectionRecord",
    "ChangeNotice",
    "ImpactSet",
    "IncrementalAnalysisReport",
    "IncrementalPropagator",
    "PropagatorRunReport",
    "SectionCache",
    "SectionSnapshot",
    "Workspace",
    "WorkspaceConfig",
    "WorkspaceConfigurationError",
    "WorkspaceDiffer",
    "compute_impact_set",
]
