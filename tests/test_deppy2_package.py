import deppy2
from deppy2.analysis.common import ProgramArtifact
from deppy2.api.engine import DeppyEngine
from deppy2.foundation.trust import TrustLevel
from deppy2.runtime.fleet import FleetArbiter
from deppy2.synthesis.lowering import lower_intent


def test_deppy2_top_level_package_is_authoritative() -> None:
    assert hasattr(deppy2, "DeppyEngine")
    assert hasattr(deppy2, "run_fleet")
    assert DeppyEngine is deppy2.DeppyEngine


def test_deppy2_subpackages_import_and_execute() -> None:
    engine = DeppyEngine()
    fleet = engine.run_fleet("Build a verified API with fleet orchestration and JSON IO.")

    assert fleet.winner.score > 0
    assert lower_intent("verify structured API").domain_tags
    assert TrustLevel.Z3_PROVEN > TrustLevel.RUNTIME_CHECKED
    assert FleetArbiter is not None
    assert ProgramArtifact.__name__ == "ProgramArtifact"
