
from __future__ import annotations

import json
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class RuntimeProofCertificate:
    fn_name: str
    fn_hash: str
    invariant_str: str
    verified: bool
    solver: str
    timestamp: str
    reason: str
    proof_trace: str = ''

    def to_json(self) -> str:
        return json.dumps(asdict(self), indent=2)

    @classmethod
    def from_json(cls, data: str) -> 'RuntimeProofCertificate':
        return cls(**json.loads(data))
