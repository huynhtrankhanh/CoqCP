"""The evaluator-owned axiom set shared by project CI and submission checks."""
import json
from pathlib import Path

POLICY_FILE = Path(__file__).resolve().parents[2] / "verification/trusted_axioms.json"


def trusted_axioms():
    data = json.loads(POLICY_FILE.read_text())
    if (set(data) != {"format", "coq_version", "axioms"}
            or data["format"] != 1 or data["coq_version"] != "8.20.1"
            or not isinstance(data["axioms"], list)
            or any(not isinstance(name, str) for name in data["axioms"])
            or len(set(data["axioms"])) != len(data["axioms"])):
        raise ValueError("Invalid evaluator-owned CI axiom policy")
    return sorted(data["axioms"])
