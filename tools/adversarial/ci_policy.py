"""The evaluator-owned axiom set shared by project CI and submission checks."""
import json
from pathlib import Path

POLICY_FILE = Path(__file__).resolve().parents[2] / "verification/trusted_axioms.json"


def trusted_policy():
    data = json.loads(POLICY_FILE.read_text())
    if (set(data) != {"format", "rocq_version", "axioms", "indices_not_mattering"}
            or data["format"] != 1 or data["rocq_version"] != "9.3.0"
            or any(not isinstance(data[field], list)
                   or any(not isinstance(name, str) for name in data[field])
                   or len(set(data[field])) != len(data[field])
                   for field in ["axioms", "indices_not_mattering"])):
        raise ValueError("Invalid evaluator-owned CI trust policy")
    return data


def trusted_axioms():
    return sorted(trusted_policy()["axioms"])


def trusted_inductives():
    return sorted(trusted_policy()["indices_not_mattering"])
