"""Read example data against the evaluator-owned independent JSON Schema.

The validator implements only the keywords used by this schema, rejects unknown
keywords, and resolves local references only. No remote schema/code is loaded.
Other tooling can validate the same document with a full JSON Schema validator.
"""
from pathlib import Path
import re

import check

MANIFEST = check.REPO / "verification/adversarial-examples.json"
SCHEMA = check.REPO / "verification/adversarial-examples.schema.json"


def validate(value, schema, root=None, path="$"):
    root = schema if root is None else root
    supported = {"$schema", "$id", "title", "description", "$defs", "$ref", "type",
                 "const", "enum", "minimum", "pattern", "properties", "required",
                 "additionalProperties", "propertyNames", "items", "minItems", "uniqueItems"}
    if set(schema) - supported:
        raise ValueError("Unsupported example schema keywords: " + str(sorted(set(schema) - supported)))
    if "$ref" in schema:
        reference = schema["$ref"]
        if not reference.startswith("#/"):
            raise ValueError("Only local example schema references are supported")
        target = root
        for part in reference[2:].split("/"):
            target = target[part.replace("~1", "/").replace("~0", "~")]
        validate(value, target, root, path)
    types = {"object": dict, "array": list, "string": str, "integer": int}
    if "type" in schema and type(value) is not types[schema["type"]]:
        raise ValueError(path + ": expected " + schema["type"])
    if "const" in schema and value != schema["const"]:
        raise ValueError(path + ": unexpected value")
    if "enum" in schema and value not in schema["enum"]:
        raise ValueError(path + ": unexpected value")
    if "minimum" in schema and value < schema["minimum"]:
        raise ValueError(path + ": value below minimum")
    if "pattern" in schema and re.search(schema["pattern"], value) is None:
        raise ValueError(path + ": invalid name or path")
    if isinstance(value, dict):
        if set(schema.get("required", [])) - set(value):
            raise ValueError(path + ": missing required fields")
        properties = schema.get("properties", {})
        for name, child in value.items():
            if "propertyNames" in schema:
                validate(name, schema["propertyNames"], root, path + ".<key>")
            if name in properties:
                validate(child, properties[name], root, path + "." + name)
            elif schema.get("additionalProperties") is False:
                raise ValueError(path + ": unexpected field " + name)
            elif isinstance(schema.get("additionalProperties"), dict):
                validate(child, schema["additionalProperties"], root, path + "." + name)
    if isinstance(value, list):
        if len(value) < schema.get("minItems", 0):
            raise ValueError(path + ": too few entries")
        if schema.get("uniqueItems") and any(child in value[:i] for i, child in enumerate(value)):
            raise ValueError(path + ": duplicate entries")
        if "items" in schema:
            for i, child in enumerate(value):
                validate(child, schema["items"], root, path + f"[{i}]")


def load(path=MANIFEST):
    schema = check.decoded(check.read_regular(SCHEMA, 64 * 1024), "example schema")
    manifest = check.decoded(check.read_regular(Path(path), 128 * 1024), "example manifest")
    validate(manifest, schema)
    if any(set(profile) != set(check.DEFAULT_LIMITS) for profile in manifest["profiles"].values()):
        raise ValueError("Example resource schema differs from the checker protocol")
    names = set()
    for example in manifest["examples"]:
        if example["name"] in names:
            raise ValueError("Duplicate example name: " + example["name"])
        names.add(example["name"])
        if example["profile"] not in manifest["profiles"]:
            raise ValueError("Unknown example resource profile: " + example["profile"])
        for field in ("spec", "candidate"):
            target = (check.REPO / example[field]).resolve()
            correct_kind = target.is_file() if field == "spec" else target.is_dir()
            if not target.is_relative_to(check.REPO) or not correct_kind:
                raise ValueError("Invalid example " + field + ": " + example[field])
    return manifest
