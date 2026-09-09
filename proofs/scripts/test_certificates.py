"""Exercise the compiled certificate reader, including parsing and semantic failures."""

from pathlib import Path
import copy
import json
import shutil
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
binary = root / ".lake/build/bin/check_certificate"
if not binary.is_file():
    raise SystemExit("Build check_certificate before running these tests")
seed = json.loads((root / "certificate-fixtures/mixed.json").read_text())
cases = []


def mutate(name, path, value, valid=False):
    data = copy.deepcopy(seed)
    target = data
    for key in path[:-1]:
        target = target[key]
    target[path[-1]] = value
    cases.append((name, json.dumps(data), 0 if valid else 1))


def custom(name, update, valid=False):
    data = copy.deepcopy(seed)
    update(data)
    cases.append((name, json.dumps(data), 0 if valid else 1))


mutate("wrong-version", ["format"], "OpenNet.RawCertificate/v2")
custom("missing-envelope-field", lambda d: d.pop("outputs"))
custom("unknown-envelope-field", lambda d: d.update(extra=True))
mutate("count-mismatch", ["variableCount"], 4)
mutate("negative-count", ["variableCount"], -1)
mutate("string-count", ["variableCount"], "3")
mutate("boolean-count", ["variableCount"], True)
mutate("fractional-count", ["variableCount"], 3.5)
mutate("decimal-integer-token", ["variableCount"], 3.0)
mutate("non-array-variables", ["variableData"], {})
mutate("non-array-outputs", ["outputs"], None)
custom("missing-variable-field", lambda d: d["variableData"][0].pop("spaceRef"))
custom("extra-state-field", lambda d: d["variableData"][0]["stateRows"][0].update(extra=1))
mutate("bad-tag", ["mechanisms", 0, "kernelRef"], {"tag": "NamedRef", "id": "x"})
mutate("missing-tag-payload", ["mechanisms", 0, "kernelRef"], {"tag": "named"})
mutate("wrong-tag-payload-type", ["mechanisms", 0, "kernelRef"], {"tag": "named", "id": 2})
mutate("extra-tag-payload", ["mechanisms", 0, "kernelRef"], {"tag": "noRef", "id": "x"})
mutate("target-out-of-range", ["mechanisms", 0, "target"], 3)
mutate("parent-out-of-range", ["mechanisms", 0, "inputRows", 0, "varId"], 3)
mutate("foot-out-of-range", ["outputs", 0, "varId"], 3)
mutate("negative-index", ["outputs", 0, "varId"], -1)
mutate("fractional-index", ["outputs", 0, "varId"], 0.5)
mutate("boolean-index", ["outputs", 0, "varId"], False)
mutate("string-index", ["outputs", 0, "varId"], "0")
mutate("large-out-of-range-index", ["outputs", 0, "varId"], 10**80)
mutate("negative-position", ["mechanisms", 0, "inputRows", 0, "position"], -1)
mutate("zero-position", ["mechanisms", 0, "inputRows", 0, "position"], 0)
mutate("duplicate-position", ["mechanisms", 0, "inputRows", 0, "position"], 1)
mutate("position-gap", ["mechanisms", 0, "inputRows", 0, "position"], 3)
mutate("state-position-gap", ["variableData", 0, "stateRows", 0, "position"], 3)
mutate("duplicate-state-name", ["variableData", 0, "stateRows", 0, "name"], "false")
mutate("empty-states", ["variableData", 0, "stateRows"], [])
mutate("bad-rank", ["variableData", 1, "rank"], 0)
mutate("negative-rank", ["variableData", 1, "rank"], -1)
mutate("large-integral-rank", ["variableData", 1, "rank"], 10**80, valid=True)
mutate("bad-foot-reference", ["outputs", 0, "attrs", "spaceRef"], {"tag": "named", "id": "wrong"})
mutate("bad-foot-state-order", ["outputs", 0, "attrs", "states"], ["true", "false"])
custom("duplicate-input", lambda d: d["inputs"].append(copy.deepcopy(d["inputs"][0])))
mutate("duplicate-target", ["mechanisms", 1, "target"], 1)
custom("uncovered-variable", lambda d: (d["variableData"].append(copy.deepcopy(d["variableData"][2])),
                                      d.update(variableCount=4)))


def tags_and_unicode(data):
    name = 'climatic-\u00e9-\U0001f603-"quoted"'
    ref = {"tag": "pointMass", "state": "\u2603"}
    data["variableData"][0]["name"] = name
    data["variableData"][0]["spaceRef"] = ref
    for row in [data["inputs"][0], data["outputs"][0]]:
        row["attrs"]["name"] = name
        row["attrs"]["spaceRef"] = copy.deepcopy(ref)
    data["variableData"][2]["spaceRef"] = {"tag": "noRef"}
    data["mechanisms"][1]["kernelRef"] = {"tag": "policy", "decision": "harvest"}


custom("all-tags-unicode-surrogates", tags_and_unicode, valid=True)
text = json.dumps(seed)
cases += [
    ("malformed-json", text[:-1], 1),
    ("trailing-json", text + " null", 1),
    ("non-object-envelope", "[]", 1),
    ("null-envelope", "null", 1),
    ("duplicate-key", text.replace('"format":', '"format":"OpenNet.RawCertificate/v1","format":', 1), 1),
    ("escaped-duplicate-key", text.replace('"format":', '"for\\u006dat":"x","format":', 1), 1),
    ("nested-duplicate-key", text.replace('"id": "bool:x"', '"id":"old","id":"bool:x"', 1), 1),
    ("exponent-token", text.replace('"variableCount": 3', '"variableCount": 3e0', 1), 1),
    ("huge-exponent", text.replace('"variableCount": 3', '"variableCount": 3e999999999', 1), 1),
    ("lone-high-surrogate", text.replace('"name": "x"', '"name": "\\uD800"', 1), 1),
    ("lone-low-surrogate", text.replace('"name": "x"', '"name": "\\uDC00"', 1), 1),
    ("bad-surrogate-pair", text.replace('"name": "x"', '"name": "\\uD800\\u0041"', 1), 1),
    ("invalid-escape", text.replace('"name": "x"', '"name": "\\q"', 1), 1),
    ("unescaped-control", text.replace('"name": "x"', '"name": "x\nx"', 1), 1),
    ("invalid-whitespace", "\v" + text, 1),
    ("trailing-comma", text[:-1] + ",}", 1),
]

work = root / ".certificate-cases"
if work.exists():
    raise SystemExit(f"Refusing to overwrite existing test workspace: {work}")
work.mkdir()
checked = 0


def run_case(name, args, expected):
    global checked
    result = subprocess.run([str(binary), *map(str, args)], cwd=root,
                            capture_output=True, text=True, timeout=30)
    if result.returncode != expected:
        raise AssertionError(f"{name}: expected exit {expected}, got {result.returncode}\n"
                             f"{result.stdout}{result.stderr}")
    if expected == 0 and not result.stdout.startswith("valid OpenNet.RawCertificate/v1:"):
        raise AssertionError(f"{name}: missing success diagnostic")
    if expected != 0 and not result.stderr:
        raise AssertionError(f"{name}: missing error diagnostic")
    checked += 1


try:
    for fixture in ["mixed.json", "empty.json", "hidden-scalar.json"]:
        run_case(fixture, [root / "certificate-fixtures" / fixture], 0)
    for name, data, expected in cases:
        path = work / f"{name}.json"
        path.write_text(data)
        run_case(name, [path], expected)
    run_case("missing-file", [work / "absent.json"], 2)
    run_case("missing-argument", [], 2)
    run_case("extra-argument", ["a", "b"], 2)
    invalid_utf8 = work / "invalid-utf8.json"
    invalid_utf8.write_bytes(b"\xff")
    run_case("invalid-utf8", [invalid_utf8], 2)
finally:
    shutil.rmtree(work)
print(f"PASS: {checked} compiled CLI certificate cases (syntax/schema/graph/I/O)")
