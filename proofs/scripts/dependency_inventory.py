"""Record the exact same-prover source closure used by this proof project."""

from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[1]
workspace = root.parents[1]
roots = {
    "CategoricalBayesianNetworksProofs": root,
    "FiniteKernelsProofs": workspace / "FiniteKernels.jl/proofs",
    "BayesianNetworksProofs": workspace / "BayesianNetworks.jl/proofs",
}
seen = set()
external = set()


def visit(path):
    path = path.resolve()
    if path in seen:
        return
    seen.add(path)
    for line in path.read_text().splitlines():
        match = re.match(r"\s*(?:public\s+)?import\s+(.+)$", line)
        if not match:
            continue
        for module in match[1].split():
            prefix = module.split(".")[0]
            if prefix in roots:
                visit(roots[prefix] / (module.replace(".", "/") + ".lean"))
            else:
                external.add(module)


visit(root / "CategoricalBayesianNetworksProofs.lean")
visit(root / "Audit.lean")
visit(root / "CertificateMain.lean")
records = [
    {
        "path": str(path.relative_to(workspace)),
        "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
    }
    for path in sorted(seen)
]
manifest = json.loads((root / "lake-manifest.json").read_text())
result = {
    "description": "Exact transitive same-prover Lean source closure; external libraries pinned below.",
    "sources": records,
    "external_imports": sorted(external),
    "git_dependencies": [
        {"name": p["name"], "rev": p["rev"], "inputRev": p.get("inputRev")}
        for p in manifest["packages"]
        if p["type"] == "git"
    ],
}
(root / "DEPENDENCIES.json").write_text(json.dumps(result, indent=2) + "\n")
print(f"Recorded {len(records)} same-prover Lean source files and pinned external dependencies.")
