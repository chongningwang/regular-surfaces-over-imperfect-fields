#!/usr/bin/env python3
"""Build and audit the Geonormal modules: Example ex:p19 at p = 19 and Proposition prop:p11
at p = 11."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parent
REPORT = ROOT / "verification" / "geonormal"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# Pin each final statement and the project definitions it reaches, as printed by
# GeonormalAudit.lean. Update a value only when that statement is meant to change.
FINGERPRINTS = {
    "Example": "80 constants, 17510596471059313213",
    "Final": "87 constants, 3506630080531362575",
    "P11Example": "95 constants, 1979517444288427197",
    "P11Final": "101 constants, 8835163795215819243",
}
CLASSICAL_INTERFACE_DECLARATIONS = {
    "SurfaceLib.Canonical.GeneralClassicalAdjunction.normalizedDuality",
    "SurfaceLib.Canonical.TopDuality.finitePresentation",
    "SurfaceLib.Canonical.TopDuality.trace",
    "SurfaceLib.Canonical.TopDuality.perfect",
    "SurfaceLib.Canonical.tracePairing",
    "SurfaceLib.Canonical.Cohomology",
}


def source_inventory():
    modules = {}
    for prefix in ("Geonormal", "SurfaceLib"):
        for path in [ROOT / f"{prefix}.lean", *sorted((ROOT / prefix).rglob("*.lean"))]:
            modules[".".join(path.relative_to(ROOT).with_suffix("").parts)] = path
    reached = set()
    pending = ["Geonormal", "SurfaceLib"]
    while pending:
        name = pending.pop()
        if name in reached:
            continue
        reached.add(name)
        pending.extend(name for name in re.findall(r"^import ([\w.]+)\s*$",
                                                   modules[name].read_text(), re.M)
                       if name in modules and name not in reached)
    if set(modules) != reached:
        raise SystemExit(f"Unbuilt source modules: {sorted(set(modules) - reached)}")
    files = [*modules.values(), ROOT / "GeonormalAudit.lean"]
    forbidden = re.compile(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b")
    for path in files:
        hit = forbidden.search(path.read_text())
        if hit:
            raise SystemExit(f"Forbidden token {hit.group()!r}: {path.relative_to(ROOT)}")
    return files


def run_logged(args, filename):
    result = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, check=False)
    (REPORT / filename).write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(f"{' '.join(args)} failed; see {REPORT / filename}\n"
                           + "\n".join(result.stdout.splitlines()[-35:]))
    return result.stdout


def main():
    REPORT.mkdir(parents=True, exist_ok=True)
    # Do not leave a stale success report after any failure.
    for name in ("status.txt", "manifest.json"):
        (REPORT / name).unlink(missing_ok=True)
    files = source_inventory()
    run_logged(["lake", "build", "Geonormal", "SurfaceLib"], "build.log")
    audit = run_logged(["lake", "env", "lean", "GeonormalAudit.lean"], "axioms.log")
    if "sorryAx" in audit:
        raise RuntimeError("Unfinished proof in transitive dependencies")
    expected = re.findall(r"^#print axioms (\S+)\s*$",
                          (ROOT / "GeonormalAudit.lean").read_text(), re.M)
    reports = re.findall(
        r"^'([^\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
        audit, re.M | re.S)
    if [name for name, _ in reports] != expected:
        raise RuntimeError("Missing or reordered theorem dependency reports")
    seen = {a.strip() for _, axs in reports for a in axs.split(",") if a.strip()}
    if seen - ALLOWED_AXIOMS:
        raise RuntimeError(f"Unexpected logical dependencies: {sorted(seen - ALLOWED_AXIOMS)}")
    counts = re.findall(r"All project declarations audited: (\d+)\.", audit)
    if len(counts) != 1 or int(counts[0]) < len(expected):
        raise RuntimeError("Incomplete environment audit")
    for label, pinned in FINGERPRINTS.items():
        found = re.findall(rf"^{label} statement fingerprint: ([^\n]+)\.$", audit, re.M)
        if found != [pinned]:
            raise RuntimeError(f"Unpinned or changed {label} statement: {found}")
    interface = re.findall(r"^Classical input interface: (.+)$", audit, re.M)
    if len(interface) != 1:
        raise RuntimeError("Missing or duplicated classical input interface report")
    entries = json.loads(interface[0])
    if {entry.get("declaration") for entry in entries} != CLASSICAL_INTERFACE_DECLARATIONS:
        raise RuntimeError("Classical input declarations have changed")
    manifest = {
        "verification": "PASS",
        "unconditional_example_theorem": "Geonormal.p19_example",
        "final_theorem": "Geonormal.p19_canonical",
        "final_theorem_classical_inputs": ["SurfaceLib.Canonical.GeneralClassicalAdjunction"],
        "scope": "Example ex:p19 of the geonormal manuscript at p = 19. Unconditional: X is a "
                 "projective, proper, integral, regular surface over k = F_19(c) with "
                 "H^0(X, O_X) = k, not smooth over k, whose absolute differentials are locally "
                 "free of rank three and whose normalized differential line is trivial. "
                 "Conditional on GeneralClassicalAdjunction: X has a canonical sheaf, and every "
                 "canonical sheaf of X is trivial.",
        "p11_unconditional_theorem": "Geonormal.P11.p11_example",
        "p11_final_theorem": "Geonormal.P11.p11_canonical",
        "p11_scope": "Proposition prop:p11 of the geonormal manuscript at p = 11. Unconditional: "
                     "X is a projective, proper, integral, regular surface over k = F_11(c) with "
                     "H^0(X, O_X) = k, not geometrically normal (its base change to "
                     "k' = k(c^(1/11)) is not normal), whose absolute differentials are locally "
                     "free of rank three and whose normalized differential line is trivial. "
                     "Conditional on GeneralClassicalAdjunction: X has a canonical sheaf, and every "
                     "canonical sheaf of X is trivial.",
        "classical_inputs": [{
            "interface": "SurfaceLib.Canonical.GeneralClassicalAdjunction",
            "parameter": "adjunction",
            "consumers": ["Geonormal.canonicalSheaf_trivial", "Geonormal.p19_canonical",
                          "Geonormal.P11.canonicalSheaf_trivial", "Geonormal.P11.p11_canonical"],
            "ingredients": ["functorial lci adjunction and presentation-independent gluing",
                            "normalized determinant comparison",
                            "top-degree Serre duality expressed in Ext cohomology"],
            "specializes_to": "SurfaceLib.Canonical.ClassicalAdjunction "
                              "(p = 5, r = 2; GeneralClassicalAdjunction.toClassicalAdjunction)",
            "documentation": "SurfaceLib/Canonical/README.md",
            "checked_types": entries,
        }],
        "logical_axioms": sorted(seen),
        "statement_fingerprints": FINGERPRINTS,
        "declarations_audited": int(counts[0]),
        "sources": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in sorted(files)},
        "remaining": ["formal proof of the classical input",
                      "the geometric singular point of type A_18 and its uniqueness; only "
                      "non-smoothness over k is proved",
                      "the elliptic fibration over P^1_k",
                      "for prop:p11, the genus-one fibration over P^1_k (described in the README "
                      "only)"],
    }
    (REPORT / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    status = (f"PASS: {len(files)} source files; {counts[0]} project declarations audited.\n"
              f"Example statement fingerprint: {FINGERPRINTS['Example']}.\n"
              f"Final statement fingerprint: {FINGERPRINTS['Final']}.\n"
              f"P11Example statement fingerprint: {FINGERPRINTS['P11Example']}.\n"
              f"P11Final statement fingerprint: {FINGERPRINTS['P11Final']}.\n"
              "Geonormal.p19_example is unconditional: X is a regular projective integral\n"
              "surface over k = F_19(c) with H^0(X, O_X) = k, not smooth over k, with locally\n"
              "free absolute differentials of rank three and trivial differential line.\n"
              "Geonormal.p19_canonical adds the canonical sheaf, conditional on\n"
              "GeneralClassicalAdjunction and on nothing else.\n"
              "Geonormal.P11.p11_example is unconditional: X is a regular projective integral\n"
              "surface over k = F_11(c) with H^0(X, O_X) = k, not geometrically normal, with\n"
              "locally free absolute differentials of rank three and trivial differential line.\n"
              "Geonormal.P11.p11_canonical adds the canonical sheaf, conditional on\n"
              "GeneralClassicalAdjunction and on nothing else.\n")
    (REPORT / "status.txt").write_text(status)
    print(status, end="")


if __name__ == "__main__":
    main()
