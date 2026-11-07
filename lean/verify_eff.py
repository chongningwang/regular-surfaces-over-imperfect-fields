#!/usr/bin/env python3
"""Build and audit the Eff modules and the final example, reporting its classical inputs."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parent
REPORT = ROOT / "verification" / "eff"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# Pin the implemented geometric statement and its reachable project definitions.
STATEMENT_FINGERPRINT = "97 constants, 12985887948955488478"
CANONICAL_STATEMENT_FINGERPRINT = "113 constants, 7640908887198818297"
FREENESS_STATEMENT_FINGERPRINT = "60 constants, 5363109288789624739"
TORSOR_STATEMENT_FINGERPRINT = "109 constants, 11022967480670452798"
# The order-five example: each statement, in the label used by EffAudit.lean.
EXAMPLE_FINGERPRINTS = {
    "Regularity": "78 constants, 16958915980947374023",
    "Order": "114 constants, 5764549006072577869",
    "CanonicalOrder": "121 constants, 5023760894144107675",
    "Nonnormal": "82 constants, 15494484949319092419",
    "Projective": "83 constants, 8179171503934481086",
    "Albanese": "86 constants, 10845012968927165029",
    "Example": "118 constants, 8774172229539891270",
    "Final": "126 constants, 3333105092890281862",
}
CLASSICAL_INTERFACE_DECLARATIONS = {
    "SurfaceLib.Abelian.ClassicalRationalRigidity.constant",
    "SurfaceLib.Canonical.ClassicalAdjunction.normalizedDuality",
    "SurfaceLib.Canonical.TopDuality.finitePresentation",
    "SurfaceLib.Canonical.TopDuality.trace",
    "SurfaceLib.Canonical.TopDuality.perfect",
    "SurfaceLib.Canonical.tracePairing",
    "SurfaceLib.Canonical.Cohomology",
    "SurfaceLib.MuFive.ClassicalDiagonalizableQuotient.torsor",
    "SurfaceLib.MuFive.HomogeneousCover.size",
    "SurfaceLib.MuFive.HomogeneousCover.value",
    "SurfaceLib.MuFive.HomogeneousCover.weight",
    "SurfaceLib.MuFive.HomogeneousCover.eigen",
    "SurfaceLib.MuFive.HomogeneousCover.nonzero",
    "SurfaceLib.MuFive.HomogeneousCover.spans",
    "SurfaceLib.MuFive.group",
    "SurfaceLib.MuFive.pullGroup",
    "SurfaceLib.MuFive.PointOver",
    "SurfaceLib.MuFive.pullPoint",
    "SurfaceLib.MuFive.Torsor.finite",
    "SurfaceLib.MuFive.Torsor.flat",
    "SurfaceLib.MuFive.Torsor.surjective",
    "SurfaceLib.MuFive.Torsor.act",
    "SurfaceLib.MuFive.Torsor.one_act",
    "SurfaceLib.MuFive.Torsor.mul_act",
    "SurfaceLib.MuFive.Torsor.natural",
    "SurfaceLib.MuFive.Torsor.principal",
    "SurfaceLib.MuFive.Torsor.rankFive",
    "SurfaceLib.MuFive.chartSection",
    "SurfaceLib.MuFive.GradedTorsor.toTorsor",
    "SurfaceLib.MuFive.GradedTorsor.weights",
}


def source_inventory():
    modules = {}
    for prefix in ("Eff", "SurfaceLib"):
        for path in [ROOT / f"{prefix}.lean", *sorted((ROOT / prefix).rglob("*.lean"))]:
            modules[".".join(path.relative_to(ROOT).with_suffix("").parts)] = path
    reached = set()
    pending = ["Eff", "SurfaceLib"]
    while pending:
        name = pending.pop()
        if name in reached:
            continue
        reached.add(name)
        source = modules[name].read_text()
        pending.extend(name for name in re.findall(r"^import ([\w.]+)\s*$", source, re.M)
                       if name in modules and name not in reached)
    if set(modules) != reached:
        raise SystemExit(f"Unbuilt source modules: {sorted(set(modules) - reached)}")
    files = [*modules.values(), ROOT / "EffAudit.lean"]
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


def checked_classical_interface(audit):
    reports = re.findall(r"^Classical input interface: (.+)$", audit, re.M)
    if len(reports) != 1:
        raise RuntimeError("Missing or duplicated mathematical-input interface report")
    entries = json.loads(reports[0])
    if not isinstance(entries, list) or len(entries) != len(CLASSICAL_INTERFACE_DECLARATIONS):
        raise RuntimeError("Incomplete mathematical-input interface report")
    if {entry.get("declaration") for entry in entries} != CLASSICAL_INTERFACE_DECLARATIONS:
        raise RuntimeError("Mathematical-input declarations have changed")
    if any(not isinstance(entry.get("type"), str) or not entry["type"].strip()
           for entry in entries):
        raise RuntimeError("Missing checked mathematical-input type")
    return entries


def main():
    REPORT.mkdir(parents=True, exist_ok=True)
    # Do not leave a stale success report after any failure.
    for name in ("status.txt", "manifest.json"):
        (REPORT / name).unlink(missing_ok=True)
    files = source_inventory()
    run_logged(["lake", "build", "Eff", "SurfaceLib"], "build.log")
    audit = run_logged(["lake", "env", "lean", "EffAudit.lean"], "axioms.log")
    if "sorryAx" in audit:
        raise RuntimeError("Unfinished proof in transitive dependencies")
    expected = re.findall(r"^#print axioms (\S+)\s*$", (ROOT / "EffAudit.lean").read_text(), re.M)
    reports = re.findall(
        r"^'([^\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
        audit, re.M | re.S)
    if [name for name, _ in reports] != expected:
        raise RuntimeError("Missing or reordered theorem dependency reports")
    seen = {a.strip() for _, axs in reports for a in axs.split(",") if a.strip()}
    if seen - ALLOWED_AXIOMS:
        raise RuntimeError(f"Unexpected logical dependencies: {sorted(seen - ALLOWED_AXIOMS)}")
    counts = re.findall(r"All project declarations audited: (\d+)\.", audit)
    fingerprints = re.findall(r"Eff statement fingerprint: ([^\n]+)\.", audit)
    if len(counts) != 1 or int(counts[0]) < len(expected) or len(fingerprints) != 1:
        raise RuntimeError("Incomplete environment audit or statement fingerprint")
    if STATEMENT_FINGERPRINT is None or fingerprints != [STATEMENT_FINGERPRINT]:
        raise RuntimeError(f"Unpinned or changed Eff statement: {fingerprints}")
    canonical_fingerprints = re.findall(r"Canonical statement fingerprint: ([^\n]+)\.", audit)
    if (CANONICAL_STATEMENT_FINGERPRINT is None or
            canonical_fingerprints != [CANONICAL_STATEMENT_FINGERPRINT]):
        raise RuntimeError(f"Unpinned or changed canonical statement: {canonical_fingerprints}")
    freeness_fingerprints = re.findall(r"Freeness statement fingerprint: ([^\n]+)\.", audit)
    if (FREENESS_STATEMENT_FINGERPRINT is None or
            freeness_fingerprints != [FREENESS_STATEMENT_FINGERPRINT]):
        raise RuntimeError(f"Unpinned or changed freeness statement: {freeness_fingerprints}")
    torsor_fingerprints = re.findall(r"Torsor statement fingerprint: ([^\n]+)\.", audit)
    if (TORSOR_STATEMENT_FINGERPRINT is None or
            torsor_fingerprints != [TORSOR_STATEMENT_FINGERPRINT]):
        raise RuntimeError(f"Unpinned or changed torsor statement: {torsor_fingerprints}")
    example_fingerprints = {}
    for label, pinned in EXAMPLE_FINGERPRINTS.items():
        found = re.findall(rf"^{label} statement fingerprint: ([^\n]+)\.$", audit, re.M)
        if found != [pinned]:
            raise RuntimeError(f"Unpinned or changed {label} statement: {found}")
        example_fingerprints[label] = found[0]
    classical_interface = checked_classical_interface(audit)
    manifest = {
        "verification": "PASS", "full_example_complete": True,
        "final_theorem": "Eff.case_C_p5",
        "final_theorem_classical_inputs": ["SurfaceLib.Canonical.ClassicalAdjunction",
                                           "SurfaceLib.Abelian.ClassicalRationalRigidity"],
        "unconditional_example_theorem": "Eff.y_example",
        "scope": "The example ex:case-C-p5. Unconditional: Y is a projective integral regular "
                 "surface over ell = F_5(s_1,s_2) with constants ell, geometrically non-normal, "
                 "whose differential line has exact order five. Conditional on the two listed "
                 "general theorems: every canonical sheaf of Y has exact order five, and the "
                 "Albanese morphism of Y is the structure morphism to Spec ell. Separately: "
                 "explicit derivations and weights, four-chart nonvanishing, a conditional "
                 "canonical-sheaf comparison for the input surface, and a conditional "
                 "rank-five mu-five torsor, none of which the final theorem uses",
        "classical_inputs": [{
            "interface": "SurfaceLib.Abelian.ClassicalRationalRigidity",
            "parameter": "rigidity",
            "consumers": ["Eff.y_albanese_trivial", "Eff.y_albanese_is_base", "Eff.case_C_p5"],
            "ingredients": ["maps from an affine plane to an abelian variety are constant "
                            "(Milne, Abelian Varieties v2.00, I.3.9 and I.3.10)",
                            "reduction to an algebraically closed field by fpqc descent "
                            "of morphisms"],
            "documentation": "SurfaceLib/Abelian/README.md",
            "checked_types": [entry for entry in classical_interface
                              if entry["declaration"].startswith("SurfaceLib.Abelian.")],
        }, {
            "interface": "SurfaceLib.Canonical.ClassicalAdjunction",
            "parameter": "adjunction",
            "consumers": ["Eff.Canonical.canonicalSheaf_trivial",
                          "Eff.Canonical.exists_trivial_canonicalSheaf",
                          "Eff.canonicalSheaf_tensorPower_trivial_iff",
                          "Eff.canonicalSheaf_order_five", "Eff.case_C_p5"],
            "ingredients": ["functorial lci adjunction and presentation-independent gluing",
                            "normalized determinant comparison",
                            "top-degree Serre duality expressed in Ext cohomology"],
            "documentation": "SurfaceLib/Canonical/README.md",
            "checked_types": [entry for entry in classical_interface
                              if entry["declaration"].startswith("SurfaceLib.Canonical.")],
        }, {
            "interface": "SurfaceLib.MuFive.ClassicalDiagonalizableQuotient",
            "parameter": "descent",
            "consumers": ["Eff.rho_has_gradedTorsor", "Eff.rho_is_muFiveTorsor",
                          "Eff.rho_action_weights", "Eff.rho_flat", "Eff.rho_rankFive"],
            "ingredients": ["geometric realization of the characteristic-five grading",
                            "SGA 3 VIII 4.1, 4.6 and 5.1 graded-algebra torsor theorem",
                            "invariant principal-localization compatibility and gluing",
                            "finite flat rank-five descent"],
            "documentation": "SurfaceLib/GroupScheme/README.md",
            "checked_types": [entry for entry in classical_interface
                              if entry["declaration"].startswith("SurfaceLib.MuFive.")],
        }],
        "unconditional_geometric_theorem": "Eff.quotient_properties",
        "unconditional_nonvanishing_theorem": "Eff.sChartEuler_nowhereVanishing",
        "conditional_torsor_theorem": "Eff.rho_is_muFiveTorsor",
        "conditional_action_weight_theorem": "Eff.rho_action_weights",
        "logical_axioms": sorted(seen),
        "canonical_statement_fingerprint": canonical_fingerprints[0],
        "freeness_statement_fingerprint": freeness_fingerprints[0],
        "torsor_statement_fingerprint": torsor_fingerprints[0],
        "example_statement_fingerprints": example_fingerprints,
        "declarations_audited": int(counts[0]), "statement_fingerprint": fingerprints[0],
        "sources": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in sorted(files)},
        "remaining": ["formal proofs of the classical inputs",
                      "K_Y numerically trivial is not stated separately: numerical equivalence "
                      "is not formalized, and it is immediate from the torsion of K_Y",
                      "IsProjectiveOver is Proj of a finitely generated graded algebra with "
                      "degree-zero part the field; generation in degree one is not proved",
                      "invariant coordinate presentation of the chart ring, unused by the "
                      "final theorem",
                      "mu-five action on Y's canonical comparison, unused by the final theorem"],
    }
    (REPORT / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    status = (f"PASS: {len(files)} source files; {counts[0]} project declarations audited.\n"
              f"Statement fingerprint: {fingerprints[0]}.\n"
              "The implemented quotient-properties theorem is unconditional.\n"
              "The input-surface canonical trivialization is conditional on ClassicalAdjunction.\n"
              "The rank-five mu-five torsor is conditional on ClassicalDiagonalizableQuotient.\n"
              "The classical interfaces and independent data fields are exported in manifest.json.\n"
              f"Canonical statement fingerprint: {canonical_fingerprints[0]}.\n"
              f"Freeness statement fingerprint: {freeness_fingerprints[0]}.\n"
              f"Torsor statement fingerprint: {torsor_fingerprints[0]}.\n"
              f"Final statement fingerprint: {example_fingerprints['Final']}.\n"
              "Eff.y_example is unconditional: Y is a regular projective integral surface over\n"
              "ell with constants ell, geometrically non-normal, with differential line of\n"
              "exact order five.\n"
              "Eff.case_C_p5 adds the canonical sheaf and the Albanese morphism, conditional on\n"
              "ClassicalAdjunction and ClassicalRationalRigidity, and on nothing else.\n"
              "It does not use ClassicalDiagonalizableQuotient.\n")
    (REPORT / "status.txt").write_text(status)
    print(status, end="")


if __name__ == "__main__":
    main()
