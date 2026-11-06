#!/usr/bin/env python3
"""Build the project, audit axioms, and check the pinned statement fingerprint."""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent
REPORT = ROOT / "verification"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# Fingerprint of the main statement printed by Audit.lean. Update it only when the
# statement of exists_theorem61_omega_rationalBase or a definition it uses is meant to change.
STATEMENT_FINGERPRINT = "43 constants, 2700237008541851014"


def run_logged(args, filename):
    result = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, check=False)
    (REPORT / filename).write_text(result.stdout)
    if result.returncode:
        (REPORT / "status.txt").write_text(f"FAIL: {' '.join(args)}; see {filename}.\n")
        print("\n".join(result.stdout.splitlines()[-40:]))
        print(f"Full log: {REPORT / filename}")
        raise SystemExit(result.returncode)
    return result.stdout


def main():
    REPORT.mkdir(exist_ok=True)
    (REPORT / "status.txt").unlink(missing_ok=True)
    files = [ROOT / "Red61.lean", ROOT / "Audit.lean", *sorted((ROOT / "Red61").rglob("*.lean"))]
    imports = set(re.findall(r"^import (Red61\.[\w.]+)\s*$", (ROOT / "Red61.lean").read_text(), re.M))
    missing = {".".join(file.relative_to(ROOT).with_suffix("").parts) for file in files[2:]} - imports
    if missing:
        raise SystemExit(f"Source modules missing from the default build: {sorted(missing)}")
    forbidden = re.compile(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b")
    for file in files:
        hit = forbidden.search(file.read_text())
        if hit:
            raise SystemExit(f"Forbidden token {hit.group()!r} in {file.relative_to(ROOT)}")
    run_logged(["lake", "build"], "build.log")
    audit = run_logged(["lake", "env", "lean", "Audit.lean"], "axioms.log")
    if "sorryAx" in audit:
        raise SystemExit("Placeholder proof detected in transitive axiom dependencies")
    expected = re.findall(r"^#print axioms (\S+)\s*$", (ROOT / "Audit.lean").read_text(), re.M)
    reports = re.findall(
        r"^'([^\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
        audit, re.S | re.M)
    names = [name for name, _ in reports]
    if names != expected:
        differences = [(i, wanted, got) for i, (wanted, got) in
                       enumerate(zip(expected, names)) if wanted != got]
        raise SystemExit(f"Axiom audit mismatch: expected {len(expected)} declarations, "
                         f"found {len(names)}; first differences: {differences[:5]}")
    seen = set()
    for _, report in reports:
        seen.update(x.strip() for x in report.split(",") if x.strip())
    if seen - ALLOWED_AXIOMS:
        raise SystemExit(f"Unexpected axioms: {sorted(seen - ALLOWED_AXIOMS)}")
    all_audit = re.findall(r"All project declarations audited: (\d+)\.", audit)
    if len(all_audit) != 1 or int(all_audit[0]) < len(reports):
        raise SystemExit("Missing or incomplete audit of all project declarations")
    fingerprint = re.findall(r"Statement fingerprint: ([^\n]+)\.", audit)
    if fingerprint != [STATEMENT_FINGERPRINT]:
        raise SystemExit(f"Statement fingerprint {fingerprint} differs from the pinned "
                         f"{STATEMENT_FINGERPRINT!r}: the main statement or a definition it "
                         "uses has changed")
    result = (f"PASS: {len(files)} Lean source files; main theorem audited.\n"
              f"All project declarations audited: {all_audit[0]}.\n"
              f"Axioms: {', '.join(sorted(seen))}.\n"
              f"Statement fingerprint matches the pinned value ({STATEMENT_FINGERPRINT}).\n"
              "Main result: exists_theorem61_omega_rationalBase (Red61/Theorem61.lean), VERIFIED unconditionally. Over the prescribed k = FractionRing (MvPolynomial (Fin 2) (ZMod 5)) it gives a proper, integral, Noetherian, regular surface of dimension two with the prescribed global constants, not geometrically reduced.\n"
              "The sheaf omega is defined as Hom(f* (exterior square of absolute base differentials), exterior fourth power of absolute surface differentials). It is isomorphic to the structure sheaf and has Euler degree zero on every proper integral curve. The absolute differential sheaf is locally free of rank four (IsLocallyFreeOfRank).\n"
              "The default build contains exactly the import closure of Red61.Theorem61.\n"
              "Identification of omega with the Serre dualizing sheaf and comparison with divisor classes are NOT verified in this project.\n")
    (REPORT / "status.txt").write_text(result)
    print(result, end="")


if __name__ == "__main__":
    main()
