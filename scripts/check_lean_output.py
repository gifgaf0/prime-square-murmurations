#!/usr/bin/env python3
"""Check the output of `lake env lean PrimeSquareMurmurations/LocalDensities.lean`.

Usage: python3 scripts/check_lean_output.py build/logs/lean_axioms.log

Passes when
  * the source contains no `sorry`, `admit` or `native_decide` (outside comments),
  * there are 26 `#print axioms` reports, one for each `#print axioms` command in the file,
  * every report depends only on propext, Classical.choice and Quot.sound,
  * every theorem named in Section 9 of the paper is among the reported declarations.
"""
import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "lean" / "PrimeSquareMurmurations" / "LocalDensities.lean"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_REPORTS = 26
PAPER_THEOREMS = ["nuSum_odd", "nuSum_two", "hasSum_E_odd", "hasSum_E_two", "KS_formula", "local_identity_odd",
                  "local_identity_two", "global_identity", "Gc_eq", "sum_norm_gc_le", "tendsto_sum_wA",
                  "poisson_coprime", "theoremB"]


def strip_comments(src):
    src = re.sub(r"/-.*?-/", "", src, flags=re.S)
    return re.sub(r"--[^\n]*", "", src)


def main():
    out = Path(sys.argv[1]).read_text()
    code = strip_comments(SRC.read_text())
    errors = []

    for word in ("sorry", "admit", "native_decide"):
        if re.search(rf"\b{word}\b", code):
            errors.append(f"source contains `{word}`")
    n_cmds = len(re.findall(r"^#print axioms\s", code, flags=re.M))
    if n_cmds != EXPECTED_REPORTS:
        errors.append(f"expected {EXPECTED_REPORTS} `#print axioms` commands in the source, found {n_cmds}")
    if re.search(r"\berror\b", out):
        errors.append("Lean reported an error")

    # Lean prints:  'Foo.bar' depends on axioms: [propext, Classical.choice, Quot.sound]
    # (possibly wrapped over several lines), or  'Foo.bar' does not depend on any axioms
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out, flags=re.S)
    reports += [(n, "") for n in re.findall(r"'([^']+)' does not depend on any axioms", out)]
    if len(reports) != EXPECTED_REPORTS:
        errors.append(f"expected {EXPECTED_REPORTS} axiom reports in Lean's output, found {len(reports)}")
    for name, axs in reports:
        used = {a.strip() for a in axs.replace("\n", " ").split(",") if a.strip()}
        extra = used - STANDARD
        if extra:
            errors.append(f"{name} depends on non-standard axioms: {sorted(extra)}")
    short = {n.split(".")[-1] for n, _ in reports}
    missing = [t for t in PAPER_THEOREMS if t not in short]
    if missing:
        errors.append("theorems from the paper with no axiom report: " + ", ".join(missing))

    for name, axs in sorted(reports):
        print(f"  {name}: [{' '.join(axs.split())}]")
    if errors:
        print("LEAN CHECK FAILED:")
        for e in errors:
            print("  - " + e)
        sys.exit(1)
    print(f"Lean check passed: {len(reports)} declarations, all using only {', '.join(sorted(STANDARD))}; "
          "no sorry / admit / native_decide.")


if __name__ == "__main__":
    main()
