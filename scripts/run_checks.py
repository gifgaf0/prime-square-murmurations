#!/usr/bin/env python3
"""Run the numerical checks listed in scripts/checks.tsv and compare their output with the committed logs.

Usage: python3 scripts/run_checks.py [--quick] [--only NAME[,NAME...]]

Every check runs in a fresh copy of proof/ under build/proof-run/, so the committed logs are not touched.
New output goes to build/logs/<name>.log.  Where a reference log exists, every number printed on every line is
compared with the reference: printed values must agree to a relative 1e-6, and quantities that are pure
round-off (both below 1e-9 in absolute value, e.g. "diff 1.6e-14") count as agreeing.  Timing fields
("(17s)", "[0s]", `time` output) are ignored.  A check may declare known differences in checks.tsv
(a printed value NEW that is allowed to replace the logged value REF); each is documented in the README.  Checks with no reference log must exit with status 0.
"""
import os, re, shutil, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROOF = ROOT / "proof"
BUILD = ROOT / "build"
RUN = BUILD / "proof-run"
LOGS = BUILD / "logs"

NUM = re.compile(r"[-+]?(?:\d+\.\d*|\.\d+|\d+)(?:[eE][-+]?\d+)?")
TIMING = [re.compile(p) for p in (r"\(\d+(?:\.\d+)?s\)", r"\[\d+(?:\.\d+)?s\]", r"\(\s*\d+(?:\.\d+)?s\s*\)")]
SKIP_LINE = re.compile(r"^(real|user|sys)\s|^PARI stack size")
REL, ABS = 1e-6, 1e-9


def load_checks():
    rows = []
    for line in (ROOT / "scripts" / "checks.tsv").read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        name, wd, cmd, ref, tier, *rest = line.split("\t")
        known = set()
        for pair in (rest[0].split(",") if rest and rest[0].strip() else []):
            new, old = pair.split("=>")
            known.add((new.strip(), old.strip()))
        rows.append(dict(name=name, wd=wd, cmd=cmd, ref=None if ref == "-" else ref, tier=tier, known=known))
    return rows


def clean(text):
    out = []
    for ln in text.splitlines():
        if SKIP_LINE.search(ln) or not ln.strip():
            continue
        for t in TIMING:
            ln = t.sub("", ln)
        out.append(ln)
    return out


def close(a, b):
    x, y = float(a), float(b)
    if x == y or (abs(x) < ABS and abs(y) < ABS):
        return True
    return abs(x - y) <= REL * max(abs(x), abs(y))


def compare(new_text, ref_text, known=frozenset()):
    """Return (mismatches, number of known differences seen); no mismatches = agreement."""
    new, ref = clean(new_text), clean(ref_text)
    problems, seen = [], 0
    if len(new) != len(ref):
        problems.append(f"line count differs: {len(new)} new vs {len(ref)} reference")
    for i, (a, b) in enumerate(zip(new, ref), 1):
        na, nb = NUM.findall(a), NUM.findall(b)
        if len(na) != len(nb) or NUM.sub("#", a).split() != NUM.sub("#", b).split():
            problems.append(f"line {i} differs in shape:\n      new: {a.strip()}\n      ref: {b.strip()}")
            continue
        seen += sum((x, y) in known for x, y in zip(na, nb))
        bad = [(x, y) for x, y in zip(na, nb) if not close(x, y) and (x, y) not in known]
        if bad:
            problems.append(f"line {i}: " + ", ".join(f"{x} vs {y}" for x, y in bad[:4]) + f"\n      new: {a.strip()}")
    return problems, seen


def main():
    args = sys.argv[1:]
    quick = "--quick" in args
    only = None
    if "--only" in args:
        only = set(args[args.index("--only") + 1].split(","))
    checks = [c for c in load_checks() if (not quick or c["tier"] == "quick") and (only is None or c["name"] in only)]

    if RUN.exists():
        shutil.rmtree(RUN)
    shutil.copytree(PROOF, RUN, ignore=shutil.ignore_patterns("*.log", "*.json", "*.md", "__pycache__"))
    LOGS.mkdir(parents=True, exist_ok=True)

    failed, t_all = [], time.time()
    for c in checks:
        t0 = time.time()
        print(f"[{c['name']}] {c['cmd']}  (in proof/{c['wd']})", flush=True)
        log = LOGS / f"{c['name']}.log"
        env = dict(os.environ, PYTHONHASHSEED="0", PYTHONDONTWRITEBYTECODE="1")
        with open(log, "w") as fh:
            rc = subprocess.call(c["cmd"].split(), cwd=RUN / c["wd"], stdout=fh, stderr=subprocess.STDOUT, env=env)
        dt = time.time() - t0
        if rc != 0:
            failed.append(c["name"])
            print(f"    FAIL: exit status {rc} after {dt:.0f}s; see {log.relative_to(ROOT)}", flush=True)
            continue
        if c["ref"] is None:
            print(f"    ok: ran cleanly in {dt:.0f}s (no reference log; output in {log.relative_to(ROOT)})", flush=True)
            continue
        problems, seen = compare(log.read_text(), (PROOF / c["ref"]).read_text(), c["known"])
        if problems:
            failed.append(c["name"])
            print(f"    FAIL: output differs from proof/{c['ref']} ({len(problems)} problem(s)):", flush=True)
            for p in problems[:10]:
                print("    - " + p, flush=True)
        else:
            note = f" (apart from {seen} documented known difference(s): {sorted(c['known'])})" if seen else ""
            print(f"    ok: matches proof/{c['ref']}{note} in {dt:.0f}s", flush=True)

    print(f"\n{len(checks) - len(failed)}/{len(checks)} numerical checks passed in {time.time() - t_all:.0f}s", flush=True)
    if failed:
        print("failed: " + ", ".join(failed))
        sys.exit(1)


if __name__ == "__main__":
    main()
