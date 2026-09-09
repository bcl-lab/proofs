"""Rebuild the formal proofs, audit dependencies, and reject a false control.

Requires the pinned Lean toolchain, Lake and the Mathlib cache. This script
does not install dependencies or alter the Lean kernel. It uses Python's
standard library only.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
MODULES = sorted(p.stem for p in ROOT.glob("*.lean") if p.stem != "Audit")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def run(args, logfile, expected_success=True):
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    result = subprocess.run(args, cwd=ROOT, text=True, capture_output=True, env=env)
    output = result.stdout + result.stderr
    (ROOT / logfile).write_text(output)
    if expected_success and result.returncode != 0:
        raise RuntimeError(f"{args} failed; see {logfile}")
    return result.returncode, output


def main():
    inventory = []
    forbidden = re.compile(
        r"\b(?:sorry|admit|native_decide|unsafe|axiom|opaque)\b|"
        r"debug\.skipKernelTC|Lean\.ofReduceBool|Lean\.trustCompiler|implemented_by"
    )
    for module in MODULES:
        source = (ROOT / f"{module}.lean").read_text()
        if forbidden.search(source):
            raise RuntimeError(f"Unexpected admission or trust feature in {module}")
        if "set_option autoImplicit false" not in source:
            raise RuntimeError(f"Implicit variable creation not disabled in {module}")
        for name in re.findall(r"^theorem (\w+)", source, re.M):
            inventory.append({"name": f"EvidenceFusion.{name}", "module": module})
    if len({t['name'] for t in inventory}) != len(inventory):
        raise RuntimeError("Duplicate declaration names in source inventory")
    # Topological order keeps this resource-intensive build sequential.
    pending, ordered = set(MODULES), []
    while pending:
        ready = sorted(m for m in pending if not (
            set(re.findall(r'^import (\w+)$', (ROOT/f'{m}.lean').read_text(), re.M)) & pending))
        if not ready:
            raise RuntimeError("Local import cycle")
        ordered.extend(ready)
        pending.difference_update(ready)
    audit = "\n".join(f"import {m}" for m in MODULES)
    audit += "\n\nset_option autoImplicit false\n\n"
    audit += "\n".join(f"#check {t['name']}\n#print axioms {t['name']}" for t in inventory)
    (ROOT / "Audit.lean").write_text(audit + "\n")
    # Only this project's generated build directory is removed. Dependencies
    # remain in .lake/packages and are not deleted or rebuilt unnecessarily.
    build = ROOT / ".lake" / "build"
    audit_only = '--audit-only' in sys.argv
    if build.exists() and not audit_only:
        shutil.rmtree(build)
    _, version = run(["lake", "env", "lean", "--version"], "lean_version.log")
    if "version 4.19.0," not in version:
        raise RuntimeError("The active Lean version does not match lean-toolchain")
    if audit_only:
        # Resume only the audit of a demonstrably completed fresh build.
        # This is useful after fixing an audit-output parser, without
        # unnecessarily rebuilding already checked and unchanged proofs.
        build_output = (ROOT / 'build.log').read_text()
        for module in ordered:
            obj = build/'lib'/'lean'/f'{module}.olean'
            if not obj.exists() or obj.stat().st_mtime < (ROOT/f'{module}.lean').stat().st_mtime:
                raise RuntimeError(f'Fresh object missing or older than source: {module}')
            if not re.search(r'\bBuilt '+re.escape(module)+r'(?:\s|$)', build_output):
                raise RuntimeError(f'Fresh compilation receipt missing: {module}')
        print('Resuming the axiom audit of the completed fresh build', flush=True)
    else:
        build_output = ""
        for index, module in enumerate(ordered, 1):
            print(f"Fresh build {index}/{len(ordered)}: {module}", flush=True)
            _, output = run(["lake", "build", module], f"fresh_{module}.log")
            build_output += output
            (ROOT / "build.log").write_text(build_output)
    _, audit_output = run(["lake", "env", "lean", "-j", "1", "Audit.lean"], "axiom_audit.log")
    warnings = [line for line in (build_output + audit_output).splitlines() if "warning:" in line]
    benign = ("unused variable", "automatically included section variable(s) unused",
              "try 'simp at ", "Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice")
    if any(not any(pattern in line for pattern in benign) for line in warnings):
        raise RuntimeError("Unexpected warning; review before certifying")
    found = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit_output))
    found.update({name: '' for name in re.findall(r"'([^']+)' does not depend on any axioms", audit_output)})
    for t in inventory:
        if t["name"] not in found:
            raise RuntimeError(f"Missing axiom record for {t['name']}")
        axioms = {a.strip() for a in found[t["name"]].split(",") if a.strip()}
        if not axioms <= ALLOWED_AXIOMS:
            raise RuntimeError(f"Unexpected axiom in {t['name']}: {axioms}")
        t["axioms"] = sorted(axioms)
    if set(found) != {t["name"] for t in inventory}:
        raise RuntimeError("The audited declarations differ from the source inventory")
    code, negative = run(
        ["lake", "env", "lean", "-j", "1", "negative_controls/FalseReportCount.lean"],
        "negative_control.log", expected_success=False)
    if code == 0 or "unsolved goals" not in negative or "⊢ False" not in negative:
        raise RuntimeError("The false report-count control was not rejected as expected")
    paths = [ROOT / f"{m}.lean" for m in MODULES]
    paths += [ROOT / "Audit.lean", ROOT / "lakefile.toml", ROOT / "lean-toolchain", ROOT / "lake-manifest.json"]
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    result = {
        "status": "passed",
        "verification_date": "2026-09-09",
        "lean_version": version.strip(),
        "mathlib_commit": "c44e0c8ee63ca166450922a373c7409c5d26b00b",
        "formal_theorem_count": len(inventory),
        "fresh_project_build": True,
        "reviewed_benign_linter_warning_count": len(warnings),
        "reviewed_benign_linter_warnings": warnings,
        "admitted_proofs": 0,
        "custom_axioms": 0,
        "native_evaluation_axioms": 0,
        "allowed_foundational_axioms": sorted(ALLOWED_AXIOMS),
        "false_claim_control": "rejected as expected",
        "theorems": inventory,
        "sha256": hashes,
        "scope": "Formal formulations of S1 through S15 and supporting results. See coverage.json for exact assumptions, formulations and exclusions.",
        "independent_kernel_checker_run": False,
    }
    (ROOT / "verification_results.json").write_text(json.dumps(result, indent=2) + "\n")
    (ROOT / "theorem_inventory.json").write_text(json.dumps(inventory, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ["status", "formal_theorem_count", "admitted_proofs", "custom_axioms", "false_claim_control"]}, indent=2))


if __name__ == "__main__":
    main()
