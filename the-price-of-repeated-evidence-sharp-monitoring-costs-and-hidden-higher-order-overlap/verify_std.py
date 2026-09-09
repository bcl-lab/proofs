#!/usr/bin/env python3
"""Fresh Lean-only build and axiom audit of the three combinatorial modules."""
from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, tempfile
root=Path(__file__).resolve().parent
logs=root/'verification_logs'/'std_extension'
logs.mkdir(parents=True,exist_ok=True)
modules=['ParityCore','OverlapReconstruction','ParityIncidence']
expected=[]
for module in modules:
    source=(root/(module+'.lean')).read_text()
    if re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*(?:axiom|opaque)\s',source,re.M):
        raise SystemExit('Disallowed construct in '+module)
    namespace=re.search(r'^namespace (\w+)',source,re.M).group(1)
    expected.extend(namespace+'.'+n for n in re.findall(r'^(?:theorem|lemma) ([\w.]+)',source,re.M))
lean=shutil.which('lean')
if not lean: raise SystemExit('Lean must be on PATH')
def run(args,name,env):
    p=subprocess.run([lean,*args],cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (logs/name).write_text(p.stdout)
    return p
with tempfile.TemporaryDirectory(prefix='lean-checked-') as tmp:
    env=dict(os.environ,LEAN_PATH=tmp)
    v=run(['--version'],'lean_version.log',env)
    if v.returncode or 'version 4.19.0' not in v.stdout: raise SystemExit('Requires Lean 4.19.0')
    for m in modules:
        p=run([m+'.lean','-o',str(Path(tmp)/(m+'.olean'))],m+'.log',env)
        if p.returncode: raise SystemExit('Rejected '+m)
    a=run(['StdProofAudit.lean'],'axioms.log',env)
    if a.returncode: raise SystemExit('Axiom audit failed')
    axioms={n:sorted(x.strip() for x in ax.replace('\n',' ').split(',') if x.strip())
      for n,ax in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",a.stdout,re.S)}
    axioms.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",a.stdout)})
    if set(axioms)!=set(expected): raise SystemExit('Incomplete inventory')
    if any(set(ax)-{'propext','Classical.choice','Quot.sound'} for ax in axioms.values()):
        raise SystemExit('Unexpected axiom dependency')
    neg=run(['tests/NegativeControl.lean'],'negative_control.log',env)
    if neg.returncode==0 or "tactic 'decide' proved that the proposition" not in neg.stdout:
        raise SystemExit('Negative control failed')
result={'status':'PASS for the three listed modules only','lean_version':v.stdout.strip(),
 'modules':modules,'declarations':len(expected),'new_declarations':sum(n.startswith('ParityIncidence.') for n in expected),
 'fresh_build':True,'axiom_audit_exit_code':a.returncode,'negative_control_exit_code':neg.returncode,
 'axioms':axioms,'source_sha256':{m+'.lean':hashlib.sha256((root/(m+'.lean')).read_bytes()).hexdigest() for m in modules},
 'full_paper_verified':False,'mathlib_probability_drafts_verified':False}
(logs/'verification_result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in {'axioms','source_sha256'}},indent=2))
