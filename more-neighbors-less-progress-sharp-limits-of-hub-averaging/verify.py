#!/usr/bin/env python3
"""Fresh Lean compilation and axiom audit of the hub-averaging formalization."""
from pathlib import Path
from datetime import datetime, timezone
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import argparse, hashlib, json, re, subprocess, sys
ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'verification'
OUT.mkdir(exist_ok=True)
MODULES = ['HubAveraging','CutAndBudget','Network','GraphMoments','RandomSweep',
           'PermutationMean','EdgeProcess','GraphCut','SpectralBridge','GraphSpectral',
           'UniformPolicy','Minimax','RandomCut','SpectrumEndpoints','EqualBudget',
           'GapRange','Asymptotic']
ALLOW = {'propext','Classical.choice','Quot.sound'}
PIN = 'c44e0c8ee63ca166450922a373c7409c5d26b00b'
CLAIMS = {
 'Lemma 1': ['hubMeanLoss_local_identity','coefficient_bounds'],
 'Proposition 2': ['uniform_graph_operator','exists_uniform_spectral_endpoints'],
 'Theorem 3': ['bipartite_policy_lower_bound','exact_bipartite_minimax'],
 'Corollary 4': ['edgeWorst_bound','edge_budget_exponential','equal_budget_separation_graph','vanishing_separation'],
 'Proposition 5': ['arbitrary_random_cut_bound','cutMaximum_le'],
}

def strip_comments(s):
    out=[]; i=0; depth=0; line=False
    while i<len(s):
        if line:
            if s[i]=='\n': line=False; out.append('\n')
            i+=1; continue
        if depth:
            if s[i:i+2]=='/-': depth+=1; i+=2
            elif s[i:i+2]=='-/': depth-=1; i+=2
            else: i+=1
            continue
        if s[i:i+2]=='/-': depth=1; i+=2
        elif s[i:i+2]=='--': line=True; i+=2
        else: out.append(s[i]); i+=1
    return ''.join(out)

def run(args, log):
    p=subprocess.run(args,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (OUT/log).write_text(p.stdout)
    if p.returncode:
        print(p.stdout,flush=True)
        raise RuntimeError(f'{args} exited {p.returncode}; see verification/{log}')
    return p.stdout

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--fetch-cache',action='store_true',help='Download the pinned dependency cache first')
    ap.add_argument('--jobs',type=int,default=2,choices=range(1,5),help='Concurrent proof modules, default 2')
    args=ap.parse_args()
    names=[]; deps={}; mathlib=set()
    for module in MODULES:
        src=strip_comments((ROOT/(module+'.lean')).read_text())
        bad=re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|run_elab)\b|#eval|skipKernelTC',src)
        if bad: raise RuntimeError(f'Forbidden construct in {module}: {bad.group()}')
        names.extend('HubAveraging.'+n for n in re.findall(r'^theorem\s+(\w+)',src,re.M))
        imports=re.findall(r'^import\s+([\w.]+)',src,re.M)
        deps[module]=set(imports)&set(MODULES)
        mathlib.update(n for n in imports if n.startswith('Mathlib.'))
    assert names and len(names)==len(set(names))
    if args.fetch_cache:
        print('Fetching pinned dependency objects',flush=True)
        run(['lake','exe','cache','get',*sorted(mathlib)],'cache.log')
    version=run(['lake','env','lean','--version'],'lean_version.log').strip()
    if 'version 4.19.0' not in version: raise RuntimeError('Expected Lean 4.19.0, got '+version)
    commit=run(['git','-C','.lake/packages/mathlib','rev-parse','HEAD'],'mathlib_commit.log').strip()
    if commit!=PIN: raise RuntimeError('Mathlib revision does not match the pin')
    run(['git','-C','.lake/packages/mathlib','diff','--exit-code','--',
         'Mathlib','lakefile.lean','lake-manifest.json','lean-toolchain'],'mathlib_source_diff.log')
    audit=''.join('import '+m+'\n' for m in MODULES)+'\n'+''.join('#print axioms '+n+'\n' for n in names)
    (ROOT/'Audit.lean').write_text(audit)
    builddir=ROOT/'.lake/build/lib/lean'
    builddir.mkdir(parents=True,exist_ok=True)
    for m in MODULES: (builddir/(m+'.olean')).unlink(missing_ok=True)
    print(f'Fresh compilation of {len(MODULES)} proof modules',flush=True)
    pending=set(MODULES); complete=set(); running={}
    def compile_one(m):
        run(['lake','env','lean','-DwarningAsError=true','-o',
             str(Path('.lake/build/lib/lean')/(m+'.olean')),m+'.lean'],m+'.log')
        return m
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            for m in MODULES:
                if m in pending and deps[m]<=complete and len(running)<args.jobs:
                    running[pool.submit(compile_one,m)]=m; pending.remove(m)
            if not running: raise RuntimeError('Cyclic or unresolved module imports: '+str(pending))
            finished,_=wait(running,return_when=FIRST_COMPLETED)
            for fut in finished:
                m=fut.result(); complete.add(m); del running[fut]
                print('ACCEPTED '+m,flush=True)
    (OUT/'build.log').write_text('\n'.join(m+': ACCEPTED' for m in MODULES)+'\n')
    print('Auditing every theorem dependency',flush=True)
    output=run(['lake','env','lean','Audit.lean'],'axioms.log')
    found={}
    for name,raw in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",output,re.S):
        found[name]=set(re.findall(r'[A-Za-z_][\w.]*',raw))
    for name in re.findall(r"'([^']+)' does not depend on any axioms",output): found[name]=set()
    for n in names:
        if n not in found: raise RuntimeError('Missing axiom result for '+n)
        if found[n]-ALLOW: raise RuntimeError('Unexpected axioms for '+n+': '+str(found[n]-ALLOW))
    for label,items in CLAIMS.items():
        for n in items:
            if 'HubAveraging.'+n not in found: raise RuntimeError('Missing manuscript entry point '+label+': '+n)
    files=[m+'.lean' for m in MODULES]+['Audit.lean','verify.py','lean-toolchain','lakefile.toml','lake-manifest.json']
    hashes={n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in files}
    result={'status':'PASS','timestamp_utc':datetime.now(timezone.utc).isoformat(),
      'lean_version':version,'mathlib_commit':PIN,'module_count':len(MODULES),'theorem_count':len(names),
      'compilation':'Fresh direct Lean compilation with warningAsError=true; dependency-ordered, at most '+str(args.jobs)+' modules concurrently',
      'allowed_axioms':sorted(ALLOW),'theorems':[{'name':n,'axioms':sorted(found[n])} for n in names],
      'source_sha256':hashes,'numbered_manuscript_results':CLAIMS,'all_five_numbered_results_formalized':True,
      'full_manuscript_formalized':False,'independent_external_checker_run':False,
      'scope_note':'The five numbered mathematical results are formalized. Numerical experiments, plots, novelty, reference interpretation, and every ancillary example are not all formalized.'}
    (OUT/'verification_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(f'PASS: {len(names)} supporting theorems in {len(MODULES)} modules; all five numbered results; no disallowed axiom dependencies',flush=True)

if __name__=='__main__':
    try: main()
    except Exception as e:
        (OUT/'verification_results.json').write_text(json.dumps({'status':'FAIL','error':str(e)},indent=2)+'\n')
        print('FAIL:',e,file=sys.stderr);sys.exit(1)
