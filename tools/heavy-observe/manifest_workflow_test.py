import json, os, pathlib, shutil, subprocess, sys
root=pathlib.Path(__file__).resolve().parents[2]; out=pathlib.Path(sys.argv[1]).resolve(); out.mkdir(parents=True,exist_ok=False)
pkg=out/'pkg'; pkg.mkdir(); (pkg/'lakefile.toml').write_text('name = "tiny"\nenableArtifactCache = false\n[[lean_lib]]\nname = "Tiny"\n'); (pkg/'lean-toolchain').write_text((root/'lean-toolchain').read_text()); source=pkg/'Tiny.lean'; source.write_text('import Std\ndef tiny : Nat := 42\n')
env=os.environ.copy(); env.update(HOME=str(out/'home'), TMPDIR=str(out), LAKE_CACHE_DIR=str(out/'cache'), FREN_BUILD_FALLBACK_KIB='550000', HEAVY_TEST_STATE_CAPTURE=str(out), PYTHONPATH=str(root/'tools/heavy-observe/test-hooks')); env.pop('FREN_BUILD_REQUESTS_FILE',None)
def build(label):
 shutil.rmtree(pkg/'.lake/build',ignore_errors=True)
 before=set(out.glob('fren-build-*'))
 p=subprocess.run([str(root/'scripts/fren-build'),'+Tiny'],cwd=pkg,env=env,capture_output=True,text=True,timeout=60)
 (out/(label+'.stdout')).write_text(p.stdout); (out/(label+'.stderr')).write_text(p.stderr); (out/(label+'.status')).write_text(str(p.returncode)+'\n')
 assert p.returncode==0, p.stderr
 state,=set(out.glob('fren-build-*'))-before
 records=list((state/'state/overlay/records').glob('process-*.json'))
 files=[(x,json.loads(x.read_text())) for x in records if json.loads(x.read_text())['input_kind']=='file']
 assert len(files)==1, files
 return files[0]
a,ar=build('capture1'); b,br=build('capture2')
assert ar['args']==br['args'] and ar['source_before']==br['source_before'] and ar['setup_fingerprint']==br['setup_fingerprint'], (ar,br)
request={'real_compiler':ar['real_compiler'],'args':ar['args'],'cutoff_monotonic_ns':0,'recent_count':2,'minimum_samples':2,'records':[str(a),str(b)]}; (out/'request.json').write_text(json.dumps(request,indent=2))
cmd=[str(root/'tools/heavy-observe/.lake/build/bin/compiler_advice'),'--manifest','--padding-kib','100000',str(out/'request.json')]; p=subprocess.run(cmd,cwd=pkg,env=env,capture_output=True,text=True,timeout=30); (out/'export.stderr').write_text(p.stderr); (out/'export.status').write_text(str(p.returncode)+'\n'); manifest=out/'manifest.tsv'; manifest.write_text(p.stdout); assert p.returncode==0,p.stderr
expected=max(ar['peak_rss_kib'],br['peak_rss_kib'])+100000; assert p.stdout.split('\t')[-1].strip()==str(expected)
env['FREN_BUILD_REQUESTS_FILE']=str(manifest); _, selected=build('selected'); assert selected['request_provenance']=='explicit-cohort-request' and selected['requested_reservation_kib']==expected,selected
source.write_text(source.read_text()+'-- changed\n'); _, fallback=build('changed'); assert fallback['request_provenance']=='explicit-unknown-fallback' and fallback['requested_reservation_kib']==550000,fallback
(out/'summary.json').write_text(json.dumps({'capture_records':[str(a),str(b)],'selected':selected,'changed':fallback,'expected':expected,'limits':'schema 3 reports requested reservation, not independently observed held charge'},indent=2)+'\n'); print(out)

# A failed export is empty; an explicitly retained empty manifest selects fallback.
unknown = {**request, 'minimum_samples': 3}
(out/'unknown-request.json').write_text(json.dumps(unknown))
p = subprocess.run([str(root/'tools/heavy-observe/.lake/build/bin/compiler_advice'), '--manifest', '--padding-kib', '100000', str(out/'unknown-request.json')], cwd=pkg, env=env, capture_output=True, text=True, timeout=30)
(out/'unknown.stderr').write_text(p.stderr); (out/'unknown.status').write_text(str(p.returncode)+'\n')
assert p.returncode != 0 and p.stdout == '' and p.stderr
empty=out/'unknown.tsv'; empty.write_text(p.stdout); env['FREN_BUILD_REQUESTS_FILE']=str(empty)
_, unknown_row=build('unknown-fallback'); assert unknown_row['request_provenance']=='explicit-unknown-fallback' and unknown_row['requested_reservation_kib']==550000
