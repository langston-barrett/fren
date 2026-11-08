#!/usr/bin/env python3
"""Exercise exported identity through the actual observer and budget session."""
import json, os, pathlib, subprocess, sys
from overlay import create
here = pathlib.Path(__file__).resolve().parent
bins = here / '.lake/build/bin'
work = pathlib.Path(sys.argv[1]).resolve(); work.mkdir(parents=True, exist_ok=False)
prefix = work / 'compiler'; (prefix / 'bin').mkdir(parents=True)
compiler = prefix / 'bin/lean'; compiler.write_text('#!/bin/sh\ncase "$1" in --print-prefix) echo '+str(prefix)+';; --version) echo fixture;; --githash) echo fixture-hash;; *) exit 0;; esac\n'); compiler.chmod(0o755)
source = work / 'Tiny.lean'; source.write_text('def x := 1\n')
setup = work / 'setup.json'; setup.write_text('{}')
overlay = create(work / 'overlay', compiler, bins / 'heavy_observe')
args = ['Tiny.lean', '--setup', 'setup.json']
env = dict(os.environ)
for k in ('HEAVY_BUDGET_DIR', 'HEAVY_OBSERVE_DIR'): env.pop(k, None)
def call(cmd):
 p = subprocess.run(cmd, cwd=work, env=env, capture_output=True, text=True, timeout=15)
 assert p.returncode == 0, (cmd, p.returncode, p.stderr)
 return p
call([str(overlay/'bin/lean'), *args])
record, = (overlay/'records').glob('process-*.json'); raw = json.loads(record.read_text())
request = work/'request.json'; request.write_text(json.dumps(dict(real_compiler=str(compiler), args=args, cutoff_monotonic_ns=0, recent_count=1, minimum_samples=1, records=[str(record)])))
row = call([str(bins/'compiler_advice'), '--manifest', '--padding-kib', '123', str(request)]).stdout
fields = row.rstrip('\n').split('\t'); demand = int(fields[-1]); manifest = work/'manifest'; manifest.write_text(row)
legacy = work/'legacy'; legacy.write_text('\t'.join([fields[0], fields[1], fields[-1]])+'\n')
count = 0
def gate(label, selected, argv=args, origin='explicit-unknown-fallback', wanted=900000):
 global count
 count += 1
 records = work / ('records-'+label); env['HEAVY_OBSERVE_DIR'] = str(records)
 call([str(bins/'budget_session'), str(work/('session-'+label)), '2000000', '100000', '900000', '5000', str(selected), '--', '/bin/sh', '-c', '"$@"; exit $?', 'sh', str(overlay/'bin/lean'), *argv])
 r, = [json.loads(p.read_text()) for p in records.glob('process-*.json')]
 assert (r['request_provenance'], r['requested_reservation_kib']) == (origin, wanted), (label, r)
 assert r['child_present'] and r['raw_wait_status'] == 0 and r['gate_errno'] == 0 and r['wrapper_code'] == 0, r
 return r
results = {}
results['matched'] = gate('matched', manifest, origin='explicit-cohort-request', wanted=demand)
setup.write_text('{"changed":true}')
results['legacy_changed_setup'] = gate('legacy', legacy, origin='explicit-source-request', wanted=demand)
results['changed_setup'] = gate('setup', manifest)
setup.unlink()
results['unavailable_setup'] = gate('unavailable-setup', manifest)
setup.write_text('{}')
results['changed_argv'] = gate('argv', manifest, args + ['-Dfoo=bar'])
compiler.write_text(compiler.read_text()+'# changed\n'); compiler.chmod(0o755)
results['changed_compiler'] = gate('compiler', manifest)
compiler.write_text(compiler.read_text().replace('# changed\n','')); compiler.chmod(0o755)
identity = fields[3]; boot = raw['boot_id']; encoded = str(len(boot.encode())) + ':' + boot.encode().hex()
assert identity.endswith(encoded)
changed = work/'boot'; changed.write_text('\t'.join(fields[:3]+[identity[:-len(encoded)] + '1:78', fields[-1]])+'\n')
results['changed_boot'] = gate('boot', changed)
missing = work/'missing'; missing.write_text('\t'.join(fields[:3]+[identity[:-len(encoded)], fields[-1]])+'\n')
results['missing_identity'] = gate('missing', missing)
source.write_text(source.read_text()+'-- changed\n')
results['changed_source'] = gate('source', manifest)
(work/'results.json').write_text(json.dumps(results, indent=2)+'\n')
print('passed', count)
