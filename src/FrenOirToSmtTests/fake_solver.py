#!/usr/bin/env python3
"""Owned transport-path controls; never used as solver evidence."""
import os
import subprocess
import sys
import time

mode = sys.argv[1]
if mode != 'hold-input':
    sys.stdin.buffer.read()
if mode == 'unknown':
    print('unknown')
elif mode == 'unsupported':
    print('unsupported')
elif mode == 'suspended':
    import signal
    os.kill(os.getpid(), signal.SIGSTOP)
elif mode == 'nonzero':
    print('unsat', flush=True)
    print('owned failure', file=sys.stderr, flush=True)
    sys.exit(7)
elif mode == 'protocol':
    print('unsat\n(error "owned failure")')
elif mode == 'stderr':
    print('unsat')
    print('owned diagnostic', file=sys.stderr)
elif mode == 'flood':
    os.write(1, b'x' * 100000)
elif mode == 'bytes':
    os.write(1, b'\xff')
elif mode == 'closed':
    os.close(1)
    os.close(2)
    time.sleep(60)
elif mode == 'descendant':
    subprocess.Popen([sys.executable, '-c', 'import time;time.sleep(60)'])
elif mode in ['sleep', 'hold-input']:
    time.sleep(60)
