#!/usr/bin/python3
"""Owned process failures at an isolated tree's fixed solver path."""
from pathlib import Path
import os
import sys
import time

sys.stdin.buffer.read()
mode = Path(__file__).with_suffix('.mode').read_text()
if mode == 'unknown':
    print('unknown')
elif mode == 'unsupported':
    print('unsupported')
elif mode == 'nonzero':
    print('unsat')
    sys.exit(7)
elif mode == 'stderr':
    print('unsat')
    print('owned diagnostic', file=sys.stderr)
elif mode == 'protocol':
    print('unsat\n(error "owned diagnostic")')
elif mode == 'bytes':
    os.write(1, b'\xff')
elif mode == 'flood':
    os.write(1, b'x' * 100000)
elif mode == 'timeout':
    time.sleep(60)
else:
    sys.exit(9)
