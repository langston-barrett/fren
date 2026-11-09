"""Capture completed success evidence before the real wrapper removes it.

Only harnesses that set HEAVY_TEST_STATE_CAPTURE load this hook. The actual
private directory is still removed by the unmodified cleanup operation.
"""
import os
import pathlib
import shutil
import sys
import tempfile

capture = os.environ.get('HEAVY_TEST_STATE_CAPTURE')
if capture and pathlib.Path(sys.argv[0]).name == 'fren-build':
    original = shutil.rmtree
    def capture_before_delete(path, *args, **kwargs):
        path = pathlib.Path(path)
        if path.name.startswith('.active-') and path.parent.name == 'build-state':
            dest = pathlib.Path(tempfile.mkdtemp(prefix='fren-build-', dir=capture))
            shutil.copytree(path, dest, dirs_exist_ok=True, symlinks=True)
            print(f'fren-build: test state snapshot: {dest}', file=sys.stderr, flush=True)
        return original(path, *args, **kwargs)
    shutil.rmtree = capture_before_delete
