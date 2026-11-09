#!/usr/bin/env python3
"""One bounded walking SMT subprocess. No shell, services or shared solver."""
import json
import os
import selectors
import signal
import subprocess
import sys
import time


cancel_requested = False


def request_cancel(_signum, _frame):
    # Record rather than raise: cancellation cannot interrupt Popen before its
    # child handle is assigned, or interrupt the owned kill/reap cleanup.
    global cancel_requested
    cancel_requested = True


def run(request):
    started = time.monotonic()
    command = request['command']
    script = request['script'].encode('utf-8')
    wall = request['wall_ms']
    cap = request['output_bytes']
    result = dict(command=command, exit_code=None, stdout='', stderr='', stdout_hex='', stderr_hex='', elapsed_ms=0,
                  reason='', kind='error')
    if (not isinstance(command, list) or not command or
            not all(isinstance(a, str) and '\x00' not in a for a in command) or
            not 0 < wall <= 10000 or not 0 < cap <= 1048576 or
            not 0 < request['input_bytes'] <= 1048576):
        result['reason'] = 'invalid bounded transport configuration'
        return result
    if len(script) > request['input_bytes']:
        result.update(kind='resource', reason='script input limit')
        return result
    child = None
    streams = {'stdout': bytearray(), 'stderr': bytearray()}
    reason = ''
    try:
        child = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, start_new_session=True)
        deadline = started + wall / 1000
        with selectors.DefaultSelector() as sel:
            for stream, role in [(child.stdin, 'stdin'), (child.stdout, 'stdout'), (child.stderr, 'stderr')]:
                os.set_blocking(stream.fileno(), False)
                sel.register(stream, selectors.EVENT_WRITE if role == 'stdin' else selectors.EVENT_READ, role)
            sent = 0
            while sel.get_map():
                if cancel_requested:
                    reason = 'transport cancelled'
                    break
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    reason = 'outer wall deadline'
                    break
                for key, _ in sel.select(min(remaining, .05)):
                    stream, role = key.fileobj, key.data
                    if role == 'stdin':
                        try:
                            sent += os.write(stream.fileno(), script[sent:sent + 4096])
                        except BrokenPipeError:
                            sent = len(script)
                        if sent == len(script):
                            sel.unregister(stream)
                            stream.close()
                    else:
                        chunk = os.read(stream.fileno(), 4096)
                        if not chunk:
                            sel.unregister(stream)
                            stream.close()
                            continue
                        available = cap - sum(map(len, streams.values()))
                        streams[role].extend(chunk[:max(available, 0)])
                        if len(chunk) > available:
                            reason = 'combined solver output limit'
                            break
                if reason:
                    break
            # A child can close both output streams and keep computing.
            while not reason and child.poll() is None:
                if cancel_requested:
                    reason = 'transport cancelled'
                elif time.monotonic() >= deadline:
                    reason = 'outer wall deadline'
                else:
                    time.sleep(.01)
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        reason = 'transport error: ' + str(exc)
    finally:
        if child is not None:
            # The new session belongs solely to this query. Also clean up an
            # owned descendant that outlives a leader or keeps pipes open.
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            child.wait()
            for stream in [child.stdin, child.stdout, child.stderr]:
                if stream is not None:
                    stream.close()
            result['exit_code'] = child.returncode
    if cancel_requested:
        reason = 'transport cancelled'
    try:
        result['stdout'] = streams['stdout'].decode('utf-8', errors='strict')
        result['stderr'] = streams['stderr'].decode('utf-8', errors='strict')
    except UnicodeDecodeError:
        reason = 'transport error: non-UTF-8 solver output'
        result['stdout'] = streams['stdout'].decode('utf-8', errors='replace')
        result['stderr'] = streams['stderr'].decode('utf-8', errors='replace')
    result['stdout_hex'] = streams['stdout'].hex()
    result['stderr_hex'] = streams['stderr'].hex()
    result['elapsed_ms'] = int((time.monotonic() - started) * 1000)
    result['reason'] = reason
    if reason:
        result['kind'] = 'resource' if reason in ['outer wall deadline', 'combined solver output limit', 'transport cancelled'] else 'error'
    else:
        result['kind'] = 'finished'
    return result


def main():
    signal.signal(signal.SIGTERM, request_cancel)
    signal.signal(signal.SIGINT, request_cancel)
    try:
        raw = sys.stdin.buffer.read(8 * 1048576 + 1)
        if len(raw) > 8 * 1048576:
            raise ValueError('transport request size')
        result = run(json.loads(raw))
        print(json.dumps(result, ensure_ascii=True))
    except (ValueError, KeyError, TypeError) as exc:
        print(json.dumps(dict(command=[], exit_code=None, stdout='', stderr='', stdout_hex='', stderr_hex='', elapsed_ms=0,
                             reason='invalid helper request: ' + str(exc), kind='error')))


if __name__ == '__main__':
    main()
