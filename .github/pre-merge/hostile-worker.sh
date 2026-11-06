#!/usr/bin/env bash
set -euo pipefail
for key in GH_TOKEN GITHUB_TOKEN ACTIONS_RUNTIME_TOKEN ACTIONS_CACHE_URL GITHUB_ENV GITHUB_OUTPUT GITHUB_PATH; do
  [ -z "${!key:-}" ] || { echo "REACHED: environment $key"; exit 1; }
done
[ "${GITHUB_STEP_SUMMARY:-}" = /work/.lake/slow-summary.md ]
# A host process with a fake token is deliberately live throughout the test.
if grep -als 'slow-host-only-token' /proc/[0-9]*/environ 2>/dev/null | grep -q .; then
  echo 'REACHED: host process environment'; exit 1
fi
for file in "$1" /var/run/docker.sock /home/runner/.credentials; do
  [ ! -r "$file" ] || { echo 'REACHED: runner file'; exit 1; }
done
if (echo escaped > /etc/slow-escape) 2>/dev/null; then echo 'REACHED: root'; exit 1; fi
if (echo escaped > /trusted/slow-escape) 2>/dev/null; then echo 'REACHED: trusted scripts'; exit 1; fi
grep -q '^CapEff:[[:space:]]*0000000000000000$' /proc/self/status
grep -q '^NoNewPrivs:[[:space:]]*1$' /proc/self/status
[ "$(id -u)" != 0 ]
printf allowed > /work/changed
# No orphan may write after the wrapper returns and collection starts.
(sleep 3; printf orphan > /work/orphan) &
echo 'worker boundaries passed'
