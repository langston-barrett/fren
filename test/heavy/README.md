`forecast.jsonl` contains 320 observations of completed jobs from the local
heavy log, captured for the first Lean forecast kernel. Only forecast
fields remain: kinds are replaced consistently by anonymous identifiers,
and completion times share an arbitrary integral origin. Relative times
and peaks are retained; no paths, commands or machine identities remain.

`heavyPrediction` replays prefixes and time windows against the active
Python forecast and the Lean kernel. Its adapter converts finite Python
timestamps to exact integer ticks using their binary ratios, so neither
rounding nor a change of time unit changes cutoff eligibility. Handwritten
cases also exercise malformed fields, cutoff endpoints and tied times.
The kernel consumes decoded observations; this does not port JSON or file
I/O into the scheduler.
