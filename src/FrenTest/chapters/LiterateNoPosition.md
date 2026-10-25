# A chapter that reports about items with no position

Lean code, which only the Lean front end reads, logs about an item of
another chapter and about one of the Lean file, with no position.

```fren
run_cmd Fren.logAbout `deep_gate .missing m!"about an item with no position" .information
run_cmd Fren.logAbout `lean_gate .missing m!"about an item with no position" .information
```
