# Contributing to Fren

How Fren is built and tested, and where it is going.

New requirements are added to the reference first, and checked with Fren
before they are implemented. The pages of the reference that contain `fren`
blocks are read by thin Lean files in `src/Reqs` with `#fren_md`, so `lake
build` checks them: `src/Reqs/Lang.lean` reads every page in `src/Reqs/Lang/`
except Modules and Instances, which, like the other chapters, have their own
Lean file and module. `lake test` checks the same pages with the `fren`
command. Pages that are only prose, such as this one, are not read.

- [Architecture](Architecture.md): design principles and libraries
- [Testing](Testing.md): the kinds of tests and where they live
- [Roadmap](Roadmap.md): what comes next, and open questions
