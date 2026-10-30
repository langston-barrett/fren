# Lint settings in a chapter

The Lean file that reads this chapter allows `upper_case_acronyms`, and
its setting is in effect at this record type:

```fren
pub struct HTTPThing { x: Int }
```

This chapter's own setting is after its last item, so it is in effect at
none:

```fren
set_option fren.lint.dead_code "allow"
```
