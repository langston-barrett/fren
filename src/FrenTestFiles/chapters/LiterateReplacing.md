# A setting that a chapter it reads replaces

This chapter denies `dead_code`, and the chapter it reads allows it
before any item, so the denial is in effect at none:

```fren
set_option fren.lint.dead_code "deny"
#fren_md "LiterateReplaced.md"
```
