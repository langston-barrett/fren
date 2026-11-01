# Writing the reference

How the chapters of the reference are written. The style is that of the
[FLS](https://rust-lang.github.io/fls/), with rule identifiers like the
[Rust Reference's](https://doc.rust-lang.org/reference/), and with more
examples, since Fren's are checked.
[Quantifiers](../Lang/Quantifiers.md) is written so.

## The split test

- A paragraph that starts with a rule identifier is a *rule*. A ```` ```fren ````
  block is the precise form of the rules around it. Rules and these blocks
  are normative; everything else is not.
- Delete everything that is not normative, and a complete spec remains.
- Delete every rule, and a readable overview remains: the introductions,
  examples and notes.

## Register

- One statement per rule, in the present tense: "The body is a `Bool`."
- Say what holds, not why. Keep "so", "that is why", "thus", "this means"
  and "in other words" out of rules. A reason goes in a rationale.
- Say "is an error" for a static error, and give its code: "is an error
  (`F0356`)".
- Use one term for one thing, and define it once, in italics, in a rule:
  "Each name that a binder declares is a *bound name*."
- Use the standard terms of the programming-language literature (lexeme,
  punctuator, bound name, instance), not invented ones.
- Write words out in prose: "procedure", "enumeration", "module". A
  keyword appears only as code: `proc`, `enum`.
- Write "Fren" in prose; `fren` only for the command and the fence tag.
- Avoid: "simply", "just", "note that", "of course", "basically",
  "essentially", "it is worth", "importantly", "we", "you", and announcing
  what follows ("Here is…", "Let's…").
- Prefer short sentences to colons and semicolons that join several facts.

## Section order

Each construct, at a `##` heading or a chapter of its own, has these
parts, in order, omitting the empty ones:

1. **Introduction**: one or two sentences in plain language, and perhaps
   a short ```` ```text ```` sketch. Not normative.
2. **Syntax**: the grammar, as a rule.
3. **Legality rules**: what is accepted, its types, its names, and the
   static errors.
4. **Dynamic semantics**: what it means.
5. **Proof obligations**: which checks the construct gives rise to, and
   what they assume, stated abstractly, without the solver's queries or
   the generated Lean.
6. **Examples**: as many as help, in checked blocks where they can be.
7. **Notes and rationale**: only where needed.

A long construct has a `###` heading for each topic, each with the
parts that apply. Rules are grouped under these labels, as bold run-in
headings (`**Legality rules**`), not headings, so that a chapter's anchors
stay those of its topics. A note or rationale is a block quote, so it needs
no label.

## What is not a rule

- The reference states what Fren accepts, what it means, which checks it
  asks, and what a user sees of them: messages and verdicts. It does not
  say how the front ends are built, nor what the solver's queries or the
  generated Lean contain.
- A statement about the implementation, such as which `Fren.Core` function
  both front ends call (`nameAlone`, `countedBetween`, `startsAtZero`),
  what each front end reads of the syntax, or how a construct appears in
  the solver's queries and the generated Lean, goes in a doc comment beside
  the function that does it. The `impl` that binds the function to its requirement
  connects the two, so the rule needs no name of a Lean function, and
  renaming one changes no identifier.

## Rule identifiers

- A rule starts with its identifier on a line of its own, then the rule
  on the next line, in one paragraph:

  ```text
  r[quantifier.limit]
  A quantifier has at most 256 instances.
  ```

- An identifier is `r[` and dot-separated segments and `]`. Each segment is
  lowercase words and digits joined by `-`. The first segment names the
  chapter's construct (`quantifier`), and each later one narrows it
  (`quantifier.guard.strict`). Spell words out, as in prose.
- The identifier of a grammar is `<construct>.syntax`, on the line
  before its block.
- An identifier is unique across the reference. `lake test` checks this
  and the format (`ruleIds`).
- An identifier is never renumbered, renamed or reused. A rule that is
  removed leaves its identifier unused. A rule that changes meaning
  gets a new identifier.
- A rule may cite another by its identifier, in backticks:
  "as `quantifier.meaning.mixed` says".

## Checked blocks

- A ```` ```fren ```` block in a chapter is part of the chapter's module,
  and `lake build` and `lake test` check it (see [Markdown
  specs](../Markdown.md)).
- The block is the precise form of a rule, and the rule names it: "...
  (`lang::quantifier_size`)". The rule states the property in a sentence;
  the block's `ensure`s state it exactly, and its `expect`s are its
  examples, which the checker checks at the block's evidence (proved,
  enumerated or tested).
- Where a rule and its block disagree, the block is right, and the rule is
  fixed.
- A block's comments are not normative. They say what a parameter or
  item stands for.

## Examples

- An example that only shows syntax or a meaning, and need not run, is
  inline code in a rule, or a ```` ```text ```` block.
- An example that shows what `fren` says is a ```` ```fren example ````
  block: a spec of its own, outside the chapter's module, checked by `lake
  test` as a [ui test](Testing.md) through both front ends (`manualExamples`).
  It states its messages as ui tests do: `--~ error: TEXT` on the line of
  the message, `--~^` for the line above, `--@ summary: ...` for the checks'
  summary. Every message must be expected, so the block shows all that
  `fren` says of it. An example runs through both front ends, so it has no
  `--@ only`, and the job fails if it finds no example at all.
- Prefer an example that the reader can read without the rest of the
  chapter. Name its items after what they stand for.

## Notes and rationale

- A note is a block quote that starts with `**Note:**`. Use it only where a
  rule surprises, or differs from Rust or Lean.
- A rationale is a block quote that starts with `**Rationale:**`. Give one
  sparingly, and cite the issue or decision behind it (#299).
- Neither states a rule. A note may repeat a consequence of the rules,
  which is the place for "so".
