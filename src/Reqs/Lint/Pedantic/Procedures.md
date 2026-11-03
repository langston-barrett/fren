# Procedures

## Procedures that only claim

`proc_without_outputs` fires on a private [procedure](../../Lang/Procedures.md)
with no results, whose every member is one that a [global
expectation](../../Lang/Global.md)'s block accepts: no guarantee, no
`exists`, no `out`, and nothing written with `det`. Its `let`s name
expressions, as a global expectation's do. Such a procedure has no output
for its members to constrain, and constrains nothing: it only claims
something of its parameters, which is what a global expectation is for. A
global expectation means what its expectations mean in a procedure with its
parameters as inputs, its assumptions, its calls and its definitions, and no
outputs or guarantees (see [Meaning](../../Lang/Global.md#meaning)). So the fix,
which writes `expect` in place of `proc`, keeps what each claim means and
how it is checked: each expectation and cover goal, the preconditions of
the calls, and that the assumptions can hold together. The procedure's
realizability check had no guarantee to realize. One check goes: whether
an assumption is [redundant](../../Check.md#redundancy), always true,
which a procedure's checks ask and a global expectation's do not
(`check::applies`), so the fixed spec loses that warning, never a verdict. The snapshots
`test/cli/lints/pedantic/f0846_proc_without_outputs` and
`f0846_proc_without_outputs_fixed` show it: 6 checks pass before the fix,
and 5 after.

The fixed item is a global expectation, so the lints that only global
expectations get now apply to it. One is
[`unrelated_binders`](../Suspicious.md#unrelated-binders), which fires
where the calls fall into groups that nothing relates. So fixing this
lint can bring that warning, which says that the claim is several claims
in one.

What the fix changes is what the procedure is to the rest of the spec. A
global expectation is not a procedure: nothing can call it, nor refine it,
and it has no [evidence](../../Trace.md), so a `tested` or `trusted` claim
cannot name it. So the lint does not fire on a procedure that a path in its
file resolves to, as [`dead_code`](../Unused.md#dead-code) counts paths: a
call of it, a refinement of it, or a claim about it. It does not fire on a
`pub` procedure, which other files, and Lean code, may call or name. As for
`dead_code`, only paths in its own file count, though a private procedure
is visible from its module's descendants, so a later file that enters its
module and calls it would need the procedure back. A
procedure with a guarantee is left alone too, though it has no outputs: its
guarantee is checked as realizability, and an `impl` proves it, which is
how [`lang::coincidence`](../../Lang/EvaluationRules.md#free-variables) and
the laws of the lints are stated. The fixed procedure leaves the
[trace](../../Trace.md) report, where it was a procedure with no
implementation.

It is in `pedantic`, and allowed, as Clippy's nearest lints are:
`unused_async`, an `async fn` that awaits nothing, and `unnecessary_wraps`,
a function whose result type wraps what it need not. Each finds an item
declared as something more than it is, which is a matter of judgement:
many specs write a claim as a procedure, the laws of these lints' own
chapters among them, and read well so. The message is reported at the
procedure's name, at the end of the file.
`lint::proc_without_outputs` states when it fires, from its results and
members, each with whether it is written with `det`, as
[`lang::block_member`](../../Lang/Global.md) reads them:

```fren
pub mod lint

pub proc proc_without_outputs(
    pub?,
    members: Rel<lang::BlockMember, Bool>,    -- its results and members, each with whether it is written with `det`
    n_uses: Nat,                              -- paths in its file that resolve to it
): (det fires?) {
    ensure rule: fires? iff (not pub? and n_uses = 0
        and (forall (m: lang::BlockMember) (det?: Bool), when (m, det?) in members, lang::block_accepts?(m, det?)))

    expect public_never: when pub?, not fires?
    expect used_never: when n_uses > 0, not fires?
    expect results_never: when (lang::BlockMember::Result, false) in members, not fires?
    expect guarantees_never: when (lang::BlockMember::Ensure, false) in members, not fires?
    cover empty: fires? and members = {}
}
```

The fix keeps the item well-formed: where the lint fires, the block of the
global expectation that the fix writes accepts each of its members, so the
fix makes no static error (`F0417`):

```fren
expect fix_accepted(
    pub?,
    members: Rel<lang::BlockMember, Bool>,
    n_uses: Nat,
    member: lang::BlockMember,
    det?,
) {
    call l := proc_without_outputs(pub?, members, n_uses)
    call b := lang::block_member(member, det?)
    expect accepted: when l.fires? and (member, det?) in members, b.accepted?
}
```
