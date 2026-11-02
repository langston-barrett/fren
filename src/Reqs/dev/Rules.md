# Rules and their requirements

<!-- Written by `lake test -- --bless` (the `ruleReqs` job). Do not edit. -->

For each rule of a chapter of the reference that has rule identifiers:
the requirements that formalize it, the `impl`s bound to them, and the
tests that cite it (see [Writing the reference](Style.md#rules-and-requirements)).
A rule of **Legality rules** or **Dynamic semantics** with no
requirement, or any rule with no test, says **none**.

| Chapter | Rules | Legality and dynamic | Without a requirement | Without a test |
|---|--:|--:|--:|--:|
| [src/Reqs/Lang/EvaluationRules.md](../Lang/EvaluationRules.md) | 89 | 88 | 65 | 89 |
| [src/Reqs/Lang/Quantifiers.md](../Lang/Quantifiers.md) | 68 | 54 | 40 | 61 |
| [src/Reqs/Lang/Semantics.md](../Lang/Semantics.md) | 113 | 101 | 92 | 113 |
| [src/Reqs/Lang/Traits.md](../Lang/Traits.md) | 33 | 22 | 19 | 32 |

## src/Reqs/Lang/EvaluationRules.md

| Rule | Label | Requirements | `impl`s | Tests |
|---|---|---|---|---|
| [`evaluation.laws`](../Lang/EvaluationRules.md#r-evaluation.laws) | Dynamic semantics | `lang::leaf_rules` |  | **none** |
| [`evaluation.literal`](../Lang/EvaluationRules.md#r-evaluation.literal) | Dynamic semantics | `lang::leaf_rules` |  | **none** |
| [`evaluation.variable`](../Lang/EvaluationRules.md#r-evaluation.variable) | Dynamic semantics | `lang::leaf_rules` |  | **none** |
| [`evaluation.constant`](../Lang/EvaluationRules.md#r-evaluation.constant) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.variant`](../Lang/EvaluationRules.md#r-evaluation.variant) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.let`](../Lang/EvaluationRules.md#r-evaluation.let) | Dynamic semantics | `lang::let_rules` |  | **none** |
| [`evaluation.let.lazy`](../Lang/EvaluationRules.md#r-evaluation.let.lazy) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.operator.strict`](../Lang/EvaluationRules.md#r-evaluation.operator.strict) | Dynamic semantics | `lang::operator_rules` |  | **none** |
| [`evaluation.operator.defined`](../Lang/EvaluationRules.md#r-evaluation.operator.defined) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.operator.not`](../Lang/EvaluationRules.md#r-evaluation.operator.not) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.operator.negation`](../Lang/EvaluationRules.md#r-evaluation.operator.negation) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.operator.arithmetic`](../Lang/EvaluationRules.md#r-evaluation.operator.arithmetic) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.operator.division`](../Lang/EvaluationRules.md#r-evaluation.operator.division) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.operator.concatenation`](../Lang/EvaluationRules.md#r-evaluation.operator.concatenation) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.operator.membership`](../Lang/EvaluationRules.md#r-evaluation.operator.membership) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.operator.equality`](../Lang/EvaluationRules.md#r-evaluation.operator.equality) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.operator.order`](../Lang/EvaluationRules.md#r-evaluation.operator.order) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.operator.order.excluded`](../Lang/EvaluationRules.md#r-evaluation.operator.order.excluded) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.operator.count`](../Lang/EvaluationRules.md#r-evaluation.operator.count) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.and.false`](../Lang/EvaluationRules.md#r-evaluation.and.false) | Dynamic semantics | `lang::lazy_rules` |  | **none** |
| [`evaluation.and.true`](../Lang/EvaluationRules.md#r-evaluation.and.true) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.or.true`](../Lang/EvaluationRules.md#r-evaluation.or.true) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.or.false`](../Lang/EvaluationRules.md#r-evaluation.or.false) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.lazy.undefined`](../Lang/EvaluationRules.md#r-evaluation.lazy.undefined) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.if.then`](../Lang/EvaluationRules.md#r-evaluation.if.then) | Dynamic semantics | `lang::if_rules` |  | **none** |
| [`evaluation.if.else`](../Lang/EvaluationRules.md#r-evaluation.if.else) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.if.one-branch`](../Lang/EvaluationRules.md#r-evaluation.if.one-branch) | Dynamic semantics | `lang::guards_evaluation` |  | **none** |
| [`evaluation.if.condition`](../Lang/EvaluationRules.md#r-evaluation.if.condition) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.match`](../Lang/EvaluationRules.md#r-evaluation.match) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.match.taken`](../Lang/EvaluationRules.md#r-evaluation.match.taken) | Dynamic semantics | `lang::match_rules` |  | **none** |
| [`evaluation.match.falls-through`](../Lang/EvaluationRules.md#r-evaluation.match.falls-through) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.match.skipped`](../Lang/EvaluationRules.md#r-evaluation.match.skipped) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.match.no-match`](../Lang/EvaluationRules.md#r-evaluation.match.no-match) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.match.order`](../Lang/EvaluationRules.md#r-evaluation.match.order) | Dynamic semantics | `lang::guarded_match` | `guarded_match` (src/Impls/Lang.lean) | **none** |
| [`evaluation.test`](../Lang/EvaluationRules.md#r-evaluation.test) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.list.nil`](../Lang/EvaluationRules.md#r-evaluation.list.nil) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.list.cons`](../Lang/EvaluationRules.md#r-evaluation.list.cons) | Dynamic semantics | `lang::list_rules` |  | **none** |
| [`evaluation.construct`](../Lang/EvaluationRules.md#r-evaluation.construct) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.project`](../Lang/EvaluationRules.md#r-evaluation.project) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.index`](../Lang/EvaluationRules.md#r-evaluation.index) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.method`](../Lang/EvaluationRules.md#r-evaluation.method) | Dynamic semantics | `lang::method_rules` |  | **none** |
| [`evaluation.method.abs`](../Lang/EvaluationRules.md#r-evaluation.method.abs) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.method.min-max`](../Lang/EvaluationRules.md#r-evaluation.method.min-max) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.method.len`](../Lang/EvaluationRules.md#r-evaluation.method.len) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.method.excluded`](../Lang/EvaluationRules.md#r-evaluation.method.excluded) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.apply`](../Lang/EvaluationRules.md#r-evaluation.apply) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.apply.body`](../Lang/EvaluationRules.md#r-evaluation.apply.body) | Dynamic semantics | `lang::call_rules` |  | **none** |
| [`evaluation.apply.caller`](../Lang/EvaluationRules.md#r-evaluation.apply.caller) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.apply.substitution`](../Lang/EvaluationRules.md#r-evaluation.apply.substitution) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.call`](../Lang/EvaluationRules.md#r-evaluation.call) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.call.generic`](../Lang/EvaluationRules.md#r-evaluation.call.generic) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.recur`](../Lang/EvaluationRules.md#r-evaluation.recur) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.call.arguments`](../Lang/EvaluationRules.md#r-evaluation.call.arguments) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.recur.fixed-point`](../Lang/EvaluationRules.md#r-evaluation.recur.fixed-point) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.recur.respects`](../Lang/EvaluationRules.md#r-evaluation.recur.respects) | Dynamic semantics | `lang::respects?` |  | **none** |
| [`evaluation.recur.language`](../Lang/EvaluationRules.md#r-evaluation.recur.language) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.recur.unfolds`](../Lang/EvaluationRules.md#r-evaluation.recur.unfolds) | Dynamic semantics | `lang::recursion_unfolds` |  | **none** |
| [`evaluation.free`](../Lang/EvaluationRules.md#r-evaluation.free) | Dynamic semantics | `lang::Mention`, `lang::free_vars` |  | **none** |
| [`evaluation.free.mention`](../Lang/EvaluationRules.md#r-evaluation.free.mention) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.free.variable`](../Lang/EvaluationRules.md#r-evaluation.free.variable) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.free.call`](../Lang/EvaluationRules.md#r-evaluation.free.call) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.free.let`](../Lang/EvaluationRules.md#r-evaluation.free.let) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.free.match`](../Lang/EvaluationRules.md#r-evaluation.free.match) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.free.apply`](../Lang/EvaluationRules.md#r-evaluation.free.apply) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.free.apply.elaborated`](../Lang/EvaluationRules.md#r-evaluation.free.apply.elaborated) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.free.recur`](../Lang/EvaluationRules.md#r-evaluation.free.recur) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.free.other`](../Lang/EvaluationRules.md#r-evaluation.free.other) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.free.unread`](../Lang/EvaluationRules.md#r-evaluation.free.unread) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.free.binders`](../Lang/EvaluationRules.md#r-evaluation.free.binders) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.free.params`](../Lang/EvaluationRules.md#r-evaluation.free.params) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.agree`](../Lang/EvaluationRules.md#r-evaluation.agree) | Dynamic semantics | `lang::agree?` |  | **none** |
| [`evaluation.points`](../Lang/EvaluationRules.md#r-evaluation.points) | Dynamic semantics | `lang::points` |  | **none** |
| [`evaluation.coincidence`](../Lang/EvaluationRules.md#r-evaluation.coincidence) | Dynamic semantics | `lang::coincidence` | `coincidence` (src/Impls/Semantics.lean) | **none** |
| [`evaluation.closed`](../Lang/EvaluationRules.md#r-evaluation.closed) | Dynamic semantics | `lang::closed` | `closed` (src/Impls/Semantics.lean) | **none** |
| [`evaluation.guard.term`](../Lang/EvaluationRules.md#r-evaluation.guard.term) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.guard`](../Lang/EvaluationRules.md#r-evaluation.guard) | Dynamic semantics | `lang::guard` | `guard` (src/Impls/Lang.lean) | **none** |
| [`evaluation.guard.when`](../Lang/EvaluationRules.md#r-evaluation.guard.when) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.guard.branches`](../Lang/EvaluationRules.md#r-evaluation.guard.branches) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.guard.and-or`](../Lang/EvaluationRules.md#r-evaluation.guard.and-or) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.guard.arm-guard`](../Lang/EvaluationRules.md#r-evaluation.guard.arm-guard) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.guard.arm-body`](../Lang/EvaluationRules.md#r-evaluation.guard.arm-body) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.guard.evaluated`](../Lang/EvaluationRules.md#r-evaluation.guard.evaluated) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.guard.unguarded`](../Lang/EvaluationRules.md#r-evaluation.guard.unguarded) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.guard.nesting`](../Lang/EvaluationRules.md#r-evaluation.guard.nesting) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.guard.evaluation`](../Lang/EvaluationRules.md#r-evaluation.guard.evaluation) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.guard.evaluation.connectives`](../Lang/EvaluationRules.md#r-evaluation.guard.evaluation.connectives) | Dynamic semantics | `lang::guards_evaluation` |  | **none** |
| [`evaluation.guard.evaluation.arms`](../Lang/EvaluationRules.md#r-evaluation.guard.evaluation.arms) | Dynamic semantics | `lang::arm_guards_evaluation` |  | **none** |
| [`evaluation.guard.evaluation.rest`](../Lang/EvaluationRules.md#r-evaluation.guard.evaluation.rest) | Dynamic semantics | **none** |  | **none** |
| [`evaluation.guard.check`](../Lang/EvaluationRules.md#r-evaluation.guard.check) | Proof obligations |  |  | **none** |

## src/Reqs/Lang/Quantifiers.md

| Rule | Label | Requirements | `impl`s | Tests |
|---|---|---|---|---|
| [`quantifier.syntax`](../Lang/Quantifiers.md#r-quantifier.syntax) | Syntax |  |  | **none** |
| [`quantifier.syntax.terms`](../Lang/Quantifiers.md#r-quantifier.syntax.terms) | Syntax |  |  | **none** |
| [`quantifier.syntax.keywords`](../Lang/Quantifiers.md#r-quantifier.syntax.keywords) | Syntax |  |  | **none** |
| [`quantifier.syntax.extent`](../Lang/Quantifiers.md#r-quantifier.syntax.extent) | Syntax |  |  | **none** |
| [`quantifier.syntax.operand`](../Lang/Quantifiers.md#r-quantifier.syntax.operand) | Syntax |  |  | **none** |
| [`quantifier.syntax.nested`](../Lang/Quantifiers.md#r-quantifier.syntax.nested) | Syntax |  |  | **none** |
| [`quantifier.syntax.positions`](../Lang/Quantifiers.md#r-quantifier.syntax.positions) | Syntax |  |  | **none** |
| [`quantifier.type.body`](../Lang/Quantifiers.md#r-quantifier.type.body) | Legality rules | **none** |  | **none** |
| [`quantifier.type.binder`](../Lang/Quantifiers.md#r-quantifier.type.binder) | Legality rules | **none** |  | **none** |
| [`quantifier.type.listed`](../Lang/Quantifiers.md#r-quantifier.type.listed) | Legality rules | `lang::quantified_type`, `lang::type_facts` | `type_facts` (src/Impls/TypeFacts.lean), `quantified_type` (src/Impls/TypeFacts.lean) | `test/ui/lang/quantifiers.fren` |
| [`quantifier.type.not-listed`](../Lang/Quantifiers.md#r-quantifier.type.not-listed) | Legality rules | **none** |  | `test/ui/lang/quantifiers_static.fren` |
| [`quantifier.type.subset`](../Lang/Quantifiers.md#r-quantifier.type.subset) | Legality rules | `lang::pattern_finite` | `pattern_finite` (src/Impls/Lang.lean) | **none** |
| [`quantifier.type.alias`](../Lang/Quantifiers.md#r-quantifier.type.alias) | Legality rules | **none** |  | **none** |
| [`quantifier.type.unbounded`](../Lang/Quantifiers.md#r-quantifier.type.unbounded) | Legality rules | **none** |  | `test/ui/lang/quantifiers_static.fren` |
| [`quantifier.meaning.reported-once`](../Lang/Quantifiers.md#r-quantifier.meaning.reported-once) | Legality rules | **none** |  | **none** |
| [`quantifier.meaning.instances`](../Lang/Quantifiers.md#r-quantifier.meaning.instances) | Dynamic semantics | **none** |  | **none** |
| [`quantifier.meaning.expansion`](../Lang/Quantifiers.md#r-quantifier.meaning.expansion) | Dynamic semantics | `lang::quantifier` |  | `test/ui/lang/quantifiers.fren` |
| [`quantifier.meaning.some-instance`](../Lang/Quantifiers.md#r-quantifier.meaning.some-instance) | Dynamic semantics | `lang::forall_implies_exists` |  | **none** |
| [`quantifier.meaning.order`](../Lang/Quantifiers.md#r-quantifier.meaning.order) | Dynamic semantics | **none** |  | **none** |
| [`quantifier.meaning.binder-order`](../Lang/Quantifiers.md#r-quantifier.meaning.binder-order) | Dynamic semantics | **none** |  | **none** |
| [`quantifier.meaning.order-free`](../Lang/Quantifiers.md#r-quantifier.meaning.order-free) | Dynamic semantics | **none** |  | **none** |
| [`quantifier.meaning.mixed`](../Lang/Quantifiers.md#r-quantifier.meaning.mixed) | Dynamic semantics | **none** |  | **none** |
| [`quantifier.limit`](../Lang/Quantifiers.md#r-quantifier.limit) | Legality rules | `lang::quantifier_size` | `quantifier_size` (src/Impls/Lang.lean) | `test/ui/lang/quantifiers_static.fren` |
| [`quantifier.limit.count`](../Lang/Quantifiers.md#r-quantifier.limit.count) | Legality rules | **none** |  | **none** |
| [`quantifier.limit.values`](../Lang/Quantifiers.md#r-quantifier.limit.values) | Legality rules | **none** |  | **none** |
| [`quantifier.limit.unexpanded`](../Lang/Quantifiers.md#r-quantifier.limit.unexpanded) | Legality rules | **none** |  | **none** |
| [`quantifier.limit.nested`](../Lang/Quantifiers.md#r-quantifier.limit.nested) | Legality rules | **none** |  | `test/ui/lang/quantifiers_static.fren` |
| [`quantifier.limit.not-listed`](../Lang/Quantifiers.md#r-quantifier.limit.not-listed) | Legality rules | **none** |  | **none** |
| [`quantifier.unbounded.lint`](../Lang/Quantifiers.md#r-quantifier.unbounded.lint) | Legality rules | **none** |  | **none** |
| [`quantifier.unbounded.meaning`](../Lang/Quantifiers.md#r-quantifier.unbounded.meaning) | Dynamic semantics | **none** |  | **none** |
| [`quantifier.unbounded.subset`](../Lang/Quantifiers.md#r-quantifier.unbounded.subset) | Dynamic semantics | **none** |  | **none** |
| [`quantifier.unbounded.nat`](../Lang/Quantifiers.md#r-quantifier.unbounded.nat) | Dynamic semantics | **none** |  | **none** |
| [`quantifier.unbounded.only-form`](../Lang/Quantifiers.md#r-quantifier.unbounded.only-form) | Dynamic semantics | **none** |  | **none** |
| [`quantifier.unbounded.elements`](../Lang/Quantifiers.md#r-quantifier.unbounded.elements) | Dynamic semantics | **none** |  | **none** |
| [`quantifier.unbounded.verdicts`](../Lang/Quantifiers.md#r-quantifier.unbounded.verdicts) | Proof obligations |  |  | **none** |
| [`quantifier.unbounded.contracts`](../Lang/Quantifiers.md#r-quantifier.unbounded.contracts) | Proof obligations |  |  | **none** |
| [`quantifier.unbounded.contracts.quantified`](../Lang/Quantifiers.md#r-quantifier.unbounded.contracts.quantified) | Proof obligations |  |  | **none** |
| [`quantifier.guard.forall`](../Lang/Quantifiers.md#r-quantifier.guard.forall) | Dynamic semantics | **none** |  | **none** |
| [`quantifier.guard.exists`](../Lang/Quantifiers.md#r-quantifier.guard.exists) | Dynamic semantics | **none** |  | **none** |
| [`quantifier.guard.conjuncts`](../Lang/Quantifiers.md#r-quantifier.guard.conjuncts) | Dynamic semantics | **none** |  | **none** |
| [`quantifier.guard.bound`](../Lang/Quantifiers.md#r-quantifier.guard.bound) | Dynamic semantics | **none** |  | **none** |
| [`quantifier.guard.free`](../Lang/Quantifiers.md#r-quantifier.guard.free) | Dynamic semantics | **none** |  | **none** |
| [`quantifier.guard.operand`](../Lang/Quantifiers.md#r-quantifier.guard.operand) | Dynamic semantics | `lang::guard_bound` | `guard_bound` (src/Impls/Lang.lean) | **none** |
| [`quantifier.guard.strict`](../Lang/Quantifiers.md#r-quantifier.guard.strict) | Dynamic semantics | **none** |  | **none** |
| [`quantifier.guard.name`](../Lang/Quantifiers.md#r-quantifier.guard.name) | Dynamic semantics | `lang::name_alone` | `name_alone` (src/Impls/Lang.lean) | **none** |
| [`quantifier.guard.name.members`](../Lang/Quantifiers.md#r-quantifier.guard.name.members) | Dynamic semantics | **none** |  | **none** |
| [`quantifier.guard.name.model`](../Lang/Quantifiers.md#r-quantifier.guard.name.model) | Dynamic semantics | `lang::name_alone` | `name_alone` (src/Impls/Lang.lean) | **none** |
| [`quantifier.guard.nat-floor`](../Lang/Quantifiers.md#r-quantifier.guard.nat-floor) | Dynamic semantics | `lang::nat_floor`, `lang::guard_domain` | `guard_domain` (src/Impls/Lang.lean), `nat_floor` (src/Impls/Lang.lean) | **none** |
| [`quantifier.guard.domain`](../Lang/Quantifiers.md#r-quantifier.guard.domain) | Dynamic semantics | `lang::guard_domain` | `guard_domain` (src/Impls/Lang.lean) | **none** |
| [`quantifier.guard.domain.inputs`](../Lang/Quantifiers.md#r-quantifier.guard.domain.inputs) | Dynamic semantics | `lang::guard_domain` | `guard_domain` (src/Impls/Lang.lean) | **none** |
| [`quantifier.guard.range`](../Lang/Quantifiers.md#r-quantifier.guard.range) | Dynamic semantics | `lang::range_domain` | `range_domain` (src/Impls/Lang.lean) | **none** |
| [`quantifier.guard.range.other`](../Lang/Quantifiers.md#r-quantifier.guard.range.other) | Dynamic semantics | **none** |  | **none** |
| [`quantifier.guard.range.model`](../Lang/Quantifiers.md#r-quantifier.guard.range.model) | Dynamic semantics | `lang::range_domain` | `range_domain` (src/Impls/Lang.lean) | **none** |
| [`quantifier.guard.meaning`](../Lang/Quantifiers.md#r-quantifier.guard.meaning) | Dynamic semantics | **none** |  | **none** |
| [`quantifier.guard.evaluation`](../Lang/Quantifiers.md#r-quantifier.guard.evaluation) | Dynamic semantics | **none** |  | **none** |
| [`quantifier.guard.bounded`](../Lang/Quantifiers.md#r-quantifier.guard.bounded) | Proof obligations |  |  | **none** |
| [`quantifier.name.scope`](../Lang/Quantifiers.md#r-quantifier.name.scope) | Legality rules | **none** |  | **none** |
| [`quantifier.name.distinct`](../Lang/Quantifiers.md#r-quantifier.name.distinct) | Legality rules | **none** |  | **none** |
| [`quantifier.name.boolean`](../Lang/Quantifiers.md#r-quantifier.name.boolean) | Legality rules | **none** |  | **none** |
| [`quantifier.name.shadowing`](../Lang/Quantifiers.md#r-quantifier.name.shadowing) | Legality rules | **none** |  | `test/ui/lang/quantifiers_static.fren` |
| [`quantifier.name.mentions.listed`](../Lang/Quantifiers.md#r-quantifier.name.mentions.listed) | Legality rules | **none** |  | **none** |
| [`quantifier.name.mentions.unbounded`](../Lang/Quantifiers.md#r-quantifier.name.mentions.unbounded) | Legality rules | **none** |  | **none** |
| [`quantifier.name.mentions.quantifier`](../Lang/Quantifiers.md#r-quantifier.name.mentions.quantifier) | Legality rules | **none** |  | **none** |
| [`quantifier.index.instances`](../Lang/Quantifiers.md#r-quantifier.index.instances) | Proof obligations |  |  | **none** |
| [`quantifier.index.unbounded`](../Lang/Quantifiers.md#r-quantifier.index.unbounded) | Proof obligations |  |  | **none** |
| [`quantifier.index.trigger`](../Lang/Quantifiers.md#r-quantifier.index.trigger) | Proof obligations |  |  | **none** |
| [`quantifier.global.short-form`](../Lang/Quantifiers.md#r-quantifier.global.short-form) | Legality rules | **none** |  | **none** |
| [`quantifier.binder.procedure`](../Lang/Quantifiers.md#r-quantifier.binder.procedure) | Legality rules | `lang::quantifier_binder` | `quantifier_binder` (src/Impls/Lang.lean) | **none** |

## src/Reqs/Lang/Semantics.md

| Rule | Label | Requirements | `impl`s | Tests |
|---|---|---|---|---|
| [`semantics.eval.big-step`](../Lang/Semantics.md#r-semantics.eval.big-step) | Dynamic semantics | `lang::eval` |  | **none** |
| [`semantics.derived-forms`](../Lang/Semantics.md#r-semantics.derived-forms) | Dynamic semantics | **none** |  | **none** |
| [`semantics.value`](../Lang/Semantics.md#r-semantics.value) | Dynamic semantics | `lang::Value` |  | **none** |
| [`semantics.value.bool`](../Lang/Semantics.md#r-semantics.value.bool) | Dynamic semantics | **none** |  | **none** |
| [`semantics.value.integer`](../Lang/Semantics.md#r-semantics.value.integer) | Dynamic semantics | **none** |  | **none** |
| [`semantics.value.text`](../Lang/Semantics.md#r-semantics.value.text) | Dynamic semantics | **none** |  | **none** |
| [`semantics.value.list`](../Lang/Semantics.md#r-semantics.value.list) | Dynamic semantics | **none** |  | **none** |
| [`semantics.value.constructed`](../Lang/Semantics.md#r-semantics.value.constructed) | Dynamic semantics | **none** |  | **none** |
| [`semantics.value.excluded`](../Lang/Semantics.md#r-semantics.value.excluded) | Dynamic semantics | **none** |  | **none** |
| [`semantics.value.truth`](../Lang/Semantics.md#r-semantics.value.truth) | Dynamic semantics | **none** |  | **none** |
| [`semantics.outcome`](../Lang/Semantics.md#r-semantics.outcome) | Dynamic semantics | `lang::Outcome` |  | **none** |
| [`semantics.outcome.well-defined`](../Lang/Semantics.md#r-semantics.outcome.well-defined) | Dynamic semantics | **none** |  | **none** |
| [`semantics.outcome.undefined`](../Lang/Semantics.md#r-semantics.outcome.undefined) | Dynamic semantics | **none** |  | **none** |
| [`semantics.outcome.undefined.unfixed`](../Lang/Semantics.md#r-semantics.outcome.undefined.unfixed) | Dynamic semantics | **none** |  | **none** |
| [`semantics.outcome.strict`](../Lang/Semantics.md#r-semantics.outcome.strict) | Dynamic semantics | **none** |  | **none** |
| [`semantics.outcome.lazy-forms`](../Lang/Semantics.md#r-semantics.outcome.lazy-forms) | Dynamic semantics | **none** |  | **none** |
| [`semantics.syntax`](../Lang/Semantics.md#r-semantics.syntax) | Syntax |  |  | **none** |
| [`semantics.syntax.paths`](../Lang/Semantics.md#r-semantics.syntax.paths) | Syntax |  |  | **none** |
| [`semantics.syntax.names`](../Lang/Semantics.md#r-semantics.syntax.names) | Syntax |  |  | **none** |
| [`semantics.syntax.names.id`](../Lang/Semantics.md#r-semantics.syntax.names.id) | Syntax |  |  | **none** |
| [`semantics.syntax.names.generic`](../Lang/Semantics.md#r-semantics.syntax.names.generic) | Syntax |  |  | **none** |
| [`semantics.syntax.names.recursion`](../Lang/Semantics.md#r-semantics.syntax.names.recursion) | Syntax |  |  | **none** |
| [`semantics.syntax.lists`](../Lang/Semantics.md#r-semantics.syntax.lists) | Syntax |  |  | **none** |
| [`semantics.syntax.pattern`](../Lang/Semantics.md#r-semantics.syntax.pattern) | Syntax |  |  | **none** |
| [`semantics.syntax.pattern.exclusive-range`](../Lang/Semantics.md#r-semantics.syntax.pattern.exclusive-range) | Syntax |  |  | **none** |
| [`semantics.syntax.pattern.list`](../Lang/Semantics.md#r-semantics.syntax.pattern.list) | Syntax |  |  | **none** |
| [`semantics.syntax.expr`](../Lang/Semantics.md#r-semantics.syntax.expr) | Syntax |  |  | **none** |
| [`semantics.syntax.expr.lists`](../Lang/Semantics.md#r-semantics.syntax.expr.lists) | Syntax |  |  | **none** |
| [`semantics.derived`](../Lang/Semantics.md#r-semantics.derived) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.repeated`](../Lang/Semantics.md#r-semantics.derived.repeated) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.not-equal`](../Lang/Semantics.md#r-semantics.derived.not-equal) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.greater`](../Lang/Semantics.md#r-semantics.derived.greater) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.iff`](../Lang/Semantics.md#r-semantics.derived.iff) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.when`](../Lang/Semantics.md#r-semantics.derived.when) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.unless`](../Lang/Semantics.md#r-semantics.derived.unless) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.chain`](../Lang/Semantics.md#r-semantics.derived.chain) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.let`](../Lang/Semantics.md#r-semantics.derived.let) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.match`](../Lang/Semantics.md#r-semantics.derived.match) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.match.empty`](../Lang/Semantics.md#r-semantics.derived.match.empty) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.match.scrutinees`](../Lang/Semantics.md#r-semantics.derived.match.scrutinees) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.table`](../Lang/Semantics.md#r-semantics.derived.table) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.table.scrutinee`](../Lang/Semantics.md#r-semantics.derived.table.scrutinee) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.test.and`](../Lang/Semantics.md#r-semantics.derived.test.and) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.test.if`](../Lang/Semantics.md#r-semantics.derived.test.if) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.test.when`](../Lang/Semantics.md#r-semantics.derived.test.when) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.test.chain`](../Lang/Semantics.md#r-semantics.derived.test.chain) | Dynamic semantics | `lang::test_scope` | `test_scope` (src/Impls/Lang.lean) | **none** |
| [`semantics.derived.list`](../Lang/Semantics.md#r-semantics.derived.list) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.variant`](../Lang/Semantics.md#r-semantics.derived.variant) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.construct`](../Lang/Semantics.md#r-semantics.derived.construct) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.record`](../Lang/Semantics.md#r-semantics.derived.record) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.field`](../Lang/Semantics.md#r-semantics.derived.field) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.update`](../Lang/Semantics.md#r-semantics.derived.update) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.apply`](../Lang/Semantics.md#r-semantics.derived.apply) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.constant`](../Lang/Semantics.md#r-semantics.derived.constant) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.call`](../Lang/Semantics.md#r-semantics.derived.call) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.call.generic`](../Lang/Semantics.md#r-semantics.derived.call.generic) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.recur`](../Lang/Semantics.md#r-semantics.derived.recur) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.higher-order`](../Lang/Semantics.md#r-semantics.derived.higher-order) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.higher-order.captures`](../Lang/Semantics.md#r-semantics.derived.higher-order.captures) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.higher-order.unfolding`](../Lang/Semantics.md#r-semantics.derived.higher-order.unfolding) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.higher-order.renaming`](../Lang/Semantics.md#r-semantics.derived.higher-order.renaming) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.lambda-match`](../Lang/Semantics.md#r-semantics.derived.lambda-match) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.function-name`](../Lang/Semantics.md#r-semantics.derived.function-name) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.function-parameter`](../Lang/Semantics.md#r-semantics.derived.function-parameter) | Dynamic semantics | **none** |  | **none** |
| [`semantics.derived.count`](../Lang/Semantics.md#r-semantics.derived.count) | Dynamic semantics | **none** |  | **none** |
| [`semantics.env`](../Lang/Semantics.md#r-semantics.env) | Dynamic semantics | `lang::Env` |  | **none** |
| [`semantics.env.lookup`](../Lang/Semantics.md#r-semantics.env.lookup) | Dynamic semantics | `lang::lookup` |  | **none** |
| [`semantics.env.unbound`](../Lang/Semantics.md#r-semantics.env.unbound) | Dynamic semantics | **none** |  | **none** |
| [`semantics.interp`](../Lang/Semantics.md#r-semantics.interp) | Dynamic semantics | `lang::Interp` |  | **none** |
| [`semantics.interp.functions`](../Lang/Semantics.md#r-semantics.interp.functions) | Dynamic semantics | **none** |  | **none** |
| [`semantics.interp.recursions`](../Lang/Semantics.md#r-semantics.interp.recursions) | Dynamic semantics | **none** |  | **none** |
| [`semantics.interp.primitives`](../Lang/Semantics.md#r-semantics.interp.primitives) | Dynamic semantics | **none** |  | **none** |
| [`semantics.interp.graph`](../Lang/Semantics.md#r-semantics.interp.graph) | Dynamic semantics | **none** |  | **none** |
| [`semantics.interp.finite`](../Lang/Semantics.md#r-semantics.interp.finite) | Dynamic semantics | **none** |  | **none** |
| [`semantics.interp.primitives.meaning`](../Lang/Semantics.md#r-semantics.interp.primitives.meaning) | Dynamic semantics | **none** |  | **none** |
| [`semantics.interp.apply`](../Lang/Semantics.md#r-semantics.interp.apply) | Dynamic semantics | **none** |  | **none** |
| [`semantics.env.shadowing`](../Lang/Semantics.md#r-semantics.env.shadowing) | Dynamic semantics | `lang::lookup_binding` |  | **none** |
| [`semantics.eval.laws`](../Lang/Semantics.md#r-semantics.eval.laws) | Dynamic semantics | **none** |  | **none** |
| [`semantics.list.nth`](../Lang/Semantics.md#r-semantics.list.nth) | Dynamic semantics | **none** |  | **none** |
| [`semantics.list.length`](../Lang/Semantics.md#r-semantics.list.length) | Dynamic semantics | **none** |  | **none** |
| [`semantics.list.append`](../Lang/Semantics.md#r-semantics.list.append) | Dynamic semantics | **none** |  | **none** |
| [`semantics.list.element`](../Lang/Semantics.md#r-semantics.list.element) | Dynamic semantics | **none** |  | **none** |
| [`semantics.list.is-list`](../Lang/Semantics.md#r-semantics.list.is-list) | Dynamic semantics | **none** |  | **none** |
| [`semantics.list.trues`](../Lang/Semantics.md#r-semantics.list.trues) | Dynamic semantics | **none** |  | **none** |
| [`semantics.list.booleans`](../Lang/Semantics.md#r-semantics.list.booleans) | Dynamic semantics | **none** |  | **none** |
| [`semantics.match.matches`](../Lang/Semantics.md#r-semantics.match.matches) | Dynamic semantics | **none** |  | **none** |
| [`semantics.match.bind`](../Lang/Semantics.md#r-semantics.match.bind) | Dynamic semantics | **none** |  | **none** |
| [`semantics.match.or`](../Lang/Semantics.md#r-semantics.match.or) | Dynamic semantics | **none** |  | **none** |
| [`semantics.match.params`](../Lang/Semantics.md#r-semantics.match.params) | Dynamic semantics | **none** |  | **none** |
| [`semantics.operator.unary`](../Lang/Semantics.md#r-semantics.operator.unary) | Dynamic semantics | **none** |  | **none** |
| [`semantics.operator.primitive`](../Lang/Semantics.md#r-semantics.operator.primitive) | Dynamic semantics | **none** |  | **none** |
| [`semantics.operator.binary`](../Lang/Semantics.md#r-semantics.operator.binary) | Dynamic semantics | **none** |  | **none** |
| [`semantics.operator.method`](../Lang/Semantics.md#r-semantics.operator.method) | Dynamic semantics | **none** |  | **none** |
| [`semantics.operator.count`](../Lang/Semantics.md#r-semantics.operator.count) | Dynamic semantics | **none** |  | **none** |
| [`semantics.eval.outcomes`](../Lang/Semantics.md#r-semantics.eval.outcomes) | Dynamic semantics | **none** |  | **none** |
| [`semantics.connective`](../Lang/Semantics.md#r-semantics.connective) | Dynamic semantics | **none** |  | **none** |
| [`semantics.connective.and`](../Lang/Semantics.md#r-semantics.connective.and) | Dynamic semantics | **none** |  | **none** |
| [`semantics.connective.or`](../Lang/Semantics.md#r-semantics.connective.or) | Dynamic semantics | **none** |  | **none** |
| [`semantics.connective.if`](../Lang/Semantics.md#r-semantics.connective.if) | Dynamic semantics | **none** |  | **none** |
| [`semantics.eval.match`](../Lang/Semantics.md#r-semantics.eval.match) | Dynamic semantics | **none** |  | **none** |
| [`semantics.test`](../Lang/Semantics.md#r-semantics.test) | Dynamic semantics | **none** |  | **none** |
| [`semantics.construction.cons`](../Lang/Semantics.md#r-semantics.construction.cons) | Dynamic semantics | **none** |  | **none** |
| [`semantics.construction.construct`](../Lang/Semantics.md#r-semantics.construction.construct) | Dynamic semantics | **none** |  | **none** |
| [`semantics.construction.project`](../Lang/Semantics.md#r-semantics.construction.project) | Dynamic semantics | **none** |  | **none** |
| [`semantics.construction.index`](../Lang/Semantics.md#r-semantics.construction.index) | Dynamic semantics | **none** |  | **none** |
| [`semantics.call`](../Lang/Semantics.md#r-semantics.call) | Dynamic semantics | **none** |  | **none** |
| [`semantics.eval`](../Lang/Semantics.md#r-semantics.eval) | Dynamic semantics | **none** |  | **none** |
| [`semantics.eval.structural`](../Lang/Semantics.md#r-semantics.eval.structural) | Dynamic semantics | **none** |  | **none** |
| [`semantics.eval.determinism`](../Lang/Semantics.md#r-semantics.eval.determinism) | Dynamic semantics | `lang::determinism` |  | **none** |
| [`semantics.excluded`](../Lang/Semantics.md#r-semantics.excluded) | Dynamic semantics | **none** |  | **none** |
| [`semantics.excluded.quantifiers`](../Lang/Semantics.md#r-semantics.excluded.quantifiers) | Dynamic semantics | **none** |  | **none** |
| [`semantics.excluded.abstract`](../Lang/Semantics.md#r-semantics.excluded.abstract) | Dynamic semantics | **none** |  | **none** |
| [`semantics.excluded.orders`](../Lang/Semantics.md#r-semantics.excluded.orders) | Dynamic semantics | **none** |  | **none** |

## src/Reqs/Lang/Traits.md

| Rule | Label | Requirements | `impl`s | Tests |
|---|---|---|---|---|
| [`trait.syntax`](../Lang/Traits.md#r-trait.syntax) | Syntax |  |  | **none** |
| [`trait.syntax.item`](../Lang/Traits.md#r-trait.syntax.item) | Syntax |  |  | **none** |
| [`trait.syntax.keywords`](../Lang/Traits.md#r-trait.syntax.keywords) | Syntax |  |  | **none** |
| [`trait.member.kinds`](../Lang/Traits.md#r-trait.member.kinds) | Legality rules | **none** |  | **none** |
| [`trait.member.other`](../Lang/Traits.md#r-trait.member.other) | Legality rules | **none** |  | **none** |
| [`trait.member.pub`](../Lang/Traits.md#r-trait.member.pub) | Legality rules | **none** |  | **none** |
| [`trait.member.default`](../Lang/Traits.md#r-trait.member.default) | Legality rules | **none** |  | **none** |
| [`trait.member.generic`](../Lang/Traits.md#r-trait.member.generic) | Legality rules | **none** |  | **none** |
| [`trait.member.use`](../Lang/Traits.md#r-trait.member.use) | Legality rules | **none** |  | **none** |
| [`trait.member.rule`](../Lang/Traits.md#r-trait.member.rule) | Legality rules | `lang::trait_member` | `trait_member` (src/Impls/Lang.lean) | `test/ui/lang/traits_static.fren` |
| [`trait.member.order`](../Lang/Traits.md#r-trait.member.order) | Legality rules | `lang::trait_member_phase` | `trait_member_phase` (src/Impls/Lang.lean) | **none** |
| [`trait.carrier`](../Lang/Traits.md#r-trait.carrier) | Legality rules | **none** |  | **none** |
| [`trait.carrier.payload`](../Lang/Traits.md#r-trait.carrier.payload) | Legality rules | **none** |  | **none** |
| [`trait.carrier.outside`](../Lang/Traits.md#r-trait.carrier.outside) | Legality rules | **none** |  | **none** |
| [`trait.scope.shadowing`](../Lang/Traits.md#r-trait.scope.shadowing) | Legality rules | **none** |  | **none** |
| [`trait.scope.order`](../Lang/Traits.md#r-trait.scope.order) | Legality rules | **none** |  | **none** |
| [`trait.scope.distinct`](../Lang/Traits.md#r-trait.scope.distinct) | Legality rules | **none** |  | **none** |
| [`trait.scope.outside`](../Lang/Traits.md#r-trait.scope.outside) | Legality rules | **none** |  | **none** |
| [`trait.law.type`](../Lang/Traits.md#r-trait.law.type) | Legality rules | **none** |  | **none** |
| [`trait.law.variables`](../Lang/Traits.md#r-trait.law.variables) | Legality rules | **none** |  | **none** |
| [`trait.law.mentions`](../Lang/Traits.md#r-trait.law.mentions) | Legality rules | **none** |  | **none** |
| [`trait.law.names`](../Lang/Traits.md#r-trait.law.names) | Legality rules | **none** |  | **none** |
| [`trait.law.meaning`](../Lang/Traits.md#r-trait.law.meaning) | Dynamic semantics | **none** |  | **none** |
| [`trait.law.interpretation`](../Lang/Traits.md#r-trait.law.interpretation) | Dynamic semantics | **none** |  | **none** |
| [`trait.law.undecidable`](../Lang/Traits.md#r-trait.law.undecidable) | Proof obligations |  |  | **none** |
| [`trait.expect.meaning`](../Lang/Traits.md#r-trait.expect.meaning) | Dynamic semantics | `lang::trait_expectation` |  | **none** |
| [`trait.expect.checks`](../Lang/Traits.md#r-trait.expect.checks) | Proof obligations |  |  | **none** |
| [`trait.expect.core`](../Lang/Traits.md#r-trait.expect.core) | Proof obligations | `lang::law_flags` | `law_flags` (src/Impls/Lang.lean) | **none** |
| [`trait.expect.lawful`](../Lang/Traits.md#r-trait.expect.lawful) | Proof obligations | `check::query_hypotheses` | `query_hypotheses` (src/Impls/Check.lean) | **none** |
| [`trait.expect.laws-unchecked`](../Lang/Traits.md#r-trait.expect.laws-unchecked) | Proof obligations | `check::law_premise`, `check::query_hypotheses` | `law_premise` (src/Impls/Check.lean), `query_hypotheses` (src/Impls/Check.lean) | **none** |
| [`trait.expect.once`](../Lang/Traits.md#r-trait.expect.once) | Proof obligations |  |  | **none** |
| [`trait.law.setting`](../Lang/Traits.md#r-trait.law.setting) | Proof obligations |  |  | **none** |
| [`trait.expect.evidence`](../Lang/Traits.md#r-trait.expect.evidence) | Proof obligations | `lang::trait_expectation_evidence` | `trait_expectation_evidence` (src/Impls/Lang.lean) | **none** |
