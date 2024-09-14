Lean version: `{{#include ../lean-toolchain}}`

# \#adaptation_note
Defined in: `«tactic#adaptation_note_»`

Adaptation notes are comments that are used to indicate that a piece of code
has been changed to accommodate a change in Lean core.
They typically require further action/maintenance to be taken in the future.

# \#check
Defined in: `Mathlib.Tactic.«tactic#check__»`

The `#check t` tactic elaborates the term `t` and then pretty prints it with its type as `e : ty`.

If `t` is an identifier, then it pretty prints a type declaration form
for the global constant `t` instead.
Use `#check (t)` to pretty print it as an elaborated expression.

Like the `#check` command, the `#check` tactic allows stuck typeclass instance problems.
These become metavariables in the output.

# \#find
Defined in: `Mathlib.Tactic.Find.«tactic#find_»`


# \#leansearch
Defined in: `LeanSearchClient.leansearch_tactic`


# (
Defined in: `Lean.Parser.Tactic.paren`

`(tacs)` executes a list of tactics in sequence, without requiring that
the goal be closed at the end like `· tacs`. Like `by` itself, the tactics
can be either separated by newlines or `;`.

# <;>
Defined in: `Batteries.Tactic.seq_focus`

`t <;> [t1; t2; ...; tn]` focuses on the first goal and applies `t`, which should result in `n`
subgoals. It then applies each `ti` to the corresponding goal and collects the resulting
subgoals.

# <;>
Defined in: `Lean.Parser.Tactic.«tactic_<;>_»`

`tac <;> tac'` runs `tac` on the main goal and `tac'` on each produced goal,
concatenating all goals produced by `tac'`.

# _
Defined in: `Batteries.Tactic.tactic_`

`_` in tactic position acts like the `done` tactic: it fails and gives the list
of goals if there are any. It is useful as a placeholder after starting a tactic block
such as `by _` to make it syntactically correct and show the current goal.

# abel
Defined in: `Mathlib.Tactic.Abel.abel_term`

Unsupported legacy syntax from mathlib3, which allowed passing additional terms to `abel`.

# abel
Defined in: `Mathlib.Tactic.Abel.abel`

Tactic for evaluating expressions in abelian groups.

* `abel!` will use a more aggressive reducibility setting to determine equality of atoms.
* `abel1` fails if the target is not an equality.

For example:
```lean
example [AddCommMonoid α] (a b : α) : a + (b + a) = a + a + b := by abel
example [AddCommGroup α] (a : α) : (3 : ℤ) • a = a + (2 : ℤ) • a := by abel
```

# abel!
Defined in: `Mathlib.Tactic.Abel.abel!_term`

Unsupported legacy syntax from mathlib3, which allowed passing additional terms to `abel!`.

# abel!
Defined in: `Mathlib.Tactic.Abel.tacticAbel!`

Tactic for evaluating expressions in abelian groups.

* `abel!` will use a more aggressive reducibility setting to determine equality of atoms.
* `abel1` fails if the target is not an equality.

For example:
```lean
example [AddCommMonoid α] (a b : α) : a + (b + a) = a + a + b := by abel
example [AddCommGroup α] (a : α) : (3 : ℤ) • a = a + (2 : ℤ) • a := by abel
```

# abel1
Defined in: `Mathlib.Tactic.Abel.abel1`

Tactic for solving equations in the language of
*additive*, commutative monoids and groups.
This version of `abel` fails if the target is not an equality
that is provable by the axioms of commutative monoids/groups.

`abel1!` will use a more aggressive reducibility setting to identify atoms.
This can prove goals that `abel` cannot, but is more expensive.

# abel1!
Defined in: `Mathlib.Tactic.Abel.abel1!`

Tactic for solving equations in the language of
*additive*, commutative monoids and groups.
This version of `abel` fails if the target is not an equality
that is provable by the axioms of commutative monoids/groups.

`abel1!` will use a more aggressive reducibility setting to identify atoms.
This can prove goals that `abel` cannot, but is more expensive.

# abel_nf
Defined in: `Mathlib.Tactic.Abel.abelNF`

Simplification tactic for expressions in the language of abelian groups,
which rewrites all group expressions into a normal form.
* `abel_nf!` will use a more aggressive reducibility setting to identify atoms.
* `abel_nf (config := cfg)` allows for additional configuration:
  * `red`: the reducibility setting (overridden by `!`)
  * `recursive`: if true, `abel_nf` will also recurse into atoms
* `abel_nf` works as both a tactic and a conv tactic.
  In tactic mode, `abel_nf at h` can be used to rewrite in a hypothesis.

# abel_nf!
Defined in: `Mathlib.Tactic.Abel.tacticAbel_nf!__`

Simplification tactic for expressions in the language of abelian groups,
which rewrites all group expressions into a normal form.
* `abel_nf!` will use a more aggressive reducibility setting to identify atoms.
* `abel_nf (config := cfg)` allows for additional configuration:
  * `red`: the reducibility setting (overridden by `!`)
  * `recursive`: if true, `abel_nf` will also recurse into atoms
* `abel_nf` works as both a tactic and a conv tactic.
  In tactic mode, `abel_nf at h` can be used to rewrite in a hypothesis.

# absurd
Defined in: `Batteries.Tactic.tacticAbsurd_`

Given a proof `h` of `p`, `absurd h` changes the goal to `⊢ ¬ p`.
If `p` is a negation `¬q` then the goal is changed to `⊢ q` instead.

# ac_change
Defined in: `Mathlib.Tactic.acChange`

`ac_change g using n` is `convert_to g using n` followed by `ac_rfl`. It is useful for
rearranging/reassociating e.g. sums:
```lean
example (a b c d e f g N : ℕ) : (a + b) + (c + d) + (e + f) + g ≤ N := by
  ac_change a + d + e + f + c + g + b ≤ _
  -- ⊢ a + d + e + f + c + g + b ≤ N
```

# ac_rfl
Defined in: `Lean.Parser.Tactic.acRfl`

`ac_rfl` proves equalities up to application of an associative and commutative operator.
```lean
instance : Associative (α := Nat) (.+.) := ⟨Nat.add_assoc⟩
instance : Commutative (α := Nat) (.+.) := ⟨Nat.add_comm⟩

example (a b c d : Nat) : a + b + c + d = d + (b + c) + a := by ac_rfl
```

# admit
Defined in: `Lean.Parser.Tactic.tacticAdmit`

`admit` is a shorthand for `exact sorry`.

# aesop
Defined in: `Aesop.Frontend.Parser.aesopTactic`

`aesop <clause>*` tries to solve the current goal by applying a set of rules
registered with the `@[aesop]` attribute. See [its
README](https://github.com/JLimperg/aesop#readme) for a tutorial and a
reference.

The variant `aesop?` prints the proof it found as a `Try this` suggestion.

Clauses can be used to customise the behaviour of an Aesop call. Available
clauses are:

- `(add <phase> <priority> <builder> <rule>)` adds a rule. `<phase>` is
  `unsafe`, `safe` or `norm`. `<priority>` is a percentage for unsafe rules and
  an integer for safe and norm rules. `<rule>` is the name of a declaration or
  local hypothesis. `<builder>` is the rule builder used to turn `<rule>` into
  an Aesop rule. Example: `(add unsafe 50% apply Or.inl)`.
- `(erase <rule>)` disables a globally registered Aesop rule. Example: `(erase
  Aesop.BuiltinRules.assumption)`.
- `(rule_sets := [<ruleset>,*])` enables or disables named sets of rules for
  this Aesop call. Example: `(rule_sets := [-builtin, MyRuleSet])`.
- `(config { <opt> := <value> })` adjusts Aesop's search options. See
  `Aesop.Options`.
- `(simp_config { <opt> := <value> })` adjusts options for Aesop's built-in
  `simp` rule. The given options are directly passed to `simp`. For example,
  `(simp_config := { zeta := false })` makes Aesop use
  `simp (config := { zeta := false })`.

# aesop?
Defined in: `Aesop.Frontend.Parser.aesopTactic?`

`aesop <clause>*` tries to solve the current goal by applying a set of rules
registered with the `@[aesop]` attribute. See [its
README](https://github.com/JLimperg/aesop#readme) for a tutorial and a
reference.

The variant `aesop?` prints the proof it found as a `Try this` suggestion.

Clauses can be used to customise the behaviour of an Aesop call. Available
clauses are:

- `(add <phase> <priority> <builder> <rule>)` adds a rule. `<phase>` is
  `unsafe`, `safe` or `norm`. `<priority>` is a percentage for unsafe rules and
  an integer for safe and norm rules. `<rule>` is the name of a declaration or
  local hypothesis. `<builder>` is the rule builder used to turn `<rule>` into
  an Aesop rule. Example: `(add unsafe 50% apply Or.inl)`.
- `(erase <rule>)` disables a globally registered Aesop rule. Example: `(erase
  Aesop.BuiltinRules.assumption)`.
- `(rule_sets := [<ruleset>,*])` enables or disables named sets of rules for
  this Aesop call. Example: `(rule_sets := [-builtin, MyRuleSet])`.
- `(config { <opt> := <value> })` adjusts Aesop's search options. See
  `Aesop.Options`.
- `(simp_config { <opt> := <value> })` adjusts options for Aesop's built-in
  `simp` rule. The given options are directly passed to `simp`. For example,
  `(simp_config := { zeta := false })` makes Aesop use
  `simp (config := { zeta := false })`.

# aesop_cat
Defined in: `CategoryTheory.aesop_cat`

A thin wrapper for `aesop` which adds the `CategoryTheory` rule set and
allows `aesop` to look through semireducible definitions when calling `intros`.
This tactic fails when it is unable to solve the goal, making it suitable for
use in auto-params.

# aesop_cat?
Defined in: `CategoryTheory.aesop_cat?`

We also use `aesop_cat?` to pass along a `Try this` suggestion when using `aesop_cat`

# aesop_cat_nonterminal
Defined in: `CategoryTheory.aesop_cat_nonterminal`

A variant of `aesop_cat` which does not fail when it is unable to solve the
goal. Use this only for exploration! Nonterminal `aesop` is even worse than
nonterminal `simp`.

# aesop_graph
Defined in: `aesop_graph`

A variant of the `aesop` tactic for use in the graph library. Changes relative
to standard `aesop`:

- We use the `SimpleGraph` rule set in addition to the default rule sets.
- We instruct Aesop's `intro` rule to unfold with `default` transparency.
- We instruct Aesop to fail if it can't fully solve the goal. This allows us to
  use `aesop_graph` for auto-params.

# aesop_graph?
Defined in: `aesop_graph?`

Use `aesop_graph?` to pass along a `Try this` suggestion when using `aesop_graph`

# aesop_graph_nonterminal
Defined in: `aesop_graph_nonterminal`

A variant of `aesop_graph` which does not fail if it is unable to solve the goal.
Use this only for exploration! Nonterminal Aesop is even worse than nonterminal `simp`.

# aesop_mat
Defined in: `Matroid.aesop_mat`

The `aesop_mat` tactic attempts to prove a set is contained in the ground set of a matroid.
It uses a `[Matroid]` ruleset, and is allowed to fail.

# aesop_unfold
Defined in: `Aesop.tacticAesop_unfold_`


# aesop_unfold
Defined in: `Aesop.tacticAesop_unfold_At_`


# all_goals
Defined in: `Lean.Parser.Tactic.allGoals`

`all_goals tac` runs `tac` on each goal, concatenating the resulting goals, if any.

# and_intros
Defined in: `Lean.Parser.Tactic.tacticAnd_intros`

`and_intros` applies `And.intro` until it does not make progress.

# any_goals
Defined in: `Lean.Parser.Tactic.anyGoals`

`any_goals tac` applies the tactic `tac` to every goal, and succeeds if at
least one application succeeds.

# apply
Defined in: `Mathlib.Tactic.tacticApply_At_`

`apply t at i` will use forward reasoning with `t` at the hypothesis `i`.
Explicitly, if `t : α₁ → ⋯ → αᵢ → ⋯ → αₙ` and `i` has type `αᵢ`, then this tactic will add
metavariables/goals for any terms of `αⱼ` for `j = 1, …, i-1`,
then replace the type of `i` with `αᵢ₊₁ → ⋯ → αₙ` by applying those metavariables and the
original `i`.

# apply
Defined in: `Lean.Parser.Tactic.apply`

`apply e` tries to match the current goal against the conclusion of `e`'s type.
If it succeeds, then the tactic returns as many subgoals as the number of premises that
have not been fixed by type inference or type class resolution.
Non-dependent premises are added before dependent ones.

The `apply` tactic uses higher-order pattern matching, type class resolution,
and first-order unification with dependent types.

# apply
Defined in: `Mathlib.Tactic.applyWith`

`apply (config := cfg) e` is like `apply e` but allows you to provide a configuration
`cfg : ApplyConfig` to pass to the underlying `apply` operation.

# apply?
Defined in: `Lean.Parser.Tactic.apply?`

Searches environment for definitions or theorems that can refine the goal using `apply`
with conditions resolved when possible with `solve_by_elim`.

The optional `using` clause provides identifiers in the local context that must be
used when closing the goal.

# apply_assumption
Defined in: `Lean.Parser.Tactic.applyAssumption`

`apply_assumption` looks for an assumption of the form `... → ∀ _, ... → head`
where `head` matches the current goal.

You can specify additional rules to apply using `apply_assumption [...]`.
By default `apply_assumption` will also try `rfl`, `trivial`, `congrFun`, and `congrArg`.
If you don't want these, or don't want to use all hypotheses, use `apply_assumption only [...]`.
You can use `apply_assumption [-h]` to omit a local hypothesis.
You can use `apply_assumption using [a₁, ...]` to use all lemmas which have been labelled
with the attributes `aᵢ` (these attributes must be created using `register_label_attr`).

`apply_assumption` will use consequences of local hypotheses obtained via `symm`.

If `apply_assumption` fails, it will call `exfalso` and try again.
Thus if there is an assumption of the form `P → ¬ Q`, the new tactic state
will have two goals, `P` and `Q`.

You can pass a further configuration via the syntax `apply_rules (config := {...}) lemmas`.
The options supported are the same as for `solve_by_elim` (and include all the options for `apply`).

# apply_ext_theorem
Defined in: `Lean.Elab.Tactic.Ext.applyExtTheorem`

Apply a single extensionality theorem to the current goal.

# apply_fun
Defined in: `Mathlib.Tactic.applyFun`

Apply a function to an equality or inequality in either a local hypothesis or the goal.

* If we have `h : a = b`, then `apply_fun f at h` will replace this with `h : f a = f b`.
* If we have `h : a ≤ b`, then `apply_fun f at h` will replace this with `h : f a ≤ f b`,
  and create a subsidiary goal `Monotone f`.
  `apply_fun` will automatically attempt to discharge this subsidiary goal using `mono`,
  or an explicit solution can be provided with `apply_fun f at h using P`, where `P : Monotone f`.
* If we have `h : a < b`, then `apply_fun f at h` will replace this with `h : f a < f b`,
  and create a subsidiary goal `StrictMono f` and behaves as in the previous case.
* If we have `h : a ≠ b`, then `apply_fun f at h` will replace this with `h : f a ≠ f b`,
  and create a subsidiary goal `Injective f` and behaves as in the previous two cases.
* If the goal is `a ≠ b`, `apply_fun f` will replace this with `f a ≠ f b`.
* If the goal is `a = b`, `apply_fun f` will replace this with `f a = f b`,
  and create a subsidiary goal `injective f`.
  `apply_fun` will automatically attempt to discharge this subsidiary goal using local hypotheses,
  or if `f` is actually an `Equiv`,
  or an explicit solution can be provided with `apply_fun f using P`, where `P : Injective f`.
* If the goal is `a ≤ b` (or similarly for `a < b`), and `f` is actually an `OrderIso`,
  `apply_fun f` will replace the goal with `f a ≤ f b`.
  If `f` is anything else (e.g. just a function, or an `Equiv`), `apply_fun` will fail.


Typical usage is:
```lean
open Function

example (X Y Z : Type) (f : X → Y) (g : Y → Z) (H : Injective <| g ∘ f) :
    Injective f := by
  intros x x' h
  apply_fun g at h
  exact H h
```

The function `f` is handled similarly to how it would be handled by `refine` in that `f` can contain
placeholders. Named placeholders (like `?a` or `?_`) will produce new goals.

# apply_gmonoid_gnpowRec_succ_tac
Defined in: `GradedMonoid.tacticApply_gmonoid_gnpowRec_succ_tac`

A tactic to for use as an optional value for `GMonoid.gnpow_succ'`.

# apply_gmonoid_gnpowRec_zero_tac
Defined in: `GradedMonoid.tacticApply_gmonoid_gnpowRec_zero_tac`

A tactic to for use as an optional value for `GMonoid.gnpow_zero'`.

# apply_mod_cast
Defined in: `Lean.Parser.Tactic.tacticApply_mod_cast_`

Normalize casts in the goal and the given expression, then `apply` the expression to the goal.

# apply_rfl
Defined in: `Lean.Parser.Tactic.applyRfl`

This tactic applies to a goal whose target has the form `x ~ x`,
where `~` is a reflexive relation other than `=`,
that is, a relation which has a reflexive lemma tagged with the attribute @[refl].

# apply_rules
Defined in: `Lean.Parser.Tactic.applyRules`

`apply_rules [l₁, l₂, ...]` tries to solve the main goal by iteratively
applying the list of lemmas `[l₁, l₂, ...]` or by applying a local hypothesis.
If `apply` generates new goals, `apply_rules` iteratively tries to solve those goals.
You can use `apply_rules [-h]` to omit a local hypothesis.

`apply_rules` will also use `rfl`, `trivial`, `congrFun` and `congrArg`.
These can be disabled, as can local hypotheses, by using `apply_rules only [...]`.

You can use `apply_rules using [a₁, ...]` to use all lemmas which have been labelled
with the attributes `aᵢ` (these attributes must be created using `register_label_attr`).

You can pass a further configuration via the syntax `apply_rules (config := {...})`.
The options supported are the same as for `solve_by_elim` (and include all the options for `apply`).

`apply_rules` will try calling `symm` on hypotheses and `exfalso` on the goal as needed.
This can be disabled with `apply_rules (config := {symm := false, exfalso := false})`.

You can bound the iteration depth using the syntax `apply_rules (config := {maxDepth := n})`.

Unlike `solve_by_elim`, `apply_rules` does not perform backtracking, and greedily applies
a lemma from the list until it gets stuck.

# arith_mult
Defined in: `ArithmeticFunction.arith_mult`

`arith_mult` solves goals of the form `IsMultiplicative f` for `f : ArithmeticFunction R`
by applying lemmas tagged with the user attribute `arith_mult`.

# arith_mult?
Defined in: `ArithmeticFunction.arith_mult?`

`arith_mult` solves goals of the form `IsMultiplicative f` for `f : ArithmeticFunction R`
by applying lemmas tagged with the user attribute `arith_mult`, and prints out the generated
proof term.

# array_get_dec
Defined in: `Array.tacticArray_get_dec`

This tactic, added to the `decreasing_trivial` toolbox, proves that
`sizeOf arr[i] < sizeOf arr`, which is useful for well founded recursions
over a nested inductive like `inductive T | mk : Array T → T`.

# array_mem_dec
Defined in: `Array.tacticArray_mem_dec`

This tactic, added to the `decreasing_trivial` toolbox, proves that `sizeOf a < sizeOf arr`
provided that `a ∈ arr` which is useful for well founded recursions over a nested inductive like
`inductive T | mk : Array T → T`.

# assumption
Defined in: `Lean.Parser.Tactic.assumption`

`assumption` tries to solve the main goal using a hypothesis of compatible type, or else fails.
Note also the `‹t›` term notation, which is a shorthand for `show t by assumption`.

# assumption'
Defined in: `Mathlib.Tactic.tacticAssumption'`

Try calling `assumption` on all goals; succeeds if it closes at least one goal.

# assumption_mod_cast
Defined in: `Lean.Parser.Tactic.tacticAssumption_mod_cast`

`assumption_mod_cast` is a variant of `assumption` that solves the goal
using a hypothesis. Unlike `assumption`, it first pre-processes the goal and
each hypothesis to move casts as far outwards as possible, so it can be used
in more situations.

Concretely, it runs `norm_cast` on the goal. For each local hypothesis `h`, it also
normalizes `h` with `norm_cast` and tries to use that to close the goal.

# aux_group₁
Defined in: `Mathlib.Tactic.Group.aux_group₁`

Auxiliary tactic for the `group` tactic. Calls the simplifier only.

# aux_group₂
Defined in: `Mathlib.Tactic.Group.aux_group₂`

Auxiliary tactic for the `group` tactic. Calls `ring_nf` to normalize exponents.

# bddDefault
Defined in: `tacticBddDefault`

Sets are automatically bounded or cobounded in complete lattices. To use the same statements
in complete and conditionally complete lattices but let automation fill automatically the
boundedness proofs in complete lattices, we use the tactic `bddDefault` in the statements,
in the form `(hA : BddAbove A := by bddDefault)`.

# beta_reduce
Defined in: `Mathlib.Tactic.betaReduceStx`

`beta_reduce at loc` completely beta reduces the given location.
This also exists as a `conv`-mode tactic.

This means that whenever there is an applied lambda expression such as
`(fun x => f x) y` then the argument is substituted into the lambda expression
yielding an expression such as `f y`.

# bicategory_coherence
Defined in: `Mathlib.Tactic.BicategoryCoherence.tacticBicategory_coherence`

Coherence tactic for bicategories.
Use `pure_coherence` instead, which is a frontend to this one.

# bitwise_assoc_tac
Defined in: `Nat.tacticBitwise_assoc_tac`

Proving associativity of bitwise operations in general essentially boils down to a huge case
distinction, so it is shorter to use this tactic instead of proving it in the general case.

# borelize
Defined in: `Mathlib.Tactic.Borelize.tacticBorelize___`

The behaviour of `borelize α` depends on the existing assumptions on `α`.

- if `α` is a topological space with instances `[MeasurableSpace α] [BorelSpace α]`, then
  `borelize α` replaces the former instance by `borel α`;
- otherwise, `borelize α` adds instances `borel α : MeasurableSpace α` and `⟨rfl⟩ : BorelSpace α`.

Finally, `borelize α β γ` runs `borelize α; borelize β; borelize γ`.

# bound
Defined in: `«tacticBound[_]»`

`bound` tactic for proving inequalities via straightforward recursion on expression structure.

An example use case is

```
-- Calc example: A weak lower bound for `z ↦ z^2 + c`
lemma le_sqr_add {c z : ℂ} (cz : abs c ≤ abs z) (z3 : 3 ≤ abs z) :
    2 * abs z ≤ abs (z^2 + c) := by
  calc abs (z^2 + c)
    _ ≥ abs (z^2) - abs c := by bound
    _ ≥ abs (z^2) - abs z := by bound
    _ ≥ (abs z - 1) * abs z := by rw [mul_comm, mul_sub_one, ← pow_two, ← abs.map_pow]
    _ ≥ 2 * abs z := by bound
```

`bound` is built on top of `aesop`, and uses
1. Apply lemmas registered via the `@[bound]` attribute
2. Forward lemmas registered via the `@[bound_forward]` attribute
3. Local hypotheses from the context
4. Optionally: additional hypotheses provided as `bound [h₀, h₁]` or similar. These are added to the
   context as if by `have := hᵢ`.

The functionality of `bound` overlaps with `positivity` and `gcongr`, but can jump back and forth
between `0 ≤ x` and `x ≤ y`-type inequalities.  For example, `bound` proves
  `0 ≤ c → b ≤ a → 0 ≤ a * c - b * c`
by turning the goal into `b * c ≤ a * c`, then using `mul_le_mul_of_nonneg_right`.  `bound` also
contains lemmas for goals of the form `1 ≤ x, 1 < x, x ≤ 1, x < 1`.  Conversely, `gcongr` can prove
inequalities for more types of relations, supports all `positivity` functionality, and is likely
faster since it is more specialized (not built atop `aesop`).

# bv_check
Defined in: `Lean.Parser.Tactic.bvCheck`

This tactic works just like `bv_decide` but skips calling a SAT solver by using a proof that is
alreay stored on disk. It is called with the name of an LRAT file in the same directory as the
current Lean file:
```lean
bv_check "proof.lrat"
```

# bv_decide
Defined in: `Lean.Parser.Tactic.bvDecide`

Close fixed-width `BitVec` and `Bool` goals by obtaining a proof from an external SAT solver and
verifying it inside Lean. The solvable goals are currently limited to the Lean equivalent of
[`QF_BV`](https://smt-lib.org/logics-all.shtml#QF_BV) with the following changes:
- Division and remainder operations are not yet implemented.
- if-then-else is not yet implemented.
- `BitVec.ofBool` is not yet implemented.

```lean
example : ∀ (a b : BitVec 64), (a &&& b) + (a ^^^ b) = a ||| b := by
  intros
  bv_decide
```

If `bv_decide` encounters an unknown definition it will be treated like an unconstrained `BitVec`
variable. Sometimes this enables solving goals despite not understanding the definition because
the precise properties of the definition do not matter in the specific proof.

If `bv_decide` fails to close a goal it provides a counter-example, containing assignments for all
terms that were considered as variables.

In order to avoid calling a SAT solver every time, the proof can be cached with `bv_decide?`.

Note: `bv_decide` uses `ofReduceBool` and thus trusts the correctness of the code generator.

# bv_decide?
Defined in: `Lean.Parser.Tactic.bvTrace`

Suggest a proof script for a `bv_decide` tactic call. Useful for caching LRAT proofs.

# bv_normalize
Defined in: `Lean.Parser.Tactic.bvNormalize`

Run the normalization procedure of `bv_decide` only. Sometimes this is enough to solve basic
`BitVec` goals already.

# bv_omega
Defined in: `Lean.Parser.Tactic.tacticBv_omega`

`bv_omega` is `omega` with an additional preprocessor that turns statements about `BitVec` into statements about `Nat`.
Currently the preprocessor is implemented as `try simp only [bv_toNat] at *`.
`bv_toNat` is a `@[simp]` attribute that you can (cautiously) add to more theorems.

# by_cases
Defined in: `«tacticBy_cases_:_»`

`by_cases (h :)? p` splits the main goal into two cases, assuming `h : p` in the first branch, and `h : ¬ p` in the second branch.

# by_contra
Defined in: `Batteries.Tactic.byContra`

`by_contra h` proves `⊢ p` by contradiction,
introducing a hypothesis `h : ¬p` and proving `False`.
* If `p` is a negation `¬q`, `h : q` will be introduced instead of `¬¬q`.
* If `p` is decidable, it uses `Decidable.byContradiction` instead of `Classical.byContradiction`.
* If `h` is omitted, the introduced variable `_: ¬p` will be anonymous.

# by_contra!
Defined in: `byContra!`

If the target of the main goal is a proposition `p`,
`by_contra!` reduces the goal to proving `False` using the additional hypothesis `this : ¬ p`.
`by_contra! h` can be used to name the hypothesis `h : ¬ p`.
The hypothesis `¬ p` will be negation normalized using `push_neg`.
For instance, `¬ a < b` will be changed to `b ≤ a`.
`by_contra! h : q` will normalize negations in `¬ p`, normalize negations in `q`,
and then check that the two normalized forms are equal.
The resulting hypothesis is the pre-normalized form, `q`.
If the name `h` is not explicitly provided, then `this` will be used as name.
This tactic uses classical reasoning.
It is a variant on the tactic `by_contra`.
Examples:
```lean
example : 1 < 2 := by
  by_contra! h
  -- h : 2 ≤ 1 ⊢ False

example : 1 < 2 := by
  by_contra! h : ¬ 1 < 2
  -- h : ¬ 1 < 2 ⊢ False
```

# calc
Defined in: `Lean.calcTactic`

Step-wise reasoning over transitive relations.
```lean
calc
  a = b := pab
  b = c := pbc
  ...
  y = z := pyz
```
proves `a = z` from the given step-wise proofs. `=` can be replaced with any
relation implementing the typeclass `Trans`. Instead of repeating the right-
hand sides, subsequent left-hand sides can be replaced with `_`.
```
calc
  a = b := pab
  _ = c := pbc
  ...
  _ = z := pyz
```
It is also possible to write the *first* relation as `<lhs>\n  _ = <rhs> :=
<proof>`. This is useful for aligning relation symbols, especially on longer:
identifiers:
```lean
calc abc
  _ = bce := pabce
  _ = cef := pbcef
  ...
  _ = xyz := pwxyz
```

`calc` works as a term, as a tactic or as a `conv` tactic.

See [Theorem Proving in Lean 4][tpil4] for more information.

[tpil4]: https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#calculational-proofs

# cancel_denoms
Defined in: `tacticCancel_denoms_`


# cancel_denoms
Defined in: `cancelDenoms`

`cancel_denoms` attempts to remove numerals from the denominators of fractions.
It works on propositions that are field-valued inequalities.

```lean
variable [LinearOrderedField α] (a b c : α)

example (h : a / 5 + b / 4 < c) : 4*a + 5*b < 20*c := by
  cancel_denoms at h
  exact h

example (h : a > 0) : a / 5 > 0 := by
  cancel_denoms
  exact h
```

# case
Defined in: `Batteries.Tactic.casePatt`

* `case _ : t => tac` finds the first goal that unifies with `t` and then solves it
using `tac` or else fails. Like `show`, it changes the type of the goal to `t`.
The `_` can optionally be a case tag, in which case it only looks at goals
whose tag would be considered by `case` (goals with an exact tag match,
followed by goals with the tag as a suffix, followed by goals with the tag as a prefix).

* `case _ n₁ ... nₘ : t => tac` additionally names the `m` most recent hypotheses with
inaccessible names to the given names. The names are renamed before matching against `t`.
The `_` can optionally be a case tag.

* `case _ : t := e` is short for `case _ : t => exact e`.

* `case _ : t₁ | _ : t₂ | ... => tac`
is equivalent to `(case _ : t₁ => tac); (case _ : t₂ => tac); ...`
but with all matching done on the original list of goals --
each goal is consumed as they are matched, so patterns may repeat or overlap.

* `case _ : t` will make the matched goal be the first goal.
`case _ : t₁ | _ : t₂ | ...` makes the matched goals be the first goals in the given order.

* `case _ : t := _` and `case _ : t := ?m` are the same as `case _ : t` but in the `?m` case the
goal tag is changed to `m`.
In particular, the goal becomes metavariable `?m`.

# case
Defined in: `Lean.Parser.Tactic.case`

* `case tag => tac` focuses on the goal with case name `tag` and solves it using `tac`,
  or else fails.
* `case tag x₁ ... xₙ => tac` additionally renames the `n` most recent hypotheses
  with inaccessible names to the given names.
* `case tag₁ | tag₂ => tac` is equivalent to `(case tag₁ => tac); (case tag₂ => tac)`.

# case'
Defined in: `Lean.Parser.Tactic.case'`

`case'` is similar to the `case tag => tac` tactic, but does not ensure the goal
has been solved after applying `tac`, nor admits the goal if `tac` failed.
Recall that `case` closes the goal using `sorry` when `tac` fails, and
the tactic execution is not interrupted.

# case'
Defined in: `Batteries.Tactic.casePatt'`

`case' _ : t => tac` is similar to the `case _ : t => tac` tactic,
but it does not ensure the goal has been solved after applying `tac`,
nor does it admit the goal if `tac` failed.
Recall that `case` closes the goal using `sorry` when `tac` fails,
and the tactic execution is not interrupted.

# cases
Defined in: `Lean.Parser.Tactic.cases`

Assuming `x` is a variable in the local context with an inductive type,
`cases x` splits the main goal, producing one goal for each constructor of the
inductive type, in which the target is replaced by a general instance of that constructor.
If the type of an element in the local context depends on `x`,
that element is reverted and reintroduced afterward,
so that the case split affects that hypothesis as well.
`cases` detects unreachable cases and closes them automatically.

For example, given `n : Nat` and a goal with a hypothesis `h : P n` and target `Q n`,
`cases n` produces one goal with hypothesis `h : P 0` and target `Q 0`,
and one goal with hypothesis `h : P (Nat.succ a)` and target `Q (Nat.succ a)`.
Here the name `a` is chosen automatically and is not accessible.
You can use `with` to provide the variables names for each constructor.
- `cases e`, where `e` is an expression instead of a variable, generalizes `e` in the goal,
  and then cases on the resulting variable.
- Given `as : List α`, `cases as with | nil => tac₁ | cons a as' => tac₂`,
  uses tactic `tac₁` for the `nil` case, and `tac₂` for the `cons` case,
  and `a` and `as'` are used as names for the new variables introduced.
- `cases h : e`, where `e` is a variable or an expression,
  performs cases on `e` as above, but also adds a hypothesis `h : e = ...` to each hypothesis,
  where `...` is the constructor instance for that particular case.

# cases'
Defined in: `Mathlib.Tactic.cases'`

The `cases'` tactic is similar to the `cases` tactic in Lean 4 core, but the syntax for giving
names is different:

```
example (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

example (h : p ∨ q) : q ∨ p := by
  cases' h with hp hq
  · exact Or.inr hp
  · exact Or.inl hq

example (h : p ∨ q) : q ∨ p := by
  rcases h with hp | hq
  · exact Or.inr hp
  · exact Or.inl hq
```

Prefer `cases` or `rcases` when possible, because these tactics promote structured proofs.

# cases_type
Defined in: `Mathlib.Tactic.casesType`

* `cases_type I` applies the `cases` tactic to a hypothesis `h : (I ...)`
* `cases_type I_1 ... I_n` applies the `cases` tactic to a hypothesis
  `h : (I_1 ...)` or ... or `h : (I_n ...)`
* `cases_type* I` is shorthand for `· repeat cases_type I`
* `cases_type! I` only applies `cases` if the number of resulting subgoals is <= 1.

Example: The following tactic destructs all conjunctions and disjunctions in the current goal.
```lean
cases_type* Or And
```

# cases_type!
Defined in: `Mathlib.Tactic.casesType!`

* `cases_type I` applies the `cases` tactic to a hypothesis `h : (I ...)`
* `cases_type I_1 ... I_n` applies the `cases` tactic to a hypothesis
  `h : (I_1 ...)` or ... or `h : (I_n ...)`
* `cases_type* I` is shorthand for `· repeat cases_type I`
* `cases_type! I` only applies `cases` if the number of resulting subgoals is <= 1.

Example: The following tactic destructs all conjunctions and disjunctions in the current goal.
```lean
cases_type* Or And
```

# casesm
Defined in: `Mathlib.Tactic.casesM`

* `casesm p` applies the `cases` tactic to a hypothesis `h : type`
  if `type` matches the pattern `p`.
* `casesm p_1, ..., p_n` applies the `cases` tactic to a hypothesis `h : type`
  if `type` matches one of the given patterns.
* `casesm* p` is a more efficient and compact version of `· repeat casesm p`.
  It is more efficient because the pattern is compiled once.

Example: The following tactic destructs all conjunctions and disjunctions in the current context.
```lean
casesm* _ ∨ _, _ ∧ _
```

# cc
Defined in: `Mathlib.Tactic.cc`

The congruence closure tactic `cc` tries to solve the goal by chaining
equalities from context and applying congruence (i.e. if `a = b`, then `f a = f b`).
It is a finishing tactic, i.e. it is meant to close
the current goal, not to make some inconclusive progress.
A mostly trivial example would be:

```lean
example (a b c : ℕ) (f : ℕ → ℕ) (h: a = b) (h' : b = c) : f a = f c := by
  cc
```

As an example requiring some thinking to do by hand, consider:

```lean
example (f : ℕ → ℕ) (x : ℕ)
    (H1 : f (f (f x)) = x) (H2 : f (f (f (f (f x)))) = x) :
    f x = x := by
  cc
```

# cfc_cont_tac
Defined in: `cfcContTac`

A tactic used to automatically discharge goals relating to the continuous functional calculus,
specifically concerning continuity of the functions involved.

# cfc_tac
Defined in: `cfcTac`

A tactic used to automatically discharge goals relating to the continuous functional calculus,
specifically whether the element satisfies the predicate.

# cfc_zero_tac
Defined in: `cfcZeroTac`

A tactic used to automatically discharge goals relating to the non-unital continuous functional
calculus, specifically concerning whether `f 0 = 0`.

# change
Defined in: `Lean.Parser.Tactic.change`

* `change tgt'` will change the goal from `tgt` to `tgt'`,
  assuming these are definitionally equal.
* `change t' at h` will change hypothesis `h : t` to have type `t'`, assuming
  assuming `t` and `t'` are definitionally equal.

# change
Defined in: `Lean.Parser.Tactic.changeWith`

* `change a with b` will change occurrences of `a` to `b` in the goal,
  assuming `a` and `b` are are definitionally equal.
* `change a with b at h` similarly changes `a` to `b` in the type of hypothesis `h`.

# change?
Defined in: `change?`

`change? term` unifies `term` with the current goal, then suggests explicit `change` syntax
that uses the resulting unified term.

If `term` is not present, `change?` suggests the current goal itself. This is useful after tactics
which transform the goal while maintaining definitional equality, such as `dsimp`; those preceding
tactic calls can then be deleted.
```lean
example : (fun x : Nat => x) 0 = 1 := by
  change? 0 = _  -- `Try this: change 0 = 1`
```

# checkpoint
Defined in: `Lean.Parser.Tactic.checkpoint`

`checkpoint tac` acts the same as `tac`, but it caches the input and output of `tac`,
and if the file is re-elaborated and the input matches, the tactic is not re-run and
its effects are reapplied to the state. This is useful for improving responsiveness
when working on a long tactic proof, by wrapping expensive tactics with `checkpoint`.

See the `save` tactic, which may be more convenient to use.

(TODO: do this automatically and transparently so that users don't have to use
this combinator explicitly.)

# choose
Defined in: `Mathlib.Tactic.Choose.choose`

* `choose a b h h' using hyp` takes a hypothesis `hyp` of the form
  `∀ (x : X) (y : Y), ∃ (a : A) (b : B), P x y a b ∧ Q x y a b`
  for some `P Q : X → Y → A → B → Prop` and outputs
  into context a function `a : X → Y → A`, `b : X → Y → B` and two assumptions:
  `h : ∀ (x : X) (y : Y), P x y (a x y) (b x y)` and
  `h' : ∀ (x : X) (y : Y), Q x y (a x y) (b x y)`. It also works with dependent versions.

* `choose! a b h h' using hyp` does the same, except that it will remove dependency of
  the functions on propositional arguments if possible. For example if `Y` is a proposition
  and `A` and `B` are nonempty in the above example then we will instead get
  `a : X → A`, `b : X → B`, and the assumptions
  `h : ∀ (x : X) (y : Y), P x y (a x) (b x)` and
  `h' : ∀ (x : X) (y : Y), Q x y (a x) (b x)`.

The `using hyp` part can be omitted,
which will effectively cause `choose` to start with an `intro hyp`.

Examples:

```
example (h : ∀ n m : ℕ, ∃ i j, m = n + i ∨ m + j = n) : True := by
  choose i j h using h
  guard_hyp i : ℕ → ℕ → ℕ
  guard_hyp j : ℕ → ℕ → ℕ
  guard_hyp h : ∀ (n m : ℕ), m = n + i n m ∨ m + j n m = n
  trivial
```

```
example (h : ∀ i : ℕ, i < 7 → ∃ j, i < j ∧ j < i+i) : True := by
  choose! f h h' using h
  guard_hyp f : ℕ → ℕ
  guard_hyp h : ∀ (i : ℕ), i < 7 → i < f i
  guard_hyp h' : ∀ (i : ℕ), i < 7 → f i < i + i
  trivial
```

# choose!
Defined in: `Mathlib.Tactic.Choose.tacticChoose!___Using_`

* `choose a b h h' using hyp` takes a hypothesis `hyp` of the form
  `∀ (x : X) (y : Y), ∃ (a : A) (b : B), P x y a b ∧ Q x y a b`
  for some `P Q : X → Y → A → B → Prop` and outputs
  into context a function `a : X → Y → A`, `b : X → Y → B` and two assumptions:
  `h : ∀ (x : X) (y : Y), P x y (a x y) (b x y)` and
  `h' : ∀ (x : X) (y : Y), Q x y (a x y) (b x y)`. It also works with dependent versions.

* `choose! a b h h' using hyp` does the same, except that it will remove dependency of
  the functions on propositional arguments if possible. For example if `Y` is a proposition
  and `A` and `B` are nonempty in the above example then we will instead get
  `a : X → A`, `b : X → B`, and the assumptions
  `h : ∀ (x : X) (y : Y), P x y (a x) (b x)` and
  `h' : ∀ (x : X) (y : Y), Q x y (a x) (b x)`.

The `using hyp` part can be omitted,
which will effectively cause `choose` to start with an `intro hyp`.

Examples:

```
example (h : ∀ n m : ℕ, ∃ i j, m = n + i ∨ m + j = n) : True := by
  choose i j h using h
  guard_hyp i : ℕ → ℕ → ℕ
  guard_hyp j : ℕ → ℕ → ℕ
  guard_hyp h : ∀ (n m : ℕ), m = n + i n m ∨ m + j n m = n
  trivial
```

```
example (h : ∀ i : ℕ, i < 7 → ∃ j, i < j ∧ j < i+i) : True := by
  choose! f h h' using h
  guard_hyp f : ℕ → ℕ
  guard_hyp h : ∀ (i : ℕ), i < 7 → i < f i
  guard_hyp h' : ∀ (i : ℕ), i < 7 → f i < i + i
  trivial
```

# classical
Defined in: `Batteries.Tactic.tacticClassical_`

`classical tacs` runs `tacs` in a scope where `Classical.propDecidable` is a low priority
local instance.

Note that (unlike lean 3) `classical` is a scoping tactic - it adds the instance only within the
scope of the tactic.

# classical!
Defined in: `Batteries.Tactic.tacticClassical!`

`classical!` has been removed; use `classical` instead

# clean
Defined in: `Mathlib.Tactic.tacticClean_`

(Deprecated) `clean t` is a macro for `exact clean% t`.

# clean_wf
Defined in: `tacticClean_wf`

This tactic is used internally by lean before presenting the proof obligations from a well-founded
definition to the user via `decreasing_by`. It is not necessary to use this tactic manuall.

# clear
Defined in: `Lean.Elab.Tactic.clearExcept`

Clears all hypotheses it can, except those provided after a minus sign. Example:
```lean
  clear * - h₁ h₂
```

# clear
Defined in: `Lean.Parser.Tactic.clear`

`clear x...` removes the given hypotheses, or fails if there are remaining
references to a hypothesis.

# clear!
Defined in: `Mathlib.Tactic.clear!`

A variant of `clear` which clears not only the given hypotheses but also any other hypotheses
depending on them

# clear_
Defined in: `Mathlib.Tactic.clear_`

Clear all hypotheses starting with `_`, like `_match` and `_let_match`.

# clear_aux_decl
Defined in: `Mathlib.Tactic.clearAuxDecl`

This tactic clears all auxiliary declarations from the context.

# clear_value
Defined in: `Mathlib.Tactic.clearValue`

`clear_value n₁ n₂ ...` clears the bodies of the local definitions `n₁, n₂ ...`, changing them
into regular hypotheses. A hypothesis `n : α := t` is changed to `n : α`.

The order of `n₁ n₂ ...` does not matter, and values will be cleared in reverse order of
where they appear in the context.

# coherence
Defined in: `Mathlib.Tactic.Coherence.coherence`

Use the coherence theorem for monoidal categories to solve equations in a monoidal equation,
where the two sides only differ by replacing strings of monoidal structural morphisms
(that is, associators, unitors, and identities)
with different strings of structural morphisms with the same source and target.

That is, `coherence` can handle goals of the form
`a ≫ f ≫ b ≫ g ≫ c = a' ≫ f ≫ b' ≫ g ≫ c'`
where `a = a'`, `b = b'`, and `c = c'` can be proved using `pure_coherence`.

(If you have very large equations on which `coherence` is unexpectedly failing,
you may need to increase the typeclass search depth,
using e.g. `set_option synthInstance.maxSize 500`.)

# compareOfLessAndEq_rfl
Defined in: `tacticCompareOfLessAndEq_rfl`

This attempts to prove that a given instance of `compare` is equal to `compareOfLessAndEq` by
introducing the arguments and trying the following approaches in order:

1. seeing if `rfl` works
2. seeing if the `compare` at hand is nonetheless essentially `compareOfLessAndEq`, but, because of
implicit arguments, requires us to unfold the defs and split the `if`s in the definition of
`compareOfLessAndEq`
3. seeing if we can split by cases on the arguments, then see if the defs work themselves out
  (useful when `compare` is defined via a `match` statement, as it is for `Bool`)

# compute_degree
Defined in: `Mathlib.Tactic.ComputeDegree.computeDegree`

`compute_degree` is a tactic to solve goals of the form
*  `natDegree f = d`,
*  `degree f = d`,
*  `natDegree f ≤ d`,
*  `degree f ≤ d`,
*  `coeff f d = r`, if `d` is the degree of `f`.

The tactic may leave goals of the form `d' = d` `d' ≤ d`, or `r ≠ 0`, where `d'` in `ℕ` or
`WithBot ℕ` is the tactic's guess of the degree, and `r` is the coefficient's guess of the
leading coefficient of `f`.

`compute_degree` applies `norm_num` to the left-hand side of all side goals, trying to close them.

The variant `compute_degree!` first applies `compute_degree`.
Then it uses `norm_num` on all the whole remaining goals and tries `assumption`.

# compute_degree!
Defined in: `Mathlib.Tactic.ComputeDegree.tacticCompute_degree!`

`compute_degree` is a tactic to solve goals of the form
*  `natDegree f = d`,
*  `degree f = d`,
*  `natDegree f ≤ d`,
*  `degree f ≤ d`,
*  `coeff f d = r`, if `d` is the degree of `f`.

The tactic may leave goals of the form `d' = d` `d' ≤ d`, or `r ≠ 0`, where `d'` in `ℕ` or
`WithBot ℕ` is the tactic's guess of the degree, and `r` is the coefficient's guess of the
leading coefficient of `f`.

`compute_degree` applies `norm_num` to the left-hand side of all side goals, trying to close them.

The variant `compute_degree!` first applies `compute_degree`.
Then it uses `norm_num` on all the whole remaining goals and tries `assumption`.

# congr
Defined in: `Lean.Parser.Tactic.congr`

Apply congruence (recursively) to goals of the form `⊢ f as = f bs` and `⊢ HEq (f as) (f bs)`.
The optional parameter is the depth of the recursive applications.
This is useful when `congr` is too aggressive in breaking down the goal.
For example, given `⊢ f (g (x + y)) = f (g (y + x))`,
`congr` produces the goals `⊢ x = y` and `⊢ y = x`,
while `congr 2` produces the intended `⊢ x + y = y + x`.

# congr
Defined in: `Batteries.Tactic.congrConfigWith`

Apply congruence (recursively) to goals of the form `⊢ f as = f bs` and `⊢ HEq (f as) (f bs)`.
* `congr n` controls the depth of the recursive applications.
  This is useful when `congr` is too aggressive in breaking down the goal.
  For example, given `⊢ f (g (x + y)) = f (g (y + x))`,
  `congr` produces the goals `⊢ x = y` and `⊢ y = x`,
  while `congr 2` produces the intended `⊢ x + y = y + x`.
* If, at any point, a subgoal matches a hypothesis then the subgoal will be closed.
* You can use `congr with p (: n)?` to call `ext p (: n)?` to all subgoals generated by `congr`.
  For example, if the goal is `⊢ f '' s = g '' s` then `congr with x` generates the goal
  `x : α ⊢ f x = g x`.

# congr
Defined in: `Batteries.Tactic.congrConfig`

Apply congruence (recursively) to goals of the form `⊢ f as = f bs` and `⊢ HEq (f as) (f bs)`.
The optional parameter is the depth of the recursive applications.
This is useful when `congr` is too aggressive in breaking down the goal.
For example, given `⊢ f (g (x + y)) = f (g (y + x))`,
`congr` produces the goals `⊢ x = y` and `⊢ y = x`,
while `congr 2` produces the intended `⊢ x + y = y + x`.

# congr!
Defined in: `Congr!.congr!`

Equates pieces of the left-hand side of a goal to corresponding pieces of the right-hand side by
recursively applying congruence lemmas. For example, with `⊢ f as = g bs` we could get
two goals `⊢ f = g` and `⊢ as = bs`.

Syntax:
```lean
congr!
congr! n
congr! with x y z
congr! n with x y z
```
Here, `n` is a natural number and `x`, `y`, `z` are `rintro` patterns (like `h`, `rfl`, `⟨x, y⟩`,
`_`, `-`, `(h | h)`, etc.).

The `congr!` tactic is similar to `congr` but is more insistent in trying to equate left-hand sides
to right-hand sides of goals. Here is a list of things it can try:

- If `R` in `⊢ R x y` is a reflexive relation, it will convert the goal to `⊢ x = y` if possible.
  The list of reflexive relations is maintained using the `@[refl]` attribute.
  As a special case, `⊢ p ↔ q` is converted to `⊢ p = q` during congruence processing and then
  returned to `⊢ p ↔ q` form at the end.

- If there is a user congruence lemma associated to the goal (for instance, a `@[congr]`-tagged
  lemma applying to `⊢ List.map f xs = List.map g ys`), then it will use that.

- It uses a congruence lemma generator at least as capable as the one used by `congr` and `simp`.
  If there is a subexpression that can be rewritten by `simp`, then `congr!` should be able
  to generate an equality for it.

- It can do congruences of pi types using lemmas like `implies_congr` and `pi_congr`.

- Before applying congruences, it will run the `intros` tactic automatically.
  The introduced variables can be given names using a `with` clause.
  This helps when congruence lemmas provide additional assumptions in hypotheses.

- When there is an equality between functions, so long as at least one is obviously a lambda, we
  apply `funext` or `Function.hfunext`, which allows for congruence of lambda bodies.

- It can try to close goals using a few strategies, including checking
  definitional equality, trying to apply `Subsingleton.elim` or `proof_irrel_heq`, and using the
  `assumption` tactic.

The optional parameter is the depth of the recursive applications.
This is useful when `congr!` is too aggressive in breaking down the goal.
For example, given `⊢ f (g (x + y)) = f (g (y + x))`,
`congr!` produces the goals `⊢ x = y` and `⊢ y = x`,
while `congr! 2` produces the intended `⊢ x + y = y + x`.

The `congr!` tactic also takes a configuration option, for example
```lean
congr! (config := {transparency := .default}) 2
```
This overrides the default, which is to apply congruence lemmas at reducible transparency.

The `congr!` tactic is aggressive with equating two sides of everything. There is a predefined
configuration that uses a different strategy:
Try
```lean
congr! (config := .unfoldSameFun)
```
This only allows congruences between functions applications of definitionally equal functions,
and it applies congruence lemmas at default transparency (rather than just reducible).
This is somewhat like `congr`.

See `Congr!.Config` for all options.

# congrm
Defined in: `Mathlib.Tactic.congrM`

`congrm e` is a tactic for proving goals of the form `lhs = rhs`, `lhs ↔ rhs`, `HEq lhs rhs`,
or `R lhs rhs` when `R` is a reflexive relation.
The expression `e` is a pattern containing placeholders `?_`,
and this pattern is matched against `lhs` and `rhs` simultaneously.
These placeholders generate new goals that state that corresponding subexpressions
in `lhs` and `rhs` are equal.
If the placeholders have names, such as `?m`, then the new goals are given tags with those names.

Examples:
```lean
example {a b c d : ℕ} :
    Nat.pred a.succ * (d + (c + a.pred)) = Nat.pred b.succ * (b + (c + d.pred)) := by
  congrm Nat.pred (Nat.succ ?h1) * (?h2 + ?h3)
  /-  Goals left:
  case h1 ⊢ a = b
  case h2 ⊢ d = b
  case h3 ⊢ c + a.pred = c + d.pred
  -/
  sorry
  sorry
  sorry

example {a b : ℕ} (h : a = b) : (fun y : ℕ => ∀ z, a + a = z) = (fun x => ∀ z, b + a = z) := by
  congrm fun x => ∀ w, ?_ + a = w
  -- ⊢ a = b
  exact h
```

The `congrm` command is a convenient frontend to `congr(...)` congruence quotations.
If the goal is an equality, `congrm e` is equivalent to `refine congr(e')` where `e'` is
built from `e` by replacing each placeholder `?m` by `$(?m)`.
The pattern `e` is allowed to contain `$(...)` expressions to immediately substitute
equality proofs into the congruence, just like for congruence quotations.

# congrm?
Defined in: `tacticCongrm?`

Display a widget panel allowing to generate a `congrm` call with holes specified by selecting
subexpressions in the goal.

# constructor
Defined in: `Lean.Parser.Tactic.constructor`

If the main goal's target type is an inductive type, `constructor` solves it with
the first matching constructor, or else fails.

# constructorm
Defined in: `Mathlib.Tactic.constructorM`

* `constructorm p_1, ..., p_n` applies the `constructor` tactic to the main goal
  if `type` matches one of the given patterns.
* `constructorm* p` is a more efficient and compact version of `· repeat constructorm p`.
  It is more efficient because the pattern is compiled once.

Example: The following tactic proves any theorem like `True ∧ (True ∨ True)` consisting of
and/or/true:
```lean
constructorm* _ ∨ _, _ ∧ _, True
```

# continuity
Defined in: `tacticContinuity`

The tactic `continuity` solves goals of the form `Continuous f` by applying lemmas tagged with the
`continuity` user attribute.

# continuity?
Defined in: `tacticContinuity?`

The tactic `continuity` solves goals of the form `Continuous f` by applying lemmas tagged with the
`continuity` user attribute.

# contradiction
Defined in: `Lean.Parser.Tactic.contradiction`

`contradiction` closes the main goal if its hypotheses are "trivially contradictory".
- Inductive type/family with no applicable constructors
```lean
example (h : False) : p := by contradiction
```
- Injectivity of constructors
```lean
example (h : none = some true) : p := by contradiction  --
```
- Decidable false proposition
```lean
example (h : 2 + 2 = 3) : p := by contradiction
```
- Contradictory hypotheses
```lean
example (h : p) (h' : ¬ p) : q := by contradiction
```
- Other simple contradictions such as
```lean
example (x : Nat) (h : x ≠ x) : p := by contradiction
```

# contrapose
Defined in: `Mathlib.Tactic.Contrapose.contrapose`

Transforms the goal into its contrapositive.
* `contrapose`     turns a goal `P → Q` into `¬ Q → ¬ P`
* `contrapose h`   first reverts the local assumption `h`, and then uses `contrapose` and `intro h`
* `contrapose h with new_h` uses the name `new_h` for the introduced hypothesis

# contrapose!
Defined in: `Mathlib.Tactic.Contrapose.contrapose!`

Transforms the goal into its contrapositive and uses pushes negations inside `P` and `Q`.
Usage matches `contrapose`

# conv
Defined in: `Lean.Parser.Tactic.Conv.conv`

`conv => ...` allows the user to perform targeted rewriting on a goal or hypothesis,
by focusing on particular subexpressions.

See <https://lean-lang.org/theorem_proving_in_lean4/conv.html> for more details.

Basic forms:
* `conv => cs` will rewrite the goal with conv tactics `cs`.
* `conv at h => cs` will rewrite hypothesis `h`.
* `conv in pat => cs` will rewrite the first subexpression matching `pat` (see `pattern`).

# conv'
Defined in: `Lean.Parser.Tactic.Conv.convTactic`

Executes the given conv block without converting regular goal into a `conv` goal.

# conv?
Defined in: `tacticConv?`

Display a widget panel allowing to generate a `conv` call zooming to the subexpression selected
in the goal.

# conv_lhs
Defined in: `Mathlib.Tactic.Conv.convLHS`


# conv_rhs
Defined in: `Mathlib.Tactic.Conv.convRHS`


# convert
Defined in: `Mathlib.Tactic.convert`

The `exact e` and `refine e` tactics require a term `e` whose type is
definitionally equal to the goal. `convert e` is similar to `refine e`,
but the type of `e` is not required to exactly match the
goal. Instead, new goals are created for differences between the type
of `e` and the goal using the same strategies as the `congr!` tactic.
For example, in the proof state

```lean
n : ℕ,
e : Prime (2 * n + 1)
⊢ Prime (n + n + 1)
```

the tactic `convert e using 2` will change the goal to

```lean
⊢ n + n = 2 * n
```

In this example, the new goal can be solved using `ring`.

The `using 2` indicates it should iterate the congruence algorithm up to two times,
where `convert e` would use an unrestricted number of iterations and lead to two
impossible goals: `⊢ HAdd.hAdd = HMul.hMul` and `⊢ n = 2`.

A variant configuration is `convert (config := .unfoldSameFun) e`, which only equates function
applications for the same function (while doing so at the higher `default` transparency).
This gives the same goal of `⊢ n + n = 2 * n` without needing `using 2`.

The `convert` tactic applies congruence lemmas eagerly before reducing,
therefore it can fail in cases where `exact` succeeds:
```lean
def p (n : ℕ) := True
example (h : p 0) : p 1 := by exact h -- succeeds
example (h : p 0) : p 1 := by convert h -- fails, with leftover goal `1 = 0`
```
Limiting the depth of recursion can help with this. For example, `convert h using 1` will work
in this case.

The syntax `convert ← e` will reverse the direction of the new goals
(producing `⊢ 2 * n = n + n` in this example).

Internally, `convert e` works by creating a new goal asserting that
the goal equals the type of `e`, then simplifying it using
`congr!`. The syntax `convert e using n` can be used to control the
depth of matching (like `congr! n`). In the example, `convert e using 1`
would produce a new goal `⊢ n + n + 1 = 2 * n + 1`.

Refer to the `congr!` tactic to understand the congruence operations. One of its many
features is that if `x y : t` and an instance `Subsingleton t` is in scope,
then any goals of the form `x = y` are solved automatically.

Like `congr!`, `convert` takes an optional `with` clause of `rintro` patterns,
for example `convert e using n with x y z`.

The `convert` tactic also takes a configuration option, for example
```lean
convert (config := {transparency := .default}) h
```
These are passed to `congr!`. See `Congr!.Config` for options.

# convert_to
Defined in: `Mathlib.Tactic.convertTo`

The `convert_to` tactic is for changing the type of the target or a local hypothesis,
but unlike the `change` tactic it will generate equality proof obligations using `congr!`
to resolve discrepancies.

* `convert_to ty` changes the target to `ty`
* `convert_to ty using n` uses `congr! n` instead of `congr! 1`
* `convert_to ty at h` changes the type of the local hypothesis `h` to `ty`.
  Any remaining `congr!` goals come first.

Operating on the target, the tactic `convert_to ty using n`
is the same as `convert (?_ : ty) using n`.
The difference is that `convert_to` takes a type but `convert` takes a proof term.

Except for it also being able to operate on local hypotheses,
the syntax for `convert_to` is the same as for `convert`, and it has variations such as
`convert_to ← g` and `convert_to (config := {transparency := .default}) g`.

Note that `convert_to ty at h` may leave a copy of `h` if a later local hypotheses or the target
depends on it, just like in `rw` or `simp`.

# count_heartbeats
Defined in: `Mathlib.CountHeartbeats.tacticCount_heartbeats_`

Count the heartbeats used by a tactic, e.g.: `count_heartbeats simp`.

# count_heartbeats!
Defined in: `Mathlib.CountHeartbeats.tacticCount_heartbeats!_In__`

`count_heartbeats! in tac` runs a tactic 10 times, counting the heartbeats used, and logs the range
and standard deviation. The tactic `count_heartbeats! n in tac` runs it `n` times instead.

# dbg_trace
Defined in: `Lean.Parser.Tactic.dbgTrace`

`dbg_trace "foo"` prints `foo` when elaborated.
Useful for debugging tactic control flow:
```lean
example : False ∨ True := by
  first
  | apply Or.inl; trivial; dbg_trace "left"
  | apply Or.inr; trivial; dbg_trace "right"
```

# decide
Defined in: `Lean.Parser.Tactic.decide`

`decide` attempts to prove the main goal (with target type `p`) by synthesizing an instance of `Decidable p`
and then reducing that instance to evaluate the truth value of `p`.
If it reduces to `isTrue h`, then `h` is a proof of `p` that closes the goal.

Limitations:
- The target is not allowed to contain local variables or metavariables.
  If there are local variables, you can try first using the `revert` tactic with these local variables
  to move them into the target, which may allow `decide` to succeed.
- Because this uses kernel reduction to evaluate the term, `Decidable` instances defined
  by well-founded recursion might not work, because evaluating them requires reducing proofs.
  The kernel can also get stuck reducing `Decidable` instances with `Eq.rec` terms for rewriting propositions.
  These can appear for instances defined using tactics (such as `rw` and `simp`).
  To avoid this, use definitions such as `decidable_of_iff` instead.

## Examples

Proving inequalities:
```lean
example : 2 + 2 ≠ 5 := by decide
```

Trying to prove a false proposition:
```lean
example : 1 ≠ 1 := by decide
/-
tactic 'decide' proved that the proposition
  1 ≠ 1
is false
-/
```

Trying to prove a proposition whose `Decidable` instance fails to reduce
```lean
opaque unknownProp : Prop

open scoped Classical in
example : unknownProp := by decide
/-
tactic 'decide' failed for proposition
  unknownProp
since its 'Decidable' instance reduced to
  Classical.choice ⋯
rather than to the 'isTrue' constructor.
-/
```

## Properties and relations

For equality goals for types with decidable equality, usually `rfl` can be used in place of `decide`.
```lean
example : 1 + 1 = 2 := by decide
example : 1 + 1 = 2 := by rfl
```

# decreasing_tactic
Defined in: `tacticDecreasing_tactic`

`decreasing_tactic` is called by default on well-founded recursions in order
to synthesize a proof that recursive calls decrease along the selected
well founded relation. It can be locally overridden by using `decreasing_by tac`
on the recursive definition, and it can also be globally extended by adding
more definitions for `decreasing_tactic` (or `decreasing_trivial`,
which this tactic calls).

# decreasing_trivial
Defined in: `tacticDecreasing_trivial`

Extensible helper tactic for `decreasing_tactic`. This handles the "base case"
reasoning after applying lexicographic order lemmas.
It can be extended by adding more macro definitions, e.g.
```lean
macro_rules | `(tactic| decreasing_trivial) => `(tactic| linarith)
```

# decreasing_trivial_pre_omega
Defined in: `tacticDecreasing_trivial_pre_omega`

Variant of `decreasing_trivial` that does not use `omega`, intended to be used in core modules
before `omega` is available.

# decreasing_with
Defined in: `tacticDecreasing_with_`

Constructs a proof of decreasing along a well founded relation, by simplifying, then applying
lexicographic order lemmas and finally using `ts` to solve the base case. If it fails,
it prints a message to help the user diagnose an ill-founded recursive definition.

# delta
Defined in: `Lean.Parser.Tactic.delta`

`delta id1 id2 ...` delta-expands the definitions `id1`, `id2`, ....
This is a low-level tactic, it will expose how recursive definitions have been
compiled by Lean.

# discrete_cases
Defined in: `CategoryTheory.Discrete.tacticDiscrete_cases`

A simple tactic to run `cases` on any `Discrete α` hypotheses.

# done
Defined in: `Lean.Parser.Tactic.done`

`done` succeeds iff there are no remaining goals.

# dsimp
Defined in: `Lean.Parser.Tactic.dsimp`

The `dsimp` tactic is the definitional simplifier. It is similar to `simp` but only
applies theorems that hold by reflexivity. Thus, the result is guaranteed to be
definitionally equal to the input.

# dsimp!
Defined in: `Lean.Parser.Tactic.dsimpAutoUnfold`

`dsimp!` is shorthand for `dsimp` with `autoUnfold := true`.
This will rewrite with all equation lemmas, which can be used to
partially evaluate many definitions.

# dsimp?
Defined in: `Lean.Parser.Tactic.dsimpTrace`

`simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal. This is useful for reducing the size of the simp
set in a local invocation to speed up processing.
```lean
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- prints "Try this: simp only [ite_true]"
```

This command can also be used in `simp_all` and `dsimp`.

# dsimp?!
Defined in: `Lean.Parser.Tactic.tacticDsimp?!_`

`simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal. This is useful for reducing the size of the simp
set in a local invocation to speed up processing.
```lean
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- prints "Try this: simp only [ite_true]"
```

This command can also be used in `simp_all` and `dsimp`.

# eapply
Defined in: `Batteries.Tactic.tacticEapply_`

`eapply e` is like `apply e` but it does not add subgoals for variables that appear
in the types of other goals. Note that this can lead to a failure where there are
no goals remaining but there are still metavariables in the term:
```lean
example (h : ∀ x : Nat, x = x → True) : True := by
  eapply h
  rfl
  -- no goals
-- (kernel) declaration has metavariables '_example'
```

# econstructor
Defined in: `tacticEconstructor`

`econstructor` is like `constructor`
(it calls `apply` using the first matching constructor of an inductive datatype)
except only non-dependent premises are added as new goals.

# elementwise
Defined in: `Tactic.Elementwise.tacticElementwise___`


# elementwise!
Defined in: `Tactic.Elementwise.tacticElementwise!___`


# else
Defined in: `Lean.Parser.Tactic.tacDepIfThenElse`

In tactic mode, `if h : t then tac1 else tac2` can be used as alternative syntax for:
```lean
by_cases h : t
· tac1
· tac2
```
It performs case distinction on `h : t` or `h : ¬t` and `tac1` and `tac2` are the subproofs.

You can use `?_` or `_` for either subproof to delay the goal to after the tactic, but
if a tactic sequence is provided for `tac1` or `tac2` then it will require the goal to be closed
by the end of the block.

# else
Defined in: `Lean.Parser.Tactic.tacIfThenElse`

In tactic mode, `if t then tac1 else tac2` is alternative syntax for:
```lean
by_cases t
· tac1
· tac2
```
It performs case distinction on `h† : t` or `h† : ¬t`, where `h†` is an anonymous
hypothesis, and `tac1` and `tac2` are the subproofs. (It doesn't actually use
nondependent `if`, since this wouldn't add anything to the context and hence would be
useless for proving theorems. To actually insert an `ite` application use
`refine if t then ?_ else ?_`.)

# eq_refl
Defined in: `Lean.Parser.Tactic.eqRefl`

`eq_refl` is equivalent to `exact rfl`, but has a few optimizations.

# erw
Defined in: `Lean.Parser.Tactic.tacticErw__`

`erw [rules]` is a shorthand for `rw (config := { transparency := .default }) [rules]`.
This does rewriting up to unfolding of regular definitions (by comparison to regular `rw`
which only unfolds `@[reducible]` definitions).

# eta_expand
Defined in: `Mathlib.Tactic.etaExpandStx`

`eta_expand at loc` eta expands all sub-expressions at the given location.
It also beta reduces any applications of eta expanded terms, so it puts it
into an eta-expanded "normal form."
This also exists as a `conv`-mode tactic.

For example, if `f` takes two arguments, then `f` becomes `fun x y => f x y`
and `f x` becomes `fun y => f x y`.

This can be useful to turn, for example, a raw `HAdd.hAdd` into `fun x y => x + y`.

# eta_reduce
Defined in: `Mathlib.Tactic.etaReduceStx`

`eta_reduce at loc` eta reduces all sub-expressions at the given location.
This also exists as a `conv`-mode tactic.

For example, `fun x y => f x y` becomes `f` after eta reduction.

# eta_struct
Defined in: `Mathlib.Tactic.etaStructStx`

`eta_struct at loc` transforms structure constructor applications such as `S.mk x.1 ... x.n`
(pretty printed as, for example, `{a := x.a, b := x.b, ...}`) into `x`.
This also exists as a `conv`-mode tactic.

The transformation is known as eta reduction for structures, and it yields definitionally
equal expressions.

For example, given `x : α × β`, then `(x.1, x.2)` becomes `x` after this transformation.

# exact
Defined in: `Lean.Parser.Tactic.exact`

`exact e` closes the main goal if its target type matches that of `e`.

# exact?
Defined in: `Lean.Parser.Tactic.exact?`

Searches environment for definitions or theorems that can solve the goal using `exact`
with conditions resolved by `solve_by_elim`.

The optional `using` clause provides identifiers in the local context that must be
used by `exact?` when closing the goal.  This is most useful if there are multiple
ways to resolve the goal, and one wants to guide which lemma is used.

# exact_mod_cast
Defined in: `Lean.Parser.Tactic.tacticExact_mod_cast_`

Normalize casts in the goal and the given expression, then close the goal with `exact`.

# exacts
Defined in: `Batteries.Tactic.exacts`

Like `exact`, but takes a list of terms and checks that all goals are discharged after the tactic.

# exfalso
Defined in: `Lean.Parser.Tactic.tacticExfalso`

`exfalso` converts a goal `⊢ tgt` into `⊢ False` by applying `False.elim`.

# exists
Defined in: `Lean.Parser.Tactic.«tacticExists_,,»`

`exists e₁, e₂, ...` is shorthand for `refine ⟨e₁, e₂, ...⟩; try trivial`.
It is useful for existential goals.

# existsi
Defined in: `Mathlib.Tactic.«tacticExistsi_,,»`

`existsi e₁, e₂, ⋯` applies the tactic `refine ⟨e₁, e₂, ⋯, ?_⟩`. It's purpose is to instantiate
existential quantifiers.

Examples:

```lean
example : ∃ x : Nat, x = x := by
  existsi 42
  rfl

example : ∃ x : Nat, ∃ y : Nat, x = y := by
  existsi 42, 42
  rfl
```

# ext
Defined in: `Lean.Elab.Tactic.Ext.ext`

Applies extensionality lemmas that are registered with the `@[ext]` attribute.
* `ext pat*` applies extensionality theorems as much as possible,
  using the patterns `pat*` to introduce the variables in extensionality theorems using `rintro`.
  For example, the patterns are used to name the variables introduced by lemmas such as `funext`.
* Without patterns,`ext` applies extensionality lemmas as much
  as possible but introduces anonymous hypotheses whenever needed.
* `ext pat* : n` applies ext theorems only up to depth `n`.

The `ext1 pat*` tactic is like `ext pat*` except that it only applies a single extensionality theorem.

Unused patterns will generate warning.
Patterns that don't match the variables will typically result in the introduction of anonymous hypotheses.

# ext1
Defined in: `Lean.Elab.Tactic.Ext.tacticExt1___`

`ext1 pat*` is like `ext pat*` except that it only applies a single extensionality theorem rather
than recursively applying as many extensionality theorems as possible.

The `pat*` patterns are processed using the `rintro` tactic.
If no patterns are supplied, then variables are introduced anonymously using the `intros` tactic.

# extract_goal
Defined in: `Mathlib.Tactic.ExtractGoal.extractGoal`

- `extract_goal` formats the current goal as a stand-alone theorem or definition after
  cleaning up the local context of irrelevant variables.
  A variable is *relevant* if (1) it occurs in the target type, (2) there is a relevant variable
  that depends on it, or (3) the type of the variable is a proposition that depends on a
  relevant variable.

  If the target is `False`, then for convenience `extract_goal` includes all variables.
- `extract_goal *` formats the current goal without cleaning up the local context.
- `extract_goal a b c ...` formats the current goal after removing everything that the given
  variables `a`, `b`, `c`, ... do not depend on.
- `extract_goal ... using name` uses the name `name` for the theorem or definition rather than
  the autogenerated name.

The tactic tries to produce an output that can be copy-pasted and just work,
but its success depends on whether the expressions are amenable
to being unambiguously pretty printed.

The tactic responds to pretty printing options.
For example, `set_option pp.all true in extract_goal` gives the `pp.all` form.

# extract_lets
Defined in: `Mathlib.extractLets`

The `extract_lets at h` tactic takes a local hypothesis of the form `h : let x := v; b`
and introduces a new local definition `x := v` while changing `h` to be `h : b`.  It can be thought
of as being a `cases` tactic for `let` expressions. It can also be thought of as being like
`intros at h` for `let` expressions.

For example, if `h : let x := 1; x = x`, then `extract_lets x at h` introduces `x : Nat := 1` and
changes `h` to `h : x = x`.

Just like `intros`, the `extract_lets` tactic either takes a list of names, in which case
that specifies the number of `let` bindings that must be extracted, or it takes no names, in which
case all the `let` bindings are extracted.

The tactic `extract_lets` (without `at`) or `extract_lets at h ⊢` acts as a weaker
form of `intros` on the goal that only introduces obvious `let`s.

# fail
Defined in: `Lean.Parser.Tactic.fail`

`fail msg` is a tactic that always fails, and produces an error using the given message.

# fail_if_no_progress
Defined in: `Mathlib.Tactic.failIfNoProgress`

`fail_if_no_progress tacs` evaluates `tacs`, and fails if no progress is made on the main goal
or the local context at reducible transparency.

# fail_if_success
Defined in: `Lean.Parser.Tactic.failIfSuccess`

`fail_if_success t` fails if the tactic `t` succeeds.

# false_or_by_contra
Defined in: `Lean.Parser.Tactic.falseOrByContra`

Changes the goal to `False`, retaining as much information as possible:

* If the goal is `False`, do nothing.
* If the goal is an implication or a function type, introduce the argument and restart.
  (In particular, if the goal is `x ≠ y`, introduce `x = y`.)
* Otherwise, for a propositional goal `P`, replace it with `¬ ¬ P`
  (attempting to find a `Decidable` instance, but otherwise falling back to working classically)
  and introduce `¬ P`.
* For a non-propositional goal use `False.elim`.

# fapply
Defined in: `Batteries.Tactic.tacticFapply_`

`fapply e` is like `apply e` but it adds goals in the order they appear,
rather than putting the dependent goals first.

# fconstructor
Defined in: `tacticFconstructor`

`fconstructor` is like `constructor`
(it calls `apply` using the first matching constructor of an inductive datatype)
except that it does not reorder goals.

# field_simp
Defined in: `Mathlib.Tactic.FieldSimp.fieldSimp`

The goal of `field_simp` is to reduce an expression in a field to an expression of the form `n / d`
where neither `n` nor `d` contains any division symbol, just using the simplifier (with a carefully
crafted simpset named `field_simps`) to reduce the number of division symbols whenever possible by
iterating the following steps:

- write an inverse as a division
- in any product, move the division to the right
- if there are several divisions in a product, group them together at the end and write them as a
  single division
- reduce a sum to a common denominator

If the goal is an equality, this simpset will also clear the denominators, so that the proof
can normally be concluded by an application of `ring`.

`field_simp [hx, hy]` is a short form for
`simp (disch := field_simp_discharge) [-one_div, -one_divp, -mul_eq_zero, hx, hy, field_simps]`

Note that this naive algorithm will not try to detect common factors in denominators to reduce the
complexity of the resulting expression. Instead, it relies on the ability of `ring` to handle
complicated expressions in the next step.

As always with the simplifier, reduction steps will only be applied if the preconditions of the
lemmas can be checked. This means that proofs that denominators are nonzero should be included. The
fact that a product is nonzero when all factors are, and that a power of a nonzero number is
nonzero, are included in the simpset, but more complicated assertions (especially dealing with sums)
should be given explicitly. If your expression is not completely reduced by the simplifier
invocation, check the denominators of the resulting expression and provide proofs that they are
nonzero to enable further progress.

To check that denominators are nonzero, `field_simp` will look for facts in the context, and
will try to apply `norm_num` to close numerical goals.

The invocation of `field_simp` removes the lemma `one_div` from the simpset, as this lemma
works against the algorithm explained above. It also removes
`mul_eq_zero : x * y = 0 ↔ x = 0 ∨ y = 0`, as `norm_num` can not work on disjunctions to
close goals of the form `24 ≠ 0`, and replaces it with `mul_ne_zero : x ≠ 0 → y ≠ 0 → x * y ≠ 0`
creating two goals instead of a disjunction.

For example,
```lean
example (a b c d x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    a + b / x + c / x^2 + d / x^3 = a + x⁻¹ * (y * b / y + (d / x + c) / x) := by
  field_simp
  ring
```

Moreover, the `field_simp` tactic can also take care of inverses of units in
a general (commutative) monoid/ring and partial division `/ₚ`, see `Algebra.Group.Units`
for the definition. Analogue to the case above, the lemma `one_divp` is removed from the simpset
as this works against the algorithm. If you have objects with an `IsUnit x` instance like
`(x : R) (hx : IsUnit x)`, you should lift them with
`lift x to Rˣ using id hx; rw [IsUnit.unit_of_val_units] clear hx`
before using `field_simp`.

See also the `cancel_denoms` tactic, which tries to do a similar simplification for expressions
that have numerals in denominators.
The tactics are not related: `cancel_denoms` will only handle numeric denominators, and will try to
entirely remove (numeric) division from the expression by multiplying by a factor.

# field_simp_discharge
Defined in: `Mathlib.Tactic.FieldSimp.tacticField_simp_discharge`

Discharge strategy for the `field_simp` tactic.

# filter_upwards
Defined in: `Mathlib.Tactic.filterUpwards`

`filter_upwards [h₁, ⋯, hₙ]` replaces a goal of the form `s ∈ f` and terms
`h₁ : t₁ ∈ f, ⋯, hₙ : tₙ ∈ f` with `∀ x, x ∈ t₁ → ⋯ → x ∈ tₙ → x ∈ s`.
The list is an optional parameter, `[]` being its default value.

`filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ` is a short form for
`{ filter_upwards [h₁, ⋯, hₙ], intros a₁ a₂ ⋯ aₖ }`.

`filter_upwards [h₁, ⋯, hₙ] using e` is a short form for
`{ filter_upwards [h1, ⋯, hn], exact e }`.

Combining both shortcuts is done by writing `filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ using e`.
Note that in this case, the `aᵢ` terms can be used in `e`.

# fin_cases
Defined in: `Lean.Elab.Tactic.finCases`

`fin_cases h` performs case analysis on a hypothesis of the form
`h : A`, where `[Fintype A]` is available, or
`h : a ∈ A`, where `A : Finset X`, `A : Multiset X` or `A : List X`.

As an example, in
```
example (f : ℕ → Prop) (p : Fin 3) (h0 : f 0) (h1 : f 1) (h2 : f 2) : f p.val := by
  fin_cases p; simp
  all_goals assumption
```
after `fin_cases p; simp`, there are three goals, `f 0`, `f 1`, and `f 2`.

# find
Defined in: `Mathlib.Tactic.Find.tacticFind`


# first
Defined in: `Lean.Parser.Tactic.first`

`first | tac | ...` runs each `tac` until one succeeds, or else fails.

# focus
Defined in: `Lean.Parser.Tactic.focus`

`focus tac` focuses on the main goal, suppressing all other goals, and runs `tac` on it.
Usually `· tac`, which enforces that the goal is closed by `tac`, should be preferred.

# forward
Defined in: `Aesop.Frontend.tacticForward___`


# forward?
Defined in: `Aesop.Frontend.tacticForward?___`


# frac_tac
Defined in: `RatFunc.tacticFrac_tac`

Solve equations for `RatFunc K` by working in `FractionRing K[X]`.

# fun_prop
Defined in: `Mathlib.Meta.FunProp.funPropTacStx`

Tactic to prove function properties

# funext
Defined in: `tacticFunext___`

Apply function extensionality and introduce new hypotheses.
The tactic `funext` will keep applying the `funext` lemma until the goal target is not reducible to
```
  |-  ((fun x => ...) = (fun x => ...))
```
The variant `funext h₁ ... hₙ` applies `funext` `n` times, and uses the given identifiers to name the new hypotheses.
Patterns can be used like in the `intro` tactic. Example, given a goal
```
  |-  ((fun x : Nat × Bool => ...) = (fun x => ...))
```
`funext (a, b)` applies `funext` once and performs pattern matching on the newly introduced pair.

# gcongr
Defined in: `Mathlib.Tactic.GCongr.tacticGcongr__With__`

The `gcongr` tactic applies "generalized congruence" rules, reducing a relational goal
between a LHS and RHS matching the same pattern to relational subgoals between the differing
inputs to the pattern.  For example,
```
example {a b x c d : ℝ} (h1 : a + 1 ≤ b + 1) (h2 : c + 2 ≤ d + 2) :
    x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  gcongr
  · linarith
  · linarith
```
This example has the goal of proving the relation `≤` between a LHS and RHS both of the pattern
```
x ^ 2 * ?_ + ?_
```
(with inputs `a`, `c` on the left and `b`, `d` on the right); after the use of
`gcongr`, we have the simpler goals `a ≤ b` and `c ≤ d`.

A pattern can be provided explicitly; this is useful if a non-maximal match is desired:
```lean
example {a b c d x : ℝ} (h : a + c + 1 ≤ b + d + 1) :
    x ^ 2 * (a + c) + 5 ≤ x ^ 2 * (b + d) + 5 := by
  gcongr x ^ 2 * ?_ + 5
  linarith
```

The "generalized congruence" rules used are the library lemmas which have been tagged with the
attribute `@[gcongr]`.  For example, the first example constructs the proof term
```
add_le_add (mul_le_mul_of_nonneg_left _ (pow_bit0_nonneg x 1)) _
```
using the generalized congruence lemmas `add_le_add` and `mul_le_mul_of_nonneg_left`.

The tactic attempts to discharge side goals to these "generalized congruence" lemmas (such as the
side goal `0 ≤ x ^ 2` in the above application of `mul_le_mul_of_nonneg_left`) using the tactic
`gcongr_discharger`, which wraps `positivity` but can also be extended. Side goals not discharged
in this way are left for the user.

# gcongr?
Defined in: `tacticGcongr?`

Display a widget panel allowing to generate a `gcongr` call with holes specified by selecting
subexpressions in the goal.

# gcongr_discharger
Defined in: `Mathlib.Tactic.GCongr.tacticGcongr_discharger`


# generalize
Defined in: `Lean.Parser.Tactic.generalize`

* `generalize ([h :] e = x),+` replaces all occurrences `e`s in the main goal
  with a fresh hypothesis `x`s. If `h` is given, `h : e = x` is introduced as well.
* `generalize e = x at h₁ ... hₙ` also generalizes occurrences of `e`
  inside `h₁`, ..., `hₙ`.
* `generalize e = x at *` will generalize occurrences of `e` everywhere.

# generalize'
Defined in: `«tacticGeneralize'_:_=_»`

Backwards compatibility shim for `generalize`.

# generalize_proofs
Defined in: `Mathlib.Tactic.generalizeProofsElab`

`generalize_proofs ids* [at locs]?` generalizes proofs in the current goal,
turning them into new local hypotheses.

- `generalize_proofs` generalizes proofs in the target.
- `generalize_proofs at h₁ h₂` generalized proofs in hypotheses `h₁` and `h₂`.
- `generalize_proofs at *` generalizes proofs in the entire local context.
- `generalize_proofs pf₁ pf₂ pf₃` uses names `pf₁`, `pf₂`, and `pf₃` for the generalized proofs.
  These can be `_` to not name proofs.

If a proof is already present in the local context, it will use that rather than create a new
local hypothesis.

When doing `generalize_proofs at h`, if `h` is a let binding, its value is cleared,
and furthermore if `h` duplicates a preceding local hypothesis then it is eliminated.

The tactic is able to abstract proofs from under binders, creating universally quantified
proofs in the local context.
To disable this, use `generalize_proofs (config := { abstract := false })`.
The tactic is also set to recursively abstract proofs from the types of the generalized proofs.
This can be controlled with the `maxDepth` configuration option,
with `generalize_proofs (config := { maxDepth := 0 })` turning this feature off.

For example:
```lean
example : List.nthLe [1, 2] 1 (by simp) = 2 := by
  -- ⊢ [1, 2].nthLe 1 ⋯ = 2
  generalize_proofs h
  -- h : 1 < [1, 2].length
  -- ⊢ [1, 2].nthLe 1 h = 2
```

# get_elem_tactic
Defined in: `tacticGet_elem_tactic`

`get_elem_tactic` is the tactic automatically called by the notation `arr[i]`
to prove any side conditions that arise when constructing the term
(e.g. the index is in bounds of the array). It just delegates to
`get_elem_tactic_trivial` and gives a diagnostic error message otherwise;
users are encouraged to extend `get_elem_tactic_trivial` instead of this tactic.

# get_elem_tactic_trivial
Defined in: `tacticGet_elem_tactic_trivial`

`get_elem_tactic_trivial` is an extensible tactic automatically called
by the notation `arr[i]` to prove any side conditions that arise when
constructing the term (e.g. the index is in bounds of the array).
The default behavior is to just try `trivial` (which handles the case
where `i < arr.size` is in the context) and `simp_arith` and `omega`
(for doing linear arithmetic in the index).

# ghost_calc
Defined in: `WittVector.Tactic.ghostCalc`

`ghost_calc` is a tactic for proving identities between polynomial functions.
Typically, when faced with a goal like
```lean
∀ (x y : 𝕎 R), verschiebung (x * frobenius y) = verschiebung x * y
```
you can
1. call `ghost_calc`
2. do a small amount of manual work -- maybe nothing, maybe `rintro`, etc
3. call `ghost_simp`

and this will close the goal.

`ghost_calc` cannot detect whether you are dealing with unary or binary polynomial functions.
You must give it arguments to determine this.
If you are proving a universally quantified goal like the above,
call `ghost_calc _ _`.
If the variables are introduced already, call `ghost_calc x y`.
In the unary case, use `ghost_calc _` or `ghost_calc x`.

`ghost_calc` is a light wrapper around type class inference.
All it does is apply the appropriate extensionality lemma and try to infer the resulting goals.
This is subtle and Lean's elaborator doesn't like it because of the HO unification involved,
so it is easier (and prettier) to put it in a tactic script.

# ghost_fun_tac
Defined in: `WittVector.«tacticGhost_fun_tac_,_»`

An auxiliary tactic for proving that `ghostFun` respects the ring operations.

# ghost_simp
Defined in: `WittVector.Tactic.ghostSimp`

A macro for a common simplification when rewriting with ghost component equations.

# group
Defined in: `Mathlib.Tactic.Group.group`

Tactic for normalizing expressions in multiplicative groups, without assuming
commutativity, using only the group axioms without any information about which group
is manipulated.

(For additive commutative groups, use the `abel` tactic instead.)

Example:
```lean
example {G : Type} [Group G] (a b c d : G) (h : c = (a*b^2)*((b*b)⁻¹*a⁻¹)*d) : a*c*d⁻¹ = a := by
  group at h -- normalizes `h` which becomes `h : c = d`
  rw [h]     -- the goal is now `a*d*d⁻¹ = a`
  group      -- which then normalized and closed
```

# guard_expr
Defined in: `Lean.Parser.Tactic.guardExpr`

Tactic to check equality of two expressions.
* `guard_expr e = e'` checks that `e` and `e'` are defeq at reducible transparency.
* `guard_expr e =~ e'` checks that `e` and `e'` are defeq at default transparency.
* `guard_expr e =ₛ e'` checks that `e` and `e'` are syntactically equal.
* `guard_expr e =ₐ e'` checks that `e` and `e'` are alpha-equivalent.

Both `e` and `e'` are elaborated then have their metavariables instantiated before the equality
check. Their types are unified (using `isDefEqGuarded`) before synthetic metavariables are
processed, which helps with default instance handling.

# guard_goal_nums
Defined in: `guardGoalNums`

`guard_goal_nums n` succeeds if there are exactly `n` goals and fails otherwise.

# guard_hyp
Defined in: `Lean.Parser.Tactic.guardHyp`

Tactic to check that a named hypothesis has a given type and/or value.

* `guard_hyp h : t` checks the type up to reducible defeq,
* `guard_hyp h :~ t` checks the type up to default defeq,
* `guard_hyp h :ₛ t` checks the type up to syntactic equality,
* `guard_hyp h :ₐ t` checks the type up to alpha equality.
* `guard_hyp h := v` checks value up to reducible defeq,
* `guard_hyp h :=~ v` checks value up to default defeq,
* `guard_hyp h :=ₛ v` checks value up to syntactic equality,
* `guard_hyp h :=ₐ v` checks the value up to alpha equality.

The value `v` is elaborated using the type of `h` as the expected type.

# guard_hyp_nums
Defined in: `guardHypNums`

`guard_hyp_nums n` succeeds if there are exactly `n` hypotheses and fails otherwise.

Note that, depending on what options are set, some hypotheses in the local context might
not be printed in the goal view. This tactic computes the total number of hypotheses,
not the number of visible hypotheses.

# guard_target
Defined in: `Lean.Parser.Tactic.guardTarget`

Tactic to check that the target agrees with a given expression.
* `guard_target = e` checks that the target is defeq at reducible transparency to `e`.
* `guard_target =~ e` checks that the target is defeq at default transparency to `e`.
* `guard_target =ₛ e` checks that the target is syntactically equal to `e`.
* `guard_target =ₐ e` checks that the target is alpha-equivalent to `e`.

The term `e` is elaborated with the type of the goal as the expected type, which is mostly
useful within `conv` mode.

# have
Defined in: `Lean.Parser.Tactic.tacticHave_`

The `have` tactic is for adding hypotheses to the local context of the main goal.
* `have h : t := e` adds the hypothesis `h : t` if `e` is a term of type `t`.
* `have h := e` uses the type of `e` for `t`.
* `have : t := e` and `have := e` use `this` for the name of the hypothesis.
* `have pat := e` for a pattern `pat` is equivalent to `match e with | pat => _`,
  where `_` stands for the tactics that follow this one.
  It is convenient for types that have only one applicable constructor.
  For example, given `h : p ∧ q ∧ r`, `have ⟨h₁, h₂, h₃⟩ := h` produces the
  hypotheses `h₁ : p`, `h₂ : q`, and `h₃ : r`.

# have
Defined in: `Mathlib.Tactic.tacticHave_`


# have!?
Defined in: `Mathlib.Tactic.Propose.«tacticHave!?:_Using__»`

* `have? using a, b, c` tries to find a lemma
which makes use of each of the local hypotheses `a, b, c`,
and reports any results via trace messages.
* `have? : h using a, b, c` only returns lemmas whose type matches `h` (which may contain `_`).
* `have?! using a, b, c` will also call `have` to add results to the local goal state.

Note that `have?` (unlike `apply?`) does not inspect the goal at all,
only the types of the lemmas in the `using` clause.

`have?` should not be left in proofs; it is a search tool, like `apply?`.

Suggestions are printed as `have := f a b c`.

# have'
Defined in: `Lean.Parser.Tactic.tacticHave'_`

Similar to `have`, but using `refine'`

# have'
Defined in: `Lean.Parser.Tactic.«tacticHave'_:=_»`

Similar to `have`, but using `refine'`

# have?
Defined in: `Mathlib.Tactic.Propose.propose'`

* `have? using a, b, c` tries to find a lemma
which makes use of each of the local hypotheses `a, b, c`,
and reports any results via trace messages.
* `have? : h using a, b, c` only returns lemmas whose type matches `h` (which may contain `_`).
* `have?! using a, b, c` will also call `have` to add results to the local goal state.

Note that `have?` (unlike `apply?`) does not inspect the goal at all,
only the types of the lemmas in the `using` clause.

`have?` should not be left in proofs; it is a search tool, like `apply?`.

Suggestions are printed as `have := f a b c`.

# have?!
Defined in: `Mathlib.Tactic.Propose.«tacticHave?!:_Using__»`

* `have? using a, b, c` tries to find a lemma
which makes use of each of the local hypotheses `a, b, c`,
and reports any results via trace messages.
* `have? : h using a, b, c` only returns lemmas whose type matches `h` (which may contain `_`).
* `have?! using a, b, c` will also call `have` to add results to the local goal state.

Note that `have?` (unlike `apply?`) does not inspect the goal at all,
only the types of the lemmas in the `using` clause.

`have?` should not be left in proofs; it is a search tool, like `apply?`.

Suggestions are printed as `have := f a b c`.

# haveI
Defined in: `Lean.Parser.Tactic.tacticHaveI_`

`haveI` behaves like `have`, but inlines the value instead of producing a `let_fun` term.

# hint
Defined in: `Mathlib.Tactic.Hint.hintStx`

The `hint` tactic tries every tactic registered using `register_hint tac`,
and reports any that succeed.

# html!
Defined in: `ProofWidgets.HtmlCommand.htmlTac`

The `html!` tactic is deprecated and does nothing.
If you have a use for it,
please open an issue on https://github.com/leanprover-community/ProofWidgets4.

# induction
Defined in: `Lean.Parser.Tactic.induction`

Assuming `x` is a variable in the local context with an inductive type,
`induction x` applies induction on `x` to the main goal,
producing one goal for each constructor of the inductive type,
in which the target is replaced by a general instance of that constructor
and an inductive hypothesis is added for each recursive argument to the constructor.
If the type of an element in the local context depends on `x`,
that element is reverted and reintroduced afterward,
so that the inductive hypothesis incorporates that hypothesis as well.

For example, given `n : Nat` and a goal with a hypothesis `h : P n` and target `Q n`,
`induction n` produces one goal with hypothesis `h : P 0` and target `Q 0`,
and one goal with hypotheses `h : P (Nat.succ a)` and `ih₁ : P a → Q a` and target `Q (Nat.succ a)`.
Here the names `a` and `ih₁` are chosen automatically and are not accessible.
You can use `with` to provide the variables names for each constructor.
- `induction e`, where `e` is an expression instead of a variable,
  generalizes `e` in the goal, and then performs induction on the resulting variable.
- `induction e using r` allows the user to specify the principle of induction that should be used.
  Here `r` should be a term whose result type must be of the form `C t`,
  where `C` is a bound variable and `t` is a (possibly empty) sequence of bound variables
- `induction e generalizing z₁ ... zₙ`, where `z₁ ... zₙ` are variables in the local context,
  generalizes over `z₁ ... zₙ` before applying the induction but then introduces them in each goal.
  In other words, the net effect is that each inductive hypothesis is generalized.
- Given `x : Nat`, `induction x with | zero => tac₁ | succ x' ih => tac₂`
  uses tactic `tac₁` for the `zero` case, and `tac₂` for the `succ` case.

# induction'
Defined in: `Mathlib.Tactic.induction'`

The `induction'` tactic is similar to the `induction` tactic in Lean 4 core,
but with slightly different syntax (such as, no requirement to name the constructors).

```
open Nat

example (n : ℕ) : 0 < factorial n := by
  induction' n with n ih
  · rw [factorial_zero]
    simp
  · rw [factorial_succ]
    apply mul_pos (succ_pos n) ih

example (n : ℕ) : 0 < factorial n := by
  induction n
  case zero =>
    rw [factorial_zero]
    simp
  case succ n ih =>
    rw [factorial_succ]
    apply mul_pos (succ_pos n) ih
```

# infer_instance
Defined in: `Lean.Parser.Tactic.tacticInfer_instance`

`infer_instance` is an abbreviation for `exact inferInstance`.
It synthesizes a value of any target type by typeclass inference.

# infer_param
Defined in: `Mathlib.Tactic.inferOptParam`

Close a goal of the form `optParam α a` or `autoParam α stx` by using `a`.

# inhabit
Defined in: `Lean.Elab.Tactic.inhabit`

`inhabit α` tries to derive a `Nonempty α` instance and
then uses it to make an `Inhabited α` instance.
If the target is a `Prop`, this is done constructively. Otherwise, it uses `Classical.choice`.

# init_ring
Defined in: `WittVector.initRing`

`init_ring` is an auxiliary tactic that discharges goals factoring `init` over ring operations.

# injection
Defined in: `Lean.Parser.Tactic.injection`

The `injection` tactic is based on the fact that constructors of inductive data
types are injections.
That means that if `c` is a constructor of an inductive datatype, and if `(c t₁)`
and `(c t₂)` are two terms that are equal then  `t₁` and `t₂` are equal too.
If `q` is a proof of a statement of conclusion `t₁ = t₂`, then injection applies
injectivity to derive the equality of all arguments of `t₁` and `t₂` placed in
the same positions. For example, from `(a::b) = (c::d)` we derive `a=c` and `b=d`.
To use this tactic `t₁` and `t₂` should be constructor applications of the same constructor.
Given `h : a::b = c::d`, the tactic `injection h` adds two new hypothesis with types
`a = c` and `b = d` to the main goal.
The tactic `injection h with h₁ h₂` uses the names `h₁` and `h₂` to name the new hypotheses.

# injections
Defined in: `Lean.Parser.Tactic.injections`

`injections` applies `injection` to all hypotheses recursively
(since `injection` can produce new hypotheses). Useful for destructing nested
constructor equalities like `(a::b::c) = (d::e::f)`.

# interval_cases
Defined in: `Mathlib.Tactic.intervalCases`

`interval_cases n` searches for upper and lower bounds on a variable `n`,
and if bounds are found,
splits into separate cases for each possible value of `n`.

As an example, in
```
example (n : ℕ) (w₁ : n ≥ 3) (w₂ : n < 5) : n = 3 ∨ n = 4 := by
  interval_cases n
  all_goals simp
```
after `interval_cases n`, the goals are `3 = 3 ∨ 3 = 4` and `4 = 3 ∨ 4 = 4`.

You can also explicitly specify a lower and upper bound to use,
as `interval_cases using hl, hu`.
The hypotheses should be in the form `hl : a ≤ n` and `hu : n < b`,
in which case `interval_cases` calls `fin_cases` on the resulting fact `n ∈ Set.Ico a b`.

You can specify a name `h` for the new hypothesis,
as `interval_cases h : n` or `interval_cases h : n using hl, hu`.

# intro
Defined in: `Batteries.Tactic.introDot`

The syntax `intro.` is deprecated in favor of `nofun`.

# intro
Defined in: `Lean.Parser.Tactic.intro`

Introduces one or more hypotheses, optionally naming and/or pattern-matching them.
For each hypothesis to be introduced, the remaining main goal's target type must
be a `let` or function type.

* `intro` by itself introduces one anonymous hypothesis, which can be accessed
  by e.g. `assumption`.
* `intro x y` introduces two hypotheses and names them. Individual hypotheses
  can be anonymized via `_`, or matched against a pattern:
  ```lean
  -- ... ⊢ α × β → ...
  intro (a, b)
  -- ..., a : α, b : β ⊢ ...
  ```
* Alternatively, `intro` can be combined with pattern matching much like `fun`:
  ```lean
  intro
  | n + 1, 0 => tac
  | ...
  ```

# intro
Defined in: `Lean.Parser.Tactic.introMatch`

The tactic
```
intro
| pat1 => tac1
| pat2 => tac2
```
is the same as:
```lean
intro x
match x with
| pat1 => tac1
| pat2 => tac2
```
That is, `intro` can be followed by match arms and it introduces the values while
doing a pattern match. This is equivalent to `fun` with match arms in term mode.

# intros
Defined in: `Lean.Parser.Tactic.intros`

Introduces zero or more hypotheses, optionally naming them.

- `intros` is equivalent to repeatedly applying `intro`
  until the goal is not an obvious candidate for `intro`, which is to say
  that so long as the goal is a `let` or a pi type (e.g. an implication, function, or universal quantifier),
  the `intros` tactic will introduce an anonymous hypothesis.
  This tactic does not unfold definitions.

- `intros x y ...` is equivalent to `intro x y ...`,
  introducing hypotheses for each supplied argument and unfolding definitions as necessary.
  Each argument can be either an identifier or a `_`.
  An identifier indicates a name to use for the corresponding introduced hypothesis,
  and a `_` indicates that the hypotheses should be introduced anonymously.

## Examples

Basic properties:
```lean
def AllEven (f : Nat → Nat) := ∀ n, f n % 2 = 0

-- Introduces the two obvious hypotheses automatically
example : ∀ (f : Nat → Nat), AllEven f → AllEven (fun k => f (k + 1)) := by
  intros
  /- Tactic state
     f✝ : Nat → Nat
     a✝ : AllEven f✝
     ⊢ AllEven fun k => f✝ (k + 1) -/
  sorry

-- Introduces exactly two hypotheses, naming only the first
example : ∀ (f : Nat → Nat), AllEven f → AllEven (fun k => f (k + 1)) := by
  intros g _
  /- Tactic state
     g : Nat → Nat
     a✝ : AllEven g
     ⊢ AllEven fun k => g (k + 1) -/
  sorry

-- Introduces exactly three hypotheses, which requires unfolding `AllEven`
example : ∀ (f : Nat → Nat), AllEven f → AllEven (fun k => f (k + 1)) := by
  intros f h n
  /- Tactic state
     f : Nat → Nat
     h : AllEven f
     n : Nat
     ⊢ (fun k => f (k + 1)) n % 2 = 0 -/
  apply h
```

Implications:
```lean
example (p q : Prop) : p → q → p := by
  intros
  /- Tactic state
     a✝¹ : p
     a✝ : q
     ⊢ p      -/
  assumption
```

Let bindings:
```lean
example : let n := 1; let k := 2; n + k = 3 := by
  intros
  /- n✝ : Nat := 1
     k✝ : Nat := 2
     ⊢ n✝ + k✝ = 3 -/
  rfl
```

# introv
Defined in: `Mathlib.Tactic.introv`

The tactic `introv` allows the user to automatically introduce the variables of a theorem and
explicitly name the non-dependent hypotheses.
Any dependent hypotheses are assigned their default names.

Examples:
```lean
example : ∀ a b : Nat, a = b → b = a := by
  introv h,
  exact h.symm
```
The state after `introv h` is
```
a b : ℕ,
h : a = b
⊢ b = a
```

```
example : ∀ a b : Nat, a = b → ∀ c, b = c → a = c := by
  introv h₁ h₂,
  exact h₁.trans h₂
```
The state after `introv h₁ h₂` is
```
a b : ℕ,
h₁ : a = b,
c : ℕ,
h₂ : b = c
⊢ a = c
```

# isBoundedDefault
Defined in: `Filter.tacticIsBoundedDefault`

Filters are automatically bounded or cobounded in complete lattices. To use the same statements
in complete and conditionally complete lattices but let automation fill automatically the
boundedness proofs in complete lattices, we use the tactic `isBoundedDefault` in the statements,
in the form `(hf : f.IsBounded (≥) := by isBoundedDefault)`.

# itauto
Defined in: `Mathlib.Tactic.ITauto.itauto`

A decision procedure for intuitionistic propositional logic. Unlike `finish` and `tauto!` this
tactic never uses the law of excluded middle (without the `!` option), and the proof search is
tailored for this use case. (`itauto!` will work as a classical SAT solver, but the algorithm is
not very good in this situation.)

```lean
example (p : Prop) : ¬ (p ↔ ¬ p) := by itauto
```

`itauto [a, b]` will additionally attempt case analysis on `a` and `b` assuming that it can derive
`Decidable a` and `Decidable b`. `itauto *` will case on all decidable propositions that it can
find among the atomic propositions, and `itauto! *` will case on all propositional atoms.
*Warning:* This can blow up the proof search, so it should be used sparingly.

# itauto!
Defined in: `Mathlib.Tactic.ITauto.itauto!`

A decision procedure for intuitionistic propositional logic. Unlike `finish` and `tauto!` this
tactic never uses the law of excluded middle (without the `!` option), and the proof search is
tailored for this use case. (`itauto!` will work as a classical SAT solver, but the algorithm is
not very good in this situation.)

```lean
example (p : Prop) : ¬ (p ↔ ¬ p) := by itauto
```

`itauto [a, b]` will additionally attempt case analysis on `a` and `b` assuming that it can derive
`Decidable a` and `Decidable b`. `itauto *` will case on all decidable propositions that it can
find among the atomic propositions, and `itauto! *` will case on all propositional atoms.
*Warning:* This can blow up the proof search, so it should be used sparingly.

# iterate
Defined in: `Lean.Parser.Tactic.tacticIterate____`

`iterate n tac` runs `tac` exactly `n` times.
`iterate tac` runs `tac` repeatedly until failure.

`iterate`'s argument is a tactic sequence,
so multiple tactics can be run using `iterate n (tac₁; tac₂; ⋯)` or
```lean
iterate n
  tac₁
  tac₂
  ⋯
```

# left
Defined in: `Lean.Parser.Tactic.left`

Applies the first constructor when
the goal is an inductive type with exactly two constructors, or fails otherwise.
```lean
example : True ∨ False := by
  left
  trivial
```

# let
Defined in: `Lean.Parser.Tactic.letrec`

`let rec f : t := e` adds a recursive definition `f` to the current goal.
The syntax is the same as term-mode `let rec`.

# let
Defined in: `Mathlib.Tactic.tacticLet_`


# let
Defined in: `Lean.Parser.Tactic.tacticLet_`

The `let` tactic is for adding definitions to the local context of the main goal.
* `let x : t := e` adds the definition `x : t := e` if `e` is a term of type `t`.
* `let x := e` uses the type of `e` for `t`.
* `let : t := e` and `let := e` use `this` for the name of the hypothesis.
* `let pat := e` for a pattern `pat` is equivalent to `match e with | pat => _`,
  where `_` stands for the tactics that follow this one.
  It is convenient for types that let only one applicable constructor.
  For example, given `p : α × β × γ`, `let ⟨x, y, z⟩ := p` produces the
  local variables `x : α`, `y : β`, and `z : γ`.

# let'
Defined in: `Lean.Parser.Tactic.tacticLet'_`

Similar to `let`, but using `refine'`

# letI
Defined in: `Lean.Parser.Tactic.tacticLetI_`

`letI` behaves like `let`, but inlines the value instead of producing a `let_fun` term.

# lift
Defined in: `Mathlib.Tactic.lift`

Lift an expression to another type.
* Usage: `'lift' expr 'to' expr ('using' expr)? ('with' id (id id?)?)?`.
* If `n : ℤ` and `hn : n ≥ 0` then the tactic `lift n to ℕ using hn` creates a new
  constant of type `ℕ`, also named `n` and replaces all occurrences of the old variable `(n : ℤ)`
  with `↑n` (where `n` in the new variable). It will remove `n` and `hn` from the context.
  + So for example the tactic `lift n to ℕ using hn` transforms the goal
    `n : ℤ, hn : n ≥ 0, h : P n ⊢ n = 3` to `n : ℕ, h : P ↑n ⊢ ↑n = 3`
    (here `P` is some term of type `ℤ → Prop`).
* The argument `using hn` is optional, the tactic `lift n to ℕ` does the same, but also creates a
  new subgoal that `n ≥ 0` (where `n` is the old variable).
  This subgoal will be placed at the top of the goal list.
  + So for example the tactic `lift n to ℕ` transforms the goal
    `n : ℤ, h : P n ⊢ n = 3` to two goals
    `n : ℤ, h : P n ⊢ n ≥ 0` and `n : ℕ, h : P ↑n ⊢ ↑n = 3`.
* You can also use `lift n to ℕ using e` where `e` is any expression of type `n ≥ 0`.
* Use `lift n to ℕ with k` to specify the name of the new variable.
* Use `lift n to ℕ with k hk` to also specify the name of the equality `↑k = n`. In this case, `n`
  will remain in the context. You can use `rfl` for the name of `hk` to substitute `n` away
  (i.e. the default behavior).
* You can also use `lift e to ℕ with k hk` where `e` is any expression of type `ℤ`.
  In this case, the `hk` will always stay in the context, but it will be used to rewrite `e` in
  all hypotheses and the target.
  + So for example the tactic `lift n + 3 to ℕ using hn with k hk` transforms the goal
    `n : ℤ, hn : n + 3 ≥ 0, h : P (n + 3) ⊢ n + 3 = 2 * n` to the goal
    `n : ℤ, k : ℕ, hk : ↑k = n + 3, h : P ↑k ⊢ ↑k = 2 * n`.
* The tactic `lift n to ℕ using h` will remove `h` from the context. If you want to keep it,
  specify it again as the third argument to `with`, like this: `lift n to ℕ using h with n rfl h`.
* More generally, this can lift an expression from `α` to `β` assuming that there is an instance
  of `CanLift α β`. In this case the proof obligation is specified by `CanLift.prf`.
* Given an instance `CanLift β γ`, it can also lift `α → β` to `α → γ`; more generally, given
  `β : Π a : α, Type*`, `γ : Π a : α, Type*`, and `[Π a : α, CanLift (β a) (γ a)]`, it
  automatically generates an instance `CanLift (Π a, β a) (Π a, γ a)`.

`lift` is in some sense dual to the `zify` tactic. `lift (z : ℤ) to ℕ` will change the type of an
integer `z` (in the supertype) to `ℕ` (the subtype), given a proof that `z ≥ 0`;
propositions concerning `z` will still be over `ℤ`. `zify` changes propositions about `ℕ` (the
subtype) to propositions about `ℤ` (the supertype), without changing the type of any variable.

# lift_lets
Defined in: `Mathlib.Tactic.lift_lets`

Lift all the `let` bindings in the type of an expression as far out as possible.

When applied to the main goal, this gives one the ability to `intro` embedded `let` expressions.
For example,
```lean
example : (let x := 1; x) = 1 := by
  lift_lets
  -- ⊢ let x := 1; x = 1
  intro x
  sorry
```

During the lifting process, let bindings are merged if they have the same type and value.

# liftable_prefixes
Defined in: `Mathlib.Tactic.Coherence.liftable_prefixes`

Internal tactic used in `coherence`.

Rewrites an equation `f = g` as `f₀ ≫ f₁ = g₀ ≫ g₁`,
where `f₀` and `g₀` are maximal prefixes of `f` and `g` (possibly after reassociating)
which are "liftable" (i.e. expressible as compositions of unitors and associators).

# linarith
Defined in: `linarith`

`linarith` attempts to find a contradiction between hypotheses that are linear (in)equalities.
Equivalently, it can prove a linear inequality by assuming its negation and proving `False`.

In theory, `linarith` should prove any goal that is true in the theory of linear arithmetic over
the rationals. While there is some special handling for non-dense orders like `Nat` and `Int`,
this tactic is not complete for these theories and will not prove every true goal. It will solve
goals over arbitrary types that instantiate `LinearOrderedCommRing`.

An example:
```lean
example (x y z : ℚ) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0) : False := by
  linarith
```

`linarith` will use all appropriate hypotheses and the negation of the goal, if applicable.
Disequality hypotheses require case splitting and are not normally considered
(see the `splitNe` option below).

`linarith [t1, t2, t3]` will additionally use proof terms `t1, t2, t3`.

`linarith only [h1, h2, h3, t1, t2, t3]` will use only the goal (if relevant), local hypotheses
`h1`, `h2`, `h3`, and proofs `t1`, `t2`, `t3`. It will ignore the rest of the local context.

`linarith!` will use a stronger reducibility setting to try to identify atoms. For example,
```lean
example (x : ℚ) : id x ≥ x := by
  linarith
```
will fail, because `linarith` will not identify `x` and `id x`. `linarith!` will.
This can sometimes be expensive.

`linarith (config := { .. })` takes a config object with five
optional arguments:
* `discharger` specifies a tactic to be used for reducing an algebraic equation in the
  proof stage. The default is `ring`. Other options include `simp` for basic
  problems.
* `transparency` controls how hard `linarith` will try to match atoms to each other. By default
  it will only unfold `reducible` definitions.
* If `splitHypotheses` is true, `linarith` will split conjunctions in the context into separate
  hypotheses.
* If `splitNe` is `true`, `linarith` will case split on disequality hypotheses.
  For a given `x ≠ y` hypothesis, `linarith` is run with both `x < y` and `x > y`,
  and so this runs linarith exponentially many times with respect to the number of
  disequality hypotheses. (`false` by default.)
* If `exfalso` is `false`, `linarith` will fail when the goal is neither an inequality nor `False`.
  (`true` by default.)
* `restrict_type` (not yet implemented in mathlib4)
  will only use hypotheses that are inequalities over `tp`. This is useful
  if you have e.g. both integer and rational valued inequalities in the local context, which can
  sometimes confuse the tactic.

A variant, `nlinarith`, does some basic preprocessing to handle some nonlinear goals.

The option `set_option trace.linarith true` will trace certain intermediate stages of the `linarith`
routine.

# linarith!
Defined in: `tacticLinarith!_`

`linarith` attempts to find a contradiction between hypotheses that are linear (in)equalities.
Equivalently, it can prove a linear inequality by assuming its negation and proving `False`.

In theory, `linarith` should prove any goal that is true in the theory of linear arithmetic over
the rationals. While there is some special handling for non-dense orders like `Nat` and `Int`,
this tactic is not complete for these theories and will not prove every true goal. It will solve
goals over arbitrary types that instantiate `LinearOrderedCommRing`.

An example:
```lean
example (x y z : ℚ) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0) : False := by
  linarith
```

`linarith` will use all appropriate hypotheses and the negation of the goal, if applicable.
Disequality hypotheses require case splitting and are not normally considered
(see the `splitNe` option below).

`linarith [t1, t2, t3]` will additionally use proof terms `t1, t2, t3`.

`linarith only [h1, h2, h3, t1, t2, t3]` will use only the goal (if relevant), local hypotheses
`h1`, `h2`, `h3`, and proofs `t1`, `t2`, `t3`. It will ignore the rest of the local context.

`linarith!` will use a stronger reducibility setting to try to identify atoms. For example,
```lean
example (x : ℚ) : id x ≥ x := by
  linarith
```
will fail, because `linarith` will not identify `x` and `id x`. `linarith!` will.
This can sometimes be expensive.

`linarith (config := { .. })` takes a config object with five
optional arguments:
* `discharger` specifies a tactic to be used for reducing an algebraic equation in the
  proof stage. The default is `ring`. Other options include `simp` for basic
  problems.
* `transparency` controls how hard `linarith` will try to match atoms to each other. By default
  it will only unfold `reducible` definitions.
* If `splitHypotheses` is true, `linarith` will split conjunctions in the context into separate
  hypotheses.
* If `splitNe` is `true`, `linarith` will case split on disequality hypotheses.
  For a given `x ≠ y` hypothesis, `linarith` is run with both `x < y` and `x > y`,
  and so this runs linarith exponentially many times with respect to the number of
  disequality hypotheses. (`false` by default.)
* If `exfalso` is `false`, `linarith` will fail when the goal is neither an inequality nor `False`.
  (`true` by default.)
* `restrict_type` (not yet implemented in mathlib4)
  will only use hypotheses that are inequalities over `tp`. This is useful
  if you have e.g. both integer and rational valued inequalities in the local context, which can
  sometimes confuse the tactic.

A variant, `nlinarith`, does some basic preprocessing to handle some nonlinear goals.

The option `set_option trace.linarith true` will trace certain intermediate stages of the `linarith`
routine.

# linear_combination
Defined in: `Mathlib.Tactic.LinearCombination.linearCombination`

`linear_combination` attempts to simplify the target by creating a linear combination
  of a list of equalities and subtracting it from the target.
  The tactic will create a linear
  combination by adding the equalities together from left to right, so the order
  of the input hypotheses does matter.  If the `norm` field of the
  tactic is set to `skip`, then the tactic will simply set the user up to
  prove their target using the linear combination instead of normalizing the subtraction.

Note: The left and right sides of all the equalities should have the same type `α`, and the
coefficients should also have type `α`.  For full functionality `α` should be a commutative ring --
strictly speaking, a commutative semiring with "cancellative" addition (in the semiring case,
negation and subtraction will be handled "formally" as if operating in the enveloping ring). If a
nonstandard normalization is used (for example `abel` or `skip`), the tactic will work over types
`α` with less algebraic structure: the minimum is instances of `[Add α] [IsRightCancelAdd α]`
together with instances of whatever operations are used in the tactic call.

* The input `e` in `linear_combination e` is a linear combination of proofs of equalities,
  given as a sum/difference of coefficients multiplied by expressions.
  The coefficients may be arbitrary expressions.
  The expressions can be arbitrary proof terms proving equalities.
  Most commonly they are hypothesis names `h1, h2, ...`.
* `linear_combination (norm := tac) e` runs the "normalization tactic" `tac`
  on the subgoal(s) after constructing the linear combination.
  * The default normalization tactic is `ring1`, which closes the goal or fails.
  * To get a subgoal in the case that it is not immediately provable, use
    `ring_nf` as the normalization tactic.
  * To avoid normalization entirely, use `skip` as the normalization tactic.
* `linear_combination (exp := n) e` will take the goal to the `n`th power before subtracting the
  combination `e`. In other words, if the goal is `t1 = t2`, `linear_combination (exp := n) e`
  will change the goal to `(t1 - t2)^n = 0` before proceeding as above.

Example Usage:
```lean
example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination 1*h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination (norm := ring_nf) -2*h2
  /- Goal: x * y + x * 2 - 1 = 0 -/

example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
    -3*x - 3*y - 4*z = 2 := by
  linear_combination ha - hb - 2*hc

example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
    x*x*y + y*x*y + 6*x = 3*x*y + 14 := by
  linear_combination x*y*h1 + 2*h2

example (x y : ℤ) (h1 : x = -3) (h2 : y = 10) : 2*x = -6 := by
  linear_combination (norm := skip) 2*h1
  simp

axiom qc : ℚ
axiom hqc : qc = 2*qc

example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc := by
  linear_combination 3 * h a b + hqc
```

# linear_combination'
Defined in: `Mathlib.Tactic.LinearCombination'.linearCombination'`

`linear_combination'` attempts to simplify the target by creating a linear combination
  of a list of equalities and subtracting it from the target.
  The tactic will create a linear
  combination by adding the equalities together from left to right, so the order
  of the input hypotheses does matter.  If the `norm` field of the
  tactic is set to `skip`, then the tactic will simply set the user up to
  prove their target using the linear combination instead of normalizing the subtraction.

Note: There is also a similar tactic `linear_combination` (no prime); this version is
provided for backward compatibility.  Compared to this tactic, `linear_combination`:
* drops the `←` syntax for reversing an equation, instead offering this operation using the `-`
  syntax
* does not support multiplication of two hypotheses (`h1 * h2`), division by a hypothesis (`3 / h`),
  or inversion of a hypothesis (`h⁻¹`)
* produces noisy output when the user adds or subtracts a constant to a hypothesis (`h + 3`)

Note: The left and right sides of all the equalities should have the same
  type, and the coefficients should also have this type.  There must be
  instances of `Mul` and `AddGroup` for this type.

* The input `e` in `linear_combination' e` is a linear combination of proofs of equalities,
  given as a sum/difference of coefficients multiplied by expressions.
  The coefficients may be arbitrary expressions.
  The expressions can be arbitrary proof terms proving equalities.
  Most commonly they are hypothesis names `h1, h2, ...`.
* `linear_combination' (norm := tac) e` runs the "normalization tactic" `tac`
  on the subgoal(s) after constructing the linear combination.
  * The default normalization tactic is `ring1`, which closes the goal or fails.
  * To get a subgoal in the case that it is not immediately provable, use
    `ring_nf` as the normalization tactic.
  * To avoid normalization entirely, use `skip` as the normalization tactic.
* `linear_combination' (exp := n) e` will take the goal to the `n`th power before subtracting the
  combination `e`. In other words, if the goal is `t1 = t2`, `linear_combination' (exp := n) e`
  will change the goal to `(t1 - t2)^n = 0` before proceeding as above.
  This feature is not supported for `linear_combination2`.
* `linear_combination2 e` is the same as `linear_combination' e` but it produces two
  subgoals instead of one: rather than proving that `(a - b) - (a' - b') = 0` where
  `a' = b'` is the linear combination from `e` and `a = b` is the goal,
  it instead attempts to prove `a = a'` and `b = b'`.
  Because it does not use subtraction, this form is applicable also to semirings.
  * Note that a goal which is provable by `linear_combination' e` may not be provable
    by `linear_combination2 e`; in general you may need to add a coefficient to `e`
    to make both sides match, as in `linear_combination2 e + c`.
  * You can also reverse equalities using `← h`, so for example if `h₁ : a = b`
    then `2 * (← h)` is a proof of `2 * b = 2 * a`.

Example Usage:
```lean
example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination' 1*h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination' h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination' (norm := ring_nf) -2*h2
  /- Goal: x * y + x * 2 - 1 = 0 -/

example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
    -3*x - 3*y - 4*z = 2 := by
  linear_combination' ha - hb - 2*hc

example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
    x*x*y + y*x*y + 6*x = 3*x*y + 14 := by
  linear_combination' x*y*h1 + 2*h2

example (x y : ℤ) (h1 : x = -3) (h2 : y = 10) : 2*x = -6 := by
  linear_combination' (norm := skip) 2*h1
  simp

axiom qc : ℚ
axiom hqc : qc = 2*qc

example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc := by
  linear_combination' 3 * h a b + hqc
```

# linear_combination2
Defined in: `Mathlib.Tactic.LinearCombination'.tacticLinear_combination2____`

`linear_combination'` attempts to simplify the target by creating a linear combination
  of a list of equalities and subtracting it from the target.
  The tactic will create a linear
  combination by adding the equalities together from left to right, so the order
  of the input hypotheses does matter.  If the `norm` field of the
  tactic is set to `skip`, then the tactic will simply set the user up to
  prove their target using the linear combination instead of normalizing the subtraction.

Note: There is also a similar tactic `linear_combination` (no prime); this version is
provided for backward compatibility.  Compared to this tactic, `linear_combination`:
* drops the `←` syntax for reversing an equation, instead offering this operation using the `-`
  syntax
* does not support multiplication of two hypotheses (`h1 * h2`), division by a hypothesis (`3 / h`),
  or inversion of a hypothesis (`h⁻¹`)
* produces noisy output when the user adds or subtracts a constant to a hypothesis (`h + 3`)

Note: The left and right sides of all the equalities should have the same
  type, and the coefficients should also have this type.  There must be
  instances of `Mul` and `AddGroup` for this type.

* The input `e` in `linear_combination' e` is a linear combination of proofs of equalities,
  given as a sum/difference of coefficients multiplied by expressions.
  The coefficients may be arbitrary expressions.
  The expressions can be arbitrary proof terms proving equalities.
  Most commonly they are hypothesis names `h1, h2, ...`.
* `linear_combination' (norm := tac) e` runs the "normalization tactic" `tac`
  on the subgoal(s) after constructing the linear combination.
  * The default normalization tactic is `ring1`, which closes the goal or fails.
  * To get a subgoal in the case that it is not immediately provable, use
    `ring_nf` as the normalization tactic.
  * To avoid normalization entirely, use `skip` as the normalization tactic.
* `linear_combination' (exp := n) e` will take the goal to the `n`th power before subtracting the
  combination `e`. In other words, if the goal is `t1 = t2`, `linear_combination' (exp := n) e`
  will change the goal to `(t1 - t2)^n = 0` before proceeding as above.
  This feature is not supported for `linear_combination2`.
* `linear_combination2 e` is the same as `linear_combination' e` but it produces two
  subgoals instead of one: rather than proving that `(a - b) - (a' - b') = 0` where
  `a' = b'` is the linear combination from `e` and `a = b` is the goal,
  it instead attempts to prove `a = a'` and `b = b'`.
  Because it does not use subtraction, this form is applicable also to semirings.
  * Note that a goal which is provable by `linear_combination' e` may not be provable
    by `linear_combination2 e`; in general you may need to add a coefficient to `e`
    to make both sides match, as in `linear_combination2 e + c`.
  * You can also reverse equalities using `← h`, so for example if `h₁ : a = b`
    then `2 * (← h)` is a proof of `2 * b = 2 * a`.

Example Usage:
```lean
example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination' 1*h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination' h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination' (norm := ring_nf) -2*h2
  /- Goal: x * y + x * 2 - 1 = 0 -/

example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
    -3*x - 3*y - 4*z = 2 := by
  linear_combination' ha - hb - 2*hc

example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
    x*x*y + y*x*y + 6*x = 3*x*y + 14 := by
  linear_combination' x*y*h1 + 2*h2

example (x y : ℤ) (h1 : x = -3) (h2 : y = 10) : 2*x = -6 := by
  linear_combination' (norm := skip) 2*h1
  simp

axiom qc : ℚ
axiom hqc : qc = 2*qc

example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc := by
  linear_combination' 3 * h a b + hqc
```

# map_fun_tac
Defined in: `WittVector.mapFun.tacticMap_fun_tac`

Auxiliary tactic for showing that `mapFun` respects the ring operations.

# map_tacs
Defined in: `Batteries.Tactic.«tacticMap_tacs[_;]»`

Assuming there are `n` goals, `map_tacs [t1; t2; ...; tn]` applies each `ti` to the respective
goal and leaves the resulting subgoals.

# match
Defined in: `Lean.Parser.Tactic.match`

`match` performs case analysis on one or more expressions.
See [Induction and Recursion][tpil4].
The syntax for the `match` tactic is the same as term-mode `match`, except that
the match arms are tactics instead of expressions.
```lean
example (n : Nat) : n = n := by
  match n with
  | 0 => rfl
  | i+1 => simp
```

[tpil4]: https://lean-lang.org/theorem_proving_in_lean4/induction_and_recursion.html

# match
Defined in: `Batteries.Tactic.«tacticMatch_,,With.»`

The syntax `match ⋯ with.` has been deprecated in favor of `nomatch ⋯`.

Both now support multiple discriminants.

# match_target
Defined in: `Mathlib.Tactic.tacticMatch_target_`


# measurability
Defined in: `tacticMeasurability_`

The tactic `measurability` solves goals of the form `Measurable f`, `AEMeasurable f`,
`StronglyMeasurable f`, `AEStronglyMeasurable f μ`, or `MeasurableSet s` by applying lemmas tagged
with the `measurability` user attribute.

# measurability!
Defined in: `measurability!`


# measurability!?
Defined in: `measurability!?`


# measurability?
Defined in: `tacticMeasurability?_`

The tactic `measurability?` solves goals of the form `Measurable f`, `AEMeasurable f`,
`StronglyMeasurable f`, `AEStronglyMeasurable f μ`, or `MeasurableSet s` by applying lemmas tagged
with the `measurability` user attribute, and suggests a faster proof script that can be substituted
for the tactic call in case of success.

# mem_tac
Defined in: `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.tacticMem_tac`


# mem_tac_aux
Defined in: `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.tacticMem_tac_aux`


# mfld_set_tac
Defined in: `Tactic.MfldSetTac.mfldSetTac`

A very basic tactic to show that sets showing up in manifolds coincide or are included
in one another.

# mod_cases
Defined in: `Mathlib.Tactic.ModCases.«tacticMod_cases_:_%_»`

* The tactic `mod_cases h : e % 3` will perform a case disjunction on `e`.
  If `e : ℤ`, then it will yield subgoals containing the assumptions
  `h : e ≡ 0 [ZMOD 3]`, `h : e ≡ 1 [ZMOD 3]`, `h : e ≡ 2 [ZMOD 3]`
  respectively. If `e : ℕ` instead, then it works similarly, except with
  `[MOD 3]` instead of `[ZMOD 3]`.
* In general, `mod_cases h : e % n` works
  when `n` is a positive numeral and `e` is an expression of type `ℕ` or `ℤ`.
* If `h` is omitted as in `mod_cases e % n`, it will be default-named `H`.

# monicity
Defined in: `Mathlib.Tactic.ComputeDegree.monicityMacro`

`monicity` tries to solve a goal of the form `Monic f`.
It converts the goal into a goal of the form `natDegree f ≤ n` and one of the form `f.coeff n = 1`
and calls `compute_degree` on those two goals.

The variant `monicity!` starts like `monicity`, but calls `compute_degree!` on the two side-goals.

# monicity!
Defined in: `Mathlib.Tactic.ComputeDegree.tacticMonicity!`

`monicity` tries to solve a goal of the form `Monic f`.
It converts the goal into a goal of the form `natDegree f ≤ n` and one of the form `f.coeff n = 1`
and calls `compute_degree` on those two goals.

The variant `monicity!` starts like `monicity`, but calls `compute_degree!` on the two side-goals.

# mono
Defined in: `Mathlib.Tactic.Monotonicity.mono`

`mono` applies monotonicity rules and local hypotheses repetitively.  For example,
```lean
example (x y z k : ℤ)
    (h : 3 ≤ (4 : ℤ))
    (h' : z ≤ y) :
    (k + 3 + x) - y ≤ (k + 4 + x) - z := by
  mono
```

# monoidal_coherence
Defined in: `Mathlib.Tactic.Coherence.tacticMonoidal_coherence`

Coherence tactic for monoidal categories.
Use `pure_coherence` instead, which is a frontend to this one.

# monoidal_nf
Defined in: `tacticMonoidal_nf`

Normalize the both sides of an equality.

# monoidal_simps
Defined in: `Mathlib.Tactic.Coherence.monoidal_simps`

Simp lemmas for rewriting a hom in monoical categories into a normal form.

# move_add
Defined in: `Mathlib.MoveAdd.tacticMove_add_`

The tactic `move_add` rearranges summands of expressions.
Calling `move_add [a, ← b, ...]` matches `a, b,...` with summands in the main goal.
It then moves `a` to the far right and `b` to the far left of each addition in which they appear.
The side to which the summands are moved is determined by the presence or absence of the arrow `←`.

The inputs `a, b,...` can be any terms, also with underscores.
The tactic uses the first "new" summand that unifies with each one of the given inputs.

There is a multiplicative variant, called `move_mul`.

There is also a general tactic for a "binary associative commutative operation": `move_oper`.
In this case the syntax requires providing first a term whose head symbol is the operation.
E.g. `move_oper HAdd.hAdd [...]` is the same as `move_add`, while `move_oper Max.max [...]`
rearranges `max`s.

# move_mul
Defined in: `Mathlib.MoveAdd.tacticMove_mul_`

The tactic `move_add` rearranges summands of expressions.
Calling `move_add [a, ← b, ...]` matches `a, b,...` with summands in the main goal.
It then moves `a` to the far right and `b` to the far left of each addition in which they appear.
The side to which the summands are moved is determined by the presence or absence of the arrow `←`.

The inputs `a, b,...` can be any terms, also with underscores.
The tactic uses the first "new" summand that unifies with each one of the given inputs.

There is a multiplicative variant, called `move_mul`.

There is also a general tactic for a "binary associative commutative operation": `move_oper`.
In this case the syntax requires providing first a term whose head symbol is the operation.
E.g. `move_oper HAdd.hAdd [...]` is the same as `move_add`, while `move_oper Max.max [...]`
rearranges `max`s.

# move_oper
Defined in: `Mathlib.MoveAdd.moveOperTac`

The tactic `move_add` rearranges summands of expressions.
Calling `move_add [a, ← b, ...]` matches `a, b,...` with summands in the main goal.
It then moves `a` to the far right and `b` to the far left of each addition in which they appear.
The side to which the summands are moved is determined by the presence or absence of the arrow `←`.

The inputs `a, b,...` can be any terms, also with underscores.
The tactic uses the first "new" summand that unifies with each one of the given inputs.

There is a multiplicative variant, called `move_mul`.

There is also a general tactic for a "binary associative commutative operation": `move_oper`.
In this case the syntax requires providing first a term whose head symbol is the operation.
E.g. `move_oper HAdd.hAdd [...]` is the same as `move_add`, while `move_oper Max.max [...]`
rearranges `max`s.

# mv_bisim
Defined in: `Mathlib.Tactic.MvBisim.tacticMv_bisim___With___`

tactic for proof by bisimulation

# native_decide
Defined in: `Lean.Parser.Tactic.nativeDecide`

`native_decide` will attempt to prove a goal of type `p` by synthesizing an instance
of `Decidable p` and then evaluating it to `isTrue ..`. Unlike `decide`, this
uses `#eval` to evaluate the decidability instance.

This should be used with care because it adds the entire lean compiler to the trusted
part, and the axiom `ofReduceBool` will show up in `#print axioms` for theorems using
this method or anything that transitively depends on them. Nevertheless, because it is
compiled, this can be significantly more efficient than using `decide`, and for very
large computations this is one way to run external programs and trust the result.
```lean
example : (List.range 1000).length = 1000 := by native_decide
```

# next
Defined in: `Lean.Parser.Tactic.«tacticNext_=>_»`

`next => tac` focuses on the next goal and solves it using `tac`, or else fails.
`next x₁ ... xₙ => tac` additionally renames the `n` most recent hypotheses with
inaccessible names to the given names.

# nlinarith
Defined in: `nlinarith`

An extension of `linarith` with some preprocessing to allow it to solve some nonlinear arithmetic
problems. (Based on Coq's `nra` tactic.) See `linarith` for the available syntax of options,
which are inherited by `nlinarith`; that is, `nlinarith!` and `nlinarith only [h1, h2]` all work as
in `linarith`. The preprocessing is as follows:

* For every subterm `a ^ 2` or `a * a` in a hypothesis or the goal,
  the assumption `0 ≤ a ^ 2` or `0 ≤ a * a` is added to the context.
* For every pair of hypotheses `a1 R1 b1`, `a2 R2 b2` in the context, `R1, R2 ∈ {<, ≤, =}`,
  the assumption `0 R' (b1 - a1) * (b2 - a2)` is added to the context (non-recursively),
  where `R ∈ {<, ≤, =}` is the appropriate comparison derived from `R1, R2`.

# nlinarith!
Defined in: `tacticNlinarith!_`

An extension of `linarith` with some preprocessing to allow it to solve some nonlinear arithmetic
problems. (Based on Coq's `nra` tactic.) See `linarith` for the available syntax of options,
which are inherited by `nlinarith`; that is, `nlinarith!` and `nlinarith only [h1, h2]` all work as
in `linarith`. The preprocessing is as follows:

* For every subterm `a ^ 2` or `a * a` in a hypothesis or the goal,
  the assumption `0 ≤ a ^ 2` or `0 ≤ a * a` is added to the context.
* For every pair of hypotheses `a1 R1 b1`, `a2 R2 b2` in the context, `R1, R2 ∈ {<, ≤, =}`,
  the assumption `0 R' (b1 - a1) * (b2 - a2)` is added to the context (non-recursively),
  where `R ∈ {<, ≤, =}` is the appropriate comparison derived from `R1, R2`.

# nofun
Defined in: `Lean.Parser.Tactic.tacticNofun`

The tactic `nofun` is shorthand for `exact nofun`: it introduces the assumptions, then performs an
empty pattern match, closing the goal if the introduced pattern is impossible.

# nomatch
Defined in: `Lean.Parser.Tactic.«tacticNomatch_,,»`

The tactic `nomatch h` is shorthand for `exact nomatch h`.

# noncomm_ring
Defined in: `Mathlib.Tactic.NoncommRing.noncomm_ring`

A tactic for simplifying identities in not-necessarily-commutative rings.

An example:
```lean
example {R : Type*} [Ring R] (a b c : R) : a * (b + c + c - b) = 2 * a * c := by
  noncomm_ring
```

You can use `noncomm_ring [h]` to also simplify using `h`.

# nontriviality
Defined in: `Mathlib.Tactic.Nontriviality.nontriviality`

Attempts to generate a `Nontrivial α` hypothesis.

The tactic first checks to see that there is not already a `Nontrivial α` instance
before trying to synthesize one using other techniques.

If the goal is an (in)equality, the type `α` is inferred from the goal.
Otherwise, the type needs to be specified in the tactic invocation, as `nontriviality α`.

The `nontriviality` tactic will first look for strict inequalities amongst the hypotheses,
and use these to derive the `Nontrivial` instance directly.

Otherwise, it will perform a case split on `Subsingleton α ∨ Nontrivial α`, and attempt to discharge
the `Subsingleton` goal using `simp [h₁, h₂, ..., hₙ, nontriviality]`, where `[h₁, h₂, ..., hₙ]` is
a list of additional `simp` lemmas that can be passed to `nontriviality` using the syntax
`nontriviality α using h₁, h₂, ..., hₙ`.

```
example {R : Type} [OrderedRing R] {a : R} (h : 0 < a) : 0 < a := by
  nontriviality -- There is now a `Nontrivial R` hypothesis available.
  assumption
```

```
example {R : Type} [CommRing R] {r s : R} : r * s = s * r := by
  nontriviality -- There is now a `Nontrivial R` hypothesis available.
  apply mul_comm
```

```
example {R : Type} [OrderedRing R] {a : R} (h : 0 < a) : (2 : ℕ) ∣ 4 := by
  nontriviality R -- there is now a `Nontrivial R` hypothesis available.
  dec_trivial
```

```
def myeq {α : Type} (a b : α) : Prop := a = b

example {α : Type} (a b : α) (h : a = b) : myeq a b := by
  success_if_fail nontriviality α -- Fails
  nontriviality α using myeq -- There is now a `Nontrivial α` hypothesis available
  assumption
```

# norm_cast
Defined in: `Lean.Parser.Tactic.tacticNorm_cast_`

The `norm_cast` family of tactics is used to normalize certain coercions (*casts*) in expressions.
- `norm_cast` normalizes casts in the target.
- `norm_cast at h` normalizes casts in hypothesis `h`.

The tactic is basically a version of `simp` with a specific set of lemmas to move casts
upwards in the expression.
Therefore even in situations where non-terminal `simp` calls are discouraged (because of fragility),
`norm_cast` is considered to be safe.
It also has special handling of numerals.

For instance, given an assumption
```lean
a b : ℤ
h : ↑a + ↑b < (10 : ℚ)
```
writing `norm_cast at h` will turn `h` into
```lean
h : a + b < 10
```

There are also variants of basic tactics that use `norm_cast` to normalize expressions during
their operation, to make them more flexible about the expressions they accept
(we say that it is a tactic *modulo* the effects of `norm_cast`):
- `exact_mod_cast` for `exact` and `apply_mod_cast` for `apply`.
  Writing `exact_mod_cast h` and `apply_mod_cast h` will normalize casts
  in the goal and `h` before using `exact h` or `apply h`.
- `rw_mod_cast` for `rw`. It applies `norm_cast` between rewrites.
- `assumption_mod_cast` for `assumption`.
  This is effectively `norm_cast at *; assumption`, but more efficient.
  It normalizes casts in the goal and, for every hypothesis `h` in the context,
  it will try to normalize casts in `h` and use `exact h`.

See also `push_cast`, which moves casts inwards rather than lifting them outwards.

# norm_cast0
Defined in: `Lean.Parser.Tactic.normCast0`

Implementation of `norm_cast` (the full `norm_cast` calls `trivial` afterwards).

# norm_num
Defined in: `Mathlib.Tactic.normNum`

Normalize numerical expressions. Supports the operations `+` `-` `*` `/` `⁻¹` `^` and `%`
over numerical types such as `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ` and some general algebraic types,
and can prove goals of the form `A = B`, `A ≠ B`, `A < B` and `A ≤ B`, where `A` and `B` are
numerical expressions. It also has a relatively simple primality prover.

# norm_num1
Defined in: `Mathlib.Tactic.normNum1`

Basic version of `norm_num` that does not call `simp`.

# nth_rewrite
Defined in: `Mathlib.Tactic.nthRewriteSeq`

`nth_rewrite` is a variant of `rewrite` that only changes the `n₁, ..., nₖ`ᵗʰ _occurrence_ of
the expression to be rewritten. `nth_rewrite n₁ ... nₖ [eq₁, eq₂,..., eqₘ]` will rewrite the
`n₁, ..., nₖ`ᵗʰ _occurrence_ of each of the `m` equalities `eqᵢ`in that order. Occurrences are
counted beginning with `1` in order of precedence.

For example,
```lean
example (h : a = 1) : a + a + a + a + a = 5 := by
  nth_rewrite 2 3 [h]
/-
a: ℕ
h: a = 1
⊢ a + 1 + 1 + a + a = 5
-/
```
Notice that the second occurrence of `a` from the left has been rewritten by `nth_rewrite`.

To understand the importance of order of precedence, consider the example below
```lean
example (a b c : Nat) : (a + b) + c = (b + a) + c := by
  nth_rewrite 2 [Nat.add_comm] -- ⊢ (b + a) + c = (b + a) + c
```
Here, although the occurrence parameter is `2`, `(a + b)` is rewritten to `(b + a)`. This happens
because in order of precedence, the first occurrence of `_ + _` is the one that adds `a + b` to `c`.
The occurrence in `a + b` counts as the second occurrence.

If a term `t` is introduced by rewriting with `eqᵢ`, then this instance of `t` will be counted as an
_occurrence_ of `t` for all subsequent rewrites of `t` with `eqⱼ` for `j > i`. This behaviour is
illustrated by the example below
```lean
example (h : a = a + b) : a + a + a + a + a = 0 := by
  nth_rewrite 3 [h, h]
/-
a b: ℕ
h: a = a + b
⊢ a + a + (a + b + b) + a + a = 0
-/
```
Here, the first `nth_rewrite` with `h` introduces an additional occurrence of `a` in the goal.
That is, the goal state after the first rewrite looks like below
```lean
/-
a b: ℕ
h: a = a + b
⊢ a + a + (a + b) + a + a = 0
-/
```
This new instance of `a` also turns out to be the third _occurrence_ of `a`.  Therefore,
the next `nth_rewrite` with `h` rewrites this `a`.

# nth_rw
Defined in: `Mathlib.Tactic.nthRwSeq`

`nth_rw` is a variant of `rw` that only changes the `n₁, ..., nₖ`ᵗʰ _occurrence_ of the expression
to be rewritten. Like `rw`, and unlike `nth_rewrite`, it will try to close the goal by trying `rfl`
afterwards. `nth_rw n₁ ... nₖ [eq₁, eq₂,..., eqₘ]` will rewrite the `n₁, ..., nₖ`ᵗʰ _occurrence_ of
each of the `m` equalities `eqᵢ`in that order. Occurrences are counted beginning with `1` in
order of precedence. For example,
```lean
example (h : a = 1) : a + a + a + a + a = 5 := by
  nth_rw 2 3 [h]
/-
a: ℕ
h: a = 1
⊢ a + 1 + 1 + a + a = 5
-/
```
Notice that the second occurrence of `a` from the left has been rewritten by `nth_rewrite`.

To understand the importance of order of precedence, consider the example below
```lean
example (a b c : Nat) : (a + b) + c = (b + a) + c := by
  nth_rewrite 2 [Nat.add_comm] -- ⊢ (b + a) + c = (b + a) + c
```
Here, although the occurrence parameter is `2`, `(a + b)` is rewritten to `(b + a)`. This happens
because in order of precedence, the first occurrence of `_ + _` is the one that adds `a + b` to `c`.
The occurrence in `a + b` counts as the second occurrence.

If a term `t` is introduced by rewriting with `eqᵢ`, then this instance of `t` will be counted as an
_occurrence_ of `t` for all subsequent rewrites of `t` with `eqⱼ` for `j > i`. This behaviour is
illustrated by the example below
```lean
example (h : a = a + b) : a + a + a + a + a = 0 := by
  nth_rw 3 [h, h]
/-
a b: ℕ
h: a = a + b
⊢ a + a + (a + b + b) + a + a = 0
-/
```
Here, the first `nth_rw` with `h` introduces an additional occurrence of `a` in the goal. That is,
the goal state after the first rewrite looks like below
```lean
/-
a b: ℕ
h: a = a + b
⊢ a + a + (a + b) + a + a = 0
-/
```
This new instance of `a` also turns out to be the third _occurrence_ of `a`.  Therefore,
the next `nth_rw` with `h` rewrites this `a`.

Further, `nth_rw` will close the remaining goal with `rfl` if possible.

# observe
Defined in: `Mathlib.Tactic.LibrarySearch.observe`

`observe hp : p` asserts the proposition `p`, and tries to prove it using `exact?`.
If no proof is found, the tactic fails.
In other words, this tactic is equivalent to `have hp : p := by exact?`.

If `hp` is omitted, then the placeholder `this` is used.

The variant `observe? hp : p` will emit a trace message of the form `have hp : p := proof_term`.
This may be particularly useful to speed up proofs.

# observe?
Defined in: `Mathlib.Tactic.LibrarySearch.«tacticObserve?__:_Using__,,»`

`observe hp : p` asserts the proposition `p`, and tries to prove it using `exact?`.
If no proof is found, the tactic fails.
In other words, this tactic is equivalent to `have hp : p := by exact?`.

If `hp` is omitted, then the placeholder `this` is used.

The variant `observe? hp : p` will emit a trace message of the form `have hp : p := proof_term`.
This may be particularly useful to speed up proofs.

# observe?
Defined in: `Mathlib.Tactic.LibrarySearch.«tacticObserve?__:_»`

`observe hp : p` asserts the proposition `p`, and tries to prove it using `exact?`.
If no proof is found, the tactic fails.
In other words, this tactic is equivalent to `have hp : p := by exact?`.

If `hp` is omitted, then the placeholder `this` is used.

The variant `observe? hp : p` will emit a trace message of the form `have hp : p := proof_term`.
This may be particularly useful to speed up proofs.

# obtain
Defined in: `Lean.Parser.Tactic.obtain`

The `obtain` tactic is a combination of `have` and `rcases`. See `rcases` for
a description of supported patterns.

```lean
obtain ⟨patt⟩ : type := proof
```
is equivalent to
```lean
have h : type := proof
rcases h with ⟨patt⟩
```

If `⟨patt⟩` is omitted, `rcases` will try to infer the pattern.

If `type` is omitted, `:= proof` is required.

# omega
Defined in: `Lean.Parser.Tactic.omega`

The `omega` tactic, for resolving integer and natural linear arithmetic problems.

It is not yet a full decision procedure (no "dark" or "grey" shadows),
but should be effective on many problems.

We handle hypotheses of the form `x = y`, `x < y`, `x ≤ y`, and `k ∣ x` for `x y` in `Nat` or `Int`
(and `k` a literal), along with negations of these statements.

We decompose the sides of the inequalities as linear combinations of atoms.

If we encounter `x / k` or `x % k` for literal integers `k` we introduce new auxiliary variables
and the relevant inequalities.

On the first pass, we do not perform case splits on natural subtraction.
If `omega` fails, we recursively perform a case split on
a natural subtraction appearing in a hypothesis, and try again.

The options
```
omega (config :=
  { splitDisjunctions := true, splitNatSub := true, splitNatAbs := true, splitMinMax := true })
```
can be used to:
* `splitDisjunctions`: split any disjunctions found in the context,
  if the problem is not otherwise solvable.
* `splitNatSub`: for each appearance of `((a - b : Nat) : Int)`, split on `a ≤ b` if necessary.
* `splitNatAbs`: for each appearance of `Int.natAbs a`, split on `0 ≤ a` if necessary.
* `splitMinMax`: for each occurrence of `min a b`, split on `min a b = a ∨ min a b = b`
Currently, all of these are on by default.

# on_goal
Defined in: `Batteries.Tactic.«tacticOn_goal-_=>_»`

`on_goal n => tacSeq` creates a block scope for the `n`-th goal and tries the sequence
of tactics `tacSeq` on it.

`on_goal -n => tacSeq` does the same, but the `n`-th goal is chosen by counting from the
bottom.

The goal is not required to be solved and any resulting subgoals are inserted back into the
list of goals, replacing the chosen goal.

# open
Defined in: `Lean.Parser.Tactic.open`

`open Foo in tacs` (the tactic) acts like `open Foo` at command level,
but it opens a namespace only within the tactics `tacs`.

# peel
Defined in: `Mathlib.Tactic.Peel.peel`

Peels matching quantifiers off of a given term and the goal and introduces the relevant variables.

- `peel e` peels all quantifiers (at reducible transparency),
  using `this` for the name of the peeled hypothesis.
- `peel e with h` is `peel e` but names the peeled hypothesis `h`.
  If `h` is `_` then uses `this` for the name of the peeled hypothesis.
- `peel n e` peels `n` quantifiers (at default transparency).
- `peel n e with x y z ... h` peels `n` quantifiers, names the peeled hypothesis `h`,
  and uses `x`, `y`, `z`, and so on to name the introduced variables; these names may be `_`.
  If `h` is `_` then uses `this` for the name of the peeled hypothesis.
  The length of the list of variables does not need to equal `n`.
- `peel e with x₁ ... xₙ h` is `peel n e with x₁ ... xₙ h`.

There are also variants that apply to an iff in the goal:
- `peel n` peels `n` quantifiers in an iff.
- `peel with x₁ ... xₙ` peels `n` quantifiers in an iff and names them.

Given `p q : ℕ → Prop`, `h : ∀ x, p x`, and a goal `⊢ : ∀ x, q x`, the tactic `peel h with x h'`
will introduce `x : ℕ`, `h' : p x` into the context and the new goal will be `⊢ q x`. This works
with `∃`, as well as `∀ᶠ` and `∃ᶠ`, and it can even be applied to a sequence of quantifiers. Note
that this is a logically weaker setup, so using this tactic is not always feasible.

For a more complex example, given a hypothesis and a goal:
```lean
h : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℝ) < ε
⊢ ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℝ) ≤ ε
```
(which differ only in `<`/`≤`), applying `peel h with ε hε N n hn h_peel` will yield a tactic state:
```lean
h : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℝ) < ε
ε : ℝ
hε : 0 < ε
N n : ℕ
hn : N ≤ n
h_peel : 1 / (n + 1 : ℝ) < ε
⊢ 1 / (n + 1 : ℝ) ≤ ε
```
and the goal can be closed with `exact h_peel.le`.
Note that in this example, `h` and the goal are logically equivalent statements, but `peel`
*cannot* be immediately applied to show that the goal implies `h`.

In addition, `peel` supports goals of the form `(∀ x, p x) ↔ ∀ x, q x`, or likewise for any
other quantifier. In this case, there is no hypothesis or term to supply, but otherwise the syntax
is the same. So for such goals, the syntax is `peel 1` or `peel with x`, and after which the
resulting goal is `p x ↔ q x`. The `congr!` tactic can also be applied to goals of this form using
`congr! 1 with x`. While `congr!` applies congruence lemmas in general, `peel` can be relied upon
to only apply to outermost quantifiers.

Finally, the user may supply a term `e` via `... using e` in order to close the goal
immediately. In particular, `peel h using e` is equivalent to `peel h; exact e`. The `using` syntax
may be paired with any of the other features of `peel`.

This tactic works by repeatedly applying lemmas such as `forall_imp`, `Exists.imp`,
`Filter.Eventually.mp`, `Filter.Frequently.mp`, and `Filter.Eventually.of_forall`.

# pgame_wf_tac
Defined in: `SetTheory.PGame.tacticPgame_wf_tac`

Discharges proof obligations of the form `⊢ Subsequent ..` arising in termination proofs
of definitions using well-founded recursion on `PGame`.

# pi_lower_bound
Defined in: `Real.«tacticPi_lower_bound[_,,]»`

Create a proof of `a < π` for a fixed rational number `a`, given a witness, which is a
sequence of rational numbers `√2 < r 1 < r 2 < ... < r n < 2` satisfying the property that
`√(2 + r i) ≤ r(i+1)`, where `r 0 = 0` and `√(2 - r n) ≥ a/2^(n+1)`.

# pi_upper_bound
Defined in: `Real.«tacticPi_upper_bound[_,,]»`

Create a proof of `π < a` for a fixed rational number `a`, given a witness, which is a
sequence of rational numbers `√2 < r 1 < r 2 < ... < r n < 2` satisfying the property that
`√(2 + r i) ≥ r(i+1)`, where `r 0 = 0` and `√(2 - r n) ≥ (a - 1/4^n) / 2^(n+1)`.

# pick_goal
Defined in: `Batteries.Tactic.«tacticPick_goal-_»`

`pick_goal n` will move the `n`-th goal to the front.

`pick_goal -n` will move the `n`-th goal (counting from the bottom) to the front.

See also `Tactic.rotate_goals`, which moves goals from the front to the back and vice-versa.

# polyrith
Defined in: `Mathlib.Tactic.Polyrith.«tacticPolyrithOnly[_]»`

Attempts to prove polynomial equality goals through polynomial arithmetic
on the hypotheses (and additional proof terms if the user specifies them).
It proves the goal by generating an appropriate call to the tactic
`linear_combination`. If this call succeeds, the call to `linear_combination`
is suggested to the user.

* `polyrith` will use all relevant hypotheses in the local context.
* `polyrith [t1, t2, t3]` will add proof terms t1, t2, t3 to the local context.
* `polyrith only [h1, h2, h3, t1, t2, t3]` will use only local hypotheses
  `h1`, `h2`, `h3`, and proofs `t1`, `t2`, `t3`. It will ignore the rest of the local context.

Notes:
* This tactic only works with a working internet connection, since it calls Sage
  using the SageCell web API at <https://sagecell.sagemath.org/>.
  Many thanks to the Sage team and organization for allowing this use.
* This tactic assumes that the user has `python3` installed and available on the path.
  (Test by opening a terminal and executing `python3 --version`.)
  It also assumes that the `requests` library is installed: `python3 -m pip install requests`.

Examples:

```lean
example (x y : ℚ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
    x*y = -2*y + 1 := by
  polyrith
-- Try this: linear_combination h1 - 2 * h2

example (x y z w : ℚ) (hzw : z = w) : x*z + 2*y*z = x*w + 2*y*w := by
  polyrith
-- Try this: linear_combination (2 * y + x) * hzw

constant scary : ∀ a b : ℚ, a + b = 0

example (a b c d : ℚ) (h : a + b = 0) (h2: b + c = 0) : a + b + c + d = 0 := by
  polyrith only [scary c d, h]
-- Try this: linear_combination scary c d + h
```

# positivity
Defined in: `Mathlib.Tactic.Positivity.positivity`

Tactic solving goals of the form `0 ≤ x`, `0 < x` and `x ≠ 0`.  The tactic works recursively
according to the syntax of the expression `x`, if the atoms composing the expression all have
numeric lower bounds which can be proved positive/nonnegative/nonzero by `norm_num`.  This tactic
either closes the goal or fails.

Examples:
```lean
example {a : ℤ} (ha : 3 < a) : 0 ≤ a ^ 3 + a := by positivity

example {a : ℤ} (ha : 1 < a) : 0 < |(3:ℤ) + a| := by positivity

example {b : ℤ} : 0 ≤ max (-3) (b ^ 2) := by positivity
```

# pure_coherence
Defined in: `Mathlib.Tactic.Coherence.pure_coherence`

`pure_coherence` uses the coherence theorem for monoidal categories to prove the goal.
It can prove any equality made up only of associators, unitors, and identities.
```lean
example {C : Type} [Category C] [MonoidalCategory C] :
  (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by
  pure_coherence
```

Users will typically just use the `coherence` tactic,
which can also cope with identities of the form
`a ≫ f ≫ b ≫ g ≫ c = a' ≫ f ≫ b' ≫ g ≫ c'`
where `a = a'`, `b = b'`, and `c = c'` can be proved using `pure_coherence`

# push_cast
Defined in: `Lean.Parser.Tactic.pushCast`

`push_cast` rewrites the goal to move certain coercions (*casts*) inward, toward the leaf nodes.
This uses `norm_cast` lemmas in the forward direction.
For example, `↑(a + b)` will be written to `↑a + ↑b`.
- `push_cast` moves casts inward in the goal.
- `push_cast at h` moves casts inward in the hypothesis `h`.
It can be used with extra simp lemmas with, for example, `push_cast [Int.add_zero]`.

Example:
```lean
example (a b : Nat)
    (h1 : ((a + b : Nat) : Int) = 10)
    (h2 : ((a + b + 0 : Nat) : Int) = 10) :
    ((a + b : Nat) : Int) = 10 := by
  /-
  h1 : ↑(a + b) = 10
  h2 : ↑(a + b + 0) = 10
  ⊢ ↑(a + b) = 10
  -/
  push_cast
  /- Now
  ⊢ ↑a + ↑b = 10
  -/
  push_cast at h1
  push_cast [Int.add_zero] at h2
  /- Now
  h1 h2 : ↑a + ↑b = 10
  -/
  exact h1
```

See also `norm_cast`.

# push_neg
Defined in: `Mathlib.Tactic.PushNeg.tacticPush_neg_`

Push negations into the conclusion of a hypothesis.
For instance, a hypothesis `h : ¬ ∀ x, ∃ y, x ≤ y` will be transformed by `push_neg at h` into
`h : ∃ x, ∀ y, y < x`. Variable names are conserved.
This tactic pushes negations inside expressions. For instance, given a hypothesis
```lean
h : ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - y₀| ≤ ε)
```
writing `push_neg at h` will turn `h` into
```lean
h : ∃ ε, ε > 0 ∧ ∀ δ, δ > 0 → (∃ x, |x - x₀| ≤ δ ∧ ε < |f x - y₀|),
```
(The pretty printer does *not* use the abbreviations `∀ δ > 0` and `∃ ε > 0` but this issue
has nothing to do with `push_neg`).

Note that names are conserved by this tactic, contrary to what would happen with `simp`
using the relevant lemmas. One can also use this tactic at the goal using `push_neg`,
at every hypothesis and the goal using `push_neg at *` or at selected hypotheses and the goal
using say `push_neg at h h' ⊢` as usual.

This tactic has two modes: in standard mode, it transforms `¬(p ∧ q)` into `p → ¬q`, whereas in
distrib mode it produces `¬p ∨ ¬q`. To use distrib mode, use `set_option push_neg.use_distrib true`.

# qify
Defined in: `Mathlib.Tactic.Qify.qify`

The `qify` tactic is used to shift propositions from `ℕ` or `ℤ` to `ℚ`.
This is often useful since `ℚ` has well-behaved division.
```lean
example (a b c x y z : ℕ) (h : ¬ x*y*z < 0) : c < a + 3*b := by
  qify
  qify at h
  /-
  h : ¬↑x * ↑y * ↑z < 0
  ⊢ ↑c < ↑a + 3 * ↑b
  -/
  sorry
```
`qify` can be given extra lemmas to use in simplification. This is especially useful in the
presence of nat subtraction: passing `≤` arguments will allow `push_cast` to do more work.
```lean
example (a b c : ℤ) (h : a / b = c) (hab : b ∣ a) (hb : b ≠ 0) : a = c * b := by
  qify [hab] at h hb ⊢
  exact (div_eq_iff hb).1 h
```
`qify` makes use of the `@[zify_simps]` and `@[qify_simps]` attributes to move propositions,
and the `push_cast` tactic to simplify the `ℚ`-valued expressions.

# rcases
Defined in: `Lean.Parser.Tactic.rcases`

`rcases` is a tactic that will perform `cases` recursively, according to a pattern. It is used to
destructure hypotheses or expressions composed of inductive types like `h1 : a ∧ b ∧ c ∨ d` or
`h2 : ∃ x y, trans_rel R x y`. Usual usage might be `rcases h1 with ⟨ha, hb, hc⟩ | hd` or
`rcases h2 with ⟨x, y, _ | ⟨z, hxz, hzy⟩⟩` for these examples.

Each element of an `rcases` pattern is matched against a particular local hypothesis (most of which
are generated during the execution of `rcases` and represent individual elements destructured from
the input expression). An `rcases` pattern has the following grammar:

* A name like `x`, which names the active hypothesis as `x`.
* A blank `_`, which does nothing (letting the automatic naming system used by `cases` name the
  hypothesis).
* A hyphen `-`, which clears the active hypothesis and any dependents.
* The keyword `rfl`, which expects the hypothesis to be `h : a = b`, and calls `subst` on the
  hypothesis (which has the effect of replacing `b` with `a` everywhere or vice versa).
* A type ascription `p : ty`, which sets the type of the hypothesis to `ty` and then matches it
  against `p`. (Of course, `ty` must unify with the actual type of `h` for this to work.)
* A tuple pattern `⟨p1, p2, p3⟩`, which matches a constructor with many arguments, or a series
  of nested conjunctions or existentials. For example if the active hypothesis is `a ∧ b ∧ c`,
  then the conjunction will be destructured, and `p1` will be matched against `a`, `p2` against `b`
  and so on.
* A `@` before a tuple pattern as in `@⟨p1, p2, p3⟩` will bind all arguments in the constructor,
  while leaving the `@` off will only use the patterns on the explicit arguments.
* An alternation pattern `p1 | p2 | p3`, which matches an inductive type with multiple constructors,
  or a nested disjunction like `a ∨ b ∨ c`.

A pattern like `⟨a, b, c⟩ | ⟨d, e⟩` will do a split over the inductive datatype,
naming the first three parameters of the first constructor as `a,b,c` and the
first two of the second constructor `d,e`. If the list is not as long as the
number of arguments to the constructor or the number of constructors, the
remaining variables will be automatically named. If there are nested brackets
such as `⟨⟨a⟩, b | c⟩ | d` then these will cause more case splits as necessary.
If there are too many arguments, such as `⟨a, b, c⟩` for splitting on
`∃ x, ∃ y, p x`, then it will be treated as `⟨a, ⟨b, c⟩⟩`, splitting the last
parameter as necessary.

`rcases` also has special support for quotient types: quotient induction into Prop works like
matching on the constructor `quot.mk`.

`rcases h : e with PAT` will do the same as `rcases e with PAT` with the exception that an
assumption `h : e = PAT` will be added to the context.

# rcongr
Defined in: `Batteries.Tactic.rcongr`

Repeatedly apply `congr` and `ext`, using the given patterns as arguments for `ext`.

There are two ways this tactic stops:
* `congr` fails (makes no progress), after having already applied `ext`.
* `congr` canceled out the last usage of `ext`. In this case, the state is reverted to before
  the `congr` was applied.

For example, when the goal is
```
⊢ (fun x => f x + 3) '' s = (fun x => g x + 3) '' s
```
then `rcongr x` produces the goal
```
x : α ⊢ f x = g x
```
This gives the same result as `congr; ext x; congr`.

In contrast, `congr` would produce
```
⊢ (fun x => f x + 3) = (fun x => g x + 3)
```
and `congr with x` (or `congr; ext x`) would produce
```
x : α ⊢ f x + 3 = g x + 3
```

# recover
Defined in: `Mathlib.Tactic.tacticRecover_`

Modifier `recover` for a tactic (sequence) to debug cases where goals are closed incorrectly.
The tactic `recover tacs` for a tactic (sequence) `tacs` applies the tactics and then adds goals
that are not closed, starting from the original goal.

# reduce
Defined in: `Mathlib.Tactic.tacticReduce__`

`reduce at loc` completely reduces the given location.
This also exists as a `conv`-mode tactic.

This does the same transformation as the `#reduce` command.

# reduce_mod_char
Defined in: `Tactic.ReduceModChar.reduce_mod_char`

The tactic `reduce_mod_char` looks for numeric expressions in characteristic `p`
and reduces these to lie between `0` and `p`.

For example:
```lean
example : (5 : ZMod 4) = 1 := by reduce_mod_char
example : (X ^ 2 - 3 * X + 4 : (ZMod 4)[X]) = X ^ 2 + X := by reduce_mod_char
```

It also handles negation, turning it into multiplication by `p - 1`,
and similarly subtraction.

This tactic uses the type of the subexpression to figure out if it is indeed of positive
characteristic, for improved performance compared to trying to synthesise a `CharP` instance.
The variant `reduce_mod_char!` also tries to use `CharP R n` hypotheses in the context.
(Limitations of the typeclass system mean the tactic can't search for a `CharP R n` instance if
`n` is not yet known; use `have : CharP R n := inferInstance; reduce_mod_char!` as a workaround.)

# reduce_mod_char!
Defined in: `Tactic.ReduceModChar.reduce_mod_char!`

The tactic `reduce_mod_char` looks for numeric expressions in characteristic `p`
and reduces these to lie between `0` and `p`.

For example:
```lean
example : (5 : ZMod 4) = 1 := by reduce_mod_char
example : (X ^ 2 - 3 * X + 4 : (ZMod 4)[X]) = X ^ 2 + X := by reduce_mod_char
```

It also handles negation, turning it into multiplication by `p - 1`,
and similarly subtraction.

This tactic uses the type of the subexpression to figure out if it is indeed of positive
characteristic, for improved performance compared to trying to synthesise a `CharP` instance.
The variant `reduce_mod_char!` also tries to use `CharP R n` hypotheses in the context.
(Limitations of the typeclass system mean the tactic can't search for a `CharP R n` instance if
`n` is not yet known; use `have : CharP R n := inferInstance; reduce_mod_char!` as a workaround.)

# refine
Defined in: `Lean.Parser.Tactic.refine`

`refine e` behaves like `exact e`, except that named (`?x`) or unnamed (`?_`)
holes in `e` that are not solved by unification with the main goal's target type
are converted into new goals, using the hole's name, if any, as the goal case name.

# refine'
Defined in: `Lean.Parser.Tactic.refine'`

`refine' e` behaves like `refine e`, except that unsolved placeholders (`_`)
and implicit parameters are also converted into new goals.

# refine_lift
Defined in: `Lean.Parser.Tactic.tacticRefine_lift_`

Auxiliary macro for lifting have/suffices/let/...
It makes sure the "continuation" `?_` is the main goal after refining.

# refine_lift'
Defined in: `Lean.Parser.Tactic.tacticRefine_lift'_`

Similar to `refine_lift`, but using `refine'`

# refold_let
Defined in: `Mathlib.Tactic.refoldLetStx`

`refold_let x y z at loc` looks for the bodies of local definitions `x`, `y`, and `z` at the given
location and replaces them with `x`, `y`, or `z`. This is the inverse of "zeta reduction."
This also exists as a `conv`-mode tactic.

# rel
Defined in: `Mathlib.Tactic.GCongr.«tacticRel[_]»`

The `rel` tactic applies "generalized congruence" rules to solve a relational goal by
"substitution".  For example,
```
example {a b x c d : ℝ} (h1 : a ≤ b) (h2 : c ≤ d) :
    x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  rel [h1, h2]
```
In this example we "substitute" the hypotheses `a ≤ b` and `c ≤ d` into the LHS `x ^ 2 * a + c` of
the goal and obtain the RHS `x ^ 2 * b + d`, thus proving the goal.

The "generalized congruence" rules used are the library lemmas which have been tagged with the
attribute `@[gcongr]`.  For example, the first example constructs the proof term
```
add_le_add (mul_le_mul_of_nonneg_left h1 (pow_bit0_nonneg x 1)) h2
```
using the generalized congruence lemmas `add_le_add` and `mul_le_mul_of_nonneg_left`.  If there are
no applicable generalized congruence lemmas, the tactic fails.

The tactic attempts to discharge side goals to these "generalized congruence" lemmas (such as the
side goal `0 ≤ x ^ 2` in the above application of `mul_le_mul_of_nonneg_left`) using the tactic
`gcongr_discharger`, which wraps `positivity` but can also be extended. If the side goals cannot
be discharged in this way, the tactic fails.

# rename
Defined in: `Lean.Parser.Tactic.rename`

`rename t => x` renames the most recent hypothesis whose type matches `t`
(which may contain placeholders) to `x`, or fails if no such hypothesis could be found.

# rename'
Defined in: `Mathlib.Tactic.rename'`

`rename' h => hnew` renames the hypothesis named `h` to `hnew`.
To rename several hypothesis, use `rename' h₁ => h₁new, h₂ => h₂new`.
You can use `rename' a => b, b => a` to swap two variables.

# rename_bvar
Defined in: `Mathlib.Tactic.«tacticRename_bvar_→__»`

* `rename_bvar old new` renames all bound variables named `old` to `new` in the target.
* `rename_bvar old new at h` does the same in hypothesis `h`.

```lean
example (P : ℕ → ℕ → Prop) (h : ∀ n, ∃ m, P n m) : ∀ l, ∃ m, P l m := by
  rename_bvar n q at h -- h is now ∀ (q : ℕ), ∃ (m : ℕ), P q m,
  rename_bvar m n -- target is now ∀ (l : ℕ), ∃ (n : ℕ), P k n,
  exact h -- Lean does not care about those bound variable names
```
Note: name clashes are resolved automatically.

# rename_i
Defined in: `Lean.Parser.Tactic.renameI`

`rename_i x_1 ... x_n` renames the last `n` inaccessible names using the given names.

# repeat
Defined in: `Lean.Parser.Tactic.tacticRepeat_`

`repeat tac` repeatedly applies `tac` so long as it succeeds.
The tactic `tac` may be a tactic sequence, and if `tac` fails at any point in its execution,
`repeat` will revert any partial changes that `tac` made to the tactic state.

The tactic `tac` should eventually fail, otherwise `repeat tac` will run indefinitely.

See also:
* `try tac` is like `repeat tac` but will apply `tac` at most once.
* `repeat' tac` recursively applies `tac` to each goal.
* `first | tac1 | tac2` implements the backtracking used by `repeat`

# repeat'
Defined in: `Lean.Parser.Tactic.repeat'`

`repeat' tac` recursively applies `tac` on all of the goals so long as it succeeds.
That is to say, if `tac` produces multiple subgoals, then `repeat' tac` is applied to each of them.

See also:
* `repeat tac` simply repeatedly applies `tac`.
* `repeat1' tac` is `repeat' tac` but requires that `tac` succeed for some goal at least once.

# repeat1
Defined in: `Mathlib.Tactic.tacticRepeat1_`

`repeat1 tac` applies `tac` to main goal at least once. If the application succeeds,
the tactic is applied recursively to the generated subgoals until it eventually fails.

# repeat1'
Defined in: `Lean.Parser.Tactic.repeat1'`

`repeat1' tac` recursively applies to `tac` on all of the goals so long as it succeeds,
but `repeat1' tac` fails if `tac` succeeds on none of the initial goals.

See also:
* `repeat tac` simply applies `tac` repeatedly.
* `repeat' tac` is like `repeat1' tac` but it does not require that `tac` succeed at least once.

# replace
Defined in: `Mathlib.Tactic.replace'`

Acts like `have`, but removes a hypothesis with the same name as
this one if possible. For example, if the state is:

Then after `replace h : β` the state will be:

```lean
case h
f : α → β
h : α
⊢ β

f : α → β
h : β
⊢ goal
```

whereas `have h : β` would result in:

```lean
case h
f : α → β
h : α
⊢ β

f : α → β
h✝ : α
h : β
⊢ goal
```

# replace
Defined in: `Lean.Parser.Tactic.replace`

Acts like `have`, but removes a hypothesis with the same name as
this one if possible. For example, if the state is:

```lean
f : α → β
h : α
⊢ goal
```

Then after `replace h := f h` the state will be:

```lean
f : α → β
h : β
⊢ goal
```

whereas `have h := f h` would result in:

```lean
f : α → β
h† : α
h : β
⊢ goal
```

This can be used to simulate the `specialize` and `apply at` tactics of Coq.

# restrict_tac
Defined in: `TopCat.Presheaf.restrict_tac`

`restrict_tac` solves relations among subsets (copied from `aesop cat`)

# restrict_tac?
Defined in: `TopCat.Presheaf.restrict_tac?`

`restrict_tac?` passes along `Try this` from `aesop`

# revert
Defined in: `Lean.Parser.Tactic.revert`

`revert x...` is the inverse of `intro x...`: it moves the given hypotheses
into the main goal's target type.

# rewrite
Defined in: `Lean.Parser.Tactic.rewriteSeq`

`rewrite [e]` applies identity `e` as a rewrite rule to the target of the main goal.
If `e` is preceded by left arrow (`←` or `<-`), the rewrite is applied in the reverse direction.
If `e` is a defined constant, then the equational theorems associated with `e` are used.
This provides a convenient way to unfold `e`.
- `rewrite [e₁, ..., eₙ]` applies the given rules sequentially.
- `rewrite [e] at l` rewrites `e` at location(s) `l`, where `l` is either `*` or a
  list of hypotheses in the local context. In the latter case, a turnstile `⊢` or `|-`
  can also be used, to signify the target of the goal.

Using `rw (config := {occs := .pos L}) [e]`,
where `L : List Nat`, you can control which "occurrences" are rewritten.
(This option applies to each rule, so usually this will only be used with a single rule.)
Occurrences count from `1`.
At each allowed occurrence, arguments of the rewrite rule `e` may be instantiated,
restricting which later rewrites can be found.
(Disallowed occurrences do not result in instantiation.)
`{occs := .neg L}` allows skipping specified occurrences.

# rfl
Defined in: `Lean.Parser.Tactic.tacticRfl`

`rfl` tries to close the current goal using reflexivity.
This is supposed to be an extensible tactic and users can add their own support
for new reflexive relations.

Remark: `rfl` is an extensible tactic. We later add `macro_rules` to try different
reflexivity theorems (e.g., `Iff.rfl`).

# rfl'
Defined in: `Lean.Parser.Tactic.tacticRfl'`

`rfl'` is similar to `rfl`, but disables smart unfolding and unfolds all kinds of definitions,
theorems included (relevant for declarations defined by well-founded recursion).

# rify
Defined in: `Mathlib.Tactic.Rify.rify`

The `rify` tactic is used to shift propositions from `ℕ`, `ℤ` or `ℚ` to `ℝ`.
Although less useful than its cousins `zify` and `qify`, it can be useful when your
goal or context already involves real numbers.

In the example below, assumption `hn` is about natural numbers, `hk` is about integers
and involves casting a natural number to `ℤ`, and the conclusion is about real numbers.
The proof uses `rify` to lift both assumptions to `ℝ` before calling `linarith`.
```
example {n : ℕ} {k : ℤ} (hn : 8 ≤ n) (hk : 2 * k ≤ n + 2) :
    (0 : ℝ) < n - k - 1 := by
  rify at hn hk /- Now have hn : 8 ≤ (n : ℝ)   hk : 2 * (k : ℝ) ≤ (n : ℝ) + 2-/
  linarith
```

`rify` makes use of the `@[zify_simps]`, `@[qify_simps]` and `@[rify_simps]` attributes to move
propositions, and the `push_cast` tactic to simplify the `ℝ`-valued expressions.

`rify` can be given extra lemmas to use in simplification. This is especially useful in the
presence of nat subtraction: passing `≤` arguments will allow `push_cast` to do more work.
```lean
example (a b c : ℕ) (h : a - b < c) (hab : b ≤ a) : a < b + c := by
  rify [hab] at h ⊢
  linarith
```
Note that `zify` or `qify` would work just as well in the above example (and `zify` is the natural
choice since it is enough to get rid of the pathological `ℕ` subtraction).

# right
Defined in: `Lean.Parser.Tactic.right`

Applies the second constructor when
the goal is an inductive type with exactly two constructors, or fails otherwise.
```lean
example {p q : Prop} (h : q) : p ∨ q := by
  right
  exact h
```

# ring
Defined in: `Mathlib.Tactic.RingNF.ring`

Tactic for evaluating expressions in *commutative* (semi)rings, allowing for variables in the
exponent. If the goal is not appropriate for `ring` (e.g. not an equality) `ring_nf` will be
suggested.

* `ring!` will use a more aggressive reducibility setting to determine equality of atoms.
* `ring1` fails if the target is not an equality.

For example:
```lean
example (n : ℕ) (m : ℤ) : 2^(n+1) * m = 2 * 2^n * m := by ring
example (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) = (a^2 + b^2 + a * b + b * a) * (a + b)^n := by ring
example (x y : ℕ) : x + id y = y + id x := by ring!
example (x : ℕ) (h : x * 2 > 5): x + x > 5 := by ring; assumption -- suggests ring_nf
```

# ring!
Defined in: `Mathlib.Tactic.RingNF.tacticRing!`

Tactic for evaluating expressions in *commutative* (semi)rings, allowing for variables in the
exponent. If the goal is not appropriate for `ring` (e.g. not an equality) `ring_nf` will be
suggested.

* `ring!` will use a more aggressive reducibility setting to determine equality of atoms.
* `ring1` fails if the target is not an equality.

For example:
```lean
example (n : ℕ) (m : ℤ) : 2^(n+1) * m = 2 * 2^n * m := by ring
example (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) = (a^2 + b^2 + a * b + b * a) * (a + b)^n := by ring
example (x y : ℕ) : x + id y = y + id x := by ring!
example (x : ℕ) (h : x * 2 > 5): x + x > 5 := by ring; assumption -- suggests ring_nf
```

# ring1
Defined in: `Mathlib.Tactic.Ring.ring1`

Tactic for solving equations of *commutative* (semi)rings,
allowing variables in the exponent.

* This version of `ring` fails if the target is not an equality.
* The variant `ring1!` will use a more aggressive reducibility setting
  to determine equality of atoms.

# ring1!
Defined in: `Mathlib.Tactic.Ring.tacticRing1!`

Tactic for solving equations of *commutative* (semi)rings,
allowing variables in the exponent.

* This version of `ring` fails if the target is not an equality.
* The variant `ring1!` will use a more aggressive reducibility setting
  to determine equality of atoms.

# ring1_nf
Defined in: `Mathlib.Tactic.RingNF.ring1NF`

Tactic for solving equations of *commutative* (semi)rings, allowing variables in the exponent.

* This version of `ring1` uses `ring_nf` to simplify in atoms.
* The variant `ring1_nf!` will use a more aggressive reducibility setting
  to determine equality of atoms.

# ring1_nf!
Defined in: `Mathlib.Tactic.RingNF.tacticRing1_nf!_`

Tactic for solving equations of *commutative* (semi)rings, allowing variables in the exponent.

* This version of `ring1` uses `ring_nf` to simplify in atoms.
* The variant `ring1_nf!` will use a more aggressive reducibility setting
  to determine equality of atoms.

# ring_nf
Defined in: `Mathlib.Tactic.RingNF.ringNF`

Simplification tactic for expressions in the language of commutative (semi)rings,
which rewrites all ring expressions into a normal form.
* `ring_nf!` will use a more aggressive reducibility setting to identify atoms.
* `ring_nf (config := cfg)` allows for additional configuration:
  * `red`: the reducibility setting (overridden by `!`)
  * `recursive`: if true, `ring_nf` will also recurse into atoms
* `ring_nf` works as both a tactic and a conv tactic.
  In tactic mode, `ring_nf at h` can be used to rewrite in a hypothesis.

This can be used non-terminally to normalize ring expressions in the goal such as
`⊢ P (x + x + x)` ~> `⊢ P (x * 3)`, as well as being able to prove some equations that
`ring` cannot because they involve ring reasoning inside a subterm, such as
`sin (x + y) + sin (y + x) = 2 * sin (x + y)`.

# ring_nf!
Defined in: `Mathlib.Tactic.RingNF.tacticRing_nf!__`

Simplification tactic for expressions in the language of commutative (semi)rings,
which rewrites all ring expressions into a normal form.
* `ring_nf!` will use a more aggressive reducibility setting to identify atoms.
* `ring_nf (config := cfg)` allows for additional configuration:
  * `red`: the reducibility setting (overridden by `!`)
  * `recursive`: if true, `ring_nf` will also recurse into atoms
* `ring_nf` works as both a tactic and a conv tactic.
  In tactic mode, `ring_nf at h` can be used to rewrite in a hypothesis.

This can be used non-terminally to normalize ring expressions in the goal such as
`⊢ P (x + x + x)` ~> `⊢ P (x * 3)`, as well as being able to prove some equations that
`ring` cannot because they involve ring reasoning inside a subterm, such as
`sin (x + y) + sin (y + x) = 2 * sin (x + y)`.

# rintro
Defined in: `Lean.Parser.Tactic.rintro`

The `rintro` tactic is a combination of the `intros` tactic with `rcases` to
allow for destructuring patterns while introducing variables. See `rcases` for
a description of supported patterns. For example, `rintro (a | ⟨b, c⟩) ⟨d, e⟩`
will introduce two variables, and then do case splits on both of them producing
two subgoals, one with variables `a d e` and the other with `b c d e`.

`rintro`, unlike `rcases`, also supports the form `(x y : ty)` for introducing
and type-ascripting multiple variables at once, similar to binders.

# rotate_left
Defined in: `Lean.Parser.Tactic.rotateLeft`

`rotate_left n` rotates goals to the left by `n`. That is, `rotate_left 1`
takes the main goal and puts it to the back of the subgoal list.
If `n` is omitted, it defaults to `1`.

# rotate_right
Defined in: `Lean.Parser.Tactic.rotateRight`

Rotate the goals to the right by `n`. That is, take the goal at the back
and push it to the front `n` times. If `n` is omitted, it defaults to `1`.

# rsuffices
Defined in: `Mathlib.Tactic.rsuffices`

The `rsuffices` tactic is an alternative version of `suffices`, that allows the usage
of any syntax that would be valid in an `obtain` block. This tactic just calls `obtain`
on the expression, and then `rotate_left`.

# run_tac
Defined in: `Lean.Parser.Tactic.runTac`

The `run_tac doSeq` tactic executes code in `TacticM Unit`.

# rw
Defined in: `Lean.Parser.Tactic.rwSeq`

`rw` is like `rewrite`, but also tries to close the goal by "cheap" (reducible) `rfl` afterwards.

# rw?
Defined in: `Lean.Parser.Tactic.rewrites?`

`rw?` tries to find a lemma which can rewrite the goal.

`rw?` should not be left in proofs; it is a search tool, like `apply?`.

Suggestions are printed as `rw [h]` or `rw [← h]`.

You can use `rw? [-my_lemma, -my_theorem]` to prevent `rw?` using the named lemmas.

# rw_mod_cast
Defined in: `Lean.Parser.Tactic.tacticRw_mod_cast___`

Rewrites with the given rules, normalizing casts prior to each step.

# rw_search
Defined in: `Mathlib.Tactic.RewriteSearch.tacticRw_search_`

`rw_search` attempts to solve an equality goal
by repeatedly rewriting using lemmas from the library.

If no solution is found,
the best sequence of rewrites found before `maxHeartbeats` elapses is returned.

The search is a best-first search, minimising the Levenshtein edit distance between
the pretty-printed expressions on either side of the equality.
(The strings are tokenized at spaces,
separating delimiters `(`, `)`, `[`, `]`, and `,` into their own tokens.)

You can use `rw_search [-my_lemma, -my_theorem]`
to prevent `rw_search` from using the names theorems.

# rwa
Defined in: `Lean.Parser.Tactic.tacticRwa__`

`rwa` calls `rw`, then closes any remaining goals using `assumption`.

# saturate
Defined in: `Aesop.Frontend.tacticSaturate_____`


# saturate?
Defined in: `Aesop.Frontend.tacticSaturate?_____`


# save
Defined in: `Lean.Parser.Tactic.save`

`save` is defined to be the same as `skip`, but the elaborator has
special handling for occurrences of `save` in tactic scripts and will transform
`by tac1; save; tac2` to `by (checkpoint tac1); tac2`, meaning that the effect of `tac1`
will be cached and replayed. This is useful for improving responsiveness
when working on a long tactic proof, by using `save` after expensive tactics.

(TODO: do this automatically and transparently so that users don't have to use
this combinator explicitly.)

# says
Defined in: `Mathlib.Tactic.Says.says`

If you write `X says`, where `X` is a tactic that produces a "Try this: Y" message,
then you will get a message "Try this: X says Y".
Once you've clicked to replace `X says` with `X says Y`,
afterwards `X says Y` will only run `Y`.

The typical usage case is:
```lean
simp? [X] says simp only [X, Y, Z]
```

If you use `set_option says.verify true` (set automatically during CI) then `X says Y`
runs `X` and verifies that it still prints "Try this: Y".

# set
Defined in: `Mathlib.Tactic.setTactic`


# set!
Defined in: `Mathlib.Tactic.tacticSet!_`


# set_option
Defined in: `Lean.Parser.Tactic.set_option`

`set_option opt val in tacs` (the tactic) acts like `set_option opt val` at the command level,
but it sets the option only within the tactics `tacs`.

# show
Defined in: `Lean.Parser.Tactic.tacticShow_`

`show t` finds the first goal whose target unifies with `t`. It makes that the main goal,
performs the unification, and replaces the target with the unified version of `t`.

# show_term
Defined in: `Lean.Parser.Tactic.showTerm`

`show_term tac` runs `tac`, then prints the generated term in the form
"exact X Y Z" or "refine X ?_ Z" if there are remaining subgoals.

(For some tactics, the printed term will not be human readable.)

# simp
Defined in: `Lean.Parser.Tactic.simp`

The `simp` tactic uses lemmas and hypotheses to simplify the main goal target or
non-dependent hypotheses. It has many variants:
- `simp` simplifies the main goal target using lemmas tagged with the attribute `[simp]`.
- `simp [h₁, h₂, ..., hₙ]` simplifies the main goal target using the lemmas tagged
  with the attribute `[simp]` and the given `hᵢ`'s, where the `hᵢ`'s are expressions.-
- If an `hᵢ` is a defined constant `f`, then `f` is unfolded. If `f` has equational lemmas associated
  with it (and is not a projection or a `reducible` definition), these are used to rewrite with `f`.
- `simp [*]` simplifies the main goal target using the lemmas tagged with the
  attribute `[simp]` and all hypotheses.
- `simp only [h₁, h₂, ..., hₙ]` is like `simp [h₁, h₂, ..., hₙ]` but does not use `[simp]` lemmas.
- `simp [-id₁, ..., -idₙ]` simplifies the main goal target using the lemmas tagged
  with the attribute `[simp]`, but removes the ones named `idᵢ`.
- `simp at h₁ h₂ ... hₙ` simplifies the hypotheses `h₁ : T₁` ... `hₙ : Tₙ`. If
  the target or another hypothesis depends on `hᵢ`, a new simplified hypothesis
  `hᵢ` is introduced, but the old one remains in the local context.
- `simp at *` simplifies all the hypotheses and the target.
- `simp [*] at *` simplifies target and all (propositional) hypotheses using the
  other hypotheses.

# simp!
Defined in: `Lean.Parser.Tactic.simpAutoUnfold`

`simp!` is shorthand for `simp` with `autoUnfold := true`.
This will rewrite with all equation lemmas, which can be used to
partially evaluate many definitions.

# simp?
Defined in: `Lean.Parser.Tactic.simpTrace`

`simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal. This is useful for reducing the size of the simp
set in a local invocation to speed up processing.
```lean
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- prints "Try this: simp only [ite_true]"
```

This command can also be used in `simp_all` and `dsimp`.

# simp?!
Defined in: `Lean.Parser.Tactic.tacticSimp?!_`

`simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal. This is useful for reducing the size of the simp
set in a local invocation to speed up processing.
```lean
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- prints "Try this: simp only [ite_true]"
```

This command can also be used in `simp_all` and `dsimp`.

# simp_all
Defined in: `Lean.Parser.Tactic.simpAll`

`simp_all` is a stronger version of `simp [*] at *` where the hypotheses and target
are simplified multiple times until no simplification is applicable.
Only non-dependent propositional hypotheses are considered.

# simp_all!
Defined in: `Lean.Parser.Tactic.simpAllAutoUnfold`

`simp_all!` is shorthand for `simp_all` with `autoUnfold := true`.
This will rewrite with all equation lemmas, which can be used to
partially evaluate many definitions.

# simp_all?
Defined in: `Lean.Parser.Tactic.simpAllTrace`

`simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal. This is useful for reducing the size of the simp
set in a local invocation to speed up processing.
```lean
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- prints "Try this: simp only [ite_true]"
```

This command can also be used in `simp_all` and `dsimp`.

# simp_all?!
Defined in: `Lean.Parser.Tactic.tacticSimp_all?!_`

`simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal. This is useful for reducing the size of the simp
set in a local invocation to speed up processing.
```lean
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- prints "Try this: simp only [ite_true]"
```

This command can also be used in `simp_all` and `dsimp`.

# simp_all_arith
Defined in: `Lean.Parser.Tactic.simpAllArith`

`simp_all_arith` combines the effects of `simp_all` and `simp_arith`.

# simp_all_arith!
Defined in: `Lean.Parser.Tactic.simpAllArithAutoUnfold`

`simp_all_arith!` combines the effects of `simp_all`, `simp_arith` and `simp!`.

# simp_arith
Defined in: `Lean.Parser.Tactic.simpArith`

`simp_arith` is shorthand for `simp` with `arith := true` and `decide := true`.
This enables the use of normalization by linear arithmetic.

# simp_arith!
Defined in: `Lean.Parser.Tactic.simpArithAutoUnfold`

`simp_arith!` is shorthand for `simp_arith` with `autoUnfold := true`.
This will rewrite with all equation lemmas, which can be used to
partially evaluate many definitions.

# simp_intro
Defined in: `Mathlib.Tactic.«tacticSimp_intro_____..Only_»`

The `simp_intro` tactic is a combination of `simp` and `intro`: it will simplify the types of
variables as it introduces them and uses the new variables to simplify later arguments
and the goal.
* `simp_intro x y z` introduces variables named `x y z`
* `simp_intro x y z ..` introduces variables named `x y z` and then keeps introducing `_` binders
* `simp_intro (config := cfg) (discharger := tac) x y .. only [h₁, h₂]`:
  `simp_intro` takes the same options as `simp` (see `simp`)
```
example : x + 0 = y → x = z := by
  simp_intro h
  -- h: x = y ⊢ y = z
  sorry
```

# simp_rw
Defined in: `Mathlib.Tactic.tacticSimp_rw___`

`simp_rw` functions as a mix of `simp` and `rw`. Like `rw`, it applies each
rewrite rule in the given order, but like `simp` it repeatedly applies these
rules and also under binders like `∀ x, ...`, `∃ x, ...` and `fun x ↦...`.
Usage:

- `simp_rw [lemma_1, ..., lemma_n]` will rewrite the goal by applying the
  lemmas in that order. A lemma preceded by `←` is applied in the reverse direction.
- `simp_rw [lemma_1, ..., lemma_n] at h₁ ... hₙ` will rewrite the given hypotheses.
- `simp_rw [...] at *` rewrites in the whole context: all hypotheses and the goal.

Lemmas passed to `simp_rw` must be expressions that are valid arguments to `simp`.
For example, neither `simp` nor `rw` can solve the following, but `simp_rw` can:

```lean
example {a : ℕ}
    (h1 : ∀ a b : ℕ, a - 1 ≤ b ↔ a ≤ b + 1)
    (h2 : ∀ a b : ℕ, a ≤ b ↔ ∀ c, c < a → c < b) :
    (∀ b, a - 1 ≤ b) = ∀ b c : ℕ, c < a → c < b + 1 := by
  simp_rw [h1, h2]
```

# simp_wf
Defined in: `tacticSimp_wf`

Unfold definitions commonly used in well founded relation definitions.

Since Lean 4.12, Lean unfolds these definitions automatically before presenting the goal to the
user, and this tactic should no longer be necessary. Calls to `simp_wf` can be removed or replaced
by plain calls to `simp`.

# simpa
Defined in: `Lean.Parser.Tactic.simpa`

This is a "finishing" tactic modification of `simp`. It has two forms.

* `simpa [rules, ⋯] using e` will simplify the goal and the type of
`e` using `rules`, then try to close the goal using `e`.

Simplifying the type of `e` makes it more likely to match the goal
(which has also been simplified). This construction also tends to be
more robust under changes to the simp lemma set.

* `simpa [rules, ⋯]` will simplify the goal and the type of a
hypothesis `this` if present in the context, then try to close the goal using
the `assumption` tactic.

# simpa!
Defined in: `Lean.Parser.Tactic.tacticSimpa!_`

This is a "finishing" tactic modification of `simp`. It has two forms.

* `simpa [rules, ⋯] using e` will simplify the goal and the type of
`e` using `rules`, then try to close the goal using `e`.

Simplifying the type of `e` makes it more likely to match the goal
(which has also been simplified). This construction also tends to be
more robust under changes to the simp lemma set.

* `simpa [rules, ⋯]` will simplify the goal and the type of a
hypothesis `this` if present in the context, then try to close the goal using
the `assumption` tactic.

# simpa?
Defined in: `Lean.Parser.Tactic.tacticSimpa?_`

This is a "finishing" tactic modification of `simp`. It has two forms.

* `simpa [rules, ⋯] using e` will simplify the goal and the type of
`e` using `rules`, then try to close the goal using `e`.

Simplifying the type of `e` makes it more likely to match the goal
(which has also been simplified). This construction also tends to be
more robust under changes to the simp lemma set.

* `simpa [rules, ⋯]` will simplify the goal and the type of a
hypothesis `this` if present in the context, then try to close the goal using
the `assumption` tactic.

# simpa?!
Defined in: `Lean.Parser.Tactic.tacticSimpa?!_`

This is a "finishing" tactic modification of `simp`. It has two forms.

* `simpa [rules, ⋯] using e` will simplify the goal and the type of
`e` using `rules`, then try to close the goal using `e`.

Simplifying the type of `e` makes it more likely to match the goal
(which has also been simplified). This construction also tends to be
more robust under changes to the simp lemma set.

* `simpa [rules, ⋯]` will simplify the goal and the type of a
hypothesis `this` if present in the context, then try to close the goal using
the `assumption` tactic.

# sizeOf_list_dec
Defined in: `List.tacticSizeOf_list_dec`

This tactic, added to the `decreasing_trivial` toolbox, proves that
`sizeOf a < sizeOf as` when `a ∈ as`, which is useful for well founded recursions
over a nested inductive like `inductive T | mk : List T → T`.

# skip
Defined in: `Lean.Parser.Tactic.skip`

`skip` does nothing.

# sleep
Defined in: `Lean.Parser.Tactic.sleep`

The tactic `sleep ms` sleeps for `ms` milliseconds and does nothing.
It is used for debugging purposes only.

# sleep_heartbeats
Defined in: `tacticSleep_heartbeats_`

do nothing for at least n heartbeats

# slice_lhs
Defined in: `sliceLHS`

`slice_lhs a b => tac` zooms to the left hand side, uses associativity for categorical
composition as needed, zooms in on the `a`-th through `b`-th morphisms, and invokes `tac`.

# slice_rhs
Defined in: `sliceRHS`

`slice_rhs a b => tac` zooms to the right hand side, uses associativity for categorical
composition as needed, zooms in on the `a`-th through `b`-th morphisms, and invokes `tac`.

# slim_check
Defined in: `slimCheckSyntax`

`slim_check` considers a proof goal and tries to generate examples
that would contradict the statement.

Let's consider the following proof goal.

```lean
xs : List ℕ,
h : ∃ (x : ℕ) (H : x ∈ xs), x < 3
⊢ ∀ (y : ℕ), y ∈ xs → y < 5
```

The local constants will be reverted and an instance will be found for
`Testable (∀ (xs : List ℕ), (∃ x ∈ xs, x < 3) → (∀ y ∈ xs, y < 5))`.
The `Testable` instance is supported by an instance of `Sampleable (List ℕ)`,
`Decidable (x < 3)` and `Decidable (y < 5)`.

Examples will be created in ascending order of size (more or less)

The first counter-examples found will be printed and will result in an error:

```
===================
Found problems!
xs := [1, 28]
x := 1
y := 28
-------------------
```

If `slim_check` successfully tests 100 examples, it acts like
admit. If it gives up or finds a counter-example, it reports an error.

For more information on writing your own `Sampleable` and `Testable`
instances, see `Testing.SlimCheck.Testable`.

Optional arguments given with `slim_check (config : { ... })`
* `numInst` (default 100): number of examples to test properties with
* `maxSize` (default 100): final size argument

Options:
* `set_option trace.slim_check.decoration true`: print the proposition with quantifier annotations
* `set_option trace.slim_check.discarded true`: print the examples discarded because they do not
  satisfy assumptions
* `set_option trace.slim_check.shrink.steps true`: trace the shrinking of counter-example
* `set_option trace.slim_check.shrink.candidates true`: print the lists of candidates considered
  when shrinking each variable
* `set_option trace.slim_check.instance true`: print the instances of `testable` being used to test
  the proposition
* `set_option trace.slim_check.success true`: print the tested samples that satisfy a property

# smul_tac
Defined in: `RatFunc.tacticSmul_tac`

Solve equations for `RatFunc K` by applying `RatFunc.induction_on`.

# solve
Defined in: `Lean.solveTactic`

Similar to `first`, but succeeds only if one the given tactics solves the current goal.

# solve_by_elim
Defined in: `Lean.Parser.Tactic.solveByElim`

`solve_by_elim` calls `apply` on the main goal to find an assumption whose head matches
and then repeatedly calls `apply` on the generated subgoals until no subgoals remain,
performing at most `maxDepth` (defaults to 6) recursive steps.

`solve_by_elim` discharges the current goal or fails.

`solve_by_elim` performs backtracking if subgoals can not be solved.

By default, the assumptions passed to `apply` are the local context, `rfl`, `trivial`,
`congrFun` and `congrArg`.

The assumptions can be modified with similar syntax as for `simp`:
* `solve_by_elim [h₁, h₂, ..., hᵣ]` also applies the given expressions.
* `solve_by_elim only [h₁, h₂, ..., hᵣ]` does not include the local context,
  `rfl`, `trivial`, `congrFun`, or `congrArg` unless they are explicitly included.
* `solve_by_elim [-h₁, ... -hₙ]` removes the given local hypotheses.
* `solve_by_elim using [a₁, ...]` uses all lemmas which have been labelled
  with the attributes `aᵢ` (these attributes must be created using `register_label_attr`).

`solve_by_elim*` tries to solve all goals together, using backtracking if a solution for one goal
makes other goals impossible.
(Adding or removing local hypotheses may not be well-behaved when starting with multiple goals.)

Optional arguments passed via a configuration argument as `solve_by_elim (config := { ... })`
- `maxDepth`: number of attempts at discharging generated subgoals
- `symm`: adds all hypotheses derived by `symm` (defaults to `true`).
- `exfalso`: allow calling `exfalso` and trying again if `solve_by_elim` fails
  (defaults to `true`).
- `transparency`: change the transparency mode when calling `apply`. Defaults to `.default`,
  but it is often useful to change to `.reducible`,
  so semireducible definitions will not be unfolded when trying to apply a lemma.

See also the doc-comment for `Lean.Meta.Tactic.Backtrack.BacktrackConfig` for the options
`proc`, `suspend`, and `discharge` which allow further customization of `solve_by_elim`.
Both `apply_assumption` and `apply_rules` are implemented via these hooks.

# sorry
Defined in: `Lean.Parser.Tactic.tacticSorry`

The `sorry` tactic closes the goal using `sorryAx`. This is intended for stubbing out incomplete
parts of a proof while still having a syntactically correct proof skeleton. Lean will give
a warning whenever a proof uses `sorry`, so you aren't likely to miss it, but
you can double check if a theorem depends on `sorry` by using
`#print axioms my_thm` and looking for `sorryAx` in the axiom list.

# sorry_if_sorry
Defined in: `CategoryTheory.sorryIfSorry`

Close the main goal with `sorry` if its type contains `sorry`, and fail otherwise.

# specialize
Defined in: `Lean.Parser.Tactic.specialize`

The tactic `specialize h a₁ ... aₙ` works on local hypothesis `h`.
The premises of this hypothesis, either universal quantifications or
non-dependent implications, are instantiated by concrete terms coming
from arguments `a₁` ... `aₙ`.
The tactic adds a new hypothesis with the same name `h := h a₁ ... aₙ`
and tries to clear the previous one.

# split
Defined in: `Lean.Parser.Tactic.split`

The `split` tactic is useful for breaking nested if-then-else and `match` expressions into separate cases.
For a `match` expression with `n` cases, the `split` tactic generates at most `n` subgoals.

For example, given `n : Nat`, and a target `if n = 0 then Q else R`, `split` will generate
one goal with hypothesis `n = 0` and target `Q`, and a second goal with hypothesis
`¬n = 0` and target `R`.  Note that the introduced hypothesis is unnamed, and is commonly
renamed used the `case` or `next` tactics.

- `split` will split the goal (target).
- `split at h` will split the hypothesis `h`.

# split_ands
Defined in: `Batteries.Tactic.tacticSplit_ands`

`split_ands` applies `And.intro` until it does not make progress.

# split_ifs
Defined in: `Mathlib.Tactic.splitIfs`

Splits all if-then-else-expressions into multiple goals.
Given a goal of the form `g (if p then x else y)`, `split_ifs` will produce
two goals: `p ⊢ g x` and `¬p ⊢ g y`.
If there are multiple ite-expressions, then `split_ifs` will split them all,
starting with a top-most one whose condition does not contain another
ite-expression.
`split_ifs at *` splits all ite-expressions in all hypotheses as well as the goal.
`split_ifs with h₁ h₂ h₃` overrides the default names for the hypotheses.

# squeeze_scope
Defined in: `Batteries.Tactic.squeezeScope`

The `squeeze_scope` tactic allows aggregating multiple calls to `simp` coming from the same syntax
but in different branches of execution, such as in `cases x <;> simp`.
The reported `simp` call covers all simp lemmas used by this syntax.
```lean
@[simp] def bar (z : Nat) := 1 + z
@[simp] def baz (z : Nat) := 1 + z

@[simp] def foo : Nat → Nat → Nat
  | 0, z => bar z
  | _+1, z => baz z

example : foo x y = 1 + y := by
  cases x <;> simp? -- two printouts:
  -- "Try this: simp only [foo, bar]"
  -- "Try this: simp only [foo, baz]"

example : foo x y = 1 + y := by
  squeeze_scope
    cases x <;> simp -- only one printout: "Try this: simp only [foo, baz, bar]"
```

# stop
Defined in: `Lean.Parser.Tactic.tacticStop_`

`stop` is a helper tactic for "discarding" the rest of a proof:
it is defined as `repeat sorry`.
It is useful when working on the middle of a complex proofs,
and less messy than commenting the remainder of the proof.

# subsingleton
Defined in: `Mathlib.Tactic.subsingletonStx`

The `subsingleton` tactic tries to prove a goal of the form `x = y` or `HEq x y`
using the fact that the types involved are *subsingletons*
(a type with exactly zero or one terms).
To a first approximation, it does `apply Subsingleton.elim`.
As a nicety, `subsingleton` first runs the `intros` tactic.

- If the goal is an equality, it either closes the goal or fails.
- `subsingleton [inst1, inst2, ...]` can be used to add additional `Subsingleton` instances
  to the local context. This can be more flexible than
  `have := inst1; have := inst2; ...; subsingleton` since the tactic does not require that
  all placeholders be solved for.

Techniques the `subsingleton` tactic can apply:
- proof irrelevance
- heterogeneous proof irrelevance (via `proof_irrel_heq`)
- using `Subsingleton` (via `Subsingleton.elim`)
- proving `BEq` instances are equal if they are both lawful (via `lawful_beq_subsingleton`)

### Properties

The tactic is careful not to accidentally specialize `Sort _` to `Prop`,
avoiding the following surprising behavior of `apply Subsingleton.elim`:
```lean
example (α : Sort _) (x y : α) : x = y := by apply Subsingleton.elim
```
The reason this `example` goes through is that
it applies the `∀ (p : Prop), Subsingleton p` instance,
specializing the universe level metavariable in `Sort _` to `0`.

# subst
Defined in: `Lean.Parser.Tactic.subst`

`subst x...` substitutes each `x` with `e` in the goal if there is a hypothesis
of type `x = e` or `e = x`.
If `x` is itself a hypothesis of type `y = e` or `e = y`, `y` is substituted instead.

# subst_eqs
Defined in: `Lean.Parser.Tactic.substEqs`

`subst_eq` repeatedly substitutes according to the equality proof hypotheses in the context,
replacing the left side of the equality with the right, until no more progress can be made.

# subst_hom_lift
Defined in: `CategoryTheory.tacticSubst_hom_lift___`

`subst_hom_lift p f φ` tries to substitute `f` with `p(φ)` by using `p.IsHomLift f φ`

# subst_vars
Defined in: `Lean.Parser.Tactic.substVars`

Applies `subst` to all hypotheses of the form `h : x = t` or `h : t = x`.

# substs
Defined in: `Mathlib.Tactic.Substs.substs`

Applies the `subst` tactic to all given hypotheses from left to right.

# success_if_fail_with_msg
Defined in: `Mathlib.Tactic.successIfFailWithMsg`

`success_if_fail_with_msg msg tacs` runs `tacs` and succeeds only if they fail with the message
`msg`.

`msg` can be any term that evaluates to an explicit `String`.

# suffices
Defined in: `Lean.Parser.Tactic.tacticSuffices_`

Given a main goal `ctx ⊢ t`, `suffices h : t' from e` replaces the main goal with `ctx ⊢ t'`,
`e` must have type `t` in the context `ctx, h : t'`.

The variant `suffices h : t' by tac` is a shorthand for `suffices h : t' from by tac`.
If `h :` is omitted, the name `this` is used.

# suffices
Defined in: `Mathlib.Tactic.tacticSuffices_`


# swap
Defined in: `Batteries.Tactic.tacticSwap`

`swap` is a shortcut for `pick_goal 2`, which interchanges the 1st and 2nd goals.

# swap_var
Defined in: `Mathlib.Tactic.«tacticSwap_var__,,»`

`swap_var swap_rule₁, swap_rule₂, ⋯` applies `swap_rule₁` then `swap_rule₂` then `⋯`.

A *swap_rule* is of the form `x y` or `x ↔ y`, and "applying it" means swapping the variable name
`x` by `y` and vice-versa on all hypotheses and the goal.

```lean
example {P Q : Prop} (q : P) (p : Q) : P ∧ Q := by
  swap_var p ↔ q
  exact ⟨p, q⟩
```

# symm
Defined in: `Lean.Parser.Tactic.symm`

* `symm` applies to a goal whose target has the form `t ~ u` where `~` is a symmetric relation,
  that is, a relation which has a symmetry lemma tagged with the attribute [symm].
  It replaces the target with `u ~ t`.
* `symm at h` will rewrite a hypothesis `h : t ~ u` to `h : u ~ t`.

# symm_saturate
Defined in: `Lean.Parser.Tactic.symmSaturate`

For every hypothesis `h : a ~ b` where a `@[symm]` lemma is available,
add a hypothesis `h_symm : b ~ a`.

# tauto
Defined in: `Mathlib.Tactic.Tauto.tauto`

`tauto` breaks down assumptions of the form `_ ∧ _`, `_ ∨ _`, `_ ↔ _` and `∃ _, _`
and splits a goal of the form `_ ∧ _`, `_ ↔ _` or `∃ _, _` until it can be discharged
using `reflexivity` or `solve_by_elim`.
This is a finishing tactic: it either closes the goal or raises an error.

The Lean 3 version of this tactic by default attempted to avoid classical reasoning
where possible. This Lean 4 version makes no such attempt. The `itauto` tactic
is designed for that purpose.

# tfae_finish
Defined in: `Mathlib.Tactic.TFAE.tfaeFinish`

`tfae_finish` is used to close goals of the form `TFAE [P₁, P₂, ...]` once a sufficient collection
of hypotheses of the form `Pᵢ → Pⱼ` or `Pᵢ ↔ Pⱼ` have been introduced to the local context.

`tfae_have` can be used to conveniently introduce these hypotheses; see `tfae_have`.

Example:
```lean
example : TFAE [P, Q, R] := by
  tfae_have 1 → 2
  · /- proof of P → Q -/
  tfae_have 2 → 1
  · /- proof of Q → P -/
  tfae_have 2 ↔ 3
  · /- proof of Q ↔ R -/
  tfae_finish
```

# tfae_have
Defined in: `Mathlib.Tactic.TFAE.tfaeHave`

`tfae_have` introduces hypotheses for proving goals of the form `TFAE [P₁, P₂, ...]`. Specifically,
`tfae_have i arrow j` introduces a hypothesis of type `Pᵢ arrow Pⱼ` to the local context,
where `arrow` can be `→`, `←`, or `↔`. Note that `i` and `j` are natural number indices (beginning
at 1) used to specify the propositions `P₁, P₂, ...` that appear in the `TFAE` goal list. A proof
is required afterward, typically via a tactic block.

```lean
example (h : P → R) : TFAE [P, Q, R] := by
  tfae_have 1 → 3
  · exact h
  ...
```
The resulting context now includes `tfae_1_to_3 : P → R`.

The introduced hypothesis can be given a custom name, in analogy to `have` syntax:
```lean
tfae_have h : 2 ↔ 3
```

Once sufficient hypotheses have been introduced by `tfae_have`, `tfae_finish` can be used to close
the goal.

```lean
example : TFAE [P, Q, R] := by
  tfae_have 1 → 2
  · /- proof of P → Q -/
  tfae_have 2 → 1
  · /- proof of Q → P -/
  tfae_have 2 ↔ 3
  · /- proof of Q ↔ R -/
  tfae_finish
```

# toFinite_tac
Defined in: `Set.tacticToFinite_tac`

A tactic (for use in default params) that applies `Set.toFinite` to synthesize a `Set.Finite`
term.

# to_encard_tac
Defined in: `Set.tacticTo_encard_tac`

A tactic useful for transferring proofs for `encard` to their corresponding `card` statements

# trace
Defined in: `Lean.Parser.Tactic.trace`

Evaluates a term to a string (when possible), and prints it as a trace message.

# trace
Defined in: `Lean.Parser.Tactic.traceMessage`

`trace msg` displays `msg` in the info view.

# trace_state
Defined in: `Lean.Parser.Tactic.traceState`

`trace_state` displays the current state in the info view.

# trans
Defined in: `Mathlib.Tactic.tacticTrans___`

`trans` applies to a goal whose target has the form `t ~ u` where `~` is a transitive relation,
that is, a relation which has a transitivity lemma tagged with the attribute [trans].

* `trans s` replaces the goal with the two subgoals `t ~ s` and `s ~ u`.
* If `s` is omitted, then a metavariable is used instead.

Additionally, `trans` also applies to a goal whose target has the form `t → u`,
in which case it replaces the goal with `t → s` and `s → u`.

# transitivity
Defined in: `Mathlib.Tactic.tacticTransitivity___`


# triv
Defined in: `Batteries.Tactic.triv`

Deprecated variant of `trivial`.

# trivial
Defined in: `Lean.Parser.Tactic.tacticTrivial`

`trivial` tries different simple tactics (e.g., `rfl`, `contradiction`, ...)
to close the current goal.
You can use the command `macro_rules` to extend the set of tactics used. Example:
```lean
macro_rules | `(tactic| trivial) => `(tactic| simp)
```

# try
Defined in: `Lean.Parser.Tactic.tacticTry_`

`try tac` runs `tac` and succeeds even if `tac` failed.

# try_this
Defined in: `Mathlib.Tactic.tacticTry_this_`

Produces the text `Try this: <tac>` with the given tactic, and then executes it.

# type_check
Defined in: `tacticType_check_`

Type check the given expression, and trace its type.

# unfold
Defined in: `Lean.Parser.Tactic.unfold`

* `unfold id` unfolds definition `id`.
* `unfold id1 id2 ...` is equivalent to `unfold id1; unfold id2; ...`.

For non-recursive definitions, this tactic is identical to `delta`. For recursive definitions,
it uses the "unfolding lemma" `id.eq_def`, which is generated for each recursive definition,
to unfold according to the recursive definition given by the user.

# unfold?
Defined in: `Mathlib.Tactic.InteractiveUnfold.tacticUnfold?`

Replace the selected expression with a definitional unfolding.
- After each unfolding, we apply `whnfCore` to simplify the expression.
- Explicit natural number expressions are evaluated.
- Unfolds of class projections of instances marked with `@[default_instance]` are not shown.
  This is relevant for notational type classes like `+`: we don't want to suggest `Add.add a b`
  as an unfolding of `a + b`. Similarly for `OfNat n : Nat` which unfolds into `n : Nat`.

To use `unfold?`, shift-click an expression in the tactic state.
This gives a list of rewrite suggestions for the selected expression.
Click on a suggestion to replace `unfold?` by a tactic that performs this rewrite.

# unfold_let
Defined in: `Mathlib.Tactic.unfoldLetStx`

`unfold_let x y z at loc` unfolds the local definitions `x`, `y`, and `z` at the given
location, which is known as "zeta reduction."
This also exists as a `conv`-mode tactic.

If no local definitions are given, then all local definitions are unfolded.
This variant also exists as the `conv`-mode tactic `zeta`.

This is similar to the `unfold` tactic, which instead is for unfolding global definitions.

# unfold_projs
Defined in: `Mathlib.Tactic.unfoldProjsStx`

`unfold_projs at loc` unfolds projections of class instances at the given location.
This also exists as a `conv`-mode tactic.

# unhygienic
Defined in: `Lean.Parser.Tactic.tacticUnhygienic_`

`unhygienic tacs` runs `tacs` with name hygiene disabled.
This means that tactics that would normally create inaccessible names will instead
make regular variables. **Warning**: Tactics may change their variable naming
strategies at any time, so code that depends on autogenerated names is brittle.
Users should try not to use `unhygienic` if possible.
```lean
example : ∀ x : Nat, x = x := by unhygienic
  intro            -- x would normally be intro'd as inaccessible
  exact Eq.refl x  -- refer to x
```

# uniqueDiffWithinAt_Ici_Iic_univ
Defined in: `intervalIntegral.tacticUniqueDiffWithinAt_Ici_Iic_univ`

An auxiliary tactic closing goals `UniqueDiffWithinAt ℝ s a` where
`s ∈ {Iic a, Ici a, univ}`.

# unit_interval
Defined in: `Tactic.Interactive.tacticUnit_interval`

A tactic that solves `0 ≤ ↑x`, `0 ≤ 1 - ↑x`, `↑x ≤ 1`, and `1 - ↑x ≤ 1` for `x : I`.

# unreachable!
Defined in: `Batteries.Tactic.unreachable`

This tactic causes a panic when run (at compile time).
(This is distinct from `exact unreachable!`, which inserts code which will panic at run time.)

It is intended for tests to assert that a tactic will never be executed, which is otherwise an
unusual thing to do (and the `unreachableTactic` linter will give a warning if you do).

The `unreachableTactic` linter has a special exception for uses of `unreachable!`.
```
example : True := by trivial <;> unreachable!
```

# use
Defined in: `Mathlib.Tactic.useSyntax`

`use e₁, e₂, ⋯` is similar to `exists`, but unlike `exists` it is equivalent to applying the tactic
`refine ⟨e₁, e₂, ⋯, ?_, ⋯, ?_⟩` with any number of placeholders (rather than just one) and
then trying to close goals associated to the placeholders with a configurable discharger (rather
than just `try trivial`).

Examples:

```lean
example : ∃ x : Nat, x = x := by use 42

example : ∃ x : Nat, ∃ y : Nat, x = y := by use 42, 42

example : ∃ x : String × String, x.1 = x.2 := by use ("forty-two", "forty-two")
```

`use! e₁, e₂, ⋯` is similar but it applies constructors everywhere rather than just for
goals that correspond to the last argument of a constructor. This gives the effect that
nested constructors are being flattened out, with the supplied values being used along the
leaves and nodes of the tree of constructors.
With `use!` one can feed in each `42` one at a time:

```lean
example : ∃ p : Nat × Nat, p.1 = p.2 := by use! 42, 42

example : ∃ p : Nat × Nat, p.1 = p.2 := by use! (42, 42)
```

The second line makes use of the fact that `use!` tries refining with the argument before
applying a constructor. Also note that `use`/`use!` by default uses a tactic
called `use_discharger` to discharge goals, so `use! 42` will close the goal in this example since
`use_discharger` applies `rfl`, which as a consequence solves for the other `Nat` metavariable.

These tactics take an optional discharger to handle remaining explicit `Prop` constructor arguments.
By default it is `use (discharger := try with_reducible use_discharger) e₁, e₂, ⋯`.
To turn off the discharger and keep all goals, use `(discharger := skip)`.
To allow "heavy refls", use `(discharger := try use_discharger)`.

# use!
Defined in: `Mathlib.Tactic.«tacticUse!___,,»`

`use e₁, e₂, ⋯` is similar to `exists`, but unlike `exists` it is equivalent to applying the tactic
`refine ⟨e₁, e₂, ⋯, ?_, ⋯, ?_⟩` with any number of placeholders (rather than just one) and
then trying to close goals associated to the placeholders with a configurable discharger (rather
than just `try trivial`).

Examples:

```lean
example : ∃ x : Nat, x = x := by use 42

example : ∃ x : Nat, ∃ y : Nat, x = y := by use 42, 42

example : ∃ x : String × String, x.1 = x.2 := by use ("forty-two", "forty-two")
```

`use! e₁, e₂, ⋯` is similar but it applies constructors everywhere rather than just for
goals that correspond to the last argument of a constructor. This gives the effect that
nested constructors are being flattened out, with the supplied values being used along the
leaves and nodes of the tree of constructors.
With `use!` one can feed in each `42` one at a time:

```lean
example : ∃ p : Nat × Nat, p.1 = p.2 := by use! 42, 42

example : ∃ p : Nat × Nat, p.1 = p.2 := by use! (42, 42)
```

The second line makes use of the fact that `use!` tries refining with the argument before
applying a constructor. Also note that `use`/`use!` by default uses a tactic
called `use_discharger` to discharge goals, so `use! 42` will close the goal in this example since
`use_discharger` applies `rfl`, which as a consequence solves for the other `Nat` metavariable.

These tactics take an optional discharger to handle remaining explicit `Prop` constructor arguments.
By default it is `use (discharger := try with_reducible use_discharger) e₁, e₂, ⋯`.
To turn off the discharger and keep all goals, use `(discharger := skip)`.
To allow "heavy refls", use `(discharger := try use_discharger)`.

# use_discharger
Defined in: `Mathlib.Tactic.tacticUse_discharger`

Default discharger to try to use for the `use` and `use!` tactics.
This is similar to the `trivial` tactic but doesn't do things like `contradiction` or `decide`.

# use_finite_instance
Defined in: `tacticUse_finite_instance`


# valid
Defined in: `CategoryTheory.ComposableArrows.tacticValid`

A wrapper for `omega` which prefaces it with some quick and useful attempts

# volume_tac
Defined in: `MeasureTheory.tacticVolume_tac`

The tactic `exact volume`, to be used in optional (`autoParam`) arguments.

# whisker_simps
Defined in: `Mathlib.Tactic.BicategoryCoherence.whisker_simps`

Simp lemmas for rewriting a 2-morphism into a normal form.

# whnf
Defined in: `Mathlib.Tactic.tacticWhnf__`

`whnf at loc` puts the given location into weak-head normal form.
This also exists as a `conv`-mode tactic.

Weak-head normal form is when the outer-most expression has been fully reduced, the expression
may contain subexpressions which have not been reduced.

# with_panel_widgets
Defined in: `ProofWidgets.withPanelWidgetsTacticStx`

Display the selected panel widgets in the nested tactic script. For example,
assuming we have written a `GeometryDisplay` component,
```lean
by with_panel_widgets [GeometryDisplay]
  simp
  rfl
```
will show the geometry display alongside the usual tactic state throughout the proof.

# with_reducible
Defined in: `Lean.Parser.Tactic.withReducible`

`with_reducible tacs` executes `tacs` using the reducible transparency setting.
In this setting only definitions tagged as `[reducible]` are unfolded.

# with_reducible_and_instances
Defined in: `Lean.Parser.Tactic.withReducibleAndInstances`

`with_reducible_and_instances tacs` executes `tacs` using the `.instances` transparency setting.
In this setting only definitions tagged as `[reducible]` or type class instances are unfolded.

# with_unfolding_all
Defined in: `Lean.Parser.Tactic.withUnfoldingAll`

`with_unfolding_all tacs` executes `tacs` using the `.all` transparency setting.
In this setting all definitions that are not opaque are unfolded.

# witt_truncateFun_tac
Defined in: `witt_truncateFun_tac`

A macro tactic used to prove that `truncateFun` respects ring operations.

# wlog
Defined in: `Mathlib.Tactic.wlog`

`wlog h : P` will add an assumption `h : P` to the main goal, and add a side goal that requires
showing that the case `h : ¬ P` can be reduced to the case where `P` holds (typically by symmetry).

The side goal will be at the top of the stack. In this side goal, there will be two additional
assumptions:
- `h : ¬ P`: the assumption that `P` does not hold
- `this`: which is the statement that in the old context `P` suffices to prove the goal.
  By default, the name `this` is used, but the idiom `with H` can be added to specify the name:
  `wlog h : P with H`.

Typically, it is useful to use the variant `wlog h : P generalizing x y`,
to revert certain parts of the context before creating the new goal.
In this way, the wlog-claim `this` can be applied to `x` and `y` in different orders
(exploiting symmetry, which is the typical use case).

By default, the entire context is reverted.

# zify
Defined in: `Mathlib.Tactic.Zify.zify`

The `zify` tactic is used to shift propositions from `Nat` to `Int`.
This is often useful since `Int` has well-behaved subtraction.
```lean
example (a b c x y z : Nat) (h : ¬ x*y*z < 0) : c < a + 3*b := by
  zify
  zify at h
  /-
  h : ¬↑x * ↑y * ↑z < 0
  ⊢ ↑c < ↑a + 3 * ↑b
  -/
```
`zify` can be given extra lemmas to use in simplification. This is especially useful in the
presence of nat subtraction: passing `≤` arguments will allow `push_cast` to do more work.
```lean
example (a b c : Nat) (h : a - b < c) (hab : b ≤ a) : false := by
  zify [hab] at h
  /- h : ↑a - ↑b < ↑c -/
```
`zify` makes use of the `@[zify_simps]` attribute to move propositions,
and the `push_cast` tactic to simplify the `Int`-valued expressions.
`zify` is in some sense dual to the `lift` tactic.
`lift (z : Int) to Nat` will change the type of an
integer `z` (in the supertype) to `Nat` (the subtype), given a proof that `z ≥ 0`;
propositions concerning `z` will still be over `Int`.
`zify` changes propositions about `Nat` (the subtype) to propositions about `Int` (the supertype),
without changing the type of any variable.

syntax ... [Lean.Parser.Tactic.nestedTactic]

syntax ... [Lean.Parser.Tactic.unknown]

syntax ... [Lean.cdot]
`· tac` focuses on the main goal and tries to solve it using `tac`, or else fails.

