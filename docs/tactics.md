# Tactics

Mathlib version: `c6cdc1bb118778092f976bf4598bc63349b6d3c7`

## \#adaptation_note
Defined in: `«tactic#adaptation_note_»`

`#adaptation_note /-- comment -/` adds an adaptation note to the current file.
Adaptation notes are comments that are used to indicate that a piece of code
has been changed to accommodate a change in Lean core.
They typically require further action/maintenance to be taken in the future.

This syntax works as a command, or inline in tactic or term mode.

## \#check
Defined in: `Mathlib.Tactic.«tactic#check__»`

`#check t` elaborates the term `t` and then pretty prints it with its type as `e : ty`.

If `t` is an identifier, then it pretty prints a type declaration form
for the global constant `t` instead.
Use `#check (t)` to pretty print it as an elaborated expression.

Like the `#check` command, the `#check` tactic allows stuck typeclass instance problems.
These become metavariables in the output.

To display only explicit arguments in the type signature, see `#check'`.

## \#check'
Defined in: `Mathlib.Tactic.«tactic#check'__»`

The `#check' t` tactic elaborates the term `t` and then pretty prints it with its type as `e : ty`.
In contrast to `#check t`, we only pretty-print explicit arguments, and omit implicit or type class
arguments. Currently this only works when `t` is the name of a declaration.

If `t` is an identifier, then it pretty prints a type declaration form
for the global constant `t` instead.
Use `#check' (t)` to pretty print it as an elaborated expression.

Like other `#check` commands, the `#check'` tactic allows stuck typeclass instance problems.
These become metavariables in the output.

## \#count_heartbeats
Defined in: `Mathlib.CountHeartbeats.«tactic#count_heartbeats_»`

`#count_heartbeats tac` counts the heartbeats used by the tactic sequence `tac`
and prints an info line with the number of heartbeats.

* `#count_heartbeats! n in tac`, where `n` is an optional natural number literal, runs `tac`
  `n` times on the same goal while counting the heartbeats, and prints an info line with range and
  standard deviation. `n` can be left out, and defaults to 10.

Example:

```
example : 1 + 1 = 2 := by
  -- The next line will print an info message of this format; the exact number may vary.
  -- info: 4646
  #count_heartbeats simp

example : 1 + 1 = 2 := by
  -- The next line will print an info message of this format; the exact numbers may vary.
  -- info: Min: 4 Max: 4 StdDev: 2%
  #count_heartbeats! 37 in simp
```

## \#count_heartbeats!
Defined in: `Mathlib.CountHeartbeats.«tactic#count_heartbeats!_In__»`

`#count_heartbeats tac` counts the heartbeats used by the tactic sequence `tac`
and prints an info line with the number of heartbeats.

* `#count_heartbeats! n in tac`, where `n` is an optional natural number literal, runs `tac`
  `n` times on the same goal while counting the heartbeats, and prints an info line with range and
  standard deviation. `n` can be left out, and defaults to 10.

Example:

```
example : 1 + 1 = 2 := by
  -- The next line will print an info message of this format; the exact number may vary.
  -- info: 4646
  #count_heartbeats simp

example : 1 + 1 = 2 := by
  -- The next line will print an info message of this format; the exact numbers may vary.
  -- info: Min: 4 Max: 4 StdDev: 2%
  #count_heartbeats! 37 in simp
```

## \#defeq_abuse
Defined in: `Mathlib.Tactic.DefEqAbuse.defeqAbuse`

> **WARNING:** `#defeq_abuse` is an experimental tool intended to assist with breaking
changes to transparency handling. Its syntax may change at any time, and it may not behave as
expected. Please report unexpected behavior [on Zulip](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/backward.2EisDefEq.2ErespectTransparency/with/575685551).

`#defeq_abuse in tac` runs `tac` with `backward.isDefEq.respectTransparency` both `true` and
`false`. If the tactic succeeds with `false` but fails with `true`, it identifies the specific
`isDefEq` checks that fail with the stricter setting.

The tactic still executes (using the permissive setting if needed), so proofs remain valid
during debugging.

## \#find
Defined in: `Mathlib.Tactic.Find.«tactic#find_»`

`#find t` finds definitions and theorems whose result type matches the term `t`, and prints them as
info lines. Use holes in `t` to indicate arbitrary subexpressions, for example `#find _ ∧ _` will
match any conjunction. `#find` is also available as a command.
`#find` will not affect the goal by itself and should be removed from the finished proof.

There is also the `find` tactic which looks for lemmas which are `apply`able against the current
goal.

Examples:
```lean
#find _ + _ = _ + _
#find ?n + _ = _ + ?n
#find (_ : Nat) + _ = _ + _
#find Nat → Nat
```

## \#leansearch
Defined in: `LeanSearchClient.leansearch_search_tactic`

Search [LeanSearch](https://leansearch.net/) from within Lean.
Queries should be a string that ends with a `.` or `?`. This works as a command, as a term
and as a tactic as in the following examples. In tactic mode, only valid tactics are displayed.

```lean
#leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m."

example := #leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m."

example : 3 ≤ 5 := by
  #leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m."
  sorry
```

You can modify the LeanSearch URL by setting the `LEANSEARCHCLIENT_LEANSEARCH_API_URL` environment variable.

## \#loogle
Defined in: `LeanSearchClient.loogle_tactic`

Search [Loogle](https://loogle.lean-lang.org/json) from within Lean. This can be used as a command, term or tactic as in the following examples. In the case of a tactic, only valid tactics are displayed.


```lean
#loogle List ?a → ?a

example := #loogle List ?a → ?a

example : 3 ≤ 5 := by
  #loogle Nat.succ_le_succ
  sorry

```

## Loogle Usage

Loogle finds definitions and lemmas in various ways:

By constant:
🔍 Real.sin
finds all lemmas whose statement somehow mentions the sine function.

By lemma name substring:
🔍 \"differ\"
finds all lemmas that have \"differ\" somewhere in their lemma name.

By subexpression:
🔍 _ * (_ ^ _)
finds all lemmas whose statements somewhere include a product where the second argument is raised to some power.

The pattern can also be non-linear, as in
🔍 Real.sqrt ?a * Real.sqrt ?a

If the pattern has parameters, they are matched in any order. Both of these will find List.map:
🔍 (?a -> ?b) -> List ?a -> List ?b
🔍 List ?a -> (?a -> ?b) -> List ?b

By main conclusion:
🔍 |- tsum _ = _ * tsum _
finds all lemmas where the conclusion (the subexpression to the right of all → and ∀) has the given shape.

As before, if the pattern has parameters, they are matched against the hypotheses of the lemma in any order; for example,
🔍 |- _ < _ → tsum _ < tsum _
will find tsum_lt_tsum even though the hypothesis f i < g i is not the last.

If you pass more than one such search filter, separated by commas Loogle will return lemmas which match all of them. The search
🔍 Real.sin, \"two\", tsum, _ * _, _ ^ _, |- _ < _ → _
would find all lemmas which mention the constants Real.sin and tsum, have \"two\" as a substring of the lemma name, include a product and a power somewhere in the type, and have a hypothesis of the form _ < _ (if there were any such lemmas). Metavariables (?a) are assigned independently in each filter.

You can modify the Loogle server URL by setting the `LEANSEARCHCLIENT_LOOGLE_API_URL` environment variable.

## \#loogle
Defined in: `LeanSearchClient.just_loogle_tactic`


## \#search
Defined in: `LeanSearchClient.search_tactic`

Search from within Lean, depending on the option `leansearchclient.backend` (currently only leansearch).
Queries should be a string that ends with a `.` or `?`. This works as a command, as a term
and as a tactic as in the following examples. In tactic mode, only valid tactics are displayed.

```lean
#search "If a natural number n is less than m, then the successor of n is less than the successor of m."

example := #search "If a natural number n is less than m, then the successor of n is less than the successor of m."

example : 3 ≤ 5 := by
  #search "If a natural number n is less than m, then the successor of n is less than the successor of m."
  sorry

In tactic mode, if the query string is not supplied, then [LeanStateSearch](https://premise-search.com) is queried based on the goal state.
```lean

## \#statesearch
Defined in: `LeanSearchClient.statesearch_search_tactic`

Search [LeanStateSearch](https://premise-search.com) from within Lean.
Your current main goal is sent as query. The revision to search can be set
using the `statesearch.revision` option. The number of results can be set
using the `statesearch.queries` option.

Hint: If you want to modify the query, you need to use the web interface.

```lean
set_option statesearch.queries 1
set_option statesearch.revision "v4.16.0"

example : 0 ≤ 1 := by
  #statesearch
  sorry
```

You can modify the LeanStateSearch URL by setting the `LEANSEARCHCLIENT_LEANSTATESEARCH_API_URL` environment variable.

## (
Defined in: `Lean.Parser.Tactic.paren`

`(tacs)` executes a list of tactics in sequence, without requiring that
the goal be closed at the end like `· tacs`. Like `by` itself, the tactics
can be either separated by newlines or `;`.

syntax ..."<;>"... [Batteries.Tactic.seq_focus]
`t <;> [t1; t2; ...; tn]` focuses on the first goal and applies `t`, which should result in `n`
subgoals. It then applies each `ti` to the corresponding goal and collects the resulting
subgoals.

syntax ..."<;>"... [Lean.Parser.Tactic.«tactic_<;>_»]
`tac <;> tac'` runs `tac` on the main goal and `tac'` on each produced goal,
concatenating all goals produced by `tac'`.

## _
Defined in: `Batteries.Tactic.tactic_`

`_` in tactic position acts like the `done` tactic: it fails and gives the list
of goals if there are any. It is useful as a placeholder after starting a tactic block
such as `by _` to make it syntactically correct and show the current goal.

## abel
Defined in: `Mathlib.Tactic.Abel.abel`

`abel` solves equations in the language of *additive*, commutative monoids and groups.

`abel` and its variants work as both tactics and conv tactics.

* `abel1` fails if the target is not an equality that is provable by the axioms of
  commutative monoids/groups.
* `abel_nf` rewrites all group expressions into a normal form.
  * `abel_nf at h` rewrites in a hypothesis.
  * `abel_nf (config := cfg)` allows for additional configuration:
    * `red`: the reducibility setting (overridden by `!`).
    * `zetaDelta`: if true, local `let` variables can be unfolded (overridden by `!`).
    * `recursive`: if true, `abel_nf` also recurses into atoms.
* `abel!`, `abel1!`, `abel_nf!` use a more aggressive reducibility setting to identify atoms.

Examples:
```lean
example [AddCommMonoid α] (a b : α) : a + (b + a) = a + a + b := by abel
example [AddCommGroup α] (a : α) : (3 : ℤ) • a = a + (2 : ℤ) • a := by abel
```

## abel!
Defined in: `Mathlib.Tactic.Abel.tacticAbel!`

`abel` solves equations in the language of *additive*, commutative monoids and groups.

`abel` and its variants work as both tactics and conv tactics.

* `abel1` fails if the target is not an equality that is provable by the axioms of
  commutative monoids/groups.
* `abel_nf` rewrites all group expressions into a normal form.
  * `abel_nf at h` rewrites in a hypothesis.
  * `abel_nf (config := cfg)` allows for additional configuration:
    * `red`: the reducibility setting (overridden by `!`).
    * `zetaDelta`: if true, local `let` variables can be unfolded (overridden by `!`).
    * `recursive`: if true, `abel_nf` also recurses into atoms.
* `abel!`, `abel1!`, `abel_nf!` use a more aggressive reducibility setting to identify atoms.

Examples:
```lean
example [AddCommMonoid α] (a b : α) : a + (b + a) = a + a + b := by abel
example [AddCommGroup α] (a : α) : (3 : ℤ) • a = a + (2 : ℤ) • a := by abel
```

## abel1
Defined in: `Mathlib.Tactic.Abel.abel1`

`abel` solves equations in the language of *additive*, commutative monoids and groups.

`abel` and its variants work as both tactics and conv tactics.

* `abel1` fails if the target is not an equality that is provable by the axioms of
  commutative monoids/groups.
* `abel_nf` rewrites all group expressions into a normal form.
  * `abel_nf at h` rewrites in a hypothesis.
  * `abel_nf (config := cfg)` allows for additional configuration:
    * `red`: the reducibility setting (overridden by `!`).
    * `zetaDelta`: if true, local `let` variables can be unfolded (overridden by `!`).
    * `recursive`: if true, `abel_nf` also recurses into atoms.
* `abel!`, `abel1!`, `abel_nf!` use a more aggressive reducibility setting to identify atoms.

Examples:
```lean
example [AddCommMonoid α] (a b : α) : a + (b + a) = a + a + b := by abel
example [AddCommGroup α] (a : α) : (3 : ℤ) • a = a + (2 : ℤ) • a := by abel
```

## abel1!
Defined in: `Mathlib.Tactic.Abel.abel1!`

`abel` solves equations in the language of *additive*, commutative monoids and groups.

`abel` and its variants work as both tactics and conv tactics.

* `abel1` fails if the target is not an equality that is provable by the axioms of
  commutative monoids/groups.
* `abel_nf` rewrites all group expressions into a normal form.
  * `abel_nf at h` rewrites in a hypothesis.
  * `abel_nf (config := cfg)` allows for additional configuration:
    * `red`: the reducibility setting (overridden by `!`).
    * `zetaDelta`: if true, local `let` variables can be unfolded (overridden by `!`).
    * `recursive`: if true, `abel_nf` also recurses into atoms.
* `abel!`, `abel1!`, `abel_nf!` use a more aggressive reducibility setting to identify atoms.

Examples:
```lean
example [AddCommMonoid α] (a b : α) : a + (b + a) = a + a + b := by abel
example [AddCommGroup α] (a : α) : (3 : ℤ) • a = a + (2 : ℤ) • a := by abel
```

## abel_nf
Defined in: `Mathlib.Tactic.Abel.abelNF`

`abel` solves equations in the language of *additive*, commutative monoids and groups.

`abel` and its variants work as both tactics and conv tactics.

* `abel1` fails if the target is not an equality that is provable by the axioms of
  commutative monoids/groups.
* `abel_nf` rewrites all group expressions into a normal form.
  * `abel_nf at h` rewrites in a hypothesis.
  * `abel_nf (config := cfg)` allows for additional configuration:
    * `red`: the reducibility setting (overridden by `!`).
    * `zetaDelta`: if true, local `let` variables can be unfolded (overridden by `!`).
    * `recursive`: if true, `abel_nf` also recurses into atoms.
* `abel!`, `abel1!`, `abel_nf!` use a more aggressive reducibility setting to identify atoms.

Examples:
```lean
example [AddCommMonoid α] (a b : α) : a + (b + a) = a + a + b := by abel
example [AddCommGroup α] (a : α) : (3 : ℤ) • a = a + (2 : ℤ) • a := by abel
```

## abel_nf!
Defined in: `Mathlib.Tactic.Abel.tacticAbel_nf!__`

`abel` solves equations in the language of *additive*, commutative monoids and groups.

`abel` and its variants work as both tactics and conv tactics.

* `abel1` fails if the target is not an equality that is provable by the axioms of
  commutative monoids/groups.
* `abel_nf` rewrites all group expressions into a normal form.
  * `abel_nf at h` rewrites in a hypothesis.
  * `abel_nf (config := cfg)` allows for additional configuration:
    * `red`: the reducibility setting (overridden by `!`).
    * `zetaDelta`: if true, local `let` variables can be unfolded (overridden by `!`).
    * `recursive`: if true, `abel_nf` also recurses into atoms.
* `abel!`, `abel1!`, `abel_nf!` use a more aggressive reducibility setting to identify atoms.

Examples:
```lean
example [AddCommMonoid α] (a b : α) : a + (b + a) = a + a + b := by abel
example [AddCommGroup α] (a : α) : (3 : ℤ) • a = a + (2 : ℤ) • a := by abel
```

## absurd
Defined in: `Batteries.Tactic.tacticAbsurd_`

Given a proof `h` of `p`, `absurd h` changes the goal to `⊢ ¬ p`.
If `p` is a negation `¬q` then the goal is changed to `⊢ q` instead.

## ac_change
Defined in: `Mathlib.Tactic.acChange`

`ac_change t` on a goal `⊢ t'` changes the goal to `⊢ t` and adds new goals for proving the equality
`t' = t` using congruence, then tries proving these goals by associativity and commutativity. The
goals are created like `congr!` would.
In other words, `ac_change t` is like `convert_to t` followed by `ac_refl`.

Like `refine e`, any holes (`?_` or `?x`) in `t` that are not solved by unification are converted
into new goals, using the hole's name, if any, as the goal case name.
Like `congr!`, `convert_to` introduces variables while applying congruence rules. These can be
pattern-matched, like `rintro` would, using the `with` keyword.

* `ac_change t using n`, where `n` is a positive numeral, controls the depth with which congruence
  is applied. For example, if the main goal is `⊢ Prime ((a * b + 1) + c)`,
  then `ac_change Prime ((1 + a * b) + c) using 2` solves the side goals, and
  `ac_change Prime ((1 + a * b) + c) using 3` (or more) results in two (impossible) goals
  `⊢ 1 = a * b` and `⊢ a * b = 1`.
  The default value for `n` is 1.

Example:
```lean
example (a b c d e f g N : ℕ) : (a + b) + (c + d) + (e + f) + g ≤ N := by
  ac_change a + d + e + f + c + g + b ≤ _
  -- ⊢ a + d + e + f + c + g + b ≤ N
```

## ac_nf
Defined in: `Lean.Parser.Tactic.tacticAc_nf_`

`ac_nf` normalizes equalities up to application of an associative and commutative operator.
- `ac_nf` normalizes all hypotheses and the goal target of the goal.
- `ac_nf at l` normalizes at location(s) `l`, where `l` is either `*` or a
  list of hypotheses in the local context. In the latter case, a turnstile `⊢` or `|-`
  can also be used, to signify the target of the goal.
```lean
instance : Std.Associative (α := Nat) (.+.) := ⟨Nat.add_assoc⟩
instance : Std.Commutative (α := Nat) (.+.) := ⟨Nat.add_comm⟩

example (a b c d : Nat) : a + b + c + d = d + (b + c) + a := by
 ac_nf
 -- goal: a + (b + (c + d)) = a + (b + (c + d))
```

## ac_nf0
Defined in: `Lean.Parser.Tactic.acNf0`

Implementation of `ac_nf` (the full `ac_nf` calls `trivial` afterwards).

## ac_rfl
Defined in: `Lean.Parser.Tactic.acRfl`

`ac_rfl` proves equalities up to application of an associative and commutative operator.
```lean
instance : Std.Associative (α := Nat) (.+.) := ⟨Nat.add_assoc⟩
instance : Std.Commutative (α := Nat) (.+.) := ⟨Nat.add_comm⟩

example (a b c d : Nat) : a + b + c + d = d + (b + c) + a := by ac_rfl
```

## admit
Defined in: `Lean.Parser.Tactic.tacticAdmit`

`admit` is a synonym for `sorry`.

## aesop
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

## aesop?
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

## aesop_cat
Defined in: `CategoryTheory.aesop_cat`

A thin wrapper for `aesop` which adds the `CategoryTheory` rule set and
allows `aesop` to look through semireducible definitions when calling `intros`.
This tactic fails when it is unable to solve the goal, making it suitable for
use in auto-params.

## aesop_cat?
Defined in: `CategoryTheory.aesop_cat?`

We also use `aesop_cat?` to pass along a `Try this` suggestion when using `aesop_cat`

## aesop_cat_nonterminal
Defined in: `CategoryTheory.aesop_cat_nonterminal`

A variant of `aesop_cat` which does not fail when it is unable to solve the
goal. Use this only for exploration! Nonterminal `aesop` is even worse than
nonterminal `simp`.

## aesop_graph
Defined in: `aesop_graph`

A variant of the `aesop` tactic for use in the graph library. Changes relative
to standard `aesop`:

- We use the `SimpleGraph` rule set in addition to the default rule sets.
- We instruct Aesop's `intro` rule to unfold with `default` transparency.
- We instruct Aesop to fail if it can't fully solve the goal. This allows us to
  use `aesop_graph` for auto-params.

## aesop_graph?
Defined in: `aesop_graph?`

Use `aesop_graph?` to pass along a `Try this` suggestion when using `aesop_graph`

## aesop_graph_nonterminal
Defined in: `aesop_graph_nonterminal`

A variant of `aesop_graph` which does not fail if it is unable to solve the goal.
Use this only for exploration! Nonterminal Aesop is even worse than nonterminal `simp`.

## aesop_mat
Defined in: `Matroid.aesop_mat`

The `aesop_mat` tactic attempts to prove a set is contained in the ground set of a matroid.
It uses a `[Matroid]` ruleset, and is allowed to fail.

## aesop_unfold
Defined in: `Aesop.tacticAesop_unfold_`


## aesop_unfold
Defined in: `Aesop.tacticAesop_unfold_At_`


## algebraize
Defined in: `Mathlib.Tactic.tacticAlgebraize__`

Tactic that, given `RingHom`s, adds the corresponding `Algebra` and (if possible)
`IsScalarTower` instances, as well as `Algebra` corresponding to `RingHom` properties available
as hypotheses.

Example: given `f : A →+* B` and `g : B →+* C`, and `hf : f.FiniteType`, `algebraize [f, g]` will
add the instances `Algebra A B`, `Algebra B C`, and `Algebra.FiniteType A B`.

See the `algebraize` tag for instructions on what properties can be added.

The tactic also comes with a configuration option `properties`. If set to `true` (default), the
tactic searches through the local context for `RingHom` properties that can be converted to
`Algebra` properties. The macro `algebraize_only` calls
`algebraize -properties`,
so in other words it only adds `Algebra` and `IsScalarTower` instances.

## algebraize_only
Defined in: `Mathlib.Tactic.tacticAlgebraize_only__`

Version of `algebraize`, which only adds `Algebra` instances and `IsScalarTower` instances,
but does not try to add any instances about any properties tagged with
`@[algebraize]`, like for example `Finite` or `IsIntegral`.

## all_goals
Defined in: `Lean.Parser.Tactic.allGoals`

`all_goals tac` runs `tac` on each goal, concatenating the resulting goals.
If the tactic fails on any goal, the entire `all_goals` tactic fails.

See also `any_goals tac`.

## and_intros
Defined in: `Lean.Parser.Tactic.tacticAnd_intros`

`and_intros` applies `And.intro` until it does not make progress.

## any_goals
Defined in: `Lean.Parser.Tactic.anyGoals`

`any_goals tac` applies the tactic `tac` to every goal,
concatenating the resulting goals for successful tactic applications.
If the tactic fails on all of the goals, the entire `any_goals` tactic fails.

This tactic is like `all_goals try tac` except that it fails if none of the applications of `tac` succeeds.

## apply
Defined in: `Mathlib.Tactic.tacticApply_At_`

`apply t at i` uses forward reasoning with `t` at the hypothesis `i`.
Explicitly, if `t : α₁ → ⋯ → αᵢ → ⋯ → αₙ` and `i` has type `αᵢ`, then this tactic adds
metavariables/goals for any terms of `αⱼ` for `j = 1, …, i-1`,
then replaces the type of `i` with `αᵢ₊₁ → ⋯ → αₙ` by applying those metavariables and the
original `i`.

## apply
Defined in: `Lean.Parser.Tactic.apply`

`apply e` tries to match the current goal against the conclusion of `e`'s type.
If it succeeds, then the tactic returns as many subgoals as the number of premises that
have not been fixed by type inference or type class resolution.
Non-dependent premises are added before dependent ones.

The `apply` tactic uses higher-order pattern matching, type class resolution,
and first-order unification with dependent types.


Extensions:

 * * `apply (config := cfg) e` allows for additional configuration (see `Lean.Meta.ApplyConfig`):
     * `newGoals` controls which new goals are added by `apply`, in which order.
     * `-synthAssignedInstances` will not synthesize instance implicit arguments if they have been
       assigned by `isDefEq`.
     * `+allowSynthFailures` will create new goals when instance synthesis fails, rather than erroring.
     * `+approx` enables `isDefEq` approximations (see `Lean.Meta.approxDefEq`).

## apply
Defined in: `Mathlib.Tactic.applyWith`

`apply e` tries to match the current goal against the conclusion of `e`'s type.
If it succeeds, then the tactic returns as many subgoals as the number of premises that
have not been fixed by type inference or type class resolution.
Non-dependent premises are added before dependent ones.

The `apply` tactic uses higher-order pattern matching, type class resolution,
and first-order unification with dependent types.


Extensions:

 * * `apply (config := cfg) e` allows for additional configuration (see `Lean.Meta.ApplyConfig`):
     * `newGoals` controls which new goals are added by `apply`, in which order.
     * `-synthAssignedInstances` will not synthesize instance implicit arguments if they have been
       assigned by `isDefEq`.
     * `+allowSynthFailures` will create new goals when instance synthesis fails, rather than erroring.
     * `+approx` enables `isDefEq` approximations (see `Lean.Meta.approxDefEq`).

## apply?
Defined in: `Lean.Parser.Tactic.apply?`

Searches environment for definitions or theorems that can refine the goal using `apply`
with conditions resolved when possible with `solve_by_elim`.

The optional `using` clause provides identifiers in the local context that must be
used when closing the goal.

Use `+grind` to enable `grind` as a fallback discharger for subgoals.
Use `+try?` to enable `try?` as a fallback discharger for subgoals.
Use `-star` to disable fallback to star-indexed lemmas.
Use `+all` to collect all successful lemmas instead of stopping at the first.

## apply_assumption
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

## apply_ext_theorem
Defined in: `Lean.Elab.Tactic.Ext.applyExtTheorem`

Apply a single extensionality theorem to the current goal.

## apply_fun
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
  intro x x' h
  apply_fun g at h
  exact H h
```

The function `f` is handled similarly to how it would be handled by `refine` in that `f` can contain
placeholders. Named placeholders (like `?a` or `?_`) will produce new goals.

## apply_gmonoid_gnpowRec_succ_tac
Defined in: `GradedMonoid.tacticApply_gmonoid_gnpowRec_succ_tac`

A tactic to for use as an optional value for `GMonoid.gnpow_succ'`.

## apply_gmonoid_gnpowRec_zero_tac
Defined in: `GradedMonoid.tacticApply_gmonoid_gnpowRec_zero_tac`

A tactic to for use as an optional value for `GMonoid.gnpow_zero'`.

## apply_mod_cast
Defined in: `Lean.Parser.Tactic.tacticApply_mod_cast_`

Normalize casts in the goal and the given expression, then `apply` the expression to the goal.

## apply_rewrite
Defined in: `Mathlib.Tactic.tacticApply_rewrite___`

`apply_rewrite [rules]` is a shorthand for `grewrite +implicationHyp [rules]`.

## apply_rfl
Defined in: `Lean.Parser.Tactic.applyRfl`

The same as `rfl`, but without trying `eq_refl` at the end.

## apply_rules
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

## apply_rw
Defined in: `Mathlib.Tactic.applyRwSeq`

`apply_rw [rules]` is a shorthand for `grw +implicationHyp [rules]`.

## arith_mult
Defined in: `ArithmeticFunction.arith_mult`

`arith_mult` solves goals of the form `IsMultiplicative f` for `f : ArithmeticFunction R`
by applying lemmas tagged with the user attribute `arith_mult`.

## arith_mult?
Defined in: `ArithmeticFunction.arith_mult?`

`arith_mult` solves goals of the form `IsMultiplicative f` for `f : ArithmeticFunction R`
by applying lemmas tagged with the user attribute `arith_mult`, and prints out the generated
proof term.

## array_get_dec
Defined in: `Array.tacticArray_get_dec`

This tactic, added to the `decreasing_trivial` toolbox, proves that
`sizeOf arr[i] < sizeOf arr`, which is useful for well founded recursions
over a nested inductive like `inductive T | mk : Array T → T`.

## array_mem_dec
Defined in: `Array.tacticArray_mem_dec`

This tactic, added to the `decreasing_trivial` toolbox, proves that `sizeOf a < sizeOf arr`
provided that `a ∈ arr` which is useful for well founded recursions over a nested inductive like
`inductive T | mk : Array T → T`.

## as_aux_lemma
Defined in: `Lean.Parser.Tactic.as_aux_lemma`

`as_aux_lemma => tac` does the same as `tac`, except that it wraps the resulting expression
into an auxiliary lemma. In some cases, this significantly reduces the size of expressions
because the proof term is not duplicated.

## assumption
Defined in: `Lean.Parser.Tactic.assumption`

`assumption` tries to solve the main goal using a hypothesis of compatible type, or else fails.
Note also the `‹t›` term notation, which is a shorthand for `show t by assumption`.

## assumption'
Defined in: `Mathlib.Tactic.tacticAssumption'`

Try calling `assumption` on all goals; succeeds if it closes at least one goal.

## assumption_mod_cast
Defined in: `Lean.Parser.Tactic.tacticAssumption_mod_cast_`

`assumption_mod_cast` is a variant of `assumption` that solves the goal
using a hypothesis. Unlike `assumption`, it first pre-processes the goal and
each hypothesis to move casts as far outwards as possible, so it can be used
in more situations.

Concretely, it runs `norm_cast` on the goal. For each local hypothesis `h`, it also
normalizes `h` with `norm_cast` and tries to use that to close the goal.

## attempt_all
Defined in: `Lean.Parser.Tactic.attemptAll`

Helper internal tactic for implementing the tactic `try?`.

## attempt_all_par
Defined in: `Lean.Parser.Tactic.attemptAllPar`

Helper internal tactic for implementing the tactic `try?` with parallel execution.

## aux_group₁
Defined in: `Mathlib.Tactic.Group.aux_group₁`

Auxiliary tactic for the `group` tactic. Calls the simplifier only.

## aux_group₂
Defined in: `Mathlib.Tactic.Group.aux_group₂`

Auxiliary tactic for the `group` tactic. Calls `ring_nf` to normalize exponents.

## bddDefault
Defined in: `tacticBddDefault`

Sets are automatically bounded or cobounded in complete lattices. To use the same statements
in complete and conditionally complete lattices but let automation fill automatically the
boundedness proofs in complete lattices, we use the tactic `bddDefault` in the statements,
in the form `(hA : BddAbove A := by bddDefault)`.

## beta_reduce
Defined in: `Mathlib.Tactic.betaReduceStx`

`beta_reduce at loc` completely beta reduces the given location.
This also exists as a `conv`-mode tactic.

This means that whenever there is an applied lambda expression such as
`(fun x => f x) y` then the argument is substituted into the lambda expression
yielding an expression such as `f y`.

## bicategory
Defined in: `Mathlib.Tactic.Bicategory.tacticBicategory`

Use the coherence theorem for bicategories to solve equations in a bicategory,
where the two sides only differ by replacing strings of bicategory structural morphisms
(that is, associators, unitors, and identities)
with different strings of structural morphisms with the same source and target.

That is, `bicategory` can handle goals of the form
`a ≫ f ≫ b ≫ g ≫ c = a' ≫ f ≫ b' ≫ g ≫ c'`
where `a = a'`, `b = b'`, and `c = c'` can be proved using `bicategory_coherence`.

## bicategory_coherence
Defined in: `Mathlib.Tactic.Bicategory.tacticBicategory_coherence`

Close the goal of the form `η.hom = θ.hom`, where `η` and `θ` are 2-isomorphisms made up only of
associators, unitors, and identities.
```lean
example {B : Type} [Bicategory B] {a : B} :
  (λ_ (𝟙 a)).hom = (ρ_ (𝟙 a)).hom := by
  bicategory_coherence
```

## bicategory_nf
Defined in: `Mathlib.Tactic.Bicategory.tacticBicategory_nf`

Normalize the both sides of an equality.

## bitwise_assoc_tac
Defined in: `Nat.tacticBitwise_assoc_tac`

Proving associativity of bitwise operations in general essentially boils down to a huge case
distinction, so it is shorter to use this tactic instead of proving it in the general case.

## borelize
Defined in: `Mathlib.Tactic.Borelize.tacticBorelize___`

The behaviour of `borelize α` depends on the existing assumptions on `α`.

- if `α` is a topological space with instances `[MeasurableSpace α] [BorelSpace α]`, then
  `borelize α` replaces the former instance by `borel α`;
- otherwise, `borelize α` adds instances `borel α : MeasurableSpace α` and `⟨rfl⟩ : BorelSpace α`.

Finally, `borelize α β γ` runs `borelize α; borelize β; borelize γ`.

## bound
Defined in: `«tacticBound[_]»`

`bound` tactic for proving inequalities via straightforward recursion on expression structure.

An example use case is

```
-- Calc example: A weak lower bound for `z ↦ z^2 + c`
lemma le_sqr_add (c z : ℝ) (cz : ‖c‖ ≤ ‖z‖) (z3 : 3 ≤ ‖z‖) :
    2 * ‖z‖ ≤ ‖z^2 + c‖ := by
  calc ‖z^2 + c‖
    _ ≥ ‖z^2‖ - ‖c‖ := by bound
    _ ≥ ‖z^2‖ - ‖z‖ := by  bound
    _ ≥ (‖z‖ - 1) * ‖z‖ := by
      rw [mul_comm, mul_sub_one, ← pow_two, ← norm_pow]
    _ ≥ 2 * ‖z‖ := by bound
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

## bv_check
Defined in: `Lean.Parser.Tactic.bvCheck`

This tactic works just like `bv_decide` but skips calling a SAT solver by using a proof that is
already stored on disk. It is called with the name of an LRAT file in the same directory as the
current Lean file:
```lean
bv_check "proof.lrat"
```

## bv_decide
Defined in: `Lean.Parser.Tactic.bvDecide`

Close fixed-width `BitVec` and `Bool` goals by obtaining a proof from an external SAT solver and
verifying it inside Lean. The solvable goals are currently limited to
- the Lean equivalent of [`QF_BV`](https://smt-lib.org/logics-all.shtml#QF_BV)
- automatically splitting up `structure`s that contain information about `BitVec` or `Bool`
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

If solving your problem relies inherently on using associativity or commutativity, consider enabling
the `bv.ac_nf` option.

Note: `bv_decide` trusts the correctness of the code generator and adds a axioms asserting its result.

Note: include `import Std.Tactic.BVDecide`

## bv_decide
Defined in: `Lean.Parser.Tactic.bvDecideMacro`

Close fixed-width `BitVec` and `Bool` goals by obtaining a proof from an external SAT solver and
verifying it inside Lean. The solvable goals are currently limited to
- the Lean equivalent of [`QF_BV`](https://smt-lib.org/logics-all.shtml#QF_BV)
- automatically splitting up `structure`s that contain information about `BitVec` or `Bool`
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

If solving your problem relies inherently on using associativity or commutativity, consider enabling
the `bv.ac_nf` option.

Note: `bv_decide` trusts the correctness of the code generator and adds a axioms asserting its result.

Note: include `import Std.Tactic.BVDecide`

## bv_decide?
Defined in: `Lean.Parser.Tactic.bvTraceMacro`

Suggest a proof script for a `bv_decide` tactic call. Useful for caching LRAT proofs.

Note: include `import Std.Tactic.BVDecide`

## bv_decide?
Defined in: `Lean.Parser.Tactic.bvTrace`

Suggest a proof script for a `bv_decide` tactic call. Useful for caching LRAT proofs.

Note: include `import Std.Tactic.BVDecide`

## bv_normalize
Defined in: `Lean.Parser.Tactic.bvNormalize`

Run the normalization procedure of `bv_decide` only. Sometimes this is enough to solve basic
`BitVec` goals already.

Note: include `import Std.Tactic.BVDecide`

## bv_normalize
Defined in: `Lean.Parser.Tactic.bvNormalizeMacro`

Run the normalization procedure of `bv_decide` only. Sometimes this is enough to solve basic
`BitVec` goals already.

Note: include `import Std.Tactic.BVDecide`

## bv_omega
Defined in: `Lean.Parser.Tactic.tacticBv_omega`

`bv_omega` is `omega` with an additional preprocessor that turns statements about `BitVec` into statements about `Nat`.
Currently the preprocessor is implemented as `try simp only [bitvec_to_nat] at *`.
`bitvec_to_nat` is a `@[simp]` attribute that you can (cautiously) add to more theorems.

## by_cases
Defined in: `«tacticBy_cases_:_»`

`by_cases (h :)? p` splits the main goal into two cases, assuming `h : p` in the first branch, and `h : ¬ p` in the second branch.

## by_cases!
Defined in: `Mathlib.Tactic.ByCases.byCases!`

`by_cases! h : p` runs the `by_cases h : p` tactic, followed by
`push Not at h` in the second subgoal. For example,
- `by_cases! h : a < b` creates one goal with hypothesis `h : a < b` and
  another with `h : b ≤ a`.
- `by_cases! h : a ≠ b` creates one goal with hypothesis `h : a ≠ b` and
  another with `h : a = b`.

## by_contra
Defined in: `Batteries.Tactic.byContra`

`by_contra h` proves `⊢ p` by contradiction,
introducing a hypothesis `h : ¬p` and proving `False`.
* If `p` is a negation `¬q`, `h : q` will be introduced instead of `¬¬q`.
* If `p` is decidable, it uses `Decidable.byContradiction` instead of `Classical.byContradiction`.
* If `h` is omitted, the introduced variable will be called `this`.

## by_contra!
Defined in: `Mathlib.Tactic.ByContra.byContra!`

If the target of the main goal is a proposition `p`,
`by_contra!` reduces the goal to proving `False` using the additional hypothesis `this : ¬ p`.
`by_contra! h` can be used to name the hypothesis `h : ¬ p`.
The hypothesis `¬ p` will be normalized using `push Not`.
For instance, `¬ a < b` will be changed to `b ≤ a`.
`by_contra!` can be used with `rcases` patterns.
For instance, `by_contra! rfl` on `⊢ s.Nonempty` will substitute the equality `s = ∅`,
and `by_contra! ⟨hp, hq⟩` on `⊢ ¬ p ∨ ¬ q` will introduce `hp : p` and `hq : q`.
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

## calc
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
<proof>`. This is useful for aligning relation symbols, especially on longer
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

## calc?
Defined in: `Lean.Elab.Tactic.tacticCalc?`

Create a `calc` proof.

## cancel_denoms
Defined in: `Mathlib.Tactic.cancelDenoms`

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

## cancel_denoms
Defined in: `Mathlib.Tactic.tacticCancel_denoms_`

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

## case
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

## case
Defined in: `Lean.Parser.Tactic.case`

* `case tag => tac` focuses on the goal with case name `tag` and solves it using `tac`,
  or else fails.
* `case tag x₁ ... xₙ => tac` additionally renames the `n` most recent hypotheses
  with inaccessible names to the given names.
* `case tag₁ | tag₂ => tac` is equivalent to `(case tag₁ => tac); (case tag₂ => tac)`.

## case'
Defined in: `Lean.Parser.Tactic.case'`

`case'` is similar to the `case tag => tac` tactic, but does not ensure the goal
has been solved after applying `tac`, nor admits the goal if `tac` failed.
Recall that `case` closes the goal using `sorry` when `tac` fails, and
the tactic execution is not interrupted.

## case'
Defined in: `Batteries.Tactic.casePatt'`

`case' _ : t => tac` is similar to the `case _ : t => tac` tactic,
but it does not ensure the goal has been solved after applying `tac`,
nor does it admit the goal if `tac` failed.
Recall that `case` closes the goal using `sorry` when `tac` fails,
and the tactic execution is not interrupted.

## cases
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
  performs cases on `e` as above, but also adds a hypothesis `h : e = ...` to each goal,
  where `...` is the constructor instance for that particular case.

## cases'
Defined in: `Mathlib.Tactic.cases'`

`cases' x`, where the variable `x` has inductive type `t`, splits the main goal,
producing one goal for each constructor of `t`, in which `x` is replaced by that constructor
applied to newly introduced variables. This is a backwards-compatible variant of the
`cases` tactic in Lean 4 core.

Prefer `cases`, `rcases`, or `obtain` when possible, because these tactics promote
structured proofs.

* `cases' x with n1 n2 ...` names the arguments to the constructors. This is the main difference
  with `cases` in core Lean.
* `cases' e`, where `e` is an expression instead of a variable, generalizes `e` in the goal,
  and then performs induction on the resulting variable.
* `cases' h : e`, where `e` is an expression instead of a variable, generalizes `e` in the goal,
  and then splits by cases on the resulting variable, adding to each goal the hypothesis
  `h : e = _` where `_` is the constructor instance.
* `cases' x using r` uses `r` as the case matching rule. Here `r` should be a term whose result type
  is of the form `C t1 t2 ...`, where `C` is a bound variable and `t1`, `t2`, ... (if present) are
  bound variables.

Example:
```lean
example (h : p ∨ q) : q ∨ p := by
  cases' h with hp hq
  · exact Or.inr hp
  · exact Or.inl hq

-- Though the following equivalent spellings should be preferred
example (h : p ∨ q) : q ∨ p := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

example (h : p ∨ q) : q ∨ p := by
  rcases h with hp | hq
  · exact Or.inr hp
  · exact Or.inl hq
```

## cases_first_enat
Defined in: `Mathlib.Tactic.ENatToNat.tacticCases_first_enat`

Finds the first `ENat` in the context and applies the `cases` tactic to it.
Then simplifies expressions involving `⊤` using the `enat_to_nat_top` simp set.

## cases_type
Defined in: `Mathlib.Tactic.casesType`

`cases_type I` searches for a hypothesis `h : type` where `I` has the form `(I ...)`, and splits the
main goal by cases on `h`. `cases_type p` fails if no hypothesis type has the identifier `I` as its
head symbol.

* `cases_type I_1 ... I_n` searches for a hypothesis `h : type` where `type` has one or more of
  `I_1`, ..., `I_n` as its head symbol, and splits the main goal by cases on `h`.
* `cases_type* I` repeatedly performs case splits until no more hypothesis type has `I` as its head
  symbol. This shorthand for `· repeat cases_type I`.
* `cases_type! p` and `cases_type!* p` skip a hypothesis if the main goal would be replaced with two
  or more subgoals.

Example:
```lean
example (h : a ∧ b ∨ c ∧ d) (h2 : e ∧ f) : True := by
  -- The following tactic destructs all conjunctions and disjunctions in the current context.
  cases_type* Or And
  · clear ‹a› ‹b› ‹e› ‹f›; (fail_if_success clear ‹c›); trivial
  · clear ‹c› ‹d› ‹e› ‹f›; trivial
```

## cases_type!
Defined in: `Mathlib.Tactic.casesType!`

`cases_type I` searches for a hypothesis `h : type` where `I` has the form `(I ...)`, and splits the
main goal by cases on `h`. `cases_type p` fails if no hypothesis type has the identifier `I` as its
head symbol.

* `cases_type I_1 ... I_n` searches for a hypothesis `h : type` where `type` has one or more of
  `I_1`, ..., `I_n` as its head symbol, and splits the main goal by cases on `h`.
* `cases_type* I` repeatedly performs case splits until no more hypothesis type has `I` as its head
  symbol. This shorthand for `· repeat cases_type I`.
* `cases_type! p` and `cases_type!* p` skip a hypothesis if the main goal would be replaced with two
  or more subgoals.

Example:
```lean
example (h : a ∧ b ∨ c ∧ d) (h2 : e ∧ f) : True := by
  -- The following tactic destructs all conjunctions and disjunctions in the current context.
  cases_type* Or And
  · clear ‹a› ‹b› ‹e› ‹f›; (fail_if_success clear ‹c›); trivial
  · clear ‹c› ‹d› ‹e› ‹f›; trivial
```

## casesm
Defined in: `Mathlib.Tactic.casesM`

`casesm p` searches for the first hypothesis `h : type` where `type` matches the term `p`,
and splits the main goal by cases on `h`. Use holes in `p` to indicate arbitrary subexpressions,
for example `casesm _ ∧ _` will match any conjunction. `casesm p` fails if no hypothesis type
matches `p`.

* `casesm p_1, ..., p_n` searches for a hypothesis `h : type` where `type` matches one or more of
  the given patterns `p_1`, ... `p_n`, and splits the main goal by cases on `h`.
* `casesm* p` repeatedly performs case splits until no more hypothesis type matches `p`.
  This is a more efficient and compact version of `· repeat casesm p`.
  It is more efficient because the pattern is compiled once.
* `casesm! p` and `casesm!* p` skip a hypothesis if the main goal would be replaced with two or more
  subgoals.

Example:
```lean
example (h : a ∧ b ∨ c ∧ d) (h2 : e ∧ f) : True := by
  -- The following tactic destructs all conjunctions and disjunctions in the current context.
  casesm* _∨_, _∧_
  · clear ‹a› ‹b› ‹e› ‹f›; (fail_if_success clear ‹c›); trivial
  · clear ‹c› ‹d› ‹e› ‹f›; trivial
```

## casesm!
Defined in: `Mathlib.Tactic.casesm!`

`casesm p` searches for the first hypothesis `h : type` where `type` matches the term `p`,
and splits the main goal by cases on `h`. Use holes in `p` to indicate arbitrary subexpressions,
for example `casesm _ ∧ _` will match any conjunction. `casesm p` fails if no hypothesis type
matches `p`.

* `casesm p_1, ..., p_n` searches for a hypothesis `h : type` where `type` matches one or more of
  the given patterns `p_1`, ... `p_n`, and splits the main goal by cases on `h`.
* `casesm* p` repeatedly performs case splits until no more hypothesis type matches `p`.
  This is a more efficient and compact version of `· repeat casesm p`.
  It is more efficient because the pattern is compiled once.
* `casesm! p` and `casesm!* p` skip a hypothesis if the main goal would be replaced with two or more
  subgoals.

Example:
```lean
example (h : a ∧ b ∨ c ∧ d) (h2 : e ∧ f) : True := by
  -- The following tactic destructs all conjunctions and disjunctions in the current context.
  casesm* _∨_, _∧_
  · clear ‹a› ‹b› ‹e› ‹f›; (fail_if_success clear ‹c›); trivial
  · clear ‹c› ‹d› ‹e› ‹f›; trivial
```

## cat_disch
Defined in: `CategoryTheory.cat_disch`

A tactic for discharging easy category theory goals, widely used as an autoparameter.
Currently this defaults to the `aesop_cat` wrapper around `aesop`, but by setting
the option `mathlib.tactic.category.grind` to `true`, it will use the `grind` tactic instead.

## cbv
Defined in: `Lean.Parser.Tactic.cbv`

`cbv` performs simplification that closely mimics call-by-value evaluation.
It reduces terms by unfolding definitions using their defining equations and
applying matcher equations. The unfolding is propositional, so `cbv` also works
with functions defined via well-founded recursion or partial fixpoints.

`cbv` has built-in support for goals of the form `lhs = rhs`. It proceeds in
two passes:
1. Reduce `lhs`. If the result is definitionally equal to `rhs`, close the goal.
2. Otherwise, reduce `rhs`. If the result is now definitionally equal to the
   reduced `lhs`, close the goal.
3. If neither check succeeds, generate a new goal `lhs' = rhs'`, where `lhs'`
   and `rhs'` are the reduced forms of the original sides.

`cbv` is therefore not a finishing tactic in general: it may leave a new
(simpler) equality goal. For goals that are not equalities, `cbv` currently
leaves the goal unchanged.

The proofs produced by `cbv` only use the three standard axioms.
In particular, they do not require trust in the correctness of the code
generator.

This tactic is experimental and its behavior is likely to change in upcoming
releases of Lean.

## cfc_cont_tac
Defined in: `cfcContTac`

A tactic used to automatically discharge goals relating to the continuous functional calculus,
specifically concerning continuity of the functions involved.

## cfc_tac
Defined in: `cfcTac`

A tactic used to automatically discharge goals relating to the continuous functional calculus,
specifically whether the element satisfies the predicate.

## cfc_zero_tac
Defined in: `cfcZeroTac`

A tactic used to automatically discharge goals relating to the non-unital continuous functional
calculus, specifically concerning whether `f 0 = 0`.

## change
Defined in: `Lean.Parser.Tactic.change`

* `change tgt'` will change the goal from `tgt` to `tgt'`,
  assuming these are definitionally equal.
* `change t' at h` will change hypothesis `h : t` to have type `t'`, assuming
  assuming `t` and `t'` are definitionally equal.
* `change a with b` will change occurrences of `a` to `b` in the goal,
  assuming `a` and `b` are definitionally equal.
* `change a with b at h` similarly changes `a` to `b` in the type of hypothesis `h`.

## change
Defined in: `Lean.Parser.Tactic.changeWith`

* `change tgt'` will change the goal from `tgt` to `tgt'`,
  assuming these are definitionally equal.
* `change t' at h` will change hypothesis `h : t` to have type `t'`, assuming
  assuming `t` and `t'` are definitionally equal.
* `change a with b` will change occurrences of `a` to `b` in the goal,
  assuming `a` and `b` are definitionally equal.
* `change a with b at h` similarly changes `a` to `b` in the type of hypothesis `h`.

## change?
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

## check_compositions
Defined in: `Mathlib.Tactic.CheckCompositions.tacticCheck_compositions`

For each composition `f ≫ g` in the goal,
which internally is represented as `CategoryStruct.comp C inst X Y Z f g`,
infer the types of `f` and `g` and check whether their sources and targets agree
with `X`, `Y`, and `Z` at "instances and reducible" transparency,
reporting any discrepancies.

An example:

```
example (j : J) :
    colimit.ι ((F ⋙ G) ⋙ H) j ≫ (preservesColimitIso (G ⋙ H) F).inv =
      H.map (G.map (colimit.ι F j)) := by

  -- We know which lemma we want to use, and it's even a simp lemma, but `rw`
  -- won't let us apply it
  fail_if_success rw [ι_preservesColimitIso_inv]
  fail_if_success rw [ι_preservesColimitIso_inv (G ⋙ H)]
  fail_if_success simp only [ι_preservesColimitIso_inv]

  -- This would work:
  -- erw [ι_preservesColimitIso_inv (G ⋙ H)]

  -- `check_compositions` checks if the two morphisms we're composing are
  -- composed by abusing defeq, and indeed it tells us that we are abusing
  -- definitional associativity of composition of functors here: it prints
  -- the following.

  -- info: In composition
  --   colimit.ι ((F ⋙ G) ⋙ H) j ≫ (preservesColimitIso (G ⋙ H) F).inv
  -- the source of
  --   (preservesColimitIso (G ⋙ H) F).inv
  -- is
  --   colimit (F ⋙ G ⋙ H)
  -- but should be
  --   colimit ((F ⋙ G) ⋙ H)

  check_compositions

  -- In this case, we can "fix" this by reassociating in the goal, but
  -- usually at this point the right thing to do is to back off and
  -- check how we ended up with a bad goal in the first place.
  dsimp only [Functor.assoc]

  -- This would work now, but it is not needed, because simp works as well
  -- rw [ι_preservesColimitIso_inv]

  simp
```

## choose
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

Like `intro`, the `choose` tactic supports type annotations to specify the expected type
of the introduced variables. This is useful for documentation and for catching mistakes early:
```lean
example (h : ∃ n : ℕ, n > 0) : True := by
  choose (n : ℕ) (hn : n > 0) using h
  trivial
```
If the provided type does not match the actual type, an error is raised.

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

## choose!
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

Like `intro`, the `choose` tactic supports type annotations to specify the expected type
of the introduced variables. This is useful for documentation and for catching mistakes early:
```lean
example (h : ∃ n : ℕ, n > 0) : True := by
  choose (n : ℕ) (hn : n > 0) using h
  trivial
```
If the provided type does not match the actual type, an error is raised.

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

## classical
Defined in: `Lean.Parser.Tactic.classical`

`classical tacs` runs `tacs` in a scope where `Classical.propDecidable` is a low priority
local instance.

Note that `classical` is a scoping tactic: it adds the instance only within the
scope of the tactic.

## clean
Defined in: `Mathlib.Tactic.tacticClean_`

(Deprecated) `clean t` is a macro for `exact clean% t`.

## clean_wf
Defined in: `tacticClean_wf`

This tactic is used internally by lean before presenting the proof obligations from a well-founded
definition to the user via `decreasing_by`. It is not necessary to use this tactic manually.

## clear
Defined in: `Lean.Elab.Tactic.clearExceptTactic`

Clears all hypotheses it can, except those provided after a minus sign. Example:
```lean
  clear * - h₁ h₂
```

## clear
Defined in: `Lean.Parser.Tactic.clear`

`clear x...` removes the given hypotheses, or fails if there are remaining
references to a hypothesis.

## clear!
Defined in: `Mathlib.Tactic.clear!`

A variant of `clear` which clears not only the given hypotheses but also any other hypotheses
depending on them

## clear_
Defined in: `Mathlib.Tactic.clear_`

Clear all hypotheses starting with `_`, like `_match` and `_let_match`.

## clear_aux_decl
Defined in: `Mathlib.Tactic.clearAuxDecl`

This tactic clears all auxiliary declarations from the context.

## clear_value
Defined in: `Lean.Parser.Tactic.clearValue`

* `clear_value x...` clears the values of the given local definitions.
  A local definition `x : α := v` becomes a hypothesis `x : α`.

* `clear_value (h : x = _)` adds a hypothesis `h : x = v` before clearing the value of `x`.
  This is short for `have h : x = v := rfl; clear_value x`.
  Any value definitionally equal to `v` can be used in place of `_`.

* `clear_value *` clears values of all hypotheses that can be cleared.
  Fails if none can be cleared.

These syntaxes can be combined. For example, `clear_value x y *` ensures that `x` and `y` are cleared
while trying to clear all other local definitions,
and `clear_value (hx : x = _) y * with hx` does the same while first adding the `hx : x = v` hypothesis.

## coherence
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

## compareOfLessAndEq_rfl
Defined in: `tacticCompareOfLessAndEq_rfl`

This attempts to prove that a given instance of `compare` is equal to `compareOfLessAndEq` by
introducing the arguments and trying the following approaches in order:

1. seeing if `rfl` works
2. seeing if the `compare` at hand is nonetheless essentially `compareOfLessAndEq`, but, because of
implicit arguments, requires us to unfold the defs and split the `if`s in the definition of
`compareOfLessAndEq`
3. seeing if we can split by cases on the arguments, then see if the defs work themselves out
  (useful when `compare` is defined via a `match` statement, as it is for `Bool`)

## compute_degree
Defined in: `Mathlib.Tactic.ComputeDegree.computeDegree`

`compute_degree` is a tactic to solve goals of the form
*  `natDegree f = d`,
*  `degree f = d`,
*  `natDegree f ≤ d` (or `<`),
*  `degree f ≤ d` (or `<`),
*  `coeff f d = r`, if `d` is the degree of `f`.

The tactic may leave goals of the form `d' = d`, `d' ≤ d`, `d' < d`, or `r ≠ 0`, where `d'` in `ℕ`
or `WithBot ℕ` is the tactic's guess of the degree, and `r` is the coefficient's guess of the
leading coefficient of `f`.

`compute_degree` applies `norm_num` to the left-hand side of all side goals, trying to close them.

The variant `compute_degree!` first applies `compute_degree`.
Then it uses `norm_num` on all the remaining goals and tries `assumption`.

## compute_degree!
Defined in: `Mathlib.Tactic.ComputeDegree.tacticCompute_degree!`

`compute_degree` is a tactic to solve goals of the form
*  `natDegree f = d`,
*  `degree f = d`,
*  `natDegree f ≤ d` (or `<`),
*  `degree f ≤ d` (or `<`),
*  `coeff f d = r`, if `d` is the degree of `f`.

The tactic may leave goals of the form `d' = d`, `d' ≤ d`, `d' < d`, or `r ≠ 0`, where `d'` in `ℕ`
or `WithBot ℕ` is the tactic's guess of the degree, and `r` is the coefficient's guess of the
leading coefficient of `f`.

`compute_degree` applies `norm_num` to the left-hand side of all side goals, trying to close them.

The variant `compute_degree!` first applies `compute_degree`.
Then it uses `norm_num` on all the remaining goals and tries `assumption`.

## congr
Defined in: `Lean.Parser.Tactic.congr`

Apply congruence (recursively) to goals of the form `⊢ f as = f bs` and `⊢ f as ≍ f bs`.
The optional parameter is the depth of the recursive applications.
This is useful when `congr` is too aggressive in breaking down the goal.
For example, given `⊢ f (g (x + y)) = f (g (y + x))`,
`congr` produces the goals `⊢ x = y` and `⊢ y = x`,
while `congr 2` produces the intended `⊢ x + y = y + x`.

## congr
Defined in: `Batteries.Tactic.congrConfigWith`

Apply congruence (recursively) to goals of the form `⊢ f as = f bs` and `⊢ f as ≍ f bs`.
* `congr n` controls the depth of the recursive applications.
  This is useful when `congr` is too aggressive in breaking down the goal.
  For example, given `⊢ f (g (x + y)) = f (g (y + x))`,
  `congr` produces the goals `⊢ x = y` and `⊢ y = x`,
  while `congr 2` produces the intended `⊢ x + y = y + x`.
* If, at any point, a subgoal matches a hypothesis then the subgoal will be closed.
* You can use `congr with p (: n)?` to call `ext p (: n)?` to all subgoals generated by `congr`.
  For example, if the goal is `⊢ f '' s = g '' s` then `congr with x` generates the goal
  `x : α ⊢ f x = g x`.

## congr
Defined in: `Batteries.Tactic.congrConfig`

Apply congruence (recursively) to goals of the form `⊢ f as = f bs` and `⊢ f as ≍ f bs`.
The optional parameter is the depth of the recursive applications.
This is useful when `congr` is too aggressive in breaking down the goal.
For example, given `⊢ f (g (x + y)) = f (g (y + x))`,
`congr` produces the goals `⊢ x = y` and `⊢ y = x`,
while `congr 2` produces the intended `⊢ x + y = y + x`.

## congr!
Defined in: `Congr!.congr!`

`congr!` tries to prove the main goal by repeatedly applying congruence rules. For example, on a
goal of the form `⊢ f a1 a2 ... = f b1 b2 ...`, `congr!` will make new goals `⊢ a1 = b1`,
`⊢ a2 = b2`, ...

`congr!` is a more powerful version of the `congr` tactic that uses congruence lemmas (tagged with
`@[congr]`), reflexivity rules (tagged with `@[refl]`) and proof discharging strategies. The full
list of congruence proof strategies is documented in the module `Mathlib.Tactic.CongrExclamation`.
The `congr!` tactic is used by the `convert` and `convert_to` tactics.

* `congr! n`, where `n` is a positive numeral, controls the depth with which congruence is
  applied. For example, if the main goal is `n + n + 1 = 2 * n + 1`, then `congr! 1` results in one
  goal, `⊢ n + n = 2 * n`, and `congr! 2` (or more) results in two (impossible) goals
  `⊢ HAdd.hAdd = HMul.hMul` and `⊢ n = 2`.
  By default, the depth is unlimited.
* `congr! with x ⟨y₁, y₂⟩ (z₁ | z₂)` names or pattern-matches the variables introduced by
  congruence rules, like `rintro x ⟨y₁, y₂⟩ (z₁ | z₂)` would.
* `congr! (config := cfg)` uses the configuration options in `cfg` to control the congruence
  rules (see `Congr!.Config`).

## congrm
Defined in: `Mathlib.Tactic.congrM`

`congrm e` is a tactic for proving goals of the form `lhs = rhs`, `lhs ↔ rhs`, `lhs ≍ rhs`,
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

## congrm?
Defined in: `tacticCongrm?`

Display a widget panel allowing to generate a `congrm` call with holes specified by selecting
subexpressions in the goal.

## constructor
Defined in: `Lean.Parser.Tactic.constructor`

If the main goal's target type is an inductive type, `constructor` solves it with
the first matching constructor, or else fails.

## constructorm
Defined in: `Mathlib.Tactic.constructorM`

`constructorm p_1, ..., p_n`, where the main goal has type `type`, applies the first matching
constructor for `type`, if `type` matches one of the given patterns. If `type` does not match any
of the patterns, `constructorm` fails.

* `constructorm* p_1, ..., p_n` repeatedly applies a constructor until the goal no longer matches
  `p_1`, ..., `p_n`. This is a more efficient and compact version of
  `· repeat constructorm p_1, ..., p_n`. It is more efficient because the pattern is compiled once.

Examples:
```lean
example : True ∧ (True ∨ True) := by
  constructorm* _ ∨ _, _ ∧ _, True
```

## continuity
Defined in: `tacticContinuity`

`continuity` solves goals of the form `Continuous f` by applying lemmas tagged with the attribute
`@[continuity]`. If the goal is not solved after attempting all rules, `continuity` fails.

`fun_prop` is a (usually more powerful) alternative to `continuity`.

This tactic is extensible. Tagging lemmas with the `@[continuity]` attribute can allow `continuity`
to solve more goals.

* `continuity?` reports the proof script found by `continuity`.

## continuity?
Defined in: `tacticContinuity?`

`continuity` solves goals of the form `Continuous f` by applying lemmas tagged with the attribute
`@[continuity]`. If the goal is not solved after attempting all rules, `continuity` fails.

`fun_prop` is a (usually more powerful) alternative to `continuity`.

This tactic is extensible. Tagging lemmas with the `@[continuity]` attribute can allow `continuity`
to solve more goals.

* `continuity?` reports the proof script found by `continuity`.

## contradiction
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

## contrapose
Defined in: `Mathlib.Tactic.Contrapose.contrapose`

`contrapose` transforms the main goal into its contrapositive. If the goal has the form `⊢ P → Q`,
then `contrapose` turns it into `⊢ ¬ Q → ¬ P`. If the goal has the form `⊢ P ↔ Q`, then `contrapose`
turns it into `⊢ ¬ P ↔ ¬ Q`.

* `contrapose h` on a goal of the form `h : P ⊢ Q` turns the goal into `h : ¬ Q ⊢ ¬ P`. This is
  equivalent to `revert h; contrapose; intro h`.
* `contrapose h with new_h` uses the name `new_h` for the introduced hypothesis. This is equivalent
  to `revert h; contrapose; intro new_h`.
* `contrapose!`, `contrapose! h` and `contrapose! h with new_h` push negation deeper into the goal
  after contraposing (but before introducing the new hypothesis). See the `push Not` tactic for more
  details on the pushing algorithm.
* `contrapose! (config := cfg)` controls the options for negation pushing. All options for
  `Mathlib.Tactic.Push.Config` are supported:
  * `contrapose! +distrib` rewrites `¬ (p ∧ q)` into `¬ p ∨ ¬ q` instead of `p → ¬ q`.

Examples:
```lean4
variables (P Q R : Prop)

example (H : ¬ Q → ¬ P) : P → Q := by
  contrapose
  exact H

example (H : ¬ P ↔ ¬ Q) : P ↔ Q := by
  contrapose
  exact H

example (H : ¬ Q → ¬ P) (h : P) : Q := by
  contrapose h
  exact H h

example (H : ¬ R → P → ¬ Q) : (P ∧ Q) → R := by
  contrapose!
  exact H

example (H : ¬ R → ¬ P ∨ ¬ Q) : (P ∧ Q) → R := by
  contrapose! +distrib
  exact H
```

## contrapose!
Defined in: `Mathlib.Tactic.Contrapose.contrapose!`

`contrapose` transforms the main goal into its contrapositive. If the goal has the form `⊢ P → Q`,
then `contrapose` turns it into `⊢ ¬ Q → ¬ P`. If the goal has the form `⊢ P ↔ Q`, then `contrapose`
turns it into `⊢ ¬ P ↔ ¬ Q`.

* `contrapose h` on a goal of the form `h : P ⊢ Q` turns the goal into `h : ¬ Q ⊢ ¬ P`. This is
  equivalent to `revert h; contrapose; intro h`.
* `contrapose h with new_h` uses the name `new_h` for the introduced hypothesis. This is equivalent
  to `revert h; contrapose; intro new_h`.
* `contrapose!`, `contrapose! h` and `contrapose! h with new_h` push negation deeper into the goal
  after contraposing (but before introducing the new hypothesis). See the `push Not` tactic for more
  details on the pushing algorithm.
* `contrapose! (config := cfg)` controls the options for negation pushing. All options for
  `Mathlib.Tactic.Push.Config` are supported:
  * `contrapose! +distrib` rewrites `¬ (p ∧ q)` into `¬ p ∨ ¬ q` instead of `p → ¬ q`.

Examples:
```lean4
variables (P Q R : Prop)

example (H : ¬ Q → ¬ P) : P → Q := by
  contrapose
  exact H

example (H : ¬ P ↔ ¬ Q) : P ↔ Q := by
  contrapose
  exact H

example (H : ¬ Q → ¬ P) (h : P) : Q := by
  contrapose h
  exact H h

example (H : ¬ R → P → ¬ Q) : (P ∧ Q) → R := by
  contrapose!
  exact H

example (H : ¬ R → ¬ P ∨ ¬ Q) : (P ∧ Q) → R := by
  contrapose! +distrib
  exact H
```

## conv
Defined in: `Lean.Parser.Tactic.Conv.conv`

`conv => ...` allows the user to perform targeted rewriting on a goal or hypothesis,
by focusing on particular subexpressions.

See <https://lean-lang.org/theorem_proving_in_lean4/conv.html> for more details.

Basic forms:
* `conv => cs` will rewrite the goal with conv tactics `cs`.
* `conv at h => cs` will rewrite hypothesis `h`.
* `conv in pat => cs` will rewrite the first subexpression matching `pat` (see `pattern`).

## conv'
Defined in: `Lean.Parser.Tactic.Conv.convTactic`

Executes the given conv block without converting regular goal into a `conv` goal.

## conv?
Defined in: `Mathlib.Tactic.Conv.tacticConv?`

Display a widget panel allowing to generate a `conv` call zooming to the subexpression selected
in the goal or in the type of a local hypothesis or let-decl.

## conv_lhs
Defined in: `Mathlib.Tactic.Conv.convLHS`

`conv_lhs => cs` runs the `conv` tactic sequence `cs` on the left hand side of the target.

In general, for an `n`-ary operator as the target, it traverses into the second to last argument.
It is a synonym for `conv => arg -2; cs`.

* `conv_lhs at h => cs` runs `cs` on the left hand side of hypothesis `h`.
* `conv_lhs in pat => cs` first looks for a subexpression matching `pat` (see also the `pattern`
  conv tactic) and then traverses into the left hand side of this subexpression.
  This syntax also supports the `occs` clause for the pattern.

## conv_rhs
Defined in: `Mathlib.Tactic.Conv.convRHS`

`conv_rhs => cs` runs the `conv` tactic sequence `cs` on the right hand side of the target.

In general, for an `n`-ary operator as the target, it traverses into the last argument.
It is a synonym for `conv => arg -1; cs`.

* `conv_rhs at h => cs` runs `cs` on the right hand side of hypothesis `h`.
* `conv_rhs in pat => cs` first looks for a subexpression matching `pat` (see the `pattern`
  conv tactic) and then traverses into the right hand side of this subexpression.
  This syntax also supports the `occs` clause for the pattern.

## convert
Defined in: `Mathlib.Tactic.convert`

`convert e`, where the term `e` is inferred to have type `t`, replaces the main goal `⊢ t'` with new
goals for proving the equality `t' = t` using congruence. The goals are created like `congr!` would.
Like `refine e`, any holes (`?_` or `?x`) in `e` that are not solved by unification are converted
into new goals, using the hole's name, if any, as the goal case name.
Like `congr!`, `convert` introduces variables while applying congruence rules. These can be
pattern-matched, like `rintro` would, using the `with` keyword.

See also `convert_to t`, where `t` specifies the expected type, instead of a proof term of type `t`.
In other words, `convert_to t` works like `convert (?_ : t)`. Both tactics use the same options.

* `convert ← e` creates equality goals in the opposite direction (with the goal type on the right).
* `convert e using n`, where `n` is a positive numeral, controls the depth with which congruence is
  applied. For example, if the main goal is `⊢ Prime (n + n + 1)` and `e : Prime (2 * n + 1)`, then
  `convert e using 2` results in one goal, `⊢ n + n = 2 * n`, and `convert e using 3` (or more)
  results in two (impossible) goals `⊢ HAdd.hAdd = HMul.hMul` and `⊢ n = 2`.
  By default, the depth is unlimited.
* `convert e with x ⟨y₁, y₂⟩ (z₁ | z₂)` names or pattern-matches the variables introduced by
  congruence rules, like `rintro x ⟨y₁, y₂⟩ (z₁ | z₂)` would.
* `convert (config := cfg) e` uses the configuration options in `cfg` to control the congruence
  rules (see `Congr!.Config`).

Examples:

```lean
-- `convert using` controls the depth of congruence.
example {n : ℕ} (e : Prime (2 * n + 1)) :
    Prime (n + n + 1) := by
  convert e using 2
  -- One goal: ⊢ n + n = 2 * n
  ring

-- `convert` can fail where `exact` succeeds.
example (h : p 0) : p 1 := by
  fail_if_success
    convert h -- fails, left-over goal 1 = 0
    done
  exact h -- succeeds

-- `convert with` names introduced variables.
example (p q : Nat → Prop) (h : ∀ ε > 0, p ε) :
    ∀ ε > 0, q ε := by
  convert h using 2 with ε hε
  -- Goal now looks like:
  -- hε : ε > 0
  -- ⊢ q ε ↔ p ε
  sorry
```

## convert_to
Defined in: `Mathlib.Tactic.convertTo`

`convert_to t` on a goal `⊢ t'` changes the goal to `⊢ t` and adds new goals for proving the
equality `t' = t` using congruence. The goals are created like `congr!` would.
Any remaining congruence goals come before the main goal.
Like `refine e`, any holes (`?_` or `?x`) in `t` that are not solved by unification are converted
into new goals, using the hole's name, if any, as the goal case name.
Like `congr!`, `convert_to` introduces variables while applying congruence rules. These can be
pattern-matched, like `rintro` would, using the `with` keyword.

`convert e`, where `e` is a term of type `t`, uses `e` to close the new main goal. In other words,
`convert e` works like `convert_to t; refine e`. Both tactics use the same options.

* `convert_to ty at h` changes the type of the local hypothesis `h` to `ty`. If later local
  hypotheses or the goal depend on `h`, then `convert_to t at h` may leave a copy of `h`.
* `convert_to ← t` creates equality goals in the opposite direction (with the original goal type on
  the right).
* `convert_to t using n`, where `n` is a positive numeral, controls the depth with which congruence
  is applied. For example, if the main goal is `⊢ Prime (n + n + 1)`,
  then `convert_to Prime (2 * n + 1) using 2` results in one goal, `⊢ n + n = 2 * n`, and
  `convert_to Prime (2 * n + 1) using 3` (or more) results in two (impossible) goals
  `⊢ HAdd.hAdd = HMul.hMul` and `⊢ n = 2`.
  The default value for `n` is 1.
* `convert_to t with x ⟨y₁, y₂⟩ (z₁ | z₂)` names or pattern-matches the variables introduced by
  congruence rules, like `rintro x ⟨y₁, y₂⟩ (z₁ | z₂)` would.
* `convert_to (config := cfg) t` uses the configuration options in `cfg` to control the congruence
  rules (see `Congr!.Config`).

## cutsat
Defined in: `Lean.Parser.Tactic.cutsat`

`cutsat` solves linear integer arithmetic goals.

It is a implemented as a thin wrapper around the `grind` tactic, enabling only the `lia` solver.
Please use `grind` instead if you need additional capabilities.

**Deprecated**: Use `lia` instead.

## dbg_trace
Defined in: `Lean.Parser.Tactic.dbgTrace`

`dbg_trace "foo"` prints `foo` when elaborated.
Useful for debugging tactic control flow:
```lean
example : False ∨ True := by
  first
  | apply Or.inl; trivial; dbg_trace "left"
  | apply Or.inr; trivial; dbg_trace "right"
```

## decide
Defined in: `Lean.Parser.Tactic.decide`

`decide` attempts to prove the main goal (with target type `p`) by synthesizing an instance of `Decidable p`
and then reducing that instance to evaluate the truth value of `p`.
If it reduces to `isTrue h`, then `h` is a proof of `p` that closes the goal.

The target is not allowed to contain local variables or metavariables.
If there are local variables, you can first try using the `revert` tactic with these local variables to move them into the target,
or you can use the `+revert` option, described below.

Options:
- `decide +revert` begins by reverting local variables that the target depends on,
  after cleaning up the local context of irrelevant variables.
  A variable is *relevant* if it appears in the target, if it appears in a relevant variable,
  or if it is a proposition that refers to a relevant variable.
- `decide +kernel` uses kernel for reduction instead of the elaborator.
  It has two key properties: (1) since it uses the kernel, it ignores transparency and can unfold everything,
  and (2) it reduces the `Decidable` instance only once instead of twice.
- `decide +native` uses the native code compiler (`#eval`) to evaluate the `Decidable` instance,
  admitting the result via an axiom. This can be significantly more efficient than using reduction, but it is at the cost of increasing the size
  This can be significantly more efficient than using reduction, but it is at the cost of increasing the size
  of the trusted code base.
  Namely, it depends on the correctness of the Lean compiler and all definitions with an `@[implemented_by]` attribute.
  Like with `+kernel`, the `Decidable` instance is evaluated only once.

Limitation: In the default mode or `+kernel` mode, since `decide` uses reduction to evaluate the term,
`Decidable` instances defined by well-founded recursion might not work because evaluating them requires reducing proofs.
Reduction can also get stuck on `Decidable` instances with `Eq.rec` terms.
These can appear in instances defined using tactics (such as `rw` and `simp`).
To avoid this, create such instances using definitions such as `decidable_of_iff` instead.

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

## decide_cbv
Defined in: `Lean.Parser.Tactic.decide_cbv`

`decide_cbv` is a finishing tactic that closes goals of the form `p`, where `p`
is a `Decidable` proposition. It proceeds in two steps:
1. Apply `of_decide_eq_true` to transform the goal into `decide p = true`.
2. Reduce `decide p` via call-by-value normalization. If the result is
   definitionally equal to `true`, the goal is closed.

`decide_cbv` fails with an error if `decide p` does not reduce to `true`.
Unlike `cbv`, `decide_cbv` is a terminal tactic: it either closes the goal or
fails.

The proofs produced by `decide_cbv` only use the three standard axioms.
In particular, they do not require trust in the correctness of the code
generator.

This tactic is experimental and its behavior is likely to change in upcoming
releases of Lean.

## decreasing_tactic
Defined in: `tacticDecreasing_tactic`

`decreasing_tactic` is called by default on well-founded recursions in order
to synthesize a proof that recursive calls decrease along the selected
well founded relation. It can be locally overridden by using `decreasing_by tac`
on the recursive definition, and it can also be globally extended by adding
more definitions for `decreasing_tactic` (or `decreasing_trivial`,
which this tactic calls).

## decreasing_trivial
Defined in: `tacticDecreasing_trivial`

Extensible helper tactic for `decreasing_tactic`. This handles the "base case"
reasoning after applying lexicographic order lemmas.
It can be extended by adding more macro definitions, e.g.
```lean
macro_rules | `(tactic| decreasing_trivial) => `(tactic| linarith)
```

## decreasing_trivial_pre_omega
Defined in: `tacticDecreasing_trivial_pre_omega`

Variant of `decreasing_trivial` that does not use `omega`, intended to be used in core modules
before `omega` is available.

## decreasing_with
Defined in: `tacticDecreasing_with_`

Constructs a proof of decreasing along a well founded relation, by simplifying, then applying
lexicographic order lemmas and finally using `ts` to solve the base case. If it fails,
it prints a message to help the user diagnose an ill-founded recursive definition.

## delta
Defined in: `Lean.Parser.Tactic.delta`

`delta id1 id2 ...` delta-expands the definitions `id1`, `id2`, ....
This is a low-level tactic, it will expose how recursive definitions have been
compiled by Lean.

## deriving_LawfulEq_tactic
Defined in: `tacticDeriving_LawfulEq_tactic`


## deriving_LawfulEq_tactic_step
Defined in: `tacticDeriving_LawfulEq_tactic_step`


## deriving_ReflEq_tactic
Defined in: `DerivingHelpers.tacticDeriving_ReflEq_tactic`


## discrete_cases
Defined in: `CategoryTheory.Discrete.tacticDiscrete_cases`

A simple tactic to run `cases` on any `Discrete α` hypotheses.

## done
Defined in: `Lean.Parser.Tactic.done`

`done` succeeds iff there are no remaining goals.

## dsimp
Defined in: `Lean.Parser.Tactic.dsimp`

The `dsimp` tactic is the definitional simplifier. It is similar to `simp` but only
applies theorems that hold by reflexivity. Thus, the result is guaranteed to be
definitionally equal to the input.

## dsimp!
Defined in: `Lean.Parser.Tactic.dsimpAutoUnfold`

`dsimp!` is shorthand for `dsimp` with `autoUnfold := true`.
This will unfold applications of functions defined by pattern matching, when one of the patterns applies.
This can be used to partially evaluate many definitions.

## dsimp?
Defined in: `Lean.Parser.Tactic.dsimpTrace`

`simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal. This is useful for reducing the size of the simp
set in a local invocation to speed up processing.
```lean
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- prints "Try this: simp only [ite_true]"
```

This command can also be used in `simp_all` and `dsimp`.

## dsimp?!
Defined in: `Lean.Parser.Tactic.tacticDsimp?!_`

`simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal. This is useful for reducing the size of the simp
set in a local invocation to speed up processing.
```lean
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- prints "Try this: simp only [ite_true]"
```

This command can also be used in `simp_all` and `dsimp`.

## eapply
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

## econstructor
Defined in: `tacticEconstructor`

`econstructor`, on a goal which is an inductive type, solves it by applying the first matching
constructor, creating new goals for non-dependent arguments to the constructor in the same order.
This is like `constructor` except only non-dependent arguments are shown as new goals.

## enat_to_nat
Defined in: `Mathlib.Tactic.ENatToNat.tacticEnat_to_nat`

`enat_to_nat` shifts all `ENat`s in the context to `Nat`, rewriting propositions about them.
A typical use case is `enat_to_nat; lia`.

## eq_refl
Defined in: `Lean.Parser.Tactic.eqRefl`

`eq_refl` is equivalent to `exact rfl`, but has a few optimizations.

## erw
Defined in: `Lean.Parser.Tactic.tacticErw___`

`erw [rules]` is a shorthand for `rw (transparency := .default) [rules]`.
This does rewriting up to unfolding of regular definitions (by comparison to regular `rw`
which only unfolds `@[reducible]` definitions).

## erw?
Defined in: `Mathlib.Tactic.Erw?.erw?`

`erw? [r, ...]` calls `erw [r, ...]` (at hypothesis `h` if written `erw [r, ...] at h`),
and then attempts to identify any subexpression which would block the use of `rw` instead.
It does so by identifying subexpressions which are defeq, but not at reducible transparency.

## eta_expand
Defined in: `Mathlib.Tactic.etaExpandStx`

`eta_expand at loc` eta expands all sub-expressions at the given location.
It also beta reduces any applications of eta expanded terms, so it puts it
into an eta-expanded "normal form."
This also exists as a `conv`-mode tactic.

For example, if `f` takes two arguments, then `f` becomes `fun x y => f x y`
and `f x` becomes `fun y => f x y`.

This can be useful to turn, for example, a raw `HAdd.hAdd` into `fun x y => x + y`.

## eta_reduce
Defined in: `Mathlib.Tactic.etaReduceStx`

`eta_reduce at loc` eta reduces all sub-expressions at the given location.
This also exists as a `conv`-mode tactic.

For example, `fun x y => f x y` becomes `f` after eta reduction.

## eta_struct
Defined in: `Mathlib.Tactic.etaStructStx`

`eta_struct at loc` transforms structure constructor applications such as `S.mk x.1 ... x.n`
(pretty printed as, for example, `{a := x.a, b := x.b, ...}`) into `x`.
This also exists as a `conv`-mode tactic.

The transformation is known as eta reduction for structures, and it yields definitionally
equal expressions.

For example, given `x : α × β`, then `(x.1, x.2)` becomes `x` after this transformation.

## exact
Defined in: `Lean.Parser.Tactic.exact`

`exact e` closes the main goal if its target type matches that of `e`.

## exact?
Defined in: `Lean.Parser.Tactic.exact?`

Searches environment for definitions or theorems that can solve the goal using `exact`
with conditions resolved by `solve_by_elim`.

The optional `using` clause provides identifiers in the local context that must be
used by `exact?` when closing the goal.  This is most useful if there are multiple
ways to resolve the goal, and one wants to guide which lemma is used.

Use `+grind` to enable `grind` as a fallback discharger for subgoals.
Use `+try?` to enable `try?` as a fallback discharger for subgoals.
Use `-star` to disable fallback to star-indexed lemmas (like `Empty.elim`, `And.left`).
Use `+all` to collect all successful lemmas instead of stopping at the first.

## exact_mod_cast
Defined in: `Lean.Parser.Tactic.tacticExact_mod_cast_`

Normalize casts in the goal and the given expression, then close the goal with `exact`.

## exacts
Defined in: `Batteries.Tactic.exacts`

Like `exact`, but takes a list of terms and checks that all goals are discharged after the tactic.

## exfalso
Defined in: `Lean.Parser.Tactic.tacticExfalso`

`exfalso` converts a goal `⊢ tgt` into `⊢ False` by applying `False.elim`.

## exists
Defined in: `Lean.Parser.Tactic.«tacticExists_,,»`

`exists e₁, e₂, ...` is shorthand for `refine ⟨e₁, e₂, ...⟩; try trivial`.
It is useful for existential goals.

## existsi
Defined in: `Mathlib.Tactic.«tacticExistsi_,,»`

`existsi e₁, e₂, ⋯` instantiates existential quantifiers in the main goal by using `e₁`, `e₂`, ...
as witnesses. `existsi e₁, e₂, ⋯` is equivalent to `refine ⟨e₁, e₂, ⋯, ?_⟩`.

See also `exists`: `exists e₁, e₂, ⋯` is equivalent to `existsi e₁, e₂, ⋯; try trivial`.

Examples:

```lean
example : ∃ x : Nat, x = x := by
  existsi 42
  rfl

example : ∃ x : Nat, ∃ y : Nat, x = y := by
  existsi 42, 42
  rfl
```

## expose_names
Defined in: `Lean.Parser.Tactic.exposeNames`

`expose_names` renames all inaccessible variables with accessible names, making them available
for reference in generated tactics. However, this renaming introduces machine-generated names
that are not fully under user control. `expose_names` is primarily intended as a preamble for
auto-generated end-game tactic scripts. It is also useful as an alternative to
`set_option tactic.hygienic false`. If explicit control over renaming is needed in the
middle of a tactic script, consider using structured tactic scripts with
`match .. with`, `induction .. with`, or `intro` with explicit user-defined names,
as well as tactics such as `next`, `case`, and `rename_i`.

## ext
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

## ext1
Defined in: `Lean.Elab.Tactic.Ext.tacticExt1___`

`ext1 pat*` is like `ext pat*` except that it only applies a single extensionality theorem rather
than recursively applying as many extensionality theorems as possible.

The `pat*` patterns are processed using the `rintro` tactic.
If no patterns are supplied, then variables are introduced anonymously using the `intros` tactic.

## extract_goal
Defined in: `Mathlib.Tactic.ExtractGoal.extractGoal`

`extract_goal` formats the current goal as a stand-alone theorem or definition after
cleaning up the local context of irrelevant variables.

A variable is *relevant* if (1) it occurs in the target type, (2) there is a relevant variable
that depends on it, or (3) the type of the variable is a proposition that depends on a
relevant variable.
If the target is `False`, then for convenience `extract_goal` includes all variables.

The tactic tries to produce an output that can be copy-pasted and just work,
but its success depends on whether the expressions are amenable
to being unambiguously pretty printed.
The tactic responds to pretty printing options.
For example, `set_option pp.all true in extract_goal` gives the `pp.all` form.

* `extract_goal *` formats the current goal without cleaning up the local context.
* `extract_goal a b c ...` formats the current goal after removing everything that the given
  variables `a`, `b`, `c`, ... do not depend on.
* `extract_goal ... using name` uses the name `name` for the theorem or definition rather than
  the autogenerated name.

## extract_lets
Defined in: `Lean.Parser.Tactic.extractLets`

Extracts `let` and `have` expressions from within the target or a local hypothesis,
introducing new local definitions.

- `extract_lets` extracts all the lets from the target.
- `extract_lets x y z` extracts all the lets from the target and uses `x`, `y`, and `z` for the first names.
  Using `_` for a name leaves it unnamed.
- `extract_lets x y z at h` operates on the local hypothesis `h` instead of the target.

For example, given a local hypotheses if the form `h : let x := v; b x`, then `extract_lets z at h`
introduces a new local definition `z := v` and changes `h` to be `h : b z`.

## fail
Defined in: `Lean.Parser.Tactic.fail`

`fail msg` is a tactic that always fails, and produces an error using the given message.

## fail_if_no_progress
Defined in: `Mathlib.Tactic.failIfNoProgress`

`fail_if_no_progress tacs` evaluates `tacs`, and fails if no progress is made on the main goal
or the local context at reducible transparency.

## fail_if_success
Defined in: `Lean.Parser.Tactic.failIfSuccess`

`fail_if_success t` fails if the tactic `t` succeeds.

## false_or_by_contra
Defined in: `Lean.Parser.Tactic.falseOrByContra`

Changes the goal to `False`, retaining as much information as possible:

* If the goal is `False`, do nothing.
* If the goal is an implication or a function type, introduce the argument and restart.
  (In particular, if the goal is `x ≠ y`, introduce `x = y`.)
* Otherwise, for a propositional goal `P`, replace it with `¬ ¬ P`
  (attempting to find a `Decidable` instance, but otherwise falling back to working classically)
  and introduce `¬ P`.
* For a non-propositional goal use `False.elim`.

## fapply
Defined in: `Batteries.Tactic.tacticFapply_`

`fapply e` is like `apply e` but it adds goals in the order they appear,
rather than putting the dependent goals first.

## fconstructor
Defined in: `tacticFconstructor`

`fconstructor`, on a goal which is an inductive type, solves it by applying the first matching
constructor, creating new goals for all arguments to the constructor in the same order.
This is like `constructor` except the goals are not reordered.

## field
Defined in: `Mathlib.Tactic.FieldSimp.field`

`field` solves equality goals in (semi-)fields. The goal must be an equality which is *universal*,
in the sense that it is true in any field in which the appropriate denominators don't vanish.
(That is, it is a consequence purely of the field axioms.)

The `field` tactic is built from the tactics `field_simp` (which clears the denominators) and `ring`
(which proves equality goals universally true in commutative (semi-)rings). If `field` fails to
prove your goal, you may still be able to prove your goal by running the `field_simp` and `ring_nf`
normalizations in some order.

The tactic will try discharge proofs of nonzeroness of denominators, and skip steps if discharging
fails. These denominators are made out of denominators appearing in the input expression, by
repeatedly taking products or divisors. The default discharger can be non-universal, i.e. can be
specific to the field at hand (order properties, explicit `≠ 0` hypotheses, `CharZero` if that is
known, etc). See `Mathlib.Tactic.FieldSimp.discharge` for full details of the default discharger
algorithm.

* `field (disch := tac)` uses the tactic sequence `tac` to discharge nonzeroness proofs.
* `field [t₁, ..., tₙ]` provides terms `t₁`, ..., `tₙ` to the discharger for nonzeroness proofs.

Examples:
```lean
example {x y : ℚ} (hx : x + y ≠ 0) : x / (x + y) + y / (x + y) = 1 := by field
example {a b : ℝ} (ha : a ≠ 0) : a / (a * b) - 1 / b = 0 := by field

-- The user can also provide additional terms to help with nonzeroness proofs:
example {K : Type*} [Field K] (hK : ∀ x : K, x ^ 2 + 1 ≠ 0) (x : K) :
    1 / (x ^ 2 + 1) + x ^ 2 / (x ^ 2 + 1) = 1 := by
  field [hK]

example {a b : ℚ} (H : b + a ≠ 0) : a / (a + b) + b / (b + a) = 1 := by
  -- `field` cannot prove this on its own.
  fail_if_success field
  -- But running `ring_nf` and `field_simp` in a different order works:
  ring_nf at *
  field
```

## field_simp
Defined in: `Mathlib.Tactic.FieldSimp.fieldSimp`

`field_simp` normalizes expressions in (semi-)fields by rewriting them to a common denominator,
i.e. to reduce them to expressions of the form `n / d` where neither `n` nor `d` contains any
division symbol. The `field_simp` tactic will also clear denominators in field *(in)equalities*, by
cross-multiplying.

A very common pattern is `field_simp; ring` (clear denominators, then the resulting goal is
solvable by the axioms of a commutative ring). The finishing tactic `field` is a shorthand for this
pattern.

The tactic will try discharge proofs of nonzeroness of denominators, and skip steps if discharging
fails. These denominators are made out of denominators appearing in the input expression,
by repeatedly taking products or divisors. The default discharger can be non-universal, i.e. can be
specific to the field at hand (order properties, explicit `≠ 0` hypotheses, `CharZero` if that is
known, etc). See `field_simp_discharge` for full details of the default discharger algorithm.

* `field_simp at l1 l2 ...` can be used to normalize at the given locations.
* `field_simp (disch := tac)` uses the tactic sequence `tac` to discharge nonzeroness/positivity
  proofs.
* `field_simp [t₁, ..., tₙ]` provides terms `t₁`, ..., `tₙ` to the discharger for
  nonzeroness/positivity proofs.

Examples:
```lean
-- `x / (1 - y) / (1 + y / (1 - y))` is reduced to `x / (1 - y + y)`
example (x y z : ℚ) (hy : 1 - y ≠ 0) :
    ⌊x / (1 - y) / (1 + y / (1 - y))⌋ < 3 := by
  field_simp
  -- new goal: `⊢ ⌊x / (1 - y + y)⌋ < 3`
  sorry

-- `field_simp` will clear the `x` denominators in the following equation
example {K : Type*} [Field K] {x : K} (hx0 : x ≠ 0) :
    (x + 1 / x) ^ 2 + (x + 1 / x) = 1 := by
  field_simp
  -- new goal: `⊢ (x ^ 2 + 1) * (x ^ 2 + 1 + x) = x ^ 2`
  sorry
```

## field_simp_discharge
Defined in: `Mathlib.Tactic.FieldSimp.tacticField_simp_discharge`

Default discharge strategy for `field` and `field_simp`: try to solve the (in)equality `prop`,
of the form `t = 0` or `t > 0`, by one of the following strategies:

* Use an assumption from the context.
* Use the `norm_num` tactic.
* Use the `positivity` tactic.
* Use the `simp` tactic with `discharge` as discharger and lemmas stating:
  * `2 ≠ 0`, `3 ≠ 0`, `4 ≠ 0`
  * `x ≠ 0 → y ≠ 0 → x * y ≠ 0`
  * `a ≠ 0 → a ^ n ≠ 0` (for `n : ℕ` and `n : ℤ`)
  * `↑n + 1 ≠ 0`, if `n : ℕ` and the field has characteristic 0.

If none of the strategies finds a proof for `prop`, the result is `none`.

## filter_upwards
Defined in: `Mathlib.Tactic.filterUpwards`

`filter_upwards [h₁, ⋯, hₙ]` replaces a goal of the form `s ∈ f` and terms
`h₁ : t₁ ∈ f, ⋯, hₙ : tₙ ∈ f` with `∀ x, x ∈ t₁ → ⋯ → x ∈ tₙ → x ∈ s`.
The list is an optional parameter, `[]` being its default value.

`filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ` is a short form for
`{ filter_upwards [h₁, ⋯, hₙ], intro a₁ a₂ ⋯ aₖ }`.

`filter_upwards [h₁, ⋯, hₙ] using e` is a short form for
`{ filter_upwards [h1, ⋯, hn], exact e }`.

Combining both shortcuts is done by writing `filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ using e`.
Note that in this case, the `aᵢ` terms can be used in `e`.

## fin_cases
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

## fin_omega
Defined in: `Fin.tacticFin_omega`

`fin_omega` is a preprocessor for `omega` to handle inequalities in `Fin`.
It rewrites all hypotheses and the goal, turning statements about addition, subtraction and
inequalities in `Fin n` into statements that `omega` can use/solve.
Note that this involves a lot of case splitting, so may be slow.

## find
Defined in: `Mathlib.Tactic.Find.tacticFind`

`find` finds definitions and theorems whose result type matches the current goal exactly,
and prints them as info lines.
In other words, `find` lists definitions and theorems that are `apply`able against the current goal.
`find` will not affect the goal by itself and should be removed from the finished proof.

For a command or tactic that takes the type to search for as an argument, see `#find`.

Example:
```lean
example : True := by
  find
  -- True.intro: True
  -- trivial: True
  -- ...
```

## finiteness
Defined in: `finiteness`

`finiteness` proves goals of the form `*** < ∞` and (equivalently) `*** ≠ ∞` in the extended
nonnegative reals (`ℝ≥0∞`). If the goal cannot be proven, `finiteness` prints a warning and shows
its intermediate progress.

This tactic is based on `aesop`. It calls `assumption`, `intros`, `positivity`, and any
lemma or rule added to the `finiteness` ruleset, except that all `simp` rules are disabled.

This tactic is extensible. By adding more rules, `finiteness` can prove more goals. For example:
* `@[aesop (rule_sets := [finiteness]) safe 50] lemma ...`
* `add_aesop_rules safe tactic (rule_sets := [finiteness]) (by ...)`
(Note that a `simp` rule cannot be added this way, since all `simp` rules are disabled.)

* `finiteness (clause)` customizes the `aesop` call using the given clause. See `aesop`
  documentation for detailed explanation. Note that `finiteness` disables `simp`, so
  `finiteness (add simp [lemma1, lemma2])` does not do anything more than a bare `finiteness`.
* `finiteness [t₁, ..., tₙ]` adds the terms `t₁`, ..., `tₙ` as local hypotheses before applying
  the search rules.
* `finiteness?` additionally shows the proof that `finiteness` found.
* `finiteness_nonterminal` is a version of `finiteness` that does not report a warning if it fails
  to close the goal.

## finiteness?
Defined in: `finiteness?`

`finiteness` proves goals of the form `*** < ∞` and (equivalently) `*** ≠ ∞` in the extended
nonnegative reals (`ℝ≥0∞`). If the goal cannot be proven, `finiteness` prints a warning and shows
its intermediate progress.

This tactic is based on `aesop`. It calls `assumption`, `intros`, `positivity`, and any
lemma or rule added to the `finiteness` ruleset, except that all `simp` rules are disabled.

This tactic is extensible. By adding more rules, `finiteness` can prove more goals. For example:
* `@[aesop (rule_sets := [finiteness]) safe 50] lemma ...`
* `add_aesop_rules safe tactic (rule_sets := [finiteness]) (by ...)`
(Note that a `simp` rule cannot be added this way, since all `simp` rules are disabled.)

* `finiteness (clause)` customizes the `aesop` call using the given clause. See `aesop`
  documentation for detailed explanation. Note that `finiteness` disables `simp`, so
  `finiteness (add simp [lemma1, lemma2])` does not do anything more than a bare `finiteness`.
* `finiteness [t₁, ..., tₙ]` adds the terms `t₁`, ..., `tₙ` as local hypotheses before applying
  the search rules.
* `finiteness?` additionally shows the proof that `finiteness` found.
* `finiteness_nonterminal` is a version of `finiteness` that does not report a warning if it fails
  to close the goal.

## finiteness_nonterminal
Defined in: `finiteness_nonterminal`

`finiteness` proves goals of the form `*** < ∞` and (equivalently) `*** ≠ ∞` in the extended
nonnegative reals (`ℝ≥0∞`). If the goal cannot be proven, `finiteness` prints a warning and shows
its intermediate progress.

This tactic is based on `aesop`. It calls `assumption`, `intros`, `positivity`, and any
lemma or rule added to the `finiteness` ruleset, except that all `simp` rules are disabled.

This tactic is extensible. By adding more rules, `finiteness` can prove more goals. For example:
* `@[aesop (rule_sets := [finiteness]) safe 50] lemma ...`
* `add_aesop_rules safe tactic (rule_sets := [finiteness]) (by ...)`
(Note that a `simp` rule cannot be added this way, since all `simp` rules are disabled.)

* `finiteness (clause)` customizes the `aesop` call using the given clause. See `aesop`
  documentation for detailed explanation. Note that `finiteness` disables `simp`, so
  `finiteness (add simp [lemma1, lemma2])` does not do anything more than a bare `finiteness`.
* `finiteness [t₁, ..., tₙ]` adds the terms `t₁`, ..., `tₙ` as local hypotheses before applying
  the search rules.
* `finiteness?` additionally shows the proof that `finiteness` found.
* `finiteness_nonterminal` is a version of `finiteness` that does not report a warning if it fails
  to close the goal.

## first
Defined in: `Lean.Parser.Tactic.first`

`first | tac | ...` runs each `tac` until one succeeds, or else fails.

## first_par
Defined in: `Lean.Parser.Tactic.firstPar`

Helper internal tactic for implementing the tactic `try?` with parallel execution, returning first success.

## focus
Defined in: `Lean.Parser.Tactic.focus`

`focus tac` focuses on the main goal, suppressing all other goals, and runs `tac` on it.
Usually `· tac`, which enforces that the goal is closed by `tac`, should be preferred.

## forward
Defined in: `Aesop.Frontend.tacticForward____`


## forward?
Defined in: `Aesop.Frontend.tacticForward?____`


## frac_tac
Defined in: `RatFunc.tacticFrac_tac`

Solve equations for `K⟮X⟯` by working in `FractionRing K[X]`.

## fun_cases
Defined in: `Lean.Parser.Tactic.funCases`

The `fun_cases` tactic is a convenience wrapper of the `cases` tactic when using a functional
cases principle.

The tactic invocation
```
fun_cases f x ... y ...`
```
is equivalent to
```
cases y, ... using f.fun_cases_unfolding x ...
```
where the arguments of `f` are used as arguments to `f.fun_cases_unfolding` or targets of the case
analysis, as appropriate.

The form
```
fun_cases f
```
(with no arguments to `f`) searches the goal for a unique eligible application of `f`, and uses
these arguments. An application of `f` is eligible if it is saturated and the arguments that will
become targets are free variables.

The form `fun_cases f x y with | case1 => tac₁ | case2 x' ih => tac₂` works like with `cases`.

Under `set_option tactic.fun_induction.unfolding true` (the default), `fun_induction` uses the
`f.fun_cases_unfolding` theorem, which will try to automatically unfold the call to `f` in
the goal. With `set_option tactic.fun_induction.unfolding false`, it uses `f.fun_cases` instead.

## fun_induction
Defined in: `Lean.Parser.Tactic.funInduction`

The `fun_induction` tactic is a convenience wrapper around the `induction` tactic to use the
functional induction principle.

The tactic invocation
```
fun_induction f x₁ ... xₙ y₁ ... yₘ
```
where `f` is a function defined by non-mutual structural or well-founded recursion, is equivalent to
```
induction y₁, ... yₘ using f.induct_unfolding x₁ ... xₙ
```
where the arguments of `f` are used as arguments to `f.induct_unfolding` or targets of the
induction, as appropriate.

The form
```
fun_induction f
```
(with no arguments to `f`) searches the goal for a unique eligible application of `f`, and uses
these arguments. An application of `f` is eligible if it is saturated and the arguments that will
become targets are free variables.

The forms `fun_induction f x y generalizing z₁ ... zₙ` and
`fun_induction f x y with | case1 => tac₁ | case2 x' ih => tac₂` work like with `induction.`

Under `set_option tactic.fun_induction.unfolding true` (the default), `fun_induction` uses the
`f.induct_unfolding` induction principle, which will try to automatically unfold the call to `f` in
the goal. With `set_option tactic.fun_induction.unfolding false`, it uses `f.induct` instead.

## fun_prop
Defined in: `Mathlib.Meta.FunProp.funPropTacStx`

`fun_prop` solves a goal of the form `P f`, where `P` is a predicate and `f` is a function,
by decomposing `f` into a composition of elementary functions, and proving `P` on each of those
by matching against a set of `@[fun_prop]` lemmas.

If `fun_prop` fails to solve a goal with the error "No theorems found", you can solve this issue
by importing or adding new theorems tagged with the `@[fun_prop]` attribute. See the module
documentation for `Mathlib/Tactic/FunProp.lean` for a detailed explanation.

* `fun_prop (disch := tac)` uses `tac` to solve potential side goals. Setting this option is
  required to solve `ContinuousAt/On/Within` goals.
* `fun_prop [c, ...]` will unfold the constant(s) `c`, ... before decomposing `f`.
* `fun_prop (config := cfg)` sets advanced configuration options using `cfg : FunProp.Config`
  (see `FunProp.Config` for details).
  These options can be combined: `fun_prop (config := cfg) (disch := tac) [c]`

Examples:

```lean
example : Continuous (fun x : ℝ ↦ x * sin x) := by fun_prop
```

```lean
-- Specify a discharger to solve `ContinuousAt`/`Within`/`On` goals:
example (y : ℝ) (hy : y ≠ 0) : ContinuousAt (fun x : ℝ ↦ 1/x) y := by
  fun_prop (disch := assumption)

example (y : ℝ) (hy : y ≠ 0) : ContinuousAt (fun x => x * (Real.log x) ^ 2 - Real.exp x / x) y := by
  fun_prop (disch := aesop)
```

## funext
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

## gcongr
Defined in: `Mathlib.Tactic.GCongr.tacticGcongr___With___`

`gcongr` applies "generalized congruence" rules to recursively reduce a goal of form
`⊢ R (f a₁ ... aₙ) (f b₁ ... bₙ)` to (possibly multiple) goal(s) `⊢ Rᵢ aᵢ bᵢ`, keeping only the
distinct pairs `aᵢ ≠ bᵢ`, where `Rᵢ` is a possibly different relation (depending on the
precise rule). The relations `R`, `Rᵢ` can be any two-argument relation, including `· → ·`.

This tactic is extensible: to add a "generalized congruence" rule, tag a theorem with the attribute
`@[gcongr]`.

If a "generalized congruence" lemma has a side goal, `gcongr` will try to discharge it using
`gcongr_discharger`, which is an extensible tactic based on `positivity`. Side goals not discharged
in this way are left for the user.

* `gcongr with x y ... z` names the variables that are introduced by descending into binders (for
  example sums or suprema).
* `gcongr n`, where `n` is a natural number literal, limits the depth of the recursive applications.
  This is useful if `gcongr` is too aggressive in breaking down the goal.
* `gcongr t`, where `t` is a term with `?_` holes, performs congruence up to the holes in `t`.
  In other words, `gcongr f ?_` turns a goal `⊢ R (f x) (f y)` into `⊢ R x y` (but no further).
  This is useful if `gcongr` is too aggressive in breaking down the goal.

Examples:
```lean
example {a b x c d : ℝ} (h1 : a + 1 ≤ b + 1) (h2 : c + 2 ≤ d + 2) :
    x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  -- LHS and RHS both have the form x ^ 2 * ?_ + ?_
  gcongr
  · -- New goal: ⊢ a ≤ b
    linarith
  · -- ⊢ New goal: c ≤ d
    linarith
-- Resulting proof term is:
--   add_le_add (mul_le_mul_of_nonneg_left ?_ (Even.pow_nonneg (even_two_mul 1) x)) ?_
-- where `add_le_add` and `mul_le_mul_of_nonneg_left` are generalized congruence lemmas
-- and the side goal `0 ≤ x ^ 2` is discharged by `gcongr_discharger`.
```

```
example {a b c d x : ℝ} (h : a + c + 1 ≤ b + d + 1) :
    x ^ 2 * (a + c) + 5 ≤ x ^ 2 * (b + d) + 5 := by
  -- Using a pattern to limit the depth.
  gcongr x ^ 2 * ?_ + 5 -- or `gcongr 2`
  -- New goal: ⊢ a + c ≤ b + d
  linarith
```

```
-- Descending into binders (here: ⨆).
example {f g : ℕ → ℝ≥0∞} (h : ∀ n, f n ≤ g n) : ⨆ n, f n ≤ ⨆ n, g n := by
  gcongr with i
  exact h i
```

## gcongr?
Defined in: `tacticGcongr?`

Display a widget panel allowing to generate a `gcongr` call with holes specified by selecting
subexpressions in the goal.

## gcongr_discharger
Defined in: `Mathlib.Tactic.GCongr.tacticGcongr_discharger`

`gcongr_discharger` is used by `gcongr` to discharge side goals.

This is an extensible tactic using [`macro_rules`](https://lean-lang.org/doc/reference/4.29.0/find/?domain=Verso.Genre.Manual.section&name=tactic-macro-extension).
By default it calls `positivity` (after importing the `positivity` tactic).
Example: ``macro_rules | `(tactic| gcongr_discharger) => `(tactic| positivity)``.

## generalize
Defined in: `Lean.Parser.Tactic.generalize`

* `generalize ([h :] e = x),+` replaces all occurrences `e`s in the main goal
  with a fresh hypothesis `x`s. If `h` is given, `h : e = x` is introduced as well.
* `generalize e = x at h₁ ... hₙ` also generalizes occurrences of `e`
  inside `h₁`, ..., `hₙ`.
* `generalize e = x at *` will generalize occurrences of `e` everywhere.

## generalize'
Defined in: `«tacticGeneralize'_:_=_»`

Backwards compatibility shim for `generalize`.

## generalize_proofs
Defined in: `Batteries.Tactic.generalizeProofsElab`

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
To disable this, use `generalize_proofs -abstract`.
The tactic is also set to recursively abstract proofs from the types of the generalized proofs.
This can be controlled with the `maxDepth` configuration option,
with `generalize_proofs (config := { maxDepth := 0 })` turning this feature off.

For example:
```lean
def List.nthLe {α} (l : List α) (n : ℕ) (_h : n < l.length) : α := sorry
example : List.nthLe [1, 2] 1 (by simp) = 2 := by
  -- ⊢ [1, 2].nthLe 1 ⋯ = 2
  generalize_proofs h
  -- h : 1 < [1, 2].length
  -- ⊢ [1, 2].nthLe 1 h = 2
```

## get_elem_tactic
Defined in: `tacticGet_elem_tactic`

`get_elem_tactic` is the tactic automatically called by the notation `arr[i]`
to prove any side conditions that arise when constructing the term
(e.g. the index is in bounds of the array). It just delegates to
`get_elem_tactic_extensible` and gives a diagnostic error message otherwise;
users are encouraged to extend `get_elem_tactic_extensible` instead of this tactic.

## get_elem_tactic_extensible
Defined in: `tacticGet_elem_tactic_extensible`

`get_elem_tactic_extensible` is an extensible tactic automatically called
by the notation `arr[i]` to prove any side conditions that arise when
constructing the term (e.g. the index is in bounds of the array).
The default behavior is to try `simp +arith` and `omega`
(for doing linear arithmetic in the index).

(Note that the core tactic `get_elem_tactic` has already tried
`done` and `assumption` before the extensible tactic is called.)

## get_elem_tactic_trivial
Defined in: `tacticGet_elem_tactic_trivial`

`get_elem_tactic_trivial` has been deprecated in favour of `get_elem_tactic_extensible`.

## ghost_calc
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

## ghost_fun_tac
Defined in: `WittVector.«tacticGhost_fun_tac_,_»`

An auxiliary tactic for proving that `ghostFun` respects the ring operations.

## ghost_simp
Defined in: `WittVector.Tactic.ghostSimp`

A macro for a common simplification when rewriting with ghost component equations.

## grewrite
Defined in: `Mathlib.Tactic.grewriteSeq`

`grewrite [e]` is like `grw [e]`, but it doesn't try to close the goal with `rfl`.
This is analogous to `rw` and `rewrite`, where `rewrite` doesn't try to close the goal with `rfl`.

## grind
Defined in: `Lean.Parser.Tactic.grind`

`grind` is a tactic inspired by modern SMT solvers. **Picture a virtual whiteboard**:
every time grind discovers a new equality, inequality, or logical fact,
it writes it on the board, groups together terms known to be equal,
and lets each reasoning engine read from and contribute to the shared workspace.
These engines work together to handle equality reasoning, apply known theorems,
propagate new facts, perform case analysis, and run specialized solvers
for domains like linear arithmetic and commutative rings.

See [the reference manual's chapter on `grind`](https://lean-lang.org/doc/reference/4.29.0/find/?domain=Verso.Genre.Manual.section&name=grind-tactic) for more information.

`grind` is *not* designed for goals whose search space explodes combinatorially,
think large pigeonhole instances, graph‑coloring reductions, high‑order N‑queens boards,
or a 200‑variable Sudoku encoded as Boolean constraints.  Such encodings require
 thousands (or millions) of case‑splits that overwhelm `grind`’s branching search.

For **bit‑level or combinatorial problems**, consider using **`bv_decide`**.
`bv_decide` calls a state‑of‑the‑art SAT solver (CaDiCaL) and then returns a
*compact, machine‑checkable certificate*.

### Equality reasoning

`grind` uses **congruence closure** to track equalities between terms.
When two terms are known to be equal, congruence closure automatically deduces
equalities between more complex expressions built from them.
For example, if `a = b`, then congruence closure will also conclude that `f a` = `f b`
for any function `f`. This forms the foundation for efficient equality reasoning in `grind`.
Here is an example:
```lean
example (f : Nat → Nat) (h : a = b) : f (f b) = f (f a) := by
  grind
```

### Applying theorems using E-matching

To apply existing theorems, `grind` uses a technique called **E-matching**,
which finds matches for known theorem patterns while taking equalities into account.
Combined with congruence closure, E-matching helps `grind` discover
non-obvious consequences of theorems and equalities automatically.

Consider the following functions and theorems:
```lean
def f (a : Nat) : Nat :=
  a + 1

def g (a : Nat) : Nat :=
  a - 1

@[grind =]
theorem gf (x : Nat) : g (f x) = x := by
  simp [f, g]
```
The theorem `gf` asserts that `g (f x) = x` for all natural numbers `x`.
The attribute `[grind =]` instructs `grind` to use the left-hand side of the equation,
`g (f x)`, as a pattern for E-matching.
Suppose we now have a goal involving:
```lean
example {a b} (h : f b = a) : g a = b := by
  grind
```
Although `g a` is not an instance of the pattern `g (f x)`,
it becomes one modulo the equation `f b = a`. By substituting `a`
with `f b` in `g a`, we obtain the term `g (f b)`,
which matches the pattern `g (f x)` with the assignment `x := b`.
Thus, the theorem `gf` is instantiated with `x := b`,
and the new equality `g (f b) = b` is asserted.
`grind` then uses congruence closure to derive the implied equality
`g a = g (f b)` and completes the proof.

The pattern used to instantiate theorems affects the effectiveness of `grind`.
For example, the pattern `g (f x)` is too restrictive in the following case:
the theorem `gf` will not be instantiated because the goal does not even
contain the function symbol `g`.

```
example (h₁ : f b = a) (h₂ : f c = a) : b = c := by
  grind
```

You can use the command `grind_pattern` to manually select a pattern for a given theorem.
In the following example, we instruct `grind` to use `f x` as the pattern,
allowing it to solve the goal automatically:
```lean
grind_pattern gf => f x

example {a b c} (h₁ : f b = a) (h₂ : f c = a) : b = c := by
  grind
```
You can enable the option `trace.grind.ematch.instance` to make `grind` print a
trace message for each theorem instance it generates.

You can also specify a **multi-pattern** to control when `grind` should apply a theorem.
A multi-pattern requires that all specified patterns are matched in the current context
before the theorem is applied. This is useful for theorems such as transitivity rules,
where multiple premises must be simultaneously present for the rule to apply.
The following example demonstrates this feature using a transitivity axiom for a binary relation `R`:
```lean
opaque R : Int → Int → Prop
axiom Rtrans {x y z : Int} : R x y → R y z → R x z

grind_pattern Rtrans => R x y, R y z

example {a b c d} : R a b → R b c → R c d → R a d := by
  grind
```
By specifying the multi-pattern `R x y, R y z`, we instruct `grind` to
instantiate `Rtrans` only when both `R x y` and `R y z` are available in the context.
In the example, `grind` applies `Rtrans` to derive `R a c` from `R a b` and `R b c`,
and can then repeat the same reasoning to deduce `R a d` from `R a c` and `R c d`.

Instead of using `grind_pattern` to explicitly specify a pattern,
you can use the `@[grind]` attribute or one of its variants, which will use a heuristic to
generate a (multi-)pattern. The complete list is available in the reference manual. The main ones are:

- `@[grind →]` will select a multi-pattern from the hypotheses of the theorem (i.e. it will use the theorem for forwards reasoning).
  In more detail, it will traverse the hypotheses of the theorem from left-to-right, and each time it encounters a minimal indexable
  (i.e. has a constant as its head) subexpression which "covers" (i.e. fixes the value of) an argument which was not
  previously covered, it will add that subexpression as a pattern, until all arguments have been covered.
- `@[grind ←]` will select a multi-pattern from the conclusion of theorem (i.e. it will use the theorem for backwards reasoning).
  This may fail if not all the arguments to the theorem appear in the conclusion.
- `@[grind]` will traverse the conclusion and then the hypotheses left-to-right, adding patterns as they increase the coverage,
  stopping when all arguments are covered.
- `@[grind =]` checks that the conclusion of the theorem is an equality, and then uses the left-hand-side of the equality as a pattern.
  This may fail if not all of the arguments appear in the left-hand-side.

Here is the previous example again but using the attribute `[grind →]`
```
opaque R : Int → Int → Prop
@[grind →] axiom Rtrans {x y z : Int} : R x y → R y z → R x z

example {a b c d} : R a b → R b c → R c d → R a d := by
  grind
```

To control theorem instantiation and avoid generating an unbounded number of instances,
`grind` uses a generation counter. Terms in the original goal are assigned generation zero.
When `grind` applies a theorem using terms of generation `≤ n`, any new terms it creates
are assigned generation `n + 1`. This limits how far the tactic explores when applying
theorems and helps prevent an excessive number of instantiations.

#### Key options:
- `grind (ematch := <num>)` controls the number of E-matching rounds.
- `grind [<name>, ...]` instructs `grind` to use the declaration `name` during E-matching.
- `grind only [<name>, ...]` is like `grind [<name>, ...]` but does not use theorems tagged with `@[grind]`.
- `grind (gen := <num>)` sets the maximum generation.

### Linear integer arithmetic (`lia`)

`grind` can solve goals that reduce to **linear integer arithmetic (LIA)** using an
integrated decision procedure called **`lia`**.  It understands

* equalities   `p = 0`
* inequalities  `p ≤ 0`
* disequalities `p ≠ 0`
* divisibility  `d ∣ p`

The solver incrementally assigns integer values to variables; when a partial
assignment violates a constraint it adds a new, implied constraint and retries.
This *model-based* search is **complete for LIA**.

#### Key options:

* `grind -lia` disable the solver (useful for debugging)
* `grind +qlia` accept rational models (shrinks the search space but is incomplete for ℤ)

#### Examples:

```
-- Even + even is never odd.
example {x y : Int} : 2 * x + 4 * y ≠ 5 := by
  grind

-- Mixing equalities and inequalities.
example {x y : Int} :
    2 * x + 3 * y = 0 → 1 ≤ x → y < 1 := by
  grind

-- Reasoning with divisibility.
example (a b : Int) :
    2 ∣ a + 1 → 2 ∣ b + a → ¬ 2 ∣ b + 2 * a := by
  grind

example (x y : Int) :
    27 ≤ 11*x + 13*y →
    11*x + 13*y ≤ 45 →
    -10 ≤ 7*x - 9*y →
    7*x - 9*y ≤ 4 → False := by
  grind

-- Types that implement the `ToInt` type-class.
example (a b c : UInt64)
    : a ≤ 2 → b ≤ 3 → c - a - b = 0 → c ≤ 5 := by
  grind
```

### Algebraic solver (`ring`)

`grind` ships with an algebraic solver nick-named **`ring`** for goals that can
be phrased as polynomial equations (or disequations) over commutative rings,
semirings, or fields.

*Works out of the box*
All core numeric types and relevant Mathlib types already provide the required
type-class instances, so the solver is ready to use in most developments.

What it can decide:

* equalities of the form `p = q`
* disequalities `p ≠ q`
* basic reasoning under field inverses (`a / b := a * b⁻¹`)
* goals that mix ring facts with other `grind` engines

#### Key options:

* `grind -ring` turn the solver off (useful when debugging)
* `grind (ringSteps := n)` cap the number of steps performed by this procedure.

#### Examples

```
open Lean Grind

example [CommRing α] (x : α) : (x + 1) * (x - 1) = x^2 - 1 := by
  grind

-- Characteristic 256 means 16 * 16 = 0.
example [CommRing α] [IsCharP α 256] (x : α) :
    (x + 16) * (x - 16) = x^2 := by
  grind

-- Works on built-in rings such as `UInt8`.
example (x : UInt8) : (x + 16) * (x - 16) = x^2 := by
  grind

example [CommRing α] (a b c : α) :
    a + b + c = 3 →
    a^2 + b^2 + c^2 = 5 →
    a^3 + b^3 + c^3 = 7 →
    a^4 + b^4 = 9 - c^4 := by
  grind

example [Field α] [NoNatZeroDivisors α] (a : α) :
    1 / a + 1 / (2 * a) = 3 / (2 * a) := by
  grind
```

### Other options

- `grind (splits := <num>)` caps the *depth* of the search tree.  Once a branch performs `num` splits
  `grind` stops splitting further in that branch.
- `grind -splitIte` disables case splitting on if-then-else expressions.
- `grind -splitMatch` disables case splitting on `match` expressions.
- `grind +splitImp` instructs `grind` to split on any hypothesis `A → B` whose antecedent `A` is **propositional**.
- `grind -linarith` disables the linear arithmetic solver for (ordered) modules and rings.

### Additional Examples

```
example {a b} {as bs : List α} : (as ++ bs ++ [b]).getLastD a = b := by
  grind

example (x : BitVec (w+1)) : (BitVec.cons x.msb (x.setWidth w)) = x := by
  grind

example (as : Array α) (lo hi i j : Nat) :
    lo ≤ i → i < j → j ≤ hi → j < as.size → min lo (as.size - 1) ≤ i := by
  grind
```

## grind?
Defined in: `Lean.Parser.Tactic.grindTrace`

`grind?` takes the same arguments as `grind`, but reports an equivalent call to `grind only`
that would be sufficient to close the goal. This is useful for reducing the size of the `grind`
theorems in a local invocation.

## grind_linarith
Defined in: `Lean.Parser.Tactic.grind_linarith`

`grind_linarith` solves simple goals about linear arithmetic.

It is a implemented as a thin wrapper around the `grind` tactic, enabling only the `linarith` solver.
Please use `grind` instead if you need additional capabilities.

## grind_order
Defined in: `Lean.Parser.Tactic.grind_order`

`grind_order` solves simple goals about partial orders and linear orders.

It is a implemented as a thin wrapper around the `grind` tactic, enabling only the `order` solver.
Please use `grind` instead if you need additional capabilities.

## grobner
Defined in: `Lean.Parser.Tactic.grobner`

`grobner` solves goals that can be phrased as polynomial equations (with further polynomial equations as hypotheses)
over commutative (semi)rings, using the Grobner basis algorithm.

It is a implemented as a thin wrapper around the `grind` tactic, enabling only the `grobner` solver.
Please use `grind` instead if you need additional capabilities.

## group
Defined in: `Mathlib.Tactic.Group.group`

`group` normalizes expressions in multiplicative groups that occur in the goal. `group` does not
assume commutativity, instead using only the group axioms without any information about which group
is manipulated. If the goal is an equality, and after normalization the two sides are equal, `group`
closes the goal.

For additive commutative groups, use the `abel` tactic instead.

* `group at l1 l2 ...` normalizes at the given locations.

Example:
```lean
example {G : Type} [Group G] (a b c d : G) (h : c = (a*b^2)*((b*b)⁻¹*a⁻¹)*d) : a*c*d⁻¹ = a := by
  group at h -- normalizes `h` which becomes `h : c = d`
  rw [h]     -- the goal is now `a*d*d⁻¹ = a`
  group      -- which then normalized and closed
```

## grw
Defined in: `Mathlib.Tactic.grwSeq`

`grw [e]` works just like `rw [e]`, but `e` can be a relation other than `=` or `↔`.

For example:

```lean
variable {a b c d n : ℤ}

example (h₁ : a < b) (h₂ : b ≤ c) : a + d ≤ c + d := by
  grw [h₁, h₂]

example (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n] := by
  grw [h]

example (h₁ : a ∣ b) (h₂ : b ∣ a ^ 2 * c) : a ∣ b ^ 2 * c := by
  grw [h₁] at *
  exact h₂
```

To replace the RHS with the LHS of the given relation, use the `←` notation (just like in `rw`):

```
example (h₁ : a < b) (h₂ : b ≤ c) : a + d ≤ c + d := by
  grw [← h₂, ← h₁]
```

The strict inequality `a < b` is turned into the non-strict inequality `a ≤ b` to rewrite with it.
A future version of `grw` may get special support for making better use of strict inequalities.

To rewrite only in the `n`-th position, use `nth_grw n`.
This is useful when `grw` tries to rewrite in a position that is not valid for the given relation.

To be able to use `grw`, the relevant lemmas need to be tagged with `@[gcongr]`.
To rewrite inside a transitive relation, you can also give it an `IsTrans` instance.

To let `grw` unfold more aggressively, as in `erw`, use `grw (transparency := default)`.

## guard_expr
Defined in: `Lean.Parser.Tactic.guardExpr`

Tactic to check equality of two expressions.
* `guard_expr e = e'` checks that `e` and `e'` are defeq at reducible transparency.
* `guard_expr e =~ e'` checks that `e` and `e'` are defeq at default transparency.
* `guard_expr e =ₛ e'` checks that `e` and `e'` are syntactically equal.
* `guard_expr e =ₐ e'` checks that `e` and `e'` are alpha-equivalent.

Both `e` and `e'` are elaborated then have their metavariables instantiated before the equality
check. Their types are unified (using `isDefEqGuarded`) before synthetic metavariables are
processed, which helps with default instance handling.

## guard_goal_nums
Defined in: `guardGoalNums`

`guard_goal_nums n` succeeds if there are exactly `n` goals and fails otherwise.

## guard_hyp
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

## guard_hyp_nums
Defined in: `guardHypNums`

`guard_hyp_nums n` succeeds if there are exactly `n` hypotheses and fails otherwise.

Note that, depending on what options are set, some hypotheses in the local context might
not be printed in the goal view. This tactic computes the total number of hypotheses,
not the number of visible hypotheses.

## guard_target
Defined in: `Lean.Parser.Tactic.guardTarget`

Tactic to check that the target agrees with a given expression.
* `guard_target = e` checks that the target is defeq at reducible transparency to `e`.
* `guard_target =~ e` checks that the target is defeq at default transparency to `e`.
* `guard_target =ₛ e` checks that the target is syntactically equal to `e`.
* `guard_target =ₐ e` checks that the target is alpha-equivalent to `e`.

The term `e` is elaborated with the type of the goal as the expected type, which is mostly
useful within `conv` mode.

## have
Defined in: `Mathlib.Tactic.tacticHave_`

The `have` tactic is for adding opaque definitions and hypotheses to the local context of the main goal.
The definitions forget their associated value and cannot be unfolded, unlike definitions added by the `let` tactic.

* `have h : t := e` adds the hypothesis `h : t` if `e` is a term of type `t`.
* `have h := e` uses the type of `e` for `t`.
* `have : t := e` and `have := e` use `this` for the name of the hypothesis.
* `have pat := e` for a pattern `pat` is equivalent to `match e with | pat => _`,
  where `_` stands for the tactics that follow this one.
  It is convenient for types that have only one applicable constructor.
  For example, given `h : p ∧ q ∧ r`, `have ⟨h₁, h₂, h₃⟩ := h` produces the
  hypotheses `h₁ : p`, `h₂ : q`, and `h₃ : r`.
* The syntax `have (eq := h) pat := e` is equivalent to `match h : e with | pat => _`,
  which adds the equation `h : e = pat` to the local context.

The tactic supports all the same syntax variants and options as the `have` term.

## Properties and relations

* It is not possible to unfold a variable introduced using `have`, since the definition's value is forgotten.
  The `let` tactic introduces definitions that can be unfolded.
* The `have h : t := e` is like doing `let h : t := e; clear_value h`.
* The `have` tactic is preferred for propositions, and `let` is preferred for non-propositions.
* Sometimes `have` is used for non-propositions to ensure that the variable is never unfolded,
  which may be important for performance reasons.
    Consider using the equivalent `let +nondep` to indicate the intent.

## have
Defined in: `Lean.Parser.Tactic.tacticHave__`

The `have` tactic is for adding opaque definitions and hypotheses to the local context of the main goal.
The definitions forget their associated value and cannot be unfolded, unlike definitions added by the `let` tactic.

* `have h : t := e` adds the hypothesis `h : t` if `e` is a term of type `t`.
* `have h := e` uses the type of `e` for `t`.
* `have : t := e` and `have := e` use `this` for the name of the hypothesis.
* `have pat := e` for a pattern `pat` is equivalent to `match e with | pat => _`,
  where `_` stands for the tactics that follow this one.
  It is convenient for types that have only one applicable constructor.
  For example, given `h : p ∧ q ∧ r`, `have ⟨h₁, h₂, h₃⟩ := h` produces the
  hypotheses `h₁ : p`, `h₂ : q`, and `h₃ : r`.
* The syntax `have (eq := h) pat := e` is equivalent to `match h : e with | pat => _`,
  which adds the equation `h : e = pat` to the local context.

The tactic supports all the same syntax variants and options as the `have` term.

## Properties and relations

* It is not possible to unfold a variable introduced using `have`, since the definition's value is forgotten.
  The `let` tactic introduces definitions that can be unfolded.
* The `have h : t := e` is like doing `let h : t := e; clear_value h`.
* The `have` tactic is preferred for propositions, and `let` is preferred for non-propositions.
* Sometimes `have` is used for non-propositions to ensure that the variable is never unfolded,
  which may be important for performance reasons.
    Consider using the equivalent `let +nondep` to indicate the intent.

## have'
Defined in: `Lean.Parser.Tactic.tacticHave'`

Similar to `have`, but using `refine'`

## haveI
Defined in: `Lean.Parser.Tactic.tacticHaveI__`

`haveI` behaves like `have`, but inlines the value instead of producing a `have` term.

## hint
Defined in: `Mathlib.Tactic.Hint.hintStx`

The `hint` tactic tries every tactic registered using `register_hint <prio> tac`,
and reports any that succeed.

## ident
Defined in: `Lean.Parser.Tactic.unknown`


## if
Defined in: `Lean.Parser.Tactic.tacDepIfThenElse`

In tactic mode, `if t then tac1 else tac2` is alternative syntax for:
```lean
by_cases t
· tac1
· tac2
```
It performs case distinction on `h† : t` or `h† : ¬t`, where `h†` is an anonymous hypothesis, and
`tac1` and `tac2` are the subproofs. (It doesn't actually use nondependent `if`, since this wouldn't
add anything to the context and hence would be useless for proving theorems. To actually insert an
`ite` application use `refine if t then ?_ else ?_`.)

The assumptions in each subgoal can be named. `if h : t then tac1 else tac2` can be used as
alternative syntax for:
```lean
by_cases h : t
· tac1
· tac2
```
It performs case distinction on `h : t` or `h : ¬t`.

You can use `?_` or `_` for either subproof to delay the goal to after the tactic, but
if a tactic sequence is provided for `tac1` or `tac2` then it will require the goal to be closed
by the end of the block.

## if
Defined in: `Lean.Parser.Tactic.tacIfThenElse`

In tactic mode, `if t then tac1 else tac2` is alternative syntax for:
```lean
by_cases t
· tac1
· tac2
```
It performs case distinction on `h† : t` or `h† : ¬t`, where `h†` is an anonymous hypothesis, and
`tac1` and `tac2` are the subproofs. (It doesn't actually use nondependent `if`, since this wouldn't
add anything to the context and hence would be useless for proving theorems. To actually insert an
`ite` application use `refine if t then ?_ else ?_`.)

The assumptions in each subgoal can be named. `if h : t then tac1 else tac2` can be used as
alternative syntax for:
```lean
by_cases h : t
· tac1
· tac2
```
It performs case distinction on `h : t` or `h : ¬t`.

You can use `?_` or `_` for either subproof to delay the goal to after the tactic, but
if a tactic sequence is provided for `tac1` or `tac2` then it will require the goal to be closed
by the end of the block.

## induction
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

## induction'
Defined in: `Mathlib.Tactic.induction'`

`induction' x` applies induction on the variable `x` of the inductive type `t` to the main goal,
producing one goal for each constructor of `t`, in which `x` is replaced by that constructor
applied to newly introduced variables. `induction'` adds an inductive hypothesis for
each recursive argument to the constructor. This is a backwards-compatible variant of the
`induction` tactic in Lean 4 core.

Prefer `induction` when possible, because it promotes structured proofs.

* `induction' x with n1 n2 ...` names the introduced hypotheses: arguments to constructors and
  inductive hypotheses. This is the main difference with `induction` in core Lean.
* `induction' e`, where `e` is an expression instead of a variable, generalizes `e` in the goal,
  and then performs induction on the resulting variable.
* `induction' h : e`, where `e` is an expression instead of a variable, generalizes `e` in the goal,
  and then performs induction on the resulting variable, adding to each goal the hypothesis
  `h : e = _` where `_` is the constructor instance.
* `induction' x using r` uses `r` as the principle of induction. Here `r` should be a term whose
  result type is of the form `C t1 t2 ...`, where `C` is a bound variable and `t1`, `t2`, ... (if
  present) are bound variables.
* `induction' x generalizing z1 z2 ...` generalizes over the local variables `z1`, `z2`, ... in the
  inductive hypothesis.

Example:
```lean
open Nat

example (n : ℕ) : 0 < factorial n := by
  induction' n with n ih
  · rw [factorial_zero]
    simp
  · rw [factorial_succ]
    apply mul_pos (succ_pos n) ih

-- Though the following equivalent spellings should be preferred
example (n : ℕ) : 0 < factorial n := by
  induction n
  case zero =>
    rw [factorial_zero]
    simp
  case succ n ih =>
    rw [factorial_succ]
    apply mul_pos (succ_pos n) ih
```

## infer_instance
Defined in: `Lean.Parser.Tactic.tacticInfer_instance`

`infer_instance` is an abbreviation for `exact inferInstance`.
It synthesizes a value of any target type by typeclass inference.

## infer_param
Defined in: `Mathlib.Tactic.inferOptParam`

Close a goal of the form `optParam α a` or `autoParam α stx` by using `a`.

## inhabit
Defined in: `Lean.Elab.Tactic.inhabit`

`inhabit α` tries to derive a `Nonempty α` instance and
then uses it to make an `Inhabited α` instance.
If the target is a `Prop`, this is done constructively. Otherwise, it uses `Classical.choice`.

## init_ring
Defined in: `WittVector.initRing`

`init_ring` is an auxiliary tactic that discharges goals factoring `init` over ring operations.

## injection
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

## injections
Defined in: `Lean.Parser.Tactic.injections`

`injections` applies `injection` to all hypotheses recursively
(since `injection` can produce new hypotheses). Useful for destructing nested
constructor equalities like `(a::b::c) = (d::e::f)`.

## interval_cases
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

## intro
Defined in: `Batteries.Tactic.introDot`

The syntax `intro.` is deprecated in favor of `nofun`.

## intro
Defined in: `Lean.Parser.Tactic.intro`

Introduces one or more hypotheses, optionally naming and/or pattern-matching them.
For each hypothesis to be introduced, the remaining main goal's target type must
be a `let` or function type.

* `intro` by itself introduces one anonymous hypothesis, which can be accessed
  by e.g. `assumption`. It is equivalent to `intro _`.
* `intro x y` introduces two hypotheses and names them. Individual hypotheses
  can be anonymized via `_`, given a type ascription, or matched against a pattern:
  ```lean
  -- ... ⊢ α × β → ...
  intro (a, b)
  -- ..., a : α, b : β ⊢ ...
  ```
* `intro rfl` is short for `intro h; subst h`, if `h` is an equality where the left-hand or right-hand side
  is a variable.
* Alternatively, `intro` can be combined with pattern matching much like `fun`:
  ```lean
  intro
  | n + 1, 0 => tac
  | ...
  ```

## intro
Defined in: `Lean.Parser.Tactic.introMatch`

Introduces one or more hypotheses, optionally naming and/or pattern-matching them.
For each hypothesis to be introduced, the remaining main goal's target type must
be a `let` or function type.

* `intro` by itself introduces one anonymous hypothesis, which can be accessed
  by e.g. `assumption`. It is equivalent to `intro _`.
* `intro x y` introduces two hypotheses and names them. Individual hypotheses
  can be anonymized via `_`, given a type ascription, or matched against a pattern:
  ```lean
  -- ... ⊢ α × β → ...
  intro (a, b)
  -- ..., a : α, b : β ⊢ ...
  ```
* `intro rfl` is short for `intro h; subst h`, if `h` is an equality where the left-hand or right-hand side
  is a variable.
* Alternatively, `intro` can be combined with pattern matching much like `fun`:
  ```lean
  intro
  | n + 1, 0 => tac
  | ...
  ```

## intros
Defined in: `Lean.Parser.Tactic.intros`

`intros` repeatedly applies `intro` to introduce zero or more hypotheses
until the goal is no longer a *binding expression*
(i.e., a universal quantifier, function type, implication, or `have`/`let`),
without performing any definitional reductions (no unfolding, beta, eta, etc.).
The introduced hypotheses receive inaccessible (hygienic) names.

`intros x y z` is equivalent to `intro x y z` and exists only for historical reasons.
The `intro` tactic should be preferred in this case.

## Properties and relations

- `intros` succeeds even when it introduces no hypotheses.

- `repeat intro` is like `intros`, but it performs definitional reductions
  to expose binders, and as such it may introduce more hypotheses than `intros`.

- `intros` is equivalent to `intro _ _ … _`,
  with the fewest trailing `_` placeholders needed so that the goal is no longer a binding expression.
  The trailing introductions do not perform any definitional reductions.

## Examples

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

Let-bindings:
```lean
example : let n := 1; let k := 2; n + k = 3 := by
  intros
  /- n✝ : Nat := 1
     k✝ : Nat := 2
     ⊢ n✝ + k✝ = 3 -/
  rfl
```

Does not unfold definitions:
```lean
def AllEven (f : Nat → Nat) := ∀ n, f n % 2 = 0

example : ∀ (f : Nat → Nat), AllEven f → AllEven (fun k => f (k + 1)) := by
  intros
  /- Tactic state
     f✝ : Nat → Nat
     a✝ : AllEven f✝
     ⊢ AllEven fun k => f✝ (k + 1) -/
  sorry
```

## introv
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

## isBoundedDefault
Defined in: `Filter.tacticIsBoundedDefault`

Filters are automatically bounded or cobounded in complete lattices. To use the same statements
in complete and conditionally complete lattices but let automation fill automatically the
boundedness proofs in complete lattices, we use the tactic `isBoundedDefault` in the statements,
in the form `(hf : f.IsBounded (≥) := by isBoundedDefault)`.

## itauto
Defined in: `Mathlib.Tactic.ITauto.itauto`

`itauto` solves the main goal when it is a tautology of intuitionistic propositional logic.
Unlike `grind` and `tauto!` this tactic never uses the law of excluded middle (without the `!`
option), and the proof search is tailored for this use case. `itauto` is complete for intuitionistic
propositional logic: it will solve any goal that is provable in this logic.

* `itauto [a, b]` will additionally attempt case analysis on `a` and `b` assuming that it can derive
  `Decidable a` and `Decidable b`.
* `itauto *` will case on all decidable propositions that it can find among the atomic propositions.
* `itauto!` will work as a classical SAT solver, but the algorithm is not very good in this
  situation.
* `itauto! *` will case on all propositional atoms. *Warning:* This can blow up the proof search, so
  it should be used sparingly.

Example:
```lean
example (p : Prop) : ¬ (p ↔ ¬ p) := by itauto
```

## itauto!
Defined in: `Mathlib.Tactic.ITauto.itauto!`

`itauto` solves the main goal when it is a tautology of intuitionistic propositional logic.
Unlike `grind` and `tauto!` this tactic never uses the law of excluded middle (without the `!`
option), and the proof search is tailored for this use case. `itauto` is complete for intuitionistic
propositional logic: it will solve any goal that is provable in this logic.

* `itauto [a, b]` will additionally attempt case analysis on `a` and `b` assuming that it can derive
  `Decidable a` and `Decidable b`.
* `itauto *` will case on all decidable propositions that it can find among the atomic propositions.
* `itauto!` will work as a classical SAT solver, but the algorithm is not very good in this
  situation.
* `itauto! *` will case on all propositional atoms. *Warning:* This can blow up the proof search, so
  it should be used sparingly.

Example:
```lean
example (p : Prop) : ¬ (p ↔ ¬ p) := by itauto
```

## iterate
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

## left
Defined in: `Lean.Parser.Tactic.left`

Applies the first constructor when
the goal is an inductive type with exactly two constructors, or fails otherwise.
```lean
example : True ∨ False := by
  left
  trivial
```

## let
Defined in: `Lean.Parser.Tactic.tacticLet__`

The `let` tactic is for adding definitions to the local context of the main goal.
The definition can be unfolded, unlike definitions introduced by `have`.

* `let x : t := e` adds the definition `x : t := e` if `e` is a term of type `t`.
* `let x := e` uses the type of `e` for `t`.
* `let : t := e` and `let := e` use `this` for the name of the hypothesis.
* `let pat := e` for a pattern `pat` is equivalent to `match e with | pat => _`,
  where `_` stands for the tactics that follow this one.
  It is convenient for types that let only one applicable constructor.
  For example, given `p : α × β × γ`, `let ⟨x, y, z⟩ := p` produces the
  local variables `x : α`, `y : β`, and `z : γ`.
* The syntax `let (eq := h) pat := e` is equivalent to `match h : e with | pat => _`,
  which adds the equation `h : e = pat` to the local context.

The tactic supports all the same syntax variants and options as the `let` term.

## Properties and relations

* Unlike `have`, it is possible to unfold definitions introduced using `let`, using tactics
  such as `simp`, `dsimp`, `unfold`, and `subst`.
* The `clear_value` tactic turns a `let` definition into a `have` definition after the fact.
  The tactic might fail if the local context depends on the value of the variable.
* The `let` tactic is preferred for data (non-propositions).
* Sometimes `have` is used for non-propositions to ensure that the variable is never unfolded,
  which may be important for performance reasons.

## let
Defined in: `Lean.Parser.Tactic.letrec`

`let rec f : t := e` adds a recursive definition `f` to the current goal.
The syntax is the same as term-mode `let rec`.

The tactic supports all the same syntax variants and options as the `let` term.

## let
Defined in: `Mathlib.Tactic.tacticLet_`

The `let` tactic is for adding definitions to the local context of the main goal.
The definition can be unfolded, unlike definitions introduced by `have`.

* `let x : t := e` adds the definition `x : t := e` if `e` is a term of type `t`.
* `let x := e` uses the type of `e` for `t`.
* `let : t := e` and `let := e` use `this` for the name of the hypothesis.
* `let pat := e` for a pattern `pat` is equivalent to `match e with | pat => _`,
  where `_` stands for the tactics that follow this one.
  It is convenient for types that let only one applicable constructor.
  For example, given `p : α × β × γ`, `let ⟨x, y, z⟩ := p` produces the
  local variables `x : α`, `y : β`, and `z : γ`.
* The syntax `let (eq := h) pat := e` is equivalent to `match h : e with | pat => _`,
  which adds the equation `h : e = pat` to the local context.

The tactic supports all the same syntax variants and options as the `let` term.

## Properties and relations

* Unlike `have`, it is possible to unfold definitions introduced using `let`, using tactics
  such as `simp`, `dsimp`, `unfold`, and `subst`.
* The `clear_value` tactic turns a `let` definition into a `have` definition after the fact.
  The tactic might fail if the local context depends on the value of the variable.
* The `let` tactic is preferred for data (non-propositions).
* Sometimes `have` is used for non-propositions to ensure that the variable is never unfolded,
  which may be important for performance reasons.

## let'
Defined in: `Lean.Parser.Tactic.tacticLet'__`

Similar to `let`, but using `refine'`

## letI
Defined in: `Lean.Parser.Tactic.tacticLetI__`

`letI` behaves like `let`, but inlines the value instead of producing a `let` term.

## let_to_have
Defined in: `Lean.Parser.Tactic.letToHave`

Transforms `let` expressions into `have` expressions when possible.
- `let_to_have` transforms `let`s in the target.
- `let_to_have at h` transforms `let`s in the given local hypothesis.

## lia
Defined in: `Lean.Parser.Tactic.lia`

`lia` solves linear integer arithmetic goals.

It is a implemented as a thin wrapper around the `grind` tactic, enabling only the `lia` solver.
Please use `grind` instead if you need additional capabilities.

## lift
Defined in: `Mathlib.Tactic.lift`

`lift e to t with x` lifts the expression `e` to the type `t` by introducing a new variable `x : t`
such that `↑x = e`, and then replacing occurrences of `e` with `↑x`. `lift` requires an instance of
the class `CanLift t' t coe cond`, where `t'` is the type of `e`, and creates a side goal for the
lifting condition, of the form `⊢ cond x`, placing this on top of the goal stack.

Given an instance `CanLift β γ`, `lift` can also lift `α → β` to `α → γ`; more generally, given
`β : Π a : α, Type*`, `γ : Π a : α, Type*`, and `[Π a : α, CanLift (β a) (γ a)]`, it
automatically generates an instance `CanLift (Π a, β a) (Π a, γ a)`.

`lift` is in some sense dual to the `zify` tactic. `lift (z : ℤ) to ℕ` will change the type of an
integer `z` (in the supertype) to `ℕ` (the subtype), given a proof that `z ≥ 0`;
propositions concerning `z` will still be over `ℤ`. `zify` changes propositions about `ℕ` (the
subtype) to propositions about `ℤ` (the supertype), without changing the type of any variable.

The `norm_cast` tactic can be used after `lift` to normalize introduced casts.

* `lift e to t using h with x` uses the expression `h` to prove the lifting condition `cond e`.
  If `h` is a variable, `lift` will try to clear it from the context. If you want to keep `h` in
  the context, write `lift e to t using h with x rfl h` (see below).
* If `e` is a variable, `lift e to t` is equivalent to `lift e to t with e`. The original variable
  `e` will be cleared from the context.
* `lift e to t with x hx` adds `hx : ↑x = e` to the context (and if `e` is a variable, does not
  clear it).
* `lift e to t with x hx h` adds `hx : ↑x = e` and `h : cond e` to the context (and if `e` is a
  variable, does not clear it). In particular, `lift e to t using h with x hx h`, where `h` is a
  variable, keeps `h` in the context.
* `lift e to t with x rfl h` adds `h : cond e` to the context (and if `e` is a variable, does not
  clear it). In particular, `lift e to t using h with x rfl h`, where `h` is a variable, keeps `h`
  in the context.

Examples:
```lean
def P (n : ℤ) : Prop := n = 3

example (n : ℤ) (h : P n) : n = 3 := by
  lift n to ℕ
  /-
  Two goals:
  n : ℤ, h : P n ⊢ n ≥ 0
  n : ℕ, h : P ↑n ⊢ ↑n = 3
  -/
  · unfold P at h; linarith
  · exact h

example (n : ℤ) (hn : n ≥ 0) (h : P n) : n = 3 := by
  lift n to ℕ using hn
  /-
  One goal:
  n : ℕ
  h : P ↑n
  ⊢ ↑n = 3
  -/
  exact h

example (n : ℤ) (hn : n + 3 ≥ 0) (h : P (n + 3)) :
    n + 3 = n * 2 + 3 := by
  lift n + 3 to ℕ using hn with k hk
  /-
  One goal:
  n : ℤ
  k : ℕ
  hk : ↑k = n + 3
  h : P ↑k
  ⊢ ↑k = 2 * n + 3
  -/
  unfold P at h; linarith
```

## lift_lets
Defined in: `Lean.Parser.Tactic.liftLets`

Lifts `let` and `have` expressions within a term as far out as possible.
It is like `extract_lets +lift`, but the top-level lets at the end of the procedure
are not extracted as local hypotheses.

- `lift_lets` lifts let expressions in the target.
- `lift_lets at h` lifts let expressions at the given local hypothesis.

For example,
```lean
example : (let x := 1; x) = 1 := by
  lift_lets
  -- ⊢ let x := 1; x = 1
  ...
```

## liftable_prefixes
Defined in: `Mathlib.Tactic.Coherence.liftable_prefixes`

Internal tactic used in `coherence`.

Rewrites an equation `f = g` as `f₀ ≫ f₁ = g₀ ≫ g₁`,
where `f₀` and `g₀` are maximal prefixes of `f` and `g` (possibly after reassociating)
which are "liftable" (i.e. expressible as compositions of unitors and associators).

## linarith
Defined in: `Mathlib.Tactic.linarith`

`linarith` attempts to find a contradiction between hypotheses that are linear (in)equalities.
Equivalently, it can prove a linear inequality by assuming its negation and proving `False`.

In theory, `linarith` should prove any goal that is true in the theory of linear arithmetic over
the rationals. While there is some special handling for non-dense orders like `Nat` and `Int`,
this tactic is not complete for these theories and will not prove every true goal. It will solve
goals over arbitrary types that instantiate `CommRing`, `LinearOrder` and `IsStrictOrderedRing`.

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
* If `minimize` is `false`, `linarith?` will report all hypotheses appearing in its initial
  proof without attempting to drop redundancies. (`true` by default.)
* `restrict_type` (not yet implemented in mathlib4)
  will only use hypotheses that are inequalities over `tp`. This is useful
  if you have e.g. both integer- and rational-valued inequalities in the local context, which can
  sometimes confuse the tactic.

A variant, `nlinarith`, does some basic preprocessing to handle some nonlinear goals.

The option `set_option trace.linarith true` will trace certain intermediate stages of the `linarith`
routine.

## linarith!
Defined in: `Mathlib.Tactic.tacticLinarith!_`

`linarith` attempts to find a contradiction between hypotheses that are linear (in)equalities.
Equivalently, it can prove a linear inequality by assuming its negation and proving `False`.

In theory, `linarith` should prove any goal that is true in the theory of linear arithmetic over
the rationals. While there is some special handling for non-dense orders like `Nat` and `Int`,
this tactic is not complete for these theories and will not prove every true goal. It will solve
goals over arbitrary types that instantiate `CommRing`, `LinearOrder` and `IsStrictOrderedRing`.

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
* If `minimize` is `false`, `linarith?` will report all hypotheses appearing in its initial
  proof without attempting to drop redundancies. (`true` by default.)
* `restrict_type` (not yet implemented in mathlib4)
  will only use hypotheses that are inequalities over `tp`. This is useful
  if you have e.g. both integer- and rational-valued inequalities in the local context, which can
  sometimes confuse the tactic.

A variant, `nlinarith`, does some basic preprocessing to handle some nonlinear goals.

The option `set_option trace.linarith true` will trace certain intermediate stages of the `linarith`
routine.

## linarith?
Defined in: `Mathlib.Tactic.linarith?`

`linarith?` behaves like `linarith` but, on success, it prints a suggestion of
the form `linarith only [...]` listing a minimized set of hypotheses used in the
final proof.  Use `linarith?!` for the higher-reducibility variant and set the
`minimize` flag in the configuration to control whether greedy minimization is
performed.

## linarith?!
Defined in: `Mathlib.Tactic.tacticLinarith?!_`

`linarith?` behaves like `linarith` but, on success, it prints a suggestion of
the form `linarith only [...]` listing a minimized set of hypotheses used in the
final proof.  Use `linarith?!` for the higher-reducibility variant and set the
`minimize` flag in the configuration to control whether greedy minimization is
performed.

## linear_combination
Defined in: `Mathlib.Tactic.LinearCombination.linearCombination`

The `linear_combination` tactic attempts to prove an (in)equality goal by exhibiting it as a
specified linear combination of (in)equality hypotheses, or other (in)equality proof terms, modulo
(A) moving terms between the LHS and RHS of the (in)equalities, and (B) a normalization tactic
which by default is ring-normalization.

Example usage:
```lean
example {a b : ℚ} (h1 : a = 1) (h2 : b = 3) : (a + b) / 2 = 2 := by
  linear_combination (h1 + h2) / 2

example {a b : ℚ} (h1 : a ≤ 1) (h2 : b ≤ 3) : (a + b) / 2 ≤ 2 := by
  linear_combination (h1 + h2) / 2

example {a b : ℚ} : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  linear_combination sq_nonneg (a - b)

example {x y z w : ℤ} (h₁ : x * z = y ^ 2) (h₂ : y * w = z ^ 2) :
    z * (x * w - y * z) = 0 := by
  linear_combination w * h₁ + y * h₂

example {x : ℚ} (h : x ≥ 5) : x ^ 2 > 2 * x + 11 := by
  linear_combination (x + 3) * h

example {R : Type*} [CommRing R] {a b : R} (h : a = b) : a ^ 2 = b ^ 2 := by
  linear_combination (a + b) * h

example {A : Type*} [AddCommGroup A]
    {x y z : A} (h1 : x + y = 10 • z) (h2 : x - y = 6 • z) :
    2 • x = 2 • (8 • z) := by
  linear_combination (norm := abel) h1 + h2

example (x y : ℤ) (h1 : x * y + 2 * x = 1) (h2 : x = y) :
    x * y = -2 * y + 1 := by
  linear_combination (norm := ring_nf) -2 * h2
  -- leaves goal `⊢ x * y + x * 2 - 1 = 0`
```

The input `e` in `linear_combination e` is a linear combination of proofs of (in)equalities,
given as a sum/difference of coefficients multiplied by expressions.
The coefficients may be arbitrary expressions (with nonnegativity constraints in the case of
inequalities).
The expressions can be arbitrary proof terms proving (in)equalities;
most commonly they are hypothesis names `h1`, `h2`, ....

The left and right sides of all the (in)equalities should have the same type `α`, and the
coefficients should also have type `α`.  For full functionality `α` should be a commutative ring --
strictly speaking, a commutative semiring with "cancellative" addition (in the semiring case,
negation and subtraction will be handled "formally" as if operating in the enveloping ring). If a
nonstandard normalization is used (for example `abel` or `skip`), the tactic will work over types
`α` with less algebraic structure: for equalities, the minimum is instances of
`[Add α] [IsRightCancelAdd α]` together with instances of whatever operations are used in the tactic
call.

The variant `linear_combination (norm := tac) e` specifies explicitly the "normalization tactic"
`tac` to be run on the subgoal(s) after constructing the linear combination.
* The default normalization tactic is `ring1` (for equalities) or `Mathlib.Tactic.Ring.prove{LE,LT}`
  (for inequalities). These are finishing tactics: they close the goal or fail.
* When working in algebraic categories other than commutative rings -- for example fields, abelian
  groups, modules -- it is sometimes useful to use normalization tactics adapted to those categories
  (`field_simp`, `abel`, `module`).
* To skip normalization entirely, use `skip` as the normalization tactic.
* The `linear_combination` tactic creates a linear combination by adding the provided (in)equalities
  together from left to right, so if `tac` is not invariant under commutation of additive
  expressions, then the order of the input hypotheses can matter.

The variant `linear_combination (exp := n) e` will take the goal to the `n`th power before
subtracting the combination `e`. In other words, if the goal is `t1 = t2`,
`linear_combination (exp := n) e` will change the goal to `(t1 - t2)^n = 0` before proceeding as
above.  This variant is implemented only for linear combinations of equalities (i.e., not for
inequalities).

## linear_combination'
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

## linear_combination2
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

## map_fun_tac
Defined in: `WittVector.mapFun.tacticMap_fun_tac`

Auxiliary tactic for showing that `mapFun` respects the ring operations.

## map_tacs
Defined in: `Batteries.Tactic.«tacticMap_tacs[_;]»`

Assuming there are `n` goals, `map_tacs [t1; t2; ...; tn]` applies each `ti` to the respective
goal and leaves the resulting subgoals.

## massumption
Defined in: `Lean.Parser.Tactic.massumption`

`massumption` is like `assumption`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (P Q : SPred σs) : Q ⊢ₛ P → Q := by
  mintro _ _
  massumption
```

## massumption
Defined in: `Lean.Parser.Tactic.massumptionMacro`

`massumption` is like `assumption`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (P Q : SPred σs) : Q ⊢ₛ P → Q := by
  mintro _ _
  massumption
```

## match
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

## match
Defined in: `Batteries.Tactic.«tacticMatch_,,With.»`

The syntax `match ⋯ with.` has been deprecated in favor of `nomatch ⋯`.

Both now support multiple discriminants.

## match_scalars
Defined in: `Mathlib.Tactic.Module.tacticMatch_scalars`

Given a goal parseable as a linear combination `⊢ a • x + ... + b • y = c • x + ... + d • y`,
`match_scalars` splits up the goal into equalities of the scalars for each respective atom. This
means the example goal above is replaced by goals `⊢ a = c` (from `x`), ..., `⊢ b = d` (from `y`).

The `module` tactic is equivalent to `match_scalars <;> ring1`.

`match_scalars` can parse into expressions made of the operators `+`, `-`, `•` and the numeral `0`.
Any other subexpressions (including variables) are treated as atoms.
If the goal is an equality in the type `M`, then `match_scalars` requires an `AddCommMonoid M`
instance. If the goal contains a scalar multiplication `(a : R) • (x : M)`, this requires a
`Semiring R` and `Module R M` instance. If any of the instances are missing, `match_scalars` fails.

The scalar type for the goals produced by the `match_scalars` tactic is the largest scalar type
encountered; for example, if `ℕ`, `ℚ` and a characteristic-zero field `K` all occur as scalars, then
the goals produced are equalities in `K` with the appropriate casts (from `ℕ`, `ℤ`, `ℚ`) and
`algebraMap`s (otherwise) inserted. Inserted casts are simplified by lemmas tagged `@[push_cast]`.
If the set of scalar types encountered is not totally ordered (in the sense that for all rings `R`,
`S` encountered, it holds that either `Algebra R S` or `Algebra S R`), then `match_scalars` fails.

Examples:
```lean
example [AddCommMonoid M] [Semiring R] [Module R M] (a b : R) (x : M) :
    a • x + b • x = (b + a) • x := by
  match_scalars
  -- one goal: `⊢ a * 1 + b * 1 = (b + a) * 1`

example [AddCommGroup M] [Ring R] [Module R M] (a b : R) (x : M) :
    a • (a • x - b • y) + (b • a • y + b • b • x) = x := by
  match_scalars
  -- two goals:
  -- `⊢ a * (a * 1) + b * (b * 1) = 1` (from the `x` atom)
  -- `⊢ a * -(b * 1) + b * (a * 1) = 0` (from the `y` atom)

example [AddCommGroup M] [Ring R] [Module R M] (a : R) (x : M) :
    -(2:R) • a • x = a • (-2:ℤ) • x := by
  match_scalars
  -- one goal: `⊢ -2 * (a * 1) = a * (-2 * 1)`
```

## match_target
Defined in: `Mathlib.Tactic.tacticMatch_target_`

Deprecated: use `guard_target =~ t` instead.

## mcases
Defined in: `Lean.Parser.Tactic.mcases`

Like `rcases`, but operating on stateful `Std.Do.SPred` goals.
Example: Given a goal `h : (P ∧ (Q ∨ R) ∧ (Q → R)) ⊢ₛ R`,
`mcases h with ⟨-, ⟨hq | hr⟩, hqr⟩` will yield two goals:
`(hq : Q, hqr : Q → R) ⊢ₛ R` and `(hr : R) ⊢ₛ R`.

That is, `mcases h with pat` has the following semantics, based on `pat`:
* `pat=□h'` renames `h` to `h'` in the stateful context, regardless of whether `h` is pure
* `pat=⌜h'⌝` introduces `h' : φ`  to the pure local context if `h : ⌜φ⌝`
  (c.f. `Lean.Elab.Tactic.Do.ProofMode.IsPure`)
* `pat=h'` is like `pat=⌜h'⌝` if `h` is pure
  (c.f. `Lean.Elab.Tactic.Do.ProofMode.IsPure`), otherwise it is like `pat=□h'`.
* `pat=_` renames `h` to an inaccessible name
* `pat=-` discards `h`
* `⟨pat₁, pat₂⟩` matches on conjunctions and existential quantifiers and recurses via
  `pat₁` and `pat₂`.
* `⟨pat₁ | pat₂⟩` matches on disjunctions, matching the left alternative via `pat₁` and the right
  alternative via `pat₂`.

## mcases
Defined in: `Lean.Parser.Tactic.mcasesError`

Like `rcases`, but operating on stateful `Std.Do.SPred` goals.
Example: Given a goal `h : (P ∧ (Q ∨ R) ∧ (Q → R)) ⊢ₛ R`,
`mcases h with ⟨-, ⟨hq | hr⟩, hqr⟩` will yield two goals:
`(hq : Q, hqr : Q → R) ⊢ₛ R` and `(hr : R) ⊢ₛ R`.

That is, `mcases h with pat` has the following semantics, based on `pat`:
* `pat=□h'` renames `h` to `h'` in the stateful context, regardless of whether `h` is pure
* `pat=⌜h'⌝` introduces `h' : φ`  to the pure local context if `h : ⌜φ⌝`
  (c.f. `Lean.Elab.Tactic.Do.ProofMode.IsPure`)
* `pat=h'` is like `pat=⌜h'⌝` if `h` is pure
  (c.f. `Lean.Elab.Tactic.Do.ProofMode.IsPure`), otherwise it is like `pat=□h'`.
* `pat=_` renames `h` to an inaccessible name
* `pat=-` discards `h`
* `⟨pat₁, pat₂⟩` matches on conjunctions and existential quantifiers and recurses via
  `pat₁` and `pat₂`.
* `⟨pat₁ | pat₂⟩` matches on disjunctions, matching the left alternative via `pat₁` and the right
  alternative via `pat₂`.

## mcases
Defined in: `Lean.Parser.Tactic.mcasesMacro`

Like `rcases`, but operating on stateful `Std.Do.SPred` goals.
Example: Given a goal `h : (P ∧ (Q ∨ R) ∧ (Q → R)) ⊢ₛ R`,
`mcases h with ⟨-, ⟨hq | hr⟩, hqr⟩` will yield two goals:
`(hq : Q, hqr : Q → R) ⊢ₛ R` and `(hr : R) ⊢ₛ R`.

That is, `mcases h with pat` has the following semantics, based on `pat`:
* `pat=□h'` renames `h` to `h'` in the stateful context, regardless of whether `h` is pure
* `pat=⌜h'⌝` introduces `h' : φ`  to the pure local context if `h : ⌜φ⌝`
  (c.f. `Lean.Elab.Tactic.Do.ProofMode.IsPure`)
* `pat=h'` is like `pat=⌜h'⌝` if `h` is pure
  (c.f. `Lean.Elab.Tactic.Do.ProofMode.IsPure`), otherwise it is like `pat=□h'`.
* `pat=_` renames `h` to an inaccessible name
* `pat=-` discards `h`
* `⟨pat₁, pat₂⟩` matches on conjunctions and existential quantifiers and recurses via
  `pat₁` and `pat₂`.
* `⟨pat₁ | pat₂⟩` matches on disjunctions, matching the left alternative via `pat₁` and the right
  alternative via `pat₂`.

## mclear
Defined in: `Lean.Parser.Tactic.mclear`

`mclear` is like `clear`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (P Q : SPred σs) : P ⊢ₛ Q → Q := by
  mintro HP
  mintro HQ
  mclear HP
  mexact HQ
```

## mclear
Defined in: `Lean.Parser.Tactic.mclearMacro`

`mclear` is like `clear`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (P Q : SPred σs) : P ⊢ₛ Q → Q := by
  mintro HP
  mintro HQ
  mclear HP
  mexact HQ
```

## mclear
Defined in: `Lean.Parser.Tactic.mclearError`

`mclear` is like `clear`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (P Q : SPred σs) : P ⊢ₛ Q → Q := by
  mintro HP
  mintro HQ
  mclear HP
  mexact HQ
```

## mconstructor
Defined in: `Lean.Parser.Tactic.mconstructor`

`mconstructor` is like `constructor`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (Q : SPred σs) : Q ⊢ₛ Q ∧ Q := by
  mintro HQ
  mconstructor <;> mexact HQ
```

## mconstructor
Defined in: `Lean.Parser.Tactic.mconstructorMacro`

`mconstructor` is like `constructor`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (Q : SPred σs) : Q ⊢ₛ Q ∧ Q := by
  mintro HQ
  mconstructor <;> mexact HQ
```

## mdup
Defined in: `Lean.Parser.Tactic.mdup`

Duplicate a stateful `Std.Do.SPred` hypothesis.

## measurability
Defined in: `Mathlib.Tactic.measurability`

The tactic `measurability` solves goals of the form `Measurable f`, `AEMeasurable f`,
`StronglyMeasurable f`, `AEStronglyMeasurable f μ`, or `MeasurableSet s` by applying lemmas tagged
with the `measurability` user attribute.

Note that `measurability` uses `fun_prop` for solving measurability of functions, so statements
about `Measurable`, `AEMeasurable`, `StronglyMeasurable` and `AEStronglyMeasurable` should be tagged
with `fun_prop` rather that `measurability`. The `measurability` attribute is equivalent to
`fun_prop` in these cases for backward compatibility with the earlier implementation.

## measurability!
Defined in: `measurability!`

The tactic `measurability` solves goals of the form `Measurable f`, `AEMeasurable f`,
`StronglyMeasurable f`, `AEStronglyMeasurable f μ`, or `MeasurableSet s` by applying lemmas tagged
with the `measurability` user attribute.

Note that `measurability` uses `fun_prop` for solving measurability of functions, so statements
about `Measurable`, `AEMeasurable`, `StronglyMeasurable` and `AEStronglyMeasurable` should be tagged
with `fun_prop` rather that `measurability`. The `measurability` attribute is equivalent to
`fun_prop` in these cases for backward compatibility with the earlier implementation.

## measurability!?
Defined in: `measurability!?`

The tactic `measurability?` solves goals of the form `Measurable f`, `AEMeasurable f`,
`StronglyMeasurable f`, `AEStronglyMeasurable f μ`, or `MeasurableSet s` by applying lemmas tagged
with the `measurability` user attribute, and suggests a faster proof script that can be substituted
for the tactic call in case of success.

## measurability?
Defined in: `Mathlib.Tactic.measurability?`

The tactic `measurability?` solves goals of the form `Measurable f`, `AEMeasurable f`,
`StronglyMeasurable f`, `AEStronglyMeasurable f μ`, or `MeasurableSet s` by applying lemmas tagged
with the `measurability` user attribute, and suggests a faster proof script that can be substituted
for the tactic call in case of success.

## mem_tac
Defined in: `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.tacticMem_tac`

`mem_tac` tries to prove goals of the form `x ∈ 𝒜 i` when `x` has the form of:
* `y ^ n` where `i = n • j` and `y ∈ 𝒜 j`.
* a natural number `n`.

## mexact
Defined in: `Lean.Parser.Tactic.mexactMacro`

`mexact` is like `exact`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (Q : SPred σs) : Q ⊢ₛ Q := by
  mstart
  mintro HQ
  mexact HQ
```

## mexact
Defined in: `Lean.Parser.Tactic.mexact`

`mexact` is like `exact`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (Q : SPred σs) : Q ⊢ₛ Q := by
  mstart
  mintro HQ
  mexact HQ
```

## mexact
Defined in: `Lean.Parser.Tactic.mexactError`

`mexact` is like `exact`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (Q : SPred σs) : Q ⊢ₛ Q := by
  mstart
  mintro HQ
  mexact HQ
```

## mexfalso
Defined in: `Lean.Parser.Tactic.mexfalsoMacro`

`mexfalso` is like `exfalso`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (P : SPred σs) : ⌜False⌝ ⊢ₛ P := by
  mintro HP
  mexfalso
  mexact HP
```

## mexfalso
Defined in: `Lean.Parser.Tactic.mexfalso`

`mexfalso` is like `exfalso`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (P : SPred σs) : ⌜False⌝ ⊢ₛ P := by
  mintro HP
  mexfalso
  mexact HP
```

## mexists
Defined in: `Lean.Parser.Tactic.mexistsMacro`

`mexists` is like `exists`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (ψ : Nat → SPred σs) : ψ 42 ⊢ₛ ∃ x, ψ x := by
  mintro H
  mexists 42
```

## mexists
Defined in: `Lean.Parser.Tactic.mexistsError`

`mexists` is like `exists`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (ψ : Nat → SPred σs) : ψ 42 ⊢ₛ ∃ x, ψ x := by
  mintro H
  mexists 42
```

## mexists
Defined in: `Lean.Parser.Tactic.mexists`

`mexists` is like `exists`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (ψ : Nat → SPred σs) : ψ 42 ⊢ₛ ∃ x, ψ x := by
  mintro H
  mexists 42
```

## mfld_set_tac
Defined in: `Tactic.MfldSetTac.mfldSetTac`

A very basic tactic to show that sets showing up in manifolds coincide or are included
in one another.

## mframe
Defined in: `Lean.Parser.Tactic.mframeMacro`

`mframe` infers which hypotheses from the stateful context can be moved into the pure context.
This is useful because pure hypotheses "survive" the next application of modus ponens
(`Std.Do.SPred.mp`) and transitivity (`Std.Do.SPred.entails.trans`).

It is used as part of the `mspec` tactic.

```lean
example (P Q : SPred σs) : ⊢ₛ ⌜p⌝ ∧ Q ∧ ⌜q⌝ ∧ ⌜r⌝ ∧ P ∧ ⌜s⌝ ∧ ⌜t⌝ → Q := by
  mintro _
  mframe
  /- `h : p ∧ q ∧ r ∧ s ∧ t` in the pure context -/
  mcases h with hP
  mexact h
```

## mframe
Defined in: `Lean.Parser.Tactic.mframe`

`mframe` infers which hypotheses from the stateful context can be moved into the pure context.
This is useful because pure hypotheses "survive" the next application of modus ponens
(`Std.Do.SPred.mp`) and transitivity (`Std.Do.SPred.entails.trans`).

It is used as part of the `mspec` tactic.

```lean
example (P Q : SPred σs) : ⊢ₛ ⌜p⌝ ∧ Q ∧ ⌜q⌝ ∧ ⌜r⌝ ∧ P ∧ ⌜s⌝ ∧ ⌜t⌝ → Q := by
  mintro _
  mframe
  /- `h : p ∧ q ∧ r ∧ s ∧ t` in the pure context -/
  mcases h with hP
  mexact h
```

## mhave
Defined in: `Lean.Parser.Tactic.mhaveMacro`

`mhave` is like `have`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (P Q : SPred σs) : P ⊢ₛ (P → Q) → Q := by
  mintro HP HPQ
  mhave HQ : Q := by mspecialize HPQ HP; mexact HPQ
  mexact HQ
```

## mhave
Defined in: `Lean.Parser.Tactic.mhave`

`mhave` is like `have`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (P Q : SPred σs) : P ⊢ₛ (P → Q) → Q := by
  mintro HP HPQ
  mhave HQ : Q := by mspecialize HPQ HP; mexact HPQ
  mexact HQ
```

## mhave
Defined in: `Lean.Parser.Tactic.mhaveError`

`mhave` is like `have`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (P Q : SPred σs) : P ⊢ₛ (P → Q) → Q := by
  mintro HP HPQ
  mhave HQ : Q := by mspecialize HPQ HP; mexact HPQ
  mexact HQ
```

## mintro
Defined in: `Lean.Parser.Tactic.mintro`

Like `intro`, but introducing stateful hypotheses into the stateful context of the `Std.Do.SPred`
proof mode.
That is, given a stateful goal `(hᵢ : Hᵢ)* ⊢ₛ P → T`, `mintro h` transforms
into `(hᵢ : Hᵢ)*, (h : P) ⊢ₛ T`.

Furthermore, `mintro ∀s` is like `intro s`, but preserves the stateful goal.
That is, `mintro ∀s` brings the topmost state variable `s:σ` in scope and transforms
`(hᵢ : Hᵢ)* ⊢ₛ T` (where the entailment is in `Std.Do.SPred (σ::σs)`) into
`(hᵢ : Hᵢ s)* ⊢ₛ T s` (where the entailment is in `Std.Do.SPred σs`).

Beyond that, `mintro` supports the full syntax of `mcases` patterns
(`mintro pat = (mintro h; mcases h with pat`), and can perform multiple
introductions in sequence.

## mintro
Defined in: `Lean.Parser.Tactic.mintroError`

Like `intro`, but introducing stateful hypotheses into the stateful context of the `Std.Do.SPred`
proof mode.
That is, given a stateful goal `(hᵢ : Hᵢ)* ⊢ₛ P → T`, `mintro h` transforms
into `(hᵢ : Hᵢ)*, (h : P) ⊢ₛ T`.

Furthermore, `mintro ∀s` is like `intro s`, but preserves the stateful goal.
That is, `mintro ∀s` brings the topmost state variable `s:σ` in scope and transforms
`(hᵢ : Hᵢ)* ⊢ₛ T` (where the entailment is in `Std.Do.SPred (σ::σs)`) into
`(hᵢ : Hᵢ s)* ⊢ₛ T s` (where the entailment is in `Std.Do.SPred σs`).

Beyond that, `mintro` supports the full syntax of `mcases` patterns
(`mintro pat = (mintro h; mcases h with pat`), and can perform multiple
introductions in sequence.

## mintro
Defined in: `Lean.Parser.Tactic.mintroMacro`

Like `intro`, but introducing stateful hypotheses into the stateful context of the `Std.Do.SPred`
proof mode.
That is, given a stateful goal `(hᵢ : Hᵢ)* ⊢ₛ P → T`, `mintro h` transforms
into `(hᵢ : Hᵢ)*, (h : P) ⊢ₛ T`.

Furthermore, `mintro ∀s` is like `intro s`, but preserves the stateful goal.
That is, `mintro ∀s` brings the topmost state variable `s:σ` in scope and transforms
`(hᵢ : Hᵢ)* ⊢ₛ T` (where the entailment is in `Std.Do.SPred (σ::σs)`) into
`(hᵢ : Hᵢ s)* ⊢ₛ T s` (where the entailment is in `Std.Do.SPred σs`).

Beyond that, `mintro` supports the full syntax of `mcases` patterns
(`mintro pat = (mintro h; mcases h with pat`), and can perform multiple
introductions in sequence.

## mleave
Defined in: `Lean.Parser.Tactic.mleave`

Leaves the stateful proof mode of `Std.Do.SPred`, tries to eta-expand through all definitions
related to the logic of the `Std.Do.SPred` and gently simplifies the resulting pure Lean
proposition. This is often the right thing to do after `mvcgen` in order for automation to prove
the goal.

## mleave
Defined in: `Lean.Parser.Tactic.mleaveMacro`

Leaves the stateful proof mode of `Std.Do.SPred`, tries to eta-expand through all definitions
related to the logic of the `Std.Do.SPred` and gently simplifies the resulting pure Lean
proposition. This is often the right thing to do after `mvcgen` in order for automation to prove
the goal.

## mleft
Defined in: `Lean.Parser.Tactic.mleftMacro`

`mleft` is like `left`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (P Q : SPred σs) : P ⊢ₛ P ∨ Q := by
  mintro HP
  mleft
  mexact HP
```

## mleft
Defined in: `Lean.Parser.Tactic.mleft`

`mleft` is like `left`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (P Q : SPred σs) : P ⊢ₛ P ∨ Q := by
  mintro HP
  mleft
  mexact HP
```

## mod_cases
Defined in: `Mathlib.Tactic.ModCases.«tacticMod_cases_:_%_»`

`mod_cases h : e % n`, where `n` is a positive numeral and `e` is an expression of type `ℕ` or `ℤ`,
performs a case disjunction on the value of `e` modulo `n`. If `e : ℤ`, the goal is split into
`n` subgoals containing the new hypotheses `h : e ≡ 0 [ZMOD n]`, ..., `h : e ≡ n-1 [ZMOD n]`
respectively. If `e : ℕ` instead, then the hypotheses contain `[MOD n]` instead of `[ZMOD n]`.

* `mod_cases e % n`, with `h` omitted, gives the default name `H` to the new hypotheses.

## module
Defined in: `Mathlib.Tactic.Module.tacticModule`

Given a goal parseable as a linear combination `⊢ a • x + ... + b • y = c • x + ... + d • y`,
`module` proves the equalities of the scalars for each respective atom, by ring normalization.
This means the example goal above is solved if `ring` can prove `⊢ a = c` (from `x`), ..., `⊢ b = d`
(from `y`).

`module` is equivalent to `match_scalars <;> ring1`. If `ring1` fails to prove one of the
equalities, you can instead use `match_scalars` followed by specialized proofs for each scalar.

Examples:
```lean
example [AddCommMonoid M] [CommSemiring R] [Module R M] (a b : R) (x : M) :
    a • x + b • x = (b + a) • x := by
  module

example [AddCommMonoid M] [Field K] [CharZero K] [Module K M] (x : M) :
    (2:K)⁻¹ • x + (3:K)⁻¹ • x + (6:K)⁻¹ • x = x := by
  module

example [AddCommGroup M] [CommRing R] [Module R M] (a : R) (v w : M) :
    (1 + a ^ 2) • (v + w) - a • (a • v - w) = v + (1 + a + a ^ 2) • w := by
  module

example [AddCommGroup M] [CommRing R] [Module R M] (a b μ ν : R) (x y : M) :
    (μ - ν) • a • x = (a • μ • x + b • ν • y) - ν • (a • x + b • y) := by
  module
```

## monicity
Defined in: `Mathlib.Tactic.ComputeDegree.monicityMacro`

`monicity` tries to solve a goal of the form `Monic f`.
It converts the goal into a goal of the form `natDegree f ≤ n` and one of the form `f.coeff n = 1`
and calls `compute_degree` on those two goals.

The variant `monicity!` starts like `monicity`, but calls `compute_degree!` on the two side-goals.

## monicity!
Defined in: `Mathlib.Tactic.ComputeDegree.tacticMonicity!`

`monicity` tries to solve a goal of the form `Monic f`.
It converts the goal into a goal of the form `natDegree f ≤ n` and one of the form `f.coeff n = 1`
and calls `compute_degree` on those two goals.

The variant `monicity!` starts like `monicity`, but calls `compute_degree!` on the two side-goals.

## mono
Defined in: `Mathlib.Tactic.Monotonicity.mono`

`mono` applies monotonicity rules and local hypotheses repetitively.  For example,
```lean
example (x y z k : ℤ)
    (h : 3 ≤ (4 : ℤ))
    (h' : z ≤ y) :
    (k + 3 + x) - y ≤ (k + 4 + x) - z := by
  mono
```

## monoidal
Defined in: `Mathlib.Tactic.Monoidal.tacticMonoidal`

Use the coherence theorem for monoidal categories to solve equations in a monoidal category,
where the two sides only differ by replacing strings of monoidal structural morphisms
(that is, associators, unitors, and identities)
with different strings of structural morphisms with the same source and target.

That is, `monoidal` can handle goals of the form
`a ≫ f ≫ b ≫ g ≫ c = a' ≫ f ≫ b' ≫ g ≫ c'`
where `a = a'`, `b = b'`, and `c = c'` can be proved using `monoidal_coherence`.

## monoidal_coherence
Defined in: `Mathlib.Tactic.Monoidal.tacticMonoidal_coherence`

Close the goal of the form `η = θ`, where `η` and `θ` are 2-isomorphisms made up only of
associators, unitors, and identities.
```lean
example {C : Type} [Category* C] [MonoidalCategory C] :
  (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by
  monoidal_coherence
```

## monoidal_nf
Defined in: `Mathlib.Tactic.Monoidal.tacticMonoidal_nf`

Normalize the both sides of an equality.

## monoidal_simps
Defined in: `Mathlib.Tactic.Coherence.monoidal_simps`

Simp lemmas for rewriting a hom in monoidal categories into a normal form.

## move_add
Defined in: `Mathlib.MoveAdd.tacticMove_add_`

`move_oper op [a]` repeatedly moves `a` to the far right hand side in applications of `op`.
Here the constant `op` refers to a binary associative commutative operation, and `a` is any term
(potentially with underscores).

If `a` contains underscores, they are filled in by unification with the first matching occurrence.
Subterms with different values for the underscores are not matched, unless you repeat `a`.

Currently, `move_oper` supports the operators `HAdd.hAdd` (`· + ·`), `HMul.hMul` (`· * ·`),
`And` (`· ∧ ·`), `Or` (`· ∨ ·`), `Max.max` and `Min.min`. To support more operations, add them to
`Mathlib.MoveAdd.moveOperSimpCtx`.

* `move_add [...]` uses addition as the operation: it abbreviates `move_oper HAdd.add [...]`.
* `move_mul [...]` uses multiplication as the operation: it abbreviates `move_oper HMul.mul [...]`.
* `move_oper op [← a]` moves the atoms matching `a` to the far left hand side instead of the right.
* `move_oper op [a, b, ← c, ← d, ...]` moves multiple atoms simultaneously, in the order indicated
  by the arguments: `c` will appear to the left of `d` and `a` will appear to the left of `b`.

## move_mul
Defined in: `Mathlib.MoveAdd.tacticMove_mul_`

`move_oper op [a]` repeatedly moves `a` to the far right hand side in applications of `op`.
Here the constant `op` refers to a binary associative commutative operation, and `a` is any term
(potentially with underscores).

If `a` contains underscores, they are filled in by unification with the first matching occurrence.
Subterms with different values for the underscores are not matched, unless you repeat `a`.

Currently, `move_oper` supports the operators `HAdd.hAdd` (`· + ·`), `HMul.hMul` (`· * ·`),
`And` (`· ∧ ·`), `Or` (`· ∨ ·`), `Max.max` and `Min.min`. To support more operations, add them to
`Mathlib.MoveAdd.moveOperSimpCtx`.

* `move_add [...]` uses addition as the operation: it abbreviates `move_oper HAdd.add [...]`.
* `move_mul [...]` uses multiplication as the operation: it abbreviates `move_oper HMul.mul [...]`.
* `move_oper op [← a]` moves the atoms matching `a` to the far left hand side instead of the right.
* `move_oper op [a, b, ← c, ← d, ...]` moves multiple atoms simultaneously, in the order indicated
  by the arguments: `c` will appear to the left of `d` and `a` will appear to the left of `b`.

## move_oper
Defined in: `Mathlib.MoveAdd.moveOperTac`

`move_oper op [a]` repeatedly moves `a` to the far right hand side in applications of `op`.
Here the constant `op` refers to a binary associative commutative operation, and `a` is any term
(potentially with underscores).

If `a` contains underscores, they are filled in by unification with the first matching occurrence.
Subterms with different values for the underscores are not matched, unless you repeat `a`.

Currently, `move_oper` supports the operators `HAdd.hAdd` (`· + ·`), `HMul.hMul` (`· * ·`),
`And` (`· ∧ ·`), `Or` (`· ∨ ·`), `Max.max` and `Min.min`. To support more operations, add them to
`Mathlib.MoveAdd.moveOperSimpCtx`.

* `move_add [...]` uses addition as the operation: it abbreviates `move_oper HAdd.add [...]`.
* `move_mul [...]` uses multiplication as the operation: it abbreviates `move_oper HMul.mul [...]`.
* `move_oper op [← a]` moves the atoms matching `a` to the far left hand side instead of the right.
* `move_oper op [a, b, ← c, ← d, ...]` moves multiple atoms simultaneously, in the order indicated
  by the arguments: `c` will appear to the left of `d` and `a` will appear to the left of `b`.

## mpure
Defined in: `Lean.Parser.Tactic.mpure`

`mpure` moves a pure hypothesis from the stateful context into the pure context.
```lean
example (Q : SPred σs) (ψ : φ → ⊢ₛ Q): ⌜φ⌝ ⊢ₛ Q := by
  mintro Hφ
  mpure Hφ
  mexact (ψ Hφ)
```

## mpure
Defined in: `Lean.Parser.Tactic.mpureMacro`

`mpure` moves a pure hypothesis from the stateful context into the pure context.
```lean
example (Q : SPred σs) (ψ : φ → ⊢ₛ Q): ⌜φ⌝ ⊢ₛ Q := by
  mintro Hφ
  mpure Hφ
  mexact (ψ Hφ)
```

## mpure
Defined in: `Lean.Parser.Tactic.mpureError`

`mpure` moves a pure hypothesis from the stateful context into the pure context.
```lean
example (Q : SPred σs) (ψ : φ → ⊢ₛ Q): ⌜φ⌝ ⊢ₛ Q := by
  mintro Hφ
  mpure Hφ
  mexact (ψ Hφ)
```

## mpure_intro
Defined in: `Lean.Parser.Tactic.mpureIntro`

`mpure_intro` operates on a stateful `Std.Do.SPred` goal of the form `P ⊢ₛ ⌜φ⌝`.
It leaves the stateful proof mode (thereby discarding `P`), leaving the regular goal `φ`.
```lean
theorem simple : ⊢ₛ (⌜True⌝ : SPred σs) := by
  mpure_intro
  exact True.intro
```

## mpure_intro
Defined in: `Lean.Parser.Tactic.mpureIntroMacro`

`mpure_intro` operates on a stateful `Std.Do.SPred` goal of the form `P ⊢ₛ ⌜φ⌝`.
It leaves the stateful proof mode (thereby discarding `P`), leaving the regular goal `φ`.
```lean
theorem simple : ⊢ₛ (⌜True⌝ : SPred σs) := by
  mpure_intro
  exact True.intro
```

## mrefine
Defined in: `Lean.Parser.Tactic.mrefine`

Like `refine`, but operating on stateful `Std.Do.SPred` goals.
```lean
example (P Q R : SPred σs) : (P ∧ Q ∧ R) ⊢ₛ P ∧ R := by
  mintro ⟨HP, HQ, HR⟩
  mrefine ⟨HP, HR⟩

example (ψ : Nat → SPred σs) : ψ 42 ⊢ₛ ∃ x, ψ x := by
  mintro H
  mrefine ⟨⌜42⌝, H⟩
```

## mrefine
Defined in: `Lean.Parser.Tactic.mrefineMacro`

Like `refine`, but operating on stateful `Std.Do.SPred` goals.
```lean
example (P Q R : SPred σs) : (P ∧ Q ∧ R) ⊢ₛ P ∧ R := by
  mintro ⟨HP, HQ, HR⟩
  mrefine ⟨HP, HR⟩

example (ψ : Nat → SPred σs) : ψ 42 ⊢ₛ ∃ x, ψ x := by
  mintro H
  mrefine ⟨⌜42⌝, H⟩
```

## mrefine
Defined in: `Lean.Parser.Tactic.mrefineError`

Like `refine`, but operating on stateful `Std.Do.SPred` goals.
```lean
example (P Q R : SPred σs) : (P ∧ Q ∧ R) ⊢ₛ P ∧ R := by
  mintro ⟨HP, HQ, HR⟩
  mrefine ⟨HP, HR⟩

example (ψ : Nat → SPred σs) : ψ 42 ⊢ₛ ∃ x, ψ x := by
  mintro H
  mrefine ⟨⌜42⌝, H⟩
```

## mrename_i
Defined in: `Lean.Parser.Tactic.mrenameI`

`mrename_i` is like `rename_i`, but names inaccessible stateful hypotheses in a `Std.Do.SPred` goal.

## mrename_i
Defined in: `Lean.Parser.Tactic.mrenameIMacro`

`mrename_i` is like `rename_i`, but names inaccessible stateful hypotheses in a `Std.Do.SPred` goal.

## mrename_i
Defined in: `Lean.Parser.Tactic.mrenameIError`

`mrename_i` is like `rename_i`, but names inaccessible stateful hypotheses in a `Std.Do.SPred` goal.

## mreplace
Defined in: `Lean.Parser.Tactic.mreplaceError`

`mreplace` is like `replace`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (P Q : SPred σs) : P ⊢ₛ (P → Q) → Q := by
  mintro HP HPQ
  mreplace HPQ : Q := by mspecialize HPQ HP; mexact HPQ
  mexact HPQ
```

## mreplace
Defined in: `Lean.Parser.Tactic.mreplaceMacro`

`mreplace` is like `replace`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (P Q : SPred σs) : P ⊢ₛ (P → Q) → Q := by
  mintro HP HPQ
  mreplace HPQ : Q := by mspecialize HPQ HP; mexact HPQ
  mexact HPQ
```

## mreplace
Defined in: `Lean.Parser.Tactic.mreplace`

`mreplace` is like `replace`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (P Q : SPred σs) : P ⊢ₛ (P → Q) → Q := by
  mintro HP HPQ
  mreplace HPQ : Q := by mspecialize HPQ HP; mexact HPQ
  mexact HPQ
```

## mrevert
Defined in: `Lean.Parser.Tactic.mrevert`

`mrevert` is like `revert`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (P Q R : SPred σs) : P ∧ Q ∧ R ⊢ₛ P → R := by
  mintro ⟨HP, HQ, HR⟩
  mrevert HR
  mrevert HP
  mintro HP'
  mintro HR'
  mexact HR'
```

## mrevert
Defined in: `Lean.Parser.Tactic.mrevertError`

`mrevert` is like `revert`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (P Q R : SPred σs) : P ∧ Q ∧ R ⊢ₛ P → R := by
  mintro ⟨HP, HQ, HR⟩
  mrevert HR
  mrevert HP
  mintro HP'
  mintro HR'
  mexact HR'
```

## mrevert
Defined in: `Lean.Parser.Tactic.mrevertMacro`

`mrevert` is like `revert`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (P Q R : SPred σs) : P ∧ Q ∧ R ⊢ₛ P → R := by
  mintro ⟨HP, HQ, HR⟩
  mrevert HR
  mrevert HP
  mintro HP'
  mintro HR'
  mexact HR'
```

## mright
Defined in: `Lean.Parser.Tactic.mright`

`mright` is like `right`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (P Q : SPred σs) : P ⊢ₛ Q ∨ P := by
  mintro HP
  mright
  mexact HP
```

## mright
Defined in: `Lean.Parser.Tactic.mrightMacro`

`mright` is like `right`, but operating on a stateful `Std.Do.SPred` goal.
```lean
example (P Q : SPred σs) : P ⊢ₛ Q ∨ P := by
  mintro HP
  mright
  mexact HP
```

## mspec
Defined in: `Lean.Parser.Tactic.mspec`

`mspec` is an `apply`-like tactic that applies a Hoare triple specification to the target of the
stateful goal.

Given a stateful goal `H ⊢ₛ wp⟦prog⟧ Q'`, `mspec foo_spec` will instantiate
`foo_spec : ... → ⦃P⦄ foo ⦃Q⦄`, match `foo` against `prog` and produce subgoals for
the verification conditions `?pre : H ⊢ₛ P` and `?post : Q ⊢ₚ Q'`.

* If `prog = x >>= f`, then `mspec Specs.bind` is tried first so that `foo` is matched against `x`
  instead. Tactic `mspec_no_bind` does not attempt to do this decomposition.
* If `?pre` or `?post` follow by `.rfl`, then they are discharged automatically.
* `?post` is automatically simplified into constituent `⊢ₛ` entailments on
  success and failure continuations.
* `?pre` and `?post.*` goals introduce their stateful hypothesis under an inaccessible name.
  You can give it a name with the `mrename_i` tactic.
* Any uninstantiated MVar arising from instantiation of `foo_spec` becomes a new subgoal.
* If the target of the stateful goal looks like `fun s => _` then `mspec` will first `mintro ∀s`.
* If `P` has schematic variables that can be instantiated by doing `mintro ∀s`, for example
  `foo_spec : ∀(n:Nat), ⦃fun s => ⌜n = s⌝⦄ foo ⦃Q⦄`, then `mspec` will do `mintro ∀s` first to
  instantiate `n = s`.
* Right before applying the spec, the `mframe` tactic is used, which has the following effect:
  Any hypothesis `Hᵢ` in the goal `h₁:H₁, h₂:H₂, ..., hₙ:Hₙ ⊢ₛ T` that is
  pure (i.e., equivalent to some `⌜φᵢ⌝`) will be moved into the pure context as `hᵢ:φᵢ`.

Additionally, `mspec` can be used without arguments or with a term argument:

* `mspec` without argument will try and look up a spec for `x` registered with `@[spec]`.
* `mspec (foo_spec blah ?bleh)` will elaborate its argument as a term with expected type
  `⦃?P⦄ x ⦃?Q⦄` and introduce `?bleh` as a subgoal.
  This is useful to pass an invariant to e.g., `Specs.forIn_list` and leave the inductive step
  as a hole.

## mspec
Defined in: `Lean.Parser.Tactic.mspecMacro`

`mspec` is an `apply`-like tactic that applies a Hoare triple specification to the target of the
stateful goal.

Given a stateful goal `H ⊢ₛ wp⟦prog⟧ Q'`, `mspec foo_spec` will instantiate
`foo_spec : ... → ⦃P⦄ foo ⦃Q⦄`, match `foo` against `prog` and produce subgoals for
the verification conditions `?pre : H ⊢ₛ P` and `?post : Q ⊢ₚ Q'`.

* If `prog = x >>= f`, then `mspec Specs.bind` is tried first so that `foo` is matched against `x`
  instead. Tactic `mspec_no_bind` does not attempt to do this decomposition.
* If `?pre` or `?post` follow by `.rfl`, then they are discharged automatically.
* `?post` is automatically simplified into constituent `⊢ₛ` entailments on
  success and failure continuations.
* `?pre` and `?post.*` goals introduce their stateful hypothesis under an inaccessible name.
  You can give it a name with the `mrename_i` tactic.
* Any uninstantiated MVar arising from instantiation of `foo_spec` becomes a new subgoal.
* If the target of the stateful goal looks like `fun s => _` then `mspec` will first `mintro ∀s`.
* If `P` has schematic variables that can be instantiated by doing `mintro ∀s`, for example
  `foo_spec : ∀(n:Nat), ⦃fun s => ⌜n = s⌝⦄ foo ⦃Q⦄`, then `mspec` will do `mintro ∀s` first to
  instantiate `n = s`.
* Right before applying the spec, the `mframe` tactic is used, which has the following effect:
  Any hypothesis `Hᵢ` in the goal `h₁:H₁, h₂:H₂, ..., hₙ:Hₙ ⊢ₛ T` that is
  pure (i.e., equivalent to some `⌜φᵢ⌝`) will be moved into the pure context as `hᵢ:φᵢ`.

Additionally, `mspec` can be used without arguments or with a term argument:

* `mspec` without argument will try and look up a spec for `x` registered with `@[spec]`.
* `mspec (foo_spec blah ?bleh)` will elaborate its argument as a term with expected type
  `⦃?P⦄ x ⦃?Q⦄` and introduce `?bleh` as a subgoal.
  This is useful to pass an invariant to e.g., `Specs.forIn_list` and leave the inductive step
  as a hole.

## mspec_no_bind
Defined in: `Lean.Parser.Tactic.mspecNoBind`

`mspec_no_simp $spec` first tries to decompose `Bind.bind`s before applying `$spec`.
This variant of `mspec_no_simp` does not; `mspec_no_bind $spec` is defined as
```
try with_reducible mspec_no_bind Std.Do.Spec.bind
mspec_no_bind $spec
```

## mspec_no_simp
Defined in: `Lean.Parser.Tactic.mspecNoSimp`

Like `mspec`, but does not attempt slight simplification and closing of trivial sub-goals.
`mspec $spec` is roughly (the set of simp lemmas below might not be up to date)
```
mspec_no_simp $spec
all_goals
  ((try simp only [SPred.true_intro_simp, SPred.apply_pure]);
   (try mpure_intro; trivial))
```

## mspecialize
Defined in: `Lean.Parser.Tactic.mspecializeError`

`mspecialize` is like `specialize`, but operating on a stateful `Std.Do.SPred` goal.
It specializes a hypothesis from the stateful context with hypotheses from either the pure
or stateful context or pure terms.
```lean
example (P Q : SPred σs) : P ⊢ₛ (P → Q) → Q := by
  mintro HP HPQ
  mspecialize HPQ HP
  mexact HPQ

example (y : Nat) (P Q : SPred σs) (Ψ : Nat → SPred σs) (hP : ⊢ₛ P) : ⊢ₛ Q → (∀ x, P → Q → Ψ x) → Ψ (y + 1) := by
  mintro HQ HΨ
  mspecialize HΨ (y + 1) hP HQ
  mexact HΨ
```

## mspecialize
Defined in: `Lean.Parser.Tactic.mspecializeMacro`

`mspecialize` is like `specialize`, but operating on a stateful `Std.Do.SPred` goal.
It specializes a hypothesis from the stateful context with hypotheses from either the pure
or stateful context or pure terms.
```lean
example (P Q : SPred σs) : P ⊢ₛ (P → Q) → Q := by
  mintro HP HPQ
  mspecialize HPQ HP
  mexact HPQ

example (y : Nat) (P Q : SPred σs) (Ψ : Nat → SPred σs) (hP : ⊢ₛ P) : ⊢ₛ Q → (∀ x, P → Q → Ψ x) → Ψ (y + 1) := by
  mintro HQ HΨ
  mspecialize HΨ (y + 1) hP HQ
  mexact HΨ
```

## mspecialize
Defined in: `Lean.Parser.Tactic.mspecialize`

`mspecialize` is like `specialize`, but operating on a stateful `Std.Do.SPred` goal.
It specializes a hypothesis from the stateful context with hypotheses from either the pure
or stateful context or pure terms.
```lean
example (P Q : SPred σs) : P ⊢ₛ (P → Q) → Q := by
  mintro HP HPQ
  mspecialize HPQ HP
  mexact HPQ

example (y : Nat) (P Q : SPred σs) (Ψ : Nat → SPred σs) (hP : ⊢ₛ P) : ⊢ₛ Q → (∀ x, P → Q → Ψ x) → Ψ (y + 1) := by
  mintro HQ HΨ
  mspecialize HΨ (y + 1) hP HQ
  mexact HΨ
```

## mspecialize_pure
Defined in: `Lean.Parser.Tactic.mspecializePure`

`mspecialize_pure` is like `mspecialize`, but it specializes a hypothesis from the
*pure* context with hypotheses from either the pure or stateful context or pure terms.
```lean
example (y : Nat) (P Q : SPred σs) (Ψ : Nat → SPred σs) (hP : ⊢ₛ P) (hΨ : ∀ x, ⊢ₛ P → Q → Ψ x) : ⊢ₛ Q → Ψ (y + 1) := by
  mintro HQ
  mspecialize_pure (hΨ (y + 1)) hP HQ => HΨ
  mexact HΨ
```

## mspecialize_pure
Defined in: `Lean.Parser.Tactic.mspecializePureMacro`

`mspecialize_pure` is like `mspecialize`, but it specializes a hypothesis from the
*pure* context with hypotheses from either the pure or stateful context or pure terms.
```lean
example (y : Nat) (P Q : SPred σs) (Ψ : Nat → SPred σs) (hP : ⊢ₛ P) (hΨ : ∀ x, ⊢ₛ P → Q → Ψ x) : ⊢ₛ Q → Ψ (y + 1) := by
  mintro HQ
  mspecialize_pure (hΨ (y + 1)) hP HQ => HΨ
  mexact HΨ
```

## mspecialize_pure
Defined in: `Lean.Parser.Tactic.mspecializePureError`

`mspecialize` is like `specialize`, but operating on a stateful `Std.Do.SPred` goal.
It specializes a hypothesis from the stateful context with hypotheses from either the pure
or stateful context or pure terms.
```lean
example (P Q : SPred σs) : P ⊢ₛ (P → Q) → Q := by
  mintro HP HPQ
  mspecialize HPQ HP
  mexact HPQ

example (y : Nat) (P Q : SPred σs) (Ψ : Nat → SPred σs) (hP : ⊢ₛ P) : ⊢ₛ Q → (∀ x, P → Q → Ψ x) → Ψ (y + 1) := by
  mintro HQ HΨ
  mspecialize HΨ (y + 1) hP HQ
  mexact HΨ
```

## mstart
Defined in: `Lean.Parser.Tactic.mstartMacro`

Start the stateful proof mode of `Std.Do.SPred`.
This will transform a stateful goal of the form `H ⊢ₛ T` into `⊢ₛ H → T`
upon which `mintro` can be used to re-introduce `H` and give it a name.
It is often more convenient to use `mintro` directly, which will
try `mstart` automatically if necessary.

## mstart
Defined in: `Lean.Parser.Tactic.mstart`

Start the stateful proof mode of `Std.Do.SPred`.
This will transform a stateful goal of the form `H ⊢ₛ T` into `⊢ₛ H → T`
upon which `mintro` can be used to re-introduce `H` and give it a name.
It is often more convenient to use `mintro` directly, which will
try `mstart` automatically if necessary.

## mstop
Defined in: `Lean.Parser.Tactic.mstopMacro`

Stops the stateful proof mode of `Std.Do.SPred`.
This will simply forget all the names given to stateful hypotheses and pretty-print
a bit differently.

## mstop
Defined in: `Lean.Parser.Tactic.mstop`

Stops the stateful proof mode of `Std.Do.SPred`.
This will simply forget all the names given to stateful hypotheses and pretty-print
a bit differently.

## mv_bisim
Defined in: `Mathlib.Tactic.MvBisim.tacticMv_bisim___With___`

tactic for proof by bisimulation

## mvcgen
Defined in: `Lean.Parser.Tactic.mvcgenMacro`

`mvcgen` will break down a Hoare triple proof goal like `⦃P⦄ prog ⦃Q⦄` into verification conditions,
provided that all functions used in `prog` have specifications registered with `@[spec]`.

### Verification Conditions and specifications

A verification condition is an entailment in the stateful logic of `Std.Do.SPred`
in which the original program `prog` no longer occurs.
Verification conditions are introduced by the `mspec` tactic; see the `mspec` tactic for what they
look like.
When there's no applicable `mspec` spec, `mvcgen` will try and rewrite an application
`prog = f a b c` with the simp set registered via `@[spec]`.

### Features

When used like `mvcgen +noLetElim [foo_spec, bar_def, instBEqFloat]`, `mvcgen` will additionally

* add a Hoare triple specification `foo_spec : ... → ⦃P⦄ foo ... ⦃Q⦄` to `spec` set for a
  function `foo` occurring in `prog`,
* unfold a definition `def bar_def ... := ...` in `prog`,
* unfold any method of the `instBEqFloat : BEq Float` instance in `prog`.
* it will no longer substitute away `let`-expressions that occur at most once in `P`, `Q` or `prog`.

### Config options

`+noLetElim` is just one config option of many. Check out `Lean.Elab.Tactic.Do.VCGen.Config` for all
options. Of particular note is `stepLimit = some 42`, which is useful for bisecting bugs in
`mvcgen` and tracing its execution.

### Extended syntax

Often, `mvcgen` will be used like this:
```lean
mvcgen [...]
case inv1 => by exact I1
case inv2 => by exact I2
all_goals (mleave; try grind)
```
There is special syntax for this:
```lean
mvcgen [...] invariants
· I1
· I2
with grind
```
When `I1` and `I2` need to refer to inaccessibles (`mvcgen` will introduce a lot of them for program
variables), you can use case label syntax:
```lean
mvcgen [...] invariants
| inv1 _ acc _ => I1 acc
| _ => I2
with grind
```
This is more convenient than the equivalent `· by rename_i _ acc _; exact I1 acc`.

### Invariant suggestions

`mvcgen` will suggest invariants for you if you use the `invariants?` keyword.
```lean
mvcgen [...] invariants?
```
This is useful if you do not recall the exact syntax to construct invariants.
Furthermore, it will suggest a concrete invariant encoding "this holds at the start of the loop and
this must hold at the end of the loop" by looking at the corresponding VCs.
Although the suggested invariant is a good starting point, it is too strong and requires users to
interpolate it such that the inductive step can be proved. Example:
```lean
def mySum (l : List Nat) : Nat := Id.run do
  let mut acc := 0
  for x in l do
    acc := acc + x
  return acc

/--
info: Try this:
  invariants
    · ⇓⟨xs, letMuts⟩ => ⌜xs.prefix = [] ∧ letMuts = 0 ∨ xs.suffix = [] ∧ letMuts = l.sum⌝
-/
#guard_msgs (info) in
theorem mySum_suggest_invariant (l : List Nat) : mySum l = l.sum := by
  generalize h : mySum l = r
  apply Id.of_wp_run_eq h
  mvcgen invariants?
  all_goals admit
```

## mvcgen
Defined in: `Lean.Parser.Tactic.mvcgen`

`mvcgen` will break down a Hoare triple proof goal like `⦃P⦄ prog ⦃Q⦄` into verification conditions,
provided that all functions used in `prog` have specifications registered with `@[spec]`.

### Verification Conditions and specifications

A verification condition is an entailment in the stateful logic of `Std.Do.SPred`
in which the original program `prog` no longer occurs.
Verification conditions are introduced by the `mspec` tactic; see the `mspec` tactic for what they
look like.
When there's no applicable `mspec` spec, `mvcgen` will try and rewrite an application
`prog = f a b c` with the simp set registered via `@[spec]`.

### Features

When used like `mvcgen +noLetElim [foo_spec, bar_def, instBEqFloat]`, `mvcgen` will additionally

* add a Hoare triple specification `foo_spec : ... → ⦃P⦄ foo ... ⦃Q⦄` to `spec` set for a
  function `foo` occurring in `prog`,
* unfold a definition `def bar_def ... := ...` in `prog`,
* unfold any method of the `instBEqFloat : BEq Float` instance in `prog`.
* it will no longer substitute away `let`-expressions that occur at most once in `P`, `Q` or `prog`.

### Config options

`+noLetElim` is just one config option of many. Check out `Lean.Elab.Tactic.Do.VCGen.Config` for all
options. Of particular note is `stepLimit = some 42`, which is useful for bisecting bugs in
`mvcgen` and tracing its execution.

### Extended syntax

Often, `mvcgen` will be used like this:
```lean
mvcgen [...]
case inv1 => by exact I1
case inv2 => by exact I2
all_goals (mleave; try grind)
```
There is special syntax for this:
```lean
mvcgen [...] invariants
· I1
· I2
with grind
```
When `I1` and `I2` need to refer to inaccessibles (`mvcgen` will introduce a lot of them for program
variables), you can use case label syntax:
```lean
mvcgen [...] invariants
| inv1 _ acc _ => I1 acc
| _ => I2
with grind
```
This is more convenient than the equivalent `· by rename_i _ acc _; exact I1 acc`.

### Invariant suggestions

`mvcgen` will suggest invariants for you if you use the `invariants?` keyword.
```lean
mvcgen [...] invariants?
```
This is useful if you do not recall the exact syntax to construct invariants.
Furthermore, it will suggest a concrete invariant encoding "this holds at the start of the loop and
this must hold at the end of the loop" by looking at the corresponding VCs.
Although the suggested invariant is a good starting point, it is too strong and requires users to
interpolate it such that the inductive step can be proved. Example:
```lean
def mySum (l : List Nat) : Nat := Id.run do
  let mut acc := 0
  for x in l do
    acc := acc + x
  return acc

/--
info: Try this:
  invariants
    · ⇓⟨xs, letMuts⟩ => ⌜xs.prefix = [] ∧ letMuts = 0 ∨ xs.suffix = [] ∧ letMuts = l.sum⌝
-/
#guard_msgs (info) in
theorem mySum_suggest_invariant (l : List Nat) : mySum l = l.sum := by
  generalize h : mySum l = r
  apply Id.of_wp_run_eq h
  mvcgen invariants?
  all_goals admit
```

## mvcgen?
Defined in: `Lean.Parser.Tactic.mvcgenHint`

A hint tactic that expands to `mvcgen invariants?`.

## mvcgen_trivial
Defined in: `Lean.Parser.Tactic.tacticMvcgen_trivial`

`mvcgen_trivial` is the tactic automatically called by `mvcgen` to discharge VCs.
It tries to discharge the VC by applying `(try mpure_intro); trivial` and otherwise delegates to
`mvcgen_trivial_extensible`.
Users are encouraged to extend `mvcgen_trivial_extensible` instead of this tactic in order not to
override the default `(try mpure_intro); trivial` behavior.

## mvcgen_trivial_extensible
Defined in: `Lean.Parser.Tactic.tacticMvcgen_trivial_extensible`


## native_decide
Defined in: `Lean.Parser.Tactic.nativeDecide`

`native_decide` is a synonym for `decide +native`.
It will attempt to prove a goal of type `p` by synthesizing an instance
of `Decidable p` and then evaluating it to `isTrue ..`. Unlike `decide`, this
uses `#eval` to evaluate the decidability instance.

This should be used with care because it adds the entire lean compiler to the trusted
part, and a new axiom will show up in `#print axioms` for theorems using
this method or anything that transitively depends on them. Nevertheless, because it is
compiled, this can be significantly more efficient than using `decide`, and for very
large computations this is one way to run external programs and trust the result.
```lean
example : (List.range 1000).length = 1000 := by native_decide
```

## next
Defined in: `Lean.Parser.Tactic.«tacticNext_=>_»`

`next => tac` focuses on the next goal and solves it using `tac`, or else fails.
`next x₁ ... xₙ => tac` additionally renames the `n` most recent hypotheses with
inaccessible names to the given names.

## nlinarith
Defined in: `Mathlib.Tactic.nlinarith`

An extension of `linarith` with some preprocessing to allow it to solve some nonlinear arithmetic
problems. (Based on Coq's `nra` tactic.) See `linarith` for the available syntax of options,
which are inherited by `nlinarith`; that is, `nlinarith!` and `nlinarith only [h1, h2]` all work as
in `linarith`. The preprocessing is as follows:

* For every subterm `a ^ 2` or `a * a` in a hypothesis or the goal,
  the assumption `0 ≤ a ^ 2` or `0 ≤ a * a` is added to the context.
* For every pair of hypotheses `a1 R1 b1`, `a2 R2 b2` in the context, `R1, R2 ∈ {<, ≤, =}`,
  the assumption `0 R' (b1 - a1) * (b2 - a2)` is added to the context (non-recursively),
  where `R ∈ {<, ≤, =}` is the appropriate comparison derived from `R1, R2`.

## nlinarith!
Defined in: `Mathlib.Tactic.tacticNlinarith!_`

An extension of `linarith` with some preprocessing to allow it to solve some nonlinear arithmetic
problems. (Based on Coq's `nra` tactic.) See `linarith` for the available syntax of options,
which are inherited by `nlinarith`; that is, `nlinarith!` and `nlinarith only [h1, h2]` all work as
in `linarith`. The preprocessing is as follows:

* For every subterm `a ^ 2` or `a * a` in a hypothesis or the goal,
  the assumption `0 ≤ a ^ 2` or `0 ≤ a * a` is added to the context.
* For every pair of hypotheses `a1 R1 b1`, `a2 R2 b2` in the context, `R1, R2 ∈ {<, ≤, =}`,
  the assumption `0 R' (b1 - a1) * (b2 - a2)` is added to the context (non-recursively),
  where `R ∈ {<, ≤, =}` is the appropriate comparison derived from `R1, R2`.

## nofun
Defined in: `Lean.Parser.Tactic.tacticNofun`

The tactic `nofun` is shorthand for `exact nofun`: it introduces the assumptions, then performs an
empty pattern match, closing the goal if the introduced pattern is impossible.

## nomatch
Defined in: `Lean.Parser.Tactic.«tacticNomatch_,,»`

The tactic `nomatch h` is shorthand for `exact nomatch h`.

## noncomm_ring
Defined in: `Mathlib.Tactic.NoncommRing.noncomm_ring`

`noncomm_ring` simplifies expressions in not-necessarily-commutative rings in the main goal
then tries closing it by "cheap" (reducible) `rfl`.
This tactic supports the operators `+`, `*`, `-`, `^` and `•` (for scalar multiplication by
natural numbers or integers).

If the ring is commutative, prefer the `ring` tactic instead, which is more powerful and efficient.
The tactic is implemented as a combination of `simp only [...]` and `abel`. The precise invocation
of `simp only` can be customized using the options listed below.

Limitation: numeric powers are unfolded entirely with `pow_succ` and can easily exceed the
maximum recursion depth.

* `noncomm_ring [h]` adds the term `h` as simplification lemma, rewriting from left to right.
  Multiple arguments can be combined as `noncomm_ring [h₁, ..., hₙ]`.
* `noncomm_ring [← h]` adds the term `h` as simplification lemma, rewriting from right to left.
* `noncomm_ring [*]` simplifies using all hypotheses in the local context.
* `noncomm_ring (config := cfg)` uses `cfg` as configuration for the simplification step.
  See `Lean.Meta.Simp.Config` for more details.
* `noncomm_ring (discharger := tac)` uses the tactic sequence `tac` to discharge assumptions
  to the simplification lemmas. This only applies to user-supplied lemmas, since the default lemmas
  used by `noncomm_ring` do not require a discharger.

Example:
```lean
example {R : Type*} [Ring R] (a b c : R) : a * (b + c + c - b) = 2 * a * c := by
  noncomm_ring
```

## nontriviality
Defined in: `Mathlib.Tactic.Nontriviality.nontriviality`

`nontriviality α` generates a proof of `Nontrivial α` and adds this as a hypothesis.

The tactic first tries to find a proof of `Nontrivial α` using instance synthesis.
If this fails, it will derive this proof using `a < b`, `a ≠ b` or `a > b` hypotheses in the
local context. Otherwise it will perform a case split on `Subsingleton α ∨ Nontrivial α`, and
attempt to prove `Subsingleton α` implies the main goal using `simp [nontriviality]`.
If the `Subsingleton` goal cannot be closed automatically, `nontriviality` fails.

This tactic is extensible: tag a lemma with `@[nontriviality]` to use it in the `simp` set for the
`Subsingleton` case. All `@[simp]` lemmas are automatically used too.

* `nontriviality` (without the argument `α`) infers the type from the main goal,
  if the goal is an (in)equality.
* `nontriviality using h₁, h₂, ..., hₙ` uses `h₁`, ..., `hₙ` as extra arguments to `simp`
  in the `Subsingleton` case. This supports the typical `simp` argument syntax:
  `nontriviality using ← h` rewrites right-to-left with this argument;
  `nontriviality using -h` removes a lemma from the default `simp` set for this tactic invocation.
  `nontriviality using *` adds all local hypotheses to the `simp` set.

Examples:
```lean
example {R : Type} [OrderedRing R] {a : R} (h : 0 < a) : 0 < a := by
  nontriviality -- There is now a `Nontrivial R` hypothesis available.
  assumption

example {R : Type} [CommRing R] {r s : R} : r * s = s * r := by
  nontriviality -- There is now a `Nontrivial R` hypothesis available.
  apply mul_comm

example {R : Type} [OrderedRing R] {a : R} (h : 0 < a) : (2 : ℕ) ∣ 4 := by
  nontriviality R -- there is now a `Nontrivial R` hypothesis available.
  dec_trivial

def myeq {α : Type} (a b : α) : Prop := a = b

example {α : Type} (a b : α) (h : a = b) : myeq a b := by
  success_if_fail nontriviality α -- Fails
  nontriviality α using myeq -- There is now a `Nontrivial α` hypothesis available
  assumption
```

## norm_cast
Defined in: `Lean.Parser.Tactic.tacticNorm_cast__`

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

## norm_cast0
Defined in: `Lean.Parser.Tactic.normCast0`

Implementation of `norm_cast` (the full `norm_cast` calls `trivial` afterwards).

## norm_num
Defined in: `Mathlib.Tactic.normNum`

`norm_num` normalizes numerical expressions in the goal. By default, it supports the operations
`+` `-` `*` `/` `⁻¹` `^` and `%` over types with (at least) an `AddMonoidWithOne` instance, such as
`ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ`. In addition to evaluating numerical expressions, `norm_num` will use `simp`
to simplify the goal. If the goal has the form `A = B`, `A ≠ B`, `A < B` or `A ≤ B`, where `A` and
`B` are numerical expressions, `norm_num` will try to close it. It also has a relatively simple
primality prover.

This tactic is extensible. Extensions can allow `norm_num` to evaluate more kinds of expressions, or
to prove more kinds of propositions. See the `@[norm_num]` attribute for further information on
extending `norm_num`.

* `norm_num at l` normalizes at location(s) `l`.
* `norm_num [h1, ...]` adds the arguments `h1, ...` to the `simp` set in addition to the default
  `simp` set. All options for `simp` arguments are supported, in particular `←`, `↑` and `↓`.
* `norm_num only` does not use the default `simp` set for simplification. `norm_num only [h1, ...]`
  uses only the arguments `h1, ...` in addition to the routines tagged `@[norm_num]`.
  `norm_num only` still performs post-processing steps, like `simp only`, use `norm_num1` if you
  exclusively want to normalize numerical expressions.
* `norm_num (config := cfg)` uses `cfg` as configuration for `simp` calls (see the `simp` tactic for
  further details).

Examples:
```lean
example : 43 ≤ 74 + (33 : ℤ) := by norm_num
example : ¬ (7-2)/(2*3) ≥ (1:ℝ) + 2/(3^2) := by norm_num
```

## norm_num1
Defined in: `Mathlib.Tactic.normNum1`

`norm_num1` normalizes numerical expressions in the goal. It is a basic version of `norm_num`
that does not call `simp`.

By default, it supports the operations `+` `-` `*` `/` `⁻¹` `^` and `%` over types with (at least)
an `AddMonoidWithOne` instance, such as `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ`. If the goal has the form `A = B`,
`A ≠ B`, `A < B` or `A ≤ B`, where `A` and `B` are numerical expressions, `norm_num1` will try to
close it. It also has a relatively simple primality prover.
:e
This tactic is extensible. Extensions can allow `norm_num1` to evaluate more kinds of expressions,
or to prove more kinds of propositions. See the `@[norm_num]` attribute for further information on
extending `norm_num1`.

* `norm_num1 at l` normalizes at location(s) `l`.

Examples:
```lean
example : 43 ≤ 74 + (33 : ℤ) := by norm_num1
example : ¬ (7-2)/(2*3) ≥ (1:ℝ) + 2/(3^2) := by norm_num1
```

## nth_grewrite
Defined in: `Mathlib.Tactic.tacticNth_grewrite_____`

`nth_grewrite` is just like `nth_rewrite`, but for `grewrite`.

## nth_grw
Defined in: `Mathlib.Tactic.tacticNth_grw_____`

`nth_grw` is just like `nth_rw`, but for `grw`.

## nth_rewrite
Defined in: `Mathlib.Tactic.tacticNth_rewrite_____`

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
Notice that the second and third occurrences of `a` from the left have been rewritten by
`nth_rewrite`.

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

## nth_rw
Defined in: `Mathlib.Tactic.tacticNth_rw_____`

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
Notice that the second and third occurrences of `a` from the left have been rewritten by
`nth_rw`.

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

## observe
Defined in: `Mathlib.Tactic.LibrarySearch.observe`

`observe hp : p` asserts the proposition `p` as a hypothesis named `hp`, and tries to prove it
using `exact?`.
If no proof is found, the tactic fails.
In other words, this tactic is equivalent to `have hp : p := by exact?`.

* `observe : p` uses the name `this` for the new hypothesis.
* `observe? hp : p` will emit a trace message of the form `have hp : p := proof_term`.
  This may be particularly useful to speed up proofs.

## observe?
Defined in: `Mathlib.Tactic.LibrarySearch.«tacticObserve?__:_Using__,,»`

`observe hp : p` asserts the proposition `p` as a hypothesis named `hp`, and tries to prove it
using `exact?`.
If no proof is found, the tactic fails.
In other words, this tactic is equivalent to `have hp : p := by exact?`.

* `observe : p` uses the name `this` for the new hypothesis.
* `observe? hp : p` will emit a trace message of the form `have hp : p := proof_term`.
  This may be particularly useful to speed up proofs.

## observe?
Defined in: `Mathlib.Tactic.LibrarySearch.«tacticObserve?__:_»`

`observe hp : p` asserts the proposition `p` as a hypothesis named `hp`, and tries to prove it
using `exact?`.
If no proof is found, the tactic fails.
In other words, this tactic is equivalent to `have hp : p := by exact?`.

* `observe : p` uses the name `this` for the new hypothesis.
* `observe? hp : p` will emit a trace message of the form `have hp : p := proof_term`.
  This may be particularly useful to speed up proofs.

## obtain
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

## omega
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
omega +splitDisjunctions +splitNatSub +splitNatAbs +splitMinMax
```
can be used to:
* `splitDisjunctions`: split any disjunctions found in the context,
  if the problem is not otherwise solvable.
* `splitNatSub`: for each appearance of `((a - b : Nat) : Int)`, split on `a ≤ b` if necessary.
* `splitNatAbs`: for each appearance of `Int.natAbs a`, split on `0 ≤ a` if necessary.
* `splitMinMax`: for each occurrence of `min a b`, split on `min a b = a ∨ min a b = b`
Currently, all of these are on by default.

## on_goal
Defined in: `Batteries.Tactic.«tacticOn_goal-_=>_»`

`on_goal n => tacSeq` creates a block scope for the `n`-th goal and tries the sequence
of tactics `tacSeq` on it.

`on_goal -n => tacSeq` does the same, but the `n`-th goal is chosen by counting from the
bottom.

The goal is not required to be solved and any resulting subgoals are inserted back into the
list of goals, replacing the chosen goal.

## open
Defined in: `Lean.Parser.Tactic.open`

`open Foo in tacs` (the tactic) acts like `open Foo` at command level,
but it opens a namespace only within the tactics `tacs`.

## order
Defined in: `Mathlib.Tactic.Order.tacticOrder_`

A finishing tactic for solving goals in arbitrary `Preorder`, `PartialOrder`,
or `LinearOrder`. Supports `⊤`, `⊥`, and lattice operations.

## order_core
Defined in: `Mathlib.Tactic.Order.order_core`

`order_core` is the part of the `order` tactic that tries to find a contradiction.

## peel
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

## pi_lower_bound
Defined in: `Real.«tacticPi_lower_bound[_,,]»`

Create a proof of `a < π` for a fixed rational number `a`, given a witness, which is a
sequence of rational numbers `√2 < r 1 < r 2 < ... < r n < 2` satisfying the property that
`√(2 + r i) ≤ r(i+1)`, where `r 0 = 0` and `√(2 - r n) ≥ a/2^(n+1)`.

## pi_upper_bound
Defined in: `Real.«tacticPi_upper_bound[_,,]»`

Create a proof of `π < a` for a fixed rational number `a`, given a witness, which is a
sequence of rational numbers `√2 < r 1 < r 2 < ... < r n < 2` satisfying the property that
`√(2 + r i) ≥ r(i+1)`, where `r 0 = 0` and `√(2 - r n) ≤ (a - 1/4^n) / 2^(n+1)`.

## pick_goal
Defined in: `Batteries.Tactic.«tacticPick_goal-_»`

`pick_goal n` will move the `n`-th goal to the front.

`pick_goal -n` will move the `n`-th goal (counting from the bottom) to the front.

See also `Tactic.rotate_goals`, which moves goals from the front to the back and vice-versa.

## plausible
Defined in: `plausibleSyntax`

`plausible` considers a proof goal and tries to generate examples
that would contradict the statement.

Let's consider the following proof goal.

```lean
xs : List Nat,
h : ∃ (x : Nat) (H : x ∈ xs), x < 3
⊢ ∀ (y : Nat), y ∈ xs → y < 5
```

The local constants will be reverted and an instance will be found for
`Testable (∀ (xs : List Nat), (∃ x ∈ xs, x < 3) → (∀ y ∈ xs, y < 5))`.
The `Testable` instance is supported by an instance of `Sampleable (List Nat)`,
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

If `plausible` successfully tests 100 examples, it acts like
admit. If it gives up or finds a counter-example, it reports an error.

For more information on writing your own `Sampleable` and `Testable`
instances, see `Testing.Plausible.Testable`.

Optional arguments given with `plausible (config : { ... })`
* `numInst` (default 100): number of examples to test properties with
* `maxSize` (default 100): final size argument

Options:
* `set_option trace.plausible.decoration true`: print the proposition with quantifier annotations
* `set_option trace.plausible.discarded true`: print the examples discarded because they do not
  satisfy assumptions
* `set_option trace.plausible.shrink.steps true`: trace the shrinking of counter-example
* `set_option trace.plausible.shrink.candidates true`: print the lists of candidates considered
  when shrinking each variable
* `set_option trace.plausible.instance true`: print the instances of `testable` being used to test
  the proposition
* `set_option trace.plausible.success true`: print the tested samples that satisfy a property

## pnat_positivity
Defined in: `Mathlib.Tactic.PNatToNat.tacticPnat_positivity`

For each `x : PNat` in the context, add the hypothesis `0 < (↑x : ℕ)`.

## pnat_to_nat
Defined in: `Mathlib.Tactic.PNatToNat.tacticPnat_to_nat`

`pnat_to_nat` shifts all `PNat`s in the context to `Nat`, rewriting propositions about them.
A typical use case is `pnat_to_nat; lia`.

## polyrith
Defined in: `Mathlib.Tactic.Polyrith.«tacticPolyrithOnly[_]»`

The `polyrith` tactic is no longer supported in Mathlib,
because it relied on a defunct external service.

---

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
* This tactic assumes that the user has `curl` available on path.

## positivity
Defined in: `Mathlib.Tactic.Positivity.positivity`

`positivity` solves goals of the form `0 ≤ x`, `0 < x` and `x ≠ 0`. The tactic works recursively
according to the syntax of the expression `x`, by attempting to prove subexpressions are
positive/nonnegative/nonzero and combining this into a final proof. This tactic either closes the
goal or fails.

For each subexpression `e`, `positivity` will try to:
* try `@[positivity]`-tagged extensions to recursively prove `e` is positive/nonnegative/nonzero
  based on its subexpressions (see the `positivity` attribute for more details), or
* try the `norm_num` tactic to prove `e` is positive/nonnegative/nonzero, or
* try showing `e : t` is nonnegative because there is a `CanonicallyOrderedAdd t` instance, or
* use a local hypothesis of the form `0 ≤ e`, `0 < e` or `e ≠ 0`.

This tactic is extensible. See the `positivity` attribute documentation for more details.

* `positivity [t₁, …, tₙ]` first executes `have := t₁; …; have := tₙ` in the current goal,
  then runs `positivity`. This is useful when `positivity` needs derived premises such as `0 < y`
  for division/reciprocal, or `0 ≤ x` for real powers.

Examples:
```lean
example {a : ℤ} (ha : 3 < a) : 0 ≤ a ^ 3 + a := by positivity

example {a : ℤ} (ha : 1 < a) : 0 < |(3:ℤ) + a| := by positivity

example {b : ℤ} : 0 ≤ max (-3) (b ^ 2) := by positivity

example {a b c d : ℝ} (hab : 0 < a * b) (hb : 0 ≤ b) (hcd : c < d) :
    0 < a ^ c + 1 / (d - c) := by
  positivity [sub_pos_of_lt hcd, pos_of_mul_pos_left hab hb]
```

## pull
Defined in: `Mathlib.Tactic.Push.pull`

`pull c` rewrites the goal by pulling the constant `c` closer to the head of the expression.
For instance, `pull _ ∈ _` rewrites `x ∈ y ∨ ¬ x ∈ z` into `x ∈ y ∪ zᶜ`.
More precisely, the `pull` tactic repeatedly rewrites an expression by applying lemmas
of the form `... (c ...) = c ...` (where `c` can appear 1 or more times on the left hand side).
`pull` is the inverse tactic to `push`. To extend the `pull` tactic, you can tag a lemma
with the `@[push]` attribute. `pull` works as both a tactic and a conv tactic.

A lemma is considered a `pull` lemma if its reverse direction is a `push` lemma
that actually moves the given constant away from the head. For example
- `not_or : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q` is a `pull` lemma, but `not_not : ¬ ¬ p ↔ p` is not.
- `log_mul : log (x * y) = log x + log y` is a `pull` lemma, but `log_abs : log |x| = log x` is not.
- `Pi.mul_def : f * g = fun (i : ι) => f i * g i` and `Pi.one_def : 1 = fun (x : ι) => 1` are both
  `pull` lemmas for `fun`, because every `push fun _ ↦ _` lemma is also considered a `pull` lemma.

TODO: define a `@[pull]` attribute for tagging `pull` lemmas that are not `push` lemmas.

* `pull _ ~ _` pulls the operator or relation `~`.
* `pull c at l1 l2 ...` rewrites at the given locations.
* `pull c at *` rewrites at all hypotheses and the goal.
* `pull (disch := tac) c` uses the tactic `tac` to discharge any hypotheses for `@[push]` lemmas.

Examples:
* `pull _ ∈ _` rewrites `x ∈ y ∨ ¬ x ∈ z` into `x ∈ y ∪ zᶜ`.
* `pull (disch := positivity) Real.log` rewrites `log a + 2 * log b` into `log (a * b ^ 2)`.
* `pull fun _ ↦ _` rewrites `f ^ 2 + 5` into `fun x => f x ^ 2 + 5` where `f` is a function.

## pure_coherence
Defined in: `Mathlib.Tactic.Coherence.pure_coherence`

`pure_coherence` uses the coherence theorem for monoidal categories to prove the goal.
It can prove any equality made up only of associators, unitors, and identities.
```lean
example {C : Type} [Category* C] [MonoidalCategory C] :
  (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by
  pure_coherence
```

Users will typically just use the `coherence` tactic,
which can also cope with identities of the form
`a ≫ f ≫ b ≫ g ≫ c = a' ≫ f ≫ b' ≫ g ≫ c'`
where `a = a'`, `b = b'`, and `c = c'` can be proved using `pure_coherence`

## pure_coherence_internal
Defined in: `Mathlib.Tactic.Coherence.pure_coherence_internal`

The same as `pure_coherence`, but used internally in `coherence` without the warning.

## push
Defined in: `Mathlib.Tactic.Push.pushStx`

`push c` rewrites the goal by pushing the constant `c` deeper into an expression.
For instance, `push _ ∈ _` rewrites `x ∈ {y} ∪ zᶜ` into `x = y ∨ ¬ x ∈ z`.
More precisely, the `push` tactic repeatedly rewrites an expression by applying lemmas
of the form `c ... = ... (c ...)` (where `c` can appear 0 or more times on the right hand side).
To extend the `push` tactic, you can tag a lemma of this form with the `@[push]` attribute.

To instead move a constant closer to the head of the expression, use the `pull` tactic.

`push` works as both a tactic and a conv tactic.

* `push _ ~ _` pushes the (binary) operator `~`, `push ~ _` pushes the (unary) operator `~`.
* `push c at l1 l2 ...` rewrites at the given locations.
* `push c at *` rewrites at all hypotheses and the goal.
* `push +distrib Not` rewrites `¬ (p ∧ q)` into `¬ p ∨ ¬ q` (without `+distrib`, it rewrites it
  into `p → ¬ q` instead).
* `push (disch := tac) c` uses the tactic `tac` to discharge any hypotheses for `@[push]` lemmas.

Examples:
* `push Not` is the same as `push ¬ _`, and it rewrites `¬ ∀ ε > 0, ∃ δ > 0, δ < ε` into
  `∃ ε > 0, ∀ δ > 0, ε ≤ δ`. Notably, this preserves the binder names.
* `push _ ∈ _` rewrites `x ∈ {y} ∪ zᶜ` into `x = y ∨ ¬ x ∈ z`.
* `push (disch := positivity) Real.log` rewrites `log (a * b ^ 2)` into `log a + 2 * log b`.
* `push fun _ ↦ _` rewrites `fun x => f x ^ 2 + 5` into `f ^ 2 + 5`
* `push ∀ _, _` rewrites `∀ a, p a ∧ q a` into `(∀ a, p a) ∧ (∀ a, q a)`.

## push_cast
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

## push_neg
Defined in: `Mathlib.Tactic.Push.push_neg`

`push_neg` rewrites the goal by pushing negations deeper into an expression.
For instance, the goal `¬ ∀ x, ∃ y, x ≤ y` will be transformed by `push_neg` into
`∃ x, ∀ y, y < x`. Binder names are preserved (contrary to what would happen with `simp`
using the relevant lemmas). `push_neg` works as both a tactic and a conv tactic.

`push_neg` is a special case of the more general `push` tactic, namely `push Not`.
The `push` tactic can be extended using the `@[push]` attribute. `push` has special-casing
built in for `push Not`.

Tactics that introduce a negation usually have a version that automatically calls `push_neg` on
that negation. These include `by_cases!`, `contrapose!` and `by_contra!`.

* `push_neg at l1 l2 ...` rewrites at the given locations.
* `push_neg at *` rewrites at each hypothesis and the goal.
* `push_neg +distrib` rewrites `¬ (p ∧ q)` into `¬ p ∨ ¬ q` (by default, the tactic rewrites it
  into `p → ¬ q` instead).

Example:

```lean
example (h : ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - y₀| ≤ ε) :
    ∃ ε > 0, ∀ δ > 0, ∃ x, |x - x₀| ≤ δ ∧ ε < |f x - y₀| := by
  push_neg at h
  -- Now we have the hypothesis `h : ∃ ε > 0, ∀ δ > 0, ∃ x, |x - x₀| ≤ δ ∧ ε < |f x - y₀|`
  exact h
```

## qify
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

## rcases
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

## rcongr
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

## recover
Defined in: `Mathlib.Tactic.tacticRecover_`

`recover tacs` applies the tactic (sequence) `tacs` and then re-adds goals that were
incorrectly marked as closed. This helps to debug issues where a tactic closes goals without
solving them (i.e. goals were removed from the MetaM state without the metavariable
being assigned), resulting in the error "(kernel) declaration has metavariables".

## reduce
Defined in: `Mathlib.Tactic.tacticReduce__`

`reduce at loc` completely reduces the given location.
This also exists as a `conv`-mode tactic.

This does the same transformation as the `#reduce` command.

## reduce_mod_char
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

## reduce_mod_char!
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

## refine
Defined in: `Lean.Parser.Tactic.refine`

`refine e` behaves like `exact e`, except that named (`?x`) or unnamed (`?_`)
holes in `e` that are not solved by unification with the main goal's target type
are converted into new goals, using the hole's name, if any, as the goal case name.

## refine'
Defined in: `Lean.Parser.Tactic.refine'`

`refine' e` behaves like `refine e`, except that unsolved placeholders (`_`)
and implicit parameters are also converted into new goals.

## refine_lift
Defined in: `Lean.Parser.Tactic.tacticRefine_lift_`

Auxiliary macro for lifting have/suffices/let/...
It makes sure the "continuation" `?_` is the main goal after refining.

## refine_lift'
Defined in: `Lean.Parser.Tactic.tacticRefine_lift'_`

Similar to `refine_lift`, but using `refine'`

## refold_let
Defined in: `Mathlib.Tactic.refoldLetStx`

`refold_let x y z at loc` looks for the bodies of local definitions `x`, `y`, and `z` at the given
location and replaces them with `x`, `y`, or `z`. This is the inverse of "zeta reduction."
This also exists as a `conv`-mode tactic.

## rel
Defined in: `Mathlib.Tactic.GCongr.«tacticRel[_]»`

`rel [h₁, ..., hₙ]` uses "generalized congruence" rules to solve a goal of form
`⊢ R (f a₁ ... aₙ) (f b₁ ... bₙ)` by substituting with the terms `hᵢ : Rᵢ aᵢ bᵢ`. The relations
`R`, `Rᵢ` can be any two-argument relation, including `· → ·`.

This tactic is extensible: to add a "generalized congruence" rule, tag a theorem with the attribute
`@[gcongr]`.

If a "generalized congruence" lemma has a side goal, `rel` will try to discharge it using
`gcongr_discharger`, which is an extensible tactic based on `positivity`. If side goals cannot be
discharged, or the terms `h₁`, ..., `hₙ` cannot solve the goals, the tactic fails.

Examples:
```lean
example {a b x c d : ℝ} (h1 : a ≤ b) (h2 : c ≤ d) :
    x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  rel [h1, h2]
-- In this example we "substitute" the hypotheses `a ≤ b` and `c ≤ d` into the LHS `x ^ 2 * a + c`
-- of the goal and obtain the RHS `x ^ 2 * b + d`, thus proving the goal.
-- This constructs the proof term:
--   add_le_add (mul_le_mul_of_nonneg_left h1 (pow_bit0_nonneg x 1)) h2
-- using the generalized congruence lemmas `add_le_add` and `mul_le_mul_of_nonneg_left`.
```

## rename
Defined in: `Lean.Parser.Tactic.rename`

`rename t => x` renames the most recent hypothesis whose type matches `t`
(which may contain placeholders) to `x`, or fails if no such hypothesis could be found.

## rename'
Defined in: `Mathlib.Tactic.rename'`

`rename' h => hnew` renames the hypothesis named `h` to `hnew`.
To rename several hypothesis, use `rename' h₁ => h₁new, h₂ => h₂new`.
You can use `rename' a => b, b => a` to swap two variables.

## rename_bvar
Defined in: `Mathlib.Tactic.«tacticRename_bvar_→__»`

* `rename_bvar old → new` renames all bound variables named `old` to `new` in the target.
* `rename_bvar old → new at h` does the same in hypothesis `h`.

```lean
example (P : ℕ → ℕ → Prop) (h : ∀ n, ∃ m, P n m) : ∀ l, ∃ m, P l m := by
  rename_bvar n → q at h -- h is now ∀ (q : ℕ), ∃ (m : ℕ), P q m,
  rename_bvar m → n -- target is now ∀ (l : ℕ), ∃ (n : ℕ), P k n,
  exact h -- Lean does not care about those bound variable names
```
Note: name clashes are resolved automatically.

## rename_i
Defined in: `Lean.Parser.Tactic.renameI`

`rename_i x_1 ... x_n` renames the last `n` inaccessible names using the given names.

## repeat
Defined in: `Lean.Parser.Tactic.tacticRepeat_`

`repeat tac` repeatedly applies `tac` so long as it succeeds.
The tactic `tac` may be a tactic sequence, and if `tac` fails at any point in its execution,
`repeat` will revert any partial changes that `tac` made to the tactic state.

The tactic `tac` should eventually fail, otherwise `repeat tac` will run indefinitely.

See also:
* `try tac` is like `repeat tac` but will apply `tac` at most once.
* `repeat' tac` recursively applies `tac` to each goal.
* `first | tac1 | tac2` implements the backtracking used by `repeat`

## repeat'
Defined in: `Lean.Parser.Tactic.repeat'`

`repeat' tac` recursively applies `tac` on all of the goals so long as it succeeds.
That is to say, if `tac` produces multiple subgoals, then `repeat' tac` is applied to each of them.

See also:
* `repeat tac` simply repeatedly applies `tac`.
* `repeat1' tac` is `repeat' tac` but requires that `tac` succeed for some goal at least once.

## repeat1
Defined in: `Mathlib.Tactic.tacticRepeat1_`

`repeat1 tac` applies `tac` to main goal at least once. If the application succeeds,
the tactic is applied recursively to the generated subgoals until it eventually fails.

## repeat1'
Defined in: `Lean.Parser.Tactic.repeat1'`

`repeat1' tac` recursively applies to `tac` on all of the goals so long as it succeeds,
but `repeat1' tac` fails if `tac` succeeds on none of the initial goals.

See also:
* `repeat tac` simply applies `tac` repeatedly.
* `repeat' tac` is like `repeat1' tac` but it does not require that `tac` succeed at least once.

## replace
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

## replace
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

## restrict_tac
Defined in: `TopCat.Presheaf.restrict_tac`

`restrict_tac` solves relations among subsets (copied from `aesop cat`)

## restrict_tac?
Defined in: `TopCat.Presheaf.restrict_tac?`

`restrict_tac?` passes along `Try this` from `aesop`

## revert
Defined in: `Lean.Parser.Tactic.revert`

`revert x...` is the inverse of `intro x...`: it moves the given hypotheses
into the main goal's target type.

## rewrite
Defined in: `Lean.Parser.Tactic.rewriteSeq`

`rewrite [e]` applies identity `e` as a rewrite rule to the target of the main goal.
If `e` is preceded by left arrow (`←` or `<-`), the rewrite is applied in the reverse direction.
If `e` is a defined constant, then the equational theorems associated with `e` are used.
This provides a convenient way to unfold `e`.
- `rewrite [e₁, ..., eₙ]` applies the given rules sequentially.
- `rewrite [e] at l` rewrites `e` at location(s) `l`, where `l` is either `*` or a
  list of hypotheses in the local context. In the latter case, a turnstile `⊢` or `|-`
  can also be used, to signify the target of the goal.

Using `rw (occs := .pos L) [e]`,
where `L : List Nat`, you can control which "occurrences" are rewritten.
(This option applies to each rule, so usually this will only be used with a single rule.)
Occurrences count from `1`.
At each allowed occurrence, arguments of the rewrite rule `e` may be instantiated,
restricting which later rewrites can be found.
(Disallowed occurrences do not result in instantiation.)
`(occs := .neg L)` allows skipping specified occurrences.

## rewrite!
Defined in: `Mathlib.Tactic.DepRewrite.depRewriteSeq`

`rewrite!` is like `rewrite`,
but can also insert casts to adjust types that depend on the LHS of a rewrite.
It is available as an ordinary tactic and a `conv` tactic.

The sort of casts that are inserted is controlled by the `castMode` configuration option.
By default, only proof terms are casted;
by proof irrelevance, this adds no observable complexity.

With `rewrite! +letAbs (castMode := .all)`, casts are inserted whenever necessary.
This means that the 'motive is not type correct' error never occurs,
at the expense of creating potentially complicated terms.

## rfl
Defined in: `Lean.Parser.Tactic.tacticRfl`

This tactic applies to a goal whose target has the form `x ~ x`,
where `~` is equality, heterogeneous equality or any relation that
has a reflexivity lemma tagged with the attribute @[refl].

## rfl'
Defined in: `Lean.Parser.Tactic.tacticRfl'`

`rfl'` is similar to `rfl`, but disables smart unfolding and unfolds all kinds of definitions,
theorems included (relevant for declarations defined by well-founded recursion).

## rfl_cat
Defined in: `CategoryTheory.rfl_cat`

`rfl_cat` is a macro for `intros; rfl` which is attempted in `aesop_cat` before
doing the more expensive `aesop` tactic.

This gives a speedup because `simp` (called by `aesop`) can be very slow.
https://github.com/leanprover-community/mathlib4/pull/25475 contains measurements from June 2025.

Implementation notes:
* `refine id ?_`:
  In some cases it is important that the type of the proof matches the expected type exactly.
  e.g. if the goal is `2 = 1 + 1`, the `rfl` tactic will give a proof of type `2 = 2`.
  Starting a proof with `refine id ?_` is a trick to make sure that the proof has exactly
  the expected type, in this case `2 = 1 + 1`. See also
  https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/changing.20a.20proof.20can.20break.20a.20later.20proof
* `apply_rfl`:
  `rfl` is a macro that attempts both `eq_refl` and `apply_rfl`. Since `apply_rfl`
  subsumes `eq_refl`, we can use `apply_rfl` instead. This fails twice as fast as `rfl`.

## rify
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
  rify at hn hk /- Now have hn : 8 ≤ (n : ℝ)   hk : 2 * (k : ℝ) ≤ (n : ℝ) + 2 -/
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

## right
Defined in: `Lean.Parser.Tactic.right`

Applies the second constructor when
the goal is an inductive type with exactly two constructors, or fails otherwise.
```lean
example {p q : Prop} (h : q) : p ∨ q := by
  right
  exact h
```

## ring
Defined in: `Mathlib.Tactic.RingNF.ring`

`ring` solves equations in *commutative* (semi)rings, allowing for variables in the
exponent. If the goal is not appropriate for `ring` (e.g. not an equality) `ring_nf` will be
suggested. See also `ring1`, which fails if the goal is not an equality.

* `ring!` will use a more aggressive reducibility setting to determine equality of atoms.

Examples:
```lean
example (n : ℕ) (m : ℤ) : 2^(n+1) * m = 2 * 2^n * m := by ring
example (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) = (a^2 + b^2 + a * b + b * a) * (a + b)^n := by ring
example (x y : ℕ) : x + id y = y + id x := by ring!
example (x : ℕ) (h : x * 2 > 5): x + x > 5 := by ring; assumption -- suggests ring_nf
```

## ring!
Defined in: `Mathlib.Tactic.RingNF.tacticRing!`

`ring` solves equations in *commutative* (semi)rings, allowing for variables in the
exponent. If the goal is not appropriate for `ring` (e.g. not an equality) `ring_nf` will be
suggested. See also `ring1`, which fails if the goal is not an equality.

* `ring!` will use a more aggressive reducibility setting to determine equality of atoms.

Examples:
```lean
example (n : ℕ) (m : ℤ) : 2^(n+1) * m = 2 * 2^n * m := by ring
example (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) = (a^2 + b^2 + a * b + b * a) * (a + b)^n := by ring
example (x y : ℕ) : x + id y = y + id x := by ring!
example (x : ℕ) (h : x * 2 > 5): x + x > 5 := by ring; assumption -- suggests ring_nf
```

## ring1
Defined in: `Mathlib.Tactic.Ring.ring1`

`ring1` solves the goal when it is an equality in *commutative* (semi)rings,
allowing variables in the exponent.

This version of `ring` fails if the target is not an equality.

* `ring1!` uses a more aggressive reducibility setting to determine equality of atoms.


Extensions:

 * * `ring1_nf` additionally uses `ring_nf` to simplify in atoms.
   * `ring1_nf!` will use a more aggressive reducibility setting
     to determine equality of atoms.

## ring1!
Defined in: `Mathlib.Tactic.Ring.tacticRing1!`

`ring1` solves the goal when it is an equality in *commutative* (semi)rings,
allowing variables in the exponent.

This version of `ring` fails if the target is not an equality.

* `ring1!` uses a more aggressive reducibility setting to determine equality of atoms.


Extensions:

 * * `ring1_nf` additionally uses `ring_nf` to simplify in atoms.
   * `ring1_nf!` will use a more aggressive reducibility setting
     to determine equality of atoms.

## ring1_nf
Defined in: `Mathlib.Tactic.RingNF.ring1NF`

`ring1` solves the goal when it is an equality in *commutative* (semi)rings,
allowing variables in the exponent.

This version of `ring` fails if the target is not an equality.

* `ring1!` uses a more aggressive reducibility setting to determine equality of atoms.


Extensions:

 * * `ring1_nf` additionally uses `ring_nf` to simplify in atoms.
   * `ring1_nf!` will use a more aggressive reducibility setting
     to determine equality of atoms.

## ring1_nf!
Defined in: `Mathlib.Tactic.RingNF.tacticRing1_nf!_`

`ring1` solves the goal when it is an equality in *commutative* (semi)rings,
allowing variables in the exponent.

This version of `ring` fails if the target is not an equality.

* `ring1!` uses a more aggressive reducibility setting to determine equality of atoms.


Extensions:

 * * `ring1_nf` additionally uses `ring_nf` to simplify in atoms.
   * `ring1_nf!` will use a more aggressive reducibility setting
     to determine equality of atoms.

## ring_nf
Defined in: `Mathlib.Tactic.RingNF.ringNF`

`ring_nf` simplifies expressions in the language of commutative (semi)rings,
which rewrites all ring expressions into a normal form, allowing variables in the exponents.

`ring_nf` works as both a tactic and a conv tactic.

See also the `ring` tactic for solving a goal which is an equation in the language
of commutative (semi)rings.

* `ring_nf!` will use a more aggressive reducibility setting to identify atoms.
* `ring_nf (config := cfg)` allows for additional configuration (see `RingNF.Config`):
  * `red`: the reducibility setting (overridden by `!`)
  * `zetaDelta`: if true, local let variables can be unfolded (overridden by `!`)
  * `recursive`: if true, `ring_nf` will also recurse into atoms
* `ring_nf at l1 l2 ...` can be used to rewrite at the given locations.

Examples:
This can be used non-terminally to normalize ring expressions in the goal such as
`⊢ P (x + x + x)` ~> `⊢ P (x * 3)`, as well as being able to prove some equations that
`ring` cannot because they involve ring reasoning inside a subterm, such as
`sin (x + y) + sin (y + x) = 2 * sin (x + y)`.

## ring_nf!
Defined in: `Mathlib.Tactic.RingNF.tacticRing_nf!__`

`ring_nf` simplifies expressions in the language of commutative (semi)rings,
which rewrites all ring expressions into a normal form, allowing variables in the exponents.

`ring_nf` works as both a tactic and a conv tactic.

See also the `ring` tactic for solving a goal which is an equation in the language
of commutative (semi)rings.

* `ring_nf!` will use a more aggressive reducibility setting to identify atoms.
* `ring_nf (config := cfg)` allows for additional configuration (see `RingNF.Config`):
  * `red`: the reducibility setting (overridden by `!`)
  * `zetaDelta`: if true, local let variables can be unfolded (overridden by `!`)
  * `recursive`: if true, `ring_nf` will also recurse into atoms
* `ring_nf at l1 l2 ...` can be used to rewrite at the given locations.

Examples:
This can be used non-terminally to normalize ring expressions in the goal such as
`⊢ P (x + x + x)` ~> `⊢ P (x * 3)`, as well as being able to prove some equations that
`ring` cannot because they involve ring reasoning inside a subterm, such as
`sin (x + y) + sin (y + x) = 2 * sin (x + y)`.

## rintro
Defined in: `Lean.Parser.Tactic.rintro`

The `rintro` tactic is a combination of the `intros` tactic with `rcases` to
allow for destructuring patterns while introducing variables. See `rcases` for
a description of supported patterns. For example, `rintro (a | ⟨b, c⟩) ⟨d, e⟩`
will introduce two variables, and then do case splits on both of them producing
two subgoals, one with variables `a d e` and the other with `b c d e`.

`rintro`, unlike `rcases`, also supports the form `(x y : ty)` for introducing
and type-ascripting multiple variables at once, similar to binders.

## rotate_left
Defined in: `Lean.Parser.Tactic.rotateLeft`

`rotate_left n` rotates goals to the left by `n`. That is, `rotate_left 1`
takes the main goal and puts it to the back of the subgoal list.
If `n` is omitted, it defaults to `1`.

## rotate_right
Defined in: `Lean.Parser.Tactic.rotateRight`

Rotate the goals to the right by `n`. That is, take the goal at the back
and push it to the front `n` times. If `n` is omitted, it defaults to `1`.

## rsuffices
Defined in: `Mathlib.Tactic.rsuffices`

The `rsuffices` tactic is an alternative version of `suffices`, that allows the usage
of any syntax that would be valid in an `obtain` block. This tactic just calls `obtain`
on the expression, and then `rotate_left`.

## run_tac
Defined in: `Lean.Parser.Tactic.runTac`

The `run_tac doSeq` tactic executes code in `TacticM Unit`.

## rw
Defined in: `Lean.Parser.Tactic.rwSeq`

`rw` is like `rewrite`, but also tries to close the goal by "cheap" (reducible) `rfl` afterwards.

## rw!
Defined in: `Mathlib.Tactic.DepRewrite.depRwSeq`

`rw!` is like `rewrite!`, but also cleans up introduced refl-casts after every substitution.
It is available as an ordinary tactic and a `conv` tactic.

## rw?
Defined in: `Lean.Parser.Tactic.rewrites?`

`rw?` tries to find a lemma which can rewrite the goal.

`rw?` should not be left in proofs; it is a search tool, like `apply?`.

Suggestions are printed as `rw [h]` or `rw [← h]`.

You can use `rw? [-my_lemma, -my_theorem]` to prevent `rw?` using the named lemmas.

## rw??
Defined in: `Mathlib.Tactic.LibraryRewrite.tacticRw??`

`rw??` is an interactive tactic that suggests rewrites for any expression selected by the user.
To use it, shift-click an expression in the goal or a hypothesis that you want to rewrite.
Clicking on one of the rewrite suggestions will paste the relevant rewrite tactic into the editor.

The rewrite suggestions are grouped and sorted by the pattern that the rewrite lemmas match with.
Rewrites that don't change the goal and rewrites that create the same goal as another rewrite
are filtered out, as well as rewrites that have new metavariables in the replacement expression.
To see all suggestions, click on the filter button (▼) in the top right.

## rw_mod_cast
Defined in: `Lean.Parser.Tactic.tacticRw_mod_cast___`

Rewrites with the given rules, normalizing casts prior to each step.

## rw_search
Defined in: `Mathlib.Tactic.RewriteSearch.tacticRw_search_`

`rw_search` has been removed from Mathlib.

## rwa
Defined in: `Lean.Parser.Tactic.tacticRwa__`

`rwa` is short-hand for `rw; assumption`.

## saturate
Defined in: `Aesop.Frontend.saturate`


## saturate?
Defined in: `Aesop.Frontend.saturate?`


syntax ..."says"... [Mathlib.Tactic.Says.says]
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

## set
Defined in: `Mathlib.Tactic.setTactic`

`set a := t with h` is a variant of `let a := t`. It adds the hypothesis `h : a = t` to
the local context and replaces `t` with `a` everywhere it can.

`set a := t with ← h` will add `h : t = a` instead.

`set! a := t with h` does not do any replacing.

```lean
example (x : Nat) (h : x + x - x = 3) : x + x - x = 3 := by
  set y := x with ← h2
  sorry
/-
x : Nat
y : Nat := x
h : y + y - y = 3
h2 : x = y
⊢ y + y - y = 3
-/
```

## set!
Defined in: `Mathlib.Tactic.tacticSet!_`

`set a := t with h` is a variant of `let a := t`. It adds the hypothesis `h : a = t` to
the local context and replaces `t` with `a` everywhere it can.

`set a := t with ← h` will add `h : t = a` instead.

`set! a := t with h` does not do any replacing.

```lean
example (x : Nat) (h : x + x - x = 3) : x + x - x = 3 := by
  set y := x with ← h2
  sorry
/-
x : Nat
y : Nat := x
h : y + y - y = 3
h2 : x = y
⊢ y + y - y = 3
-/
```

## set_option
Defined in: `Lean.Parser.Tactic.set_option`

`set_option opt val in tacs` (the tactic) acts like `set_option opt val` at the command level,
but it sets the option only within the tactics `tacs`.

## show
Defined in: `Lean.Parser.Tactic.show`

`show t` finds the first goal whose target unifies with `t`. It makes that the main goal,
performs the unification, and replaces the target with the unified version of `t`.

## show_term
Defined in: `Lean.Parser.Tactic.showTerm`

`show_term tac` runs `tac`, then prints the generated term in the form
"exact X Y Z" or "refine X ?_ Z" (prefixed by `expose_names` if necessary)
if there are remaining subgoals.

(For some tactics, the printed term will not be human readable.)

## simp
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

## simp!
Defined in: `Lean.Parser.Tactic.simpAutoUnfold`

`simp!` is shorthand for `simp` with `autoUnfold := true`.
This will unfold applications of functions defined by pattern matching, when one of the patterns applies.
This can be used to partially evaluate many definitions.

## simp?
Defined in: `Lean.Parser.Tactic.simpTrace`

`simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal. This is useful for reducing the size of the simp
set in a local invocation to speed up processing.
```lean
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- prints "Try this: simp only [ite_true]"
```

This command can also be used in `simp_all` and `dsimp`.

## simp?!
Defined in: `Lean.Parser.Tactic.tacticSimp?!_`

`simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal. This is useful for reducing the size of the simp
set in a local invocation to speed up processing.
```lean
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- prints "Try this: simp only [ite_true]"
```

This command can also be used in `simp_all` and `dsimp`.

## simp_all
Defined in: `Lean.Parser.Tactic.simpAll`

`simp_all` is a stronger version of `simp [*] at *` where the hypotheses and target
are simplified multiple times until no simplification is applicable.
Only non-dependent propositional hypotheses are considered.

## simp_all!
Defined in: `Lean.Parser.Tactic.simpAllAutoUnfold`

`simp_all!` is shorthand for `simp_all` with `autoUnfold := true`.
This will unfold applications of functions defined by pattern matching, when one of the patterns applies.
This can be used to partially evaluate many definitions.

## simp_all?
Defined in: `Lean.Parser.Tactic.simpAllTrace`

`simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal. This is useful for reducing the size of the simp
set in a local invocation to speed up processing.
```lean
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- prints "Try this: simp only [ite_true]"
```

This command can also be used in `simp_all` and `dsimp`.

## simp_all?!
Defined in: `Lean.Parser.Tactic.tacticSimp_all?!_`

`simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal. This is useful for reducing the size of the simp
set in a local invocation to speed up processing.
```lean
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- prints "Try this: simp only [ite_true]"
```

This command can also be used in `simp_all` and `dsimp`.

## simp_all_arith
Defined in: `Lean.Parser.Tactic.simpAllArith`

`simp_all_arith` has been deprecated. It was a shorthand for `simp_all +arith +decide`.
Note that `+decide` is not needed for reducing arithmetic terms since simprocs have been added to Lean.

## simp_all_arith!
Defined in: `Lean.Parser.Tactic.simpAllArithBang`

`simp_all_arith!` has been deprecated. It was a shorthand for `simp_all! +arith +decide`.
Note that `+decide` is not needed for reducing arithmetic terms since simprocs have been added to Lean.

## simp_arith
Defined in: `Lean.Parser.Tactic.simpArith`

`simp_arith` has been deprecated. It was a shorthand for `simp +arith +decide`.
Note that `+decide` is not needed for reducing arithmetic terms since simprocs have been added to Lean.

## simp_arith!
Defined in: `Lean.Parser.Tactic.simpArithBang`

`simp_arith!` has been deprecated. It was a shorthand for `simp! +arith +decide`.
Note that `+decide` is not needed for reducing arithmetic terms since simprocs have been added to Lean.

## simp_intro
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

## simp_rw
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

## simp_wf
Defined in: `tacticSimp_wf`

Unfold definitions commonly used in well founded relation definitions.

Since Lean 4.12, Lean unfolds these definitions automatically before presenting the goal to the
user, and this tactic should no longer be necessary. Calls to `simp_wf` can be removed or replaced
by plain calls to `simp`.

## simpa
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

## simpa!
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

## simpa?
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

## simpa?!
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

## sizeOf_list_dec
Defined in: `List.tacticSizeOf_list_dec`

This tactic, added to the `decreasing_trivial` toolbox, proves that
`sizeOf a < sizeOf as` when `a ∈ as`, which is useful for well founded recursions
over a nested inductive like `inductive T | mk : List T → T`.

## skip
Defined in: `Lean.Parser.Tactic.skip`

`skip` does nothing.

## sleep
Defined in: `Lean.Parser.Tactic.sleep`

The tactic `sleep ms` sleeps for `ms` milliseconds and does nothing.
It is used for debugging purposes only.

## sleep_heartbeats
Defined in: `tacticSleep_heartbeats_`

do nothing for at least n heartbeats

## slice_lhs
Defined in: `Mathlib.Tactic.Slice.sliceLHS`

`slice_lhs a b => tac` zooms to the left-hand side, uses associativity for categorical
composition as needed, zooms in on the `a`-th through `b`-th morphisms, and invokes `tac`.

## slice_rhs
Defined in: `Mathlib.Tactic.Slice.sliceRHS`

`slice_rhs a b => tac` zooms to the right-hand side, uses associativity for categorical
composition as needed, zooms in on the `a`-th through `b`-th morphisms, and invokes `tac`.

## smul_tac
Defined in: `RatFunc.tacticSmul_tac`

Solve equations for `K⟮X⟯` by applying `RatFunc.induction_on`.

## solve
Defined in: `Lean.solveTactic`

Similar to `first`, but succeeds only if one the given tactics solves the current goal.

## solve_by_elim
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

## sorry
Defined in: `Lean.Parser.Tactic.tacticSorry`

The `sorry` tactic is a temporary placeholder for an incomplete tactic proof,
closing the main goal using `exact sorry`.

This is intended for stubbing-out incomplete parts of a proof while still having a syntactically correct proof skeleton.
Lean will give a warning whenever a proof uses `sorry`, so you aren't likely to miss it,
but you can double check if a theorem depends on `sorry` by looking for `sorryAx` in the output
of the `#print axioms my_thm` command, the axiom used by the implementation of `sorry`.

## sorry_if_sorry
Defined in: `CategoryTheory.sorryIfSorry`

Close the main goal with `sorry` if its type contains `sorry`, and fail otherwise.

## specialize
Defined in: `Lean.Parser.Tactic.specialize`

The tactic `specialize h a₁ ... aₙ` works on local hypothesis `h`.
The premises of this hypothesis, either universal quantifications or
non-dependent implications, are instantiated by concrete terms coming
from arguments `a₁` ... `aₙ`.
The tactic adds a new hypothesis with the same name `h := h a₁ ... aₙ`
and tries to clear the previous one.

## specialize_all
Defined in: `Mathlib.Tactic.TautoSet.specialize_all`

`specialize_all x` runs `specialize h x` for all hypotheses `h` where this tactic succeeds.

## split
Defined in: `Lean.Parser.Tactic.split`

The `split` tactic is useful for breaking nested if-then-else and `match` expressions into separate cases.
For a `match` expression with `n` cases, the `split` tactic generates at most `n` subgoals.

For example, given `n : Nat`, and a target `if n = 0 then Q else R`, `split` will generate
one goal with hypothesis `n = 0` and target `Q`, and a second goal with hypothesis
`¬n = 0` and target `R`.  Note that the introduced hypothesis is unnamed, and is commonly
renamed using the `case` or `next` tactics.

- `split` will split the goal (target).
- `split at h` will split the hypothesis `h`.

## split_ands
Defined in: `Batteries.Tactic.tacticSplit_ands`

`split_ands` applies `And.intro` until it does not make progress.

## split_ifs
Defined in: `Mathlib.Tactic.splitIfs`

Splits all if-then-else-expressions into multiple goals.
Given a goal of the form `g (if p then x else y)`, `split_ifs` will produce
two goals: `p ⊢ g x` and `¬p ⊢ g y`.
If there are multiple ite-expressions, then `split_ifs` will split them all,
starting with a top-most one whose condition does not contain another
ite-expression.
`split_ifs at *` splits all ite-expressions in all hypotheses as well as the goal.
`split_ifs with h₁ h₂ h₃` overrides the default names for the hypotheses.

## squeeze_scope
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

## stop
Defined in: `Lean.Parser.Tactic.tacticStop_`

`stop` is a helper tactic for "discarding" the rest of a proof:
it is defined as `repeat sorry`.
It is useful when working on the middle of a complex proofs,
and less messy than commenting the remainder of the proof.

## subsingleton
Defined in: `Mathlib.Tactic.subsingletonStx`

The `subsingleton` tactic tries to prove a goal of the form `x = y` or `x ≍ y`
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

## subst
Defined in: `Lean.Parser.Tactic.subst`

`subst x...` substitutes each hypothesis `x` with a definition found in the local context,
then eliminates the hypothesis.
- If `x` is a local definition, then its definition is used.
- Otherwise, if there is a hypothesis of the form `x = e` or `e = x`,
  then `e` is used for the definition of `x`.

If `h : a = b`, then `subst h` may be used if either `a` or `b` unfolds to a local hypothesis.
This is similar to the `cases h` tactic.

See also: `subst_vars` for substituting all local hypotheses that have a defining equation.

## subst_eqs
Defined in: `Lean.Parser.Tactic.substEqs`

`subst_eq` repeatedly substitutes according to the equality proof hypotheses in the context,
replacing the left side of the equality with the right, until no more progress can be made.

## subst_hom_lift
Defined in: `CategoryTheory.tacticSubst_hom_lift___`

`subst_hom_lift p f φ` tries to substitute `f` with `p(φ)` by using `p.IsHomLift f φ`

## subst_vars
Defined in: `Lean.Parser.Tactic.substVars`

Applies `subst` to all hypotheses of the form `h : x = t` or `h : t = x`.

## substs
Defined in: `Mathlib.Tactic.Substs.substs`

Applies the `subst` tactic to all given hypotheses from left to right.

## success_if_fail_with_msg
Defined in: `Mathlib.Tactic.successIfFailWithMsg`

`success_if_fail_with_msg msg tacs` runs `tacs` and succeeds only if they fail with the message
`msg`.

`msg` can be any term that evaluates to an explicit `String`.

## suffices
Defined in: `Lean.Parser.Tactic.tacticSuffices_`

Given a main goal `ctx ⊢ t`, `suffices h : t' from e` replaces the main goal with `ctx ⊢ t'`,
`e` must have type `t` in the context `ctx, h : t'`.

The variant `suffices h : t' by tac` is a shorthand for `suffices h : t' from by tac`.
If `h :` is omitted, the name `this` is used.

## suffices
Defined in: `Mathlib.Tactic.tacticSuffices_`

Given a main goal `ctx ⊢ t`, `suffices h : t' from e` replaces the main goal with `ctx ⊢ t'`,
`e` must have type `t` in the context `ctx, h : t'`.

The variant `suffices h : t' by tac` is a shorthand for `suffices h : t' from by tac`.
If `h :` is omitted, the name `this` is used.

## suggestions
Defined in: `Lean.Parser.Tactic.suggestions`

`#suggestions` will suggest relevant theorems from the library for the current goal,
using the currently registered library suggestion engine.

The suggestions are printed in the order of their confidence, from highest to lowest.

## swap
Defined in: `Batteries.Tactic.tacticSwap`

`swap` is a shortcut for `pick_goal 2`, which interchanges the 1st and 2nd goals.

## swap_var
Defined in: `Mathlib.Tactic.«tacticSwap_var__,,»`

`swap_var swap_rule₁, swap_rule₂, ⋯` applies `swap_rule₁` then `swap_rule₂` then `⋯`.

A `swap_rule` is of the form `x y` or `x ↔ y`, and "applying it" means swapping the variable name
`x` by `y` and vice-versa on all hypotheses and the goal.

```lean
example {P Q : Prop} (q : P) (p : Q) : P ∧ Q := by
  swap_var p ↔ q
  exact ⟨p, q⟩
```

## symm
Defined in: `Lean.Parser.Tactic.symm`

* `symm` applies to a goal whose target has the form `t ~ u` where `~` is a symmetric relation,
  that is, a relation which has a symmetry lemma tagged with the attribute [symm].
  It replaces the target with `u ~ t`.
* `symm at h` will rewrite a hypothesis `h : t ~ u` to `h : u ~ t`.

## symm_saturate
Defined in: `Lean.Parser.Tactic.symmSaturate`

For every hypothesis `h : a ~ b` where a `@[symm]` lemma is available,
add a hypothesis `h_symm : b ~ a`.

## tauto
Defined in: `Mathlib.Tactic.Tauto.tauto`

`tauto` breaks down assumptions of the form `_ ∧ _`, `_ ∨ _`, `_ ↔ _` and `∃ _, _`
and splits a goal of the form `_ ∧ _`, `_ ↔ _` or `∃ _, _` until it can be discharged
using `rfl` or `solve_by_elim`.
This is a finishing tactic: it either closes the goal or raises an error.

The Lean 3 version of this tactic by default attempted to avoid classical reasoning
where possible. This Lean 4 version makes no such attempt. The `itauto` tactic
is designed for that purpose.

## tauto_set
Defined in: `Mathlib.Tactic.TautoSet.tacticTauto_set`

`tauto_set` attempts to prove tautologies involving hypotheses and goals of the form `X ⊆ Y`
or `X = Y`, where `X`, `Y` are expressions built using ∪, ∩, \, and ᶜ from finitely many
variables of type `Set α`. It also unfolds expressions of the form `Disjoint A B` and
`symmDiff A B`.

Examples:
```lean
example {α} (A B C D : Set α) (h1 : A ⊆ B) (h2 : C ⊆ D) : C \ B ⊆ D \ A := by
  tauto_set

example {α} (A B C : Set α) (h1 : A ⊆ B ∪ C) : (A ∩ B) ∪ (A ∩ C) = A := by
  tauto_set
```

## tfae_finish
Defined in: `Mathlib.Tactic.TFAE.tfaeFinish`

`tfae_finish` closes goals of the form `TFAE [P₁, P₂, ...]` once a sufficient collection
of hypotheses of the form `Pᵢ → Pⱼ` or `Pᵢ ↔ Pⱼ` have been introduced to the local context.

`tfae_have` can be used to conveniently introduce these hypotheses; see `tfae_have`.

Example:
```lean4
example : TFAE [P, Q, R] := by
  tfae_have 1 → 2 := sorry /- proof of P → Q -/
  tfae_have 2 → 1 := sorry /- proof of Q → P -/
  tfae_have 2 ↔ 3 := sorry /- proof of Q ↔ R -/
  tfae_finish
```

## tfae_have
Defined in: `Mathlib.Tactic.TFAE.tfaeHave`

`tfae_have i → j := t`, where the goal is `TFAE [P₁, P₂, ...]` introduces a hypothesis
`tfae_i_to_j : Pᵢ → Pⱼ` and proof `t` to the local context. Note that `i` and `j` are
natural number literals (beginning at 1) used as indices to specify the propositions
`P₁, P₂, ...` that appear in the goal.

Once sufficient hypotheses have been introduced by `tfae_have`, `tfae_finish` can be used to close
the goal.

All features of `have` are supported by `tfae_have`, including naming, matching,
destructuring, and goal creation.

* `tfae_have i ← j := t` adds a hypothesis in the reverse direction, of type `Pⱼ → Pᵢ`.
* `tfae_have i ↔ j := t` adds a hypothesis in the both directions, of type `Pᵢ ↔ Pⱼ`.
* `tfae_have hij : i → j := t` names the introduced hypothesis `hij` instead of `tfae_i_to_j`.
* `tfae_have i j | p₁ => t₁ | ...` matches on the assumption `p : Pᵢ`.
* `tfae_have ⟨hij, hji⟩ : i ↔ j := t` destructures the bi-implication into `hij : Pᵢ → Pⱼ`
  and `hji : Pⱼ → Pⱼ`.
* `tfae_have i → j := t ?a` creates a new goal for `?a`.

Examples:
```lean4
example (h : P → R) : TFAE [P, Q, R] := by
  tfae_have 1 → 3 := h
  -- The resulting context now includes `tfae_1_to_3 : P → R`.
  sorry
```

```lean4
-- An example of `tfae_have` and `tfae_finish`:
example : TFAE [P, Q, R] := by
  tfae_have 1 → 2 := sorry /- proof of P → Q -/
  tfae_have 2 → 1 := sorry /- proof of Q → P -/
  tfae_have 2 ↔ 3 := sorry /- proof of Q ↔ R -/
  tfae_finish
```

```lean4
-- All features of `have` are supported by `tfae_have`:
example : TFAE [P, Q] := by
  -- assert `tfae_1_to_2 : P → Q`:
  tfae_have 1 → 2 := sorry

  -- assert `hpq : P → Q`:
  tfae_have hpq : 1 → 2 := sorry

  -- match on `p : P` and prove `Q` via `f p`:
  tfae_have 1 → 2
  | p => f p

  -- assert `pq : P → Q`, `qp : Q → P`:
  tfae_have ⟨pq, qp⟩ : 1 ↔ 2 := sorry

  -- assert `h : P → Q`; `?a` is a new goal:
  tfae_have h : 1 → 2 := f ?a

  sorry
```

## tfae_have
Defined in: `Mathlib.Tactic.TFAE.tfaeHave'`

`tfae_have i → j := t`, where the goal is `TFAE [P₁, P₂, ...]` introduces a hypothesis
`tfae_i_to_j : Pᵢ → Pⱼ` and proof `t` to the local context. Note that `i` and `j` are
natural number literals (beginning at 1) used as indices to specify the propositions
`P₁, P₂, ...` that appear in the goal.

Once sufficient hypotheses have been introduced by `tfae_have`, `tfae_finish` can be used to close
the goal.

All features of `have` are supported by `tfae_have`, including naming, matching,
destructuring, and goal creation.

* `tfae_have i ← j := t` adds a hypothesis in the reverse direction, of type `Pⱼ → Pᵢ`.
* `tfae_have i ↔ j := t` adds a hypothesis in the both directions, of type `Pᵢ ↔ Pⱼ`.
* `tfae_have hij : i → j := t` names the introduced hypothesis `hij` instead of `tfae_i_to_j`.
* `tfae_have i j | p₁ => t₁ | ...` matches on the assumption `p : Pᵢ`.
* `tfae_have ⟨hij, hji⟩ : i ↔ j := t` destructures the bi-implication into `hij : Pᵢ → Pⱼ`
  and `hji : Pⱼ → Pⱼ`.
* `tfae_have i → j := t ?a` creates a new goal for `?a`.

Examples:
```lean4
example (h : P → R) : TFAE [P, Q, R] := by
  tfae_have 1 → 3 := h
  -- The resulting context now includes `tfae_1_to_3 : P → R`.
  sorry
```

```lean4
-- An example of `tfae_have` and `tfae_finish`:
example : TFAE [P, Q, R] := by
  tfae_have 1 → 2 := sorry /- proof of P → Q -/
  tfae_have 2 → 1 := sorry /- proof of Q → P -/
  tfae_have 2 ↔ 3 := sorry /- proof of Q ↔ R -/
  tfae_finish
```

```lean4
-- All features of `have` are supported by `tfae_have`:
example : TFAE [P, Q] := by
  -- assert `tfae_1_to_2 : P → Q`:
  tfae_have 1 → 2 := sorry

  -- assert `hpq : P → Q`:
  tfae_have hpq : 1 → 2 := sorry

  -- match on `p : P` and prove `Q` via `f p`:
  tfae_have 1 → 2
  | p => f p

  -- assert `pq : P → Q`, `qp : Q → P`:
  tfae_have ⟨pq, qp⟩ : 1 ↔ 2 := sorry

  -- assert `h : P → Q`; `?a` is a new goal:
  tfae_have h : 1 → 2 := f ?a

  sorry
```

## toFinite_tac
Defined in: `Set.tacticToFinite_tac`

A tactic (for use in default params) that applies `Set.toFinite` to synthesize a `Set.Finite`
term.

## to_encard_tac
Defined in: `Set.tacticTo_encard_tac`

A tactic useful for transferring proofs for `encard` to their corresponding `card` statements

## trace
Defined in: `Lean.Parser.Tactic.trace`

Evaluates a term to a string (when possible), and prints it as a trace message.

## trace
Defined in: `Lean.Parser.Tactic.traceMessage`

`trace msg` displays `msg` in the info view.

## trace_state
Defined in: `Lean.Parser.Tactic.traceState`

`trace_state` displays the current state in the info view.

## trans
Defined in: `Batteries.Tactic.tacticTrans___`

`trans` applies to a goal whose target has the form `t ~ u` where `~` is a transitive relation,
that is, a relation which has a transitivity lemma tagged with the attribute [trans].

* `trans s` replaces the goal with the two subgoals `t ~ s` and `s ~ u`.
* If `s` is omitted, then a metavariable is used instead.

Additionally, `trans` also applies to a goal whose target has the form `t → u`,
in which case it replaces the goal with `t → s` and `s → u`.

## transitivity
Defined in: `Batteries.Tactic.tacticTransitivity___`

Synonym for `trans` tactic.

## triv
Defined in: `Batteries.Tactic.triv`

Deprecated variant of `trivial`.

## trivial
Defined in: `Lean.Parser.Tactic.tacticTrivial`

`trivial` tries different simple tactics (e.g., `rfl`, `contradiction`, ...)
to close the current goal.
You can use the command `macro_rules` to extend the set of tactics used. Example:
```lean
macro_rules | `(tactic| trivial) => `(tactic| simp)
```

## try
Defined in: `Lean.Parser.Tactic.tacticTry_`

`try tac` runs `tac` and succeeds even if `tac` failed.

## try?
Defined in: `Lean.Parser.Tactic.tryTrace`


## try_suggestions
Defined in: `Lean.Parser.Tactic.tryResult`

Helper internal tactic used to implement `evalSuggest` in `try?`

## try_this
Defined in: `Mathlib.Tactic.tacticTry_this__`

Produces the text `Try this: <tac>` with the given tactic, and then executes it.

## type_check
Defined in: `tacticType_check_`

Type check the given expression, and trace its type.

## unfold
Defined in: `Lean.Parser.Tactic.unfold`

* `unfold id` unfolds all occurrences of definition `id` in the target.
* `unfold id1 id2 ...` is equivalent to `unfold id1; unfold id2; ...`.
* `unfold id at h` unfolds at the hypothesis `h`.

Definitions can be either global or local definitions.

For non-recursive global definitions, this tactic is identical to `delta`.
For recursive global definitions, it uses the "unfolding lemma" `id.eq_def`,
which is generated for each recursive definition, to unfold according to the recursive definition given by the user.
Only one level of unfolding is performed, in contrast to `simp only [id]`, which unfolds definition `id` recursively.

## unfold?
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

## unfold_projs
Defined in: `Mathlib.Tactic.unfoldProjsStx`

`unfold_projs at loc` unfolds projections of class instances at the given location.
This also exists as a `conv`-mode tactic.

## unhygienic
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

## uniqueDiffWithinAt_Ici_Iic_univ
Defined in: `intervalIntegral.tacticUniqueDiffWithinAt_Ici_Iic_univ`

An auxiliary tactic closing goals `UniqueDiffWithinAt ℝ s a` where
`s ∈ {Iic a, Ici a, univ}`.

## unit_interval
Defined in: `Tactic.Interactive.tacticUnit_interval`

A tactic that solves `0 ≤ ↑x`, `0 ≤ 1 - ↑x`, `↑x ≤ 1`, and `1 - ↑x ≤ 1` for `x : I`.

## unreachable!
Defined in: `Batteries.Tactic.unreachable`

This tactic causes a panic when run (at compile time).
(This is distinct from `exact unreachable!`, which inserts code which will panic at run time.)

It is intended for tests to assert that a tactic will never be executed, which is otherwise an
unusual thing to do (and the `unreachableTactic` linter will give a warning if you do).

The `unreachableTactic` linter has a special exception for uses of `unreachable!`.
```
example : True := by trivial <;> unreachable!
```

## use
Defined in: `Mathlib.Tactic.useSyntax`

`use e₁, e₂, ⋯` instantiates all existential quantifiers in the main goal by using `e₁`, `e₂`, ...
as witnesses, creates goals for all the remaining witnesses, and tries to discharge these goals
automatically.

`use` is similar to `exists` or `existsi`, but unlike `exists` it is equivalent to applying the
tactic `refine ⟨e₁, e₂, ⋯, ?_, ⋯, ?_⟩` with any number of placeholders (rather than just one) and
then trying to close goals associated to the placeholders with a configurable discharger (rather
than just `try trivial`).

* `use! e₁, e₂, ⋯` applies constructors everywhere rather than just for goals that correspond to the
  last argument of a constructor. This gives the effect that nested constructors are being flattened
  out, with the supplied values being used along the leaves and nodes of the tree of constructors.
* `use (discharger := tac) e₁, e₂, ...` calls `tac` as a discharger, on all remaining `Prop`-valued
  goals. If this option is omitted, `use` calls `try with_reducible use_discharger` as default
  discharger.
  To turn off the discharger and keep all goals, use `(discharger := skip)`.
  To allow "heavy refls", use `(discharger := try use_discharger)`.
  If `tac` fails on the new goal, `use (discharger := tac)` fails (hint: you might want to use
  `(discharger := try tac)` instead).

Examples:

```lean
example : ∃ x : Nat, x = x := by use 42

example : ∃ x : Nat, ∃ y : Nat, x = y := by use 42, 42

example : Nonempty Nat := by use 5

example : Nonempty (PNat ≃ Nat) := by
  use PNat.natPred, Nat.succPNat
  · exact PNat.succPNat_natPred
  · intro; rfl

-- With `use!` one can feed in each `42` one at a time:
example : ∃ n : {n : Nat // n % 2 = 0}, n.val > 10 := by use! 20; simp

example : ∃ p : Nat × Nat, p.1 = p.2 := by use! (42, 42)
/-
The second line makes use of the fact that `use!` tries refining with the argument before
applying a constructor. Also note that `use`/`use!` by default uses a tactic
called `use_discharger` to discharge goals, so `use! 42` will close the goal in this example since
`use_discharger` applies `rfl`, which as a consequence solves for the other `Nat` metavariable.
-/
```

## use!
Defined in: `Mathlib.Tactic.«tacticUse!___,,»`

`use e₁, e₂, ⋯` instantiates all existential quantifiers in the main goal by using `e₁`, `e₂`, ...
as witnesses, creates goals for all the remaining witnesses, and tries to discharge these goals
automatically.

`use` is similar to `exists` or `existsi`, but unlike `exists` it is equivalent to applying the
tactic `refine ⟨e₁, e₂, ⋯, ?_, ⋯, ?_⟩` with any number of placeholders (rather than just one) and
then trying to close goals associated to the placeholders with a configurable discharger (rather
than just `try trivial`).

* `use! e₁, e₂, ⋯` applies constructors everywhere rather than just for goals that correspond to the
  last argument of a constructor. This gives the effect that nested constructors are being flattened
  out, with the supplied values being used along the leaves and nodes of the tree of constructors.
* `use (discharger := tac) e₁, e₂, ...` calls `tac` as a discharger, on all remaining `Prop`-valued
  goals. If this option is omitted, `use` calls `try with_reducible use_discharger` as default
  discharger.
  To turn off the discharger and keep all goals, use `(discharger := skip)`.
  To allow "heavy refls", use `(discharger := try use_discharger)`.
  If `tac` fails on the new goal, `use (discharger := tac)` fails (hint: you might want to use
  `(discharger := try tac)` instead).

Examples:

```lean
example : ∃ x : Nat, x = x := by use 42

example : ∃ x : Nat, ∃ y : Nat, x = y := by use 42, 42

example : Nonempty Nat := by use 5

example : Nonempty (PNat ≃ Nat) := by
  use PNat.natPred, Nat.succPNat
  · exact PNat.succPNat_natPred
  · intro; rfl

-- With `use!` one can feed in each `42` one at a time:
example : ∃ n : {n : Nat // n % 2 = 0}, n.val > 10 := by use! 20; simp

example : ∃ p : Nat × Nat, p.1 = p.2 := by use! (42, 42)
/-
The second line makes use of the fact that `use!` tries refining with the argument before
applying a constructor. Also note that `use`/`use!` by default uses a tactic
called `use_discharger` to discharge goals, so `use! 42` will close the goal in this example since
`use_discharger` applies `rfl`, which as a consequence solves for the other `Nat` metavariable.
-/
```

## use_discharger
Defined in: `Mathlib.Tactic.tacticUse_discharger`

`use_discharger` is used by `use` to discharge side goals.

This is an extensible tactic using `macro_rules`. By default it can:
* rewrite a goal `∃ _ : p, q` into `p ∧ q` if `p` is in Prop;
* solve the goal `p ∧ q` by creating subgoals `p` and `q`;
* apply `rfl`;
* solve a goal by applying an assumption;
* solve the goal `True`.

## use_finite_instance
Defined in: `tacticUse_finite_instance`

Try using `Set.toFinite` to dispatch a `Set.Finite` goal.

## valid
Defined in: `CategoryTheory.ComposableArrows.tacticValid`

A wrapper for `omega` which prefaces it with some quick and useful attempts

## volume_tac
Defined in: `MeasureTheory.tacticVolume_tac`

The tactic `exact volume`, to be used in optional (`autoParam`) arguments.

## wait_for_unblock_async
Defined in: `Lean.Server.Test.Cancel.tacticWait_for_unblock_async`

Spawns a `logSnapshotTask` that waits for `unblock` to be called, which is expected to happen in a
subsequent document version that does not invalidate this tactic. Complains if cancellation token
was set before unblocking, i.e. if the tactic was invalidated after all.

## whisker_simps
Defined in: `Mathlib.Tactic.BicategoryCoherence.whisker_simps`

Simp lemmas for rewriting a 2-morphism into a normal form.

## whnf
Defined in: `Mathlib.Tactic.tacticWhnf__`

`whnf at loc` puts the given location into weak-head normal form.
This also exists as a `conv`-mode tactic.

Weak-head normal form is when the outer-most expression has been fully reduced, the expression
may contain subexpressions which have not been reduced.

## with_panel_widgets
Defined in: `ProofWidgets.withPanelWidgetsTacticStx`

Display the selected panel widgets in the nested tactic script. For example,
assuming we have written a `GeometryDisplay` component,
```lean
by with_panel_widgets [GeometryDisplay]
  simp
  rfl
```
will show the geometry display alongside the usual tactic state throughout the proof.

## with_reducible
Defined in: `Lean.Parser.Tactic.withReducible`

`with_reducible tacs` executes `tacs` using the reducible transparency setting.
In this setting only definitions tagged as `[reducible]` are unfolded.

## with_reducible_and_instances
Defined in: `Lean.Parser.Tactic.withReducibleAndInstances`

`with_reducible_and_instances tacs` executes `tacs` using the `.instances` transparency setting.
In this setting only definitions tagged as `[reducible]` or type class instances are unfolded.

## with_unfolding_all
Defined in: `Lean.Parser.Tactic.withUnfoldingAll`

`with_unfolding_all tacs` executes `tacs` using the `.all` transparency setting.
In this setting all definitions that are not opaque are unfolded.

## with_unfolding_none
Defined in: `Lean.Parser.Tactic.withUnfoldingNone`

`with_unfolding_none tacs` executes `tacs` using the `.none` transparency setting.
In this setting no definitions are unfolded.

## witt_truncateFun_tac
Defined in: `witt_truncateFun_tac`

A macro tactic used to prove that `truncateFun` respects ring operations.

## wlog
Defined in: `Mathlib.Tactic.wlog`

`wlog h : P` adds an assumption `h : P` to the main goal, and adds a side goal that
requires showing that the case `h : ¬ P` can be reduced to the case where `P` holds
(typically by symmetry). The side goal will be at the top of the stack. In this side goal,
there will be two additional assumptions:
- `h : ¬ P`: the assumption that `P` does not hold
- `this`: which is the statement that in the old context `P` suffices to prove the goal.
  By default, the entire context is reverted to produce `this`.

* `wlog h : P with H` gives the name `H` to the statement that `P` proves the goal.
* `wlog h : P generalizing x y ...` reverts certain parts of the context before creating the new
  goal. In this way, the wlog-claim `this` can be applied to `x` and `y` in different orders
  (exploiting symmetry, which is the typical use case).
* `wlog! h : P` also calls `push Not` at the generated hypothesis `h`.
  `wlog! h : P ∧ Q` will transform `¬ (P ∧ Q)` to `P → ¬ Q`
* `wlog! +distrib h : P` also calls `push +distrib Not` at the generated hypothesis `h`.
  `wlog! +distrib h : P ∧ Q` will transform `¬ (P ∧ Q)` to `¬P ∨ ¬Q`.

## wlog!
Defined in: `Mathlib.Tactic.wlog!`

`wlog h : P` adds an assumption `h : P` to the main goal, and adds a side goal that
requires showing that the case `h : ¬ P` can be reduced to the case where `P` holds
(typically by symmetry). The side goal will be at the top of the stack. In this side goal,
there will be two additional assumptions:
- `h : ¬ P`: the assumption that `P` does not hold
- `this`: which is the statement that in the old context `P` suffices to prove the goal.
  By default, the entire context is reverted to produce `this`.

* `wlog h : P with H` gives the name `H` to the statement that `P` proves the goal.
* `wlog h : P generalizing x y ...` reverts certain parts of the context before creating the new
  goal. In this way, the wlog-claim `this` can be applied to `x` and `y` in different orders
  (exploiting symmetry, which is the typical use case).
* `wlog! h : P` also calls `push Not` at the generated hypothesis `h`.
  `wlog! h : P ∧ Q` will transform `¬ (P ∧ Q)` to `P → ¬ Q`
* `wlog! +distrib h : P` also calls `push +distrib Not` at the generated hypothesis `h`.
  `wlog! +distrib h : P ∧ Q` will transform `¬ (P ∧ Q)` to `¬P ∨ ¬Q`.

## zify
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

## {
Defined in: `Lean.Parser.Tactic.nestedTactic`


## ·
Defined in: `Lean.cdot`

`· tac` focuses on the main goal and tries to solve it using `tac`, or else fails.

## ∎
Defined in: `«tactic∎»`

`∎` (typed as `\qed`) is a macro that expands to `try?` in tactic mode.

