Lean version: `{{#include ../lean-toolchain}}`

# \#adaptation_note
Defined in: `adaptationNoteCmd`

Adaptation notes are comments that are used to indicate that a piece of code
has been changed to accomodate a change in Lean core.
They typically require further action/maintenance to be taken in the future.

# \#aesop_rules
Defined in: `Aesop.Frontend.Parser.«command#aesop_rules»`


# \#aesop_stats
Defined in: `Aesop.Frontend.Parser.«command#aesop_stats_»`


# \#allow_unused_tactic
Defined in: `Mathlib.Linter.UnusedTactic.«command#allow_unused_tactic_»`

`#allow_unused_tactic` takes an input a space-separated list of identifiers.
These identifiers are then allowed by the unused tactic linter:
even if these tactics do not modify goals, there will be no warning emitted.
Note: for this to work, these identifiers should be the `SyntaxNodeKind` of each tactic.

For instance, you can allow the `done` and `skip` tactics using
```lean
#allow_unused_tactic Lean.Parser.Tactic.done Lean.Parser.Tactic.skip
```
Notice that you should use the `SyntaxNodeKind` of the tactic.

# \#check
Defined in: `Lean.Parser.Command.check`


# \#check_failure
Defined in: `Lean.Parser.Command.check_failure`


# \#check_simp
Defined in: `Lean.Parser.checkSimp`

`#check_simp t ~> r` checks `simp` reduces `t` to `r`.

# \#check_simp
Defined in: `Lean.Parser.checkSimpFailure`

`#check_simp t !~>` checks `simp` fails on reducing `t`.

# \#check_tactic
Defined in: `Lean.Parser.checkTactic`

`#check_tactic t ~> r by commands` runs the tactic sequence `commands`
on a goal with `t` and sees if the resulting expression has reduced it
to `r`.

# \#check_tactic_failure
Defined in: `Lean.Parser.checkTacticFailure`

`#check_tactic_failure t by tac` runs the tactic `tac`
on a goal with `t` and verifies it fails.

# \#conv
Defined in: `Mathlib.Tactic.Conv.«command#conv_=>_»`

The command `#conv tac => e` will run a conv tactic `tac` on `e`, and display the resulting
expression (discarding the proof).
For example, `#conv rw [true_and_iff] => True ∧ False` displays `False`.
There are also shorthand commands for several common conv tactics:

* `#whnf e` is short for `#conv whnf => e`
* `#simp e` is short for `#conv simp => e`
* `#norm_num e` is short for `#conv norm_num => e`
* `#push_neg e` is short for `#conv push_neg => e`

# \#discr_tree_key
Defined in: `Lean.Parser.discrTreeKeyCmd`

`#discr_tree_key  t` prints the discrimination tree keys for a term `t` (or, if it is a single identifier, the type of that constant).
It uses the default configuration for generating keys.

For example,
```
#discr_tree_key (∀ {a n : Nat}, bar a (OfNat.ofNat n))
-- bar _ (@OfNat.ofNat Nat _ _)

#discr_tree_simp_key Nat.add_assoc
-- @HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ _ _) _
```

`#discr_tree_simp_key` is similar to `#discr_tree_key`, but treats the underlying type
as one of a simp lemma, i.e. transforms it into an equality and produces the key of the
left-hand side.

# \#discr_tree_simp_key
Defined in: `Lean.Parser.discrTreeSimpKeyCmd`

`#discr_tree_key  t` prints the discrimination tree keys for a term `t` (or, if it is a single identifier, the type of that constant).
It uses the default configuration for generating keys.

For example,
```
#discr_tree_key (∀ {a n : Nat}, bar a (OfNat.ofNat n))
-- bar _ (@OfNat.ofNat Nat _ _)

#discr_tree_simp_key Nat.add_assoc
-- @HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ _ _) _
```

`#discr_tree_simp_key` is similar to `#discr_tree_key`, but treats the underlying type
as one of a simp lemma, i.e. transforms it into an equality and produces the key of the
left-hand side.

# \#eval
Defined in: `Lean.Parser.Command.eval`


# \#eval!
Defined in: `Lean.Parser.Command.evalBang`


# \#exit
Defined in: `Lean.Parser.Command.exit`


# \#explode
Defined in: `Mathlib.Explode.«command#explode_»`

`#explode expr` displays a proof term in a line-by-line format somewhat akin to a Fitch-style
proof or the Metamath proof style.

For example, exploding the following theorem:

```lean
#explode iff_of_true
```

produces:

```lean
iff_of_true : ∀ {a b : Prop}, a → b → (a ↔ b)

0│         │ a         ├ Prop
1│         │ b         ├ Prop
2│         │ ha        ├ a
3│         │ hb        ├ b
4│         │ x✝        │ ┌ a
5│4,3      │ ∀I        │ a → b
6│         │ x✝        │ ┌ b
7│6,2      │ ∀I        │ b → a
8│5,7      │ Iff.intro │ a ↔ b
9│0,1,2,3,8│ ∀I        │ ∀ {a b : Prop}, a → b → (a ↔ b)
```

## Overview

The `#explode` command takes the body of the theorem and decomposes it into its parts,
displaying each expression constructor one at a time. The constructor is indicated
in some way in column 3, and its dependencies are recorded in column 2.

These are the main constructor types:

  - Lambda expressions (`Expr.lam`). The expression `fun (h : p) => s` is displayed as
    ```lean
     0│    │ h   │ ┌ p
     1│**  │ **  │ │ q
     2│1,2 │ ∀I  │ ∀ (h : p), q
    ```
    with `**` a wildcard, and there can be intervening steps between 0 and 1.
    Nested lambda expressions can be merged, and `∀I` can depend on a whole list of arguments.

  - Applications (`Expr.app`). The expression `f a b c` is displayed as
     ```lean
     0│**      │ f  │ A → B → C → D
     1│**      │ a  │ A
     2│**      │ b  │ B
     3│**      │ c  │ C
     1│0,1,2,3 │ ∀E │ D
     ```
     There can be intervening steps between each of these.
     As a special case, if `f` is a constant it can be omitted and the display instead looks like
     ```lean
     0│**    │ a │ A
     1│**    │ b │ B
     2│**    │ c │ C
     3│1,2,3 │ f │ D
     ```

  - Let expressions (`Expr.letE`) do not display in any special way, but they do
    ensure that in `let x := v; b` that `v` is processed first and then `b`, rather
    than first doing zeta reduction. This keeps lambda merging and application merging
    from making proofs with `let` confusing to interpret.

  - Everything else (constants, fvars, etc.) display `x : X` as
    ```lean
    0│  │ x │ X
    ```

## In more detail

The output of `#explode` is a Fitch-style proof in a four-column diagram modeled after Metamath
proof displays like [this](http://us.metamath.org/mpeuni/ru.html). The headers of the columns are
"Step", "Hyp", "Ref", "Type" (or "Expression" in the case of Metamath):
* **Step**: An increasing sequence of numbers for each row in the proof, used in the Hyp fields.
* **Hyp**: The direct children of the current step. These are step numbers for the subexpressions
  for this step's expression. For theorem applications, it's the theorem arguments, and for
  foralls it is all the bound variables and the conclusion.
* **Ref**: The name of the theorem being applied. This is well-defined in Metamath, but in Lean
  there are some special steps that may have long names because the structure of proof terms doesn't
  exactly match this mold.
  * If the theorem is `foo (x y : Z) : A x -> B y -> C x y`:
    * the Ref field will contain `foo`,
    * `x` and `y` will be suppressed, because term construction is not interesting, and
    * the Hyp field will reference steps proving `A x` and `B y`. This corresponds to a proof term
      like `@foo x y pA pB` where `pA` and `pB` are subproofs.
    * In the Hyp column, suppressed terms are omitted, including terms that ought to be
      suppressed but are not (in particular lambda arguments).
      TODO: implement a configuration option to enable representing suppressed terms using
      an `_` rather than a step number.
  * If the head of the proof term is a local constant or lambda, then in this case the Ref will
    say `∀E` for forall-elimination. This happens when you have for example `h : A -> B` and
    `ha : A` and prove `b` by `h ha`; we reinterpret this as if it said `∀E h ha` where `∀E` is
    (n-ary) modus ponens.
  * If the proof term is a lambda, we will also use `∀I` for forall-introduction, referencing the
    body of the lambda. The indentation level will increase, and a bracket will surround the proof
    of the body of the lambda, starting at a proof step labeled with the name of the lambda variable
    and its type, and ending with the `∀I` step. Metamath doesn't have steps like this, but the
    style is based on Fitch proofs in first-order logic.
* **Type**: This contains the type of the proof term, the theorem being proven at the current step.

Also, it is common for a Lean theorem to begin with a sequence of lambdas introducing local
constants of the theorem. In order to minimize the indentation level, the `∀I` steps at the end of
the proof will be introduced in a group and the indentation will stay fixed. (The indentation
brackets are only needed in order to delimit the scope of assumptions, and these assumptions
have global scope anyway so detailed tracking is not necessary.)

# \#find
Defined in: `Mathlib.Tactic.Find.«command#find_»`


# \#find_home
Defined in: `«command#find_home!_»`

Find locations as high as possible in the import hierarchy
where the named declaration could live.
Using `#find_home!` will forcefully remove the current file.
Note that this works best if used in a file with `import Mathlib`.

The current file could still be the only suggestion, even using `#find_home! lemma`.
The reason is that `#find_home!` scans the import graph below the current file,
selects all the files containing declarations appearing in `lemma`, excluding
the current file itself and looks for all least upper bounds of such files.

For a simple example, if `lemma` is in a file importing only `A.lean` and `B.lean` and
uses one lemma from each, then `#find_home! lemma` returns the current file.

# \#guard
Defined in: `Lean.Parser.Command.guardCmd`

Command to check that an expression evaluates to `true`.

`#guard e` elaborates `e` ensuring its type is `Bool` then evaluates `e` and checks that
the result is `true`. The term is elaborated *without* variables declared using `variable`, since
these cannot be evaluated.

Since this makes use of coercions, so long as a proposition `p` is decidable, one can write
`#guard p` rather than `#guard decide p`. A consequence to this is that if there is decidable
equality one can write `#guard a = b`. Note that this is not exactly the same as checking
if `a` and `b` evaluate to the same thing since it uses the `DecidableEq` instance to do
the evaluation.

Note: this uses the untrusted evaluator, so `#guard` passing is *not* a proof that the
expression equals `true`.

# \#guard_expr
Defined in: `Lean.Parser.Command.guardExprCmd`

Command to check equality of two expressions.
* `#guard_expr e = e'` checks that `e` and `e'` are defeq at reducible transparency.
* `#guard_expr e =~ e'` checks that `e` and `e'` are defeq at default transparency.
* `#guard_expr e =ₛ e'` checks that `e` and `e'` are syntactically equal.
* `#guard_expr e =ₐ e'` checks that `e` and `e'` are alpha-equivalent.

This is a command version of the `guard_expr` tactic.

# \#guard_msgs
Defined in: `Lean.guardMsgsCmd`

`/-- ... -/ #guard_msgs in cmd` captures the messages generated by the command `cmd`
and checks that they match the contents of the docstring.

Basic example:
```lean
/--
error: unknown identifier 'x'
-/
#guard_msgs in
example : α := x
```
This checks that there is such an error and then consumes the message.

By default, the command captures all messages, but the filter condition can be adjusted.
For example, we can select only warnings:
```lean
/--
warning: declaration uses 'sorry'
-/
#guard_msgs(warning) in
example : α := sorry
```
or only errors
```lean
#guard_msgs(error) in
example : α := sorry
```
In the previous example, since warnings are not captured there is a warning on `sorry`.
We can drop the warning completely with
```lean
#guard_msgs(error, drop warning) in
example : α := sorry
```

In general, `#guard_msgs` accepts a comma-separated list of configuration clauses in parentheses:
```lean
#guard_msgs (configElt,*) in cmd
```
By default, the configuration list is `(all, whitespace := normalized, ordering := exact)`.

Message filters (processed in left-to-right order):
- `info`, `warning`, `error`: capture messages with the given severity level.
- `all`: capture all messages (the default).
- `drop info`, `drop warning`, `drop error`: drop messages with the given severity level.
- `drop all`: drop every message.

Whitespace handling (after trimming leading and trailing whitespace):
- `whitespace := exact` requires an exact whitespace match.
- `whitespace := normalized` converts all newline characters to a space before matching
  (the default). This allows breaking long lines.
- `whitespace := lax` collapses whitespace to a single space before matching.

Message ordering:
- `ordering := exact` uses the exact ordering of the messages (the default).
- `ordering := sorted` sorts the messages in lexicographic order.
  This helps with testing commands that are non-deterministic in their ordering.

For example, `#guard_msgs (error, drop all) in cmd` means to check warnings and drop
everything else.

# \#help
Defined in: `Mathlib.Tactic.«command#help_Cats___»`

The command `#help cats` shows all syntax categories that have been defined in the
current environment.
Each syntax has a format like:
```lean
category command [Lean.Parser.initFn✝]
```
The name of the syntax category in this case is `command`, and `Lean.Parser.initFn✝` is the
name of the declaration that introduced it. (It is often an anonymous declaration like this,
but you can click to go to the definition.) It also shows the doc string if available.

The form `#help cats id` will show only syntax categories that begin with `id`.

# \#help
Defined in: `Mathlib.Tactic.«command#help_Tactic+____»`

The command `#help tactic` shows all tactics that have been defined in the current environment.
See `#help cat` for more information.

# \#help
Defined in: `Mathlib.Tactic.«command#help_Conv+____»`

The command `#help conv` shows all tactics that have been defined in the current environment.
See `#help cat` for more information.

# \#help
Defined in: `Mathlib.Tactic.«command#help_Option___»`

The command `#help option` shows all options that have been defined in the current environment.
Each option has a format like:
```lean
option pp.all : Bool := false
  (pretty printer) display coercions, implicit parameters, proof terms, fully qualified names,
  universe, and disable beta reduction and notations during pretty printing
```
This says that `pp.all` is an option which can be set to a `Bool` value, and the default value is
`false`. If an option has been modified from the default using e.g. `set_option pp.all true`,
it will appear as a `(currently: true)` note next to the option.

The form `#help option id` will show only options that begin with `id`.

# \#help
Defined in: `Mathlib.Tactic.«command#help_Term+____»`

The command `#help term` shows all term syntaxes that have been defined in the current environment.
See `#help cat` for more information.

# \#help
Defined in: `Mathlib.Tactic.«command#help_Cat+______»`

The command `#help cat C` shows all syntaxes that have been defined in syntax category `C` in the
current environment.
Each syntax has a format like:
```lean
# first
Defined in: `Parser.tactic.first`

  `first | tac | ...` runs each `tac` until one succeeds, or else fails.
```lean
The quoted string is the leading token of the syntax, if applicable. It is followed by the full
name of the syntax (which you can also click to go to the definition), and the documentation.

* The form `#help cat C id` will show only attributes that begin with `id`.
* The form `#help cat+ C` will also show information about any `macro`s and `elab`s
  associated to the listed syntaxes.

# \#help
Defined in: `Mathlib.Tactic.«command#help_Command+____»`

The command `#help command` shows all commands that have been defined in the current environment.
See `#help cat` for more information.

# \#help
Defined in: `Mathlib.Tactic.«command#help_AttrAttribute___»`

The command `#help attribute` (or the short form `#help attr`) shows all attributes that have been
defined in the current environment.
Each attribute has a format like:
```lean
[inline]: mark definition to always be inlined
```
This says that `inline` is an attribute that can be placed on definitions like
`@[inline] def foo := 1`. (Individual attributes may have restrictions on where they can be
applied; see the attribute's documentation for details.) Both the attribute's `descr` field as well
as the docstring will be displayed here.

The form `#help attr id` will show only attributes that begin with `id`.

# \#instances
Defined in: `Batteries.Tactic.Instances.instancesCmd`

`#instances term` prints all the instances for the given class.
For example, `#instances Add _` gives all `Add` instances, and `#instances Add Nat` gives the
`Nat` instance. The `term` can be any type that can appear in `[...]` binders.

Trailing underscores can be omitted, and `#instances Add` and `#instances Add _` are equivalent;
the command adds metavariables until the argument is no longer a function.

The `#instances` command is closely related to `#synth`, but `#synth` does the full
instance synthesis algorithm and `#instances` does the first step of finding potential instances.

# \#instances
Defined in: `Batteries.Tactic.Instances.«command#instances__:_»`

`#instances term` prints all the instances for the given class.
For example, `#instances Add _` gives all `Add` instances, and `#instances Add Nat` gives the
`Nat` instance. The `term` can be any type that can appear in `[...]` binders.

Trailing underscores can be omitted, and `#instances Add` and `#instances Add _` are equivalent;
the command adds metavariables until the argument is no longer a function.

The `#instances` command is closely related to `#synth`, but `#synth` does the full
instance synthesis algorithm and `#instances` does the first step of finding potential instances.

# \#lint
Defined in: `Std.Tactic.Lint.«command#lint+-*Only___»`

The command `#lint` runs the linters on the current file (by default).

`#lint only someLinter` can be used to run only a single linter.

# \#list_linters
Defined in: `Std.Tactic.Lint.«command#list_linters»`

The command `#list_linters` prints a list of all available linters.

# \#long_instances
Defined in: `«command#long_instances_»`

Lists all instances with a long name beginning with `inst`,
gathered according to the module they are defined in.
This is useful for finding automatically named instances with absurd names.

Use as `#long_names` or `#long_names 100` to specify the length.

# \#long_names
Defined in: `«command#long_names_»`

Lists all declarations with a long name, gathered according to the module they are defined in.
Use as `#long_names` or `#long_names 100` to specify the length.

# \#min_imports
Defined in: `«command#min_imports»`

Try to compute a minimal set of imports for this file,
by analyzing the declarations.

This must be run at the end of the file,
and is not aware of syntax and tactics,
so the results will likely need to be adjusted by hand.

# \#min_imports in
Defined in: `Mathlib.Command.MinImports.minImpsStx`

`#min_imports in cmd` scans the syntax `cmd` and the declaration obtained by elaborating `cmd`
to find a collection of minimal imports that should be sufficient for `cmd` to work.

# \#min_imports in
Defined in: `Mathlib.Command.MinImports.«command#min_imports_in_»`

`#min_imports in cmd` scans the syntax `cmd` and the declaration obtained by elaborating `cmd`
to find a collection of minimal imports that should be sufficient for `cmd` to work.

# \#minimize_imports
Defined in: `«command#minimize_imports»`


# \#norm_num
Defined in: `Mathlib.Tactic.normNumCmd`

The basic usage is `#norm_num e`, where `e` is an expression,
which will print the `norm_num` form of `e`.

Syntax: `#norm_num` (`only`)? (`[` simp lemma list `]`)? `:`? expression

This accepts the same options as the `#simp` command.
You can specify additional simp lemmas as usual, for example using `#norm_num [f, g] : e`.
(The colon is optional but helpful for the parser.)
The `only` restricts `norm_num` to using only the provided lemmas, and so
`#norm_num only : e` behaves similarly to `norm_num1`.

Unlike `norm_num`, this command does not fail when no simplifications are made.

`#norm_num` understands local variables, so you can use them to introduce parameters.

# \#print
Defined in: `Batteries.Tactic.printPrefix`

The command `#print prefix foo` will print all definitions that start with
the namespace `foo`.

For example, the command below will print out definitions in the `List` namespace:

```lean
#print prefix List
```

`#print prefix` can be controlled by flags in `PrintPrefixConfig`.  These provide
options for filtering names and formatting.   For example,
`#print prefix` by default excludes internal names, but this can be controlled
via config:
```lean
#print prefix (config := {internals := true}) List
```

By default, `#print prefix` prints the type after each name.  This can be controlled
by setting `showTypes` to `false`:
```lean
#print prefix (config := {showTypes := false}) List
```

The complete set of flags can be seen in the documentation
for `Lean.Elab.Command.PrintPrefixConfig`.

# \#print
Defined in: `Lean.Parser.Command.printAxioms`


# \#print
Defined in: `Lean.Parser.Command.printTacTags`

Displays all available tactic tags, with documentation.

# \#print
Defined in: `Lean.Parser.Command.printEqns`


# \#print
Defined in: `Batteries.Tactic.«command#printDependents___»`

The command `#print dependents X Y` prints a list of all the declarations in the file that
transitively depend on `X` or `Y`. After each declaration, it shows the list of all declarations
referred to directly in the body which also depend on `X` or `Y`.

For example, `#print axioms bar'` below shows that `bar'` depends on `Classical.choice`, but not
why. `#print dependents Classical.choice` says that `bar'` depends on `Classical.choice` because
it uses `foo` and `foo` uses `Classical.em`. `bar` is not listed because it is proved without using
`Classical.choice`.
```
import Batteries.Tactic.PrintDependents

theorem foo : x = y ∨ x ≠ y := Classical.em _
theorem bar : 1 = 1 ∨ 1 ≠ 1 := by simp
theorem bar' : 1 = 1 ∨ 1 ≠ 1 := foo

#print axioms bar'
-- 'bar'' depends on axioms: [Classical.choice, Quot.sound, propext]

#print dependents Classical.choice
-- foo: Classical.em
-- bar': foo
```

# \#print
Defined in: `Lean.Parser.Command.print`


# \#push_neg
Defined in: `Mathlib.Tactic.PushNeg.pushNeg`

The syntax is `#push_neg e`, where `e` is an expression,
which will print the `push_neg` form of `e`.

`#push_neg` understands local variables, so you can use them to introduce parameters.

# \#reduce
Defined in: `Lean.reduceCmd`

`#reduce <expression>` reduces the expression `<expression>` to its normal form. This
involves applying reduction rules until no further reduction is possible.

By default, proofs and types within the expression are not reduced. Use modifiers
`(proofs := true)`  and `(types := true)` to reduce them.
Recall that propositions are types in Lean.

**Warning:** This can be a computationally expensive operation,
especially for complex expressions.

Consider using `#eval <expression>` for simple evaluation/execution
of expressions.

# \#redundant_imports
Defined in: `«command#redundant_imports»`

List the imports in this file which can be removed
because they are transitively implied by another import.

# \#reset_min_imports
Defined in: `Mathlib.Linter.«command#reset_min_imports»`

`#reset_min_imports` sets to empty the current list of cumulative imports.

# \#sample
Defined in: `SlimCheck.«command#sample_»`

`#sample type`, where `type` has an instance of `SampleableExt`, prints ten random
values of type `type` using an increasing size parameter.

```lean
#sample Nat
-- prints
-- 0
-- 0
-- 2
-- 24
-- 64
-- 76
-- 5
-- 132
-- 8
-- 449
-- or some other sequence of numbers

#sample List Int
-- prints
-- []
-- [1, 1]
-- [-7, 9, -6]
-- [36]
-- [-500, 105, 260]
-- [-290]
-- [17, 156]
-- [-2364, -7599, 661, -2411, -3576, 5517, -3823, -968]
-- [-643]
-- [11892, 16329, -15095, -15461]
-- or whatever
```

# \#show_unused
Defined in: `Batteries.Tactic.ShowUnused.«command#show_unused___»`

`#show_unused decl1 decl2 ..` will highlight every theorem or definition in the current file
not involved in the definition of declarations `decl1`, `decl2`, etc. The result is shown
both in the message on `#show_unused`, as well as on the declarations themselves.
```lean
def foo := 1
def baz := 2
def bar := foo
#show_unused bar -- highlights `baz`
```

# \#simp
Defined in: `Mathlib.Tactic.Conv.«command#simpOnly_=>__»`

* `#simp => e` runs `simp` on the expression `e` and displays the resulting expression after
  simplification.
* `#simp only [lems] => e` runs `simp only [lems]` on `e`.
* The `=>` is optional, so `#simp e` and `#simp only [lems] e` have the same behavior.
  It is mostly useful for disambiguating the expression `e` from the lemmas.

# \#synth
Defined in: `Lean.Parser.Command.synth`


# \#test
Defined in: `SlimCheck.«command#test_»`


# \#time
Defined in: `timeCmd`


# \#unfold?
Defined in: `Mathlib.Tactic.InteractiveUnfold.unfoldCommand`

`#unfold? e` gives all unfolds of `e`.
In tactic mode, use `unfold?` instead.

# \#where
Defined in: `Batteries.Tactic.Where.«command#where»`

`#where` gives a description of the global scope at this point in the module.
This includes the namespace, `open` namespaces, `universe` and `variable` commands,
and options set with `set_option`.

# \#whnf
Defined in: `Mathlib.Tactic.Conv.«command#whnf_»`

The command `#whnf e` evaluates `e` to Weak Head Normal Form, which means that the "head"
of the expression is reduced to a primitive - a lambda or forall, or an axiom or inductive type.
It is similar to `#reduce e`, but it does not reduce the expression completely,
only until the first constructor is exposed. For example:
```lean
open Nat List
set_option pp.notation false
#whnf [1, 2, 3].map succ
-- cons (succ 1) (map succ (cons 2 (cons 3 nil)))
#reduce [1, 2, 3].map succ
-- cons 2 (cons 3 (cons 4 nil))
```
The head of this expression is the `List.cons` constructor,
so we can see from this much that the list is not empty,
but the subterms `Nat.succ 1` and `List.map Nat.succ (List.cons 2 (List.cons 3 List.nil))` are
still unevaluated. `#reduce` is equivalent to using `#whnf` on every subexpression.

# \#whnfR
Defined in: `Mathlib.Tactic.Conv.«command#whnfR_»`

The command `#whnfR e` evaluates `e` to Weak Head Normal Form with Reducible transparency,
that is, it uses `whnf` but only unfolding reducible definitions.

# \#widget
Defined in: `Lean.Widget.widgetCmd`

Use `#widget <widget>` to display a panel widget,
and `#widget <widget> with <props>` to display it with the given props.
Useful for debugging widgets.

The type of `<widget>` must implement `Widget.ToModule`,
and the type of `<props>` must implement `Server.RpcEncodable`.
In particular, `<props> : Json` works.

# /-!
Defined in: `Lean.Parser.Command.moduleDoc`

`/-! <text> -/` defines a *module docstring* that can be displayed by documentation generation
tools. The string is associated with the corresponding position in the file. It can be used
multiple times in the same file.

# add_aesop_rules
Defined in: `Aesop.Frontend.Parser.command_Add_aesop_rules_`


# add_decl_doc
Defined in: `Lean.Parser.Command.addDocString`

Adds a docstring to an existing declaration, replacing any existing docstring.
The provided docstring should be written as a docstring for the `add_decl_doc` command, as in
```
/-- My new docstring -/
add_decl_doc oldDeclaration
```

This is useful for auto-generated declarations
for which there is no place to write a docstring in the source code.

Parent projections in structures are an example of this:
```lean
structure Triple (α β γ : Type) extends Prod α β where
  thrd : γ

/-- Extracts the first two projections of a triple. -/
add_decl_doc Triple.toProd
```

Documentation can only be added to declarations in the same module.

# alias
Defined in: `Batteries.Tactic.Alias.alias`

The command `alias name := target` creates a synonym of `target` with the given name.

The command `alias ⟨fwd, rev⟩ := target` creates synonyms for the forward and reverse directions
of an iff theorem. Use `_` if only one direction is required.

These commands accept all modifiers and attributes that `def` and `theorem` do.

# alias
Defined in: `Batteries.Tactic.Alias.aliasLR`

The command `alias name := target` creates a synonym of `target` with the given name.

The command `alias ⟨fwd, rev⟩ := target` creates synonyms for the forward and reverse directions
of an iff theorem. Use `_` if only one direction is required.

These commands accept all modifiers and attributes that `def` and `theorem` do.

# assert_exists
Defined in: `commandAssert_exists_`

`assert_exists n` is a user command that asserts that a declaration named `n` exists
in the current import scope.

Be careful to use names (e.g. `Rat`) rather than notations (e.g. `ℚ`).

# assert_no_sorry
Defined in: `commandAssert_no_sorry_`

Throws an error if the given identifier uses sorryAx.

# assert_not_exists
Defined in: `commandAssert_not_exists_`

`assert_not_exists n` is a user command that asserts that a declaration named `n` *does not exist*
in the current import scope.

Be careful to use names (e.g. `Rat`) rather than notations (e.g. `ℚ`).

It may be used (sparingly!) in mathlib to enforce plans that certain files
are independent of each other.

If you encounter an error on an `assert_not_exists` command while developing mathlib,
it is probably because you have introduced new import dependencies to a file.

In this case, you should refactor your work
(for example by creating new files rather than adding imports to existing files).
You should *not* delete the `assert_not_exists` statement without careful discussion ahead of time.

`assert_not_exists` statements should generally live at the top of the file, after the module doc.

# assert_not_imported
Defined in: `commandAssert_not_imported_`

`assert_not_imported m₁ m₂ ... mₙ` checks that each one of the modules `m₁ m₂ ... mₙ` is not
among the transitive imports of the current file.

The command does not currently check whether the modules `m₁ m₂ ... mₙ` actually exist.

# attribute
Defined in: `Lean.Parser.Command.attribute`


# binder_predicate
Defined in: `Lean.Parser.Command.binderPredicate`

Declares a binder predicate.  For example:
```lean
binder_predicate x " > " y:term => `($x > $y)
```

# builtin_dsimproc
Defined in: `Lean.Parser.«command__Builtin_dsimproc__[_]_(_):=_»`

A builtin defeq simplification procedure.

# builtin_dsimproc_decl
Defined in: `Lean.Parser.«command_Builtin_dsimproc_decl_(_):=_»`

A builtin defeq simplification procedure declaration.

# builtin_simproc
Defined in: `Lean.Parser.«command__Builtin_simproc__[_]_(_):=_»`

A builtin simplification procedure.

# builtin_simproc_decl
Defined in: `Lean.Parser.«command_Builtin_simproc_decl_(_):=_»`

A builtin simplification procedure declaration.

# builtin_simproc_pattern%
Defined in: `Lean.Parser.simprocPatternBuiltin`

Auxiliary command for associating a pattern with a builtin simplification procedure.

# class
Defined in: `Lean.Parser.Command.classAbbrev`

Expands
```
class abbrev C <params> := D_1, ..., D_n
```
into
```
class C <params> extends D_1, ..., D_n
attribute [instance] C.mk
```

# compile_def%
Defined in: `Mathlib.Util.«commandCompile_def%_»`

`compile_def% Foo.foo` adds compiled code for the definition `Foo.foo`.
This can be used for type class projections or definitions like `List._sizeOf_1`,
for which Lean does not generate compiled code by default
(since it is not used 99% of the time).

# compile_inductive%
Defined in: `Mathlib.Util.«commandCompile_inductive%_»`

`compile_inductive% Foo` creates compiled code for the recursor `Foo.rec`,
so that `Foo.rec` can be used in a definition
without having to mark the definition as `noncomputable`.

# count_heartbeats
Defined in: `Mathlib.CountHeartbeats.commandCount_heartbeatsIn__`

Count the heartbeats used in the enclosed command.

This is most useful for setting sufficient but reasonable limits via `set_option maxHeartbeats`
for long running declarations.

If you do so, please resist the temptation to set the limit as low as possible.
As the `simp` set and other features of the library evolve,
other contributors will find that their (likely unrelated) changes
have pushed the declaration over the limit.
`count_heartbearts in` will automatically suggest a `set_option maxHeartbeats` via "Try this:"
using the least number of the form `2^k * 200000` that suffices.

Note that that internal heartbeat counter accessible via `IO.getNumHeartbeats`
has granularity 1000 times finer that the limits set by `set_option maxHeartbeats`.
As this is intended as a user command, we divide by 1000.

# count_heartbeats!
Defined in: `Mathlib.CountHeartbeats.commandCount_heartbeats!_In__`

`count_heartbeats! in cmd` runs a command `10` times, reporting the range in heartbeats, and the
standard deviation. The command `count_heartbeats! n in cmd` runs it `n` times instead.

Example usage:
```lean
count_heartbeats! in
def f := 37
```
displays the info message `Min: 7 Max: 8 StdDev: 14%`.

# declare_aesop_rule_sets
Defined in: `Aesop.Frontend.Parser.declareAesopRuleSets`


# declare_bitwise_uint_theorems
Defined in: `commandDeclare_bitwise_uint_theorems_`


# declare_config_elab
Defined in: `Lean.Elab.Tactic.configElab`


# declare_simp_like_tactic
Defined in: `Lean.Parser.Tactic.declareSimpLikeTactic`


# declare_syntax_cat
Defined in: `Lean.Parser.Command.syntaxCat`


# declare_uint_simprocs
Defined in: `commandDeclare_uint_simprocs_`


# declare_uint_theorems
Defined in: `commandDeclare_uint_theorems_`


# deprecate to
Defined in: `Mathlib.Tactic.DeprecateMe.commandDeprecate_to____`

Writing
```lean
deprecate to new_name new_name₂ ... new_nameₙ
theorem old_name : True := .intro
```
where `new_name new_name₂ ... new_nameₙ` is a sequence of identifiers produces the
`Try this` suggestion:
```lean
theorem new_name : True := .intro

@[deprecated (since := "YYYY-MM-DD")] alias old_name := new_name

@[deprecated (since := "YYYY-MM-DD")] alias old_name₂ := new_name₂
...

@[deprecated (since := "YYYY-MM-DD")] alias old_nameₙ := new_nameₙ
```
where `old_name old_name₂ ... old_nameₙ` are the non-blacklisted declarations
(auto)generated by the initial command.

The "YYYY-MM-DD" entry is today's date and it is automatically filled in.

`deprecate to` makes an effort to match `old_name`, the "visible" name, with
`new_name`, the first identifier produced by the user.
The "old", autogenerated declarations `old_name₂ ... old_nameₙ` are retrieved in alphabetical order.
In the case in which the initial declaration produces at most 1 non-blacklisted
declarations besides itself, the alphabetical sorting is irrelevant.

Technically, the command also take an optional `String` argument to fill in the date in `since`.
However, its use is mostly intended for debugging purposes, where having a variable date would
make tests time-dependent.

# deriving
Defined in: `Lean.Parser.Command.deriving`


# dsimproc
Defined in: `Lean.Parser.«command__Dsimproc__[_]_(_):=_»`

Similar to `simproc`, but resulting expression must be definitionally equal to the input one.

# dsimproc_decl
Defined in: `Lean.Parser.«command_Dsimproc_decl_(_):=_»`

A user-defined defeq simplification procedure declaration. To activate this procedure in `simp` tactic,
we must provide it as an argument, or use the command `attribute` to set its `[simproc]` attribute.

# elab
Defined in: `Lean.Parser.Command.elab`


# elab_rules
Defined in: `Lean.Parser.Command.elab_rules`


# elab_stx_quot
Defined in: `Lean.Elab.Term.Quotation.commandElab_stx_quot_`


# end
Defined in: `Lean.Parser.Command.end`

`end` closes a `section` or `namespace` scope. If the scope is named `<id>`, it has to be closed
with `end <id>`. The `end` command is optional at the end of a file.

# erase_aesop_rules
Defined in: `Aesop.Frontend.Parser.«commandErase_aesop_rules[_,,]»`


# export
Defined in: `Lean.Parser.Command.export`

Adds names from other namespaces to the current namespace.

The command `export Some.Namespace (name₁ name₂)` makes `name₁` and `name₂`:

- visible in the current namespace without prefix `Some.Namespace`, like `open`, and
- visible from outside the current namespace `N` as `N.name₁` and `N.name₂`.

## Examples

```lean
namespace Morning.Sky
  def star := "venus"
end Morning.Sky

namespace Evening.Sky
  export Morning.Sky (star)
  -- `star` is now in scope
  #check star
end Evening.Sky

-- `star` is visible in `Evening.Sky`
#check Evening.Sky.star
```

# export private
Defined in: `Lean.Elab.Command.exportPrivate`

The command `export private a b c in foo bar` is similar to `open private`, but instead of opening
them in the current scope it will create public aliases to the private definition. The definition
will exist at exactly the original location and name, as if the `private` keyword was not used
originally.

It will also open the newly created alias definition under the provided short name, like
`open private`.
It is also possible to specify the module instead with
`export private a b c from Other.Module`.

# extend_docs
Defined in: `Mathlib.Tactic.ExtendDocs.commandExtend_docs__Before__After_`

`extend_docs <declName> before <prefix_string> after <suffix_string>` extends the
docs of `<declName>` by adding `<prefix_string>` before and `<suffix_string>` after.

# gen_injective_theorems%
Defined in: `Lean.Parser.Command.genInjectiveTheorems`

This is an auxiliary command for generation constructor injectivity theorems for
inductive types defined at `Prelude.lean`.
It is meant for bootstrapping purposes only.

# import
Defined in: `Lean.Parser.Command.import`


# in
Defined in: `Lean.Parser.Command.in`


# include
Defined in: `Lean.Parser.Command.include`

`include eeny meeny` instructs Lean to include the section `variable`s `eeny` and `meeny` in all
declarations in the remainder of the current section, differing from the default behavior of
conditionally including variables based on use in the declaration header. `include` is usually
followed by the `in` combinator to limit the inclusion to the subsequent declaration.

# init_quot
Defined in: `Lean.Parser.Command.init_quot`


# initialize_simps_projections
Defined in: `Lean.Parser.Command.initialize_simps_projections`

This command specifies custom names and custom projections for the simp attribute `simpsAttr`.
* You can specify custom names by writing e.g.
  `initialize_simps_projections Equiv (toFun → apply, invFun → symm_apply)`.
* See Note [custom simps projection] and the examples below for information how to declare custom
  projections.
* For algebraic structures, we will automatically use the notation (like `Mul`)
  for the projections if such an instance is available.
* By default, the projections to parent structures are not default projections,
  but all the data-carrying fields are (including those in parent structures).
* You can disable a projection by default by running
  `initialize_simps_projections Equiv (-invFun)`
  This will ensure that no simp lemmas are generated for this projection,
  unless this projection is explicitly specified by the user.
* Conversely, you can enable a projection by default by running
  `initialize_simps_projections Equiv (+toEquiv)`.
* If you want the projection name added as a prefix in the generated lemma name, you can use
  `as_prefix fieldName`:
  `initialize_simps_projections Equiv (toFun → coe, as_prefix coe)`
  Note that this does not influence the parsing of projection names: if you have a declaration
  `foo` and you want to apply the projections `snd`, `coe` (which is a prefix) and `fst`, in that
  order you can run `@[simps snd_coe_fst] def foo ...` and this will generate a lemma with the
  name `coe_foo_snd_fst`.
  * Run `initialize_simps_projections?` (or `set_option trace.simps.verbose true`)
  to see the generated projections.
* Running `initialize_simps_projections MyStruc` without arguments is not necessary, it has the
  same effect if you just add `@[simps]` to a declaration.
* It is recommended to call `@[simps]` or `initialize_simps_projections` in the same file as the
  structure declaration. Otherwise, the projections could be generated multiple times in different
  files.

Some common uses:
* If you define a new homomorphism-like structure (like `MulHom`) you can just run
  `initialize_simps_projections` after defining the `DFunLike` instance (or instance that implies
  a `DFunLike` instance).
  ```
    instance {mM : Mul M} {mN : Mul N} : DFunLike (MulHom M N) M N := ...
    initialize_simps_projections MulHom (toFun → apply)
  ```
  This will generate `foo_apply` lemmas for each declaration `foo`.
* If you prefer `coe_foo` lemmas that state equalities between functions, use
  `initialize_simps_projections MulHom (toFun → coe, as_prefix coe)`
  In this case you have to use `@[simps (config := .asFn)]` or equivalently
  `@[simps (config := .asFn)]` whenever you call `@[simps]`.
* You can also initialize to use both, in which case you have to choose which one to use by default,
  by using either of the following
  ```
    initialize_simps_projections MulHom (toFun → apply, toFun → coe, as_prefix coe, -coe)
    initialize_simps_projections MulHom (toFun → apply, toFun → coe, as_prefix coe, -apply)
  ```
  In the first case, you can get both lemmas using `@[simps, simps (config := .asFn) coe]` and in
  the second case you can get both lemmas using `@[simps (config := .asFn), simps apply]`.
* If you declare a new homomorphism-like structure (like `RelEmbedding`),
  then `initialize_simps_projections` will automatically find any `DFunLike` coercions
  that will be used as the default projection for the `toFun` field.
  ```
    initialize_simps_projections relEmbedding (toFun → apply)
  ```
* If you have an isomorphism-like structure (like `Equiv`) you often want to define a custom
  projection for the inverse:
  ```
    def Equiv.Simps.symm_apply (e : α ≃ β) : β → α := e.symm
    initialize_simps_projections Equiv (toFun → apply, invFun → symm_apply)
  ```

# initialize_simps_projections?
Defined in: `Lean.Parser.Command.commandInitialize_simps_projections?_`

This command specifies custom names and custom projections for the simp attribute `simpsAttr`.
* You can specify custom names by writing e.g.
  `initialize_simps_projections Equiv (toFun → apply, invFun → symm_apply)`.
* See Note [custom simps projection] and the examples below for information how to declare custom
  projections.
* For algebraic structures, we will automatically use the notation (like `Mul`)
  for the projections if such an instance is available.
* By default, the projections to parent structures are not default projections,
  but all the data-carrying fields are (including those in parent structures).
* You can disable a projection by default by running
  `initialize_simps_projections Equiv (-invFun)`
  This will ensure that no simp lemmas are generated for this projection,
  unless this projection is explicitly specified by the user.
* Conversely, you can enable a projection by default by running
  `initialize_simps_projections Equiv (+toEquiv)`.
* If you want the projection name added as a prefix in the generated lemma name, you can use
  `as_prefix fieldName`:
  `initialize_simps_projections Equiv (toFun → coe, as_prefix coe)`
  Note that this does not influence the parsing of projection names: if you have a declaration
  `foo` and you want to apply the projections `snd`, `coe` (which is a prefix) and `fst`, in that
  order you can run `@[simps snd_coe_fst] def foo ...` and this will generate a lemma with the
  name `coe_foo_snd_fst`.
  * Run `initialize_simps_projections?` (or `set_option trace.simps.verbose true`)
  to see the generated projections.
* Running `initialize_simps_projections MyStruc` without arguments is not necessary, it has the
  same effect if you just add `@[simps]` to a declaration.
* It is recommended to call `@[simps]` or `initialize_simps_projections` in the same file as the
  structure declaration. Otherwise, the projections could be generated multiple times in different
  files.

Some common uses:
* If you define a new homomorphism-like structure (like `MulHom`) you can just run
  `initialize_simps_projections` after defining the `DFunLike` instance (or instance that implies
  a `DFunLike` instance).
  ```
    instance {mM : Mul M} {mN : Mul N} : DFunLike (MulHom M N) M N := ...
    initialize_simps_projections MulHom (toFun → apply)
  ```
  This will generate `foo_apply` lemmas for each declaration `foo`.
* If you prefer `coe_foo` lemmas that state equalities between functions, use
  `initialize_simps_projections MulHom (toFun → coe, as_prefix coe)`
  In this case you have to use `@[simps (config := .asFn)]` or equivalently
  `@[simps (config := .asFn)]` whenever you call `@[simps]`.
* You can also initialize to use both, in which case you have to choose which one to use by default,
  by using either of the following
  ```
    initialize_simps_projections MulHom (toFun → apply, toFun → coe, as_prefix coe, -coe)
    initialize_simps_projections MulHom (toFun → apply, toFun → coe, as_prefix coe, -apply)
  ```
  In the first case, you can get both lemmas using `@[simps, simps (config := .asFn) coe]` and in
  the second case you can get both lemmas using `@[simps (config := .asFn), simps apply]`.
* If you declare a new homomorphism-like structure (like `RelEmbedding`),
  then `initialize_simps_projections` will automatically find any `DFunLike` coercions
  that will be used as the default projection for the `toFun` field.
  ```
    initialize_simps_projections relEmbedding (toFun → apply)
  ```
* If you have an isomorphism-like structure (like `Equiv`) you often want to define a custom
  projection for the inverse:
  ```
    def Equiv.Simps.symm_apply (e : α ≃ β) : β → α := e.symm
    initialize_simps_projections Equiv (toFun → apply, invFun → symm_apply)
  ```

# irreducible_def
Defined in: `Lean.Elab.Command.command_Irreducible_def____`

Introduces an irreducible definition.
`irreducible_def foo := 42` generates
a constant `foo : Nat` as well as
a theorem `foo_def : foo = 42`.

# library_note
Defined in: `Batteries.Util.LibraryNote.commandLibrary_note___`

```
library_note "some tag" /--
... some explanation ...
-/
```
creates a new "library note", which can then be cross-referenced using
```
-- See note [some tag]
```
in doc-comments.

# lrat_proof
Defined in: `Mathlib.Tactic.Sat.commandLrat_proof_Example____`

A macro for producing SAT proofs from CNF / LRAT files.
These files are commonly used in the SAT community for writing proofs.

The input to the `lrat_proof` command is the name of the theorem to define,
and the statement (written in CNF format) and the proof (in LRAT format).
For example:
```lean
lrat_proof foo
  "p cnf 2 4  1 2 0  -1 2 0  1 -2 0  -1 -2 0"
  "5 -2 0 4 3 0  5 d 3 4 0  6 1 0 5 1 0  6 d 1 0  7 0 5 2 6 0"
```
produces a theorem:
```lean
foo : ∀ (a a_1 : Prop), (¬a ∧ ¬a_1 ∨ a ∧ ¬a_1) ∨ ¬a ∧ a_1 ∨ a ∧ a_1
```

* You can see the theorem statement by hovering over the word `foo`.
* You can use the `example` keyword in place of `foo` to avoid generating a theorem.
* You can use the `include_str` macro in place of the two strings
  to load CNF / LRAT files from disk.

# macro
Defined in: `Lean.Parser.Command.macro`


# macro_rules
Defined in: `Lean.Parser.Command.macro_rules`


# mk_iff_of_inductive_prop
Defined in: `Mathlib.Tactic.MkIff.mkIffOfInductiveProp`

`mk_iff_of_inductive_prop i r` makes an `iff` rule for the inductively-defined proposition `i`.
The new rule `r` has the shape `∀ps is, i as ↔ ⋁_j, ∃cs, is = cs`, where `ps` are the type
parameters, `is` are the indices, `j` ranges over all possible constructors, the `cs` are the
parameters for each of the constructors, and the equalities `is = cs` are the instantiations for
each constructor for each of the indices to the inductive type `i`.

In each case, we remove constructor parameters (i.e. `cs`) when the corresponding equality would
be just `c = i` for some index `i`.

For example, `mk_iff_of_inductive_prop` on `List.Chain` produces:

```lean
∀ { α : Type*} (R : α → α → Prop) (a : α) (l : List α),
  Chain R a l ↔ l = [] ∨ ∃(b : α) (l' : List α), R a b ∧ Chain R b l ∧ l = b :: l'
```

See also the `mk_iff` user attribute.

# mutual
Defined in: `Lean.Parser.Command.mutual`


# namespace
Defined in: `Lean.Parser.Command.namespace`

`namespace <id>` opens a section with label `<id>` that influences naming and name resolution inside
the section:
* Declarations names are prefixed: `def seventeen : ℕ := 17` inside a namespace `Nat` is given the
  full name `Nat.seventeen`.
* Names introduced by `export` declarations are also prefixed by the identifier.
* All names starting with `<id>.` become available in the namespace without the prefix. These names
  are preferred over names introduced by outer namespaces or `open`.
* Within a namespace, declarations can be `protected`, which excludes them from the effects of
  opening the namespace.

As with `section`, namespaces can be nested and the scope of a namespace is terminated by a
corresponding `end <id>` or the end of the file.

`namespace` also acts like `section` in delimiting the scope of `variable`, `open`, and other scoped commands.

# noncomputable
Defined in: `Lean.Parser.Command.noncomputableSection`


# norm_cast_add_elim
Defined in: `Lean.Parser.Tactic.normCastAddElim`

`norm_cast_add_elim foo` registers `foo` as an elim-lemma in `norm_cast`.

# notation
Defined in: `Lean.Parser.Command.notation`


# notation3
Defined in: `Mathlib.Notation3.notation3`

`notation3` declares notation using Lean-3-style syntax.

Examples:
```lean
notation3 "∀ᶠ " (...) " in " f ", " r:(scoped p => Filter.eventually p f) => r
notation3 "MyList[" (x", "* => foldr (a b => MyList.cons a b) MyList.nil) "]" => x
```
By default notation is unable to mention any variables defined using `variable`, but
`local notation3` is able to use such local variables.

Use `notation3 (prettyPrint := false)` to keep the command from generating a pretty printer
for the notation.

This command can be used in mathlib4 but it has an uncertain future and was created primarily
for backward compatibility.

# open
Defined in: `Lean.Parser.Command.open`

Makes names from other namespaces visible without writing the namespace prefix.

Names that are made available with `open` are visible within the current `section` or `namespace`
block. This makes referring to (type) definitions and theorems easier, but note that it can also
make [scoped instances], notations, and attributes from a different namespace available.

The `open` command can be used in a few different ways:

* `open Some.Namespace.Path1 Some.Namespace.Path2` makes all non-protected names in
  `Some.Namespace.Path1` and `Some.Namespace.Path2` available without the prefix, so that
  `Some.Namespace.Path1.x` and `Some.Namespace.Path2.y` can be referred to by writing only `x` and
  `y`.

* `open Some.Namespace.Path hiding def1 def2` opens all non-protected names in `Some.Namespace.Path`
  except `def1` and `def2`.

* `open Some.Namespace.Path (def1 def2)` only makes `Some.Namespace.Path.def1` and
  `Some.Namespace.Path.def2` available without the full prefix, so `Some.Namespace.Path.def3` would
  be unaffected.

  This works even if `def1` and `def2` are `protected`.

* `open Some.Namespace.Path renaming def1 → def1', def2 → def2'` same as `open Some.Namespace.Path
  (def1 def2)` but `def1`/`def2`'s names are changed to `def1'`/`def2'`.

  This works even if `def1` and `def2` are `protected`.

* `open scoped Some.Namespace.Path1 Some.Namespace.Path2` **only** opens [scoped instances],
  notations, and attributes from `Namespace1` and `Namespace2`; it does **not** make any other name
  available.

* `open <any of the open shapes above> in` makes the names `open`-ed visible only in the next
  command or expression.

[scoped instance]: https://lean-lang.org/theorem_proving_in_lean4/type_classes.html#scoped-instances
(Scoped instances in Theorem Proving in Lean)


## Examples

```lean
/-- SKI combinators https://en.wikipedia.org/wiki/SKI_combinator_calculus -/
namespace Combinator.Calculus
  def I (a : α) : α := a
  def K (a : α) : β → α := fun _ => a
  def S (x : α → β → γ) (y : α → β) (z : α) : γ := x z (y z)
end Combinator.Calculus

section
  -- open everything under `Combinator.Calculus`, *i.e.* `I`, `K` and `S`,
  -- until the section ends
  open Combinator.Calculus

  theorem SKx_eq_K : S K x = I := rfl
end

-- open everything under `Combinator.Calculus` only for the next command (the next `theorem`, here)
open Combinator.Calculus in
theorem SKx_eq_K' : S K x = I := rfl

section
  -- open only `S` and `K` under `Combinator.Calculus`
  open Combinator.Calculus (S K)

  theorem SKxy_eq_y : S K x y = y := rfl

  -- `I` is not in scope, we have to use its full path
  theorem SKxy_eq_Iy : S K x y = Combinator.Calculus.I y := rfl
end

section
  open Combinator.Calculus
    renaming
      I → identity,
      K → konstant

  #check identity
  #check konstant
end

section
  open Combinator.Calculus
    hiding S

  #check I
  #check K
end

section
  namespace Demo
    inductive MyType
    | val

    namespace N1
      scoped infix:68 " ≋ " => BEq.beq

      scoped instance : BEq MyType where
        beq _ _ := true

      def Alias := MyType
    end N1
  end Demo

  -- bring `≋` and the instance in scope, but not `Alias`
  open scoped Demo.N1

  #check Demo.MyType.val == Demo.MyType.val
  #check Demo.MyType.val ≋ Demo.MyType.val
  -- #check Alias -- unknown identifier 'Alias'
end
```

# open private
Defined in: `Lean.Elab.Command.openPrivate`

The command `open private a b c in foo bar` will look for private definitions named `a`, `b`, `c`
in declarations `foo` and `bar` and open them in the current scope. This does not make the
definitions public, but rather makes them accessible in the current section by the short name `a`
instead of the (unnameable) internal name for the private declaration, something like
`_private.Other.Module.0.Other.Namespace.foo.a`, which cannot be typed directly because of the `0`
name component.

It is also possible to specify the module instead with
`open private a b c from Other.Module`.

# proof_wanted
Defined in: `proof_wanted`

This proof would be a welcome contribution to the library!

The syntax of `proof_wanted` declarations is just like that of `theorem`, but without `:=` or the
proof. Lean checks that `proof_wanted` declarations are well-formed (e.g. it ensures that all the
mentioned names are in scope, and that the theorem statement is a valid proposition), but they are
discarded afterwards. This means that they cannot be used as axioms.

Typical usage:
```lean
@[simp] proof_wanted empty_find? [BEq α] [Hashable α] {a : α} :
    (∅ : HashMap α β).find? a = none
```

# recall
Defined in: `Mathlib.Tactic.Recall.recall`

The `recall` command redeclares a previous definition for illustrative purposes.
This can be useful for files that give an expository account of some theory in Lean.

The syntax of the command mirrors `def`, so all the usual bells and whistles work.
```lean
recall List.cons_append (a : α) (as bs : List α) : (a :: as) ++ bs = a :: (as ++ bs) := rfl
```
Also, one can leave out the body.
```lean
recall Nat.add_comm (n m : Nat) : n + m = m + n
```

The command verifies that the new definition type-checks and that the type and value
provided are definitionally equal to the original declaration. However, this does not
capture some details (like binders), so the following works without error.
```lean
recall Nat.add_comm {n m : Nat} : n + m = m + n
```

# register_builtin_option
Defined in: `Lean.Option.registerBuiltinOption`


# register_hint
Defined in: `Mathlib.Tactic.Hint.registerHintStx`

Register a tactic for use with the `hint` tactic, e.g. `register_hint simp_all`.

# register_label_attr
Defined in: `Lean.Parser.Command.registerLabelAttr`

Initialize a new "label" attribute.
Declarations tagged with the attribute can be retrieved using `Std.Tactic.LabelAttr.labelled`.

# register_option
Defined in: `Lean.Option.registerOption`


# register_simp_attr
Defined in: `Lean.Parser.Command.registerSimpAttr`


# register_tactic_tag
Defined in: `Lean.Parser.Command.register_tactic_tag`

Register a tactic tag, saving its user-facing name and docstring.

Tactic tags can be used by documentation generation tools to classify related tactics.

# run_cmd
Defined in: `Lean.runCmd`

The `run_cmd doSeq` command executes code in `CommandElabM Unit`.
This is almost the same as `#eval show CommandElabM Unit from do doSeq`,
except that it doesn't print an empty diagnostic.

# run_elab
Defined in: `Lean.runElab`

The `run_elab doSeq` command executes code in `TermElabM Unit`.
This is almost the same as `#eval show TermElabM Unit from do doSeq`,
except that it doesn't print an empty diagnostic.

# run_meta
Defined in: `Lean.runMeta`

The `run_meta doSeq` command executes code in `MetaM Unit`.
This is almost the same as `#eval show MetaM Unit from do doSeq`,
except that it doesn't print an empty diagnostic.

(This is effectively a synonym for `run_elab`.)

# scoped
Defined in: `Mathlib.Tactic.scopedNS`

`scoped[NS]` is similar to the `scoped` modifier on attributes and notations,
but it scopes the syntax in the specified namespace instead of the current namespace.
```lean
scoped[Matrix] infixl:72 " ⬝ᵥ " => Matrix.dotProduct
-- declares `*` as a notation for vector dot productss
-- which is only accessible if you `open Matrix` or `open scoped Matrix`.

namespace Nat

scoped[Nat.Count] attribute [instance] CountSet.fintype
-- make the definition Nat.CountSet.fintype an instance,
-- but only if `Nat.Count` is open
```

# seal
Defined in: `Lean.Parser.commandSeal__`

The `seal foo` command ensures that the definition of `foo` is sealed, meaning it is marked as `[irreducible]`.
This command is particularly useful in contexts where you want to prevent the reduction of `foo` in proofs.

In terms of functionality, `seal foo` is equivalent to `attribute [local irreducible] foo`.
This attribute specifies that `foo` should be treated as irreducible only within the local scope,
which helps in maintaining the desired abstraction level without affecting global settings.

# section
Defined in: `Lean.Parser.Command.section`

A `section`/`end` pair delimits the scope of `variable`, `include, `open`, `set_option`, and `local`
commands. Sections can be nested. `section <id>` provides a label to the section that has to appear
with the matching `end`. In either case, the `end` can be omitted, in which case the section is
closed at the end of the file.

# set_option
Defined in: `Lean.Parser.Command.set_option`

`set_option <id> <value>` sets the option `<id>` to `<value>`. Depending on the type of the option,
the value can be `true`, `false`, a string, or a numeral. Options are used to configure behavior of
Lean as well as user-defined extensions. The setting is active until the end of the current `section`
or `namespace` or the end of the file.
Auto-completion is available for `<id>` to list available options.

`set_option <id> <value> in <command>` sets the option for just a single command:
```lean
set_option pp.all true in
#check 1 + 1
```
Similarly, `set_option <id> <value> in` can also be used inside terms and tactics to set an option
only in a single term or tactic.

# show_panel_widgets
Defined in: `Lean.Widget.showPanelWidgetsCmd`

Use `show_panel_widgets [<widget>]` to mark that `<widget>`
should always be displayed, including in downstream modules.

The type of `<widget>` must implement `Widget.ToModule`,
and the type of `<props>` must implement `Server.RpcEncodable`.
In particular, `<props> : Json` works.

Use `show_panel_widgets [<widget> with <props>]`
to specify the `<props>` that the widget should be given
as arguments.

Use `show_panel_widgets [local <widget> (with <props>)?]` to mark it
for display in the current section, namespace, or file only.

Use `show_panel_widgets [scoped <widget> (with <props>)?]` to mark it
for display only when the current namespace is open.

Use `show_panel_widgets [-<widget>]` to temporarily hide a previously shown widget
in the current section, namespace, or file.
Note that persistent erasure is not possible, i.e.,
`-<widget>` has no effect on downstream modules.

# simproc
Defined in: `Lean.Parser.«command__Simproc__[_]_(_):=_»`

A user-defined simplification procedure used by the `simp` tactic, and its variants.
Here is an example.
```lean
theorem and_false_eq {p : Prop} (q : Prop) (h : p = False) : (p ∧ q) = False := by simp [*]

open Lean Meta Simp
simproc ↓ shortCircuitAnd (And _ _) := fun e => do
  let_expr And p q := e | return .continue
  let r ← simp p
  let_expr False := r.expr | return .continue
  let proof ← mkAppM ``and_false_eq #[q, (← r.getProof)]
  return .done { expr := r.expr, proof? := some proof }
```
The `simp` tactic invokes `shortCircuitAnd` whenever it finds a term of the form `And _ _`.
The simplification procedures are stored in an (imperfect) discrimination tree.
The procedure should **not** assume the term `e` perfectly matches the given pattern.
The body of a simplification procedure must have type `Simproc`, which is an alias for
`Expr → SimpM Step`
You can instruct the simplifier to apply the procedure before its sub-expressions
have been simplified by using the modifier `↓` before the procedure name.
Simplification procedures can be also scoped or local.

# simproc_decl
Defined in: `Lean.Parser.«command_Simproc_decl_(_):=_»`

A user-defined simplification procedure declaration. To activate this procedure in `simp` tactic,
we must provide it as an argument, or use the command `attribute` to set its `[simproc]` attribute.

# simproc_pattern%
Defined in: `Lean.Parser.simprocPattern`

Auxiliary command for associating a pattern with a simplification procedure.

# sudo
Defined in: `commandSudoSet_option___`

The command `sudo set_option name val` is similar to `set_option name val`,
but it also allows to set undeclared options.

# suppress_compilation
Defined in: `commandSuppress_compilation`

Replacing `def` and `instance` by `noncomputable def` and `noncomputable instance`, designed
to disable the compiler in a given file or a given section.
This is a hack to work around mathlib4#7103.
Note that it does not work with `notation3`. You need to prefix such a notation declaration with
`unsuppress_compilation` if `suppress_compilation` is active.

# syntax
Defined in: `Lean.Parser.Command.syntax`


# syntax
Defined in: `Lean.Parser.Command.syntaxAbbrev`


# tactic_extension
Defined in: `Lean.Parser.Command.tactic_extension`

Add more documentation as an extension of the documentation for a given tactic.

The extended documentation is placed in the command's docstring. It is shown as part of a bulleted
list, so it should be brief.

# test_extern
Defined in: `testExternCmd`


# unif_hint
Defined in: `Lean.«command__Unif_hint____Where_|_-⊢_»`


# universe
Defined in: `Lean.Parser.Command.universe`

Declares one or more universe variables.

`universe u v`

`Prop`, `Type`, `Type u` and `Sort u` are types that classify other types, also known as
*universes*. In `Type u` and `Sort u`, the variable `u` stands for the universe's *level*, and a
universe at level `u` can only classify universes that are at levels lower than `u`. For more
details on type universes, please refer to [the relevant chapter of Theorem Proving in Lean][tpil
universes].

Just as type arguments allow polymorphic definitions to be used at many different types, universe
parameters, represented by universe variables, allow a definition to be used at any required level.
While Lean mostly handles universe levels automatically, declaring them explicitly can provide more
control when writing signatures. The `universe` keyword allows the declared universe variables to be
used in a collection of definitions, and Lean will ensure that these definitions use them
consistently.

[tpil universes]: https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html#types-as-objects
(Type universes on Theorem Proving in Lean)

```lean
/- Explicit type-universe parameter. -/
def id₁.{u} (α : Type u) (a : α) := a

/- Implicit type-universe parameter, equivalent to `id₁`.
  Requires option `autoImplicit true`, which is the default. -/
def id₂ (α : Type u) (a : α) := a

/- Explicit standalone universe variable declaration, equivalent to `id₁` and `id₂`. -/
universe u
def id₃ (α : Type u) (a : α) := a
```

On a more technical note, using a universe variable only in the right-hand side of a definition
causes an error if the universe has not been declared previously.

```lean
def L₁.{u} := List (Type u)

-- def L₂ := List (Type u) -- error: `unknown universe level 'u'`

universe u
def L₃ := List (Type u)
```

## Examples

```lean
universe u v w

structure Pair (α : Type u) (β : Type v) : Type (max u v) where
  a : α
  b : β

#check Pair.{v, w}
-- Pair : Type v → Type w → Type (max v w)
```

# unseal
Defined in: `Lean.Parser.commandUnseal__`

The `unseal foo` command ensures that the definition of `foo` is unsealed, meaning it is marked as `[semireducible]`, the
default reducibility setting. This command is useful when you need to allow some level of reduction of `foo` in proofs.

Functionally, `unseal foo` is equivalent to `attribute [local semireducible] foo`.
Applying this attribute makes `foo` semireducible only within the local scope.

# unset_option
Defined in: `Lean.Elab.Command.unsetOption`

Unset a user option

# unsuppress_compilation
Defined in: `commandUnsuppress_compilationIn_`

The command `unsuppress_compilation in def foo : ...` makes sure that the definition is
compiled to executable code, even if `suppress_compilation` is active.

# variable
Defined in: `Lean.Parser.Command.variable`

Declares one or more typed variables, or modifies whether already-declared variables are
  implicit.

Introduces variables that can be used in definitions within the same `namespace` or `section` block.
When a definition mentions a variable, Lean will add it as an argument of the definition. This is
useful in particular when writing many definitions that have parameters in common (see below for an
example).

Variable declarations have the same flexibility as regular function paramaters. In particular they
can be [explicit, implicit][binder docs], or [instance implicit][tpil classes] (in which case they
can be anonymous). This can be changed, for instance one can turn explicit variable `x` into an
implicit one with `variable {x}`. Note that currently, you should avoid changing how variables are
bound and declare new variables at the same time; see [issue 2789] for more on this topic.

In *theorem bodies* (i.e. proofs), variables are not included based on usage in order to ensure that
changes to the proof cannot change the statement of the overall theorem. Instead, variables are only
available to the proof if they have been mentioned in the theorem header or in an `include` command
or are instance implicit and depend only on such variables.

See [*Variables and Sections* from Theorem Proving in Lean][tpil vars] for a more detailed
discussion.

[tpil vars]:
https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html#variables-and-sections
(Variables and Sections on Theorem Proving in Lean) [tpil classes]:
https://lean-lang.org/theorem_proving_in_lean4/type_classes.html (Type classes on Theorem Proving in
Lean) [binder docs]:
https://leanprover-community.github.io/mathlib4_docs/Lean/Expr.html#Lean.BinderInfo (Documentation
for the BinderInfo type) [issue 2789]: https://github.com/leanprover/lean4/issues/2789 (Issue 2789
on github)

## Examples

```lean
section
  variable
    {α : Type u}      -- implicit
    (a : α)           -- explicit
    [instBEq : BEq α] -- instance implicit, named
    [Hashable α]      -- instance implicit, anonymous

  def isEqual (b : α) : Bool :=
    a == b

  #check isEqual
  -- isEqual.{u} {α : Type u} (a : α) [instBEq : BEq α] (b : α) : Bool

  variable
    {a} -- `a` is implicit now

  def eqComm {b : α} := a == b ↔ b == a

  #check eqComm
  -- eqComm.{u} {α : Type u} {a : α} [instBEq : BEq α] {b : α} : Prop
end
```

The following shows a typical use of `variable` to factor out definition arguments:

```lean
variable (Src : Type)

structure Logger where
  trace : List (Src × String)
#check Logger
-- Logger (Src : Type) : Type

namespace Logger
  -- switch `Src : Type` to be implicit until the `end Logger`
  variable {Src}

  def empty : Logger Src where
    trace := []
  #check empty
  -- Logger.empty {Src : Type} : Logger Src

  variable (log : Logger Src)

  def len :=
    log.trace.length
  #check len
  -- Logger.len {Src : Type} (log : Logger Src) : Nat

  variable (src : Src) [BEq Src]

  -- at this point all of `log`, `src`, `Src` and the `BEq` instance can all become arguments

  def filterSrc :=
    log.trace.filterMap
      fun (src', str') => if src' == src then some str' else none
  #check filterSrc
  -- Logger.filterSrc {Src : Type} (log : Logger Src) (src : Src) [inst✝ : BEq Src] : List String

  def lenSrc :=
    log.filterSrc src |>.length
  #check lenSrc
  -- Logger.lenSrc {Src : Type} (log : Logger Src) (src : Src) [inst✝ : BEq Src] : Nat
end Logger
```

The following example demonstrates availability of variables in proofs:
```lean
variable
  {α : Type}    -- available in the proof as indirectly mentioned through `a`
  [ToString α]  -- available in the proof as `α` is included
  (a : α)       -- available in the proof as mentioned in the header
  {β : Type}    -- not available in the proof
  [ToString β]  -- not available in the proof

theorem ex : a = a := rfl
```
After elaboration of the proof, the following warning will be generated to highlight the unused
hypothesis:
```lean
included section variable '[ToString α]' is not used in 'ex', consider excluding it
```
In such cases, the offending variable declaration should be moved down or into a section so that
only theorems that do depend on it follow it until the end of the section.

# variable?
Defined in: `Mathlib.Command.Variable.variable?`

The `variable?` command has the same syntax as `variable`, but it will auto-insert
missing instance arguments wherever they are needed.
It does not add variables that can already be deduced from others in the current context.
By default the command checks that variables aren't implied by earlier ones, but it does *not*
check that earlier variables aren't implied by later ones.
Unlike `variable`, the `variable?` command does not support changing variable binder types.

The `variable?` command will give a suggestion to replace itself with a command of the form
`variable? ...binders... => ...binders...`.  The binders after the `=>` are the completed
list of binders. When this `=>` clause is present, the command verifies that the expanded
binders match the post-`=>` binders.  The purpose of this is to help keep code that uses
`variable?` resilient against changes to the typeclass hierarchy, at least in the sense
that this additional information can be used to debug issues that might arise.
One can also replace `variable? ...binders... =>` with `variable`.

The core algorithm is to try elaborating binders one at a time, and whenever there is a
typeclass instance inference failure, it synthesizes binder syntax for it and adds it to
the list of binders and tries again, recursively. There are no guarantees that this
process gives the "correct" list of binders.

Structures tagged with the `variable_alias` attribute can serve as aliases for a collection
of typeclasses. For example, given
```lean
@[variable_alias]
structure VectorSpace (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
```
then `variable? [VectorSpace k V]` is
equivalent to `variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]`, assuming
that there are no pre-existing instances on `k` and `V`.
Note that this is not a simple replacement: it only adds instances not inferrable
from others in the current scope.

A word of warning: the core algorithm depends on pretty printing, so if terms that appear
in binders do not round trip, this algorithm can fail. That said, it has some support
for quantified binders such as `[∀ i, F i]`.

# variables
Defined in: `Mathlib.Tactic.variables`

Syntax for the `variables` command: this command is just a stub,
and merely warns that it has been renamed to `variable` in Lean 4.

# whatsnew
Defined in: `Mathlib.WhatsNew.commandWhatsnewIn__`

`whatsnew in $command` executes the command and then prints the
declarations that were added to the environment.

# with_weak_namespace
Defined in: `Lean.Elab.Command.commandWith_weak_namespace__`

Changes the current namespace without causing scoped things to go out of scope

syntax ... [Batteries.Tactic.Lemma.lemmaCmd]
`lemma` is not supported, please use `theorem` instead

syntax ... [Lean.Parser.Command.declaration]

syntax ... [Lean.Parser.Command.initialize]

syntax ... [Lean.Parser.Command.mixfix]

syntax ... [lemma]
`lemma` means the same as `theorem`. It is used to denote "less important" theorems

