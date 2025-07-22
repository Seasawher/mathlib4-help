# Attributes

Mathlib version: `f1a92a38b2f279f32599ad03e2f51e62a5eef56b`

## Std.Internal.tree_tac
 simp theorems used by internal DTreeMap lemmas

## aesop
 Register a declaration as an Aesop rule.

## aesop_Bound
 simp theorems in the Aesop rule set 'Bound'

## aesop_Bound_proc
 simprocs in the Aesop rule set 'Bound'

## aesop_CStarAlgebra
 simp theorems in the Aesop rule set 'CStarAlgebra'

## aesop_CStarAlgebra_proc
 simprocs in the Aesop rule set 'CStarAlgebra'

## aesop_CategoryTheory
 simp theorems in the Aesop rule set 'CategoryTheory'

## aesop_CategoryTheory_proc
 simprocs in the Aesop rule set 'CategoryTheory'

## aesop_Continuous
 simp theorems in the Aesop rule set 'Continuous'

## aesop_Continuous_proc
 simprocs in the Aesop rule set 'Continuous'

## aesop_IsMultiplicative
 simp theorems in the Aesop rule set 'IsMultiplicative'

## aesop_IsMultiplicative_proc
 simprocs in the Aesop rule set 'IsMultiplicative'

## aesop_Matroid
 simp theorems in the Aesop rule set 'Matroid'

## aesop_Matroid_proc
 simprocs in the Aesop rule set 'Matroid'

## aesop_Measurable
 simp theorems in the Aesop rule set 'Measurable'

## aesop_Measurable_proc
 simprocs in the Aesop rule set 'Measurable'

## aesop_Restrict
 simp theorems in the Aesop rule set 'Restrict'

## aesop_Restrict_proc
 simprocs in the Aesop rule set 'Restrict'

## aesop_SetLike
 simp theorems in the Aesop rule set 'SetLike'

## aesop_SetLike!
 simp theorems in the Aesop rule set 'SetLike!'

## aesop_SetLike!_proc
 simprocs in the Aesop rule set 'SetLike!'

## aesop_SetLike_proc
 simprocs in the Aesop rule set 'SetLike'

## aesop_SimpleGraph
 simp theorems in the Aesop rule set 'SimpleGraph'

## aesop_SimpleGraph_proc
 simprocs in the Aesop rule set 'SimpleGraph'

## aesop_Sym2
 simp theorems in the Aesop rule set 'Sym2'

## aesop_Sym2_proc
 simprocs in the Aesop rule set 'Sym2'

## aesop_builtin
 simp theorems in the Aesop rule set 'builtin'

## aesop_builtin_proc
 simprocs in the Aesop rule set 'builtin'

## aesop_default
 simp theorems in the Aesop rule set 'default'

## aesop_default_proc
 simprocs in the Aesop rule set 'default'

## aesop_finiteness
 simp theorems in the Aesop rule set 'finiteness'

## aesop_finiteness_proc
 simprocs in the Aesop rule set 'finiteness'

## aesop_finsetNonempty
 simp theorems in the Aesop rule set 'finsetNonempty'

## aesop_finsetNonempty_proc
 simprocs in the Aesop rule set 'finsetNonempty'

## algebraize
 Tag that lets the `algebraize` tactic know which `Algebra` property corresponds to this `RingHom`
property.
A user attribute that is used to tag `RingHom` properties that can be converted to `Algebra`
properties. Using an (optional) parameter, it will also generate a `Name` of a declaration which
will help the `algebraize` tactic access the corresponding `Algebra` property.

There are two cases for what declaration corresponding to this `Name` can be.

1. An inductive type (i.e. the `Algebra` property itself), in this case it is assumed that the
`RingHom` and the `Algebra` property are definitionally the same, and the tactic will construct the
`Algebra` property by giving the `RingHom` property as a term.
2. A lemma (or constructor) proving the `Algebra` property from the `RingHom` property. In this case
it is assumed that the `RingHom` property is the final argument, and that no other explicit argument
is needed. The tactic then constructs the `Algebra` property by applying the lemma or constructor.

Finally, if no argument is provided to the `algebraize` attribute, it is assumed that the tagged
declaration has name `RingHom.Property` and that the corresponding `Algebra` property has name
`Algebra.Property`. The attribute then returns `Algebra.Property` (so assume case 1 above).

## always_inline
 mark definition to be always inlined
Changes the inlining behavior. This attribute comes in several variants:
- `@[inline]`: marks the definition to be inlined when it is appropriate.
- `@[inline_if_reduce]`: marks the definition to be inlined if an application of it after inlining
  and applying reduction isn't a `match` expression. This attribute can be used for inlining
  structurally recursive functions.
- `@[noinline]`: marks the definition to never be inlined.
- `@[always_inline]`: marks the definition to always be inlined.
- `@[macro_inline]`: marks the definition to always be inlined at the beginning of compilation.
  This makes it possible to define functions that evaluate some of their parameters lazily.
  Example:
  ```
  @[macro_inline]
  def test (x y : Nat) : Nat :=
    if x = 42 then x else y

  #eval test 42 (2^1000000000000) -- doesn't compute 2^1000000000000
  ```
  Only non-recursive functions may be marked `@[macro_inline]`.

## app_unexpander
 Register an unexpander for applications of a given constant.
Registers an unexpander for applications of a given constant.

`@[app_unexpander c]` registers a `Lean.PrettyPrinter.Unexpander` for applications of the constant
`c`. The unexpander is passed the result of pre-pretty printing the application *without*
implicitly passed arguments. If `pp.explicit` is set to true or `pp.notation` is set to false,
it will not be called at all.

Unexpanders work as an alternative for delaborators (`@[app_delab]`) that can be used without
special imports. This however also makes them much less capable since they can only transform
syntax and don't have access to the expression tree.

## attr_parser
 parser

## bitvec_to_nat
 simp lemmas converting `BitVec` goals to `Nat` goals

## boolToPropSimps
 simp lemmas converting boolean expressions in terms of `decide` into propositional statements

## bool_to_prop
 simp lemmas converting boolean expressions in terms of `decide` into propositional statements

## bound
 Register a theorem as an apply rule for the `bound` tactic.
Register a lemma as an `apply` rule for the `bound` tactic.

A lemma is appropriate for `bound` if it proves an inequality using structurally simpler
inequalities, "recursing" on the structure of the expressions involved, assuming positivity or
nonnegativity where useful. Examples include
1. `gcongr`-like inequalities over `<` and `≤` such as `f x ≤ f y` where `f` is monotone (note that
   `gcongr` supports other relations).
2. `mul_le_mul` which proves `a * b ≤ c * d` from `a ≤ c ∧ b ≤ d ∧ 0 ≤ b ∧ 0 ≤ c`
3. Positivity or nonnegativity inequalities such as `sub_nonneg`: `a ≤ b → 0 ≤ b - a`
4. Inequalities involving `1` such as `one_le_div` or `Real.one_le_exp`
5. Disjunctions where the natural recursion branches, such as `a ^ n ≤ a ^ m` when the inequality
   for `n,m` depends on whether `1 ≤ a ∨ a ≤ 1`.

Each `@[bound]` lemma is assigned a score based on the number and complexity of its hypotheses,
and the `aesop` implementation chooses lemmas with lower scores first:
1. Inequality hypotheses involving `0` add 1 to the score.
2. General inequalities add `10`.
3. Disjuctions `a ∨ b` add `100` plus the sum of the scores of `a` and `b`.

The functionality of `bound` overlaps with `positivity` and `gcongr`, but can jump back and forth
between `0 ≤ x` and `x ≤ y`-type inequalities.  For example, `bound` proves
  `0 ≤ c → b ≤ a → 0 ≤ a * c - b * c`
by turning the goal into `b * c ≤ a * c`, then using `mul_le_mul_of_nonneg_right`.  `bound` also
uses specialized lemmas for goals of the form `1 ≤ x, 1 < x, x ≤ 1, x < 1`.

See also `@[bound_forward]` which marks a lemma as a forward rule for `bound`: these lemmas are
applied to hypotheses to extract inequalities (e.g. `HasPowerSeriesOnBall.r_pos`).

## builtin_attr_parser
 Builtin parser

## builtin_category_parenthesizer
 (builtin) Register a parenthesizer for a syntax category.
Registers a parenthesizer for a syntax category.

`@[category_parenthesizer cat]` registers a declaration of type
`Lean.PrettyPrinter.CategoryParenthesizer` for the syntax category `cat`, which is used when
parenthesizing occurrences of `cat:prec` (`categoryParser cat prec`). Implementations should call
`maybeParenthesize` with the precedence and `cat`. If no category parenthesizer is registered, the
category will never be parenthesized, but still traversed for parenthesizing nested categories.

## builtin_code_action_provider
 (builtin) Use to decorate methods for suggesting code actions. This is a low-level interface for making code actions.

## builtin_command_code_action
 Declare a new builtin command code action, to appear in the code actions on commands

## builtin_command_elab
 (builtin) command elaborator
Registers a command elaborator for the given syntax node kind.

A command elaborator should have type `Lean.Elab.Command.CommandElab` (which is
`Lean.Syntax → Lean.Elab.Term.CommandElabM Unit`), i.e. should take syntax of the given syntax
node kind as a parameter and perform an action.

The `elab_rules` and `elab` commands should usually be preferred over using this attribute
directly.

## builtin_command_parser
 Builtin parser

## builtin_delab
 (builtin) Register a delaborator
Registers a delaborator.

`@[delab k]` registers a declaration of type `Lean.PrettyPrinter.Delaborator.Delab` for the
`Lean.Expr` constructor `k`. Multiple delaborators for a single constructor are tried in turn until
the first success. If the term to be delaborated is an application of a constant `c`, elaborators
for `app.c` are tried first; this is also done for `Expr.const`s ("nullary applications") to reduce
special casing. If the term is an `Expr.mdata` with a single key `k`, `mdata.k` is tried first.

## builtin_doElem_parser
 Builtin parser

## builtin_doc
 make the docs and location of this declaration available as a builtin
Makes the documentation and location of a declaration available as a builtin.

This allows the documentation of core Lean features to be visible without importing the file they
are defined in. This is only useful during bootstrapping and should not be used outside of
the Lean source code.

## builtin_formatter
 (builtin) Register a formatter for a parser.
Registers a formatter for a parser.

`@[formatter k]` registers a declaration of type `Lean.PrettyPrinter.Formatter` to be used for
formatting syntax of kind `k`.

## builtin_incremental
 (builtin) Marks an elaborator (tactic or command, currently) as supporting incremental elaboration. For unmarked elaborators, the corresponding snapshot bundle field in the elaboration context is unset so as to prevent accidental, incorrect reuse.
Marks an elaborator (tactic or command, currently) as supporting incremental elaboration.

For unmarked elaborators, the corresponding snapshot bundle field in the elaboration context is
unset so as to prevent accidental, incorrect reuse.

## builtin_inductive_elab
 (builtin) Register an elaborator for inductive types
Registers an inductive type elaborator for the given syntax node kind.

Commands registered using this attribute are allowed to be used together in mutual blocks with
other inductive type commands. This attribute is mostly used internally for `inductive` and
`structure`.

An inductive type elaborator should have type `Lean.Elab.Command.InductiveElabDescr`.

## builtin_init
 initialization procedure for global references
Registers a builtin initialization procedure.

This attribute is used internally to define builtin initialization procedures for bootstrapping and
should not be used otherwise.

## builtin_level_parser
 Builtin parser

## builtin_macro
 (builtin) macro elaborator
Registers a macro expander for a given syntax node kind.

A macro expander should have type `Lean.Macro` (which is `Lean.Syntax → Lean.MacroM Lean.Syntax`),
i.e. should take syntax of the given syntax node kind as a parameter and produce different syntax
in the same syntax category.

The `macro_rules` and `macro` commands should usually be preferred over using this attribute
directly.

## builtin_missing_docs_handler
 (builtin) adds a syntax traversal for the missing docs linter

## builtin_parenthesizer
 (builtin) Register a parenthesizer for a parser.
Registers a parenthesizer for a parser.

`@[parenthesizer k]` registers a declaration of type `Lean.PrettyPrinter.Parenthesizer` to be used
for parenthesizing syntax of kind `k`.

## builtin_prec_parser
 Builtin parser

## builtin_prio_parser
 Builtin parser

## builtin_quot_precheck
 (builtin) Register a double backtick syntax quotation pre-check.
Registers a double backtick syntax quotation pre-check.

`@[quot_precheck k]` registers a declaration of type `Lean.Elab.Term.Quotation.Precheck` for the
syntax node kind `k`. It should implement eager name analysis on the passed syntax by throwing an
exception on unbound identifiers, and calling `precheck` recursively on nested terms, potentially
with an extended local context (`withNewLocal`). Macros without registered precheck hook are
unfolded, and identifier-less syntax is ultimately assumed to be well-formed.

## builtin_structInstFieldDecl_parser
 Builtin parser

## builtin_syntax_parser
 Builtin parser

## builtin_tactic
 (builtin) tactic elaborator
Registers a tactic elaborator for the given syntax node kind.

A tactic elaborator should have type `Lean.Elab.Tactic.Tactic` (which is
`Lean.Syntax → Lean.Elab.Tactic.TacticM Unit`), i.e. should take syntax of the given syntax
node kind as a parameter and alter the tactic state.

The `elab_rules` and `elab` commands should usually be preferred over using this attribute
directly.

## builtin_tactic_parser
 Builtin parser

## builtin_term_elab
 (builtin) term elaborator
Registers a term elaborator for the given syntax node kind.

A term elaborator should have type `Lean.Elab.Term.TermElab` (which is
`Lean.Syntax → Option Lean.Expr → Lean.Elab.Term.TermElabM Lean.Expr`), i.e. should take syntax of
the given syntax node kind and an optional expected type as parameters and produce an expression.

The `elab_rules` and `elab` commands should usually be preferred over using this attribute
directly.

## builtin_term_parser
 Builtin parser

## builtin_try_tactic
 (builtin) try_tactic elaborator

## builtin_unused_variables_ignore_fn
 (builtin) Marks a function of type `Lean.Linter.IgnoreFunction` for suppressing unused variable warnings
Adds the `@[{builtin_}unused_variables_ignore_fn]` attribute, which is applied
to declarations of type `IgnoreFunction` for use by the unused variables linter.

## builtin_widget_module
 (builtin) Registers a widget module. Its type must implement Lean.Widget.ToModule.
Registers a widget module. Its type must implement `Lean.Widget.ToModule`.

## bvNormalizeProcBuiltinAttr
 Builtin bv_normalize simproc

## bv_normalize
 simp theorems used by bv_normalize

## bv_normalize_proc
 simprocs used by bv_normalize

## bv_toNat
 simp lemmas converting `BitVec` goals to `Nat` goals, for the `bv_omega` preprocessor

## cases_eliminator
 custom `casesOn`-like eliminator for the `cases` tactic
Registers a custom eliminator for the `cases` tactic.

Whenever the types of the targets in an `cases` call matches a custom eliminator, it is used
instead of the `casesOn` eliminator. This can be useful for redefining the default eliminator to a
more useful one.

Example:
```lean example
structure Three where
  val : Fin 3

example (x : Three) (p : Three → Prop) : p x := by
  cases x
  -- val : Fin 3 ⊢ p ⟨val⟩

@[cases_eliminator, elab_as_elim]
def Three.myRec {motive : Three → Sort u}
    (zero : motive ⟨0⟩) (one : motive ⟨1⟩) (two : motive ⟨2⟩) :
    ∀ x, motive x
  | ⟨0⟩ => zero | ⟨1⟩ => one | ⟨2⟩ => two

example (x : Three) (p : Three → Prop) : p x := by
  cases x
  -- ⊢ p ⟨0⟩
  -- ⊢ p ⟨1⟩
  -- ⊢ p ⟨2⟩
```

`@[induction_eliminator]` works similarly for the `induction` tactic.

## category_parenthesizer
 Register a parenthesizer for a syntax category.
Registers a parenthesizer for a syntax category.

`@[category_parenthesizer cat]` registers a declaration of type
`Lean.PrettyPrinter.CategoryParenthesizer` for the syntax category `cat`, which is used when
parenthesizing occurrences of `cat:prec` (`categoryParser cat prec`). Implementations should call
`maybeParenthesize` with the precedence and `cat`. If no category parenthesizer is registered, the
category will never be parenthesized, but still traversed for parenthesizing nested categories.

## class
 type class
Registers an inductive type or structure as a type class. Using `class` or `class inductive` is
generally preferred over using `@[class] structure` or `@[class] inductive` directly.

## code_action_provider
 Use to decorate methods for suggesting code actions. This is a low-level interface for making code actions.

## coe
 Adds a definition as a coercion

## coe_decl
 auxiliary definition used to implement coercion (unfolded during elaboration)
Tags declarations to be unfolded during coercion elaboration.

This is mostly used to hide coercion implementation details and show the coerced result instead of
an application of auxiliary definitions (e.g. `CoeT.coe`, `Coe.coe`). This attribute only works on
reducible functions and instance projections.

## combinator_formatter
 Register a formatter for a parser combinator

## combinator_parenthesizer
 Register a parenthesizer for a parser combinator.

## command_code_action
 Declare a new command code action, to appear in the code actions on commands

## command_elab
 command elaborator
Registers a command elaborator for the given syntax node kind.

A command elaborator should have type `Lean.Elab.Command.CommandElab` (which is
`Lean.Syntax → Lean.Elab.Term.CommandElabM Unit`), i.e. should take syntax of the given syntax
node kind as a parameter and perform an action.

The `elab_rules` and `elab` commands should usually be preferred over using this attribute
directly.

## command_parser
 parser

## computed_field
 Marks a function as a computed field of an inductive
Marks a function as a computed field of an inductive.

Computed fields are specified in the with-block of an inductive type declaration. They can be used
to allow certain values to be computed only once at the time of construction and then later be
accessed immediately.

Example:
```lean
inductive NatList where
  | nil
  | cons : Nat → NatList → NatList
with
  @[computed_field] sum : NatList → Nat
  | .nil => 0
  | .cons x l => x + l.sum
  @[computed_field] length : NatList → Nat
  | .nil => 0
  | .cons _ l => l.length + 1
```

## congr
 congruence theorem
Registers `simp` congruence lemmas.

A `simp` congruence lemma should prove the equality of two applications of the same function from
the equality of the individual arguments. They are used by `simp` to visit subexpressions of an
application where the default congruence algorithm fails. This is particularly important for
functions where some parameters depend on previous parameters.

Congruence lemmas should have an equality for every parameter, possibly bounded by foralls, with
the right hand side being an application of a parameter on the right-hand side. When applying
congruence theorems, `simp` will first infer parameters from the right-hand side, then try to
simplify each left-hand side of the parameter equalities and finally infer the right-hand side
parameters from the result.

Example:
```lean
def Option.pbind (o : Option α) (f : (a : α) → o = some a → Option β) : Option β := ...

@[congr]
theorem Option.pbind_congr
    {o o' : Option α} (ho : o = o') -- equality for first parameter
    {f : (a : α) → o = some a → Option β} {f' : (a : α) → o' = some a → Option β}
    (hf : ∀ (a : α) (h : _), f a (ho.trans h) = f' a h) : -- equality for second parameter
    o.pbind f = o'.pbind f' := -- conclusion: equality of the whole application
  ...
```

## cpass
 compiler passes for the code generator

## csimp
 simplification theorem for the compiler
Tags compiler simplification theorems, which allow one value to be replaced by another equal value
in compiled code. This is typically used to replace a slow function whose definition is convenient
in proofs with a faster equivalent or to make noncomputable functions computable. In particular,
many operations on lists and arrays are replaced by tail-recursive equivalents.

A compiler simplification theorem cannot take any parameters and must prove a statement `@f = @g`
where `f` and `g` may be arbitrary constants. In functions defined after the theorem tagged
`@[csimp]`, any occurrence of `f` is replaced with `g` in compiled code, but not in the type
theory. In this sense, `@[csimp]` is a safer alternative to `@[implemented_by]`.

However it is still possible to register unsound `@[csimp]` lemmas by using `unsafe` or unsound
axioms (like `sorryAx`).

## default_instance
 type class default instance

## defeq
 mark theorem as a definitional equality, to be used by `dsimp`
Marks the theorem as a definitional equality.

The theorem must be an equality that holds by `rfl`. This allows `dsimp` to use this theorem
when rewriting.

A theorem with with a definition that is (syntactically) `:= rfl` is implicitly marked `@[defeq]`.
To avoid this behavior, write `:= (rfl)` instead.

The attribute should be given before a `@[simp]` attribute to have effect.

When using the module system, an exported theorem can only be `@[defeq]` if all definitions that
need to be unfolded to prove the theorem are exported and exposed.

## delab
 Register a delaborator
Registers a delaborator.

`@[delab k]` registers a declaration of type `Lean.PrettyPrinter.Delaborator.Delab` for the
`Lean.Expr` constructor `k`. Multiple delaborators for a single constructor are tried in turn until
the first success. If the term to be delaborated is an application of a constant `c`, elaborators
for `app.c` are tried first; this is also done for `Expr.const`s ("nullary applications") to reduce
special casing. If the term is an `Expr.mdata` with a single key `k`, `mdata.k` is tried first.

## deprecated
 mark declaration as deprecated

## doElem_parser
 parser

## elab_as_elim
 instructs elaborator that the arguments of the function application should be elaborated as were an eliminator
Instructs the elaborator that applications of this function should be elaborated like an eliminator.

An eliminator is a function that returns an application of a "motive" which is a parameter of the
form `_ → ... → Sort _`, i.e. a function that takes in a certain amount of arguments (referred to
as major premises) and returns a type in some universe. The `rec` and `casesOn` functions of
inductive types are automatically treated as eliminators, for other functions this attribute needs
to be used.

Eliminator elaboration can be compared to the `induction` tactic: The expected type is used as the
return value of the motive, with occurrences of the major premises replaced with the arguments.
When more arguments are specified than necessary, the remaining arguments are reverted into the
expected type.

Examples:
```lean example
@[elab_as_elim]
def evenOddRecOn {motive : Nat → Sort u}
    (even : ∀ n, motive (n * 2)) (odd : ∀ n, motive (n * 2 + 1))
    (n : Nat) : motive n := ...

-- simple usage
example (a : Nat) : (a * a) % 2 = a % 2 :=
  evenOddRec _ _ a
  /-
  1. basic motive is `fun n => (a + 2) % 2 = a % 2`
  2. major premise `a` substituted: `fun n => (n + 2) % 2 = n % 2`
  3. now elaborate the other parameters as usual:
    "even" (first hole): expected type `∀ n, ((n * 2) * (n * 2)) % 2 = (n * 2) % 2`,
    "odd" (second hole): expected type `∀ n, ((n * 2 + 1) * (n * 2 + 1)) % 2 = (n * 2 + 1) % 2`
  -/

-- complex substitution
example (a : Nat) (f : Nat → Nat) : (f a + 1) % 2 ≠ f a :=
  evenOddRec _ _ (f a)
  /-
  Similar to before, except `f a` is substituted: `motive := fun n => (n + 1) % 2 ≠ n`.
  Now the first hole has expected type `∀ n, (n * 2 + 1) % 2 ≠ n * 2`.
  Now the second hole has expected type `∀ n, (n * 2 + 1 + 1) % 2 ≠ n * 2 + 1`.
  -/

-- more parameters
example (a : Nat) (h : a % 2 = 1) : (a + 1) % 2 = 0 :=
  evenOddRec _ _ a h
  /-
  Before substitution, `a % 2 = 1` is reverted: `motive := fun n => a % 2 = 0 → (a + 1) % 2 = 0`.
  Substitution: `motive := fun n => n % 2 = 1 → (n + 1) % 2 = 0`
  Now the first hole has expected type `∀ n, n * 2 % 2 = 1 → (n * 2) % 2 = 0`.
  Now the second hole has expected type `∀ n, (n * 2 + 1) % 2 = 1 → (n * 2 + 1) % 2 = 0`.
  -/
```

See also `@[induction_eliminator]` and `@[cases_eliminator]` for registering default eliminators.

## elab_without_expected_type
 mark that applications of the given declaration should be elaborated without the expected type
Instructs the elaborator to elaborate applications of the given declaration without an expected
type. This may prevent the elaborator from incorrectly inferring implicit arguments.

## elementwise
 

## enat_to_nat_coe
 A simp set for pushing coercions from `ℕ` to `ℕ∞` in `enat_to_nat`. 

## enat_to_nat_coe_proc
 simproc set for enat_to_nat_coe_proc

## enat_to_nat_top
 A simp set for simplifying expressions involving `⊤` in `enat_to_nat`. 

## enat_to_nat_top_proc
 simproc set for enat_to_nat_top_proc

## env_linter
 Use this declaration as a linting test in #lint

## eqns
 Overrides the equation lemmas for a declaration to the provided list
Similar to `registerParametricAttribute` except that attributes do not
have to be assigned in the same file as the declaration.

## export
 name to be used by code generators
Exports a function under the provided unmangled symbol name. This can be used to refer to Lean
functions from other programming languages like C.

Example:
```lean
@[export lean_color_from_map]
def colorValue (properties : @& Std.HashMap String String) : UInt32 :=
  match properties["color"]? with
  | some "red" => 0xff0000
  | some "green" => 0x00ff00
  | some "blue" => 0x0000ff
  | _ => -1
```
C code:
```c
#include <lean/lean.h>

uint32_t lean_color_from_map(b_lean_obj_arg properties);

void fill_rectangle_from_map(b_lean_obj_arg properties) {
    uint32_t color = lean_color_from_map(properties);
    // ...
}
```

The opposite of this is `@[extern]`, which allows Lean functions to refer to functions from other
programming languages.

## expose
 (module system) Make bodies of definitions available to importing modules.
Makes the bodies of definitions available to importing modules.

This only has an effect if both the module the definition is defined in and the importing module
have the module system enabled.

## expr_presenter
 Register an Expr presenter. It must have the type `ProofWidgets.ExprPresenter`.
Register an Expr presenter. It must have the type `ProofWidgets.ExprPresenter`.

## ext
 Marks a theorem as an extensionality theorem

## extern
 builtin and foreign functions

## field_simps
 The simpset `field_simps` is used by the tactic `field_simp` to
reduce an expression in a field to an expression of the form `n / d` where `n` and `d` are
division-free. 

## field_simps_proc
 simproc set for field_simps_proc

## fin_omega
 A simp set for the `fin_omega` wrapper around `omega`. 

## fin_omega_proc
 simproc set for fin_omega_proc

## formatter
 Register a formatter for a parser.
Registers a formatter for a parser.

`@[formatter k]` registers a declaration of type `Lean.PrettyPrinter.Formatter` to be used for
formatting syntax of kind `k`.

## fun_prop
 `fun_prop` tactic to prove function properties like `Continuous`, `Differentiable`, `IsLinearMap`
Initialization of `funProp` attribute

## functor_norm
 Simp set for `functor_norm` 

## functor_norm_proc
 simproc set for functor_norm_proc

## gcongr
 generalized congruence
Attribute marking "generalized congruence" (`gcongr`) lemmas.  Such lemmas must have a
conclusion of a form such as `f x₁ y z₁ ∼ f x₂ y z₂`; that is, a relation between the application of
a function to two argument lists, in which the "varying argument" pairs (here `x₁`/`x₂` and
`z₁`/`z₂`) are all free variables.

The antecedents of such a lemma are classified as generating "main goals" if they are of the form
`x₁ ≈ x₂` for some "varying argument" pair `x₁`/`x₂` (and a possibly different relation `≈` to `∼`),
or more generally of the form `∀ i h h' j h'', f₁ i j ≈ f₂ i j` (say) for some "varying argument"
pair `f₁`/`f₂`. (Other antecedents are considered to generate "side goals".) The index of the
"varying argument" pair corresponding to each "main" antecedent is recorded.

Lemmas involving `<` or `≤` can also be marked `@[bound]` for use in the related `bound` tactic.

## gcongr_forward
 adds a gcongr_forward extension

## ghost_simps
 Simplification rules for ghost equations. 

## ghost_simps_proc
 simproc set for ghost_simps_proc

## grind
 The `[grind]` attribute is used to annotate declarations.When applied to an equational theorem, `[grind =]`, `[grind =_]`, or `[grind _=_]`will mark the theorem for use in heuristic instantiations by the `grind` tactic,
      using respectively the left-hand side, the right-hand side, or both sides of the theorem.When applied to a function, `[grind =]` automatically annotates the equational theorems associated with that function.When applied to a theorem `[grind ←]` will instantiate the theorem whenever it encounters the conclusion of the theorem
      (that is, it will use the theorem for backwards reasoning).When applied to a theorem `[grind →]` will instantiate the theorem whenever it encounters sufficiently many of the propositional hypotheses
      (that is, it will use the theorem for forwards reasoning).The attribute `[grind]` by itself will effectively try `[grind ←]` (if the conclusion is sufficient for instantiation) and then `[grind →]`.The `grind` tactic utilizes annotated theorems to add instances of matching patterns into the local context during proof search.For example, if a theorem `@[grind =] theorem foo_idempotent : foo (foo x) = foo x` is annotated,`grind` will add an instance of this theorem to the local context whenever it encounters the pattern `foo (foo x)`.
Auxiliary function for registering `grind` and `grind?` attributes.
The `grind?` is an alias for `grind` which displays patterns using `logInfo`.
It is just a convenience for users.

## grind?
 The `[grind?]` attribute is identical to the `[grind]` attribute, but displays inferred pattern information.When applied to an equational theorem, `[grind =]`, `[grind =_]`, or `[grind _=_]`will mark the theorem for use in heuristic instantiations by the `grind` tactic,
      using respectively the left-hand side, the right-hand side, or both sides of the theorem.When applied to a function, `[grind =]` automatically annotates the equational theorems associated with that function.When applied to a theorem `[grind ←]` will instantiate the theorem whenever it encounters the conclusion of the theorem
      (that is, it will use the theorem for backwards reasoning).When applied to a theorem `[grind →]` will instantiate the theorem whenever it encounters sufficiently many of the propositional hypotheses
      (that is, it will use the theorem for forwards reasoning).The attribute `[grind]` by itself will effectively try `[grind ←]` (if the conclusion is sufficient for instantiation) and then `[grind →]`.The `grind` tactic utilizes annotated theorems to add instances of matching patterns into the local context during proof search.For example, if a theorem `@[grind =] theorem foo_idempotent : foo (foo x) = foo x` is annotated,`grind` will add an instance of this theorem to the local context whenever it encounters the pattern `foo (foo x)`.
Auxiliary function for registering `grind` and `grind?` attributes.
The `grind?` is an alias for `grind` which displays patterns using `logInfo`.
It is just a convenience for users.

## grindPropagatorBuiltinAttr
 Builtin `grind` propagator procedure

## higherOrder
 From a lemma of the shape `∀ x, f (g x) = h x` derive an auxiliary lemma of the
form `f ∘ g = h` for reasoning about higher-order functions.

Syntax: `[higher_order]` or `[higher_order name]`, where the given name is used for the
generated theorem.
The `higher_order` attribute. From a lemma of the shape `∀ x, f (g x) = h x` derive an
auxiliary lemma of the form `f ∘ g = h` for reasoning about higher-order functions.

Syntax: `[higher_order]` or `[higher_order name]` where the given name is used for the
generated theorem.

## hole_code_action
 Declare a new hole code action, to appear in the code actions on ?_ and _

## implemented_by
 name of the Lean (probably unsafe) function that implements opaque constant
Instructs the compiler to use a different function as the implementation of a function. With the
exception of tactics that call native code such as `native_decide`, the kernel and type checking
are unaffected. When this attribute is used on a function, the function is not compiled and all
compiler-related attributes (e.g. `noncomputable`, `@[inline]`) are ignored. Calls to this
function are replaced by calls to its implementation.

The most common use cases of `@[implemented_by]` are to provide an efficient unsafe implementation
and to make an unsafe function accessible in safe code through an opaque function:

```
unsafe def testEqImpl (as bs : Array Nat) : Bool :=
  ptrEq as bs || as == bs

@[implemented_by testEqImpl]
def testEq (as bs : Array Nat) : Bool :=
  as == bs

unsafe def printAddrImpl {α : Type u} (x : α) : IO Unit :=
  IO.println s!"Address: {ptrAddrUnsafe x}"

@[implemented_by printAddrImpl]
opaque printAddr {α : Type u} (x : α) : IO Unit
```

The provided implementation is not checked to be equivalent to the original definition. This makes
it possible to prove `False` with `native_decide` using incorrect implementations. For a safer
variant of this attribute that however doesn't work for unsafe implementations, see `@[csimp]`,
which requires a proof that the two functions are equal.

## incremental
 Marks an elaborator (tactic or command, currently) as supporting incremental elaboration. For unmarked elaborators, the corresponding snapshot bundle field in the elaboration context is unset so as to prevent accidental, incorrect reuse.
Marks an elaborator (tactic or command, currently) as supporting incremental elaboration.

For unmarked elaborators, the corresponding snapshot bundle field in the elaboration context is
unset so as to prevent accidental, incorrect reuse.

## induction_eliminator
 custom `rec`-like eliminator for the `induction` tactic
Registers a custom eliminator for the `induction` tactic.

Whenever the types of the targets in an `induction` call matches a custom eliminator, it is used
instead of the recursor. This can be useful for redefining the default eliminator to a more useful
one.

Example:
```lean example
structure Three where
  val : Fin 3

example (x : Three) (p : Three → Prop) : p x := by
  induction x
  -- val : Fin 3 ⊢ p ⟨val⟩

@[induction_eliminator, elab_as_elim]
def Three.myRec {motive : Three → Sort u}
    (zero : motive ⟨0⟩) (one : motive ⟨1⟩) (two : motive ⟨2⟩) :
    ∀ x, motive x
  | ⟨0⟩ => zero | ⟨1⟩ => one | ⟨2⟩ => two

example (x : Three) (p : Three → Prop) : p x := by
  induction x
  -- ⊢ p ⟨0⟩
  -- ⊢ p ⟨1⟩
  -- ⊢ p ⟨2⟩
```

`@[cases_eliminator]` works similarly for the `cases` tactic.

## inductive_elab
 Register an elaborator for inductive types
Registers an inductive type elaborator for the given syntax node kind.

Commands registered using this attribute are allowed to be used together in mutual blocks with
other inductive type commands. This attribute is mostly used internally for `inductive` and
`structure`.

An inductive type elaborator should have type `Lean.Elab.Command.InductiveElabDescr`.

## inherit_doc
 inherit documentation from a specified declaration
Uses documentation from a specified declaration.

`@[inherit_doc decl]` is used to inherit the documentation from the declaration `decl`.

## init
 initialization procedure for global references
Registers an initialization procedure. Initialization procedures are run in files that import the
file they are defined in.

This attribute comes in two kinds: Without arguments, the tagged declaration should have type
`IO Unit` and are simply run during initialization. With a declaration name as a argument, the
tagged declaration should be an opaque constant and the provided declaration name an action in `IO`
that returns a value of the type of the tagged declaration. Such initialization procedures store
the resulting value and make it accessible through the tagged declaration.

The `initialize` command should usually be preferred over using this attribute directly.

## inline
 mark definition to be inlined
Changes the inlining behavior. This attribute comes in several variants:
- `@[inline]`: marks the definition to be inlined when it is appropriate.
- `@[inline_if_reduce]`: marks the definition to be inlined if an application of it after inlining
  and applying reduction isn't a `match` expression. This attribute can be used for inlining
  structurally recursive functions.
- `@[noinline]`: marks the definition to never be inlined.
- `@[always_inline]`: marks the definition to always be inlined.
- `@[macro_inline]`: marks the definition to always be inlined at the beginning of compilation.
  This makes it possible to define functions that evaluate some of their parameters lazily.
  Example:
  ```
  @[macro_inline]
  def test (x y : Nat) : Nat :=
    if x = 42 then x else y

  #eval test 42 (2^1000000000000) -- doesn't compute 2^1000000000000
  ```
  Only non-recursive functions may be marked `@[macro_inline]`.

## inline_if_reduce
 mark definition to be inlined when resultant term after reduction is not a `cases_on` application
Changes the inlining behavior. This attribute comes in several variants:
- `@[inline]`: marks the definition to be inlined when it is appropriate.
- `@[inline_if_reduce]`: marks the definition to be inlined if an application of it after inlining
  and applying reduction isn't a `match` expression. This attribute can be used for inlining
  structurally recursive functions.
- `@[noinline]`: marks the definition to never be inlined.
- `@[always_inline]`: marks the definition to always be inlined.
- `@[macro_inline]`: marks the definition to always be inlined at the beginning of compilation.
  This makes it possible to define functions that evaluate some of their parameters lazily.
  Example:
  ```
  @[macro_inline]
  def test (x y : Nat) : Nat :=
    if x = 42 then x else y

  #eval test 42 (2^1000000000000) -- doesn't compute 2^1000000000000
  ```
  Only non-recursive functions may be marked `@[macro_inline]`.

## instance
 type class instance
Registers type class instances.

The `instance` command, which expands to `@[instance] def`, is usually preferred over using this
attribute directly. However it might sometimes still be necessary to use this attribute directly,
in particular for `opaque` instances.

To assign priorities to instances, `@[instance prio]` can be used (where `prio` is a priority).
This corresponds to the `instance (priority := prio)` notation.

## int_toBitVec
 simp theorems used to convert UIntX/IntX statements into BitVec ones

## integral_simps
 Simp set for integral rules. 

## integral_simps_proc
 simproc set for integral_simps_proc

## irreducible
 irreducible declaration

## is_poly
 A stub attribute for `is_poly`. 

## macro
 macro elaborator
Registers a macro expander for a given syntax node kind.

A macro expander should have type `Lean.Macro` (which is `Lean.Syntax → Lean.MacroM Lean.Syntax`),
i.e. should take syntax of the given syntax node kind as a parameter and produce different syntax
in the same syntax category.

The `macro_rules` and `macro` commands should usually be preferred over using this attribute
directly.

## macro_inline
 mark definition to always be inlined before ANF conversion
Changes the inlining behavior. This attribute comes in several variants:
- `@[inline]`: marks the definition to be inlined when it is appropriate.
- `@[inline_if_reduce]`: marks the definition to be inlined if an application of it after inlining
  and applying reduction isn't a `match` expression. This attribute can be used for inlining
  structurally recursive functions.
- `@[noinline]`: marks the definition to never be inlined.
- `@[always_inline]`: marks the definition to always be inlined.
- `@[macro_inline]`: marks the definition to always be inlined at the beginning of compilation.
  This makes it possible to define functions that evaluate some of their parameters lazily.
  Example:
  ```
  @[macro_inline]
  def test (x y : Nat) : Nat :=
    if x = 42 then x else y

  #eval test 42 (2^1000000000000) -- doesn't compute 2^1000000000000
  ```
  Only non-recursive functions may be marked `@[macro_inline]`.

## match_pattern
 mark that a definition can be used in a pattern (remark: the dependent pattern matching compiler will unfold the definition)
Instructs the pattern matcher to unfold occurrences of this definition.

By default, only constructors and literals can be used for pattern matching. Using
`@[match_pattern]` allows using other definitions, as long as they eventually reduce to
constructors and literals.

Example:
```lean
@[match_pattern]
def yellowString : String := "yellow"

def isYellow (color : String) : Bool :=
  match color with
  | yellowString => true
  | _ => false
```

## mfld_simps
 The simpset `mfld_simps` records several simp lemmas that are
especially useful in manifolds. It is a subset of the whole set of simp lemmas, but it makes it
possible to have quicker proofs (when used with `squeeze_simp` or `simp only`) while retaining
readability.

The typical use case is the following, in a file on manifolds:
If `simp [foo, bar]` is slow, replace it with `squeeze_simp [foo, bar, mfld_simps]` and paste
its output. The list of lemmas should be reasonable (contrary to the output of
`squeeze_simp [foo, bar]` which might contain tens of lemmas), and the outcome should be quick
enough.


## mfld_simps_proc
 simproc set for mfld_simps_proc

## missing_docs_handler
 adds a syntax traversal for the missing docs linter

## mkIff
 Generate an `iff` lemma for an inductive `Prop`.

## monad_norm
 Simp set for `functor_norm` 

## monad_norm_proc
 simproc set for monad_norm_proc

## mono
 A lemma stating the monotonicity of some function, with respect to appropriate
relations on its domain and range, and possibly with side conditions.

## multigoal
 this tactic acts on multiple goals
The `multigoal` attribute keeps track of tactics that operate on multiple goals,
meaning that `tac` acts differently from `focus tac`. This is used by the
'unnecessary `<;>`' linter to prevent false positives where `tac <;> tac'` cannot
be replaced by `(tac; tac')` because the latter would expose `tac` to a different set of goals.

## mvcgen_simp
 simp theorems internally used by `mvcgen`
This attribute should not be used directly.
It is an implementation detail of the `mvcgen` tactic.

## never_extract
 instruct the compiler that function applications using the tagged declaration should not be extracted when they are closed terms, nor common subexpression should be performed. This is useful for declarations that have implicit effects.
Instructs the compiler that function applications using the tagged declaration should not be
extracted when they are closed terms, and that common subexpression elimination should not be
performed.

Ordinarily, the Lean compiler identifies closed terms (without free variables) and extracts them
to top-level definitions. This optimization can prevent unnecessary recomputation of values.

Preventing the extraction of closed terms is useful for declarations that have implicit effects
that should be repeated.

## no_expose
 (module system) Negate previous `[expose]` attribute.
Negates a previous `@[expose]` attribute. This is useful for declaring definitions that shouldn't.
be exposed in a section tagged `@[expose]`

This only has an effect if both the module the definition is defined in and the importing module
have the module system enabled.

## noinline
 mark definition to never be inlined
Changes the inlining behavior. This attribute comes in several variants:
- `@[inline]`: marks the definition to be inlined when it is appropriate.
- `@[inline_if_reduce]`: marks the definition to be inlined if an application of it after inlining
  and applying reduction isn't a `match` expression. This attribute can be used for inlining
  structurally recursive functions.
- `@[noinline]`: marks the definition to never be inlined.
- `@[always_inline]`: marks the definition to always be inlined.
- `@[macro_inline]`: marks the definition to always be inlined at the beginning of compilation.
  This makes it possible to define functions that evaluate some of their parameters lazily.
  Example:
  ```
  @[macro_inline]
  def test (x y : Nat) : Nat :=
    if x = 42 then x else y

  #eval test 42 (2^1000000000000) -- doesn't compute 2^1000000000000
  ```
  Only non-recursive functions may be marked `@[macro_inline]`.

## nolint
 Do not report this declaration in any of the tests of `#lint`
Defines the user attribute `nolint` for skipping `#lint`

## nontriviality
 The `@[nontriviality]` simp set is used by the `nontriviality` tactic to automatically
discharge theorems about the trivial case (where we know `Subsingleton α` and many theorems
in e.g. groups are trivially true). 

## nontriviality_proc
 simproc set for nontriviality_proc

## norm_cast
 attribute for norm_cast

## norm_num
 adds a norm_num extension

## nospecialize
 mark definition to never be specialized
Marks a definition to never be specialized during code generation.

## notation_class
 An attribute specifying that this is a notation class. Used by @[simps].
`@[notation_class]` attribute. Note: this is *not* a `NameMapAttribute` because we key on the
argument of the attribute, not the declaration name.

## parenthesizer
 Register a parenthesizer for a parser.
Registers a parenthesizer for a parser.

`@[parenthesizer k]` registers a declaration of type `Lean.PrettyPrinter.Parenthesizer` to be used
for parenthesizing syntax of kind `k`.

## parity_simps
 Simp attribute for lemmas about `Even` 

## parity_simps_proc
 simproc set for parity_simps_proc

## partial_fixpoint_monotone
 monotonicity theorem
Registers a monotonicity theorem for `partial_fixpoint`.

Monotonicity theorems should have `Lean.Order.monotone ...` as a conclusion. They are used in the
`monotonicity` tactic (scoped in the `Lean.Order` namespace) to automatically prove monotonicity
for functions defined using `partial_fixpoint`.

## pnat_to_nat_coe
 A simp set for the `pnat_to_nat` tactic. 

## pnat_to_nat_coe_proc
 simproc set for pnat_to_nat_coe_proc

## positivity
 adds a positivity extension

## ppWithUnivAttr
 

## pp_nodot
 mark declaration to never be pretty printed using field notation
Marks a declaration to never be pretty printed using field notation.

## pp_using_anonymous_constructor
 mark structure to be pretty printed using `⟨a,b,c⟩` notation
Marks a structure to be pretty printed using the anonymous constructor notation (`⟨a, b, c⟩`).

## prec_parser
 parser

## prio_parser
 parser

## push_cast
 The `push_cast` simp attribute uses `norm_cast` lemmas to move casts toward the leaf nodes of the expression.
The `push_cast` simp attribute.

## qify_simps
 The simpset `qify_simps` is used by the tactic `qify` to move expressions from `ℕ` or `ℤ` to `ℚ`
which gives a well-behaved division. 

## qify_simps_proc
 simproc set for qify_simps_proc

## quot_precheck
 Register a double backtick syntax quotation pre-check.
Registers a double backtick syntax quotation pre-check.

`@[quot_precheck k]` registers a declaration of type `Lean.Elab.Term.Quotation.Precheck` for the
syntax node kind `k`. It should implement eager name analysis on the passed syntax by throwing an
exception on unbound identifiers, and calling `precheck` recursively on nested terms, potentially
with an extended local context (`withNewLocal`). Macros without registered precheck hook are
unfolded, and identifier-less syntax is ultimately assumed to be well-formed.

## rclike_simps
 "Simp attribute for lemmas about `RCLike`" 

## rclike_simps_proc
 simproc set for rclike_simps_proc

## reassoc
 

## recursor
 user defined recursor, numerical parameter specifies position of the major premise

## reduce_mod_char
 lemmas for preprocessing and cleanup in the `reduce_mod_char` tactic
`@[reduce_mod_char]` is an attribute that tags lemmas for preprocessing and cleanup in the
`reduce_mod_char` tactic

## reducible
 reducible declaration

## refl
 reflexivity relation
Tags reflexivity lemmas to be used by the `rfl` tactic.

A reflexivity lemma should have the conclusion `r x x` where `r` is an arbitrary relation.

It is not possible to tag reflexivity lemmas for `=` using this attribute. These are handled as a
special case in the `rfl` tactic.

## rify_simps
 The simpset `rify_simps` is used by the tactic `rify` to move expressions from `ℕ`, `ℤ`, or
`ℚ` to `ℝ`. 

## rify_simps_proc
 simproc set for rify_simps_proc

## run_builtin_parser_attribute_hooks
 explicitly run hooks normally activated by builtin parser attributes

## run_parser_attribute_hooks
 explicitly run hooks normally activated by parser attributes

## semireducible
 semireducible declaration

## server_rpc_method
 Marks a function as a Lean server RPC method.
    Shorthand for `registerRpcProcedure`.
    The function must have type `α → RequestM (RequestTask β)` with
    `[RpcEncodable α]` and `[RpcEncodable β]`.

## server_rpc_method_cancellable
 Like `server_rpc_method`, but requests for this method can be cancelled. The method should check for that using `IO.checkCanceled`. Cancellable methods are invoked differently from JavaScript: see `callCancellable` in `cancellable.ts`.
Like `server_rpc_method`, but requests for this method can be cancelled.
The method should check for that using `IO.checkCanceled`.
Cancellable methods are invoked differently from JavaScript:
see `callCancellable` in `cancellable.ts`.

## seval
 symbolic evaluator theorem

## sevalprocAttr
 Symbolic evaluator procedure

## sevalprocBuiltinAttr
 Builtin symbolic evaluation procedure

## simp
 simplification theorem

## simprocAttr
 Simplification procedure

## simprocBuiltinAttr
 Builtin simplification procedure

## simps
 Automatically derive lemmas specifying the projections of this declaration.
The `simps` attribute.

## spec
 Marks Hoare triple specifications and simp theorems to use with the `mspec` and `mvcgen` tactics

## specialize
 mark definition to always be specialized
Marks a definition to always be specialized during code generation.

Specialization is an optimization in the code generator for generating variants of a function that
are specialized to specific parameter values. This is in particular useful for functions that take
other functions as parameters: Usually when passing functions as parameters, a closure needs to be
allocated that will then be called. Using `@[specialize]` prevents both of these operations by
using the provided function directly in the specialization of the inner function.

`@[specialize]` can take additional arguments for the parameter names or indices (starting at 1) of
the parameters that should be specialized. By default, instance and function parameters are
specialized.

## stacksTag
 Apply a Stacks or Kerodon project tag to a theorem.

## stx_parser
 parser

## symm
 symmetric relation
Tags symmetry lemmas to be used by the `symm` tactic.

A symmetry lemma should be of the form `r x y → r y x` where `r` is an arbitrary relation.

## tactic
 tactic elaborator
Registers a tactic elaborator for the given syntax node kind.

A tactic elaborator should have type `Lean.Elab.Tactic.Tactic` (which is
`Lean.Syntax → Lean.Elab.Tactic.TacticM Unit`), i.e. should take syntax of the given syntax
node kind as a parameter and alter the tactic state.

The `elab_rules` and `elab` commands should usually be preferred over using this attribute
directly.

## tactic_alt
 Register a tactic parser as an alternative form of an existing tactic, so they can be grouped together in documentation.

## tactic_code_action
 Declare a new tactic code action, to appear in the code actions on tactics

## tactic_parser
 parser

## tactic_tag
 Register a tactic parser as an alternative of an existing tactic, so they can be grouped together in documentation.

## term_elab
 term elaborator
Registers a term elaborator for the given syntax node kind.

A term elaborator should have type `Lean.Elab.Term.TermElab` (which is
`Lean.Syntax → Option Lean.Expr → Lean.Elab.Term.TermElabM Lean.Expr`), i.e. should take syntax of
the given syntax node kind and an optional expected type as parameters and produce an expression.

The `elab_rules` and `elab` commands should usually be preferred over using this attribute
directly.

## term_parser
 parser

## to_additive
 Transport multiplicative to additive

## to_additive_change_numeral
 Auxiliary attribute for `to_additive` that stores functions that have numerals as argument.
Similar to `registerParametricAttribute` except that attributes do not
have to be assigned in the same file as the declaration.

## to_additive_dont_translate
 Auxiliary attribute for `to_additive` stating that the operations on this type should not be translated.
Similar to `registerParametricAttribute` except that attributes do not
have to be assigned in the same file as the declaration.

## to_additive_ignore_args
 Auxiliary attribute for `to_additive` stating that certain arguments are not additivized.
Similar to `registerParametricAttribute` except that attributes do not
have to be assigned in the same file as the declaration.

## to_additive_relevant_arg
 Auxiliary attribute for `to_additive` stating which arguments are the types with a multiplicative structure.
Similar to `registerParametricAttribute` except that attributes do not
have to be assigned in the same file as the declaration.

## to_app
 

## trans
 transitive relation

## try_tactic
 try_tactic elaborator

## typevec
 simp set for the manipulation of typevec and arrow expressions 

## typevec_proc
 simproc set for typevec_proc

## unbox
 compiler tries to unbox result values if their types are tagged with `[unbox]`
Tags types that the compiler should unbox if they occur in result values.

This attribute currently has no effect.

## unification_hint
 unification hint

## unused_variables_ignore_fn
 Marks a function of type `Lean.Linter.IgnoreFunction` for suppressing unused variable warnings
Adds the `@[{builtin_}unused_variables_ignore_fn]` attribute, which is applied
to declarations of type `IgnoreFunction` for use by the unused variables linter.

## variable_alias
 Attribute to record aliases for the `variable?` command.
Attribute to record aliases for the `variable?` command. Aliases are structures that have no
fields, and additional typeclasses are recorded as *arguments* to the structure.

Example:
```lean
@[variable_alias]
structure VectorSpace (k V : Type*)
  [Field k] [AddCommGroup V] [Module k V]
```
Then `variable? [VectorSpace k V]` ensures that these three typeclasses are present in
the current scope. Notice that it's looking at the arguments to the `VectorSpace` type
constructor. You should not have any fields in `variable_alias` structures.

Notice that `VectorSpace` is not a class; the `variable?` command allows non-classes with the
`variable_alias` attribute to use instance binders.

## wf_preprocess
 simp lemma used in the preprocessing of well-founded recursive function definitions, in particular to add additional hypotheses to the context. Also see `wfParam`.

## widget_module
 Registers a widget module. Its type must implement Lean.Widget.ToModule.
Registers a widget module. Its type must implement `Lean.Widget.ToModule`.

## zify_simps
 The simpset `zify_simps` is used by the tactic `zify` to move expressions from `ℕ` to `ℤ`
which gives a well-behaved subtraction. 

## zify_simps_proc
 simproc set for zify_simps_proc

