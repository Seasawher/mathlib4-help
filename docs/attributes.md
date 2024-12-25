# Attributes

Mathlib version: `c93dd21f321c9fe77ab73aecf674178a6af5ce5e`

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

## app_unexpander
 Register an unexpander for applications of a given constant.

[app_unexpander c] registers a `Lean.PrettyPrinter.Unexpander` for applications of the constant `c`. The unexpander is
passed the result of pre-pretty printing the application *without* implicitly passed arguments. If `pp.explicit` is set
to true or `pp.notation` is set to false, it will not be called at all.

## attr_parser
 parser

## boolToPropSimps
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

  [category_parenthesizer cat] registers a declaration of type `Lean.PrettyPrinter.CategoryParenthesizer` for the category `cat`,
  which is used when parenthesizing calls of `categoryParser cat prec`. Implementations should call `maybeParenthesize`
  with the precedence and `cat`. If no category parenthesizer is registered, the category will never be parenthesized,
  but still be traversed for parenthesizing nested categories.

## builtin_code_action_provider
 (builtin) Use to decorate methods for suggesting code actions. This is a low-level interface for making code actions.

## builtin_command_code_action
 Declare a new builtin command code action, to appear in the code actions on commands

## builtin_command_elab
 (builtin) command elaborator

## builtin_command_parser
 Builtin parser

## builtin_delab
 (builtin) Register a delaborator.

  [delab k] registers a declaration of type `Lean.PrettyPrinter.Delaborator.Delab` for the `Lean.Expr`
  constructor `k`. Multiple delaborators for a single constructor are tried in turn until
  the first success. If the term to be delaborated is an application of a constant `c`,
  elaborators for `app.c` are tried first; this is also done for `Expr.const`s ("nullary applications")
  to reduce special casing. If the term is an `Expr.mdata` with a single key `k`, `mdata.k`
  is tried first.

## builtin_doElem_parser
 Builtin parser

## builtin_doc
 make the docs and location of this declaration available as a builtin

## builtin_formatter
 (builtin) Register a formatter for a parser.

  [formatter k] registers a declaration of type `Lean.PrettyPrinter.Formatter` for the `SyntaxNodeKind` `k`.

## builtin_incremental
 (builtin) Marks an elaborator (tactic or command, currently) as supporting incremental elaboration. For unmarked elaborators, the corresponding snapshot bundle field in the elaboration context is unset so as to prevent accidental, incorrect reuse.

## builtin_inductive_elab
 (builtin) Register an elaborator for inductive types
Environment extension to register inductive type elaborator commands.

## builtin_init
 initialization procedure for global references

## builtin_level_parser
 Builtin parser

## builtin_macro
 (builtin) macro elaborator

## builtin_missing_docs_handler
 (builtin) adds a syntax traversal for the missing docs linter

## builtin_parenthesizer
 (builtin) Register a parenthesizer for a parser.

  [parenthesizer k] registers a declaration of type `Lean.PrettyPrinter.Parenthesizer` for the `SyntaxNodeKind` `k`.

## builtin_prec_parser
 Builtin parser

## builtin_prio_parser
 Builtin parser

## builtin_quot_precheck
 (builtin) Register a double backtick syntax quotation pre-check.

[quot_precheck k] registers a declaration of type `Lean.Elab.Term.Quotation.Precheck` for the `SyntaxNodeKind` `k`.
It should implement eager name analysis on the passed syntax by throwing an exception on unbound identifiers,
and calling `precheck` recursively on nested terms, potentially with an extended local context (`withNewLocal`).
Macros without registered precheck hook are unfolded, and identifier-less syntax is ultimately assumed to be well-formed.

## builtin_structInstFieldDecl_parser
 Builtin parser

## builtin_syntax_parser
 Builtin parser

## builtin_tactic
 (builtin) tactic elaborator

## builtin_tactic_parser
 Builtin parser

## builtin_term_elab
 (builtin) term elaborator

## builtin_term_parser
 Builtin parser

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

## category_parenthesizer
 Register a parenthesizer for a syntax category.

  [category_parenthesizer cat] registers a declaration of type `Lean.PrettyPrinter.CategoryParenthesizer` for the category `cat`,
  which is used when parenthesizing calls of `categoryParser cat prec`. Implementations should call `maybeParenthesize`
  with the precedence and `cat`. If no category parenthesizer is registered, the category will never be parenthesized,
  but still be traversed for parenthesizing nested categories.

## class
 type class

## code_action_provider
 Use to decorate methods for suggesting code actions. This is a low-level interface for making code actions.

## coe
 Adds a definition as a coercion

## coe_decl
 auxiliary definition used to implement coercion (unfolded during elaboration)

## combinator_formatter
 Register a formatter for a parser combinator.

  [combinator_formatter c] registers a declaration of type `Lean.PrettyPrinter.Formatter` for the `Parser` declaration `c`.
  Note that, unlike with [formatter], this is not a node kind since combinators usually do not introduce their own node kinds.
  The tagged declaration may optionally accept parameters corresponding to (a prefix of) those of `c`, where `Parser` is replaced
  with `Formatter` in the parameter types.

## combinator_parenthesizer
 Register a parenthesizer for a parser combinator.

  [combinator_parenthesizer c] registers a declaration of type `Lean.PrettyPrinter.Parenthesizer` for the `Parser` declaration `c`.
  Note that, unlike with [parenthesizer], this is not a node kind since combinators usually do not introduce their own node kinds.
  The tagged declaration may optionally accept parameters corresponding to (a prefix of) those of `c`, where `Parser` is replaced
  with `Parenthesizer` in the parameter types.

## command_code_action
 Declare a new command code action, to appear in the code actions on commands

## command_elab
 command elaborator

## command_parser
 parser

## computed_field
 Marks a function as a computed field of an inductive

## congr
 congruence theorem

## cpass
 compiler passes for the code generator

## csimp
 simplification theorem for the compiler

## default_instance
 type class default instance

## delab
 Register a delaborator.

  [delab k] registers a declaration of type `Lean.PrettyPrinter.Delaborator.Delab` for the `Lean.Expr`
  constructor `k`. Multiple delaborators for a single constructor are tried in turn until
  the first success. If the term to be delaborated is an application of a constant `c`,
  elaborators for `app.c` are tried first; this is also done for `Expr.const`s ("nullary applications")
  to reduce special casing. If the term is an `Expr.mdata` with a single key `k`, `mdata.k`
  is tried first.

## deprecated
 mark declaration as deprecated

## doElem_parser
 parser

## elab_as_elim
 instructs elaborator that the arguments of the function application should be elaborated as were an eliminator

## elab_without_expected_type
 mark that applications of the given declaration should be elaborated without the expected type

## elementwise
 

## env_linter
 Use this declaration as a linting test in #lint

## eqns
 Overrides the equation lemmas for a declaration to the provided list
Similar to `registerParametricAttribute` except that attributes do not
have to be assigned in the same file as the declaration.

## export
 name to be used by code generators

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

  [formatter k] registers a declaration of type `Lean.PrettyPrinter.Formatter` for the `SyntaxNodeKind` `k`.

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

## grind_cases
 `grind` tactic applies `cases` to (non-recursive) inductives during pre-processing step

## grind_norm
 simplification/normalization theorems for `grind`

## grind_norm_proc
 simplification/normalization procedured for `grind`

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

## incremental
 Marks an elaborator (tactic or command, currently) as supporting incremental elaboration. For unmarked elaborators, the corresponding snapshot bundle field in the elaboration context is unset so as to prevent accidental, incorrect reuse.

## induction_eliminator
 custom `rec`-like eliminator for the `induction` tactic

## inductive_elab
 Register an elaborator for inductive types
Environment extension to register inductive type elaborator commands.

## inherit_doc
 inherit documentation from a specified declaration

## init
 initialization procedure for global references

## inline
 mark definition to be inlined

## inline_if_reduce
 mark definition to be inlined when resultant term after reduction is not a `cases_on` application

## instance
 type class instance

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

## macro_inline
 mark definition to always be inlined before ANF conversion

## match_pattern
 mark that a definition can be used in a pattern (remark: the dependent pattern matching compiler will unfold the definition)

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

## never_extract
 instruct the compiler that function applications using the tagged declaration should not be extracted when they are closed terms, nor common subexpression should be performed. This is useful for declarations that have implicit effects.

## noinline
 mark definition to never be inlined

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

## notation_class
 An attribute specifying that this is a notation class. Used by @[simps].
`@[notation_class]` attribute. Note: this is *not* a `NameMapAttribute` because we key on the
argument of the attribute, not the declaration name.

## parenthesizer
 Register a parenthesizer for a parser.

  [parenthesizer k] registers a declaration of type `Lean.PrettyPrinter.Parenthesizer` for the `SyntaxNodeKind` `k`.

## parity_simps
 Simp attribute for lemmas about `Even` 

## parity_simps_proc
 simproc set for parity_simps_proc

## positivity
 adds a positivity extension

## ppDotAttr
 

## ppWithUnivAttr
 

## pp_nodot
 mark declaration to never be pretty printed using field notation

## pp_using_anonymous_constructor
 mark structure to be pretty printed using `⟨a,b,c⟩` notation

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

[quot_precheck k] registers a declaration of type `Lean.Elab.Term.Quotation.Precheck` for the `SyntaxNodeKind` `k`.
It should implement eager name analysis on the passed syntax by throwing an exception on unbound identifiers,
and calling `precheck` recursively on nested terms, potentially with an extended local context (`withNewLocal`).
Macros without registered precheck hook are unfolded, and identifier-less syntax is ultimately assumed to be well-formed.

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

## specialize
 mark definition to always be specialized

## stacksTag
 Apply a Stacks or Kerodon project tag to a theorem.

## stx_parser
 parser

## symm
 symmetric relation

## tactic
 tactic elaborator

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

## to_additive_reorder
 Auxiliary attribute for `to_additive` that stores arguments that need to be reordered. This should not appear in any file. We keep it as an attribute for now so that mathport can still use it, and it can generate a warning.
Similar to `registerParametricAttribute` except that attributes do not
have to be assigned in the same file as the declaration.

## to_app
 

## trans
 transitive relation

## typevec
 simp set for the manipulation of typevec and arrow expressions 

## typevec_proc
 simproc set for typevec_proc

## unbox
 compiler tries to unbox result values if their types are tagged with `[unbox]`

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

## widget_module
 Registers a widget module. Its type must implement Lean.Widget.ToModule.
Registers a widget module. Its type must implement `Lean.Widget.ToModule`.

## zify_simps
 The simpset `zify_simps` is used by the tactic `zify` to move expressions from `ℕ` to `ℤ`
which gives a well-behaved subtraction.   ## zify_simps_proc
 simproc set for zify_simps_proc  
