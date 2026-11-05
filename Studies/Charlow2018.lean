module

public import Linglib.Semantics.Composition.Assignment
public import Mathlib.Control.Applicative
public import Mathlib.Control.Basic
public import Mathlib.Control.Monad.Cont
public import Mathlib.Control.Traversable.Basic
public import Mathlib.Data.Set.Functor

/-!
# Charlow 2018: a modular theory of pronouns and binding

Heim and Kratzer's theory of pronouns makes every meaning depend on an assignment and hands one
assignment to both daughters of a branching node, so [no denotation of a binder can
bind](##not_exists_abstraction_denotation). Charlow factors the theory into a lift `ρ` and an
application `⊛`, the `pure` and `<*>` of Lean's reader applicative, under which abstraction is an
ordinary operation on meanings. A flattener `μ`, the reader monad's `joinM`, lets a pronoun's value
be an intension, and derives [paycheck pronouns](##paycheck) and [binding
reconstruction](##reconstruction). Assignments can [hold every intension only if there is at most
one individual](##subsingleton_of_surjective), and on assignments typed by the values they hold,
two composed reader applicatives derive [the paycheck reading with no flattener](##typed_paycheck).
At the entity type the same applicative is Jacobson's variable-free semantics, whose meanings are
[the variable-full meanings up to isomorphism](##bijOn_toAssignment).

## Implementation notes

* `ρ`, `⊛` and `μ` are `pure`, `<*>` and `joinM` of `ReaderM (Assignment E)`, the paper's four
  applicative laws are its `LawfulApplicative` instance, and the composite of two applicatives is
  mathlib's `Functor.Comp`.
* For pronouns whose values are intensions, `G` is an abstract type of assignments with lookups
  `ind i` for individual variables and `con i` for variables over individual concepts, and a
  shift for each. The paper's one polymorphic pronoun type is these two lookups. Each derivation
  assumes only the laws it uses, for the one intension it stores.
* As in the paper, `likes x y` is "`y` likes `x`".

## Errata

* The paper presents a monad by `ρ`, `⊛` and `μ` with an associativity and an identity law, which
  mention `⊛` only as `ρ f ⊛ m`, the functor's map, and so leave `⊛` free of `μ`. The writer's
  flattener satisfies both laws with the writer's application run backwards, a lawful applicative
  that is [not the application its monad determines](##BackwardsWriter.exists_seq_ne). The two
  presentations agree only under a further law such as `m ⊛ n = μ (ρ (λf. ρ f ⊛ n) ⊛ m)`, which
  every lawful monad satisfies.
* The paycheck reading on type-homogeneous assignments is stated for *her₀* but reads `g₁`, the
  variable of the earlier derivation's *her₁*; the formula is encoded. The text calls that
  derivation "Figure 6 (left)", a figure with one panel.

## TODO

* Composing sets with the reader (`S ∘ G`) admits no lawful flattener.

## References

* [charlow-2018]
* [heim-kratzer-1998]
* [jacobson-1999]
* [mcbride-paterson-2008]
-/

@[expose] public section

namespace Charlow2018

open Montague
open scoped Assignment

variable {E : Type}

/-! ### Abstraction under the standard theory

The standard rule interprets a branching node by giving both daughters the same assignment,
`⟦α β⟧ := λg. ⟦α⟧ g (⟦β⟧ g)` (6). Binding needs the sister of `Λᵢ` evaluated at shifted
assignments, which the rule never supplies. -/

/-- No denotation for `Λᵢ` binds under the standard rule (section 2.2), since whatever `L` is,
`λg. L g (⟦α⟧ g)` sees `⟦α⟧` only at `g`, while binding needs `λg. λx. ⟦α⟧ g^{i→x}`. -/
theorem not_exists_abstraction_denotation [Nontrivial E] (i : ℕ) :
    ¬ ∃ L : Assignment E → Prop → E → Prop,
      ∀ α : Assignment E → Prop, (fun g ↦ L g (α g)) = lambdaAbsG i α := by
  rintro ⟨L, hL⟩
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  have h₁ := congrFun (congrFun (hL fun g ↦ g i = a) fun _ ↦ a) b
  have h₂ := congrFun (congrFun (hL fun _ ↦ True) fun _ ↦ a) b
  simp only [lambdaAbsG, Function.update_self, eq_self] at h₁ h₂
  exact hab (of_eq_true (h₁.symm.trans h₂)).symm

/-! ### The reader applicative

The lift `ρ` (11) and application `⊛` (12) are the `pure` and `<*>` of the reader monad, and the
four laws of section 3.3 are its `LawfulApplicative` instance. Abstraction is the operation
`Λᵢ f := λg. λx. f g^{i→x}` (13), `lambdaAbsG`. -/

example {α : Type} (x : α) : (pure x : ReaderM (Assignment E) α) = fun _ ↦ x := rfl

example {α β : Type} (m : ReaderM (Assignment E) (α → β)) (n : ReaderM (Assignment E) α) :
    m <*> n = fun g ↦ m g (n g) := rfl

example : LawfulApplicative (ReaderM (Assignment E)) := inferInstance

/-- *She₀ left* and *John saw her₀* (Fig. 3). -/
example (left : E → Prop) :
    (pure left <*> Function.eval 0 : ReaderM (Assignment E) Prop) = fun g ↦ left (g 0) := rfl

example (saw : E → E → Prop) (j : E) :
    (pure saw <*> Function.eval 0 <*> pure j : ReaderM (Assignment E) Prop) =
      fun g ↦ saw (g 0) j := rfl

/-- *Bill Λ₀ t₀ left* and *everyone Λ₀ t₀ likes their₀ mom* (Fig. 4). -/
example (left : E → Prop) (b : E) :
    (lambdaAbsG 0 (pure left <*> Function.eval 0 : ReaderM (Assignment E) Prop) <*> pure b :
      ReaderM (Assignment E) Prop) = fun _ ↦ left b := by
  funext g
  exact congrArg left (Function.update_self ..)

example (likes : E → E → Prop) (mom : E → E) (everyone : (E → Prop) → Prop) :
    (pure everyone <*> lambdaAbsG 0
        (pure likes <*> (pure mom <*> Function.eval 0) <*> Function.eval 0 :
          ReaderM (Assignment E) Prop) : ReaderM (Assignment E) Prop) =
      fun _ ↦ everyone fun x ↦ likes (mom x) x := by
  funext g
  show everyone (fun x ↦ likes (mom ((g[0 ↦ x]) 0)) ((g[0 ↦ x]) 0)) = _
  simp only [Function.update_self]

/-! ### Applicatives elsewhere in semantics -/

section Applicatives

variable {α β : Type}

/-- Hamblin's `ρ x := {x}` (14) and pointwise application `{f x | f ∈ m, x ∈ n}` (15). -/
example (x : α) : (pure x : Set α) = {x} := rfl

example (m : Set (α → β)) (n : Set α) : m <*> n = {b | ∃ f ∈ m, ∃ x ∈ n, f x = b} := by
  ext b
  simp only [Set.seq_eq_set_seq, Set.mem_seq_iff, Set.mem_ofPred_eq]

/-- The continuation combinators of Shan and Barker (16), (17). -/
example {R : Type} (x : α) : (pure x : Cont R α) = fun κ ↦ κ x := rfl

example {R : Type} (m : Cont R (α → β)) (n : Cont R α) :
    m <*> n = fun κ ↦ m fun f ↦ n fun x ↦ κ (f x) := rfl

/-- Applicatives compose (Fig. 5). -/
example {F G : Type → Type} [Applicative F] [LawfulApplicative F] [Applicative G]
    [LawfulApplicative G] : LawfulApplicative (Functor.Comp F G) := inferInstance

/-- The reader composed with itself has `ρ x = λg. λh. x` and `m ⊛ n = λg. λh. m g h (n g h)`. -/
example {E₁ E₂ : Type} (x : α) :
    (pure x : Functor.Comp (ReaderM E₁) (ReaderM E₂) α).run = fun _ _ ↦ x := rfl

example {E₁ E₂ : Type} (m : Functor.Comp (ReaderM E₁) (ReaderM E₂) (α → β))
    (n : Functor.Comp (ReaderM E₁) (ReaderM E₂) α) :
    (m <*> n).run = fun g h ↦ m.run g h (n.run g h) := rfl

end Applicatives

/-! ### The flattener

A pronoun whose value is an intension has type `g → g → e` (18). The flattener `μ m := λg. m g g`
(19) is the reader monad's `joinM`. Section 4.3 states the monad laws with `ρ`, `⊛` and `μ`:
associativity `μ ∘ μ = λm. μ (ρ μ ⊛ m)` and identity `μ ∘ ρ = λm. μ (ρ ρ ⊛ m) = λm. m`. They
hold in every lawful monad. -/

example {α : Type} (m : ReaderM (Assignment E) (ReaderM (Assignment E) α)) :
    joinM m = fun g ↦ m g g := rfl

section MonadLaws

variable {M : Type → Type} [Monad M] [LawfulMonad M] {α : Type}

example (m : M (M (M α))) : joinM (joinM m) = joinM (pure joinM <*> m) := by
  rw [pure_seq, joinM_map_joinM]

example (m : M α) : joinM (pure m) = m := joinM_pure m

example (m : M α) : joinM (pure pure <*> m) = m := by rw [pure_seq, joinM_map_pure]

/-- The application of a monad is `m ⊛ n = μ (ρ (λf. ρ f ⊛ n) ⊛ m)`. -/
example {β : Type} (m : M (α → β)) (n : M α) : m <*> n = joinM ((· <$> n) <$> m) := by
  simp [joinM, seq_eq_bind_map]

end MonadLaws

/-! The laws do not relate `⊛` to `μ`. A log of bits paired with a value carries the writer's
flattener, which appends the inner log to the outer, and the writer's application run backwards,
which appends the function's log to the argument's, so that the monad the flattener determines
applies forwards. -/

/-- A value with a log of bits, applied backwards. -/
def BackwardsWriter (α : Type) : Type := List Bool × α

namespace BackwardsWriter

instance : Applicative BackwardsWriter where
  pure x := ([], x)
  map f x := (x.1, f x.2)
  seq f x := ((x ()).1 ++ f.1, f.2 (x ()).2)

instance : LawfulApplicative BackwardsWriter where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ x := Prod.ext x.1.append_nil rfl
  map_pure _ _ := rfl
  seq_pure _ _ := rfl
  seq_assoc _ _ _ := Prod.ext (List.append_assoc ..) rfl

/-- The writer's flattener, the outer log followed by the inner one. -/
def flatten {α : Type} (m : BackwardsWriter (BackwardsWriter α)) : BackwardsWriter α :=
  (m.1 ++ m.2.1, m.2.2)

example {α : Type} (m : BackwardsWriter (BackwardsWriter (BackwardsWriter α))) :
    flatten (flatten m) = flatten (pure flatten <*> m) :=
  Prod.ext (by simp [flatten, Seq.seq, pure]) rfl

example {α : Type} (m : BackwardsWriter α) : flatten (pure m) = m := rfl

example {α : Type} (m : BackwardsWriter α) : flatten (pure pure <*> m) = m :=
  Prod.ext (by simp [flatten, Seq.seq, pure]) rfl

-- Erratum: the laws of section 4.3 leave `⊛` free of `μ`.
theorem exists_seq_ne :
    ∃ (m : BackwardsWriter (Unit → Unit)) (n : BackwardsWriter Unit),
      m <*> n ≠ flatten ((· <$> n) <$> m) :=
  ⟨([true], id), ([false], ()), fun h ↦ by
    simpa [Seq.seq, Functor.map, flatten] using congrArg Prod.fst h⟩

end BackwardsWriter

/-! ### Higher-order variables

For the analyses of section 4 an assignment values both individual variables and variables over
individual concepts. Here `G` is a type of assignments, `ind i` and `con i` look up variable `i`
of each sort, and `shift i x` and `shiftCon i n` are the shifted assignments `g^{i→x}`. -/

section HigherOrder

variable {G : Type} (ind : ℕ → ReaderM G E) (con : ℕ → ReaderM G (ReaderM G E))

/-- Abstraction `Λᵢ f := λg. λx. f g^{i→x}` (13), given the shift `x ↦ g^{i→x}`. -/
def abstraction {α β : Type} (shift : α → G → G) (f : ReaderM G β) : ReaderM G (α → β) :=
  fun g x ↦ f (shift x g)

example {α : Type} (i : ℕ) (f : ReaderM (Assignment E) α) :
    abstraction (fun x g ↦ g[i ↦ x]) f = lambdaAbsG i f := rfl

variable (shift : ℕ → E → G → G) (shiftCon : ℕ → ReaderM G E → G → G)

/-- In the paycheck reading (Fig. 6), if variable 1 holds the intension of *his₀ mom*, *Bill likes
her₁* says Bill likes Bill's mom. `hcon` is the equivalence of footnote 5. -/
theorem paycheck (likes : E → E → Prop) (mom : E → E) (b : E) (g : G)
    (hg : con 1 g = pure mom <*> ind 0)
    (hcon : ∀ x g, con 1 (shift 0 x g) = con 1 g) (hind : ∀ x g, ind 0 (shift 0 x g) = x) :
    (abstraction (shift 0) (pure likes <*> joinM (con 1) <*> ind 0) <*> pure b) g =
      likes (mom b) b := by
  show likes (con 1 (shift 0 b g) (shift 0 b g)) (ind 0 (shift 0 b g)) = _
  rw [hcon, hg, hind]
  exact congrArg (likes · b) (congrArg mom (hind b g))

/-- In binding reconstruction (Fig. 7), *[his₀ mom] Λ₁ every boy Λ₀ t₀ likes t₁* says every boy
likes his own mom. -/
theorem reconstruction (likes : E → E → Prop) (mom : E → E) (everyBoy : (E → Prop) → Prop)
    (g : G) (hstore : ∀ g, con 1 (shiftCon 1 (pure mom <*> ind 0) g) = pure mom <*> ind 0)
    (hcon : ∀ x g, con 1 (shift 0 x g) = con 1 g) (hind : ∀ x g, ind 0 (shift 0 x g) = x) :
    (abstraction (shiftCon 1)
        (pure everyBoy <*> abstraction (shift 0) (pure likes <*> joinM (con 1) <*> ind 0)) <*>
      pure (pure mom <*> ind 0)) g = everyBoy fun x ↦ likes (mom x) x := by
  show everyBoy (fun x ↦
    likes (con 1 (shift 0 x (shiftCon 1 (pure mom <*> ind 0) g))
      (shift 0 x (shiftCon 1 (pure mom <*> ind 0) g)))
      (ind 0 (shift 0 x (shiftCon 1 (pure mom <*> ind 0) g)))) = _
  simp only [hcon, hstore, hind]
  exact congrArg everyBoy (funext fun x ↦ congrArg (likes · x) (congrArg mom (hind x _)))

/-- The laws `reconstruction` assumes are satisfiable over any domain, by assignments of
individuals whose variable 1 constantly holds the intension of *his₀ mom*. -/
example (mom : E → E) :
    ∃ (G : Type) (ind : ℕ → ReaderM G E) (con : ℕ → ReaderM G (ReaderM G E))
      (shift : ℕ → E → G → G) (shiftCon : ℕ → ReaderM G E → G → G),
      (∀ g, con 1 (shiftCon 1 (pure mom <*> ind 0) g) = pure mom <*> ind 0) ∧
      (∀ x g, con 1 (shift 0 x g) = con 1 g) ∧ ∀ x g, ind 0 (shift 0 x g) = x :=
  ⟨Assignment E, Function.eval,
    fun _ _ ↦ (pure mom <*> Function.eval 0 : ReaderM (Assignment E) E),
    fun i x g ↦ g[i ↦ x], fun _ _ g ↦ g, fun _ ↦ rfl, fun _ _ ↦ rfl,
    fun _ _ ↦ by simp only [Function.eval, Function.update_self]⟩

-- Storing every intension, `con i (shiftCon i n g) = n` for all `n`, makes the lookup `con i` a
-- surjection from `G` onto `G → E`. By Lawvere's fixed-point theorem every function on `E` then
-- has a fixed point, which swapping two individuals does not. This is why the laws above store
-- only the intension a derivation needs, and an obstruction of the kind section 5.1 cites.
theorem subsingleton_of_surjective {i : ℕ} (h : Function.Surjective (con i)) :
    Subsingleton E := by
  classical
  refine ⟨fun a b ↦ by_contra fun hab ↦ ?_⟩
  obtain ⟨x, hx⟩ := Function.exists_fixed_point_of_surjective _ h fun x ↦ if x = a then b else a
  split_ifs at hx with hxa
  exacts [hab (hx.trans hxa).symm, hxa hx.symm]

end HigherOrder

/-! ### Type-homogeneous assignments

Section 5 gives each type `r` its own assignments, `g_r := ℕ → r`, which is `Assignment r`. A
meaning that depends on assignments of two sorts lives in the composite of two reader
applicatives. -/

section TypeHomogeneous

/-- In *…and buy the couch Λ₀ she₁ did t₀* (20), a pronoun over individuals and a trace over
properties give `λg. λh. h₀ g₁`. -/
example :
    (Functor.Comp.mk (fun _ h ↦ h 0) <*> Functor.Comp.mk (fun g _ ↦ g 1) :
      Functor.Comp (ReaderM (Assignment E)) (ReaderM (Assignment (E → Prop))) Prop).run =
      fun g h ↦ h 0 (g 1) := rfl

/-- The meanings that depend on an assignment of individual concepts and then on one of
individuals, the composite `G_{G_e e} ∘ G_e` of section 5.2. -/
abbrev ConceptThenIndividual (E : Type) : Type → Type :=
  Functor.Comp (ReaderM (Assignment (Assignment E → E))) (ReaderM (Assignment E))

/-- On type-homogeneous assignments (section 5.2) the paycheck reading has `her₁` read an
intension from the outer assignment and evaluate it at the inner one, with `Λ₀` binding the
subject's trace in the inner layer. The meaning is `λg. λh. likes (g₁ h^{0→b}) b`, with no
flattener. -/
theorem typed_paycheck (likes : E → E → Prop) (mom : E → E) (b : E)
    (g : Assignment (Assignment E → E)) (h : Assignment E) (hg : g 1 = fun h ↦ mom (h 0)) :
    (Functor.Comp.mk (lambdaAbsG 0 <$> (pure likes <*>
          (Functor.Comp.mk fun g h ↦ g 1 h : ConceptThenIndividual E E) <*>
          (Functor.Comp.mk fun _ h ↦ h 0 : ConceptThenIndividual E E)).run) <*> pure b :
      ConceptThenIndividual E Prop).run g h = likes (mom b) b := by
  show likes (g 1 (h[0 ↦ b])) ((h[0 ↦ b]) 0) = _
  simp only [hg, Function.update_self]

end TypeHomogeneous

/-! ### Variable-free pronouns

A variable-free pronoun is the identity `λx. x` (Fig. 8), composed with the same `ρ` and `⊛` at
the entity type (section 6). A sentence with two pronouns lives in the reader at the entity type
composed with itself, and depends on two individuals as a variable-full meaning depends on two
variables of an assignment. -/

/-- *She left*. -/
example (left : E → Prop) : (pure left <*> (fun x ↦ x) : ReaderM E Prop) = left := rfl

/-- *She saw her* is `λx. λy. saw y x`. -/
example (saw : E → E → Prop) :
    (pure saw <*> Functor.Comp.mk (fun _ y ↦ y) <*> Functor.Comp.mk (fun x _ ↦ x) :
      Functor.Comp (ReaderM E) (ReaderM E) Prop).run = fun x y ↦ saw y x := rfl

/-- A variable-free meaning that depends on two individuals, read as the variable-full meaning
whose variable 0 is the outer individual and variable 1 the inner one. It preserves `ρ` and `⊛`,
so it maps each variable-free derivation to the variable-full derivation with the same lexical
items. -/
def toAssignment : ApplicativeTransformation (Functor.Comp (ReaderM E) (ReaderM E))
    (ReaderM (Assignment E)) where
  app _ m g := m.run (g 0) (g 1)
  preserves_pure' _ := rfl
  preserves_seq' _ _ := rfl

/-- *She saw her* read variable-full is *she₀ saw her₁*. -/
example (saw : E → E → Prop) :
    toAssignment (pure saw <*> Functor.Comp.mk (fun _ y ↦ y) <*> Functor.Comp.mk (fun x _ ↦ x)) =
      (pure saw <*> Function.eval 1 <*> Function.eval 0 : ReaderM (Assignment E) Prop) := rfl

/-- Variable-free and variable-full semantics generate the same meanings up to isomorphism
(section 6): reading a variable-free meaning's two individuals as variables 0 and 1 is a bijection
onto the variable-full meanings that read no other variable. -/
theorem bijOn_toAssignment {α : Type} :
    Set.BijOn ((toAssignment (E := E)).app α) Set.univ {m | DependsOn m {0, 1}} := by
  refine ⟨fun m _ g g' h ↦ ?_, fun m _ m' _ h ↦ ?_, fun m hm ↦ ?_⟩
  · show m.run (g 0) (g 1) = m.run (g' 0) (g' 1)
    rw [h 0 (by simp), h 1 (by simp)]
  · refine Functor.Comp.ext (funext fun x ↦ funext fun y ↦ ?_)
    simpa [toAssignment] using congrFun h ((fun _ ↦ y)[0 ↦ x])
  · refine ⟨Functor.Comp.mk fun x y ↦ m ((fun _ ↦ y)[0 ↦ x]), trivial, funext fun g ↦ hm ?_⟩
    rintro i (rfl | rfl) <;> simp

end Charlow2018
