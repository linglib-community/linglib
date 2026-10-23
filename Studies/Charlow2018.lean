module

public import Linglib.Semantics.Composition.Assignment
public import Mathlib.Control.Applicative
public import Mathlib.Control.Basic
public import Mathlib.Control.Monad.Cont
public import Mathlib.Data.Set.Functor

/-!
# Charlow 2018: a modular theory of pronouns and binding

The standard theory of pronouns, Heim and Kratzer's, makes every meaning depend on an assignment
and composes by handing one assignment to both daughters. Charlow factors this into two
operations: a lift `ρ x := λg. x` for meanings that do not depend on the assignment, and
an application `m ⊛ n := λg. m g (n g)` used only where it is needed. Together they make
assignment-dependent meanings an applicative functor. A flattener `μ m := λg. m g g` for pronouns
whose value is an intension then makes them a monad. These are the `pure`, `<*>` and `joinM` of
Lean's reader monad, so the laws the paper lists are the reader monad's own. Abstraction becomes
an ordinary operation on meanings where the standard rule can only have it as a special rule, and
paycheck pronouns and binding reconstruction follow from pronouns whose values are intensions.

Those analyses store intensions in assignments. Assignments that can store every intension exist
only over a one-element domain, by Cantor's diagonal argument. This is the difficulty the paper
cites in section 5, whose type-homogeneous assignments avoid it: two composed reader applicatives
derive the paycheck reading with no flattener. The pronouns of Jacobson's variable-free
semantics use the same applicative at the entity type.

## Main results

* `not_exists_abstraction_denotation`: under the standard rule no denotation of `Λᵢ` binds
* `hamblin_seq`: Hamblin's pointwise application is the `<*>` of sets
* `joinM_joinM`, `joinM_pure_seq_pure`: the monad laws in the paper's form
* `paycheck`, `reconstruction`: the paycheck reading and binding reconstruction
* `subsingleton_of_forall_store`: assignments storing every intension are trivial
* `typed_paycheck`: the paycheck reading on type-homogeneous assignments

## Implementation notes

`ρ`, `⊛` and `μ` are not defined here: they are `pure`, `<*>` and `joinM` of
`ReaderM (Assignment E)`, and the composition of two applicatives (Fig. 5) is mathlib's
`Functor.Comp`. For section 4, `G` is an abstract type of assignments with lookups for individual
variables and for variables over individual concepts, and a shift `g^{i→x}` for each; each
derivation assumes only the laws it uses, for the one intension it stores. As in the paper,
`likes x y` is "`y` likes `x`".

## TODO

* Section 4.3: composing sets with the reader (`S ∘ G`) admits no lawful flattener.

## References

* [charlow-2018]
* [heim-kratzer-1998]
* [jacobson-1999]
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
      ∀ α : Assignment E → Prop, (fun g => L g (α g)) = lambdaAbsG i α := by
  rintro ⟨L, hL⟩
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  have h₁ := congrFun (congrFun (hL fun g => g i = a) fun _ => a) b
  have h₂ := congrFun (congrFun (hL fun _ => True) fun _ => a) b
  simp only [lambdaAbsG, Function.update_self, eq_self] at h₁ h₂
  exact hab (of_eq_true (h₁.symm.trans h₂)).symm

/-! ### The reader applicative

The lift `ρ` (11) and application `⊛` (12) are the `pure` and `<*>` of the reader monad, and the
four laws of section 3.3 are its `LawfulApplicative` instance. Abstraction is the operation
`Λᵢ f := λg. λx. f g^{i→x}` (13), `lambdaAbsG`. -/

example {α : Type} (x : α) : (pure x : ReaderM (Assignment E) α) = fun _ => x := rfl

example {α β : Type} (m : ReaderM (Assignment E) (α → β)) (n : ReaderM (Assignment E) α) :
    m <*> n = fun g => m g (n g) := rfl

example : LawfulApplicative (ReaderM (Assignment E)) := inferInstance

/-- *She₀ left* and *John saw her₀* (Fig. 3). -/
example (left : E → Prop) :
    (pure left <*> Function.eval 0 : ReaderM (Assignment E) Prop) = fun g => left (g 0) := rfl

example (saw : E → E → Prop) (j : E) :
    (pure saw <*> Function.eval 0 <*> pure j : ReaderM (Assignment E) Prop) =
      fun g => saw (g 0) j := rfl

/-- *Bill Λ₀ t₀ left* and *everyone Λ₀ t₀ likes their₀ mom* (Fig. 4). -/
example (left : E → Prop) (b : E) :
    (lambdaAbsG 0 (pure left <*> Function.eval 0 : ReaderM (Assignment E) Prop) <*> pure b :
      ReaderM (Assignment E) Prop) = fun _ => left b := by
  funext g
  exact congrArg left (Function.update_self ..)

example (likes : E → E → Prop) (mom : E → E) (everyone : (E → Prop) → Prop) :
    (pure everyone <*> lambdaAbsG 0
        (pure likes <*> (pure mom <*> Function.eval 0) <*> Function.eval 0 :
          ReaderM (Assignment E) Prop) : ReaderM (Assignment E) Prop) =
      fun _ => everyone fun x => likes (mom x) x := by
  funext g
  show everyone (fun x => likes (mom ((g[0 ↦ x]) 0)) ((g[0 ↦ x]) 0)) = _
  simp only [Function.update_self]

/-! ### Applicatives elsewhere in semantics -/

section Applicatives

variable {α β : Type}

/-- Hamblin's pointwise application `{f x | f ∈ m, x ∈ n}` (15) is the `<*>` of sets. -/
theorem hamblin_seq (m : Set (α → β)) (n : Set α) :
    m <*> n = {b | ∃ f ∈ m, ∃ x ∈ n, f x = b} := by
  ext b
  simp only [Set.seq_eq_set_seq, Set.mem_seq_iff, Set.mem_ofPred_eq]

/-- Hamblin's `ρ x := {x}` (14). -/
example (x : α) : (pure x : Set α) = {x} := rfl

/-- The continuation combinators of Shan and Barker (16), (17). -/
example {R : Type} (x : α) : (pure x : Cont R α) = fun κ => κ x := rfl

example {R : Type} (m : Cont R (α → β)) (n : Cont R α) :
    m <*> n = fun κ => m fun f => n fun x => κ (f x) := rfl

/-- Applicatives compose (Fig. 5). -/
example {F G : Type → Type} [Applicative F] [LawfulApplicative F] [Applicative G]
    [LawfulApplicative G] : LawfulApplicative (Functor.Comp F G) := inferInstance

/-- The reader composed with itself has `ρ x = λg. λh. x` and `m ⊛ n = λg. λh. m g h (n g h)`. -/
example {E₁ E₂ : Type} (x : α) :
    (pure x : Functor.Comp (ReaderM E₁) (ReaderM E₂) α).run = fun _ _ => x := rfl

example {E₁ E₂ : Type} (m : Functor.Comp (ReaderM E₁) (ReaderM E₂) (α → β))
    (n : Functor.Comp (ReaderM E₁) (ReaderM E₂) α) :
    (m <*> n).run = fun g h => m.run g h (n.run g h) := rfl

end Applicatives

/-! ### The flattener

A pronoun whose value is an intension has type `g → g → e` (18). The flattener `μ m := λg. m g g`
(19) is the reader monad's `joinM`. Section 4.3 states the monad laws with `ρ`, `⊛` and `μ`; they
hold in every lawful monad. -/

example {α : Type} (m : ReaderM (Assignment E) (ReaderM (Assignment E) α)) :
    joinM m = fun g => m g g := rfl

section MonadLaws

variable {M : Type → Type} [Monad M] [LawfulMonad M] {α : Type}

/-- The flattener is associative, `μ ∘ μ = λm. μ (ρ μ ⊛ m)`. -/
theorem joinM_joinM (m : M (M (M α))) : joinM (joinM m) = joinM (pure joinM <*> m) := by
  rw [pure_seq, joinM_map_joinM]

/-- Flattening undoes the inner lift, `λm. μ (ρ ρ ⊛ m) = λm. m`; the other half of the identity
law, `μ ∘ ρ = id`, is `joinM_pure`. -/
theorem joinM_pure_seq_pure (m : M α) : joinM (pure pure <*> m) = m := by
  rw [pure_seq, joinM_map_pure]

end MonadLaws

/-! ### Higher-order variables

For the analyses of section 4 an assignment values both individual variables and variables over
individual concepts. Here `G` is a type of assignments, `ind i` and `con i` look up variable `i`
of each sort, and `shift i x` and `shiftCon i n` are the shifted assignments `g^{i→x}`. -/

section HigherOrder

variable {G : Type} (ind : ℕ → ReaderM G E) (con : ℕ → ReaderM G (ReaderM G E))

/-- Abstraction `Λᵢ f := λg. λx. f g^{i→x}` (13), given the shift `x ↦ g^{i→x}`. -/
def abstraction {α β : Type} (shift : α → G → G) (f : ReaderM G β) : ReaderM G (α → β) :=
  fun g x => f (shift x g)

example {α : Type} (i : ℕ) (f : ReaderM (Assignment E) α) :
    abstraction (fun x g => g[i ↦ x]) f = lambdaAbsG i f := rfl

variable (shift : ℕ → E → G → G) (shiftCon : ℕ → ReaderM G E → G → G)

/-- In the paycheck reading (Fig. 6), if variable 1 holds the intension of *his₀ mom*, *Bill likes
her₁* says Bill likes Bill's mom. -/
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
      pure (pure mom <*> ind 0)) g = everyBoy fun x => likes (mom x) x := by
  show everyBoy (fun x =>
    likes (con 1 (shift 0 x (shiftCon 1 (pure mom <*> ind 0) g))
      (shift 0 x (shiftCon 1 (pure mom <*> ind 0) g)))
      (ind 0 (shift 0 x (shiftCon 1 (pure mom <*> ind 0) g)))) = _
  simp only [hcon, hstore, hind]
  exact congrArg everyBoy (funext fun x => congrArg (likes · x) (congrArg mom (hind x _)))

/-- The laws `reconstruction` assumes are satisfiable over any domain, by assignments of
individuals whose variable 1 constantly holds the intension of *his₀ mom*. -/
example (mom : E → E) :
    ∃ (G : Type) (ind : ℕ → ReaderM G E) (con : ℕ → ReaderM G (ReaderM G E))
      (shift : ℕ → E → G → G) (shiftCon : ℕ → ReaderM G E → G → G),
      (∀ g, con 1 (shiftCon 1 (pure mom <*> ind 0) g) = pure mom <*> ind 0) ∧
      (∀ x g, con 1 (shift 0 x g) = con 1 g) ∧ ∀ x g, ind 0 (shift 0 x g) = x :=
  ⟨Assignment E, Function.eval,
    fun _ _ => (pure mom <*> Function.eval 0 : ReaderM (Assignment E) E),
    fun i x g => g[i ↦ x], fun _ _ g => g, fun _ => rfl, fun _ _ => rfl,
    fun _ _ => by simp only [Function.eval, Function.update_self]⟩

/-- Assignments that can store every intension exist only over a one-element domain. Storing
makes the lookup `con i` a surjection from `G` onto `G → E`, which Cantor's diagonal argument
rules out once `E` has two elements. This is why the laws above store only the intension a
derivation needs, and the difficulty section 5.1 cites for such assignments. -/
theorem subsingleton_of_forall_store [Nonempty G] (i : ℕ)
    (h : ∀ n g, con i (shiftCon i n g) = n) : Subsingleton E := by
  classical
  refine ⟨fun a b => by_contra fun hab => ?_⟩
  obtain ⟨g₀⟩ := ‹Nonempty G›
  let d : ReaderM G E := fun g => if con i g g = a then b else a
  have hd := congrFun (h d g₀) (shiftCon i d g₀)
  simp only [d] at hd
  split_ifs at hd with h'
  exacts [hab (h'.symm.trans hd), h' hd]

end HigherOrder

/-! ### Type-homogeneous assignments

Section 5 gives each type `r` its own assignments, `g_r := ℕ → r`, which is `Assignment r`. A
meaning that depends on assignments of two sorts lives in the composite of two reader
applicatives. -/

section TypeHomogeneous

/-- In *…and buy the couch Λ₀ she₁ did t₀* (20), a pronoun over individuals and a trace over
properties give `λg. λh. h₀ g₁`. -/
example :
    (Functor.Comp.mk (fun _ h => h 0) <*> Functor.Comp.mk (fun g _ => g 1) :
      Functor.Comp (ReaderM (Assignment E)) (ReaderM (Assignment (E → Prop))) Prop).run =
      fun g h => h 0 (g 1) := rfl

/-- The meanings that depend on an assignment of individual concepts and then on one of
individuals, the composite `G_{G_e e} ∘ G_e` of section 5.2. -/
abbrev ConceptThenIndividual (E : Type) : Type → Type :=
  Functor.Comp (ReaderM (Assignment (Assignment E → E))) (ReaderM (Assignment E))

/-- On type-homogeneous assignments (section 5.2) the paycheck reading has `her₁` read an
intension from the outer assignment and evaluate it at the inner one, with `Λ₀` binding the
subject's trace in the inner layer. The meaning is `λg. λh. likes (g₁ h^{0→b}) b`, with no
flattener. -/
theorem typed_paycheck (likes : E → E → Prop) (mom : E → E) (b : E)
    (g : Assignment (Assignment E → E)) (h : Assignment E) (hg : g 1 = fun h => mom (h 0)) :
    (Functor.Comp.mk (lambdaAbsG 0 <$> (pure likes <*>
          (Functor.Comp.mk fun g h => g 1 h : ConceptThenIndividual E E) <*>
          (Functor.Comp.mk fun _ h => h 0 : ConceptThenIndividual E E)).run) <*> pure b :
      ConceptThenIndividual E Prop).run g h = likes (mom b) b := by
  show likes (g 1 (h[0 ↦ b])) ((h[0 ↦ b]) 0) = _
  simp only [hg, Function.update_self]

end TypeHomogeneous

/-! ### Variable-free pronouns

A variable-free pronoun is the identity `λx. x` (Fig. 8), composed with the same `ρ` and `⊛` at
the entity type (section 6). -/

/-- *She left*. -/
example (left : E → Prop) : (pure left <*> (fun x => x) : ReaderM E Prop) = left := rfl

/-- *She saw her* in the variable-free applicative composed with itself is `λx. λy. saw y x`, and
uncurried it depends on a pair of individuals, as a meaning depends on an assignment. -/
example (saw : E → E → Prop) :
    (pure saw <*> Functor.Comp.mk (fun _ y => y) <*> Functor.Comp.mk (fun x _ => x) :
      Functor.Comp (ReaderM E) (ReaderM E) Prop).run = fun x y => saw y x := rfl

example (saw : E → E → Prop) :
    Function.uncurry (pure saw <*> Functor.Comp.mk (fun _ y => y) <*>
      Functor.Comp.mk (fun x _ => x) : Functor.Comp (ReaderM E) (ReaderM E) Prop).run =
      fun p => saw p.2 p.1 := rfl

end Charlow2018
