module

public import Linglib.Logic.Natural.Basic
public import Linglib.Logic.Natural.Additivity
public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.Order.Hom.BoundedLattice
public import Mathlib.Order.Hom.Set

/-!
# Soundness of the projectivity calculus

This file gives the seven relations their lattice content and proves the calculus of
`Logic/Natural/Basic.lean` sound for it over bounded lattices. The join and the projections are
sound because they assert only what the atom and property rules give, and each rule is a lattice
fact about single constraints or properties. A signature's projection row holds of a map exactly
when the map is monotone or antitone and carries disjoint and codisjoint pairs as the row says,
and [every map in the class of a signature](##NaturalLogic.Signature.soundFor_of_holdsFor) falls
in its row, as do bounded lattice homomorphisms and, into the order dual, complementation.

## Implementation notes

* Icard works over Boolean algebras; the proofs need only bounded lattices, and distributivity
  for the join rule taking a disjoint pair and a codisjoint pair to `≤`.

## References

* [icard-2012] — Definitions 1.2 and 2.3, Lemmas 1.6 and 2.5.
-/

@[expose] public section

namespace NaturalLogic


/-! ### Lattice content of the relations -/

/-- The lattice content of a natural-logic relation ([icard-2012]
Definition 1.2), in mathlib's complementation vocabulary: `negation` is
`IsCompl`, `alternation` is `Disjoint`, `cover` is `Codisjoint`; `forward`
is non-strict `≤` (MacCartney's exclusive reading takes it proper, which
the projectivity tables do not need). -/
def Relation.Holds {α : Type*} [Lattice α] [BoundedOrder α] :
    Relation → α → α → Prop
  | .equiv => (· = ·)
  | .forward => (· ≤ ·)
  | .reverse => (· ≥ ·)
  | .negation => IsCompl
  | .alternation => Disjoint
  | .cover => Codisjoint
  | .independent => fun _ _ => True

/-- The lattice content of an atomic constraint ([icard-2012]
Definition 1.2). -/
def Relation.Atom.Holds {α : Type*} [Lattice α] [BoundedOrder α] :
    Relation.Atom → α → α → Prop
  | .le => (· ≤ ·)
  | .ge => (· ≥ ·)
  | .disjoint => Disjoint
  | .codisjoint => Codisjoint

theorem Relation.holds_iff {α : Type*} [Lattice α] [BoundedOrder α]
    {R : Relation} {x y : α} :
    R.Holds x y ↔ ∀ a ∈ R.constraints, a.Holds x y := by
  cases R <;>
    simp [Relation.Holds, Relation.Atom.Holds, Relation.constraints,
      isCompl_iff, le_antisymm_iff]

instance Relation.Atom.decidableHolds {α : Type*} [Lattice α] [BoundedOrder α]
    [DecidableEq α] [DecidableLE α] :
    ∀ (a : Relation.Atom) (x y : α), Decidable (a.Holds x y)
  | .le, x, y => inferInstanceAs (Decidable (x ≤ y))
  | .ge, x, y => inferInstanceAs (Decidable (y ≤ x))
  | .disjoint, x, y => decidable_of_iff (x ⊓ y = ⊥) disjoint_iff.symm
  | .codisjoint, x, y => decidable_of_iff (x ⊔ y = ⊤) codisjoint_iff.symm

instance Relation.decidableHolds {α : Type*} [Lattice α] [BoundedOrder α]
    [DecidableEq α] [DecidableLE α] :
    ∀ (R : Relation) (x y : α), Decidable (R.Holds x y)
  | .equiv, x, y => inferInstanceAs (Decidable (x = y))
  | .forward, x, y => inferInstanceAs (Decidable (x ≤ y))
  | .reverse, x, y => inferInstanceAs (Decidable (y ≤ x))
  | .negation, x, y =>
      decidable_of_iff (x ⊓ y = ⊥ ∧ x ⊔ y = ⊤)
        (by rw [← disjoint_iff, ← codisjoint_iff]; exact isCompl_iff.symm)
  | .alternation, x, y => decidable_of_iff (x ⊓ y = ⊥) disjoint_iff.symm
  | .cover, x, y => decidable_of_iff (x ⊔ y = ⊤) codisjoint_iff.symm
  | .independent, _, _ => .isTrue trivial

/-! ### Join soundness -/

/-- The atom rule is sound: chained constraints give the constraint `Relation.Atom.join` says.
Distributivity is needed for a disjoint pair followed by a codisjoint one, which gives `≤`. -/
theorem Relation.Atom.Holds.join {β : Type*} [DistribLattice β] [BoundedOrder β]
    {a b c : Relation.Atom} (h : a.join b = some c) {x y z : β} (ha : a.Holds x y)
    (hb : b.Holds y z) : c.Holds x z := by
  cases a <;> cases b <;> simp only [Relation.Atom.join, reduceCtorEq, Option.some.injEq] at h <;>
    subst h <;> simp only [Relation.Atom.Holds] at ha hb ⊢
  all_goals first
    | exact le_trans ha hb
    | exact ge_trans ha hb
    | exact hb.mono_left ha
    | exact ha.mono_right hb
    | exact ha.le_of_codisjoint hb
    | exact hb.symm.le_of_codisjoint ha.symm

/-- Chained relations compose as the join says, constraint by constraint. -/
theorem Relation.Holds.join {β : Type*} [DistribLattice β] [BoundedOrder β]
    {R S : Relation} {x y z : β} (hR : R.Holds x y) (hS : S.Holds y z) :
    (R * S).Holds x z :=
  Relation.holds_iff.2 fun _ hc ↦ by
    obtain ⟨a, ha, b, hb, h⟩ := Relation.mem_constraints_mul.1 hc
    exact Relation.Atom.Holds.join h (Relation.holds_iff.1 hR a ha) (Relation.holds_iff.1 hS b hb)

/-! ### Soundness of a signature for a function -/

section SoundFor

variable {α β γ : Type*} [Lattice α] [BoundedOrder α] [Lattice β]
  [BoundedOrder β] [Lattice γ] [BoundedOrder γ]

/-- A signature σ is **sound for** `f` when `f` projects every relation as
σ's row of the projection table says ([icard-2012] Lemma 2.5: every
φ-function projects `R` to `[R]^φ`). -/
def Signature.SoundFor (σ : Signature) (f : α → β) : Prop :=
  ∀ (R : Relation) (x y : α), R.Holds x y →
    (Signature.project R σ).Holds (f x) (f y)

theorem soundFor_mono_iff {f : α → β} :
    Signature.SoundFor .mono f ↔ Monotone f := by
  constructor
  · intro h x y hxy
    exact h .forward x y hxy
  · intro h R x y hR
    cases R with
    | equiv => exact congrArg f hR
    | forward => exact h hR
    | reverse => exact h hR
    | negation | alternation | cover | independent => trivial

theorem soundFor_anti_iff {f : α → β} :
    Signature.SoundFor .anti f ↔ Antitone f := by
  constructor
  · intro h x y hxy
    exact h .forward x y hxy
  · intro h R x y hR
    cases R with
    | equiv => exact congrArg f hR
    | forward => exact h hR
    | reverse => exact h hR
    | negation | alternation | cover | independent => trivial

theorem Signature.SoundFor.monotone {σ : Signature} {f : α → β} (h : σ.SoundFor f)
    (hσ : σ.sign = 1) : Monotone f := by
  intro x y hxy
  cases σ <;> first | exact h .forward x y hxy | exact absurd hσ (by decide)

theorem Signature.SoundFor.antitone {σ : Signature} {f : α → β} (h : σ.SoundFor f)
    (hσ : σ.sign = -1) : Antitone f := by
  intro x y hxy
  cases σ <;> first | exact h .forward x y hxy | exact absurd hσ (by decide)

/-- The `.additive` row is sound exactly for the monotone functions sending codisjoint pairs to
codisjoint pairs. -/
theorem soundFor_additive_iff {f : α → β} :
    Signature.SoundFor .additive f ↔
      Monotone f ∧ ∀ ⦃x y⦄, Codisjoint x y → Codisjoint (f x) (f y) := by
  refine ⟨fun h ↦ ⟨fun x y ↦ h .forward x y, fun x y ↦ h .cover x y⟩, fun ⟨hm, hc⟩ R x y hR ↦ ?_⟩
  cases R with
  | equiv => exact congrArg f hR
  | forward | reverse => exact hm hR
  | negation => exact hc hR.codisjoint
  | cover => exact hc hR
  | alternation | independent => trivial

theorem soundFor_mult_iff {f : α → β} :
    Signature.SoundFor .mult f ↔ Monotone f ∧ ∀ ⦃x y⦄, Disjoint x y → Disjoint (f x) (f y) := by
  refine ⟨fun h ↦ ⟨fun x y ↦ h .forward x y, fun x y ↦ h .alternation x y⟩,
    fun ⟨hm, hd⟩ R x y hR ↦ ?_⟩
  cases R with
  | equiv => exact congrArg f hR
  | forward | reverse => exact hm hR
  | negation => exact hd hR.disjoint
  | alternation => exact hd hR
  | cover | independent => trivial

theorem soundFor_antiAdd_iff {f : α → β} :
    Signature.SoundFor .antiAdd f ↔
      Antitone f ∧ ∀ ⦃x y⦄, Codisjoint x y → Disjoint (f x) (f y) := by
  refine ⟨fun h ↦ ⟨fun x y ↦ h .forward x y, fun x y ↦ h .cover x y⟩, fun ⟨ha, hc⟩ R x y hR ↦ ?_⟩
  cases R with
  | equiv => exact congrArg f hR
  | forward | reverse => exact ha hR
  | negation => exact hc hR.codisjoint
  | cover => exact hc hR
  | alternation | independent => trivial

theorem soundFor_antiMult_iff {f : α → β} :
    Signature.SoundFor .antiMult f ↔
      Antitone f ∧ ∀ ⦃x y⦄, Disjoint x y → Codisjoint (f x) (f y) := by
  refine ⟨fun h ↦ ⟨fun x y ↦ h .forward x y, fun x y ↦ h .alternation x y⟩,
    fun ⟨ha, hd⟩ R x y hR ↦ ?_⟩
  cases R with
  | equiv => exact congrArg f hR
  | forward | reverse => exact ha hR
  | negation => exact hd hR.disjoint
  | alternation => exact hd hR
  | cover | independent => trivial

theorem soundFor_addMult_iff {f : α → β} :
    Signature.SoundFor .addMult f ↔ Monotone f ∧
      (∀ ⦃x y⦄, Disjoint x y → Disjoint (f x) (f y)) ∧
        ∀ ⦃x y⦄, Codisjoint x y → Codisjoint (f x) (f y) := by
  refine ⟨fun h ↦ ⟨fun x y ↦ h .forward x y, fun x y ↦ h .alternation x y,
    fun x y ↦ h .cover x y⟩, fun ⟨hm, hd, hc⟩ R x y hR ↦ ?_⟩
  cases R with
  | equiv => exact congrArg f hR
  | forward | reverse => exact hm hR
  | negation => exact ⟨hd hR.disjoint, hc hR.codisjoint⟩
  | alternation => exact hd hR
  | cover => exact hc hR
  | independent => trivial

/-- The `.antiAddMult` row is sound exactly for the antitone functions exchanging disjointness
and codisjointness. -/
theorem soundFor_antiAddMult_iff {f : α → β} :
    Signature.SoundFor .antiAddMult f ↔ Antitone f ∧
      (∀ ⦃x y⦄, Disjoint x y → Codisjoint (f x) (f y)) ∧
        ∀ ⦃x y⦄, Codisjoint x y → Disjoint (f x) (f y) := by
  refine ⟨fun h ↦ ⟨fun x y ↦ h .forward x y, fun x y ↦ h .alternation x y,
    fun x y ↦ h .cover x y⟩, fun ⟨ha, hd, hc⟩ R x y hR ↦ ?_⟩
  cases R with
  | equiv => exact congrArg f hR
  | forward | reverse => exact ha hR
  | negation => exact ⟨hc hR.codisjoint, hd hR.disjoint⟩
  | alternation => exact hd hR
  | cover => exact hc hR
  | independent => trivial

private theorem codisjoint_map_of_map_sup {f : α → β}
    (h : (∀ p q, f (p ⊔ q) = f p ⊔ f q) ∧ f ⊤ = ⊤) {x y : α} (hxy : Codisjoint x y) :
    Codisjoint (f x) (f y) :=
  codisjoint_iff.2 (by rw [← h.1, hxy.eq_top, h.2])

private theorem disjoint_map_of_map_inf {f : α → β}
    (h : (∀ p q, f (p ⊓ q) = f p ⊓ f q) ∧ f ⊥ = ⊥) {x y : α} (hxy : Disjoint x y) :
    Disjoint (f x) (f y) :=
  disjoint_iff.2 (by rw [← h.1, hxy.eq_bot, h.2])

private theorem disjoint_map_of_isAntiAdditive {f : α → β} (h : IsAntiAdditive f ∧ f ⊤ = ⊥)
    {x y : α} (hxy : Codisjoint x y) : Disjoint (f x) (f y) :=
  disjoint_iff.2 (by rw [← h.1, hxy.eq_top, h.2])

private theorem codisjoint_map_of_isAntiMultiplicative {f : α → β}
    (h : IsAntiMultiplicative f ∧ f ⊥ = ⊤) {x y : α} (hxy : Disjoint x y) :
    Codisjoint (f x) (f y) :=
  codisjoint_iff.2 (by rw [← h.1, hxy.eq_bot, h.2])

theorem soundFor_addMult_of_boundedLatticeHomClass {F : Type*} [FunLike F α β]
    [BoundedLatticeHomClass F α β] (f : F) : Signature.SoundFor .addMult f :=
  soundFor_addMult_iff.2 ⟨OrderHomClass.mono f, fun _ _ h ↦ h.map f, fun _ _ h ↦ h.map f⟩

theorem soundFor_antiAddMult_of_boundedLatticeHomClass {F : Type*} [FunLike F α βᵒᵈ]
    [BoundedLatticeHomClass F α βᵒᵈ] (f : F) :
    Signature.SoundFor .antiAddMult (OrderDual.ofDual ∘ f) :=
  soundFor_antiAddMult_iff.2 ⟨fun _ _ h ↦ OrderHomClass.mono f h,
    fun _ _ h ↦ codisjoint_ofDual_iff.2 (h.map f), fun _ _ h ↦ disjoint_ofDual_iff.2 (h.map f)⟩

theorem soundFor_all (f : α → β) : Signature.SoundFor .all f := by
  intro R x y hR
  cases R
  case equiv => exact congrArg f hR
  all_goals trivial

/-- Relation-level order soundness: `≤` is the implication order on
the lattice content ([icard-2012] §1). -/
theorem _root_.NaturalLogic.Relation.Holds.of_le
    {R R' : Relation} {u v : β} (h : R.Holds u v) (href : R ≤ R') :
    R'.Holds u v := by
  cases R <;> cases R' <;>
    first
    | exact h
    | trivial
    | exact h.1
    | exact h.2
    | exact le_of_eq h
    | exact le_of_eq (Eq.symm h)

theorem _root_.NaturalLogic.Relation.Holds.apply {ι : Type*} {R : Relation} {f g : ι → β}
    (h : R.Holds f g) (i : ι) : R.Holds (f i) (g i) := by
  cases R with
  | equiv => exact congrFun h i
  | forward | reverse => exact h i
  | negation =>
    exact isCompl_iff.2 ⟨disjoint_iff.2 (congrFun (disjoint_iff.1 h.disjoint) i),
      codisjoint_iff.2 (congrFun (codisjoint_iff.1 h.codisjoint) i)⟩
  | alternation => exact disjoint_iff.2 (congrFun (disjoint_iff.1 h) i)
  | cover => exact codisjoint_iff.2 (congrFun (codisjoint_iff.1 h) i)
  | independent => trivial

theorem Signature.SoundFor.apply {ι : Type*} {σ : Signature} {f : α → ι → β}
    (h : σ.SoundFor f) (i : ι) : σ.SoundFor (f · i) :=
  fun R x y hR => (h R x y hR).apply i

theorem Signature.SoundFor.of_le {σ τ : Signature} {f : α → β}
    (h : σ.SoundFor f) (hστ : σ ≤ τ) : τ.SoundFor f :=
  fun R x y hR => (h R x y hR).of_le (Signature.project_mono R hστ)

/-! ### Composition and paths -/

/-- If ψ is sound for the outer function and φ for the inner one, `ψ * φ` is sound for the composite
([icard-2012] Lemma 2.7, Proposition 2.10). -/
theorem Signature.SoundFor.comp {ψ φ : Signature} {f : β → γ}
    {g : α → β} (hf : ψ.SoundFor f) (hg : φ.SoundFor g) :
    (ψ * φ).SoundFor (f ∘ g) := by
  intro R x y hR
  have h := hf (Signature.project R φ) (g x) (g y) (hg R x y hR)
  rwa [Signature.project_project] at h

theorem soundFor_addMult_id : Signature.SoundFor .addMult (id : α → α) :=
  soundFor_addMult_iff.2 ⟨monotone_id, fun _ _ h ↦ h, fun _ _ h ↦ h⟩

theorem Signature.project_forward_of_sign_eq_one {σ : Signature} (h : σ.sign = 1) :
    Signature.project .forward σ = .forward := by
  revert h; cases σ <;> decide

theorem Signature.project_forward_of_sign_eq_neg_one {σ : Signature} (h : σ.sign = -1) :
    Signature.project .forward σ = .reverse := by
  revert h; cases σ <;> decide

/-- A function a signature of positive sign is sound for is monotone. -/
theorem Signature.SoundFor.monotone_of_sign_eq_one {σ : Signature} {f : α → β}
    (hf : σ.SoundFor f) (h : σ.sign = 1) : Monotone f := fun x y hxy ↦ by
  simpa [Signature.project_forward_of_sign_eq_one h, Relation.Holds] using hf .forward x y hxy

/-- A function a signature of negative sign is sound for is antitone. -/
theorem Signature.SoundFor.antitone_of_sign_eq_neg_one {σ : Signature} {f : α → β}
    (hf : σ.SoundFor f) (h : σ.sign = -1) : Antitone f := fun x y hxy ↦ by
  simpa [Signature.project_forward_of_sign_eq_neg_one h, Relation.Holds] using hf .forward x y hxy

end SoundFor

/-! ### Complementation

Complementation in a Boolean algebra is completely anti-additive and anti-multiplicative, so the
anti-morphism row `⊖` is sound for it. -/

section ComplInstance

variable {α : Type*} [BooleanAlgebra α]

theorem compl_soundFor_antiAddMult :
    Signature.SoundFor .antiAddMult (compl : α → α) :=
  soundFor_antiAddMult_of_boundedLatticeHomClass (OrderIso.compl α)

theorem not_soundFor_antiAddMult : Signature.SoundFor .antiAddMult Not :=
  compl_soundFor_antiAddMult

end ComplInstance

/-! ### Per-position profiles

Two-place operators carry one signature per argument position — a
determiner is one signature in its restrictor and another in its scope.
`Signature₂` records the pair, `Signature₂.SoundFor` says each component is sound
for the corresponding section (the other argument held constant), and
`Signature.SoundFor.comp₂` composes an outer context into both
positions at once. Certified instances for generalized quantifiers live
in `Semantics/Quantification/Signatures.lean`. -/

/-- A per-position signature profile for a two-place operator. For
determiners the positions are restrictor and scope; under the restrictor
analysis of conditionals, antecedent and consequent. -/
structure Signature₂ where
  restrictor : Signature
  scope : Signature
  deriving DecidableEq, Repr

section Signature₂

variable {α β γ δ : Type*} [Lattice α] [BoundedOrder α] [Lattice β]
  [BoundedOrder β] [Lattice γ] [BoundedOrder γ] [Lattice δ] [BoundedOrder δ]

/-- A profile is sound for a two-place operator when each component
signature is sound for the corresponding section (the other argument held
constant). -/
def Signature₂.SoundFor (σ : Signature₂) (f : α → β → γ) : Prop :=
  (∀ y, σ.restrictor.SoundFor (fun x => f x y)) ∧
  (∀ x, σ.scope.SoundFor (f x))

theorem Signature.SoundFor.comp₂ {ψ : Signature} {g : γ → δ}
    {σ : Signature₂} {f : α → β → γ} (hg : ψ.SoundFor g) (hf : σ.SoundFor f) :
    Signature₂.SoundFor ⟨ψ * σ.restrictor, ψ * σ.scope⟩ (fun x y => g (f x y)) :=
  ⟨fun y => hg.comp (hf.1 y), fun x => hg.comp (hf.2 x)⟩

end Signature₂


/-! ### The projection row of a function class -/

section HoldsFor

variable {α β : Type*} [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β]

/-- The property rule is sound: a function with property `p` carries a constraint between its
arguments to the constraint `Signature.Property.project` says between its values. -/
theorem Signature.Property.HoldsFor.project {p : Signature.Property} {f : α → β}
    (hf : p.HoldsFor f) {a b : Relation.Atom} (h : Signature.Property.project a p = some b)
    {x y : α} (ha : a.Holds x y) : b.Holds (f x) (f y) := by
  cases a <;> cases p <;>
    simp only [Signature.Property.project, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    simp only [Signature.Property.HoldsFor, Relation.Atom.Holds] at hf ha ⊢
  all_goals first
    | exact hf ha
    | exact codisjoint_map_of_map_sup hf ha
    | exact disjoint_map_of_map_inf hf ha
    | exact disjoint_map_of_isAntiAdditive hf ha
    | exact codisjoint_map_of_isAntiMultiplicative hf ha

/-- σ's projection row is sound for every σ-function ([icard-2012] Lemma 2.5): `≡` because `f` is
a function, and every other constraint by the property rule. -/
theorem Signature.soundFor_of_holdsFor {σ : Signature} {f : α → β}
    (h : σ.HoldsFor f) : σ.SoundFor f := by
  intro R x y hR
  by_cases hRe : R = .equiv
  · subst hRe
    exact congrArg f hR
  refine Relation.holds_iff.2 fun _ hb ↦ ?_
  obtain ⟨p, hp, a, ha, hab⟩ := (Signature.mem_constraints_project hRe).1 hb
  exact (h p hp).project hab (Relation.holds_iff.1 hR a ha)

end HoldsFor

end NaturalLogic
