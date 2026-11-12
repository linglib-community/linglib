module

public import Linglib.Logic.Natural.ProjectivitySignature
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.Order.Hom.BoundedLattice
public import Mathlib.Order.Hom.Set

/-!
# Projection through projectivity signatures

A map of known projectivity signature carries a relation between two arguments to a relation
between their values: a monotone map keeps `⊑`, an antitone one turns it into `⊒`, and the
additive and multiplicative properties carry disjointness and codisjointness. Projection is an
[action](##NaturalLogic.ProjectivitySignature.project_project) of the signature monoid on the
relations, and each signature's row is
[sound](##NaturalLogic.ProjectivitySignature.soundFor_of_holdsFor) for the maps in its function
class, as it is for bounded lattice homomorphisms and, into the order dual, for complementation.

## Implementation notes

* Icard works over Boolean algebras; the proofs need only bounded lattices.

## References

* [icard-2012]
-/

@[expose] public section

namespace NaturalLogic

/-! ### Projection -/

namespace ProjectivitySignature

/-- The constraint between the values of a function with property `p` that a constraint `a`
between its arguments guarantees, when there is one
(`ProjectivitySignature.Property.HoldsFor.project`): a monotone function keeps `≤` and `≥` and an
antitone one swaps them, an additive function keeps codisjointness and a multiplicative one
disjointness, an anti-additive function turns codisjointness into disjointness and an
anti-multiplicative one the reverse. -/
def Property.project : Relation.Atom → Property → Option Relation.Atom
  | .le, .monotone => some .le
  | .ge, .monotone => some .ge
  | .le, .antitone => some .ge
  | .ge, .antitone => some .le
  | .codisjoint, .additive => some .codisjoint
  | .disjoint, .multiplicative => some .disjoint
  | .codisjoint, .antiAdditive => some .disjoint
  | .disjoint, .antiMultiplicative => some .codisjoint
  | _, _ => none

private theorem Property.compose_project : ∀ (p q : Property) (a : Relation.Atom),
    (p.compose q).bind (Property.project a ·) =
      (Property.project a q).bind (Property.project · p) := by
  decide

/-- The projection of a relation through a function of the given signature is the strongest relation
guaranteed between `f x` and `f y` when `x R y` and `f` has signature `σ` ([icard-2012] Definition
2.3, computed by his Lemma 2.4): `≡`, since every function preserves equality, and otherwise the
relation asserting what the property rule gives for each property of `σ` and constraint of `R`
(`ProjectivitySignature.mem_constraints_project`). Each row is sound
(`ProjectivitySignature.soundFor_of_holdsFor`) and least (`ProjectivitySignature.isLeast_project` in
`Logic/Natural/Completeness.lean`). [icard-2012] remarks under the table that `[R]^• = #` for all
`R` (p. 715), which is what the property rule alone gives for `≡` too. -/
def project (R : Relation) (σ : ProjectivitySignature) : Relation :=
  if R = .equiv then .equiv else
    Relation.ofAtoms fun b ↦ ∃ p ∈ σ.properties, ∃ a ∈ R.constraints, Property.project a p = some b

@[simp] theorem project_equiv (φ : ProjectivitySignature) : project .equiv φ = .equiv := rfl

@[simp] theorem project_independent (φ : ProjectivitySignature) :
    project .independent φ = .independent := by
  cases φ <;> rfl

theorem mem_constraints_project {R : Relation} (hR : R ≠ .equiv) {σ : ProjectivitySignature}
    {b : Relation.Atom} : b ∈ (project R σ).constraints ↔
      ∃ p ∈ σ.properties, ∃ a ∈ R.constraints, Property.project a p = some b := by
  revert R σ b
  decide

/-- Projection through a less specific signature gives a weaker relation. -/
theorem project_mono (R : Relation) : Monotone (project R) := by
  intro σ τ h
  by_cases hR : R = .equiv
  · subst hR
    exact le_rfl
  refine Relation.le_iff.2 fun _ hb ↦ ?_
  obtain ⟨p, hp, a, ha, hab⟩ := (mem_constraints_project hR).1 hb
  exact (mem_constraints_project hR).2 ⟨p, le_iff.1 h hp, a, ha, hab⟩

private theorem project_ne_equiv : ∀ {R : Relation} (σ : ProjectivitySignature), R ≠ .equiv →
    project R σ ≠ .equiv := by
  decide

/-- Projecting through `φ` and then through `ψ` is projecting through `ψ * φ` ([icard-2012]
Definition 2.6 and Lemma 2.7), since applying the composite property rule is applying the two
rules in turn. -/
theorem project_project (R : Relation) (φ ψ : ProjectivitySignature) :
    project (project R φ) ψ = project R (ψ * φ) := by
  by_cases hR : R = .equiv
  · subst hR; simp only [project_equiv]
  refine Relation.constraints_injective <| Finset.ext fun _ ↦ ?_
  simp only [mem_constraints_project (project_ne_equiv φ hR), mem_constraints_project hR,
    mem_properties_mul]
  exact (exists_bind_comm Property.compose_project).symm

instance : SMul ProjectivitySignature Relation := ⟨fun σ R ↦ project R σ⟩

@[simp] theorem smul_def (σ : ProjectivitySignature) (R : Relation) : σ • R = project R σ := rfl

/-- Projection is an action of the signature monoid on the relations, with
`ProjectivitySignature.project_project` as its `mul_smul` law. -/
instance : MulAction ProjectivitySignature Relation where
  one_smul := by decide
  mul_smul ψ φ R := (project_project R φ ψ).symm

private theorem eq_of_project_eq : ∀ σ τ : ProjectivitySignature,
    project .forward σ = project .forward τ → project .negation σ = project .negation τ → σ = τ := by
  decide

/-- A signature is determined by how it projects the relations, already by its projections of `⊑`
and `^`. -/
instance : FaithfulSMul ProjectivitySignature Relation where
  eq_of_smul_eq_smul {σ τ} h := eq_of_project_eq σ τ (h .forward) (h .negation)

end ProjectivitySignature

/-! ### Soundness of a signature for a function -/

namespace ProjectivitySignature

section SoundFor

variable {α β γ : Type*} [Lattice α] [BoundedOrder α] [Lattice β]
  [BoundedOrder β] [Lattice γ] [BoundedOrder γ]

/-- A signature σ is **sound for** `f` when `f` projects every relation as
σ's row of the projection table says ([icard-2012] Lemma 2.5: every
φ-function projects `R` to `[R]^φ`). -/
def SoundFor (σ : ProjectivitySignature) (f : α → β) : Prop :=
  ∀ (R : Relation) (x y : α), R.Holds x y →
    (project R σ).Holds (f x) (f y)

theorem soundFor_mono_iff {f : α → β} :
    SoundFor .mono f ↔ Monotone f := by
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
    SoundFor .anti f ↔ Antitone f := by
  constructor
  · intro h x y hxy
    exact h .forward x y hxy
  · intro h R x y hR
    cases R with
    | equiv => exact congrArg f hR
    | forward => exact h hR
    | reverse => exact h hR
    | negation | alternation | cover | independent => trivial

theorem SoundFor.monotone {σ : ProjectivitySignature} {f : α → β} (h : σ.SoundFor f)
    (hσ : σ.sign = 1) : Monotone f := by
  intro x y hxy
  cases σ <;> first | exact h .forward x y hxy | exact absurd hσ (by decide)

theorem SoundFor.antitone {σ : ProjectivitySignature} {f : α → β} (h : σ.SoundFor f)
    (hσ : σ.sign = -1) : Antitone f := by
  intro x y hxy
  cases σ <;> first | exact h .forward x y hxy | exact absurd hσ (by decide)

/-- The `.additive` row is sound exactly for the monotone functions sending codisjoint pairs to
codisjoint pairs. -/
theorem soundFor_additive_iff {f : α → β} :
    SoundFor .additive f ↔
      Monotone f ∧ ∀ ⦃x y⦄, Codisjoint x y → Codisjoint (f x) (f y) := by
  refine ⟨fun h ↦ ⟨fun x y ↦ h .forward x y, fun x y ↦ h .cover x y⟩, fun ⟨hm, hc⟩ R x y hR ↦ ?_⟩
  cases R with
  | equiv => exact congrArg f hR
  | forward | reverse => exact hm hR
  | negation => exact hc hR.codisjoint
  | cover => exact hc hR
  | alternation | independent => trivial

theorem soundFor_mult_iff {f : α → β} :
    SoundFor .mult f ↔ Monotone f ∧ ∀ ⦃x y⦄, Disjoint x y → Disjoint (f x) (f y) := by
  refine ⟨fun h ↦ ⟨fun x y ↦ h .forward x y, fun x y ↦ h .alternation x y⟩,
    fun ⟨hm, hd⟩ R x y hR ↦ ?_⟩
  cases R with
  | equiv => exact congrArg f hR
  | forward | reverse => exact hm hR
  | negation => exact hd hR.disjoint
  | alternation => exact hd hR
  | cover | independent => trivial

theorem soundFor_antiAdd_iff {f : α → β} :
    SoundFor .antiAdd f ↔
      Antitone f ∧ ∀ ⦃x y⦄, Codisjoint x y → Disjoint (f x) (f y) := by
  refine ⟨fun h ↦ ⟨fun x y ↦ h .forward x y, fun x y ↦ h .cover x y⟩, fun ⟨ha, hc⟩ R x y hR ↦ ?_⟩
  cases R with
  | equiv => exact congrArg f hR
  | forward | reverse => exact ha hR
  | negation => exact hc hR.codisjoint
  | cover => exact hc hR
  | alternation | independent => trivial

theorem soundFor_antiMult_iff {f : α → β} :
    SoundFor .antiMult f ↔
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
    SoundFor .addMult f ↔ Monotone f ∧
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
    SoundFor .antiAddMult f ↔ Antitone f ∧
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
    [BoundedLatticeHomClass F α β] (f : F) : SoundFor .addMult f :=
  soundFor_addMult_iff.2 ⟨OrderHomClass.mono f, fun _ _ h ↦ h.map f, fun _ _ h ↦ h.map f⟩

theorem soundFor_antiAddMult_of_boundedLatticeHomClass {F : Type*} [FunLike F α βᵒᵈ]
    [BoundedLatticeHomClass F α βᵒᵈ] (f : F) :
    SoundFor .antiAddMult (OrderDual.ofDual ∘ f) :=
  soundFor_antiAddMult_iff.2 ⟨fun _ _ h ↦ OrderHomClass.mono f h,
    fun _ _ h ↦ codisjoint_ofDual_iff.2 (h.map f), fun _ _ h ↦ disjoint_ofDual_iff.2 (h.map f)⟩

theorem soundFor_all (f : α → β) : SoundFor .all f := by
  intro R x y hR
  cases R
  case equiv => exact congrArg f hR
  all_goals trivial

theorem SoundFor.apply {ι : Type*} {σ : ProjectivitySignature} {f : α → ι → β}
    (h : σ.SoundFor f) (i : ι) : σ.SoundFor (f · i) :=
  fun R x y hR => (h R x y hR).apply i

theorem SoundFor.of_le {σ τ : ProjectivitySignature} {f : α → β}
    (h : σ.SoundFor f) (hστ : σ ≤ τ) : τ.SoundFor f :=
  fun R x y hR => (h R x y hR).of_le (project_mono R hστ)

/-! ### Composition and paths -/

/-- If ψ is sound for the outer function and φ for the inner one, `ψ * φ` is sound for the composite
([icard-2012] Lemma 2.7, Proposition 2.10). -/
theorem SoundFor.comp {ψ φ : ProjectivitySignature} {f : β → γ}
    {g : α → β} (hf : ψ.SoundFor f) (hg : φ.SoundFor g) :
    (ψ * φ).SoundFor (f ∘ g) := by
  intro R x y hR
  have h := hf (project R φ) (g x) (g y) (hg R x y hR)
  rwa [project_project] at h

theorem soundFor_addMult_id : SoundFor .addMult (id : α → α) :=
  soundFor_addMult_iff.2 ⟨monotone_id, fun _ _ h ↦ h, fun _ _ h ↦ h⟩

theorem project_forward_of_sign_eq_one {σ : ProjectivitySignature} (h : σ.sign = 1) :
    project .forward σ = .forward := by
  revert h; cases σ <;> decide

theorem project_forward_of_sign_eq_neg_one {σ : ProjectivitySignature} (h : σ.sign = -1) :
    project .forward σ = .reverse := by
  revert h; cases σ <;> decide

/-- A function a signature of positive sign is sound for is monotone. -/
theorem SoundFor.monotone_of_sign_eq_one {σ : ProjectivitySignature} {f : α → β}
    (hf : σ.SoundFor f) (h : σ.sign = 1) : Monotone f := fun x y hxy ↦ by
  simpa [project_forward_of_sign_eq_one h, Relation.Holds] using hf .forward x y hxy

/-- A function a signature of negative sign is sound for is antitone. -/
theorem SoundFor.antitone_of_sign_eq_neg_one {σ : ProjectivitySignature} {f : α → β}
    (hf : σ.SoundFor f) (h : σ.sign = -1) : Antitone f := fun x y hxy ↦ by
  simpa [project_forward_of_sign_eq_neg_one h, Relation.Holds] using hf .forward x y hxy

end SoundFor

/-! ### Complementation

Complementation in a Boolean algebra is completely anti-additive and anti-multiplicative, so the
anti-morphism row `⊖` is sound for it. -/

section ComplInstance

variable {α : Type*} [BooleanAlgebra α]

theorem compl_soundFor_antiAddMult :
    SoundFor .antiAddMult (compl : α → α) :=
  soundFor_antiAddMult_of_boundedLatticeHomClass (OrderIso.compl α)

theorem not_soundFor_antiAddMult : SoundFor .antiAddMult Not :=
  compl_soundFor_antiAddMult

end ComplInstance

end ProjectivitySignature

/-! ### Per-position profiles

Two-place operators carry one signature per argument position — a
determiner is one signature in its restrictor and another in its scope.
`ProjectivitySignature₂` records the pair, `ProjectivitySignature₂.SoundFor` says each component is
sound for the corresponding section (the other argument held constant), and
`ProjectivitySignature.SoundFor.comp₂` composes an outer context into both
positions at once. Certified instances for generalized quantifiers live
in `Semantics/Quantification/Signatures.lean`. -/

/-- A per-position signature profile for a two-place operator. For
determiners the positions are restrictor and scope; under the restrictor
analysis of conditionals, antecedent and consequent. -/
structure ProjectivitySignature₂ where
  restrictor : ProjectivitySignature
  scope : ProjectivitySignature
  deriving DecidableEq, Repr

section ProjectivitySignature₂

variable {α β γ δ : Type*} [Lattice α] [BoundedOrder α] [Lattice β]
  [BoundedOrder β] [Lattice γ] [BoundedOrder γ] [Lattice δ] [BoundedOrder δ]

/-- A profile is sound for a two-place operator when each component
signature is sound for the corresponding section (the other argument held
constant). -/
def ProjectivitySignature₂.SoundFor (σ : ProjectivitySignature₂) (f : α → β → γ) : Prop :=
  (∀ y, σ.restrictor.SoundFor (fun x => f x y)) ∧
  (∀ x, σ.scope.SoundFor (f x))

theorem ProjectivitySignature.SoundFor.comp₂ {ψ : ProjectivitySignature} {g : γ → δ}
    {σ : ProjectivitySignature₂} {f : α → β → γ} (hg : ψ.SoundFor g) (hf : σ.SoundFor f) :
    ProjectivitySignature₂.SoundFor ⟨ψ * σ.restrictor, ψ * σ.scope⟩ (fun x y => g (f x y)) :=
  ⟨fun y => hg.comp (hf.1 y), fun x => hg.comp (hf.2 x)⟩

end ProjectivitySignature₂


/-! ### The projection row of a function class -/

namespace ProjectivitySignature

section HoldsFor

variable {α β : Type*} [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β]

/-- The property rule is sound: a function with property `p` carries a constraint between its
arguments to the constraint `Property.project` says between its values. -/
theorem Property.HoldsFor.project {p : Property} {f : α → β}
    (hf : p.HoldsFor f) {a b : Relation.Atom} (h : Property.project a p = some b)
    {x y : α} (ha : a.Holds x y) : b.Holds (f x) (f y) := by
  cases a <;> cases p <;>
    simp only [Property.project, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    simp only [Property.HoldsFor, Relation.Atom.Holds] at hf ha ⊢
  all_goals first
    | exact hf ha
    | exact codisjoint_map_of_map_sup hf ha
    | exact disjoint_map_of_map_inf hf ha
    | exact disjoint_map_of_isAntiAdditive hf ha
    | exact codisjoint_map_of_isAntiMultiplicative hf ha

/-- A function carries the constraints of a property when it takes each constraint between its
arguments to the constraint `Property.project` says between its values. A function with the
property does (`Property.HoldsFor.project`), and so do others: carrying codisjointness to
codisjointness is weaker than preserving joins. -/
def Property.Carries (p : Property) (f : α → β) : Prop :=
  ∀ ⦃a b⦄, Property.project a p = some b → ∀ ⦃x y⦄, a.Holds x y → b.Holds (f x) (f y)

theorem Property.HoldsFor.carries {p : Property} {f : α → β} (hf : p.HoldsFor f) : p.Carries f :=
  fun _ _ h _ _ ha ↦ hf.project h ha

/-- σ's projection row is sound for exactly the functions that carry the constraints of each of
σ's properties, as its function class is the functions with each of them
(`ProjectivitySignature.HoldsFor`). -/
theorem soundFor_iff_forall_carries {σ : ProjectivitySignature} {f : α → β} :
    σ.SoundFor f ↔ ∀ p ∈ σ.properties, p.Carries f := by
  refine ⟨fun h p hp a b hab x y ha ↦ ?_, fun h R x y hR ↦ ?_⟩
  · have hne : a.toRelation ≠ .equiv := by cases a <;> decide
    exact Relation.holds_iff.1 (h a.toRelation x y (Relation.holds_toRelation.2 ha)) b
      ((mem_constraints_project hne).2 ⟨p, hp, a, by simp, hab⟩)
  · by_cases hRe : R = .equiv
    · subst hRe
      exact congrArg f hR
    refine Relation.holds_iff.2 fun _ hb ↦ ?_
    obtain ⟨p, hp, a, ha, hab⟩ := (mem_constraints_project hRe).1 hb
    exact h p hp hab (Relation.holds_iff.1 hR a ha)

/-- σ's projection row is sound for every σ-function ([icard-2012] Lemma 2.5): a function with a
property carries its constraints. -/
theorem soundFor_of_holdsFor {σ : ProjectivitySignature} {f : α → β}
    (h : σ.HoldsFor f) : σ.SoundFor f :=
  soundFor_iff_forall_carries.2 fun p hp ↦ (h p hp).carries

end HoldsFor

end ProjectivitySignature

end NaturalLogic
