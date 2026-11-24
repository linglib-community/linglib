module

public import Linglib.Logic.Natural.ProjectivitySignature
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.Order.Hom.BoundedLattice
public import Mathlib.Order.Hom.Set

/-!
# Projection through projectivity signatures

A map carries a relation between two arguments to a relation between their values: a monotone map
keeps `⊑`, an antitone map turns it into `⊒`, and a map that takes disjoint elements to disjoint
elements keeps `|`. The projection of a relation `R` through a signature `σ` is the relation that
every `σ`-function carries `R` to. We define projection, show that it is an action of the monoid
of signatures on the relations, and call a signature sound for a map when the map carries every
relation to its projection.

## Main definitions

* `ProjectivitySignature.project`: the projection of a relation through a signature.
* `SoundFor`: `σ.SoundFor f` says that `f` carries every relation `R` to `project R σ`.

## Main results

* `project_project`: projecting through `φ` and then through `ψ` is projecting through `ψ * φ`.
* `soundFor_of_holdsFor`: a signature is sound for every map in its function class.
* `SoundFor.comp`: if `ψ` is sound for `f` and `φ` for `g`, then `ψ * φ` is sound for `f ∘ g`.
* `soundFor_mult_iff_map_compl_le` and its five companions: between Boolean algebras, a signature
  with a direction is sound for exactly the maps of that direction that take complementary
  elements to disjoint, codisjoint or complementary ones.

## Implementation notes

* Icard works over Boolean algebras. The definitions, and every result that does not mention
  complements, need only bounded lattices.
* A signature is sound for more maps than its function class holds: carrying codisjoint elements
  to codisjoint elements is weaker than preserving joins.

## References

* [icard-2012]
-/

@[expose] public section

namespace NaturalLogic

/-! ### Projection -/

namespace ProjectivitySignature

/-- The constraint between the values of a function with property `p` that a constraint `a` between
its arguments gives, when there is one: a monotone function keeps `≤` and `≥` and an antitone one
swaps them, an additive function keeps codisjointness and a multiplicative one disjointness, and
an anti-additive or anti-multiplicative function exchanges the two. -/
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

/-- Projecting through a composite property is projecting through the inner one and then the
outer. -/
theorem Property.compose_project : ∀ (p q : Property) (a : Relation.Atom),
    (p.compose q).bind (Property.project a ·) =
      (Property.project a q).bind (Property.project · p) := by
  decide

/-- The projection of a relation `R` through a signature `σ` ([icard-2012] Definition 2.3) is `≡`
when `R` is `≡`, since every function preserves equality, and otherwise the relation asserting
what the property rule gives for each property of `σ` and each constraint of `R`. -/
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

/-- Only `≡` projects to `≡`. -/
@[simp] theorem project_eq_equiv_iff : ∀ {R : Relation} {σ : ProjectivitySignature},
    project R σ = .equiv ↔ R = .equiv := by
  decide

/-- Projecting through `φ` and then through `ψ` is projecting through `ψ * φ` ([icard-2012]
Definition 2.6 and Lemma 2.7), since applying the composite property rule is applying the two
rules in turn. -/
theorem project_project (R : Relation) (φ ψ : ProjectivitySignature) :
    project (project R φ) ψ = project R (ψ * φ) := by
  by_cases hR : R = .equiv
  · subst hR; simp only [project_equiv]
  refine Relation.constraints_injective <| Finset.ext fun _ ↦ ?_
  simp only [mem_constraints_project (project_eq_equiv_iff.not.2 hR), mem_constraints_project hR,
    mem_properties_mul]
  exact (exists_bind_comm Property.compose_project).symm

instance : SMul ProjectivitySignature Relation := ⟨fun σ R ↦ project R σ⟩

@[simp] theorem smul_def (σ : ProjectivitySignature) (R : Relation) : σ • R = project R σ := rfl

/-- Projection is an action of the monoid of signatures on the relations. -/
instance : MulAction ProjectivitySignature Relation where
  one_smul := by decide
  mul_smul ψ φ R := (project_project R φ ψ).symm

/-- A signature is determined by how it projects the relations, already by its projections of `⊑`
and `^`. -/
instance : FaithfulSMul ProjectivitySignature Relation where
  eq_of_smul_eq_smul {σ τ} h := by
    have key : ∀ σ τ : ProjectivitySignature, project .forward σ = project .forward τ →
        project .negation σ = project .negation τ → σ = τ := by
      decide
    exact key σ τ (h .forward) (h .negation)

end ProjectivitySignature

/-! ### Soundness of a signature for a function -/

namespace ProjectivitySignature

section SoundFor

variable {α β γ : Type*} [Lattice α] [BoundedOrder α] [Lattice β]
  [BoundedOrder β] [Lattice γ] [BoundedOrder γ]

/-- `σ.SoundFor f` says that `f` takes arguments related by `R` to values related by the projection
of `R` through `σ`, for every relation `R` ([icard-2012] Lemma 2.5). -/
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

end ComplInstance

/-! ### Maps of Boolean algebras and complementation

Between Boolean algebras a row of the projection table is sound for a map exactly when the map has
the direction of the row and compares with complementation as the row says: `f xᶜ ≤ (f x)ᶜ` when it
takes complementary elements to disjoint ones, `(f x)ᶜ ≤ f xᶜ` when it takes them to codisjoint
ones, and equality when it commutes with complementation. A map of the first kind lies below its
De Morgan dual `x ↦ (f xᶜ)ᶜ` and one of the second kind above it. -/

section BooleanAlgebra

variable {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β] {f : α → β}

/-- The `⊞` row is sound for the monotone maps that take complements to disjoint elements. -/
theorem soundFor_mult_iff_map_compl_le :
    SoundFor .mult f ↔ Monotone f ∧ ∀ x, f xᶜ ≤ (f x)ᶜ := by
  rw [soundFor_mult_iff]
  exact and_congr_right fun hf ↦ ⟨fun h _ ↦ (h disjoint_compl_right).le_compl_left,
    fun h x _ hxy ↦ (disjoint_compl_right.mono_right (h x)).mono_right (hf hxy.le_compl_left)⟩

/-- The additive row is sound for the monotone maps that take complements to codisjoint
elements. -/
theorem soundFor_additive_iff_compl_map_le :
    SoundFor .additive f ↔ Monotone f ∧ ∀ x, (f x)ᶜ ≤ f xᶜ := by
  rw [soundFor_additive_iff]
  exact and_congr_right fun hf ↦
    ⟨fun h x ↦ codisjoint_iff_compl_le_right.1 (h (isCompl_compl (x := x)).codisjoint),
      fun h x _ hxy ↦ codisjoint_iff_compl_le_right.2
        ((h x).trans (hf (codisjoint_iff_compl_le_right.1 hxy)))⟩

/-- The `⊕` row is sound for the monotone maps that commute with complementation. -/
theorem soundFor_addMult_iff_map_compl :
    SoundFor .addMult f ↔ Monotone f ∧ ∀ x, f xᶜ = (f x)ᶜ := by
  have : SoundFor .addMult f ↔ SoundFor .mult f ∧ SoundFor .additive f := by
    rw [soundFor_addMult_iff, soundFor_mult_iff, soundFor_additive_iff]
    exact ⟨fun ⟨hm, hd, hc⟩ ↦ ⟨⟨hm, hd⟩, hm, hc⟩, fun ⟨⟨hm, hd⟩, _, hc⟩ ↦ ⟨hm, hd, hc⟩⟩
  rw [this, soundFor_mult_iff_map_compl_le, soundFor_additive_iff_compl_map_le]
  exact ⟨fun h ↦ ⟨h.1.1, fun x ↦ le_antisymm (h.1.2 x) (h.2.2 x)⟩,
    fun h ↦ ⟨⟨h.1, fun x ↦ (h.2 x).le⟩, h.1, fun x ↦ (h.2 x).ge⟩⟩

/-- The anti-additive row is sound for the antitone maps that take complements to disjoint
elements. -/
theorem soundFor_antiAdd_iff_map_compl_le :
    SoundFor .antiAdd f ↔ Antitone f ∧ ∀ x, f xᶜ ≤ (f x)ᶜ := by
  rw [soundFor_antiAdd_iff]
  exact and_congr_right fun hf ↦
    ⟨fun h x ↦ (h (isCompl_compl (x := x)).codisjoint).le_compl_left,
      fun h x _ hxy ↦ disjoint_compl_right.mono_right
        ((hf (codisjoint_iff_compl_le_right.1 hxy)).trans (h x))⟩

/-- The anti-multiplicative row is sound for the antitone maps that take complements to
codisjoint elements. -/
theorem soundFor_antiMult_iff_compl_map_le :
    SoundFor .antiMult f ↔ Antitone f ∧ ∀ x, (f x)ᶜ ≤ f xᶜ := by
  rw [soundFor_antiMult_iff]
  exact and_congr_right fun hf ↦
    ⟨fun h x ↦ codisjoint_iff_compl_le_right.1 (h (disjoint_compl_right (a := x))),
      fun h x _ hxy ↦ codisjoint_iff_compl_le_right.2 ((h x).trans (hf hxy.le_compl_left))⟩

/-- The `⊖` row is sound for the antitone maps that commute with complementation. -/
theorem soundFor_antiAddMult_iff_map_compl :
    SoundFor .antiAddMult f ↔ Antitone f ∧ ∀ x, f xᶜ = (f x)ᶜ := by
  have : SoundFor .antiAddMult f ↔ SoundFor .antiAdd f ∧ SoundFor .antiMult f := by
    rw [soundFor_antiAddMult_iff, soundFor_antiAdd_iff, soundFor_antiMult_iff]
    exact ⟨fun ⟨ha, hd, hc⟩ ↦ ⟨⟨ha, hc⟩, ha, hd⟩, fun ⟨⟨ha, hc⟩, _, hd⟩ ↦ ⟨ha, hd, hc⟩⟩
  rw [this, soundFor_antiAdd_iff_map_compl_le, soundFor_antiMult_iff_compl_map_le]
  exact ⟨fun h ↦ ⟨h.1.1, fun x ↦ le_antisymm (h.1.2 x) (h.2.2 x)⟩,
    fun h ↦ ⟨⟨h.1, fun x ↦ (h.2 x).le⟩, h.1, fun x ↦ (h.2 x).ge⟩⟩

end BooleanAlgebra

end ProjectivitySignature

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
    | exact codisjoint_iff.2 (by rw [← hf.1, ha.eq_top, hf.2])
    | exact disjoint_iff.2 (by rw [← hf.1, ha.eq_bot, hf.2])
    | exact disjoint_iff.2 (by rw [← hf.1, ha.eq_top, hf.2])
    | exact codisjoint_iff.2 (by rw [← hf.1, ha.eq_bot, hf.2])

/-- A function carries the constraints of a property `p` when it takes arguments satisfying a
constraint to values satisfying the constraint that `Property.project` gives for `p`. -/
def Property.Carries (p : Property) (f : α → β) : Prop :=
  ∀ ⦃a b⦄, Property.project a p = some b → ∀ ⦃x y⦄, a.Holds x y → b.Holds (f x) (f y)

theorem Property.HoldsFor.carries {p : Property} {f : α → β} (hf : p.HoldsFor f) : p.Carries f :=
  fun _ _ h _ _ ha ↦ hf.project h ha

/-- The row of `σ` is sound for exactly the functions that carry the constraints of each property
of `σ`. -/
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

/-- The row of `σ` is sound for every σ-function ([icard-2012] Lemma 2.5). -/
theorem soundFor_of_holdsFor {σ : ProjectivitySignature} {f : α → β}
    (h : σ.HoldsFor f) : σ.SoundFor f :=
  soundFor_iff_forall_carries.2 fun p hp ↦ (h p hp).carries

end HoldsFor

end ProjectivitySignature

end NaturalLogic
