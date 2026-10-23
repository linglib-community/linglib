module

public import Linglib.Logic.Natural.Basic
public import Linglib.Logic.Natural.Additivity
public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.Order.Hom.BoundedLattice
public import Mathlib.Order.Hom.Set

/-!
# Soundness of the projectivity calculus

This file gives the seven relations their lattice content and proves the tables of
`Logic/Natural/Basic.lean` sound for it over bounded lattices: chained relations compose as the
join table says, and a signature's projection row holds of a function exactly when the function
is monotone or antitone and carries disjoint and codisjoint pairs as the row says. The function
classes of [icard-2012] fall in their rows, their unit conditions being mathlib's pairing of
meets with `⊥` and joins with `⊤`, and so do bounded lattice homomorphisms and, into the order
dual, complementation.

## Main results

* `Relation.Holds.join`: soundness of the join table.
* `soundFor_additive_iff`, …, `soundFor_antiAddMult_iff`: what each projection row demands of a
  function.
* `Signature.soundFor_of_holdsFor`: a signature's row holds of every function in its class.
* `Signature.SoundFor.comp`: soundness composes along `Signature.compose`.

## Implementation notes

* Icard works over Boolean algebras; the proofs need only bounded lattices, and distributivity
  for the join table.

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

theorem Relation.Holds.join {β : Type*} [DistribLattice β] [BoundedOrder β]
    {R S : Relation} {x y z : β} (hR : R.Holds x y) (hS : S.Holds y z) :
    (R.join S).Holds x z := by
  cases R <;> cases S <;>
    first
      | trivial
      | exact hR.symm ▸ hS
      | exact hS ▸ hR
      | exact hR.trans hS
      | exact hS.trans hR
      | exact hS.disjoint.mono_left hR
      | exact hS.mono_left hR
      | exact hS.codisjoint.mono_left hR
      | exact hR.codisjoint.mono_right hS
      | exact hR.disjoint.mono_right hS
      | exact hR.symm.right_unique hS
      | exact hS.symm.le_of_codisjoint hR.codisjoint.symm
      | exact hR.disjoint.le_of_codisjoint hS
      | exact hR.le_of_codisjoint hS.codisjoint
      | exact hR.mono_right hS
      | exact hR.le_of_codisjoint hS
      | exact hS.symm.le_of_codisjoint hR.symm
      | exact hS.disjoint.symm.le_of_codisjoint hR.symm

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

theorem soundFor_additive {f : α → β} (h : (∀ p q, f (p ⊔ q) = f p ⊔ f q) ∧ f ⊤ = ⊤) :
    Signature.SoundFor .additive f :=
  soundFor_additive_iff.2 ⟨monotone_of_map_sup h.1, fun _ _ ↦ codisjoint_map_of_map_sup h⟩

theorem soundFor_mult {f : α → β} (h : (∀ p q, f (p ⊓ q) = f p ⊓ f q) ∧ f ⊥ = ⊥) :
    Signature.SoundFor .mult f :=
  soundFor_mult_iff.2 ⟨monotone_of_map_inf h.1, fun _ _ ↦ disjoint_map_of_map_inf h⟩

theorem soundFor_antiAdd {f : α → β} (h : IsAntiAdditive f ∧ f ⊤ = ⊥) :
    Signature.SoundFor .antiAdd f :=
  soundFor_antiAdd_iff.2 ⟨h.1.antitone, fun _ _ ↦ disjoint_map_of_isAntiAdditive h⟩

theorem soundFor_antiMult {f : α → β} (h : IsAntiMultiplicative f ∧ f ⊥ = ⊤) :
    Signature.SoundFor .antiMult f :=
  soundFor_antiMult_iff.2 ⟨h.1.antitone, fun _ _ ↦ codisjoint_map_of_isAntiMultiplicative h⟩

theorem soundFor_addMult {f : α → β}
    (hadd : (∀ p q, f (p ⊔ q) = f p ⊔ f q) ∧ f ⊤ = ⊤)
    (hmult : (∀ p q, f (p ⊓ q) = f p ⊓ f q) ∧ f ⊥ = ⊥) :
    Signature.SoundFor .addMult f :=
  soundFor_addMult_iff.2 ⟨monotone_of_map_sup hadd.1, fun _ _ ↦ disjoint_map_of_map_inf hmult,
    fun _ _ ↦ codisjoint_map_of_map_sup hadd⟩

theorem soundFor_antiAddMult {f : α → β}
    (haa : IsAntiAdditive f ∧ f ⊤ = ⊥) (ham : IsAntiMultiplicative f ∧ f ⊥ = ⊤) :
    Signature.SoundFor .antiAddMult f :=
  soundFor_antiAddMult_iff.2 ⟨haa.1.antitone,
    fun _ _ ↦ codisjoint_map_of_isAntiMultiplicative ham,
    fun _ _ ↦ disjoint_map_of_isAntiAdditive haa⟩

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

theorem Signature.project_mono (R : Relation) :
    Monotone (Signature.project R) := by
  intro σ τ h
  revert h; cases σ <;> cases τ <;> cases R <;> decide

theorem Signature.SoundFor.of_le {σ τ : Signature} {f : α → β}
    (h : σ.SoundFor f) (hστ : σ ≤ τ) : τ.SoundFor f :=
  fun R x y hR => (h R x y hR).of_le (Signature.project_mono R hστ)

/-! ### Composition and paths -/

/-- **Soundness composes along `Signature.compose`** ([icard-2012]
Lemma 2.7 + Proposition 2.10): if ψ is sound for the outer function and φ
for the inner one, `ψ * φ` is sound for the composite. This is the theorem
that certifies the enum-level `compose` table against actual context
functions. -/
theorem Signature.SoundFor.comp {ψ φ : Signature} {f : β → γ}
    {g : α → β} (hf : ψ.SoundFor f) (hg : φ.SoundFor g) :
    (ψ * φ).SoundFor (f ∘ g) := by
  intro R x y hR
  have h := hf (Signature.project R φ) (g x) (g y) (hg R x y hR)
  rwa [projection_composition] at h

theorem soundFor_addMult_id : Signature.SoundFor .addMult (id : α → α) :=
  soundFor_addMult ⟨fun _ _ => rfl, rfl⟩ ⟨fun _ _ => rfl, rfl⟩

theorem soundFor_contextProjectivity :
    ∀ (l : List (Signature × (α → α))),
      (∀ p ∈ l, p.1.SoundFor p.2) →
      (Signature.contextProjectivity (l.map Prod.fst)).SoundFor
        ((l.map Prod.snd).foldr (· ∘ ·) id)
  | [], _ => soundFor_addMult_id
  | p :: l, h => by
      have hhead : p.1.SoundFor p.2 := h p (List.mem_cons_self ..)
      have htail := soundFor_contextProjectivity l
        (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simpa [Signature.contextProjectivity, List.prod_cons, List.map_cons,
        List.foldr_cons] using
        hhead.comp htail

end SoundFor

/-! ### Worked instance: double negation is a morphism, semantically

Complementation in a Boolean algebra is completely anti-additive and
anti-multiplicative, so the `.antiAddMult` row is sound for it;
composing it with itself certifies the enum fact `◇⊟ ∘ ◇⊟ = ⊕⊞` against
the actual function `compl ∘ compl`. -/

section ComplInstance


variable {α : Type*} [BooleanAlgebra α]

theorem compl_soundFor_antiAddMult :
    Signature.SoundFor .antiAddMult (compl : α → α) :=
  soundFor_antiAddMult_of_boundedLatticeHomClass (OrderIso.compl α)

/-- Double negation realizes the morphism row — the composed-signature
fact `◇⊟ ∘ ◇⊟ = ⊕⊞`, certified semantically rather than by enum table
lookup. -/
example : Signature.SoundFor .addMult ((compl : α → α) ∘ compl) :=
  compl_soundFor_antiAddMult.comp compl_soundFor_antiAddMult

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


/-! ### The function class of a signature -/

section HoldsFor

variable {α β : Type*} [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β]

/-- The function class a property asserts. -/
def Signature.Property.HoldsFor : Signature.Property → (α → β) → Prop
  | .monotone => Monotone
  | .antitone => Antitone
  | .additive => fun f => (∀ p q, f (p ⊔ q) = f p ⊔ f q) ∧ f ⊤ = ⊤
  | .multiplicative => fun f => (∀ p q, f (p ⊓ q) = f p ⊓ f q) ∧ f ⊥ = ⊥
  | .antiAdditive => fun f => IsAntiAdditive f ∧ f ⊤ = ⊥
  | .antiMultiplicative => fun f => IsAntiMultiplicative f ∧ f ⊥ = ⊤

/-- A function has signature σ — is a "σ-function" — when it has every
property σ asserts. -/
def Signature.HoldsFor (σ : Signature) (f : α → β) : Prop :=
  ∀ p ∈ σ.properties, p.HoldsFor f

/-- σ's projection row is sound for every σ-function ([icard-2012]
Lemma 2.5), aggregating the per-row theorems. -/
theorem Signature.soundFor_of_holdsFor {σ : Signature} {f : α → β}
    (h : σ.HoldsFor f) : σ.SoundFor f := by
  cases σ with
  | all => exact soundFor_all f
  | mono => exact soundFor_mono_iff.mpr (h .monotone (by decide))
  | anti => exact soundFor_anti_iff.mpr (h .antitone (by decide))
  | additive => exact soundFor_additive (h .additive (by decide))
  | antiAdd => exact soundFor_antiAdd (h .antiAdditive (by decide))
  | mult => exact soundFor_mult (h .multiplicative (by decide))
  | antiMult => exact soundFor_antiMult (h .antiMultiplicative (by decide))
  | addMult =>
      exact soundFor_addMult (h .additive (by decide)) (h .multiplicative (by decide))
  | antiAddMult =>
      exact soundFor_antiAddMult (h .antiAdditive (by decide))
        (h .antiMultiplicative (by decide))

theorem Signature.HoldsFor.of_le {σ τ : Signature} {f : α → β}
    (h : σ.HoldsFor f) (hστ : σ ≤ τ) : τ.HoldsFor f :=
  λ p hp => h p (Signature.le_iff.mp hστ hp)

theorem Signature.holdsFor_anti_iff {f : α → β} : Signature.HoldsFor .anti f ↔ Antitone f := by
  simp [Signature.HoldsFor, Signature.properties, Signature.Property.HoldsFor]

theorem Signature.holdsFor_antiAdd_iff {f : α → β} :
    Signature.HoldsFor .antiAdd f ↔ IsAntiAdditive f ∧ f ⊤ = ⊥ := by
  simp only [Signature.HoldsFor, Signature.properties, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, Signature.Property.HoldsFor]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.1.antitone, h⟩⟩

theorem Signature.holdsFor_antiAddMult_iff {f : α → β} :
    Signature.HoldsFor .antiAddMult f ↔
      (IsAntiAdditive f ∧ f ⊤ = ⊥) ∧ IsAntiMultiplicative f ∧ f ⊥ = ⊤ := by
  simp only [Signature.HoldsFor, Signature.properties, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, Signature.Property.HoldsFor]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.1.1.antitone, h⟩⟩

theorem Signature.holdsFor_addMult_of_galoisConnection {f u l : α → α}
    (gc₁ : GaloisConnection f u) (gc₂ : GaloisConnection l f) :
    Signature.HoldsFor .addMult f := by
  intro p hp
  cases p with
  | monotone => exact gc₁.monotone_l
  | additive => exact ⟨λ _ _ => gc₁.l_sup, gc₂.u_top⟩
  | multiplicative => exact ⟨λ _ _ => gc₂.u_inf, gc₁.l_bot⟩
  | antitone | antiAdditive | antiMultiplicative => exact absurd hp (by decide)

theorem Signature.holdsFor_antiAddMult_compl {γ : Type*} [BooleanAlgebra γ] :
    Signature.HoldsFor .antiAddMult (compl : γ → γ) := by
  intro p hp
  cases p with
  | antitone => exact antitone_compl
  | antiAdditive => exact ⟨isAntiAdditive_compl, compl_top⟩
  | antiMultiplicative => exact ⟨isAntiMultiplicative_compl, compl_bot⟩
  | monotone | additive | multiplicative => exact absurd hp (by decide)

end HoldsFor

section DecidableHoldsFor

variable {α β : Type*} [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β]
  [Fintype α] [DecidableLE α] [DecidableEq β] [DecidableLE β]

instance Signature.Property.decidableHoldsFor :
    ∀ (p : Signature.Property) (f : α → β), Decidable (p.HoldsFor f)
  | .monotone, f => decidable_of_iff (∀ a b, a ≤ b → f a ≤ f b) Iff.rfl
  | .antitone, f => decidable_of_iff (∀ a b, a ≤ b → f b ≤ f a) Iff.rfl
  | .additive, f =>
      decidable_of_iff ((∀ p q, f (p ⊔ q) = f p ⊔ f q) ∧ f ⊤ = ⊤) Iff.rfl
  | .multiplicative, f =>
      decidable_of_iff ((∀ p q, f (p ⊓ q) = f p ⊓ f q) ∧ f ⊥ = ⊥) Iff.rfl
  | .antiAdditive, f =>
      decidable_of_iff ((∀ p q, f (p ⊔ q) = f p ⊓ f q) ∧ f ⊤ = ⊥) Iff.rfl
  | .antiMultiplicative, f =>
      decidable_of_iff ((∀ p q, f (p ⊓ q) = f p ⊔ f q) ∧ f ⊥ = ⊤) Iff.rfl

instance Signature.decidableHoldsFor (σ : Signature) (f : α → β) :
    Decidable (σ.HoldsFor f) :=
  inferInstanceAs (Decidable (∀ p ∈ σ.properties, p.HoldsFor f))

end DecidableHoldsFor


end NaturalLogic
