module

public import Linglib.Logic.Aristotelian.Morphism
public import Linglib.Logic.Modal.Basic
public import Linglib.Semantics.Quantification.Basic
public import Studies.DemeySmessaert2018
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod

/-!
# Demey and Smessaert 2024

Keynes and Johnson extended the square of opposition to an octagon of categorical statements with
subject negation, read in first-order logic with existential import (EFOL). Demey and Smessaert
compare it with an octagon of sets from knowledge representation, built from a relation `R` and a
set `S`, and with a new octagon of deontic formulas in the modal logic KD. All three are
Aristotelian isomorphic, but the first two have Boolean closures of `2 ^ 7` elements and the
deontic one of `2 ^ 6`, so the deontic octagon is not Boolean isomorphic to the others. Every
octagon with the same Aristotelian relations, in any Boolean algebra, has six or seven cells, and
is Boolean isomorphic to the deontic octagon or to the octagon for subject negation accordingly.

## Main definitions

* `subjectNegation`, `deontic`, `knowledgeRep`: the three Keynes–Johnson octagons.

## Implementation notes

A subject-negation statement depends only on which regions of `S` and `P` are inhabited, so a
proposition is a set of EFOL patterns, each read on its canonical model as in
[demey-smessaert-2018]; a deontic formula is likewise a set of KD world types. Both readings are
exact: over a domain of four individuals and a frame of three worlds, the octagons over EFOL and
KD models are Boolean isomorphic to those over patterns and types (`subjectNegationModelsIso`,
`deonticModelsIso`), so [the deontic octagon of KD models is not Boolean isomorphic to the octagon
for subject negation of EFOL models](##isEmpty_booleanIso_deonticModels). The octagons are
indexed by the subject-negation positions, so `γ` and `δ` are the identity, and Section 5's
generic description is the subject-negation octagon's. The knowledge-representation octagon
assumes, as the paper does tacitly, that `X` realizes every pattern. The paper identifies the
Boolean subfamilies with the sizes of the closures; here two octagons of one size are shown to
have minterms vanishing at the same polarity assignments, which makes their Aristotelian
isomorphism a Boolean one.

## References

* [demey-smessaert-2024]
* [demey-smessaert-2018]
-/

@[expose] public section

namespace DemeySmessaert2024

open Finset Function Quantifier Quantifier.Det Aristotelian ModalLogic SetRel
open DemeySmessaert2018 (InS InP regions mem_regions exists_regions_eq)

/-! ### Subject negation (Section 2) -/

/-- A finite set of regions, a region recording whether an individual is `S` and whether it is
`P`, is an EFOL pattern when `S`, non-`S`, `P` and non-`P` are each inhabited. -/
def IsEFOLPattern (m : Finset (Bool × Bool)) : Prop :=
  (∃ r ∈ m, r.1 = true) ∧ (∃ r ∈ m, r.1 = false) ∧ (∃ r ∈ m, r.2 = true) ∧ (∃ r ∈ m, r.2 = false)

instance : DecidablePred IsEFOLPattern := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The Keynes–Johnson octagon for subject negation lists *all*, *some*, *no* and *not all* `S`
are `P`, then the same with non-`S` (Definition 2). -/
def subjectNegation : Fin 8 → Finset {m // IsEFOLPattern m} := ![
  univ.filter fun m ↦ every (InS m.1) (InP m.1),
  univ.filter fun m ↦ Det.some (InS m.1) (InP m.1),
  univ.filter fun m ↦ no (InS m.1) (InP m.1),
  univ.filter fun m ↦ ¬ every (InS m.1) (InP m.1),
  univ.filter fun m ↦ every (InS m.1)ᶜ (InP m.1),
  univ.filter fun m ↦ Det.some (InS m.1)ᶜ (InP m.1),
  univ.filter fun m ↦ no (InS m.1)ᶜ (InP m.1),
  univ.filter fun m ↦ ¬ every (InS m.1)ᶜ (InP m.1)]

/-- The octagon for subject negation induces a partition of seven cells, so its Boolean closure
has `2 ^ 7` elements. -/
theorem card_minterms_subjectNegation : #(Finpartition.minterms subjectNegation).parts = 7 := by
  decide +kernel

/-! ### Deontic logic (Section 4) -/

/-- A KD world type records the value of `p` at a world and the nonempty set of its values at
the world's successors. -/
abbrev KDType := Bool × {s : Finset Bool // s.Nonempty}

/-- In the canonical model of a type, the evaluation world `none` sees one world for each value
at its successors, and each of those sees itself. -/
def Succ (t : KDType) : Option Bool → Option Bool → Prop
  | none, some v => v ∈ t.2.1
  | some v, some v' => v = v'
  | _, none => False

instance (t : KDType) (w v : Option Bool) : Decidable (Succ t w v) := by
  cases w <;> cases v <;> unfold Succ <;> infer_instance

/-- The accessibility relation of the canonical model of a type. -/
def access (t : KDType) : SetRel (Option Bool) (Option Bool) := {wv | Succ t wv.1 wv.2}

instance (t : KDType) (w v : Option Bool) : Decidable (w ~[access t] v) :=
  inferInstanceAs (Decidable (Succ t w v))

/-- The valuation of `p` in the canonical model of a type. -/
def Val (t : KDType) : Option Bool → Prop
  | none => t.1 = true
  | some v => v = true

instance (t : KDType) : DecidablePred (Val t) := by
  intro w; cases w <;> unfold Val <;> infer_instance

/-- The Keynes–Johnson octagon for deontic logic, with permission `◇` and obligation `□`, each
formula at the position of the subject-negation statement `δ` sends to it (Definition 8). -/
def deontic : Fin 8 → Finset KDType := ![
  univ.filter fun t ↦ Val t none ∧ ◇[access t] (Val t) none,
  univ.filter fun t ↦ Val t none ∨ □[access t] (fun w ↦ ¬ Val t w) none,
  univ.filter fun t ↦ ¬ Val t none ∧ ◇[access t] (Val t) none,
  univ.filter fun t ↦ ¬ Val t none ∨ □[access t] (fun w ↦ ¬ Val t w) none,
  univ.filter fun t ↦ ¬ Val t none ∧ ◇[access t] (fun w ↦ ¬ Val t w) none,
  univ.filter fun t ↦ ¬ Val t none ∨ □[access t] (Val t) none,
  univ.filter fun t ↦ Val t none ∧ ◇[access t] (fun w ↦ ¬ Val t w) none,
  univ.filter fun t ↦ Val t none ∨ □[access t] (Val t) none]

/-- The deontic octagon induces a partition of six cells, so its Boolean closure has `2 ^ 6`
elements. -/
theorem card_minterms_deontic : #(Finpartition.minterms deontic).parts = 6 := by
  decide +kernel

/-- The deontic octagon is Aristotelian isomorphic to the octagon for subject negation, by the
map `δ`. -/
def deonticIso : AristotelianIso subjectNegation deontic where
  toEquiv := .refl _
  map_disjoint' := by decide +kernel
  map_codisjoint' := by simp only [codisjoint_iff]; decide +kernel
  map_le' := by decide +kernel

/-- The deontic octagon is not Boolean isomorphic to the octagon for subject negation, since
their closures have `2 ^ 6` and `2 ^ 7` elements. -/
theorem isEmpty_booleanIso_deontic : IsEmpty (BooleanIso subjectNegation deontic) :=
  ⟨fun e ↦ by
    have := (BooleanSubalgebra.nonempty_orderIso_closure_iff _ _).1 ⟨e.closureIso⟩
    rw [card_minterms_subjectNegation, card_minterms_deontic] at this
    exact absurd this (by decide)⟩

/-! ### Knowledge representation (Section 3) -/

/-- The region each subject-negation statement is about, and whether it says that region is
inhabited. -/
private def region : Fin 8 → (Bool × Bool) × Bool :=
  ![((true, false), false), ((true, true), true), ((true, true), false), ((true, false), true),
    ((false, false), false), ((false, true), true), ((false, true), false), ((false, false), true)]

private theorem mem_subjectNegation :
    ∀ i m, m ∈ subjectNegation i ↔ ((region i).1 ∈ m.1 ↔ (region i).2 = true) := by
  decide +kernel

section KnowledgeRep

variable {X Y : Type*} (R : SetRel X Y) (S : Set Y)

/-- The Keynes–Johnson octagon for knowledge representation (Definition 5), each set at the
position of the subject-negation statement `γ` sends to it; `R.preimage S` is `R(S)` and `Rᶜ` is
`R̄`. -/
def knowledgeRep : Fin 8 → Set X :=
  ![(Rᶜ.preimage S)ᶜ, R.preimage S, (R.preimage S)ᶜ, Rᶜ.preimage S,
    (Rᶜ.preimage Sᶜ)ᶜ, R.preimage Sᶜ, (R.preimage Sᶜ)ᶜ, Rᶜ.preimage Sᶜ]

variable {R S} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) (hR : ∀ x, ∃ y, x ~[R] y)
  (hRc : ∀ x, ∃ y, ¬ x ~[R] y)

/-- The pattern of `x` records which regions of `S` and `R[x]` are inhabited. The assumptions of
the paper, that `S` is nontrivial and that `R` and its complement are serial, make it an EFOL
pattern. -/
noncomputable def pattern (x : X) : {m // IsEFOLPattern m} :=
  ⟨regions (S, {y | x ~[R] y}), by
    classical
    have mem (y : Y) : (decide (y ∈ S), decide (x ~[R] y)) ∈ regions (S, {y | x ~[R] y}) :=
      mem_regions.2 ⟨y, by simp, by simp⟩
    obtain ⟨y₁, hy₁⟩ := hS
    obtain ⟨y₂, hy₂⟩ := hSc
    obtain ⟨y₃, hy₃⟩ := hR x
    obtain ⟨y₄, hy₄⟩ := hRc x
    exact ⟨⟨_, mem y₁, by simpa using hy₁⟩, ⟨_, mem y₂, by simpa using hy₂⟩,
      ⟨_, mem y₃, by simpa using hy₃⟩, ⟨_, mem y₄, by simpa using hy₄⟩⟩⟩

theorem mem_pattern {x : X} {r : Bool × Bool} :
    r ∈ (pattern hS hSc hR hRc x).1 ↔ ∃ y, (y ∈ S ↔ r.1 = true) ∧ (x ~[R] y ↔ r.2 = true) :=
  mem_regions

theorem knowledgeRep_eq :
    knowledgeRep R S = fun i ↦ pattern hS hSc hR hRc ⁻¹' ↑(subjectNegation i) := by
  funext i
  ext x
  change x ∈ knowledgeRep R S i ↔ pattern hS hSc hR hRc x ∈ subjectNegation i
  rw [mem_subjectNegation, mem_pattern]
  fin_cases i <;> simp [knowledgeRep, region]

/-- When every pattern is realized, the octagon for knowledge representation is Boolean isomorphic
to the octagon for subject negation, by the map `γ`. -/
noncomputable def knowledgeRepIso (h : Surjective (pattern hS hSc hR hRc)) :
    BooleanIso subjectNegation (knowledgeRep R S) :=
  (knowledgeRep_eq hS hSc hR hRc).symm ▸ BooleanIso.ofSurjective _ h

open Classical in
theorem card_minterms_knowledgeRep (h : Surjective (pattern hS hSc hR hRc)) :
    #(Finpartition.minterms (knowledgeRep R S)).parts = 7 :=
  card_minterms_subjectNegation ▸ ((BooleanSubalgebra.nonempty_orderIso_closure_iff _ _).1
    ⟨(knowledgeRepIso hS hSc hR hRc h).closureIso⟩).symm

end KnowledgeRep

/-! ### Models -/

section EFOLModels

variable {D : Type*}

/-- An EFOL model interprets `S` and `P` over the domain `D` with `S`, non-`S`, `P` and non-`P`
each inhabited. -/
def IsEFOLModel (m : Set D × Set D) : Prop :=
  m.1.Nonempty ∧ m.1ᶜ.Nonempty ∧ m.2.Nonempty ∧ m.2ᶜ.Nonempty

/-- The octagon for subject negation over the EFOL models with domain `D`. -/
def subjectNegationModels (D : Type*) :
    Fin 8 → Set {m : Set D × Set D // IsEFOLModel m} :=
  ![{m | every m.1.1 m.1.2}, {m | Det.some m.1.1 m.1.2}, {m | no m.1.1 m.1.2},
    {m | ¬ every m.1.1 m.1.2}, {m | every m.1.1ᶜ m.1.2}, {m | Det.some m.1.1ᶜ m.1.2},
    {m | no m.1.1ᶜ m.1.2}, {m | ¬ every m.1.1ᶜ m.1.2}]

/-- The type of an EFOL model is the set of regions it inhabits. -/
noncomputable def efolType (m : {m : Set D × Set D // IsEFOLModel m}) : {n // IsEFOLPattern n} :=
  ⟨regions m.1, by
    classical
    obtain ⟨⟨x₁, h₁⟩, ⟨x₂, h₂⟩, ⟨x₃, h₃⟩, ⟨x₄, h₄⟩⟩ := m.2
    have mem (x : D) : (decide (x ∈ m.1.1), decide (x ∈ m.1.2)) ∈ regions m.1 :=
      mem_regions.2 ⟨x, by simp, by simp⟩
    exact ⟨⟨_, mem x₁, by simpa using h₁⟩, ⟨_, mem x₂, by simpa using h₂⟩,
      ⟨_, mem x₃, by simpa using h₃⟩, ⟨_, mem x₄, by simpa using h₄⟩⟩⟩

-- A subject-negation statement holds of an EFOL model iff it holds of the canonical model of the
-- model's type.
theorem subjectNegationModels_eq :
    subjectNegationModels D = fun i ↦ efolType ⁻¹' ↑(subjectNegation i) := by
  funext i
  ext m
  change m ∈ subjectNegationModels D i ↔ efolType m ∈ subjectNegation i
  rw [mem_subjectNegation]
  fin_cases i <;>
    simp [subjectNegationModels, region, efolType, mem_regions, every, no, Det.some,
      Set.subset_def, Set.Nonempty, not_imp_not]

theorem efolType_surjective [Fintype D] (hD : 4 ≤ Fintype.card D) :
    Surjective (efolType (D := D)) := by
  rintro ⟨n, hn⟩
  obtain ⟨m, hm⟩ := exists_regions_eq hD (hn.1.imp fun _ h ↦ h.1)
  refine ⟨⟨m, ?_⟩, Subtype.ext hm⟩
  obtain ⟨⟨r₁, h₁, e₁⟩, ⟨r₂, h₂, e₂⟩, ⟨r₃, h₃, e₃⟩, ⟨r₄, h₄, e₄⟩⟩ := hn
  rw [← hm] at h₁ h₂ h₃ h₄
  obtain ⟨x₁, a₁, -⟩ := mem_regions.1 h₁
  obtain ⟨x₂, a₂, -⟩ := mem_regions.1 h₂
  obtain ⟨x₃, -, a₃⟩ := mem_regions.1 h₃
  obtain ⟨x₄, -, a₄⟩ := mem_regions.1 h₄
  exact ⟨⟨x₁, a₁.2 e₁⟩, ⟨x₂, fun h ↦ by simpa [e₂] using a₂.1 h⟩, ⟨x₃, a₃.2 e₃⟩,
    ⟨x₄, fun h ↦ by simpa [e₄] using a₄.1 h⟩⟩

/-- Over a domain of at least four individuals, the EFOL models realize every pattern. -/
noncomputable def subjectNegationModelsIso [Fintype D] (hD : 4 ≤ Fintype.card D) :
    BooleanIso subjectNegation (subjectNegationModels D) :=
  (subjectNegationModels_eq (D := D)).symm ▸
    BooleanIso.ofSurjective efolType (efolType_surjective hD)

end EFOLModels

section KDModels

variable {W : Type*}

/-- A KD model on the worlds `W` has a serial accessibility relation, a valuation of `p` and an
evaluation world. -/
def IsKDModel (m : SetRel W W × (W → Prop) × W) : Prop := ∀ w, ∃ v, w ~[m.1] v

/-- The deontic octagon over the KD models on the worlds `W`. -/
def deonticModels (W : Type*) : Fin 8 → Set {m : SetRel W W × (W → Prop) × W // IsKDModel m} :=
  ![{m | m.1.2.1 m.1.2.2 ∧ ◇[m.1.1] m.1.2.1 m.1.2.2},
    {m | m.1.2.1 m.1.2.2 ∨ □[m.1.1] (fun v ↦ ¬ m.1.2.1 v) m.1.2.2},
    {m | ¬ m.1.2.1 m.1.2.2 ∧ ◇[m.1.1] m.1.2.1 m.1.2.2},
    {m | ¬ m.1.2.1 m.1.2.2 ∨ □[m.1.1] (fun v ↦ ¬ m.1.2.1 v) m.1.2.2},
    {m | ¬ m.1.2.1 m.1.2.2 ∧ ◇[m.1.1] (fun v ↦ ¬ m.1.2.1 v) m.1.2.2},
    {m | ¬ m.1.2.1 m.1.2.2 ∨ □[m.1.1] m.1.2.1 m.1.2.2},
    {m | m.1.2.1 m.1.2.2 ∧ ◇[m.1.1] (fun v ↦ ¬ m.1.2.1 v) m.1.2.2},
    {m | m.1.2.1 m.1.2.2 ∨ □[m.1.1] m.1.2.1 m.1.2.2}]

open Classical in
/-- The type of a KD model: the value of `p` at the evaluation world and its values at the world's
successors. -/
noncomputable def kdType (m : {m : SetRel W W × (W → Prop) × W // IsKDModel m}) : KDType :=
  (decide (m.1.2.1 m.1.2.2),
    ⟨univ.filter fun b ↦ ∃ v, m.1.2.2 ~[m.1.1] v ∧ (m.1.2.1 v ↔ b = true), by
      obtain ⟨v, hv⟩ := m.2 m.1.2.2
      exact ⟨decide (m.1.2.1 v), mem_filter.2 ⟨mem_univ _, v, hv, by simp⟩⟩⟩)

private theorem val_none {t : KDType} : Val t none ↔ t.1 = true := .rfl
private theorem dia_access {t : KDType} : ◇[access t] (Val t) none ↔ true ∈ t.2.1 := by
  revert t; decide
private theorem dia_access_not {t : KDType} :
    ◇[access t] (fun w ↦ ¬ Val t w) none ↔ false ∈ t.2.1 := by
  revert t; decide
private theorem box_access {t : KDType} : □[access t] (Val t) none ↔ false ∉ t.2.1 := by
  revert t; decide
private theorem box_access_not {t : KDType} :
    □[access t] (fun w ↦ ¬ Val t w) none ↔ true ∉ t.2.1 := by
  revert t; decide

-- A deontic formula holds of a KD model iff it holds of the canonical model of the model's type.
theorem deonticModels_eq : deonticModels W = fun i ↦ kdType ⁻¹' ↑(deontic i) := by
  funext i
  ext m
  fin_cases i <;>
    simp only [deonticModels, deontic, Set.mem_preimage, Finset.mem_coe, val_none, dia_access,
      dia_access_not, box_access, box_access_not] <;>
    simp [kdType, Box, Diamond]

theorem kdType_surjective [Fintype W] (hW : 3 ≤ Fintype.card W) : Surjective (kdType (W := W)) := by
  rintro ⟨a, s, hs⟩
  obtain ⟨e⟩ : Nonempty (Option s ↪ W) := Function.Embedding.nonempty_of_card_le <| by
    rw [Fintype.card_option, Fintype.card_coe]
    exact (Nat.succ_le_succ ((card_le_univ s).trans (by simp))).trans hW
  have : Nonempty (Option s) := ⟨none⟩
  have hl := Function.leftInverse_invFun e.injective
  set V : W → Prop := fun v ↦ (Function.invFun e v).elim (a = true) fun b ↦ b.1 = true
  set R : SetRel W W := {xy | ∃ b : s, xy.2 = e (some b)}
  obtain ⟨b₀, hb₀⟩ := hs
  refine ⟨⟨(R, V, e none), fun _ ↦ ⟨e (some ⟨b₀, hb₀⟩), ⟨b₀, hb₀⟩, rfl⟩⟩, ?_⟩
  refine Prod.ext (by simp [kdType, V, hl none]) (Subtype.ext <| Finset.ext fun b ↦ ?_)
  simp only [kdType, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨v, ⟨c, rfl⟩, hv⟩
    simp only [V, hl (some c), Option.elim_some] at hv
    exact (Bool.eq_iff_iff.2 hv) ▸ c.2
  · intro hb
    exact ⟨e (some ⟨b, hb⟩), ⟨⟨b, hb⟩, rfl⟩, by simp [V, hl (some ⟨b, hb⟩)]⟩

/-- On at least three worlds, the KD models realize every type. -/
noncomputable def deonticModelsIso [Fintype W] (hW : 3 ≤ Fintype.card W) :
    BooleanIso deontic (deonticModels W) :=
  (deonticModels_eq (W := W)).symm ▸ BooleanIso.ofSurjective kdType (kdType_surjective hW)

end KDModels

/-- Over a domain of at least four individuals and on at least three worlds, the deontic octagon
of KD models is not Boolean isomorphic to the octagon for subject negation of EFOL models. -/
theorem isEmpty_booleanIso_deonticModels {D W : Type*} [Fintype D] [Fintype W]
    (hD : 4 ≤ Fintype.card D) (hW : 3 ≤ Fintype.card W) :
    IsEmpty (BooleanIso (subjectNegationModels D) (deonticModels W)) :=
  ⟨fun e ↦ isEmpty_booleanIso_deontic.false
    ((subjectNegationModelsIso hD).trans (e.trans (deonticModelsIso hW).symm))⟩

/-! ### The family of Keynes–Johnson octagons (Section 5) -/

-- Definition 10: seven polarity assignments are consistent with the relations of the octagon.
theorem card_filter_consistent : #(univ.filter (Consistent subjectNegation)) = 7 := by
  decide +kernel

/-- The six meets of two corners among the consistent assignments, `ε₁` to `ε₆`. -/
private def pairs : Finset (Fin 8 × Fin 8) := {(0, 6), (0, 5), (2, 4), (2, 7), (3, 6), (1, 4)}

/-- The polarity assignment of the meet of two corners. -/
private def polarity (t : Fin 8 × Fin 8) (k : Fin 8) : Bool :=
  decide (subjectNegation t.1 ⊓ subjectNegation t.2 ≤ subjectNegation k)

-- Each of the six is consistent, and each of its literals lies above one of its two corners, so
-- it is the meet of two corners in every octagon of the family.
private theorem consistent_pairs : ∀ t ∈ pairs, Consistent subjectNegation (polarity t) ∧
    ∀ k, literal (subjectNegation t.1) (polarity t t.1) ≤
        literal (subjectNegation k) (polarity t k) ∨
      literal (subjectNegation t.2) (polarity t t.2) ≤
        literal (subjectNegation k) (polarity t k) := by
  decide +kernel

private theorem card_image_polarity : #(pairs.image polarity) = 6 := by
  decide +kernel

variable {α : Type*} [BooleanAlgebra α] [DecidableEq α] {φ : Fin 8 → α}

private theorem image_polarity_subset (e : AristotelianIso subjectNegation φ) :
    pairs.image polarity ⊆ univ.filter fun σ ↦ minterm (φ ∘ e.toEquiv) σ ≠ ⊥ :=
  image_subset_iff.2 fun t ht ↦ mem_filter.2
    ⟨mem_univ _, e.minterm_ne_bot_of_consistent (consistent_pairs t ht).1 (consistent_pairs t ht).2⟩

private theorem minterm_ne_bot_iff_mem_image (e : AristotelianIso subjectNegation φ)
    (h : #(Finpartition.minterms φ).parts = 6) (σ : Fin 8 → Bool) :
    minterm (φ ∘ e.toEquiv) σ ≠ ⊥ ↔ σ ∈ pairs.image polarity := by
  have := eq_of_subset_of_card_le (image_polarity_subset e) <| by
    rw [card_image_polarity, ← Finpartition.card_parts_minterms,
      Finpartition.parts_minterms_comp_equiv, h]
  simpa using congrArg (σ ∈ ·) this.symm

/-- Every Keynes–Johnson octagon, in any Boolean algebra, induces a partition of six or of seven
cells. Its nonzero minterms are among the seven consistent ones, six of which are meets of two
corners and so nonzero; the seventh may or may not vanish. -/
theorem card_minterms_eq_six_or_seven (e : AristotelianIso subjectNegation φ) :
    #(Finpartition.minterms φ).parts = 6 ∨ #(Finpartition.minterms φ).parts = 7 := by
  have h₁ := card_le_card (image_polarity_subset e)
  rw [card_image_polarity, ← Finpartition.card_parts_minterms,
    Finpartition.parts_minterms_comp_equiv] at h₁
  have h₂ := e.card_parts_minterms_le
  rw [card_filter_consistent] at h₂
  omega

/-- A Keynes–Johnson octagon is Boolean isomorphic to the octagon for subject negation iff it
induces seven cells, its nonzero minterms then being the seven consistent ones. -/
theorem nonempty_booleanIso_subjectNegation_iff (e : AristotelianIso subjectNegation φ) :
    Nonempty (BooleanIso subjectNegation φ) ↔ #(Finpartition.minterms φ).parts = 7 where
  mp := fun ⟨b⟩ ↦ (BooleanSubalgebra.nonempty_orderIso_closure_iff _ _).1 ⟨b.closureIso⟩ ▸
    card_minterms_subjectNegation
  mpr h := ⟨.ofMintermEqBot e.toEquiv fun _ ↦ not_iff_not.1 <|
    ((AristotelianIso.refl _).minterm_ne_bot_iff_of_card_eq
      (card_minterms_subjectNegation.trans card_filter_consistent.symm)).trans
      (e.minterm_ne_bot_iff_of_card_eq (h.trans card_filter_consistent.symm)).symm⟩

/-- A Keynes–Johnson octagon is Boolean isomorphic to the deontic octagon iff it induces six
cells, its nonzero minterms then being the six meets of two corners. -/
theorem nonempty_booleanIso_deontic_iff (e : AristotelianIso subjectNegation φ) :
    Nonempty (BooleanIso deontic φ) ↔ #(Finpartition.minterms φ).parts = 6 where
  mp := fun ⟨b⟩ ↦ (BooleanSubalgebra.nonempty_orderIso_closure_iff _ _).1 ⟨b.closureIso⟩ ▸
    card_minterms_deontic
  mpr h := ⟨.ofMintermEqBot e.toEquiv fun σ ↦ not_iff_not.1 <|
    (minterm_ne_bot_iff_mem_image deonticIso card_minterms_deontic σ).trans
      (minterm_ne_bot_iff_mem_image e h σ).symm⟩

omit [DecidableEq α] in
/-- The Keynes–Johnson octagons form exactly two Boolean subfamilies, each octagon being Boolean
isomorphic to the octagon for subject negation or to the deontic octagon, which are not Boolean
isomorphic to each other (`isEmpty_booleanIso_deontic`). -/
theorem nonempty_booleanIso_subjectNegation_or_deontic (e : AristotelianIso subjectNegation φ) :
    Nonempty (BooleanIso subjectNegation φ) ∨ Nonempty (BooleanIso deontic φ) := by
  classical
  exact (card_minterms_eq_six_or_seven e).symm.imp (nonempty_booleanIso_subjectNegation_iff e).2
    (nonempty_booleanIso_deontic_iff e).2

end DemeySmessaert2024
