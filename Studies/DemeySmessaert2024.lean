module

public import Linglib.Logic.Aristotelian.Morphism
public import Linglib.Logic.Modal.Basic
public import Linglib.Semantics.Quantification.Basic
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
proposition is a set of EFOL patterns, each read on its canonical model; a deontic formula is
likewise a set of KD world types. The octagons are indexed by the subject-negation positions, so
`γ` and `δ` are the identity, and Section 5's generic description is the subject-negation
octagon's. The knowledge-representation octagon assumes, as the paper does tacitly, that `X`
realizes every pattern. The paper identifies the Boolean subfamilies with the sizes of the
closures; here two octagons of one size are shown to have minterms vanishing at the same polarity
assignments, which makes their Aristotelian isomorphism a Boolean one.

## References

* [demey-smessaert-2024]
-/

@[expose] public section

namespace DemeySmessaert2024

open Finset Function Quantifier Quantifier.GQ Aristotelian ModalLogic SetRel

/-! ### Subject negation (Section 2) -/

/-- A finite set of regions, a region recording whether an individual is `S` and whether it is
`P`, is an EFOL pattern when `S`, non-`S`, `P` and non-`P` are each inhabited. -/
def IsEFOLPattern (m : Finset (Bool × Bool)) : Prop :=
  (∃ r ∈ m, r.1 = true) ∧ (∃ r ∈ m, r.1 = false) ∧ (∃ r ∈ m, r.2 = true) ∧ (∃ r ∈ m, r.2 = false)

instance : DecidablePred IsEFOLPattern := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- In the canonical model of a pattern, whose individuals are its regions, `S` holds of the
regions inside `S`. -/
def InS (m : Finset (Bool × Bool)) (r : m) : Prop := r.1.1 = true

/-- In the canonical model of a pattern, `P` holds of the regions inside `P`. -/
def InP (m : Finset (Bool × Bool)) (r : m) : Prop := r.1.2 = true

instance (m : Finset (Bool × Bool)) : DecidablePred (InS m) :=
  fun _ ↦ inferInstanceAs (Decidable (_ = _))

instance (m : Finset (Bool × Bool)) : DecidablePred (InP m) :=
  fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- The Keynes–Johnson octagon for subject negation lists *all*, *some*, *no* and *not all* `S`
are `P`, then the same with non-`S` (Definition 2). -/
def subjectNegation : Fin 8 → Finset {m // IsEFOLPattern m} := ![
  univ.filter fun m ↦ every (InS m.1) (InP m.1),
  univ.filter fun m ↦ GQ.some (InS m.1) (InP m.1),
  univ.filter fun m ↦ no (InS m.1) (InP m.1),
  univ.filter fun m ↦ ¬ every (InS m.1) (InP m.1),
  univ.filter fun m ↦ every (fun r ↦ ¬ InS m.1 r) (InP m.1),
  univ.filter fun m ↦ GQ.some (fun r ↦ ¬ InS m.1 r) (InP m.1),
  univ.filter fun m ↦ no (fun r ↦ ¬ InS m.1 r) (InP m.1),
  univ.filter fun m ↦ ¬ every (fun r ↦ ¬ InS m.1 r) (InP m.1)]

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
  map_disjoint := by decide +kernel
  map_codisjoint := by simp only [codisjoint_iff]; decide +kernel
  map_lt := by decide +kernel

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

open Classical in
/-- The pattern of `x` records which regions of `S` and `R[x]` are inhabited. The assumptions of
the paper, that `S` is nontrivial and that `R` and its complement are serial, make it an EFOL
pattern. -/
noncomputable def pattern (x : X) : {m // IsEFOLPattern m} :=
  ⟨univ.filter fun r ↦ ∃ y, (y ∈ S ↔ r.1 = true) ∧ (x ~[R] y ↔ r.2 = true), by
    have mem (y : Y) : (decide (y ∈ S), decide (x ~[R] y)) ∈
        univ.filter fun r ↦ ∃ y, (y ∈ S ↔ r.1 = true) ∧ (x ~[R] y ↔ r.2 = true) := by
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨y, by simp, by simp⟩
    obtain ⟨y₁, hy₁⟩ := hS
    obtain ⟨y₂, hy₂⟩ := hSc
    obtain ⟨y₃, hy₃⟩ := hR x
    obtain ⟨y₄, hy₄⟩ := hRc x
    exact ⟨⟨_, mem y₁, by simpa using hy₁⟩, ⟨_, mem y₂, by simpa using hy₂⟩,
      ⟨_, mem y₃, by simpa using hy₃⟩, ⟨_, mem y₄, by simpa using hy₄⟩⟩⟩

theorem mem_pattern {x : X} {r : Bool × Bool} :
    r ∈ (pattern hS hSc hR hRc x).1 ↔ ∃ y, (y ∈ S ↔ r.1 = true) ∧ (x ~[R] y ↔ r.2 = true) := by
  simp [pattern]

/-- Pulling a set of patterns back along `pattern` is a Boolean homomorphism. -/
noncomputable def pullback : BoundedLatticeHom (Finset {m // IsEFOLPattern m}) (Set X) where
  toFun s := pattern hS hSc hR hRc ⁻¹' ↑s
  map_sup' _ _ := by simp
  map_inf' _ _ := by simp
  map_top' := by simp
  map_bot' := by simp

theorem knowledgeRep_eq : knowledgeRep R S = pullback hS hSc hR hRc ∘ subjectNegation := by
  funext i
  ext x
  change x ∈ knowledgeRep R S i ↔ pattern hS hSc hR hRc x ∈ subjectNegation i
  rw [mem_subjectNegation, mem_pattern]
  fin_cases i <;> simp [knowledgeRep, region]

/-- When every pattern is realized, the octagon for knowledge representation is Boolean isomorphic
to the octagon for subject negation, by the map `γ`. -/
noncomputable def knowledgeRepIso (h : Surjective (pattern hS hSc hR hRc)) :
    BooleanIso subjectNegation (knowledgeRep R S) :=
  (knowledgeRep_eq hS hSc hR hRc).symm ▸ BooleanIso.ofInjective (pullback hS hSc hR hRc)
    fun _ _ hst ↦ Finset.coe_injective ((Set.preimage_injective.2 h) hst)

open Classical in
theorem card_minterms_knowledgeRep (h : Surjective (pattern hS hSc hR hRc)) :
    #(Finpartition.minterms (knowledgeRep R S)).parts = 7 :=
  card_minterms_subjectNegation ▸ ((BooleanSubalgebra.nonempty_orderIso_closure_iff _ _).1
    ⟨(knowledgeRepIso hS hSc hR hRc h).closureIso⟩).symm

end KnowledgeRep

/-! ### The family of Keynes–Johnson octagons (Section 5) -/

/-- A polarity assignment is consistent with the Keynes–Johnson configuration when its meet
contains no two contrary or contradictory literals (Definition 9). No two true corners are
disjoint, no two false corners are jointly exhaustive, and no true corner lies below a false
one. -/
def Consistent (σ : Fin 8 → Bool) : Prop :=
  ∀ i j, ¬ (σ i = true ∧ σ j = true ∧ Disjoint (subjectNegation i) (subjectNegation j)) ∧
    ¬ (σ i = false ∧ σ j = false ∧ subjectNegation i ⊔ subjectNegation j = ⊤) ∧
    ¬ (σ i = true ∧ σ j = false ∧ subjectNegation i < subjectNegation j)

instance : DecidablePred Consistent := fun _ ↦ by unfold Consistent; infer_instance

theorem card_filter_consistent : #(univ.filter Consistent) = 7 := by decide +kernel

/-- The meets of two corners among the consistent minterms. -/
private def pairs : Finset (Fin 8 × Fin 8) := {(0, 6), (0, 5), (2, 4), (2, 7), (3, 6), (1, 4)}

/-- The polarity assignment of the meet of two corners. -/
private def polarity (t : Fin 8 × Fin 8) (k : Fin 8) : Bool :=
  decide (subjectNegation t.1 ⊓ subjectNegation t.2 ≤ subjectNegation k)

/-- A positive literal `k` of the polarity assignment of `t` lies above the meet of `t`, by the
relations of the octagon. -/
private def CoversPos (t : Fin 8 × Fin 8) (k : Fin 8) : Prop :=
  polarity t k = true → k = t.1 ∨ k = t.2 ∨ subjectNegation t.1 < subjectNegation k ∨
    subjectNegation t.2 < subjectNegation k

/-- A negative literal `k` of the polarity assignment of `t` lies above the meet of `t`, by the
relations of the octagon. -/
private def CoversNeg (t : Fin 8 × Fin 8) (k : Fin 8) : Prop :=
  polarity t k = false → Disjoint (subjectNegation t.1) (subjectNegation k) ∨
    Disjoint (subjectNegation t.2) (subjectNegation k)

private instance (t : Fin 8 × Fin 8) : DecidablePred (CoversPos t) := fun _ ↦ by
  unfold CoversPos; infer_instance

private instance (t : Fin 8 × Fin 8) : DecidablePred (CoversNeg t) := fun _ ↦ by
  unfold CoversNeg; infer_instance

/-- The certificate that the meet of a pair is nonzero and below the minterm of its polarity
assignment. -/
private def Certified (t : Fin 8 × Fin 8) : Prop :=
  ¬ Disjoint (subjectNegation t.1) (subjectNegation t.2) ∧ ∀ k, CoversPos t k ∧ CoversNeg t k

private instance : DecidablePred Certified := fun _ ↦ by unfold Certified; infer_instance

private theorem certified : ∀ t ∈ pairs, Certified t := by decide +kernel

private theorem card_image_polarity : #(pairs.image polarity) = 6 := by
  decide +kernel

section Family

variable {α : Type*} [BooleanAlgebra α] {ψ : Fin 8 → α}
  (hD : ∀ i j, Disjoint (subjectNegation i) (subjectNegation j) ↔ Disjoint (ψ i) (ψ j))
  (hC : ∀ i j, Codisjoint (subjectNegation i) (subjectNegation j) ↔ Codisjoint (ψ i) (ψ j))
  (hL : ∀ i j, subjectNegation i < subjectNegation j ↔ ψ i < ψ j)

include hD hC hL in
private theorem consistent_of_minterm_ne_bot {σ : Fin 8 → Bool} (h : minterm ψ σ ≠ ⊥) :
    Consistent σ :=
  fun i j ↦ ⟨fun ⟨hi, hj, hd⟩ ↦ h <| le_bot_iff.1 <|
      (le_inf (minterm_le_of_true hi) (minterm_le_of_true hj)).trans
        (disjoint_iff_inf_le.1 ((hD i j).1 hd)),
    fun ⟨hi, hj, hc⟩ ↦ h <| le_bot_iff.1 <|
      (le_inf (minterm_le_compl_of_false hi) (minterm_le_compl_of_false hj)).trans_eq <| by
        rw [← compl_sup, codisjoint_iff.1 ((hC i j).1 (codisjoint_iff.2 hc)), compl_top],
    fun ⟨hi, hj, hl⟩ ↦ h <| le_bot_iff.1 <|
      (le_inf ((minterm_le_of_true hi).trans ((hL i j).1 hl).le)
        (minterm_le_compl_of_false hj)).trans_eq (inf_compl_self _)⟩

include hD hL in
private theorem minterm_polarity_ne_bot {t : Fin 8 × Fin 8} (ht : t ∈ pairs) :
    minterm ψ (polarity t) ≠ ⊥ := by
  have h := certified t ht
  refine fun h0 ↦ (hD _ _).not.1 h.1 (disjoint_iff.2 (le_bot_iff.1 ?_))
  refine (Finset.le_inf fun k _ ↦ ?_).trans_eq h0
  cases hk : polarity t k
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases (h.2 k).2 hk with hd | hd
    · exact inf_le_left.trans ((hD _ _).1 hd).le_compl_right
    · exact inf_le_right.trans ((hD _ _).1 hd).le_compl_right
  · simp only [↓reduceIte]
    rcases (h.2 k).1 hk with rfl | rfl | hl | hl
    · exact inf_le_left
    · exact inf_le_right
    · exact inf_le_left.trans ((hL _ _).1 hl).le
    · exact inf_le_right.trans ((hL _ _).1 hl).le

variable [DecidableEq α]

include hD hC hL in
private theorem filter_minterm_ne_bot_subset :
    (univ.filter fun σ ↦ minterm ψ σ ≠ ⊥) ⊆ univ.filter Consistent :=
  fun _ hσ ↦ mem_filter.2 ⟨mem_univ _, consistent_of_minterm_ne_bot hD hC hL (mem_filter.1 hσ).2⟩

include hD hL in
private theorem image_polarity_subset :
    pairs.image polarity ⊆ univ.filter fun σ ↦ minterm ψ σ ≠ ⊥ :=
  image_subset_iff.2 fun _ ht ↦ mem_filter.2 ⟨mem_univ _, minterm_polarity_ne_bot hD hL ht⟩

include hD hC hL in
private theorem minterm_ne_bot_iff_consistent (h : #(Finpartition.minterms ψ).parts = 7)
    (σ : Fin 8 → Bool) : minterm ψ σ ≠ ⊥ ↔ Consistent σ := by
  have := eq_of_subset_of_card_le (filter_minterm_ne_bot_subset hD hC hL) <| by
    rw [card_filter_consistent, ← Finpartition.card_parts_minterms, h]
  simpa using congrArg (σ ∈ ·) this

include hD hL in
private theorem minterm_ne_bot_iff_mem_image (h : #(Finpartition.minterms ψ).parts = 6)
    (σ : Fin 8 → Bool) : minterm ψ σ ≠ ⊥ ↔ σ ∈ pairs.image polarity := by
  have := eq_of_subset_of_card_le (image_polarity_subset hD hL) <| by
    rw [card_image_polarity, ← Finpartition.card_parts_minterms, h]
  simpa using congrArg (σ ∈ ·) this.symm

end Family

variable {α : Type*} [BooleanAlgebra α] {φ : Fin 8 → α}

/-- Every Keynes–Johnson octagon, in any Boolean algebra, induces a partition of six or of seven
cells. Its nonzero minterms are among the seven consistent ones, six of which are meets of two
corners and so nonzero; the seventh may or may not vanish. -/
theorem card_minterms_eq_six_or_seven [DecidableEq α] (e : AristotelianIso subjectNegation φ) :
    #(Finpartition.minterms φ).parts = 6 ∨ #(Finpartition.minterms φ).parts = 7 := by
  rw [← Finpartition.parts_minterms_comp_equiv e.toEquiv, Finpartition.card_parts_minterms]
  have h₁ := card_le_card (image_polarity_subset (ψ := φ ∘ e.toEquiv) e.map_disjoint e.map_lt)
  have h₂ := card_le_card (filter_minterm_ne_bot_subset (ψ := φ ∘ e.toEquiv) e.map_disjoint
    e.map_codisjoint e.map_lt)
  rw [card_image_polarity] at h₁
  rw [card_filter_consistent] at h₂
  omega

/-- A Keynes–Johnson octagon is Boolean isomorphic to the octagon for subject negation iff it
induces seven cells, its nonzero minterms then being the seven consistent ones. -/
theorem nonempty_booleanIso_subjectNegation_iff [DecidableEq α]
    (e : AristotelianIso subjectNegation φ) :
    Nonempty (BooleanIso subjectNegation φ) ↔ #(Finpartition.minterms φ).parts = 7 where
  mp := fun ⟨b⟩ ↦ (BooleanSubalgebra.nonempty_orderIso_closure_iff _ _).1 ⟨b.closureIso⟩ ▸
    card_minterms_subjectNegation
  mpr h := ⟨.ofMintermEqBot e.toEquiv fun σ ↦ not_iff_not.1 <|
    (minterm_ne_bot_iff_consistent (ψ := subjectNegation) (fun _ _ ↦ .rfl) (fun _ _ ↦ .rfl)
      (fun _ _ ↦ .rfl) card_minterms_subjectNegation σ).trans
    (minterm_ne_bot_iff_consistent (ψ := φ ∘ e.toEquiv) e.map_disjoint e.map_codisjoint e.map_lt
      (by rwa [Finpartition.parts_minterms_comp_equiv]) σ).symm⟩

/-- A Keynes–Johnson octagon is Boolean isomorphic to the deontic octagon iff it induces six
cells, its nonzero minterms then being the six meets of two corners. -/
theorem nonempty_booleanIso_deontic_iff [DecidableEq α] (e : AristotelianIso subjectNegation φ) :
    Nonempty (BooleanIso deontic φ) ↔ #(Finpartition.minterms φ).parts = 6 where
  mp := fun ⟨b⟩ ↦ (BooleanSubalgebra.nonempty_orderIso_closure_iff _ _).1 ⟨b.closureIso⟩ ▸
    card_minterms_deontic
  mpr h := ⟨.ofMintermEqBot e.toEquiv fun σ ↦ not_iff_not.1 <|
    (minterm_ne_bot_iff_mem_image (ψ := deontic) deonticIso.map_disjoint deonticIso.map_lt
      card_minterms_deontic σ).trans
    (minterm_ne_bot_iff_mem_image (ψ := φ ∘ e.toEquiv) e.map_disjoint e.map_lt
      (by rwa [Finpartition.parts_minterms_comp_equiv]) σ).symm⟩

/-- The Keynes–Johnson octagons form exactly two Boolean subfamilies, each octagon being Boolean
isomorphic to the octagon for subject negation or to the deontic octagon, which are not Boolean
isomorphic to each other (`isEmpty_booleanIso_deontic`). -/
theorem nonempty_booleanIso_subjectNegation_or_deontic (e : AristotelianIso subjectNegation φ) :
    Nonempty (BooleanIso subjectNegation φ) ∨ Nonempty (BooleanIso deontic φ) := by
  classical
  exact (card_minterms_eq_six_or_seven e).symm.imp (nonempty_booleanIso_subjectNegation_iff e).2
    (nonempty_booleanIso_deontic_iff e).2

end DemeySmessaert2024
