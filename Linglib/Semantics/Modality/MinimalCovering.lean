module

public import Linglib.Core.Order.DeMorganAlgebra.Kalman
public import Linglib.Semantics.Questions.Basic
public import Mathlib.Order.Comparable

/-!
# Minimal covering semantics

Booth's semantics for modals over disjunctions ([booth-2022a], [booth-2022b]): a necessity modal
requires the alternatives of its prejacent to form a minimal cover of the relevant worlds, not
merely a cover, and a possibility modal requires them to minimally cover some nonempty set of
relevant worlds. Each alternative must then contribute a relevant world the others miss, which
yields the Independence inferences of free choice and blocks the Ross inference.

The unilateral modals `box` and `dia` act on inquisitive propositions (`Question W`), whose
alternatives let a modal see the disjuncts of its prejacent. The bilateral semantics assigns each
sentence a pair of inquisitive propositions, the states verifying and the states falsifying it,
overlapping only in the inconsistent state `∅`. These pairs are Kalman's construction over the
inquisitive algebra, `BilatInqProp W := Kalman (Question W)`, so negation swaps the pair and
conjunction and disjunction are the Kleene-lattice operations, with the De Morgan laws and double
negation for free. The bilateral modals are pairs of unilateral ones, `necessity = (box, dia)` and
`possibility = (dia, box)` applied to the two coordinates, so the duality of `□` and `◇` holds by
definition. Truth and falsity are the informative contents of the two coordinates, together the
Kleene homomorphism `BilatInqProp.info` into the partial propositions `Kalman (Set W)`: no sentence
is both true and false, but a modal sentence can be neither.

## Main definitions

* `MinimalCovering.IsMinCover`, `MinimalCovering.IsSuperCover`: minimal covers and the super
  covers of [simons-2005].
* `MinimalCovering.box`, `MinimalCovering.dia`: the unilateral modals.
* `MinimalCovering.BilatInqProp`: bilateral inquisitive propositions; `BilatInqProp.info`,
  `BilatInqProp.truth`, `BilatInqProp.falsity`.
* `MinimalCovering.atom`, `MinimalCovering.bang`, `MinimalCovering.necessity`,
  `MinimalCovering.possibility`, `MinimalCovering.updateAccess`: the clauses of the semantics.
* `MinimalCovering.Formula`, `MinimalCovering.Formula.eval`: the language and its interpretation,
  the restrictor conditional evaluating its consequent under the updated accessibility.

## Main results

* `MinimalCovering.isMinCover_iff`: a cover is minimal exactly when each member is needed.
* `MinimalCovering.IsMinCover.isSuperCover`: a minimal cover is a super cover.
* `MinimalCovering.possibility_eq_compl_necessity_compl`: the duality of the modals.
* `MinimalCovering.truth_necessity_of_alt_eq_singleton`,
  `MinimalCovering.truth_possibility_of_alt_eq_singleton`: over a single alternative the modals
  have their orthodox truth conditions.

## References

* [booth-2022a]
* [booth-2022b]
* [simons-2005]
* [ciardelli-groenendijk-roelofsen-2018]
* [kalman-1958]
-/

@[expose] public section

open Question

namespace MinimalCovering

variable {W : Type*}

/-! ### Covers -/

/-- `C` is a minimal cover of `S`: it covers `S`, `S ⊆ ⋃₀ C`, and no proper subfamily does. -/
def IsMinCover (C : Set (Set W)) (S : Set W) : Prop :=
  Minimal (fun X ↦ S ⊆ ⋃₀ X) C

theorem IsMinCover.subset_sUnion {C : Set (Set W)} {S : Set W} (h : IsMinCover C S) :
    S ⊆ ⋃₀ C :=
  h.prop

theorem isMinCover_iff {C : Set (Set W)} {S : Set W} :
    IsMinCover C S ↔ S ⊆ ⋃₀ C ∧ ∀ c ∈ C, ¬ S ⊆ ⋃₀ (C \ {c}) := by
  refine ⟨fun h ↦ ⟨h.prop, fun c hc hcov ↦ (h.le_of_le hcov Set.sdiff_subset hc).2 rfl⟩,
    fun ⟨hcov, hmin⟩ ↦ ⟨hcov, fun Y hY hYC ↦ ?_⟩⟩
  by_contra hCY
  obtain ⟨c, hcC, hcY⟩ := Set.not_subset.1 hCY
  exact hmin c hcC (hY.trans (Set.sUnion_mono fun d hd ↦ ⟨hYC hd, fun hdc ↦ hcY (hdc ▸ hd)⟩))

theorem isMinCover_empty_iff {C : Set (Set W)} : IsMinCover C ∅ ↔ C = ∅ := by
  refine ⟨fun h ↦ Set.subset_empty_iff.1 (h.le_of_le (Set.empty_subset _) (Set.empty_subset _)),
    fun h ↦ h ▸ ⟨Set.empty_subset _, fun _ _ _ ↦ Set.empty_subset _⟩⟩

theorem IsMinCover.nonempty {C : Set (Set W)} {S : Set W} (h : IsMinCover C S)
    (hC : C.Nonempty) : S.Nonempty :=
  Set.nonempty_iff_ne_empty.2 fun hS ↦ hC.ne_empty (isMinCover_empty_iff.1 (hS ▸ h))

theorem isMinCover_singleton_iff {X S : Set W} (hS : S.Nonempty) :
    IsMinCover {X} S ↔ S ⊆ X := by
  refine ⟨fun h ↦ by simpa using h.subset_sUnion, fun h ↦ ⟨by simpa using h, fun Y hY hYX ↦ ?_⟩⟩
  obtain ⟨v, hv⟩ := hS
  obtain ⟨Z, hZY, -⟩ := hY hv
  exact Set.singleton_subset_iff.2 (Set.mem_singleton_iff.1 (hYX hZY) ▸ hZY)

theorem isMinCover_singleton_iff' {X S : Set W} :
    IsMinCover {X} S ↔ S.Nonempty ∧ S ⊆ X :=
  ⟨fun h ↦ ⟨h.nonempty (Set.singleton_nonempty X), by simpa using h.subset_sUnion⟩,
    fun ⟨hS, h⟩ ↦ (isMinCover_singleton_iff hS).2 h⟩

theorem isMinCover_pair_iff {A B S : Set W} (hAB : A ≠ B) :
    IsMinCover {A, B} S ↔ S ⊆ A ∪ B ∧ ¬ S ⊆ A ∧ ¬ S ⊆ B := by
  refine ⟨fun h ↦ ⟨by simpa using h.subset_sUnion, fun hA ↦ ?_, fun hB ↦ ?_⟩, ?_⟩
  · have h' := h.le_of_le (y := {A}) (by simpa using hA)
      (Set.singleton_subset_iff.2 (Set.mem_insert A _))
    exact hAB (h' (Set.mem_insert_of_mem A (Set.mem_singleton B))).symm
  · have h' := h.le_of_le (y := {B}) (by simpa using hB)
      (Set.singleton_subset_iff.2 (Set.mem_insert_of_mem A (Set.mem_singleton B)))
    exact hAB (h' (Set.mem_insert A _))
  rintro ⟨hcov, hA, hB⟩
  refine ⟨by simpa using hcov, fun Y hY hYAB ↦ Set.insert_subset_iff.2 ⟨?_, ?_⟩⟩
  · obtain ⟨u, huS, huB⟩ := Set.not_subset.1 hB
    obtain ⟨Z, hZY, huZ⟩ := hY huS
    rcases hYAB hZY with rfl | rfl
    · exact hZY
    · exact absurd huZ huB
  · obtain ⟨v, hvS, hvA⟩ := Set.not_subset.1 hA
    obtain ⟨Z, hZY, hvZ⟩ := hY hvS
    rcases hYAB hZY with rfl | rfl
    · exact absurd hvZ hvA
    · exact Set.singleton_subset_iff.2 hZY

theorem isMinCover_pair_iff_inter_sdiff {A B S : Set W} (hAB : A ≠ B) :
    IsMinCover {A, B} S ↔ S ⊆ A ∪ B ∧ (S ∩ (A \ B)).Nonempty ∧ (S ∩ (B \ A)).Nonempty := by
  rw [isMinCover_pair_iff hAB]
  refine and_congr_right fun hcov ↦ ?_
  have key : ∀ {X Y : Set W}, S ⊆ X ∪ Y → (¬ S ⊆ Y ↔ (S ∩ (X \ Y)).Nonempty) := fun hXY ↦
    ⟨fun h ↦ (Set.not_subset.1 h).imp fun _ ⟨hv, hvY⟩ ↦ ⟨hv, (hXY hv).resolve_right hvY, hvY⟩,
      fun ⟨_, hv, _, hvY⟩ h ↦ hvY (h hv)⟩
  rw [key hcov, key (hcov.trans (Set.union_comm A B).subset)]
  exact and_comm

/-- `C` is a super cover of `S` ([simons-2005]): it covers `S` and each of its members meets `S`. -/
def IsSuperCover (C : Set (Set W)) (S : Set W) : Prop :=
  S ⊆ ⋃₀ C ∧ ∀ c ∈ C, (c ∩ S).Nonempty

theorem isSuperCover_pair_iff {A B S : Set W} :
    IsSuperCover {A, B} S ↔ S ⊆ A ∪ B ∧ (A ∩ S).Nonempty ∧ (B ∩ S).Nonempty := by
  simp [IsSuperCover]

theorem IsMinCover.isSuperCover {C : Set (Set W)} {S : Set W} (h : IsMinCover C S) :
    IsSuperCover C S := by
  refine ⟨h.subset_sUnion, fun c hc ↦ Set.nonempty_iff_ne_empty.2 fun hcS ↦ ?_⟩
  refine isMinCover_iff.1 h |>.2 c hc fun v hv ↦ ?_
  obtain ⟨d, hd, hvd⟩ := h.subset_sUnion hv
  refine ⟨d, ⟨hd, fun hdc ↦ ?_⟩, hvd⟩
  rw [Set.mem_singleton_iff.1 hdc] at hvd
  exact Set.eq_empty_iff_forall_notMem.1 hcS v ⟨hvd, hv⟩

/-! ### The unilateral modals -/

/-- The unilateral necessity modal: `□P` holds at `w` when the alternatives of `P` minimally
cover the relevant worlds `R w`. -/
def box (R : W → Set W) (P : Question W) : Question W :=
  ofSet {w | IsMinCover (alt P) (R w)}

/-- The unilateral possibility modal: `◇P` holds at `w` when the alternatives of `P` minimally
cover a nonempty set of relevant worlds. -/
def dia (R : W → Set W) (P : Question W) : Question W :=
  ofSet {w | ∃ R' ⊆ R w, R'.Nonempty ∧ IsMinCover (alt P) R'}

@[simp] theorem info_box (R : W → Set W) (P : Question W) :
    (box R P).info = {w | IsMinCover (alt P) (R w)} :=
  info_ofSet _

@[simp] theorem info_dia (R : W → Set W) (P : Question W) :
    (dia R P).info = {w | ∃ R' ⊆ R w, R'.Nonempty ∧ IsMinCover (alt P) R'} :=
  info_ofSet _

theorem disjoint_box_dia (R : W → Set W) {P Q : Question W} (h : Disjoint P.info Q.info) :
    Disjoint (box R P) (dia R Q) := by
  rw [box, dia, disjoint_ofSet_iff]
  exact Set.disjoint_left.2 fun w hP ⟨R', hR', ⟨v, hv⟩, hQ⟩ ↦
    Set.disjoint_left.1 h (P.sUnion_alt_subset_info (hP.subset_sUnion (hR' hv)))
      (Q.sUnion_alt_subset_info (hQ.subset_sUnion hv))

/-! ### Bilateral inquisitive propositions -/

/-- A **bilateral inquisitive proposition**: a pair of inquisitive propositions, the states
verifying and the states falsifying a sentence, overlapping only in `∅` (disjoint in `Question W`,
whose bottom is `{∅}`). This is Kalman's construction over the inquisitive algebra; `Kalman.pro`
and `Kalman.con` are Booth's `⟦φ⟧⁺` and `⟦φ⟧⁻`, and negation, conjunction and disjunction are
`ᶜ`, `⊓` and `⊔`. -/
abbrev BilatInqProp (W : Type*) := Kalman (Question W)

namespace BilatInqProp

/-- The informative contents of the two coordinates, `(info ⟦φ⟧⁺, info ⟦φ⟧⁻)`, as a Kleene
homomorphism into the partial propositions. -/
def info : BoundedLatticeHom (BilatInqProp W) (Kalman (Set W)) :=
  Kalman.map infoHom.toBoundedLatticeHom

/-- The worlds at which `φ` is true, `info ⟦φ⟧⁺`. -/
abbrev truth (φ : BilatInqProp W) : Set W := (info φ).pro

/-- The worlds at which `φ` is false, `info ⟦φ⟧⁻`. -/
abbrev falsity (φ : BilatInqProp W) : Set W := (info φ).con

variable (φ ψ : BilatInqProp W)

theorem truth_eq : truth φ = φ.pro.info := rfl
theorem falsity_eq : falsity φ = φ.con.info := rfl

theorem mem_truth_iff {w : W} : w ∈ truth φ ↔ {w} ∈ φ.pro :=
  mem_info_iff_singleton_mem _ _

theorem mem_falsity_iff {w : W} : w ∈ falsity φ ↔ {w} ∈ φ.con :=
  mem_info_iff_singleton_mem _ _

theorem disjoint_truth_falsity : Disjoint (truth φ) (falsity φ) :=
  (info φ).disjoint_pro_con

@[simp] theorem truth_compl : truth φᶜ = falsity φ := rfl
@[simp] theorem falsity_compl : falsity φᶜ = truth φ := rfl
@[simp] theorem truth_sup : truth (φ ⊔ ψ) = truth φ ∪ truth ψ := info_sup _ _
@[simp] theorem falsity_sup : falsity (φ ⊔ ψ) = falsity φ ∩ falsity ψ := info_inf _ _
@[simp] theorem truth_inf : truth (φ ⊓ ψ) = truth φ ∩ truth ψ := info_inf _ _
@[simp] theorem falsity_inf : falsity (φ ⊓ ψ) = falsity φ ∪ falsity ψ := info_sup _ _

end BilatInqProp

open BilatInqProp

/-- An atomic sentence true at `V`: `(↓{V}, ↓{Vᶜ})`. -/
def atom (V : Set W) : BilatInqProp W :=
  Kalman.mk (ofSet V) (ofSet Vᶜ) (disjoint_ofSet_iff.2 disjoint_compl_right)

@[simp] theorem pro_atom (V : Set W) : (atom V).pro = ofSet V := rfl
@[simp] theorem con_atom (V : Set W) : (atom V).con = ofSet Vᶜ := rfl
@[simp] theorem truth_atom (V : Set W) : truth (atom V) = V := info_ofSet V
@[simp] theorem falsity_atom (V : Set W) : falsity (atom V) = Vᶜ := info_ofSet Vᶜ

theorem compl_atom (V : Set W) : (atom V)ᶜ = atom Vᶜ :=
  Kalman.ext rfl (by simp)

theorem alt_atom_pro (V : Set W) : alt (atom V).pro = {V} := alt_ofSet V
theorem alt_atom_con (V : Set W) : alt (atom V).con = {Vᶜ} := alt_ofSet Vᶜ

theorem alt_sup_atom {Vp Vq : Set W} (h : IncompRel (· ⊆ ·) Vp Vq) :
    alt (atom Vp ⊔ atom Vq).pro = {Vp, Vq} :=
  alt_ofSet_sup_ofSet h.1 h.2

theorem alt_sup_atom_con (Vp Vq : Set W) : alt (atom Vp ⊔ atom Vq).con = {Vpᶜ ∩ Vqᶜ} := by
  rw [Kalman.con_sup, con_atom, con_atom, ofSet_inf, alt_ofSet]

theorem alt_inf_compl_atom (Vp Vq : Set W) : alt (atom Vp ⊓ (atom Vq)ᶜ).pro = {Vp ∩ Vqᶜ} := by
  rw [Kalman.pro_inf, Kalman.pro_compl, pro_atom, con_atom, ofSet_inf, alt_ofSet]

/-- The inquisitive `!`, erasing the distinctions between alternatives on both sides:
`(↓{info ⟦φ⟧⁺}, ↓{info ⟦φ⟧⁻})`, each coordinate its double pseudocomplement. -/
def bang (φ : BilatInqProp W) : BilatInqProp W :=
  Kalman.mk φ.proᶜᶜ φ.conᶜᶜ (by
    rw [compl_compl_eq, compl_compl_eq, disjoint_ofSet_iff]
    exact disjoint_truth_falsity φ)

@[simp] theorem truth_bang (φ : BilatInqProp W) : truth (bang φ) = truth φ :=
  info_compl_compl _

@[simp] theorem falsity_bang (φ : BilatInqProp W) : falsity (bang φ) = falsity φ :=
  info_compl_compl _

theorem alt_bang_pro (φ : BilatInqProp W) : alt (bang φ).pro = {truth φ} := by
  change alt φ.proᶜᶜ = _
  rw [compl_compl_eq, alt_ofSet]
  rfl

/-! ### The bilateral modals -/

/-- **Necessity**: true where the positive alternatives of the prejacent minimally cover the
relevant worlds, false where its negative alternatives minimally cover a nonempty part of them. -/
def necessity (R : W → Set W) (φ : BilatInqProp W) : BilatInqProp W :=
  Kalman.mk (box R φ.pro) (dia R φ.con) (disjoint_box_dia R (disjoint_truth_falsity φ))

/-- **Possibility**: true where the positive alternatives of the prejacent minimally cover a
nonempty part of the relevant worlds, false where its negative alternatives minimally cover
them. -/
def possibility (R : W → Set W) (φ : BilatInqProp W) : BilatInqProp W :=
  Kalman.mk (dia R φ.pro) (box R φ.con)
    (disjoint_box_dia R (disjoint_truth_falsity φ).symm).symm

variable (R : W → Set W) (φ : BilatInqProp W)

theorem possibility_eq_compl_necessity_compl : possibility R φ = (necessity R φᶜ)ᶜ := rfl

theorem necessity_eq_compl_possibility_compl : necessity R φ = (possibility R φᶜ)ᶜ := rfl

@[simp] theorem truth_necessity :
    truth (necessity R φ) = {w | IsMinCover (alt φ.pro) (R w)} :=
  info_box R _

@[simp] theorem falsity_necessity :
    falsity (necessity R φ) = {w | ∃ R' ⊆ R w, R'.Nonempty ∧ IsMinCover (alt φ.con) R'} :=
  info_dia R _

@[simp] theorem truth_possibility :
    truth (possibility R φ) = {w | ∃ R' ⊆ R w, R'.Nonempty ∧ IsMinCover (alt φ.pro) R'} :=
  info_dia R _

@[simp] theorem falsity_possibility :
    falsity (possibility R φ) = {w | IsMinCover (alt φ.con) (R w)} :=
  info_box R _

theorem truth_necessity_of_alt_eq_singleton {A : Set W} (h : alt φ.pro = {A}) :
    truth (necessity R φ) = {w | (R w).Nonempty ∧ R w ⊆ A} := by
  ext w
  simp [h, isMinCover_singleton_iff']

theorem truth_possibility_of_alt_eq_singleton {A : Set W} (h : alt φ.pro = {A}) :
    truth (possibility R φ) = {w | (R w ∩ A).Nonempty} := by
  ext w
  simp only [truth_possibility, h, isMinCover_singleton_iff', Set.mem_ofPred_eq]
  refine ⟨fun ⟨R', hR', _, ⟨v, hv⟩, hA⟩ ↦ ⟨v, hR' hv, hA hv⟩, fun ⟨v, hvR, hvA⟩ ↦ ?_⟩
  exact ⟨{v}, Set.singleton_subset_iff.2 hvR, Set.singleton_nonempty v,
    Set.singleton_nonempty v, Set.singleton_subset_iff.2 hvA⟩

theorem falsity_necessity_of_alt_eq_singleton {B : Set W} (h : alt φ.con = {B}) :
    falsity (necessity R φ) = {w | (R w ∩ B).Nonempty} :=
  truth_possibility_of_alt_eq_singleton R φᶜ h

theorem falsity_possibility_of_alt_eq_singleton {B : Set W} (h : alt φ.con = {B}) :
    falsity (possibility R φ) = {w | (R w).Nonempty ∧ R w ⊆ B} :=
  truth_necessity_of_alt_eq_singleton R φᶜ h

/-! ### Conditionals and the language -/

/-- The accessibility update by `φ`: the relevant worlds at which `φ` is true. -/
def updateAccess (R : W → Set W) (φ : BilatInqProp W) (w : W) : Set W :=
  R w ∩ truth φ

/-- The language: atoms, negation, conjunction, disjunction, the inquisitive `!`, the restrictor
conditional, and the two modals. -/
inductive Formula (At : Type*) where
  | atom (p : At)
  | neg (φ : Formula At)
  | conj (φ ψ : Formula At)
  | disj (φ ψ : Formula At)
  | bang (φ : Formula At)
  | cond (φ ψ : Formula At)
  | box (φ : Formula At)
  | diamond (φ : Formula At)

namespace Formula

variable {At : Type*}

/-- The interpretation of a sentence in the model `⟨W, R, V⟩`. The restrictor conditional
evaluates its consequent under the accessibility updated by its antecedent. -/
def eval (V : At → Set W) : (W → Set W) → Formula At → BilatInqProp W
  | _, atom p => MinimalCovering.atom (V p)
  | R, neg φ => (eval V R φ)ᶜ
  | R, conj φ ψ => eval V R φ ⊓ eval V R ψ
  | R, disj φ ψ => eval V R φ ⊔ eval V R ψ
  | R, bang φ => MinimalCovering.bang (eval V R φ)
  | R, cond φ ψ => eval V (updateAccess R (eval V R φ)) ψ
  | R, box φ => necessity R (eval V R φ)
  | R, diamond φ => possibility R (eval V R φ)

end Formula

end MinimalCovering
