module

public import Linglib.Core.Order.DeMorganAlgebra.Kalman
public import Linglib.Semantics.Questions.Basic
public import Mathlib.Order.Comparable

/-!
# Minimal covering semantics

Modals over a disjunction require its disjuncts to divide up the relevant worlds. For
[simons-2005] the disjuncts must super cover them, each disjunct meeting them, so possibility
holds exactly when [each disjunct is possible](##exists_isSuperCover_iff), the Diversity
inference. Booth's semantics ([booth-2022a], [booth-2022b]) requires a minimal cover instead,
which holds exactly when [each disjunct contains a covered world that no other
contains](##isMinCover_iff_inter_sdiff). Possibility then holds exactly when [each disjunct has a
relevant world to itself](##exists_isMinCover_iff), the Independence inference, and necessity is
[orthodox necessity together with possibility](##truth_necessity_eq_inter). A minimal cover of a
nonempty set is [a super cover](##IsMinCover.isSuperCover).

The unilateral modals `box` and `diamond` act on inquisitive propositions (`Question W`), whose
alternatives let a modal see the disjuncts of its prejacent. The bilateral semantics assigns each
sentence a pair of inquisitive propositions, the states verifying and the states falsifying it,
overlapping only in the inconsistent state `∅`. These pairs are Kalman's construction over the
inquisitive algebra, `Kalman (Question W)`, so negation swaps the pair and conjunction and
disjunction are the Kleene-lattice operations, with the De Morgan laws and double negation for
free. The bilateral modals are pairs of unilateral ones, `necessity = (box, diamond)` and
`possibility = (diamond, box)` on the two coordinates, so the duality of `□` and `◇` holds by
definition. Truth and falsity are the informative contents of the two coordinates: no sentence is
[both true and false](##disjoint_truth_falsity), but a modal sentence can be neither.

## Implementation notes

`IsMinCover C S` is mathlib's `Minimal` for the predicate of covering `S`, which is closed
upward, so `Set.minimal_iff_forall_sdiff_singleton` is the characterization by needed members.

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

/-- `C` is a super cover of `S` ([simons-2005]): `C` is nonempty, each of its members meets `S`,
and each member of `S` belongs to one of them. -/
def IsSuperCover (C : Set (Set W)) (S : Set W) : Prop :=
  C.Nonempty ∧ (∀ c ∈ C, (c ∩ S).Nonempty) ∧ S ⊆ ⋃₀ C

variable {C : Set (Set W)} {S A B X : Set W}

theorem IsMinCover.subset_sUnion (h : IsMinCover C S) : S ⊆ ⋃₀ C :=
  h.prop

/-- A cover is minimal exactly when each member is needed: dropping it leaves part of `S`
uncovered. -/
theorem isMinCover_iff : IsMinCover C S ↔ S ⊆ ⋃₀ C ∧ ∀ c ∈ C, ¬ S ⊆ ⋃₀ (C \ {c}) :=
  Set.minimal_iff_forall_sdiff_singleton fun _ _ hS hXY ↦ hS.trans (Set.sUnion_mono hXY)

/-- A cover is minimal exactly when each member contains a point of `S` that no other member
contains. -/
theorem isMinCover_iff_inter_sdiff :
    IsMinCover C S ↔ S ⊆ ⋃₀ C ∧ ∀ c ∈ C, (S ∩ (c \ ⋃₀ (C \ {c}))).Nonempty := by
  refine isMinCover_iff.trans (and_congr_right fun hS ↦ forall₂_congr fun c _ ↦ ?_)
  refine ⟨fun h ↦ ?_, fun ⟨v, hvS, _, hv⟩ h ↦ hv (h hvS)⟩
  obtain ⟨v, hvS, hv⟩ := Set.not_subset.1 h
  obtain ⟨d, hdC, hvd⟩ := hS hvS
  obtain rfl : d = c := by_contra fun hdc ↦ hv ⟨d, ⟨hdC, hdc⟩, hvd⟩
  exact ⟨v, hvS, hvd, hv⟩

/-- Some nonempty part of `S` is minimally covered by `C` exactly when `C` is nonempty and each of
its members contains a point of `S` that no other member contains. -/
theorem exists_isMinCover_iff :
    (∃ S' ⊆ S, S'.Nonempty ∧ IsMinCover C S') ↔
      C.Nonempty ∧ ∀ c ∈ C, (S ∩ (c \ ⋃₀ (C \ {c}))).Nonempty := by
  refine ⟨fun ⟨S', hS', ⟨v, hv⟩, h⟩ ↦ ?_, fun ⟨⟨c₀, hc₀⟩, h⟩ ↦ ?_⟩
  · obtain ⟨c, hc, -⟩ := h.subset_sUnion hv
    exact ⟨⟨c, hc⟩, fun c hc ↦ ((isMinCover_iff_inter_sdiff.1 h).2 c hc).mono
      (Set.inter_subset_inter_left _ hS')⟩
  refine ⟨⋃ c ∈ C, S ∩ (c \ ⋃₀ (C \ {c})), Set.iUnion₂_subset fun _ _ ↦ Set.inter_subset_left,
    (h c₀ hc₀).mono (Set.subset_biUnion_of_mem hc₀), isMinCover_iff_inter_sdiff.2
      ⟨Set.iUnion₂_subset fun c hc _ hv ↦ ⟨c, hc, hv.2.1⟩, fun c hc ↦ ?_⟩⟩
  obtain ⟨v, hv⟩ := h c hc
  exact ⟨v, Set.mem_biUnion hc hv, hv.2⟩

theorem isMinCover_empty_iff : IsMinCover C ∅ ↔ C = ∅ :=
  ⟨fun h ↦ Set.subset_empty_iff.1 (h.le_of_le (Set.empty_subset _) (Set.empty_subset _)),
    fun h ↦ h ▸ ⟨Set.empty_subset _, fun _ _ _ ↦ Set.empty_subset _⟩⟩

theorem IsMinCover.nonempty (h : IsMinCover C S) (hC : C.Nonempty) : S.Nonempty :=
  let ⟨c, hc⟩ := hC
  ((isMinCover_iff_inter_sdiff.1 h).2 c hc).mono Set.inter_subset_left

theorem isMinCover_singleton_iff : IsMinCover {X} S ↔ S.Nonempty ∧ S ⊆ X := by
  simp only [isMinCover_iff_inter_sdiff, Set.sUnion_singleton, Set.mem_singleton_iff, forall_eq,
    sdiff_self, Set.bot_eq_empty, Set.sUnion_empty, Set.sdiff_empty]
  exact ⟨fun ⟨h, hX⟩ ↦ ⟨hX.mono Set.inter_subset_left, h⟩,
    fun ⟨hS, h⟩ ↦ ⟨h, (Set.inter_eq_left.2 h).symm ▸ hS⟩⟩

theorem isMinCover_pair_iff (hAB : A ≠ B) :
    IsMinCover {A, B} S ↔ S ⊆ A ∪ B ∧ ¬ S ⊆ A ∧ ¬ S ⊆ B := by
  simp [isMinCover_iff, Set.pair_sdiff_left hAB, Set.pair_sdiff_right hAB, and_comm]

theorem isMinCover_pair_iff_inter_sdiff (hAB : A ≠ B) :
    IsMinCover {A, B} S ↔ S ⊆ A ∪ B ∧ (S ∩ (A \ B)).Nonempty ∧ (S ∩ (B \ A)).Nonempty := by
  simp [isMinCover_iff_inter_sdiff, Set.pair_sdiff_left hAB, Set.pair_sdiff_right hAB]

theorem IsSuperCover.subset_sUnion (h : IsSuperCover C S) : S ⊆ ⋃₀ C :=
  h.2.2

/-- A super cover covers a nonempty set, since its members meet it. -/
theorem IsSuperCover.nonempty (h : IsSuperCover C S) : S.Nonempty :=
  let ⟨c, hc⟩ := h.1
  (h.2.1 c hc).mono Set.inter_subset_right

theorem isSuperCover_pair_iff :
    IsSuperCover {A, B} S ↔ (A ∩ S).Nonempty ∧ (B ∩ S).Nonempty ∧ S ⊆ A ∪ B := by
  simp [IsSuperCover, and_assoc]

/-- Some part of `S` is super covered by `C` exactly when `C` is nonempty and each of its members
meets `S`. -/
theorem exists_isSuperCover_iff :
    (∃ S' ⊆ S, IsSuperCover C S') ↔ C.Nonempty ∧ ∀ c ∈ C, (c ∩ S).Nonempty := by
  refine ⟨fun ⟨S', hS', hC, h, _⟩ ↦ ⟨hC, fun c hc ↦ (h c hc).mono
    (Set.inter_subset_inter_right _ hS')⟩, fun ⟨hC, h⟩ ↦ ⟨S ∩ ⋃₀ C, Set.inter_subset_left, hC,
      fun c hc ↦ ?_, Set.inter_subset_right⟩⟩
  obtain ⟨v, hvc, hvS⟩ := h c hc
  exact ⟨v, hvc, hvS, c, hc, hvc⟩

/-- A minimal cover of a nonempty set is a super cover, since a member missing the set could be
dropped. -/
theorem IsMinCover.isSuperCover (h : IsMinCover C S) (hS : S.Nonempty) : IsSuperCover C S := by
  obtain ⟨v, hv⟩ := hS
  obtain ⟨c, hc, -⟩ := h.subset_sUnion hv
  exact ⟨⟨c, hc⟩, fun c hc ↦ ((isMinCover_iff_inter_sdiff.1 h).2 c hc).mono
    fun _ hv ↦ ⟨hv.2.1, hv.1⟩, h.subset_sUnion⟩

/-! ### The unilateral modals -/

/-- The unilateral necessity modal: `□P` holds at `w` when the alternatives of `P` minimally
cover the relevant worlds `R w`. -/
def box (R : W → Set W) (P : Question W) : Question W :=
  ofSet {w | IsMinCover (alt P) (R w)}

/-- The unilateral possibility modal: `◇P` holds at `w` when the alternatives of `P` minimally
cover a nonempty set of relevant worlds. -/
def diamond (R : W → Set W) (P : Question W) : Question W :=
  ofSet {w | ∃ R' ⊆ R w, R'.Nonempty ∧ IsMinCover (alt P) R'}

@[simp] theorem info_box (R : W → Set W) (P : Question W) :
    (box R P).info = {w | IsMinCover (alt P) (R w)} :=
  info_ofSet _

@[simp] theorem info_diamond (R : W → Set W) (P : Question W) :
    (diamond R P).info = {w | ∃ R' ⊆ R w, R'.Nonempty ∧ IsMinCover (alt P) R'} :=
  info_ofSet _

/-- Necessity is orthodox necessity of what the alternatives cover together with possibility:
the alternatives cover the relevant worlds, and each has a relevant world to itself. -/
theorem box_eq_inf_diamond (R : W → Set W) {P : Question W} (hP : (alt P).Nonempty) :
    box R P = ofSet {w | R w ⊆ ⋃₀ alt P} ⊓ diamond R P := by
  rw [box, diamond, ofSet_inf]
  congr 1
  ext w
  rw [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
    exists_isMinCover_iff, isMinCover_iff_inter_sdiff]
  exact ⟨fun h ↦ ⟨h.1, hP, h.2⟩, fun h ↦ ⟨h.1, h.2.2⟩⟩

theorem disjoint_box_diamond (R : W → Set W) {P Q : Question W} (h : Disjoint P.info Q.info) :
    Disjoint (box R P) (diamond R Q) := by
  rw [box, diamond, disjoint_ofSet_iff]
  exact Set.disjoint_left.2 fun w hP ⟨R', hR', ⟨v, hv⟩, hQ⟩ ↦
    Set.disjoint_left.1 h (P.sUnion_alt_subset_info (hP.subset_sUnion (hR' hv)))
      (Q.sUnion_alt_subset_info (hQ.subset_sUnion hv))

/-! ### Bilateral inquisitive propositions

A bilateral inquisitive proposition is a pair of inquisitive propositions, the states verifying
and the states falsifying a sentence, overlapping only in `∅`: disjoint in `Question W`, whose
bottom is `{∅}`. These are the elements of `Kalman (Question W)`; `Kalman.pro` and `Kalman.con` are
Booth's `⟦φ⟧⁺` and `⟦φ⟧⁻`, and negation, conjunction and disjunction are `ᶜ`, `⊓` and `⊔`. -/

/-- The worlds at which `φ` is true, `info ⟦φ⟧⁺`. -/
abbrev truth (φ : Kalman (Question W)) : Set W := φ.pro.info

/-- The worlds at which `φ` is false, `info ⟦φ⟧⁻`. -/
abbrev falsity (φ : Kalman (Question W)) : Set W := φ.con.info

section Connectives

variable (φ ψ : Kalman (Question W))

theorem mem_truth_iff {w : W} : w ∈ truth φ ↔ {w} ∈ φ.pro :=
  mem_info_iff_singleton_mem _ _

theorem mem_falsity_iff {w : W} : w ∈ falsity φ ↔ {w} ∈ φ.con :=
  mem_info_iff_singleton_mem _ _

/-- No sentence is both true and false. -/
theorem disjoint_truth_falsity : Disjoint (truth φ) (falsity φ) :=
  φ.disjoint_pro_con.map infoHom

@[simp] theorem truth_compl : truth φᶜ = falsity φ := rfl
@[simp] theorem falsity_compl : falsity φᶜ = truth φ := rfl
@[simp] theorem truth_sup : truth (φ ⊔ ψ) = truth φ ∪ truth ψ := info_sup _ _
@[simp] theorem falsity_sup : falsity (φ ⊔ ψ) = falsity φ ∩ falsity ψ := info_inf _ _
@[simp] theorem truth_inf : truth (φ ⊓ ψ) = truth φ ∩ truth ψ := info_inf _ _
@[simp] theorem falsity_inf : falsity (φ ⊓ ψ) = falsity φ ∪ falsity ψ := info_sup _ _

/-- An atomic sentence true at `V`: `(↓{V}, ↓{Vᶜ})`. -/
def atom (V : Set W) : Kalman (Question W) :=
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
`!φ = (↓{info ⟦φ⟧⁺}, ↓{info ⟦φ⟧⁻})`. -/
def bang : Kalman (Question W) :=
  Kalman.mk (ofSet (truth φ)) (ofSet (falsity φ))
    (disjoint_ofSet_iff.2 (disjoint_truth_falsity φ))

@[simp] theorem truth_bang : truth (bang φ) = truth φ := info_ofSet _
@[simp] theorem falsity_bang : falsity (bang φ) = falsity φ := info_ofSet _

theorem alt_bang_pro : alt (bang φ).pro = {truth φ} := alt_ofSet _

end Connectives

/-! ### The bilateral modals -/

/-- **Necessity**: true where the positive alternatives of the prejacent minimally cover the
relevant worlds, false where its negative alternatives minimally cover a nonempty part of them. -/
def necessity (R : W → Set W) (φ : Kalman (Question W)) : Kalman (Question W) :=
  Kalman.mk (box R φ.pro) (diamond R φ.con) (disjoint_box_diamond R (disjoint_truth_falsity φ))

/-- **Possibility**: true where the positive alternatives of the prejacent minimally cover a
nonempty part of the relevant worlds, false where its negative alternatives minimally cover
them. -/
def possibility (R : W → Set W) (φ : Kalman (Question W)) : Kalman (Question W) :=
  Kalman.mk (diamond R φ.pro) (box R φ.con)
    (disjoint_box_diamond R (disjoint_truth_falsity φ).symm).symm

section Modals

variable (R : W → Set W) (φ : Kalman (Question W))

/-- The duality of the modals: `◇φ = ¬□¬φ`. -/
theorem possibility_eq_compl_necessity_compl : possibility R φ = (necessity R φᶜ)ᶜ := rfl

theorem necessity_eq_compl_possibility_compl : necessity R φ = (possibility R φᶜ)ᶜ := rfl

@[simp] theorem truth_necessity :
    truth (necessity R φ) = {w | IsMinCover (alt φ.pro) (R w)} :=
  info_box R _

@[simp] theorem falsity_necessity :
    falsity (necessity R φ) = {w | ∃ R' ⊆ R w, R'.Nonempty ∧ IsMinCover (alt φ.con) R'} :=
  info_diamond R _

@[simp] theorem truth_possibility :
    truth (possibility R φ) = {w | ∃ R' ⊆ R w, R'.Nonempty ∧ IsMinCover (alt φ.pro) R'} :=
  info_diamond R _

@[simp] theorem falsity_possibility :
    falsity (possibility R φ) = {w | IsMinCover (alt φ.con) (R w)} :=
  info_box R _

/-- Over a single alternative `A`, necessity is orthodox: true where the relevant worlds are
nonempty and inside `A`. -/
theorem truth_necessity_of_alt_eq_singleton (h : alt φ.pro = {A}) :
    truth (necessity R φ) = {w | (R w).Nonempty ∧ R w ⊆ A} := by
  simp [h, isMinCover_singleton_iff]

/-- Over a single alternative `A`, possibility is orthodox: true where some relevant world lies
in `A`. -/
theorem truth_possibility_of_alt_eq_singleton (h : alt φ.pro = {A}) :
    truth (possibility R φ) = {w | (R w ∩ A).Nonempty} := by
  simp [h, exists_isMinCover_iff]

theorem falsity_necessity_of_alt_eq_singleton (h : alt φ.con = {B}) :
    falsity (necessity R φ) = {w | (R w ∩ B).Nonempty} :=
  truth_possibility_of_alt_eq_singleton R φᶜ h

theorem falsity_possibility_of_alt_eq_singleton (h : alt φ.con = {B}) :
    falsity (possibility R φ) = {w | (R w).Nonempty ∧ R w ⊆ B} :=
  truth_necessity_of_alt_eq_singleton R φᶜ h

/-- Necessity is orthodox necessity together with possibility: where the positive alternatives of
`φ` generate it, `□φ` is true exactly where `□!φ` and `◇φ` are. -/
theorem truth_necessity_eq_inter (hφ : φ.pro.IsNormal) :
    truth (necessity R φ) = truth (necessity R (bang φ)) ∩ truth (possibility R φ) := by
  rw [truth_necessity_of_alt_eq_singleton R _ (alt_bang_pro φ)]
  change (box R φ.pro).info = _ ∩ (diamond R φ.pro).info
  rw [box_eq_inf_diamond R hφ.alt_nonempty, info_inf, info_ofSet, ← hφ.info_eq_sUnion_alt]
  ext w
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, info_diamond]
  exact ⟨fun ⟨h₁, h₂⟩ ↦ ⟨⟨h₂.elim fun _ ⟨hR', hne, _⟩ ↦ hne.mono hR', h₁⟩, h₂⟩,
    fun ⟨⟨_, h₁⟩, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

end Modals

/-! ### Conditionals and the language -/

/-- The accessibility update by `φ`: the relevant worlds at which `φ` is true. -/
def updateAccess (R : W → Set W) (φ : Kalman (Question W)) (w : W) : Set W :=
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
def eval (V : At → Set W) : (W → Set W) → Formula At → Kalman (Question W)
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
