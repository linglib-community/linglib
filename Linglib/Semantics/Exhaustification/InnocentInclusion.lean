module

public import Linglib.Semantics.Exhaustification.InnocentExclusion

/-!
# Innocent inclusion

This file defines Bar-Lev and Fox's innocent inclusion, which runs after innocent exclusion. A set
of alternatives is a consistent inclusion when its members can all be true together with the
exhaustified prejacent; an alternative is innocently includable when it belongs to every maximal
consistent inclusion. `exhII` asserts the prejacent, denies the innocently excludable
alternatives and asserts the innocently includable ones. The `cell` of the prejacent asserts it,
denies the excludable alternatives and asserts all the others; when the cell is consistent,
`exhII` is the cell, and when it is not, as for simple disjunction, innocent inclusion adds
nothing to innocent exclusion.

## Main statements

* `Exhaustification.mem_II_iff_of_cell_nonempty`: when the cell is consistent, the
  innocently includable alternatives are exactly those not innocently excludable.
* `Exhaustification.exhII_eq_cell_of_cell_nonempty`: when the cell is consistent,
  exhaustification is the cell.
* `Exhaustification.mem_cell_iff`: the cell consists of the prejacent worlds verifying exactly the
  alternatives of the minimal verified sets.

## References

* [bar-lev-fox-2020]
-/

@[expose] public section

namespace Exhaustification

variable {World : Type*}
variable (ALT : Set (Set World))
variable (φ : Set World)

/-- A set of alternatives is a consistent inclusion when its members can all be true together
with the exhaustified prejacent. -/
def IsConsistentInclusion (R : Set (Set World)) : Prop :=
  R ⊆ ALT ∧ (exhᴵᴱ ALT φ ∩ ⋂₀ R).Nonempty

/-- The innocently includable alternatives are those in every maximal consistent inclusion. -/
def II : Set (Set World) :=
  {a ∈ ALT | ∀ R, Maximal (IsConsistentInclusion ALT φ) R → a ∈ R}

/-- `exhII ALT φ` asserts the prejacent, denies the innocently excludable alternatives and
asserts the innocently includable ones. -/
def exhII : Set World :=
  {w | w ∈ φ ∧ (∀ q, q ∈ IE ALT φ → w ∉ q) ∧
    ∀ r, r ∈ II ALT φ → w ∈ r}

@[inherit_doc] scoped notation "exhᴵᴱ⁺ᴵᴵ" => exhII

theorem mem_exhII_iff {w : World} : w ∈ exhᴵᴱ⁺ᴵᴵ ALT φ ↔ w ∈ φ ∧
    (∀ q, q ∈ IE ALT φ → w ∉ q) ∧ ∀ r, r ∈ II ALT φ → w ∈ r :=
  Iff.rfl

theorem exhII_eq_exhIE_inter :
    exhᴵᴱ⁺ᴵᴵ ALT φ = exhᴵᴱ ALT φ ∩ ⋂₀ II ALT φ := by
  ext w
  rw [Set.mem_inter_iff, mem_exhIE_iff, Set.mem_sInter, and_assoc]
  exact Iff.rfl

/-- The cell of the prejacent in the partition the alternatives induce asserts the prejacent,
denies the innocently excludable alternatives and asserts all the others. -/
def cell : Set World :=
  {w | w ∈ φ ∧ (∀ q, q ∈ IE ALT φ → w ∉ q) ∧
    ∀ r ∈ ALT, ¬ r ∈ IE ALT φ → w ∈ r}

theorem mem_cell {w : World} : w ∈ cell ALT φ ↔ w ∈ φ ∧
    (∀ q, q ∈ IE ALT φ → w ∉ q) ∧
      ∀ r ∈ ALT, ¬ r ∈ IE ALT φ → w ∈ r :=
  Iff.rfl

variable {ALT φ} in
lemma IsConsistentInclusion.mono {R S : Set (Set World)} (hS : IsConsistentInclusion ALT φ S)
    (hRS : R ⊆ S) : IsConsistentInclusion ALT φ R :=
  ⟨hRS.trans hS.1, hS.2.mono (Set.inter_subset_inter_right _ (Set.sInter_subset_sInter hRS))⟩

variable {ALT φ} in
/-- No member of a consistent inclusion is innocently excludable. -/
lemma IsConsistentInclusion.notMem_IE {R : Set (Set World)}
    (hR : IsConsistentInclusion ALT φ R) {r : Set World} (hr : r ∈ R) :
    ¬ r ∈ IE ALT φ := fun hexc ↦
  let ⟨_, hu, huR⟩ := hR.2; hu.2 r hexc (huR r hr)

lemma isConsistentInclusion_of_cell_nonempty (h : (cell ALT φ).Nonempty) :
    IsConsistentInclusion ALT φ {r ∈ ALT | ¬ r ∈ IE ALT φ} :=
  let ⟨u, hφ, hexcl, hne⟩ := h
  ⟨fun _ hr ↦ hr.1, u, ⟨hφ, hexcl⟩, fun r hr ↦ hne r hr.1 hr.2⟩

variable {ALT φ} in
/-- When the cell is consistent, the innocently includable alternatives are exactly those that
are not innocently excludable. -/
theorem mem_II_iff_of_cell_nonempty (h : (cell ALT φ).Nonempty) {a : Set World} :
    a ∈ II ALT φ ↔ a ∈ ALT ∧ ¬ a ∈ IE ALT φ := by
  have hD := isConsistentInclusion_of_cell_nonempty ALT φ h
  refine ⟨fun ⟨ha, hR⟩ ↦ hR _ ⟨hD, fun R hR' _ ↦ fun r hr ↦
    ⟨hR'.1 hr, hR'.notMem_IE hr⟩⟩, fun ha ↦ ⟨ha.1, fun R hR ↦
      hR.mem_of_prop_insert (hD.mono (Set.insert_subset ha fun r hr ↦
        ⟨hR.1.1 hr, hR.1.notMem_IE hr⟩))⟩⟩

/-- When the cell is consistent, exhaustification is the cell. -/
theorem exhII_eq_cell_of_cell_nonempty (h : (cell ALT φ).Nonempty) :
    exhᴵᴱ⁺ᴵᴵ ALT φ = cell ALT φ := by
  ext w
  refine ⟨fun ⟨hφ, hexcl, hII⟩ ↦ ⟨hφ, hexcl, fun r hr hnr ↦ hII r
      ((mem_II_iff_of_cell_nonempty h).2 ⟨hr, hnr⟩)⟩,
    fun ⟨hφ, hexcl, hne⟩ ↦ ⟨hφ, hexcl, fun r hr ↦
      let ⟨hrA, hnr⟩ := (mem_II_iff_of_cell_nonempty h).1 hr; hne r hrA hnr⟩⟩

variable {ALT φ} in
/-- An alternative true at a world of the cell is innocently includable. -/
theorem mem_II_of_mem_cell {a : Set World} {w : World} (ha : a ∈ ALT)
    (hw : w ∈ cell ALT φ) (hwa : w ∈ a) : a ∈ II ALT φ :=
  (mem_II_iff_of_cell_nonempty ⟨w, hw⟩).2 ⟨ha, fun hexc ↦ hw.2.1 a hexc hwa⟩

/-! ### Cells from a characterization of innocent exclusion -/

theorem cell_eq_of_iff {P : Set World → Prop}
    (h : ∀ q ∈ ALT, q ∈ IE ALT φ ↔ P q) :
    cell ALT φ = {w | w ∈ φ ∧ ∀ q ∈ ALT, (w ∈ q ↔ ¬ P q)} := by
  ext w
  constructor
  · rintro ⟨hw, hIE, hne⟩
    exact ⟨hw, fun q hq ↦ ⟨fun hwq hP ↦ hIE q ((h q hq).2 hP) hwq,
      fun hP ↦ hne q hq fun hIE' ↦ hP ((h q hq).1 hIE')⟩⟩
  · rintro ⟨hw, h'⟩
    exact ⟨hw, fun q hIE hwq ↦ (h' q hIE.1).1 hwq ((h q hIE.1).1 hIE),
      fun r hr hnr ↦ (h' r hr).2 fun hP ↦ hnr ((h r hr).2 hP)⟩

theorem cell_image_eq {ι : Type*} {f : ι → Set World} {I : Set ι} {P : ι → Prop}
    (h : ∀ i ∈ I, (f i) ∈ IE (f '' I) φ ↔ P i) :
    cell (f '' I) φ = {w | w ∈ φ ∧ ∀ i ∈ I, (w ∈ f i ↔ ¬ P i)} := by
  ext w
  constructor
  · rintro ⟨hw, hIE, hne⟩
    exact ⟨hw, fun i hi ↦ ⟨fun hwi hP ↦ hIE _ ((h i hi).2 hP) hwi,
      fun hP ↦ hne _ ⟨i, hi, rfl⟩ fun hIE' ↦ hP ((h i hi).1 hIE')⟩⟩
  · rintro ⟨hw, h'⟩
    refine ⟨hw, fun q hIE ↦ ?_, fun r hr ↦ ?_⟩
    · obtain ⟨i, hi, rfl⟩ := hIE.1
      exact fun hwi ↦ (h' i hi).1 hwi ((h i hi).1 hIE)
    · obtain ⟨i, hi, rfl⟩ := hr
      exact fun hnr ↦ (h' i hi).2 fun hP ↦ hnr ((h i hi).2 hP)

/-! ### Representative minimal worlds -/

section MinimalCover

variable {ALT φ} {M : Set World}

theorem IsMinimalCover.singleton {w₀ : World} (hw₀ : w₀ ∈ φ) (h : ∀ q ∈ ALT, w₀ ∈ q → φ ⊆ q) :
    IsMinimalCover ALT φ {w₀} :=
  ⟨fun _ hv ↦ hv ▸ hw₀, fun _ hw ↦ ⟨w₀, rfl, fun q hq hq₀ ↦ h q hq hq₀ hw⟩,
    by rintro _ rfl _ rfl h; exact h⟩

theorem IsMinimalCover.cell_eq (hM : IsMinimalCover ALT φ M) :
    cell ALT φ = {w | w ∈ φ ∧ ∀ q ∈ ALT, (w ∈ q ↔ ∃ v ∈ M, v ∈ q)} := by
  ext w
  constructor
  · rintro ⟨hφ, hIE, hne⟩
    refine ⟨hφ, fun q hq ↦ ⟨fun hwq ↦ ?_, fun ⟨v, hv, hvq⟩ ↦ hne q hq fun hIEq ↦ ?_⟩⟩
    · by_contra hnone
      push Not at hnone
      exact hIE q ((hM.mem_IE_iff hq).2 hnone) hwq
    · exact (hM.mem_IE_iff hq).1 hIEq v hv hvq
  · rintro ⟨hφ, h⟩
    refine ⟨hφ, fun q hIEq hwq ↦ ?_, fun r hr hnIE ↦ ?_⟩
    · obtain ⟨v, hv, hvq⟩ := (h q hIEq.1).1 hwq
      exact (hM.mem_IE_iff hIEq.1).1 hIEq v hv hvq
    · by_contra hnr
      exact hnIE ((hM.mem_IE_iff hr).2 fun v hv hvr ↦ hnr ((h r hr).2 ⟨v, hv, hvr⟩))

/-- With a representative set of minimal worlds and a consistent cell, exhaustification asserts
the prejacent and settles every alternative as the minimal worlds jointly do. -/
theorem IsMinimalCover.exhII_eq (hM : IsMinimalCover ALT φ M)
    (hne : ∃ w ∈ φ, ∀ q ∈ ALT, (w ∈ q ↔ ∃ v ∈ M, v ∈ q)) :
    exhᴵᴱ⁺ᴵᴵ ALT φ = {w | w ∈ φ ∧ ∀ q ∈ ALT, (w ∈ q ↔ ∃ v ∈ M, v ∈ q)} := by
  rw [← hM.cell_eq]
  exact exhII_eq_cell_of_cell_nonempty ALT φ (by rw [hM.cell_eq]; exact hne)

/-- With a representative set of minimal worlds and a consistent cell, the innocently
includable alternatives are those true at some minimal world. -/
theorem IsMinimalCover.mem_II_iff (hM : IsMinimalCover ALT φ M)
    (hne : ∃ w ∈ φ, ∀ q ∈ ALT, (w ∈ q ↔ ∃ v ∈ M, v ∈ q)) {a : Set World} :
    a ∈ II ALT φ ↔ a ∈ ALT ∧ ∃ v ∈ M, v ∈ a := by
  rw [mem_II_iff_of_cell_nonempty (by rw [hM.cell_eq]; exact hne)]
  exact and_congr_right fun ha ↦ by rw [hM.mem_IE_iff ha]; push Not; rfl

theorem exhII_eq_diff_of_forall_subset {d : Set World} (hd : d ∈ ALT)
    (hA : ∀ q ∈ ALT, q ≠ d → φ ⊆ q) (hne : ∃ w ∈ φ, w ∉ d) : exhᴵᴱ⁺ᴵᴵ ALT φ = φ \ d := by
  obtain ⟨w₀, hw₀, hw₀d⟩ := hne
  have hM : IsMinimalCover ALT φ {w₀} :=
    .singleton hw₀ fun q hq hq₀ ↦ hA q hq fun h ↦ hw₀d (h ▸ hq₀)
  rw [hM.exhII_eq ⟨w₀, hw₀, by simp⟩]
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, exists_eq_left, Set.mem_sdiff]
  refine ⟨fun ⟨hw, h⟩ ↦ ⟨hw, fun hwd ↦ hw₀d ((h d hd).1 hwd)⟩, fun ⟨hw, hwd⟩ ↦ ⟨hw, fun q hq ↦ ?_⟩⟩
  by_cases hqd : q = d
  · subst hqd
    exact ⟨fun h ↦ absurd h hwd, fun h ↦ absurd h hw₀d⟩
  · exact ⟨fun _ ↦ hA q hq hqd hw₀, fun _ ↦ hA q hq hqd hw⟩

theorem exhII_eq_self_of_forall_subset (hA : ∀ q ∈ ALT, φ ⊆ q) (hsat : φ.Nonempty) :
    exhᴵᴱ⁺ᴵᴵ ALT φ = φ := by
  obtain ⟨w₀, hw₀⟩ := hsat
  have hM : IsMinimalCover ALT φ {w₀} := .singleton hw₀ fun q hq _ ↦ hA q hq
  rw [hM.exhII_eq ⟨w₀, hw₀, by simp⟩]
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, exists_eq_left]
  exact ⟨And.left, fun hw ↦ ⟨hw, fun q hq ↦ iff_of_true (hA q hq hw) (hA q hq hw₀)⟩⟩

theorem exhII_singleton (hsat : φ.Nonempty) : exhᴵᴱ⁺ᴵᴵ {φ} φ = φ :=
  exhII_eq_self_of_forall_subset (by simp) hsat

end MinimalCover

/-! ### Verified alternatives -/

section Verified

variable {ALT φ} {w : World}

/-- The cell of the prejacent consists of the prejacent worlds verifying exactly the alternatives
of the minimal verified sets. -/
theorem mem_cell_iff : w ∈ cell ALT φ ↔ w ∈ φ ∧ satisfied ALT w =
    ⋃₀ {P | Minimal (· ∈ (satisfied ALT) '' φ) P} := by
  rw [mem_cell]
  refine and_congr_right fun _ ↦
    ⟨fun ⟨hIE, hnon⟩ ↦ ?_, fun h ↦ ⟨fun q hq hwq ↦ ?_, fun r hr hnr ↦ ?_⟩⟩
  · ext a
    refine ⟨fun ⟨ha, hwa⟩ ↦ by_contra fun hn ↦ hIE a ((mem_IE_iff_forall_minimal
      ha).2 fun P hP haP ↦ hn ⟨P, hP, haP⟩) hwa, fun ⟨P, hP, haP⟩ ↦ ?_⟩
    have hP' := hP
    obtain ⟨⟨u, hu, rfl⟩, -⟩ := hP'
    exact ⟨haP.1, hnon a haP.1 fun hIEa ↦
      (mem_IE_iff_forall_minimal haP.1).1 hIEa _ hP haP⟩
  · obtain ⟨P, hP, hqP⟩ := (h ▸ (⟨hq.1, hwq⟩ : q ∈ satisfied ALT w) :
      q ∈ ⋃₀ {P | Minimal (· ∈ (satisfied ALT) '' φ) P})
    exact (mem_IE_iff_forall_minimal hq.1).1 hq P hP hqP
  · have : r ∈ ⋃₀ {P | Minimal (· ∈ (satisfied ALT) '' φ) P} := by
      by_contra hn
      exact hnr ((mem_IE_iff_forall_minimal hr).2 fun P hP hrP ↦
        hn ⟨P, hP, hrP⟩)
    exact (h ▸ this : r ∈ satisfied ALT w).2

theorem cell_nonempty_iff : (cell ALT φ).Nonempty ↔
    ⋃₀ {P | Minimal (· ∈ (satisfied ALT) '' φ) P} ∈
      (satisfied ALT) '' φ :=
  ⟨fun ⟨w, hw⟩ ↦ ⟨w, (mem_cell_iff.1 hw).1, (mem_cell_iff.1 hw).2⟩,
    fun ⟨w, hw, h⟩ ↦ ⟨w, mem_cell_iff.2 ⟨hw, h⟩⟩⟩

end Verified

end Exhaustification
