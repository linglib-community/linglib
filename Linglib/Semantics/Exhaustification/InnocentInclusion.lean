module

public import Linglib.Semantics.Exhaustification.InnocentExclusion

/-!
# Innocent Inclusion

Bar-Lev and Fox's Innocent Inclusion runs after Innocent Exclusion and collects the alternatives
that belong to every maximal consistent inclusion, a maximal set of alternatives that can all be
true together with the exhaustified prejacent, (25b). Their operator `exhIEII` asserts the
prejacent, denies the innocently excludable alternatives and asserts the innocently includable
ones, (26). The cell of the prejacent in the partition the alternatives induce asserts the
prejacent, denies the excludable alternatives and asserts all the others, (20); when the cell is
consistent `exhIEII` is the cell, (27), and when it is not, as for simple disjunction, Innocent
Inclusion adds nothing to Innocent Exclusion.

## Main declarations

* `IsConsistentInclusion`, `II`, `IsInnocentlyIncludable`: the innocently includable
  alternatives.
* `exhIEII`: exhaustification with Innocent Exclusion and Innocent Inclusion.
* `cell`, `exhIEII_eq_cell_of_cell_nonempty`, `mem_cell_iff`: cell identification, the cell being
  the prejacent worlds verifying exactly the alternatives of the minimal verified sets.
* `IsMinimalCover.exhIEII_eq`, `IsMinimalCover.II_eq`: exhaustification read off representative
  minimal worlds.

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
  R ⊆ ALT ∧ (exhIE ALT φ ∩ ⋂₀ R).Nonempty

/-- `II ALT φ` is the set of alternatives that belong to every maximal consistent inclusion. -/
def II : Set (Set World) :=
  {r ∈ ALT | ∀ R, Maximal (IsConsistentInclusion ALT φ) R → r ∈ R}

/-- An alternative is innocently includable when it belongs to `II ALT φ`. -/
def IsInnocentlyIncludable (a : Set World) : Prop :=
  a ∈ II ALT φ

/-- `exhIEII ALT φ` asserts the prejacent, denies the innocently excludable alternatives and
asserts the innocently includable ones. -/
def exhIEII : Set World := fun w ↦
  φ w ∧
  (∀ q, IsInnocentlyExcludable ALT φ q → ¬q w) ∧
  (∀ r, IsInnocentlyIncludable ALT φ r → r w)

theorem exhIEII_eq_exhIE_inter : exhIEII ALT φ = exhIE ALT φ ∩ ⋂₀ II ALT φ := by
  ext w
  rw [Set.mem_inter_iff, mem_exhIE_iff, Set.mem_sInter, and_assoc]
  exact Iff.rfl

/-- `nonExcludable ALT φ` is the set of alternatives that are not innocently excludable. -/
def nonExcludable : Set (Set World) :=
  {r ∈ ALT | ¬ IsInnocentlyExcludable ALT φ r}

/-- The cell of the prejacent in the partition the alternatives induce asserts the prejacent,
denies the innocently excludable alternatives and asserts all the others. -/
def cell : Set World := fun w ↦
  φ w ∧
  (∀ q, IsInnocentlyExcludable ALT φ q → ¬ q w) ∧
  (∀ r ∈ nonExcludable ALT φ, r w)

@[simp] lemma mem_nonExcludable {r : Set World} :
    r ∈ nonExcludable ALT φ ↔ r ∈ ALT ∧ ¬ IsInnocentlyExcludable ALT φ r := Iff.rfl

variable {ALT φ} in
lemma IsConsistentInclusion.mono {R S : Set (Set World)} (hS : IsConsistentInclusion ALT φ S)
    (hRS : R ⊆ S) : IsConsistentInclusion ALT φ R :=
  ⟨hRS.trans hS.1, hS.2.mono (Set.inter_subset_inter_right _ (Set.sInter_subset_sInter hRS))⟩

variable {ALT φ} in
lemma IsConsistentInclusion.subset_nonExcludable {R : Set (Set World)}
    (hR : IsConsistentInclusion ALT φ R) : R ⊆ nonExcludable ALT φ := fun r hr ↦
  ⟨hR.1 hr, fun hexc ↦ let ⟨_, hu, huR⟩ := hR.2; hu.2 r hexc (huR r hr)⟩

lemma isConsistentInclusion_nonExcludable_of_cell_nonempty (h : (cell ALT φ).Nonempty) :
    IsConsistentInclusion ALT φ (nonExcludable ALT φ) :=
  let ⟨u, hφ, hexcl, hne⟩ := h
  ⟨fun _ hr ↦ hr.1, u, ⟨hφ, hexcl⟩, hne⟩

theorem II_eq_nonExcludable_of_cell_nonempty (h : (cell ALT φ).Nonempty) :
    II ALT φ = nonExcludable ALT φ := by
  have hD := isConsistentInclusion_nonExcludable_of_cell_nonempty ALT φ h
  ext r
  refine ⟨fun ⟨_, hr⟩ ↦ hr _ ⟨hD, fun _ hR _ ↦ hR.subset_nonExcludable⟩, fun hr ↦ ⟨hr.1, fun R hR ↦
    hR.mem_of_prop_insert (hD.mono (Set.insert_subset hr hR.1.subset_nonExcludable))⟩⟩

/-- When the cell is consistent, exhaustification is the cell. -/
theorem exhIEII_eq_cell_of_cell_nonempty
    (h : (cell ALT φ).Nonempty) :
    exhIEII ALT φ = cell ALT φ := by
  have hII := II_eq_nonExcludable_of_cell_nonempty ALT φ h
  ext w
  refine ⟨fun ⟨hφ, hexcl, hII_w⟩ => ⟨hφ, hexcl, fun r hr => ?_⟩,
          fun ⟨hφ, hexcl, hne⟩ => ⟨hφ, hexcl, fun r hr_II => ?_⟩⟩
  · exact hII_w r (show r ∈ II ALT φ by rw [hII]; exact hr)
  · have : r ∈ nonExcludable ALT φ := by rw [← hII]; exact hr_II
    exact hne r this

theorem mem_II_of_cell_witness {target : Set World}
    (htarget_alt : target ∈ ALT) (w : World)
    (hwitness : cell ALT φ w) (htarget : target w) :
    target ∈ II ALT φ := by
  rw [II_eq_nonExcludable_of_cell_nonempty ALT φ ⟨w, hwitness⟩]
  exact ⟨htarget_alt, fun hexc => hwitness.2.1 target hexc htarget⟩

/-! ### Consequences of a world of the cell -/

theorem exhIEII_implies_cell_witnessed_alt {target : Set World}
    (htarget_alt : target ∈ ALT)
    (w : World) (hwitness : cell ALT φ w) (htarget : target w) :
    ∀ u, exhIEII ALT φ u → target u := by
  intro u h_exh
  exact h_exh.2.2 target (mem_II_of_cell_witness ALT φ htarget_alt w hwitness htarget)

theorem exhIEII_implies_cell_witnessed_alts
    (targets : List (Set World))
    (h_in_alt : ∀ t ∈ targets, t ∈ ALT)
    (w : World) (hwitness : cell ALT φ w)
    (h_witness : ∀ t ∈ targets, t w) :
    ∀ u, exhIEII ALT φ u → ∀ t ∈ targets, t u :=
  fun u h_exh t ht =>
    exhIEII_implies_cell_witnessed_alt ALT φ
      (h_in_alt t ht) w hwitness (h_witness t ht) u h_exh

theorem exhIEII_negates_excludable {target : Set World}
    (h_ie : IsInnocentlyExcludable ALT φ target) :
    ∀ u, exhIEII ALT φ u → ¬ target u :=
  fun _ h_exh => h_exh.2.1 target h_ie

theorem not_isInnocentlyExcludable_of_cell_witness {target : Set World}
    (w : World) (hwitness : cell ALT φ w) (htarget : target w) :
    ¬ IsInnocentlyExcludable ALT φ target :=
  fun h_ie => hwitness.2.1 target h_ie htarget

/-! ### Cells from a characterization of innocent exclusion -/

theorem cell_eq_of_iff {P : Set World → Prop}
    (h : ∀ q ∈ ALT, IsInnocentlyExcludable ALT φ q ↔ P q) :
    cell ALT φ = {w | w ∈ φ ∧ ∀ q ∈ ALT, (w ∈ q ↔ ¬ P q)} := by
  ext w
  constructor
  · rintro ⟨hw, hIE, hne⟩
    exact ⟨hw, fun q hq ↦ ⟨fun hwq hP ↦ hIE q ((h q hq).2 hP) hwq,
      fun hP ↦ hne q ⟨hq, fun hIE' ↦ hP ((h q hq).1 hIE')⟩⟩⟩
  · rintro ⟨hw, h'⟩
    exact ⟨hw, fun q hIE hwq ↦ (h' q hIE.1).1 hwq ((h q hIE.1).1 hIE),
      fun r hr ↦ (h' r hr.1).2 fun hP ↦ hr.2 ((h r hr.1).2 hP)⟩

theorem cell_image_eq {ι : Type*} {f : ι → Set World} {I : Set ι} {P : ι → Prop}
    (h : ∀ i ∈ I, IsInnocentlyExcludable (f '' I) φ (f i) ↔ P i) :
    cell (f '' I) φ = {w | w ∈ φ ∧ ∀ i ∈ I, (w ∈ f i ↔ ¬ P i)} := by
  ext w
  constructor
  · rintro ⟨hw, hIE, hne⟩
    exact ⟨hw, fun i hi ↦ ⟨fun hwi hP ↦ hIE _ ((h i hi).2 hP) hwi,
      fun hP ↦ hne _ ⟨⟨i, hi, rfl⟩, fun hIE' ↦ hP ((h i hi).1 hIE')⟩⟩⟩
  · rintro ⟨hw, h'⟩
    refine ⟨hw, fun q hIE ↦ ?_, fun r hr ↦ ?_⟩
    · obtain ⟨i, hi, rfl⟩ := hIE.1
      exact fun hwi ↦ (h' i hi).1 hwi ((h i hi).1 hIE)
    · obtain ⟨i, hi, rfl⟩ := hr.1
      exact (h' i hi).2 fun hP ↦ hr.2 ((h i hi).2 hP)

/-! ### Representative minimal worlds -/

section MinimalCover

variable {ALT φ} {M : Set World}

theorem IsMinimalCover.singleton {w₀ : World} (hw₀ : w₀ ∈ φ) (h : ∀ q ∈ ALT, w₀ ∈ q → φ ⊆ q) :
    IsMinimalCover ALT φ {w₀} :=
  ⟨fun _ hv ↦ hv ▸ hw₀, fun _ hw ↦ ⟨w₀, rfl, fun q hq hq₀ ↦ h q hq hq₀ hw⟩, by simp⟩

theorem IsMinimalCover.cell_eq (hM : IsMinimalCover ALT φ M) :
    cell ALT φ = {w | w ∈ φ ∧ ∀ q ∈ ALT, (w ∈ q ↔ ∃ v ∈ M, v ∈ q)} := by
  ext w
  constructor
  · rintro ⟨hφ, hIE, hne⟩
    refine ⟨hφ, fun q hq ↦ ⟨fun hwq ↦ ?_, fun ⟨v, hv, hvq⟩ ↦ hne q ⟨hq, fun hIEq ↦ ?_⟩⟩⟩
    · by_contra hnone
      push Not at hnone
      exact hIE q ((hM.isInnocentlyExcludable_iff hq).2 hnone) hwq
    · exact (hM.isInnocentlyExcludable_iff hq).1 hIEq v hv hvq
  · rintro ⟨hφ, h⟩
    refine ⟨hφ, fun q hIEq hwq ↦ ?_, fun r ⟨hr, hnIE⟩ ↦ ?_⟩
    · obtain ⟨v, hv, hvq⟩ := (h q hIEq.1).1 hwq
      exact (hM.isInnocentlyExcludable_iff hIEq.1).1 hIEq v hv hvq
    · by_contra hnr
      exact hnIE ((hM.isInnocentlyExcludable_iff hr).2 fun v hv hvr ↦ hnr ((h r hr).2 ⟨v, hv, hvr⟩))

/-- With a representative set of minimal worlds and a consistent cell, exhaustification asserts
the prejacent and settles every alternative as the minimal worlds jointly do. -/
theorem IsMinimalCover.exhIEII_eq (hM : IsMinimalCover ALT φ M)
    (hne : ∃ w ∈ φ, ∀ q ∈ ALT, (w ∈ q ↔ ∃ v ∈ M, v ∈ q)) :
    exhIEII ALT φ = {w | w ∈ φ ∧ ∀ q ∈ ALT, (w ∈ q ↔ ∃ v ∈ M, v ∈ q)} := by
  rw [← hM.cell_eq]
  exact exhIEII_eq_cell_of_cell_nonempty ALT φ (by rw [hM.cell_eq]; exact hne)

/-- With a representative set of minimal worlds and a consistent cell, the innocently
includable alternatives are those true at some minimal world. -/
theorem IsMinimalCover.II_eq (hM : IsMinimalCover ALT φ M)
    (hne : ∃ w ∈ φ, ∀ q ∈ ALT, (w ∈ q ↔ ∃ v ∈ M, v ∈ q)) :
    II ALT φ = {r ∈ ALT | ∃ v ∈ M, v ∈ r} := by
  rw [II_eq_nonExcludable_of_cell_nonempty ALT φ (by rw [hM.cell_eq]; exact hne)]
  ext r
  exact and_congr_right fun hr ↦ by rw [hM.isInnocentlyExcludable_iff hr]; push Not; rfl

theorem exhIEII_eq_diff_of_forall_subset {d : Set World} (hd : d ∈ ALT)
    (hA : ∀ q ∈ ALT, q ≠ d → φ ⊆ q) (hne : ∃ w ∈ φ, w ∉ d) : exhIEII ALT φ = φ \ d := by
  obtain ⟨w₀, hw₀, hw₀d⟩ := hne
  have hM : IsMinimalCover ALT φ {w₀} :=
    .singleton hw₀ fun q hq hq₀ ↦ hA q hq fun h ↦ hw₀d (h ▸ hq₀)
  rw [hM.exhIEII_eq ⟨w₀, hw₀, by simp⟩]
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, exists_eq_left, Set.mem_sdiff]
  refine ⟨fun ⟨hw, h⟩ ↦ ⟨hw, fun hwd ↦ hw₀d ((h d hd).1 hwd)⟩, fun ⟨hw, hwd⟩ ↦ ⟨hw, fun q hq ↦ ?_⟩⟩
  by_cases hqd : q = d
  · subst hqd
    exact ⟨fun h ↦ absurd h hwd, fun h ↦ absurd h hw₀d⟩
  · exact ⟨fun _ ↦ hA q hq hqd hw₀, fun _ ↦ hA q hq hqd hw⟩

theorem exhIEII_eq_self_of_forall_subset (hA : ∀ q ∈ ALT, φ ⊆ q) (hsat : φ.Nonempty) :
    exhIEII ALT φ = φ := by
  obtain ⟨w₀, hw₀⟩ := hsat
  have hM : IsMinimalCover ALT φ {w₀} := .singleton hw₀ fun q hq _ ↦ hA q hq
  rw [hM.exhIEII_eq ⟨w₀, hw₀, by simp⟩]
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, exists_eq_left]
  exact ⟨And.left, fun hw ↦ ⟨hw, fun q hq ↦ iff_of_true (hA q hq hw) (hA q hq hw₀)⟩⟩

theorem exhIEII_singleton (hsat : φ.Nonempty) : exhIEII {φ} φ = φ :=
  exhIEII_eq_self_of_forall_subset (by simp) hsat

end MinimalCover

/-! ### Verified alternatives -/

section Verified

variable {ALT φ} {w : World}

/-- The cell of the prejacent consists of the prejacent worlds verifying exactly the alternatives
of the minimal verified sets. -/
theorem mem_cell_iff : w ∈ cell ALT φ ↔ w ∈ φ ∧ Preorder.satisfied (· ∈ ·) ALT w =
    ⋃₀ {P | Minimal (· ∈ Preorder.satisfied (· ∈ ·) ALT '' φ) P} := by
  change (w ∈ φ ∧ (∀ q, IsInnocentlyExcludable ALT φ q → w ∉ q) ∧
    (∀ r ∈ nonExcludable ALT φ, w ∈ r)) ↔ _
  refine and_congr_right fun _ ↦ ⟨fun ⟨hIE, hnon⟩ ↦ ?_, fun h ↦ ⟨fun q hq hwq ↦ ?_, fun r hr ↦ ?_⟩⟩
  · ext a
    refine ⟨fun ⟨ha, hwa⟩ ↦ by_contra fun hn ↦ hIE a ((isInnocentlyExcludable_iff_forall_minimal
      ha).2 fun P hP haP ↦ hn ⟨P, hP, haP⟩) hwa, fun ⟨P, hP, haP⟩ ↦ ?_⟩
    have hP' := hP
    obtain ⟨⟨u, hu, rfl⟩, -⟩ := hP'
    exact ⟨haP.1, hnon a ⟨haP.1, fun hIEa ↦
      (isInnocentlyExcludable_iff_forall_minimal haP.1).1 hIEa _ hP haP⟩⟩
  · obtain ⟨P, hP, hqP⟩ := (h ▸ (⟨hq.1, hwq⟩ : q ∈ Preorder.satisfied (· ∈ ·) ALT w) :
      q ∈ ⋃₀ {P | Minimal (· ∈ Preorder.satisfied (· ∈ ·) ALT '' φ) P})
    exact (isInnocentlyExcludable_iff_forall_minimal hq.1).1 hq P hP hqP
  · have : r ∈ ⋃₀ {P | Minimal (· ∈ Preorder.satisfied (· ∈ ·) ALT '' φ) P} := by
      by_contra hn
      exact hr.2 ((isInnocentlyExcludable_iff_forall_minimal hr.1).2 fun P hP hrP ↦
        hn ⟨P, hP, hrP⟩)
    exact (h ▸ this : r ∈ Preorder.satisfied (· ∈ ·) ALT w).2

theorem cell_nonempty_iff : (cell ALT φ).Nonempty ↔
    ⋃₀ {P | Minimal (· ∈ Preorder.satisfied (· ∈ ·) ALT '' φ) P} ∈
      Preorder.satisfied (· ∈ ·) ALT '' φ :=
  ⟨fun ⟨w, hw⟩ ↦ ⟨w, (mem_cell_iff.1 hw).1, (mem_cell_iff.1 hw).2⟩,
    fun ⟨w, hw, h⟩ ↦ ⟨w, mem_cell_iff.2 ⟨hw, h⟩⟩⟩

end Verified

end Exhaustification
