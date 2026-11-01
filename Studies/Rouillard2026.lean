module

public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Data.NNRat.BigOperators
public import Mathlib.MeasureTheory.Measure.AddContent
public import Linglib.Core.Order.Interval.Set.LinearOrder
public import Linglib.Semantics.Questions.HamblinSet
public import Linglib.Semantics.Aspect.SubintervalProperty
public import Linglib.Semantics.Negation.Polarity

/-!
# Rouillard 2026: temporal *in*-adverbials and maximal informativity

A temporal *in*-adverbial measures either an event, as in *Mary wrote up a paper in three days*
(an E-TIA), or a gap in which no event occurs, as in *Mary hasn't been sick in three days* (a
G-TIA). E-TIAs take telic but not atelic VPs, and G-TIAs are polarity items confined to negated
perfects. Rouillard derives both from the Maximal Informativity Principle: the numeral must be
able to be the maximally informative value of the property of numbers its constituent denotes.
An atelic VP has the subinterval property, so its E-TIA property does not depend on the numeral.
The perfect quantifies over open spans ending at speech time while run times are closed, so over
dense time no open span including a run time is smallest, though one excluding it is largest;
of the eight readings of *Mary has been sick in three days* and its negation, exactly one
survives.

## Main definitions

* `IsTimeMeasure`: an additive content on the spans of time, positive and onto the positive
  numbers on the spans ending at any time.
* `duration`: the measure of a closed time.
* `IsMIPLicensed`: licensing by maximal informativity, after Fox and Hackl.
* `eTIA`: the E-TIA property.
* `gTIA`: the G-TIA property.

## Implementation notes

* A measure of time is an `AddContent` on the half-open spans `Set.Ioc a b` of a linearly ordered
  time `T`, so the additivity over non-overlapping times of (6) is the finite additivity of the
  content. A closed time `[a, b]` is measured by its half-open counterpart, as §2.2.4 allows for
  open intervals. The span of a moment is empty and measures `0`, where the paper leaves moments
  outside the domain of `μ`.
* Numerals form a canonically ordered cancellative monoid, the paper's positive reals with `0`.
* Positivity on nondegenerate spans is the axiom, and (7) follows (`IsTimeMeasure.strictAntiOn`);
  the paper derives positivity from (7).
* The paper assumes (13) and the surjectivity of `μ` onto the positive reals. Both follow from one
  stronger axiom, that `pts(n, φ, s)` of (50) is defined for every positive `n` and every `s`, and
  (13) then holds with a final part.
* The subinterval property is the closed one of `Aspect/SubintervalProperty.lean`, the paper's
  (111).

## References

* [rouillard-2026]
* [fox-hackl-2006]
-/

@[expose] public section

namespace Rouillard2026

open Event (τ)

open Question Aspect MeasureTheory NonemptyInterval Set

/-! ### Measuring times (§2.2) -/

section Measure

variable {T α : Type*} [LinearOrder T] [AddCommMonoid α] [PartialOrder α]
  (μ : AddContent α {s : Set T | ∃ u v, u ≤ v ∧ s = Ioc u v})

/-- The duration of a closed time is the measure of its half-open counterpart (§2.2.4). -/
def duration (i : NonemptyInterval T) : α := μ (Ioc i.fst i.snd)

private theorem Ioc_mem {a b : T} (h : a ≤ b) :
    Ioc a b ∈ {s : Set T | ∃ u v, u ≤ v ∧ s = Ioc u v} :=
  ⟨a, b, h, rfl⟩

variable [CanonicallyOrderedAdd α] in
theorem duration_mono : Monotone (duration μ) := fun i j h ↦ by
  have : Nonempty T := ⟨i.fst⟩
  exact addContent_mono IsSetSemiring.Ioc (Ioc_mem i.fst_le_snd) (Ioc_mem j.fst_le_snd)
    (Ioc_subset_Ioc (le_def.1 h).1 (le_def.1 h).2)

/-- An additive content on the half-open spans is a temporal measure when it is positive on
nondegenerate spans and maps the spans ending at any time onto the positive numbers, so that
`pts(n, φ, s)` of (50) is always defined. -/
class IsTimeMeasure : Prop where
  pos : ∀ ⦃a b : T⦄, a < b → 0 < μ (Ioc a b)
  surjOn : ∀ s : T, SurjOn (fun l ↦ μ (Ioc l s)) (Iio s) (Ioi 0)

namespace IsTimeMeasure

variable {μ} [IsTimeMeasure μ]

theorem pos_iff {a b : T} : 0 < μ (Ioc a b) ↔ a < b :=
  ⟨fun h ↦ not_le.1 fun hba ↦ h.ne' (by rw [Ioc_eq_empty (not_lt.2 hba), addContent_empty]),
    fun h ↦ pos h⟩

variable (μ) [IsOrderedCancelAddMonoid α] in
-- (7)
theorem strictAntiOn (s : T) : StrictAntiOn (fun l ↦ μ (Ioc l s)) (Iic s) :=
  fun _ _ _ hb hab ↦ by
    dsimp only
    rw [← Ioc_union_Ioc_eq_Ioc hab.le hb, addContent_union' (Ioc_mem hab.le) (Ioc_mem hb)
      (Ioc_union_Ioc_eq_Ioc hab.le hb ▸ Ioc_mem (hab.le.trans hb)) (Ioc_disjoint_Ioc_of_le le_rfl)]
    exact lt_add_of_pos_left _ (pos hab)

variable (μ) [CanonicallyOrderedAdd α] in
theorem exists_Ioc_eq (s : T) (n : α) : ∃ l ≤ s, μ (Ioc l s) = n := by
  rcases (zero_le : 0 ≤ n).eq_or_lt with rfl | hn
  · exact ⟨s, le_rfl, by rw [Ioc_self, addContent_empty]⟩
  · obtain ⟨l, hl, hln⟩ := surjOn (μ := μ) s hn
    exact ⟨l, le_of_lt hl, hln⟩

variable [IsOrderedCancelAddMonoid α] [CanonicallyOrderedAdd α]

/-- Every larger number measures a leftward extension of a span, the surjectivity of a measure
onto the positive numbers (§2.2.3). -/
theorem exists_Ioc_eq_of_le {a s : T} {n : α} (h : μ (Ioc a s) ≤ n) :
    ∃ l ≤ a, μ (Ioc l s) = n := by
  obtain ⟨l, hls, rfl⟩ := exists_Ioc_eq μ s n
  exact ⟨l, le_of_not_gt fun hal ↦ (strictAntiOn μ s (hal.le.trans hls) hls hal).not_ge h, rfl⟩

/-- Every smaller number measures a final part of a span, (13). -/
theorem exists_Ioc_eq_of_ge {a s : T} {n : α} (has : a ≤ s) (h : n ≤ μ (Ioc a s)) :
    ∃ l ∈ Icc a s, μ (Ioc l s) = n := by
  obtain ⟨l, hls, rfl⟩ := exists_Ioc_eq μ s n
  exact ⟨l, ⟨le_of_not_gt fun hla ↦ (strictAntiOn μ s (hla.le.trans has) has hla).not_ge h,
    hls⟩, rfl⟩

end IsTimeMeasure

end Measure

variable {W T E α : Type*} [LinearOrder T] [Event.TemporalTrace E T]
  [AddCommMonoid α] [LinearOrder α] [IsOrderedCancelAddMonoid α] [CanonicallyOrderedAdd α]

/-! ### The Maximal Informativity Principle (§4.1.3) -/

/-- A property of numbers is licensed when at some world the numeral is its unique maximally
informative value, (92) with (75). -/
def IsMIPLicensed {N : Type*} (φ : N → Set W) : Prop :=
  ∃ w, ∃! n, IsStrongestTrueAnswer (range φ) w (φ n)

theorem not_isMIPLicensed_of_forall_eq {N : Type*} [Nontrivial N] {φ : N → Set W}
    (h : ∀ n m, φ n = φ m) : ¬ IsMIPLicensed φ := by
  rintro ⟨w, n, hn, huniq⟩
  obtain ⟨m, hm⟩ := exists_ne n
  obtain ⟨hnw, hmin⟩ := isStrongestTrueAnswer_range_iff.1 hn
  exact hm (huniq m (isStrongestTrueAnswer_range_iff.2 ⟨h n m ▸ hnw, fun k hk ↦ h n m ▸ hmin k hk⟩))

theorem not_isMIPLicensed_of_not_isLeast {N : Type*} [LinearOrder N] {φ : N → Set W}
    (hφ : Monotone φ) (h : ∀ w n, ¬ IsLeast {m | w ∈ φ m} n) : ¬ IsMIPLicensed φ := by
  rintro ⟨w, n, hn, huniq⟩
  obtain ⟨hnw, hmin⟩ := isStrongestTrueAnswer_range_iff.1 hn
  refine h w n ⟨hnw, fun m hm ↦ not_lt.1 fun hlt ↦ ?_⟩
  exact hlt.ne (huniq m (isStrongestTrueAnswer_range_iff.2
    ⟨hm, fun k hk ↦ (hφ hlt.le).trans (hmin k hk)⟩))

theorem isMIPLicensed_of_isGreatest {N : Type*} [LinearOrder N] {φ : N → Set W}
    (hφ : StrictAnti φ) {w : W} (h : ∃ n, IsGreatest {m | w ∈ φ m} n) : IsMIPLicensed φ := by
  obtain ⟨n, hn⟩ :=
    isExhaustivelyResolvable_range_iff_exists.1
      ((isExhaustivelyResolvable_range_iff_isGreatest hφ).2 h)
  refine ⟨w, n, hn, fun m hm ↦ hφ.injective (subset_antisymm ?_ ?_)⟩
  exacts [(isStrongestTrueAnswer_range_iff.1 hm).2 n (isStrongestTrueAnswer_range_iff.1 hn).1,
    (isStrongestTrueAnswer_range_iff.1 hn).2 m (isStrongestTrueAnswer_range_iff.1 hm).1]

theorem isMIPLicensed_of_isLeast {N : Type*} [LinearOrder N] {φ : N → Set W}
    (hφ : StrictMono φ) {w : W} (h : ∃ n, IsLeast {m | w ∈ φ m} n) : IsMIPLicensed φ := by
  obtain ⟨n, hn⟩ :=
    isExhaustivelyResolvable_range_iff_exists.1
      ((isExhaustivelyResolvable_range_iff_isLeast hφ).2 h)
  refine ⟨w, n, hn, fun m hm ↦ hφ.injective (subset_antisymm ?_ ?_)⟩
  exacts [(isStrongestTrueAnswer_range_iff.1 hm).2 n (isStrongestTrueAnswer_range_iff.1 hn).1,
    (isStrongestTrueAnswer_range_iff.1 hn).2 m (isStrongestTrueAnswer_range_iff.1 hm).1]

/-! ### E-TIAs (§4.1) -/

variable (μ : AddContent α {s : Set T | ∃ u v, u ≤ v ∧ s = Ioc u v}) [IsTimeMeasure μ]

/-- The E-TIA property (76) holds of `n` when `n` measures a time including a `Q`-event, `Q` being
the event predicate the rest of the LF supplies ((78) for the simple past). -/
def eTIA (Q : W → E → Prop) (n : α) : Set W :=
  {w | ∃ t, duration μ t = n ∧ ∃ e, Q w e ∧ τ e ≤ t}

theorem eTIA_monotone (Q : W → E → Prop) : Monotone (eTIA μ Q) := by
  rintro n m hnm w ⟨t, rfl, e, he, het⟩
  obtain ⟨l, hl, hlm⟩ := IsTimeMeasure.exists_Ioc_eq_of_le hnm
  exact ⟨⟨⟨l, t.snd⟩, hl.trans t.fst_le_snd⟩, hlm, e, he, het.trans (le_def.2 ⟨hl, le_rfl⟩)⟩

-- (83)
theorem eTIA_eq_of_hasSubintervalProperty {Q : W → E → Prop}
    (hQ : HasSubintervalProperty Q) (n m : α) : eTIA μ Q n = eTIA μ Q m := by
  suffices h : ∀ n m w, w ∈ eTIA μ Q n → w ∈ eTIA μ Q m from
    Set.ext fun w ↦ ⟨h n m w, h m n w⟩
  rintro n m w ⟨-, -, e, he, -⟩
  rcases le_total m (duration μ (τ e)) with hle | hge
  · obtain ⟨l, ⟨hl, hls⟩, hlm⟩ := IsTimeMeasure.exists_Ioc_eq_of_ge (τ e).fst_le_snd hle
    obtain ⟨e', he'τ, he'⟩ := hasSubintervalProperty_iff_witnesses.1 hQ e w he
      ⟨⟨l, (τ e).snd⟩, hls⟩ (le_def.2 ⟨hl, le_rfl⟩)
    exact ⟨⟨⟨l, (τ e).snd⟩, hls⟩, hlm, e', he', he'τ.le⟩
  · obtain ⟨l, hl, hlm⟩ := IsTimeMeasure.exists_Ioc_eq_of_le hge
    exact ⟨⟨⟨l, (τ e).snd⟩, hl.trans (τ e).fst_le_snd⟩, hlm, e, he, le_def.2 ⟨hl, le_rfl⟩⟩

/-- With an atelic VP, as in *Mary was sick in three days*, the E-TIA is not licensed. -/
theorem not_isMIPLicensed_eTIA [Nontrivial α] {Q : W → E → Prop}
    (hQ : HasSubintervalProperty Q) : ¬ IsMIPLicensed (eTIA μ Q) :=
  not_isMIPLicensed_of_forall_eq (eTIA_eq_of_hasSubintervalProperty μ hQ)

omit [IsOrderedCancelAddMonoid α] [IsTimeMeasure μ] in
theorem isLeast_eTIA {Q : W → E → Prop} {w : W} {e₀ : E} (h₀ : Q w e₀)
    (hmin : ∀ e, Q w e → duration μ (τ e₀) ≤ duration μ (τ e)) :
    IsLeast {n | w ∈ eTIA μ Q n} (duration μ (τ e₀)) :=
  ⟨⟨τ e₀, rfl, e₀, h₀, le_rfl⟩, fun _ ⟨_, ht, e, he, het⟩ ↦
    ht ▸ (hmin e he).trans (duration_mono μ het)⟩

omit [IsOrderedCancelAddMonoid α] [IsTimeMeasure μ] in
theorem isMIPLicensed_eTIA {Q : W → E → Prop} (hφ : StrictMono (eTIA μ Q)) {w : W}
    {e₀ : E} (h₀ : Q w e₀) (hmin : ∀ e, Q w e → duration μ (τ e₀) ≤ duration μ (τ e)) :
    IsMIPLicensed (eTIA μ Q) :=
  isMIPLicensed_of_isLeast hφ ⟨_, isLeast_eTIA μ h₀ hmin⟩

/-! ### G-TIAs (§4.2) -/

/-- The G-TIA property (101) holds of `n` when the open counterpart of the span of measure `n`
ending at `s`, `pts(n, d, s)` of (50), includes the closed run time of a `P`-event. -/
def gTIA (P : W → E → Prop) (s : T) (n : α) : Set W :=
  {w | ∃ l, μ (Ioc l s) = n ∧ ∃ e, P w e ∧ (τ e : Set T) ⊆ Ioo l s}

/-- `gTIANeg` is the negated G-TIA property (104). -/
def gTIANeg (P : W → E → Prop) (s : T) (n : α) : Set W := (gTIA μ P s n)ᶜ

theorem gTIA_monotone (P : W → E → Prop) (s : T) : Monotone (gTIA μ P s) := by
  rintro n m hnm w ⟨l, rfl, e, he, hei⟩
  obtain ⟨l', hl', hl'm⟩ := IsTimeMeasure.exists_Ioc_eq_of_le hnm
  exact ⟨l', hl'm, e, he, hei.trans (Ioo_subset_Ioo_left hl')⟩

theorem gTIANeg_antitone (P : W → E → Prop) (s : T) : Antitone (gTIANeg μ P s) :=
  fun _ _ h ↦ compl_subset_compl.2 (gTIA_monotone μ P s h)

omit [CanonicallyOrderedAdd α] in
-- §4.2.2
theorem exists_lt_of_mem_gTIA [DenselyOrdered T] {P : W → E → Prop} {s : T} {w : W}
    {n : α} (h : w ∈ gTIA μ P s n) : ∃ m, 0 < m ∧ m < n ∧ w ∈ gTIA μ P s m := by
  obtain ⟨l, rfl, e, he, hei⟩ := h
  obtain ⟨hl, hs⟩ := (Icc_subset_Ioo_iff (τ e).fst_le_snd).1 hei
  obtain ⟨l', hll', hl'⟩ := exists_between hl
  have hl's : l' < s := hl'.trans_le ((τ e).fst_le_snd.trans_lt hs).le
  exact ⟨μ (Ioc l' s), IsTimeMeasure.pos hl's,
    IsTimeMeasure.strictAntiOn μ s (hll'.trans hl's).le hl's.le hll',
    l', rfl, e, he, (Icc_subset_Ioo_iff (τ e).fst_le_snd).2 ⟨hl', hs⟩⟩

omit [CanonicallyOrderedAdd α] in
theorem not_isLeast_gTIA [DenselyOrdered T] (P : W → E → Prop) (s : T) (w : W) (n : α) :
    ¬ IsLeast {m | w ∈ gTIA μ P s m} n := fun ⟨hn, hlb⟩ ↦
  let ⟨_, _, hmn, hm⟩ := exists_lt_of_mem_gTIA μ hn
  hmn.not_ge (hlb hm)

/-- A positive G-TIA, as in *Mary has been sick in three days*, is not licensed over dense time. -/
theorem not_isMIPLicensed_gTIA [DenselyOrdered T] (P : W → E → Prop) (s : T) :
    ¬ IsMIPLicensed (gTIA μ P s) :=
  not_isMIPLicensed_of_not_isLeast (gTIA_monotone μ P s) (not_isLeast_gTIA μ P s)

-- §4.2.2
theorem isGreatest_gTIANeg {P : W → E → Prop} {s : T} {w : W} {l₀ : T}
    (hall : ∀ e, P w e → (τ e).fst ≤ l₀) (hwit : ∃ e, P w e ∧ (τ e).fst = l₀ ∧ (τ e).snd < s) :
    IsGreatest {n | w ∈ gTIANeg μ P s n} (μ (Ioc l₀ s)) := by
  obtain ⟨e₀, he₀, hfst, hsnd⟩ := hwit
  have hl : l₀ ≤ s := hfst ▸ (τ e₀).fst_le_snd.trans hsnd.le
  refine ⟨fun ⟨l, hlμ, e, he, hei⟩ ↦ ?_, fun n hn ↦ not_lt.1 fun hlt ↦ ?_⟩
  · have hll₀ : l < l₀ := ((Icc_subset_Ioo_iff (τ e).fst_le_snd).1 hei).1.trans_le (hall e he)
    exact (IsTimeMeasure.strictAntiOn μ s (hll₀.le.trans hl) hl hll₀).ne' hlμ
  · obtain ⟨l, hll₀, hlμ⟩ := IsTimeMeasure.exists_Ioc_eq_of_le hlt.le
    have hll₀ : l < l₀ := hll₀.lt_of_ne fun h ↦ hlt.ne (h ▸ hlμ)
    exact hn ⟨l, hlμ, e₀, he₀, (Icc_subset_Ioo_iff (τ e₀).fst_le_snd).2
      ⟨hll₀.trans_eq hfst.symm, hsnd⟩⟩

/-- In *Mary hasn't been sick in three days*, when worlds separate the gap's length, a negated
G-TIA is licensed at the world where the last event abuts the span. -/
theorem isMIPLicensed_gTIANeg {P : W → E → Prop} {s : T} (hφ : StrictAnti (gTIANeg μ P s))
    {w : W} {l₀ : T} (hall : ∀ e, P w e → (τ e).fst ≤ l₀)
    (hwit : ∃ e, P w e ∧ (τ e).fst = l₀ ∧ (τ e).snd < s) : IsMIPLicensed (gTIANeg μ P s) :=
  isMIPLicensed_of_isGreatest hφ ⟨_, isGreatest_gTIANeg μ hall hwit⟩

/-! ### The rational model -/

/-- `ratLength` measures a span of rational time by its length. -/
noncomputable def ratLength : AddContent ℚ≥0 {s : Set ℚ | ∃ u v, u ≤ v ∧ s = Ioc u v} where
  toFun s := (AddContent.onIoc id s).toNNRat
  empty' := by simp
  sUnion' I hI hdis hmem := by
    rw [addContent_sUnion hI hdis hmem, NNRat.toNNRat_sum_of_nonneg]
    intro u hu
    obtain ⟨a, b, hab, rfl⟩ := hI hu
    rw [AddContent.onIoc_apply hab]
    exact sub_nonneg.2 hab

theorem ratLength_Ioc {a b : ℚ} (h : a ≤ b) : ratLength (Ioc a b) = (b - a).toNNRat :=
  congrArg Rat.toNNRat (AddContent.onIoc_apply h)

instance : IsTimeMeasure ratLength where
  pos a b h := by simp [ratLength_Ioc h.le, h]
  surjOn s n hn := ⟨s - n, by simpa using hn, by simp [ratLength_Ioc]⟩

/-- The blocking theorem's hypotheses are jointly satisfiable at rational time. -/
example (P : W → NonemptyInterval ℚ → Prop) (s : ℚ) : ¬ IsMIPLicensed (gTIA ratLength P s) :=
  not_isMIPLicensed_gTIA ratLength P s

/-! ### Table 1 (§5.1.1)

The four readings of *Mary has been sick in three days* — E- or G-TIA under an E- or U-perfect
(perfective or imperfective aspect) — and their negations, over the positive numerals. -/

/-- The E-perfect hands an E-TIA the event predicate (114) of a `P`-event inside an open span
ending at `s`. -/
def ePerfFrame (P : W → E → Prop) (s : T) (w : W) (e : E) : Prop :=
  P w e ∧ ∃ l, (τ e : Set T) ⊆ Ioo l s

/-- The U-perfect hands an E-TIA the event predicate (117) of a `P`-event including a nondegenerate
open span ending at `s`. -/
def uPerfFrame (P : W → E → Prop) (s : T) (w : W) (e : E) : Prop :=
  P w e ∧ ∃ l < s, Ioo l s ⊆ (τ e : Set T)

/-- The G-TIA property under a U-perfect, (122), holds when some nondegenerate open span ending at
`s` lies inside a `P`-event and inside a time of measure `n`. -/
def uPerfGTIA (P : W → E → Prop) (s : T) (n : α) : Set W :=
  {w | ∃ t, duration μ t = n ∧
    ∃ l < s, Ioo l s ⊆ (t : Set T) ∧ ∃ e, P w e ∧ Ioo l s ⊆ (τ e : Set T)}

theorem hasSubintervalProperty_ePerfFrame {P : W → E → Prop} {s : T}
    (hP : HasSubintervalProperty P) : HasSubintervalProperty (ePerfFrame P s) :=
  hasSubintervalProperty_iff_witnesses.2 fun e w ⟨he, l, hei⟩ t ht ↦
    let ⟨e', he'τ, he'⟩ := hasSubintervalProperty_iff_witnesses.1 hP e w he t ht
    ⟨e', he'τ, he', l, he'τ ▸ (coe_subset_coe.2 ht).trans hei⟩

omit [IsOrderedCancelAddMonoid α] in
-- (117), (118)
theorem eTIA_uPerfFrame_eq [DenselyOrdered T] {P : W → E → Prop} {s : T}
    (hP : HasSubintervalProperty P) {n m : α} (hn : 0 < n) (hm : 0 < m) :
    eTIA μ (uPerfFrame P s) n = eTIA μ (uPerfFrame P s) m := by
  suffices h : ∀ n m : α, 0 < m → ∀ w, w ∈ eTIA μ (uPerfFrame P s) n →
      w ∈ eTIA μ (uPerfFrame P s) m from Set.ext fun w ↦ ⟨h n m hm w, h m n hn w⟩
  rintro n m hm w ⟨-, -, e, ⟨he, l, hls, hle⟩, -⟩
  obtain ⟨hel, hse⟩ := (Ioo_subset_Icc_iff hls).1 hle
  obtain ⟨l', -, hl'm⟩ := IsTimeMeasure.exists_Ioc_eq μ s m
  have hl's : l' < s := IsTimeMeasure.pos_iff.1 (hm.trans_eq hl'm.symm)
  obtain ⟨e', he'τ, he'⟩ := hasSubintervalProperty_iff_witnesses.1 hP e w he
    ⟨⟨max l l', s⟩, (max_lt hls hl's).le⟩ (le_def.2 ⟨hel.trans (le_max_left _ _), hse⟩)
  exact ⟨⟨⟨l', s⟩, hl's.le⟩, hl'm, e', ⟨he', max l l', max_lt hls hl's,
    he'τ ▸ Ioo_subset_Icc_self⟩, he'τ ▸ le_def.2 ⟨le_max_right _ _, le_rfl⟩⟩

omit [IsOrderedCancelAddMonoid α] in
-- (122), (123)
theorem uPerfGTIA_eq {P : W → E → Prop} {s : T} {n m : α} (hn : 0 < n) (hm : 0 < m) :
    uPerfGTIA μ P s n = uPerfGTIA μ P s m := by
  suffices h : ∀ n m : α, 0 < m → ∀ w, w ∈ uPerfGTIA μ P s n → w ∈ uPerfGTIA μ P s m from
    Set.ext fun w ↦ ⟨h n m hm w, h m n hn w⟩
  rintro n m hm w ⟨-, -, l, hls, -, e, he, hei⟩
  obtain ⟨l', -, hl'm⟩ := IsTimeMeasure.exists_Ioc_eq μ s m
  have hl's : l' < s := IsTimeMeasure.pos_iff.1 (hm.trans_eq hl'm.symm)
  exact ⟨⟨⟨l', s⟩, hl's.le⟩, hl'm, max l l', max_lt hls hl's,
    Ioo_subset_Icc_self.trans (Icc_subset_Icc_left (le_max_right _ _)), e, he,
    (Ioo_subset_Ioo_left (le_max_left _ _)).trans hei⟩

/-- An `Adverbial` is event-level or gap-level. -/
inductive Adverbial | event | gap
  deriving DecidableEq

/-- A `Viewpoint` is perfective (E-perfect) or imperfective (U-perfect) aspect under the perfect. -/
inductive Viewpoint | pfv | impv
  deriving DecidableEq

/-- `positiveReading` gives the four positive readings of *Mary has been sick in three days*. -/
def positiveReading (P : W → E → Prop) (s : T) : Adverbial → Viewpoint → α → Set W
  | .event, .pfv => eTIA μ (ePerfFrame P s)
  | .event, .impv => eTIA μ (uPerfFrame P s)
  | .gap, .pfv => gTIA μ P s
  | .gap, .impv => uPerfGTIA μ P s

/-- `reading` gives a cell of Table 1 over the positive numerals, the positive reading under the
row's polarity. -/
def reading (P : W → E → Prop) (s : T) (pol : Polarity) (a : Adverbial) (v : Viewpoint)
    (n : {n : α // 0 < n}) : Set W :=
  pol • positiveReading μ P s a v n

private instance [NoMaxOrder α] : Nontrivial {n : α // 0 < n} :=
  let ⟨n, hn⟩ := exists_gt (0 : α)
  let ⟨m, hm⟩ := exists_gt n
  ⟨⟨⟨n, hn⟩, ⟨m, hn.trans hm⟩, fun h ↦ hm.ne (congrArg Subtype.val h)⟩⟩

-- Table 1
theorem table1_blocked [DenselyOrdered T] [NoMaxOrder α] {P : W → E → Prop} {s : T}
    (hP : HasSubintervalProperty P) (pol : Polarity) (a : Adverbial) (v : Viewpoint)
    (h : (pol, a, v) ≠ (.negative, .gap, .pfv)) : ¬ IsMIPLicensed (reading μ P s pol a v) := by
  have hconst : ∀ a v, (a, v) ≠ (.gap, .pfv) → ∀ n m : {n : α // 0 < n},
      positiveReading μ P s a v n = positiveReading μ P s a v m := by
    rintro a v h ⟨n, hn⟩ ⟨m, hm⟩
    cases a <;> cases v
    · exact eTIA_eq_of_hasSubintervalProperty μ (hasSubintervalProperty_ePerfFrame hP) n m
    · exact eTIA_uPerfFrame_eq μ hP hn hm
    · exact absurd rfl h
    · exact uPerfGTIA_eq μ hn hm
  cases pol
  · cases a <;> cases v
    · exact not_isMIPLicensed_of_forall_eq (hconst .event .pfv (by decide))
    · exact not_isMIPLicensed_of_forall_eq (hconst .event .impv (by decide))
    · refine not_isMIPLicensed_of_not_isLeast (fun n m hnm ↦ gTIA_monotone μ P s hnm)
        fun w n ⟨hn, hlb⟩ ↦ ?_
      obtain ⟨m, hm, hmn, hw⟩ := exists_lt_of_mem_gTIA μ hn
      exact hmn.not_ge (hlb (a := ⟨m, hm⟩) hw)
    · exact not_isMIPLicensed_of_forall_eq (hconst .gap .impv (by decide))
  · refine not_isMIPLicensed_of_forall_eq fun n m ↦ congrArg compl (hconst a v ?_ n m)
    exact fun hav ↦ h (congrArg (Prod.mk Polarity.negative) hav)

/-- The survivor of Table 1 is negated G-TIA under perfective aspect, licensed where worlds separate
gap lengths and some world's last event abuts the span. -/
theorem table1_survivor {P : W → E → Prop} {s : T} (hφ : StrictAnti (gTIANeg μ P s))
    {w : W} {l₀ : T} (hall : ∀ e, P w e → (τ e).fst ≤ l₀)
    (hwit : ∃ e, P w e ∧ (τ e).fst = l₀ ∧ (τ e).snd < s) :
    IsMIPLicensed (reading μ P s .negative .gap .pfv) := by
  obtain ⟨e₀, he₀, hfst, hsnd⟩ := hwit
  have hl : l₀ < s := hfst ▸ (τ e₀).fst_le_snd.trans_lt hsnd
  refine isMIPLicensed_of_isGreatest (w := w) (fun n m hnm ↦ hφ (Subtype.coe_lt_coe.2 hnm))
    ⟨⟨μ (Ioc l₀ s), IsTimeMeasure.pos hl⟩, ?_⟩
  have hg := isGreatest_gTIANeg μ hall ⟨e₀, he₀, hfst, hsnd⟩
  exact ⟨hg.1, fun m hm ↦ Subtype.coe_le_coe.1 (hg.2 hm)⟩

end Rouillard2026
