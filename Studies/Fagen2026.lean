module

public import Linglib.Semantics.Quantification.Restriction
public import Linglib.Semantics.Exhaustification.MinimalWorlds
public import Studies.Spector2007

/-!
# Fagen (2026): Order selection: the logical foundations of exhaustivity

Fagen derives the exhaustive interpretation of an answer from its meaning and the question, with
no alternative sentences: an answer holds in the best worlds where it is true, and what varies is
the order that ranks them. The default order minimizes the question-property, as [the
minimal-worlds exhaustifier](##Fagen2026.exh_ltDefault) does; the hybrid order minimizes it within
an answer's positive restriction and maximizes it within the negative one, [concluding nothing
outside](##Fagen2026.mem_exh_ltHybrid_iff_of_inter), so that *some of the linguists but not all
of the computer scientists* [says that exactly one linguist and all but one computer scientist
attended](##Fagen2026.exh_selectedOrder_someButNotAll). Fagen selects the default order by
positive skew, [Spector's quasi-positivity](##Fagen2026.quasiPositive_iff_positivelySkewed), and
derives the choice from Preserve Restriction; yet when something lies outside an answer's
restriction, the default order preserves it [exactly when the answer's minimal sets cover
it](##Fagen2026.preservesRestriction_ltDefault_iff), which positive skew does not ensure.

## Implementation notes

* An answer is a quantifier `T` over individuals and the question a property `P : W → Set E` of
  worlds; exhaustive interpretation `exh P T r` takes the order `r` as a parameter, as (29) does.
* The worked examples take the worlds to be all extensions of the question-property, as Fagen's
  diagrams do. There the restriction operators over property intensions that Preserve Restriction
  applies to an exhaustified answer (25) are those of `exh id T r` as a quantifier.
* A proposition of Spector's question-relative language, a set of valuations of the atoms, is a
  quantifier over the atoms, `quantifierOf`.

## TODO

* Reduce Markedness, and the choice of an order that preserves the restriction in any domain the
  participants might assume (§3.2.1), are not formalized; nor are answers to second-order
  questions (§2.4) or the conditions under which the dual order is chosen (§3.3).
* The answers of Table 3.1 are not recorded as data.

## References

* [L. Fagen, *Order selection: the logical foundations of exhaustivity* (2026)][fagen-2026]
* [B. Spector, *Scalar implicatures: exhaustivity and Gricean reasoning* (2007)][spector-2007]
* [J. Groenendijk and M. Stokhof, *Studies on the semantics of questions and the pragmatics of
  answers* (1984)][groenendijk-stokhof-1984]
-/

@[expose] public section

namespace Fagen2026

open Set Quantifier

variable {E : Type*}

/-! ### Restriction and skew (§2.2, §3.1, Appendix) -/

section Restriction

variable {T : Quantifier E}

-- A4 on an infinite domain
theorem not_livesOn_restriction_cofinite :
    ¬ Quantifier.LivesOn (fun S : Set ℕ ↦ Sᶜ.Finite) (restriction fun S : Set ℕ ↦ Sᶜ.Finite) := by
  have hR : restriction (fun S : Set ℕ ↦ Sᶜ.Finite) = ∅ := by
    refine eq_empty_of_forall_notMem fun x ↦ notMem_restriction_iff.2 fun B ↦ ?_
    rw [compl_inter, compl_compl]
    exact ⟨fun h ↦ (finite_singleton x).union h, fun h ↦ h.subset subset_union_right⟩
  rw [hR]
  intro h
  exact infinite_univ (by simpa using (h univ).1 (by simp))

variable (T) in
/-- A quantifier is positively skewed when its restriction is its positive restriction ((2)). -/
def PositivelySkewed : Prop := restriction T = positiveRestriction T

variable (T) in
/-- A quantifier is negatively skewed when its restriction is its negative restriction ((2)). -/
def NegativelySkewed : Prop := restriction T = negativeRestriction T

theorem positivelySkewed_iff : PositivelySkewed T ↔ negativeRestriction T ⊆ positiveRestriction T :=
  by rw [PositivelySkewed, ← positiveRestriction_union_negativeRestriction, union_eq_left]

theorem negativelySkewed_iff : NegativelySkewed T ↔ positiveRestriction T ⊆ negativeRestriction T :=
  by rw [NegativelySkewed, ← positiveRestriction_union_negativeRestriction, union_eq_right]

-- A12
theorem positivelySkewed_of_monotone (hT : Monotone T) : PositivelySkewed T :=
  positivelySkewed_iff.2 (negativeRestriction_eq_empty_of_monotone hT ▸ empty_subset _)

-- A13
theorem negativelySkewed_of_antitone (hT : Antitone T) : NegativelySkewed T :=
  negativelySkewed_iff.2 (positiveRestriction_eq_empty_of_antitone hT ▸ empty_subset _)

end Restriction

/-! ### Orders over worlds (§2.1, §2.3, §3.3) -/

section Orders

variable {W : Type*} (P : W → Set E) (T : Quantifier E)

/-- The default order ranks worlds by inclusion of the question-property ((30)). -/
def ltDefault (v w : W) : Prop := P v ⊂ P w

/-- The positive component of the hybrid order ((31a)). -/
def ltPos (v w : W) : Prop :=
  P v ∩ positiveRestriction T ⊂ P w ∩ positiveRestriction T

/-- The negative component of the hybrid order ((31b)). -/
def ltNeg (v w : W) : Prop :=
  P w ∩ negativeRestriction T ⊂ P v ∩ negativeRestriction T

/-- `v` is hybrid-below `w` when it is below by either component ((31c)). -/
def leHybrid (v w : W) : Prop := ltPos P T v w ∨ ltNeg P T v w

/-- The hybrid order keeps the pairs on which the two components do not conflict ((31d)). -/
def ltHybrid (v w : W) : Prop := leHybrid P T v w ∧ ¬ leHybrid P T w v

/-- The dual order ranks worlds by reverse inclusion of the question-property ((39)). -/
def ltDual (v w : W) : Prop := P w ⊂ P v

/-- Exhaustive interpretation keeps the worlds where the answer holds of the question-property
and no such world lies below by the order `r` ((29)). -/
def exh (r : W → W → Prop) : Set W := {w | T (P w) ∧ ¬ ∃ v, T (P v) ∧ r v w}

open Classical in
/-- Order selection: a positively skewed answer takes the default order and any other answer the
hybrid order ((12)). -/
noncomputable def selectedOrder : W → W → Prop :=
  if PositivelySkewed T then ltDefault P else ltHybrid P T

open Exhaustification in
/-- Under the default order, exhaustive interpretation is the minimal-worlds exhaustifier over the
propositions that the question-property holds of each individual ((83)). -/
theorem exh_ltDefault :
    exh P T (ltDefault P) = exhMW (range fun x ↦ {w | x ∈ P w}) {w | T (P w)} := by
  have h : ∀ v w, Preorder.satisfied (· ∈ ·) (range fun x ↦ {w | x ∈ P w}) v ⊆
      Preorder.satisfied (· ∈ ·) (range fun x ↦ {w | x ∈ P w}) w ↔ P v ⊆ P w := fun v w ↦ by
    simp only [subset_def, Preorder.mem_satisfied, mem_range, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff, exists_apply_eq_apply, true_and, mem_ofPred_eq]
  ext w
  simp only [exh, mem_exhMW, MinimalFor, mem_ofPred_eq, h, ltDefault, ssubset_def, not_exists,
    not_and, not_not]

-- p. 70: the hybrid order is antisymmetric
theorem ltHybrid_asymm {v w : W} (h : ltHybrid P T v w) : ¬ ltHybrid P T w v :=
  fun h' ↦ h.2 h'.1

variable {P T}

theorem ltHybrid_iff_of_inter_eq {v v' w w' : W} (hv : P v ∩ restriction T = P v' ∩ restriction T)
    (hw : P w ∩ restriction T = P w' ∩ restriction T) :
    ltHybrid P T v w ↔ ltHybrid P T v' w' := by
  have hp : ∀ u, P u ∩ positiveRestriction T = (P u ∩ restriction T) ∩ positiveRestriction T :=
    fun u ↦ by rw [inter_assoc, inter_eq_right.2 positiveRestriction_subset_restriction]
  have hn : ∀ u, P u ∩ negativeRestriction T = (P u ∩ restriction T) ∩ negativeRestriction T :=
    fun u ↦ by rw [inter_assoc, inter_eq_right.2 negativeRestriction_subset_restriction]
  simp only [ltHybrid, leHybrid, ltPos, ltNeg, hp v, hp w, hn v, hn w, hv, hw, ← hp, ← hn]

/-- Exhaustive interpretation with the hybrid order treats alike two worlds that agree within the
answer's restriction, so it concludes nothing about objects outside it (§2.2.1). -/
theorem mem_exh_ltHybrid_iff_of_inter [Finite E] {w w' : W}
    (h : P w ∩ restriction T = P w' ∩ restriction T) :
    w ∈ exh P T (ltHybrid P T) ↔ w' ∈ exh P T (ltHybrid P T) := by
  have hT : T (P w) ↔ T (P w') := by
    rw [livesOn_restriction T (P w), livesOn_restriction T (P w'), inter_comm, h,
      inter_comm]
  simp only [exh, mem_ofPred_eq, hT, ltHybrid_iff_of_inter_eq rfl h]

theorem not_ltHybrid_of_eq (h : T.positiveRestriction = T.negativeRestriction) (v w : W) :
    ¬ ltHybrid P T v w := fun ⟨hvw, hwv⟩ ↦ hwv <| by
  simp only [leHybrid, ltPos, ltNeg, h] at hvw ⊢
  exact hvw.symm

-- p. 104: the hybrid order leaves an answer with equal restrictions as it is
theorem exh_ltHybrid_of_eq (h : T.positiveRestriction = T.negativeRestriction) :
    exh P T (ltHybrid P T) = {w | T (P w)} := by
  ext w
  simp [exh, not_ltHybrid_of_eq h]

end Orders

/-! ### Preserve Restriction (§3.2) -/

section Preserve

variable {T : Quantifier E} {S : Set E}

variable (T) in
/-- (26): an order preserves an answer's restriction when the restriction, the positive
restriction or the negative restriction of the exhaustified answer is the answer's restriction. -/
def PreservesRestriction (r : Set E → Set E → Prop) : Prop :=
  restriction (· ∈ exh id T r) = T.restriction ∨
    positiveRestriction (· ∈ exh id T r) = T.restriction ∨
    negativeRestriction (· ∈ exh id T r) = T.restriction

theorem mem_exh_ltDefault_id : S ∈ exh id T (ltDefault id) ↔ Minimal T S := by
  simp only [exh, mem_ofPred_eq, ltDefault, id, ssubset_def, not_exists, not_and, not_not, Minimal]

/-- When something lies outside an answer's restriction, the default order preserves the
restriction exactly when the answer's minimal sets cover it. -/
theorem preservesRestriction_ltDefault_iff [Finite E] (h : T.restriction ≠ univ) :
    PreservesRestriction T (ltDefault id) ↔ ⋃₀ {S | Minimal T S} = T.restriction := by
  have hexh : (· ∈ exh id T (ltDefault id)) = (Minimal T ·) :=
    funext fun _ ↦ propext mem_exh_ltDefault_id
  have hpos : positiveRestriction (Minimal T ·) = ⋃₀ {S | Minimal T S} :=
    positiveRestriction_subset_sUnion.antisymm fun x hx ↦
      let ⟨M, hM, hxM⟩ := mem_sUnion.1 hx
      subset_positiveRestriction_of_minimal (Q := (Minimal T ·))
        ⟨hM, fun _ hS hSM ↦ hM.2 hS.1 hSM⟩ hxM
  rw [PreservesRestriction, hexh, hpos]
  refine ⟨fun hP ↦ ?_, fun hU ↦ .inr (.inl hU)⟩
  obtain ⟨y, hy⟩ := (ne_univ_iff_exists_notMem _).1 h
  by_cases hA : ∃ M, Minimal T M
  · obtain ⟨M, hM⟩ := hA
    have hyM : y ∉ M := fun hyM ↦
      hy (positiveRestriction_subset_restriction (subset_positiveRestriction_of_minimal hM hyM))
    have hyN : y ∈ negativeRestriction (Minimal T ·) := mem_negativeRestriction_iff.2
      ⟨M, hM, fun h' ↦ hyM (h'.2 hM.1 (subset_insert y M) (mem_insert y M))⟩
    rcases hP with hP | hP | hP
    · exact (hy (hP ▸ negativeRestriction_subset_restriction hyN)).elim
    · exact hP
    · exact (hy (hP ▸ hyN)).elim
  · have hT : ∀ S, ¬ T S := fun S hS ↦
      hA (let ⟨M, _, hM⟩ := exists_minimal_le_of_wellFoundedLT T S hS; ⟨M, hM⟩)
    have hU : ⋃₀ {S | Minimal T S} = ∅ := sUnion_eq_empty.2 fun S hS ↦ absurd ⟨S, hS⟩ hA
    rw [hU, eq_comm, ← positiveRestriction_union_negativeRestriction, union_empty_iff]
    exact ⟨eq_empty_of_forall_notMem fun _ ⟨_, _, hS⟩ ↦ hT _ hS,
      eq_empty_of_forall_notMem fun _ ⟨_, _, hS⟩ ↦ hT _ hS⟩

end Preserve

/-! ### Worked examples (§2.1.2, §2.3) -/

section Examples

-- (6): *Agnes* takes the default order and says that Agnes alone has the property
theorem exh_selectedOrder_individual (a : E) :
    exh id (individual a) (selectedOrder id (individual a)) = {{a}} := by
  have hmono : Monotone (individual a) := fun _ _ h ha ↦ h ha
  simp only [selectedOrder, positivelySkewed_of_monotone hmono, ↓reduceIte]
  ext S
  simp only [exh, mem_ofPred_eq, individual, ltDefault, id, mem_singleton_iff, not_exists, not_and]
  constructor
  · rintro ⟨ha, h⟩
    by_contra hne
    exact h {a} (mem_singleton a)
      (ssubset_iff_subset_ne.2 ⟨singleton_subset_iff.2 ha, fun h' ↦ hne h'.symm⟩)
  · rintro rfl
    exact ⟨mem_singleton a, fun v hv hlt ↦ hlt.ne (hlt.subset.antisymm (singleton_subset_iff.2 hv))⟩

-- (33): *not Beatrice* licenses nothing beyond itself
theorem exh_ltHybrid_not (b : E) :
    exh id (fun S ↦ b ∉ S) (ltHybrid id fun S ↦ b ∉ S) = {S | b ∉ S} := by
  ext S
  refine ⟨fun h ↦ h.1, fun hS ↦ ⟨hS, ?_⟩⟩
  rintro ⟨v, hv, (hpos | hneg), -⟩
  · obtain ⟨y, ⟨-, hy⟩, -⟩ := exists_of_ssubset hpos
    rw [positiveRestriction_eq_empty_of_antitone (Q := fun S ↦ b ∉ S)
      fun _ _ h hB hA ↦ hB (h hA)] at hy
    exact hy
  · obtain ⟨y, ⟨hyv, S', hS', hS'y⟩, -⟩ := exists_of_ssubset hneg
    have hyb : y = b := by_contra fun hne ↦ hS'y ⟨not_not.1 hS', fun h ↦ hne h.symm⟩
    exact hv (hyb ▸ hyv)

-- (39), §3.3.1: under the dual order *not Beatrice* says that everyone else has the property
theorem exh_ltDual_not (b : E) : exh id (fun S ↦ b ∉ S) (ltDual id) = {{b}ᶜ} := by
  ext S
  simp only [exh, mem_ofPred_eq, ltDual, id, mem_singleton_iff, not_exists, not_and]
  constructor
  · rintro ⟨hb, h⟩
    by_contra hne
    exact h {b}ᶜ (fun h' ↦ h' rfl)
      (ssubset_iff_subset_ne.2 ⟨subset_compl_singleton_iff.2 hb, hne⟩)
  · rintro rfl
    exact ⟨fun h ↦ h rfl,
      fun v hv hlt ↦ not_subset_of_ssubset hlt (subset_compl_singleton_iff.2 hv)⟩

variable {L C : Set E}

/-- *Some of the `L` but not all of the `C`*. -/
def someButNotAll (L C : Set E) : Quantifier E := fun S ↦ (S ∩ L).Nonempty ∧ ¬ C ⊆ S

theorem positiveRestriction_someButNotAll (hLC : Disjoint L C) (hC : C.Nonempty) :
    positiveRestriction (someButNotAll L C) = L := by
  ext x
  constructor
  · rintro ⟨S, hS, ⟨y, hyS, hyL⟩, hCS⟩
    by_contra hx
    refine hS ⟨⟨y, ?_, hyL⟩, fun h ↦ hCS (h.trans (subset_insert x S))⟩
    rcases hyS with rfl | hyS
    · exact absurd hyL hx
    · exact hyS
  · intro hx
    refine ⟨∅, fun h ↦ (h.1.ne_empty (by simp)), ⟨x, by simp, hx⟩, fun h ↦ ?_⟩
    obtain ⟨c, hc⟩ := hC
    have hcx : c = x := by simpa using h hc
    exact hLC.ne_of_mem hx (hcx ▸ hc) rfl

theorem negativeRestriction_someButNotAll (hLC : Disjoint L C) (hL : L.Nonempty) :
    negativeRestriction (someButNotAll L C) = C := by
  ext x
  constructor
  · rintro ⟨S, hS, ⟨y, hyS, hyL⟩, hCS⟩
    by_contra hx
    exact hS ⟨⟨y, hyS.1, hyL⟩, fun h ↦ hCS fun c hc ↦ ⟨h hc, fun hcx ↦ hx (hcx ▸ hc)⟩⟩
  · intro hx
    obtain ⟨l, hl⟩ := hL
    refine ⟨L ∪ C, fun h ↦ h.2 subset_union_right, ⟨l, ⟨.inl hl, ?_⟩, hl⟩, fun h ↦ ?_⟩
    · rintro rfl
      exact hLC.ne_of_mem hl hx rfl
    · exact (h hx).2 rfl

theorem not_positivelySkewed_someButNotAll (hLC : Disjoint L C) (hL : L.Nonempty)
    (hC : C.Nonempty) : ¬ PositivelySkewed (someButNotAll L C) := fun h ↦ by
  rw [positivelySkewed_iff, positiveRestriction_someButNotAll hLC hC,
    negativeRestriction_someButNotAll hLC hL] at h
  obtain ⟨c, hc⟩ := hC
  exact hLC.ne_of_mem (h hc) hc rfl

/-- *Some of the `L` but not all of the `C`* takes the hybrid order and says that exactly one `L`
and all but one `C` have the property ((40)). -/
theorem exh_selectedOrder_someButNotAll (hLC : Disjoint L C) (hL : L.Nonempty)
    (hC : C.Nonempty) :
    exh id (someButNotAll L C) (selectedOrder id (someButNotAll L C)) =
      {S | (∃ l, S ∩ L = {l}) ∧ ∃ c, C \ S = {c}} := by
  simp only [selectedOrder, not_positivelySkewed_someButNotAll hLC hL hC, ↓reduceIte]
  have hd : ∀ z, z ∈ L → z ∉ C := fun z hz hz' ↦ hLC.ne_of_mem hz hz' rfl
  have hlt : ∀ v w : Set E, ltHybrid id (someButNotAll L C) v w ↔
      (v ∩ L ⊂ w ∩ L ∨ w ∩ C ⊂ v ∩ C) ∧ ¬ (w ∩ L ⊂ v ∩ L ∨ v ∩ C ⊂ w ∩ C) := fun v w ↦ by
    simp only [ltHybrid, leHybrid, ltPos, ltNeg, positiveRestriction_someButNotAll hLC hC,
      negativeRestriction_someButNotAll hLC hL, id]
  ext S
  simp only [exh, mem_ofPred_eq, id, hlt, someButNotAll]
  constructor
  · rintro ⟨⟨⟨y, hyS, hyL⟩, hCS⟩, hmin⟩
    obtain ⟨c, hcC, hcS⟩ := not_subset.1 hCS
    refine ⟨⟨y, eq_singleton_iff_unique_mem.2 ⟨⟨hyS, hyL⟩, fun l ⟨hlS, hlL⟩ ↦ ?_⟩⟩,
      ⟨c, eq_singleton_iff_unique_mem.2 ⟨⟨hcC, hcS⟩, fun d ⟨hdC, hdS⟩ ↦ ?_⟩⟩⟩
    · -- a second linguist: drop every linguist but `y`
      by_contra hly
      have hvL : ∀ z, z ∈ (S \ L) ∪ {y} → z ∈ L → z = y := fun z hz hzL ↦
        hz.elim (fun h ↦ absurd hzL h.2) id
      have hvC : ∀ z ∈ C, z ∈ (S \ L) ∪ {y} ↔ z ∈ S := fun z hzC ↦
        ⟨fun h ↦ h.elim And.left fun h ↦ absurd (h ▸ hyL) (fun h' ↦ hd z h' hzC),
          fun h ↦ .inl ⟨h, fun h' ↦ hd z h' hzC⟩⟩
      refine hmin ⟨(S \ L) ∪ {y}, ⟨⟨y, .inr rfl, hyL⟩, fun h ↦ hcS ((hvC c hcC).1 (h hcC))⟩,
        .inl (ssubset_iff_of_subset (fun z (hz : z ∈ ((S \ L) ∪ {y}) ∩ L) ↦
          hvL z hz.1 hz.2 ▸ ⟨hyS, hyL⟩) |>.2
          ⟨l, ⟨hlS, hlL⟩, fun ⟨hl, _⟩ ↦ hly (hvL l hl hlL)⟩), ?_⟩
      rintro (h | h)
      · exact hly (hvL l (h.subset ⟨hlS, hlL⟩).1 hlL)
      · obtain ⟨z, ⟨hzS, hzC⟩, hz⟩ := exists_of_ssubset h
        exact hz ⟨(hvC z hzC).2 hzS, hzC⟩
    · -- a second missing computer scientist: add `d`
      by_contra hdc
      refine hmin ⟨insert d S, ⟨⟨y, .inr hyS, hyL⟩, fun h ↦ (h hcC).elim
          (fun h ↦ hdc h.symm) hcS⟩,
        .inr (ssubset_iff_of_subset (fun z (hz : z ∈ S ∩ C) ↦ (⟨.inr hz.1, hz.2⟩ :
          z ∈ insert d S ∩ C)) |>.2
          ⟨d, ⟨.inl rfl, hdC⟩, fun h ↦ hdS h.1⟩), ?_⟩
      rintro (h | h)
      · obtain ⟨z, ⟨hz, hzL⟩, hzS⟩ := exists_of_ssubset h
        exact hz.elim (fun h ↦ hd z hzL (h ▸ hdC)) fun h ↦ hzS ⟨h, hzL⟩
      · exact hdS (h.subset ⟨.inl rfl, hdC⟩).1
  · rintro ⟨⟨l, hl⟩, c, hc⟩
    have hcm : c ∈ C \ S := hc.symm ▸ mem_singleton c
    refine ⟨⟨⟨l, hl.symm ▸ mem_singleton l⟩, fun h ↦ hcm.2 (h hcm.1)⟩,
      fun ⟨v, ⟨hvL, hCv⟩, h, _⟩ ↦ ?_⟩
    rcases h with h | h
    · rw [hl, ssubset_singleton_iff] at h
      exact hvL.ne_empty h
    · refine hCv fun z hzC ↦ ?_
      by_cases hzS : z ∈ S
      · exact (h.subset ⟨hzS, hzC⟩).1
      · obtain ⟨y, ⟨hyv, hyC⟩, hy⟩ := exists_of_ssubset h
        have hyc : y = c := by
          have : y ∈ C \ S := ⟨hyC, fun hyS ↦ hy ⟨hyS, hyC⟩⟩
          rwa [hc] at this
        have hzc : z = c := by
          have : z ∈ C \ S := ⟨hzC, hzS⟩
          rwa [hc] at this
        exact hzc ▸ hyc ▸ hyv

-- Table 3.2: under the default order *some of the `L`* says that exactly one `L` has the property
theorem exh_ltDefault_some :
    exh id (fun S ↦ (S ∩ L).Nonempty) (ltDefault id) = {S | ∃ l ∈ L, S = {l}} := by
  ext S
  rw [mem_exh_ltDefault_id]
  constructor
  · rintro ⟨⟨l, hlS, hlL⟩, hmin⟩
    exact ⟨l, hlL, (hmin ⟨l, mem_singleton l, hlL⟩ (singleton_subset_iff.2 hlS)).antisymm
      (singleton_subset_iff.2 hlS)⟩
  · rintro ⟨l, hlL, rfl⟩
    refine ⟨⟨l, mem_singleton l, hlL⟩, fun y ⟨z, hzy, _⟩ hy ↦ ?_⟩
    obtain rfl : z = l := hy hzy
    exact singleton_subset_iff.2 hzy

/-- *All or none of the `L`*. -/
def allOrNone (L : Set E) : Quantifier E := fun S ↦ L ⊆ S ∨ Disjoint S L

theorem allOrNone_livesOn : (allOrNone L).LivesOn L := fun B ↦ by
  simp only [allOrNone, subset_inter_iff, subset_rfl, true_and]
  exact or_congr_right ⟨fun h ↦ h.mono_left inter_subset_right,
    fun h ↦ disjoint_left.2 fun z hzB hzL ↦ disjoint_left.1 h ⟨hzL, hzB⟩ hzL⟩

theorem positiveRestriction_allOrNone (hL : L.Nontrivial) :
    (allOrNone L).positiveRestriction = L := by
  refine (positiveRestriction_subset_restriction.trans
    allOrNone_livesOn.restriction_subset).antisymm fun x hx ↦ ?_
  obtain ⟨z, hzL, hzx⟩ := hL.exists_ne x
  refine ⟨L \ {x}, fun h ↦ h.elim (fun h ↦ (h hx).2 (mem_singleton x))
    fun h ↦ disjoint_left.1 h ⟨hzL, hzx⟩ hzL, .inl ?_⟩
  rw [insert_sdiff_singleton]
  exact subset_insert x L

theorem negativeRestriction_allOrNone (hL : L.Nontrivial) :
    (allOrNone L).negativeRestriction = L := by
  refine (negativeRestriction_subset_restriction.trans
    allOrNone_livesOn.restriction_subset).antisymm fun x hx ↦ ?_
  obtain ⟨z, hzL, hzx⟩ := hL.exists_ne x
  refine ⟨{x}, fun h ↦ h.elim (fun h ↦ hzx (h hzL)) fun h ↦ disjoint_left.1 h (mem_singleton x) hx,
    .inr ?_⟩
  rw [sdiff_self]
  exact empty_disjoint L

theorem positivelySkewed_allOrNone (hL : L.Nontrivial) : PositivelySkewed (allOrNone L) :=
  positivelySkewed_iff.2
    ((negativeRestriction_allOrNone hL).trans (positiveRestriction_allOrNone hL).symm).subset

theorem minimal_allOrNone_iff {S : Set E} : Minimal (allOrNone L) S ↔ S = ∅ :=
  ⟨fun h ↦ subset_empty_iff.1 (h.2 (.inr (empty_disjoint L)) (empty_subset S)),
    by rintro rfl; exact ⟨.inr (empty_disjoint L), fun _ _ _ ↦ empty_subset _⟩⟩

-- (12): *all or none of the `L`* takes the default order and says that nothing has the property
theorem exh_selectedOrder_allOrNone (hL : L.Nontrivial) :
    exh id (allOrNone L) (selectedOrder id (allOrNone L)) = {∅} := by
  simp only [selectedOrder, positivelySkewed_allOrNone hL, ↓reduceIte]
  ext S
  rw [mem_exh_ltDefault_id, minimal_allOrNone_iff, mem_singleton_iff]

-- (26): the default order does not preserve the restriction of *all or none of the `L`*
theorem not_preservesRestriction_allOrNone [Finite E] {y : E} (hL : L.Nontrivial) (hy : y ∉ L) :
    ¬ PreservesRestriction (allOrNone L) (ltDefault id) := by
  have hR : (allOrNone L).restriction = L := allOrNone_livesOn.restriction_subset.antisymm
    ((positiveRestriction_allOrNone hL).symm.subset.trans positiveRestriction_subset_restriction)
  rw [preservesRestriction_ltDefault_iff
    (by rw [hR]; exact (ne_univ_iff_exists_notMem L).2 ⟨y, hy⟩), hR]
  simp only [minimal_allOrNone_iff, ofPred_eq_eq_singleton, sUnion_singleton]
  exact hL.nonempty.ne_empty.symm

-- (26): the hybrid order leaves *all or none of the `L`* as it is
theorem exh_ltHybrid_allOrNone (hL : L.Nontrivial) :
    exh id (allOrNone L) (ltHybrid id (allOrNone L)) = {S | allOrNone L S} :=
  exh_ltHybrid_of_eq
    ((positiveRestriction_allOrNone hL).trans (negativeRestriction_allOrNone hL).symm)

-- §3.1.2: *Charmian and exactly one of Agnes and Beatrice* is skewed only positively
theorem positivelySkewed_not_negativelySkewed_oneOf {a b c : E} (hab : a ≠ b) (hca : c ≠ a)
    (hcb : c ≠ b) :
    let T : Quantifier E := fun S ↦ c ∈ S ∧ (a ∈ S ↔ b ∉ S)
    ¬ Monotone T ∧ ¬ Antitone T ∧ PositivelySkewed T ∧ ¬ NegativelySkewed T := by
  intro T
  have hT : T {a, c} := by simp [T, hab.symm, hcb.symm]
  have hc : ¬ T {c} := by simp [T, hca.symm, hcb.symm]
  have hpos : {a, b, c} ⊆ T.positiveRestriction :=
    insert_subset_iff.2 ⟨⟨{c}, hc, hT⟩, insert_subset_iff.2 ⟨⟨{c}, hc, by simp [T, hab, hca.symm]⟩,
      singleton_subset_iff.2 ⟨{a}, by simp [T, hca], by simp [T, hab.symm, hcb.symm]⟩⟩⟩
  have hlive : T.LivesOn {a, b, c} := fun B ↦ by simp [T]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_, positivelySkewed_iff.2
    (negativeRestriction_subset_restriction.trans (hlive.restriction_subset.trans hpos)),
    fun h ↦ ?_⟩
  · simpa [T] using h (show ({a, c} : Set E) ⊆ {a, b, c} by simp [insert_subset_iff]) hT
  · simpa [T] using h (empty_subset {a, c}) hT
  · obtain ⟨S, -, hS⟩ := negativelySkewed_iff.1 h (hpos (show c ∈ ({a, b, c} : Set E) by simp))
    exact hS.1.2 (mem_singleton c)

-- p. 70: the hybrid order is not transitive with three linguists and three computer scientists
theorem not_transitive_ltHybrid :
    let r := ltHybrid (fun w : Finset (Fin 6) ↦ (w : Set (Fin 6)))
      (someButNotAll ↑({0, 1, 2} : Finset (Fin 6)) ↑({3, 4, 5} : Finset (Fin 6)))
    r {0, 4} {0, 1, 3, 5} ∧ r {0, 1, 3, 5} {2, 3} ∧ ¬ r {0, 4} {2, 3} := by
  have hLC : Disjoint (↑({0, 1, 2} : Finset (Fin 6)) : Set (Fin 6))
      ↑({3, 4, 5} : Finset (Fin 6)) := Finset.disjoint_coe.2 (by decide)
  have hL : (↑({0, 1, 2} : Finset (Fin 6)) : Set (Fin 6)).Nonempty := ⟨0, by simp⟩
  have hC : (↑({3, 4, 5} : Finset (Fin 6)) : Set (Fin 6)).Nonempty := ⟨3, by simp⟩
  simp only [ltHybrid, leHybrid, ltPos, ltNeg, positiveRestriction_someButNotAll hLC hC,
    negativeRestriction_someButNotAll hLC hL, ← Finset.coe_inter, Finset.coe_ssubset]
  decide

end Examples

/-! ### Spector's favoring (§1.3.2, §2.2.2) -/

section Spector

open Spector2007

variable {Atom : Type*} [DecidableEq Atom] {P : Proposition Atom} {x : Atom}

/-- A proposition of Spector's question-relative language, a set of valuations of the atoms, as a
quantifier over the atoms: it holds of the sets of atoms its valuations make true. -/
def quantifierOf (P : Proposition Atom) : Quantifier Atom := fun S ↦ ∃ V ∈ P, (V : Set Atom) = S

-- p. 67: favoring a positive literal is membership in the positive restriction
theorem favors_pos_iff : Favors P (.pos x) ↔ x ∈ positiveRestriction (quantifierOf P) := by
  rw [mem_positiveRestriction_iff]
  constructor
  · rintro ⟨V, hV, hx, hflip⟩
    refine ⟨V, ⟨V, hV, rfl⟩, fun ⟨V', hV', hV'eq⟩ ↦ hflip ?_⟩
    have hx : x ∈ V := hx
    have : V' = V.erase x := Finset.coe_injective (by rw [hV'eq, Finset.coe_erase])
    rw [show Spector2007.flip V (.pos x) = V.erase x by simp [Spector2007.flip, Literal.atom, hx],
      ← this]
    exact hV'
  · rintro ⟨S, ⟨V, hV, rfl⟩, hS⟩
    have hx : x ∈ V := by_contra fun h ↦ hS ⟨V, hV, by rw [sdiff_singleton_eq_self (by simpa)]⟩
    refine ⟨V, hV, hx, fun h ↦ hS ⟨_, h, ?_⟩⟩
    simp [Spector2007.flip, Literal.atom, hx]

-- p. 67: favoring a negative literal is membership in the negative restriction
theorem favors_neg_iff : Favors P (.neg x) ↔ x ∈ negativeRestriction (quantifierOf P) := by
  rw [mem_negativeRestriction_iff]
  constructor
  · rintro ⟨V, hV, hx, hflip⟩
    refine ⟨V, ⟨V, hV, rfl⟩, fun ⟨V', hV', hV'eq⟩ ↦ hflip ?_⟩
    have hx : x ∉ V := hx
    have : V' = insert x V := Finset.coe_injective (by rw [hV'eq, Finset.coe_insert])
    rw [show Spector2007.flip V (.neg x) = insert x V by simp [Spector2007.flip, Literal.atom, hx],
      ← this]
    exact hV'
  · rintro ⟨S, ⟨V, hV, rfl⟩, hS⟩
    have hx : x ∉ V := fun h ↦ hS ⟨V, hV, by rw [insert_eq_of_mem (by simpa)]⟩
    refine ⟨V, hV, hx, fun h ↦ hS ⟨_, h, ?_⟩⟩
    simp [Spector2007.flip, Literal.atom, hx]

/-- A proposition is quasi-positive in Spector's sense, strongly favoring no negative literal,
just when the quantifier it determines is positively skewed (§2.1.1, after Spector's (77b)). -/
theorem quasiPositive_iff_positivelySkewed :
    (∀ x, ¬ (Favors P (.neg x) ∧ ¬ Favors P (.pos x))) ↔ PositivelySkewed (quantifierOf P) := by
  simp only [positivelySkewed_iff, favors_neg_iff, favors_pos_iff, not_and, not_not]
  rfl

end Spector

end Fagen2026
