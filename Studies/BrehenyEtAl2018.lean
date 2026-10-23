module

public import Studies.TrinhHaida2015
public import Linglib.Data.Examples.BrehenyEtAl2018

/-!
# Breheny, Klinedinst, Romoli and Sudo (2018): the symmetry problem

[breheny-et-al-2018] survey the symmetry problem for the alternatives of scalar implicature: an
assertion `S` implicating `¬A` must have `A` among its alternatives but not `S ∧ ¬A`, which
would implicate the opposite. On the structural approach of [katzir-2007] and
[fox-katzir-2011] the alternatives negated are a contextual subset `C` of the formal
alternatives `F(S)` obeying the closure condition (8): `S ∈ C`, and every formal alternative in
the Boolean closure of `C` is in `C`. That condition is [trinh-haida-2015]'s (27), the sibling
study's `TrinhHaida2015.IsDomain`, and the implicatures are computed by innocent exclusion,
`Exhaustification.exhIE`, of which the paper's (9) is the simplification its footnote 7
describes. The paper's arguments then all have one shape: some formal alternative is the
negation, or the symmetric partner, of the alternative the inference needs, closure puts it into
every domain holding the other (`IsDomain.compl_mem`, `IsDomain.mem_of_isSymmetric`), and
neither can be innocently excluded, since negating both contradicts the assertion
(`Exhaustification.not_isInnocentlyExcludable_of_subset_union`); the study's
`exhIE_eq_self_of_isDomain` is that shape.

* Indirect implicatures, (12)–(15), after [romoli-2013]: *some* is derived from *not all* by
  (15), it is the negation of the needed *not any*, and exhaustification is vacuous on every
  domain (`exhIE_indirect_eq_self`); the Atomicity Constraint of [trinh-haida-2015] removes
  *some*, (22), and the implicature follows (`exhIE_indirect_atomicity`).
* Particularised implicatures, (28)–(31): with the conjunction of (18) split across sentences,
  the salient constituents yield only *smoke* and *not smoke*, and no domain licenses any
  inference (`exhIE_split_eq_self`); ignoring the salient *didn't smoke* derives the opposite
  one, footnote 16 (`exhIE_split_ignored`).
* Gradable adjectives, (32)–(40): Atomicity blocks *empty* but not *not empty*, so `{¬full,
  ¬empty}` is a domain (`isDomain_notFull_notEmpty`) on which exhaustification derives the
  unattested *the glass is empty* (`exhIE_notFull_notEmpty`); without Atomicity, *empty* joins
  every domain holding *not empty* and neither inference arises (`exhIE_notFull_eq_self`). The
  observed inference is available through the modifier alternatives of (37), *not half full*
  in place of *not empty* (`isDomain_notFull_notHalf`, `exhIE_notFull_notHalf`), but keeping
  both leaves exhaustification vacuous, footnote 20 (`exhIE_adjectiveAlts_eq_self`), and (38)
  shows the modifier route overgenerating for *safe*, *tall*, and *transparent*, adjectives of
  every scale structure in [kennedy-2007]'s sense.
* Lexicalised symmetric partners, (44)–(45), after [swanson-2010]: *required* and *optional*
  partition *permitted* and are lexical items of the same complexity, so both are formal
  alternatives, every domain holding one holds the other, and exhaustification is vacuous
  (`exhIE_permitted_eq_self`).

Section 4.1's problem of too few lexical alternatives, the Japanese deontic paradigm
(41)–(43) in which necessity is a negated verbal stem or an existential construction and yet
*yoi* 'allowed' implicates *not required*, and Section 5's assessment of the cost-and-
informativity account of [bergen-levy-goodman-2016], which covers (46), (48), and (50) and
fails (54)–(58), are recorded as rows and prose: the paper concludes that no account solves
the problem in full generality.

## Implementation notes

Sentences are propositions `Set W` over an arbitrary set of worlds, in the paper's schematic
notation (*¬all*, *some*, *run ∧ ¬smoke*); the relations the paper assumes among them (that
no glass is both half filled and empty) are hypotheses, and the worlds of the paper's
partitions (none, some but not all; empty, a bit filled, half filled) are witnesses. Which
sentences are formal alternatives is taken from the paper's sets (14), (19), (31), and (37),
not derived from a lexicon; that *some* is not derivable from *not all* under Atomicity is
`TrinhHaida2015.atoms_mem_source`, and (18) itself is `TrinhHaida2015.exhIE_run_smoke` on the
domain `TrinhHaida2015.run_smoke_isDomain`. The examples are the rows of `Examples.all`.

## TODO

* Section 5.1.2's argument that alternatives of equal cost and equal relative informativity
  leave the listener undecided is an invariance of the posterior under an involution
  of worlds and utterances that preserves meaning and cost and fixes the assertion; the paper's
  hypothetical of a *just some* no costlier than *all* and its cases (54)–(58) await that
  theorem.

## References

* [breheny-et-al-2018]
* [katzir-2007]
* [fox-katzir-2011]
* [trinh-haida-2015]
* [romoli-2013]
* [swanson-2010]
* [bergen-levy-goodman-2016]
* [fox-2007]
* [kennedy-2007]
-/

@[expose] public section

namespace BrehenyEtAl2018

open Alternatives Exhaustification Set TrinhHaida2015

variable {W : Type*}

/-! ### The shape of the arguments -/

theorem exhIE_eq_self_of_isDomain {F C : Set (Set W)} {φ p : Set W}
    (hF : F ⊆ {φ, p, pᶜ, φᶜ}) (hp : p ∈ F) (hpc : pᶜ ∈ F) (hC : IsDomain F φ C)
    (h₁ : (φ ∩ p).Nonempty) (h₂ : (φ ∩ pᶜ).Nonempty) : exhIE C φ = φ := by
  have hfin : C.Finite := (toFinite _).subset (hC.subset.trans hF)
  rw [exhIE_eq_self_iff C φ]
  intro a ha
  have hmem := hF (hC.subset ha.1)
  simp only [mem_insert_iff, mem_singleton_iff] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact absurd ha
      (not_isInnocentlyExcludable_of_phi_subset hfin (h₁.mono inter_subset_left) subset_rfl)
  · exact absurd ha (not_isInnocentlyExcludable_of_subset_union _ _ hfin ha.1
      (hC.compl_mem ha.1 hpc) (by simp) (by rwa [sdiff_compl]))
  · exact absurd ha (not_isInnocentlyExcludable_of_subset_union _ _ hfin ha.1
      (by simpa using hC.compl_mem ha.1 (by simpa using hp)) (by simp) (by rwa [sdiff_eq]))
  · exact disjoint_compl_right

/-! ### Indirect scalar implicatures, Section 2.2 -/

section Indirect

variable {all any : Set W}

/-- On the structural approach the formal alternatives of *John didn't do all of the homework*
are *not all*, *not any*, *all*, and *some*, the last by the derivation (15), as in (14). -/
def indirectAlts (all any : Set W) : Set (Set W) := {allᶜ, anyᶜ, all, any}

/-- On structural alternatives, exhaustifying *not all* is vacuous on every domain, so the
structural approach undergenerates (12). -/
theorem exhIE_indirect_eq_self {C : Set (Set W)} (hC : IsDomain (indirectAlts all any) allᶜ C)
    (h₀ : (allᶜ ∩ anyᶜ).Nonempty) (h₁ : (allᶜ ∩ any).Nonempty) : exhIE C allᶜ = allᶜ :=
  exhIE_eq_self_of_isDomain (p := anyᶜ) (by simp [indirectAlts, insert_subset_iff])
    (by simp [indirectAlts]) (by simp [indirectAlts]) hC h₀ (by simpa using h₁)

/-- Under the Atomicity Constraint, exhaustifying *not all* over *not any* and *all* derives *some*
(12b), as in (22). -/
theorem exhIE_indirect_atomicity (h₁ : (allᶜ ∩ any).Nonempty) :
    exhIE {allᶜ, anyᶜ, all} allᶜ = allᶜ ∩ any := by
  obtain ⟨v, hv, hv'⟩ := h₁
  have hIE : ∀ a ∈ ({anyᶜ, all} : Set (Set W)),
      IsInnocentlyExcludable {allᶜ, anyᶜ, all} allᶜ a := by
    rintro a (rfl | rfl)
    · refine .of_forall_subset_or_notMem (by simp) hv (notMem_compl_iff.2 hv') ?_
      rintro b (rfl | rfl | rfl)
      · exact Or.inl subset_rfl
      · exact Or.inr (notMem_compl_iff.2 hv')
      · exact Or.inr hv
    · refine .of_forall_subset_or_notMem (by simp) hv hv ?_
      rintro b (rfl | rfl | rfl)
      · exact Or.inl subset_rfl
      · exact Or.inr (notMem_compl_iff.2 hv')
      · exact Or.inr hv
  ext w
  rw [mem_exhIE_iff _ _, mem_inter_iff]
  refine ⟨fun ⟨hw, h⟩ ↦ ⟨hw, notMem_compl_iff.1 (h _ (hIE anyᶜ (by simp)))⟩,
    fun ⟨hw, hw'⟩ ↦ ⟨hw, fun a ha ↦ ?_⟩⟩
  rcases ha.1 with rfl | rfl | rfl
  · exact absurd ha (not_isInnocentlyExcludable_of_phi_subset (toFinite _) ⟨w, hw⟩ subset_rfl)
  · exact notMem_compl_iff.2 hw'
  · exact hw

end Indirect

/-! ### Particularised scalar implicatures, Section 3.2.1 -/

section Particularised

variable {run smoke : Set W}

/-- The alternatives of *John went for a run* from the constituents that (28) makes salient are
*run*, *smoke*, and *not smoke*, as in (31). -/
def splitAlts (run smoke : Set W) : Set (Set W) := {run, smoke, smokeᶜ}

/-- In the context (28) exhaustification is vacuous on every domain, with or without Atomicity. -/
theorem exhIE_split_eq_self {C : Set (Set W)} (hC : IsDomain (splitAlts run smoke) run C)
    (h₁ : (run ∩ smoke).Nonempty) (h₂ : (run ∩ smokeᶜ).Nonempty) : exhIE C run = run :=
  exhIE_eq_self_of_isDomain (p := smoke) (by simp [splitAlts, insert_subset_iff])
    (by simp [splitAlts]) (by simp [splitAlts]) hC h₁ h₂

/-- Ignoring the salient *didn't smoke* leaves `{run, smoke}`, and exhaustification derives that
John did not smoke, the opposite of the attested inference (footnote 16). -/
theorem exhIE_split_ignored (h₂ : (run ∩ smokeᶜ).Nonempty) :
    exhIE {run, smoke} run = run ∩ smokeᶜ := by
  rw [exhIE_pair_sdiff run (by rwa [sdiff_eq]), sdiff_eq]

end Particularised

/-! ### Gradable adjectives, Section 3.2.2 -/

section Gradable

variable {full empty half : Set W}

/-- Under Atomicity `{¬full, ¬empty}` is a domain for (32), by (39)–(40) with (37) and footnote 20.
-/
theorem isDomain_notFull_notEmpty {l m : W} (hl : l ∈ fullᶜ ∩ emptyᶜ ∩ halfᶜ)
    (hm : m ∈ fullᶜ ∩ emptyᶜ ∩ half) :
    IsDomain {fullᶜ, emptyᶜ, halfᶜ} fullᶜ {fullᶜ, emptyᶜ} := by
  refine isDomain_pair (by simp) (by simp) ?_
  rintro _ (rfl | rfl | rfl) hc
  · exact Or.inl rfl
  · exact Or.inr rfl
  · refine absurd hc (notMem_closure_of_separates ?_ hl.2 (notMem_compl_iff.2 hm.2))
    rintro _ (rfl | rfl) <;> simp [hl.1.1, hl.1.2, hm.1.1, hm.1.2]

/-- On that domain exhaustifying *not full* asserts *empty*, so the Atomicity Constraint backfires
(32b). -/
theorem exhIE_notFull_notEmpty (h : Disjoint full empty) (hne : empty.Nonempty) :
    exhIE {fullᶜ, emptyᶜ} fullᶜ = empty := by
  have hsd : fullᶜ \ emptyᶜ = empty := by rw [sdiff_compl, inter_eq_right.2 h.subset_compl_left]
  rw [exhIE_pair_sdiff fullᶜ (by rwa [hsd]), hsd]

/-- Without Atomicity, as in [fox-katzir-2011], *empty* is a formal alternative by (40) and
exhaustifying *not full* is vacuous, yielding neither (32b) nor (32a). -/
theorem exhIE_notFull_eq_self {C : Set (Set W)}
    (hC : IsDomain {fullᶜ, emptyᶜ, empty, full} fullᶜ C) (h₁ : (fullᶜ ∩ emptyᶜ).Nonempty)
    (h₂ : (fullᶜ ∩ empty).Nonempty) : exhIE C fullᶜ = fullᶜ :=
  exhIE_eq_self_of_isDomain (p := emptyᶜ) (by simp) (by simp) (by simp) hC h₁ (by simpa using h₂)

/-- `{¬full, ¬half full}` is also a domain, as in (37). -/
theorem isDomain_notFull_notHalf {e l : W} (he : e ∈ fullᶜ ∩ empty ∩ halfᶜ)
    (hl : l ∈ fullᶜ ∩ emptyᶜ ∩ halfᶜ) :
    IsDomain {fullᶜ, emptyᶜ, halfᶜ} fullᶜ {fullᶜ, halfᶜ} := by
  refine isDomain_pair (by simp) (by simp) ?_
  rintro _ (rfl | rfl | rfl) hc
  · exact Or.inl rfl
  · refine absurd hc (notMem_closure_of_separates ?_ hl.1.2 (notMem_compl_iff.2 he.1.2))
    rintro _ (rfl | rfl) <;> simp [he.1.1, he.2, hl.1.1, hl.2]
  · exact Or.inr rfl

theorem exhIE_notFull_notHalf (hm : (fullᶜ ∩ half).Nonempty) :
    exhIE {fullᶜ, halfᶜ} fullᶜ = fullᶜ ∩ half := by
  rw [exhIE_pair_sdiff fullᶜ (by rwa [sdiff_compl]), sdiff_compl]

/-- That inference entails (32a), *not empty*, when no glass is both half filled and empty. -/
theorem exhIE_notFull_notHalf_subset (h : Disjoint half empty) (hm : (fullᶜ ∩ half).Nonempty) :
    exhIE {fullᶜ, halfᶜ} fullᶜ ⊆ emptyᶜ :=
  (exhIE_notFull_notHalf hm).symm ▸ inter_subset_right.trans h.subset_compl_right

/-- Exhaustifying *not full* over *not empty* and *not half full* is vacuous (footnote 20). -/
theorem exhIE_adjectiveAlts_eq_self (h : Disjoint half empty) (he : (fullᶜ ∩ empty).Nonempty)
    (hm : (fullᶜ ∩ half).Nonempty) : exhIE {fullᶜ, emptyᶜ, halfᶜ} fullᶜ = fullᶜ := by
  have hcov : fullᶜ ⊆ emptyᶜ ∪ halfᶜ := by
    rw [← compl_inter, inter_comm, h.inter_eq, compl_empty]
    exact subset_univ _
  rw [exhIE_eq_self_iff _ _]
  intro a ha
  rcases ha.1 with rfl | rfl | rfl
  · exact absurd ha (not_isInnocentlyExcludable_of_phi_subset (toFinite _)
      (he.mono inter_subset_left) subset_rfl)
  · exact absurd ha (not_isInnocentlyExcludable_of_subset_union _ _ (toFinite _) ha.1 (by simp)
      hcov (by rwa [sdiff_compl]))
  · exact absurd ha (not_isInnocentlyExcludable_of_subset_union _ _ (toFinite _) ha.1 (by simp)
      (union_comm _ _ ▸ hcov) (by rwa [sdiff_compl]))

end Gradable

/-! ### Too many lexical alternatives, Section 4.2 -/

section Lexicalised

variable {permitted required optional : Set W}

/-- Since *required* and *optional* partition *permitted* in (44), exhaustifying *permitted* is
vacuous on every domain, so neither (44b) nor (44c) arises. -/
theorem exhIE_permitted_eq_self {C : Set (Set W)} (h : IsSymmetric permitted required optional)
    (hC : IsDomain {permitted, required, optional} permitted C) (h₁ : required.Nonempty)
    (h₂ : optional.Nonempty) : exhIE C permitted = permitted := by
  have hfin : C.Finite := (toFinite _).subset hC.subset
  rw [exhIE_eq_self_iff C permitted]
  intro a ha
  rcases hC.subset ha.1 with rfl | rfl | rfl
  · exact absurd ha
      (not_isInnocentlyExcludable_of_phi_subset hfin (h₁.mono h.subset_left) subset_rfl)
  · exact absurd ha (not_isInnocentlyExcludable_of_subset_union _ _ hfin ha.1
      (hC.mem_of_isSymmetric h ha.1 (by simp)) h.union.symm.subset (h.symm.sdiff_eq.symm ▸ h₁))
  · exact absurd ha (not_isInnocentlyExcludable_of_subset_union _ _ hfin ha.1
      (hC.mem_of_isSymmetric h.symm ha.1 (by simp)) h.symm.union.symm.subset
      (h.sdiff_eq.symm ▸ h₂))

end Lexicalised

end BrehenyEtAl2018
