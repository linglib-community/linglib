module

public import Studies.BarLevFox2020
public import Linglib.Semantics.Questions.Partition.Basic
public import Linglib.Semantics.Homogeneity.Plural
public import Linglib.Data.Statistics.KrizChemla2015

/-!
# Bar-Lev (2021): An Implicature Account of Homogeneity and Non-Maximality

Bar-Lev derives homogeneity as an implicature. A plural definite means existential
pluralization, that some atom of the plurality in a domain has the property, and its alternatives
replace the domain by its subsets, so that they are the disjunctions of the atomic predications
with no conjunction among them. Exhaustifying over all of them
[gives the universal reading](##exhIEII_eq_universal), while under negation
[exhaustification is vacuous](##exhIEII_compl_biUnion). Non-maximal readings come from
pruning: a set of alternatives may replace the whole set when exhaustifying over it only weakens
the universal reading, which holds exactly when it makes no alternative innocently excludable, and
the readings so derived are [the conjunctions of alternatives that are not themselves
alternatives, and the plain existential one](##readings_eq). They include "at least
`k`" for every `k` and lie among Križ and Spector's candidate meanings. The question the context
raises selects the strongest reading it determines; [every reading is selected by the question
whether it holds](##isReading_polar), and a world is gappy, true on the reading one
question selects and false on another's, [exactly where trivalent plural predication is
undefined](##gappy_iff_barePlural_eq_undefined).

## Implementation notes

The prejacent and the alternatives are the disjunction of the atomic predications over `x ∩ D`
and its closure under disjunction, the form the paper adopts once the domain is assumed to hold
every part of the plurality; subdomains that miss the plurality contribute no alternative. The
maximality clause of the final constraint on pruning is not formalized: `IsReading` is the
paper's summary of its effect, the strongest derivable reading the question determines. `Gappy`
ranges over all partitions and is context-free; that a context fixing the partition removes the
gap is carried by `reading_80` and `reading_81`.

## TODO

* The negative sentence is modelled only at the LF with negation over `∃-PL`; the LF with
  `∃-PL` over negation and the cover-restricted `∃-PL`, the paper's source of the marginal
  negative non-maximal readings and of Križ and Chemla's negative gaps, are not formalized.
* That the readings of *the kids laughed* for three kids number twelve, and the non-distributive
  extension.

## References

* [bar-lev-2021]
* [magri-2009]
* [magri-2014]
* [fox-2007]
* [fox-spector-2018]
* [crnic-chemla-fox-2015]
* [bar-lev-fox-2020]
* [malamud-2012]
* [kriz-2015]
* [kriz-2016]
* [kriz-chemla-2015]
* [kriz-spector-2021]
* [tieu-kriz-chemla-2019]
-/

@[expose] public section

namespace BarLev2021

open Exhaustification

variable {Atom W : Type*} {D x : Finset Atom} {P : Atom → W → Prop} [DecidableEq Atom]

/-! ### Existential pluralization and its subdomain alternatives

The existential pluralization `∃-PL_D` of `P` over `x` is the disjunction of the atoms of `x` in
the domain `D`. A subdomain `D' ⊆ D` leaves the atoms of `x ∩ D'`, so the subdomain alternatives
are the closure of the atoms under disjunction, `supClosure (atom P '' ↑(x ∩ D))`. -/

variable (P) in
/-- The proposition `a` satisfies `P`. -/
def atom (a : Atom) : Set W := {w | P a w}

instance [∀ a w, Decidable (P a w)] (w : W) (a : Atom) : Decidable (w ∈ atom P a) :=
  inferInstanceAs (Decidable (P a w))

theorem supClosure_subset_readings :
    supClosure (atom P '' ↑(x ∩ D)) ⊆ Homogeneity.readings (fun z ↦ {w | ∀ a ∈ z, P a w}) x := by
  intro q hq
  obtain ⟨S, ⟨a, ha⟩, hS, -⟩ := Set.mem_supClosure_image.1 hq
  rw [Homogeneity.readings_eq_latticeClosure ⟨a, (Finset.mem_inter.1 (hS ha)).1⟩]
  exact supClosure_min ((Set.image_mono (Finset.coe_subset.2 Finset.inter_subset_left)).trans
    subset_latticeClosure) isSublattice_latticeClosure.supClosed hq

variable (D x P) in
/-- Every atom laughs alone at some world, and all laugh together at some world. -/
structure Separating : Prop where
  /-- Each atom of `x ∩ D` satisfies `P` alone at some world. -/
  single : ∀ a ∈ x ∩ D, ∃ w, ∀ b ∈ x ∩ D, P b w ↔ b = a
  /-- All atoms of `x ∩ D` satisfy `P` together at some world. -/
  all : ∃ w, ∀ a ∈ x ∩ D, P a w

theorem Separating.of_forall_subset (h : ∀ T ⊆ x ∩ D, ∃ w, ∀ a ∈ x ∩ D, P a w ↔ a ∈ T) :
    Separating D x P where
  single a ha :=
    let ⟨w, hw⟩ := h {a} (Finset.singleton_subset_iff.2 ha)
    ⟨w, fun b hb ↦ (hw b hb).trans Finset.mem_singleton⟩
  all := let ⟨w, hw⟩ := h (x ∩ D) subset_rfl; ⟨w, fun a ha ↦ (hw a ha).2 ha⟩

theorem Separating.biUnion_nonempty (h : Separating D x P) (hne : (x ∩ D).Nonempty) :
    (⋃ b ∈ x ∩ D, atom P b).Nonempty :=
  let ⟨w, hw⟩ := h.all
  let ⟨a, ha⟩ := hne
  ⟨w, Set.mem_biUnion ha (hw a ha)⟩

theorem biUnion_mem_supClosure (hne : (x ∩ D).Nonempty) :
    (⋃ b ∈ x ∩ D, atom P b) ∈ supClosure (atom P '' ↑(x ∩ D)) :=
  Set.mem_supClosure_image.2 ⟨x ∩ D, hne, subset_rfl, rfl⟩

theorem subset_biUnion_of_mem_supClosure {q : Set W}
    (hq : q ∈ supClosure (atom P '' ↑(x ∩ D))) : q ⊆ ⋃ b ∈ x ∩ D, atom P b := by
  obtain ⟨S, -, hS, rfl⟩ := Set.mem_supClosure_image.1 hq
  exact Set.biUnion_subset_biUnion_left hS

/-! ### Homogeneity -/

/-- Exhaustifying `∃-PL` over its subdomain alternatives gives the universal reading, the
maximality implicature. -/
theorem exhIEII_eq_universal (h : Separating D x P) (hne : (x ∩ D).Nonempty) :
    exhIEII (supClosure (atom P '' ↑(x ∩ D))) (⋃ b ∈ x ∩ D, atom P b) =
      {w | ∀ a ∈ x, a ∈ D → P a w} := by
  rw [exhIEII_supClosure (p := atom P) h.single hne h.all]
  ext w; simp [atom, Finset.mem_inter]

/-- With negation over `∃-PL` every negated subdomain alternative is entailed by the negated
prejacent, so exhaustification over any of them is vacuous and no pruning yields a non-maximal
reading. -/
theorem exhIEII_compl_biUnion {C : Set (Set W)} (hC : C ⊆ compl '' supClosure (atom P '' ↑(x ∩ D)))
    (hsat : (⋃ b ∈ x ∩ D, atom P b)ᶜ.Nonempty) :
    exhIEII C (⋃ b ∈ x ∩ D, atom P b)ᶜ = (⋃ b ∈ x ∩ D, atom P b)ᶜ := by
  refine exhIEII_eq_self_of_forall_subset (fun q hq ↦ ?_) hsat
  obtain ⟨_, hq', rfl⟩ := hC hq
  exact Set.compl_subset_compl.2 (subset_biUnion_of_mem_supClosure hq')

-- (6a)
theorem exists_mem_biUnion_and_not (h : Separating D x P) {a : Atom} (ha : a ∈ x ∩ D)
    (h2 : 2 ≤ (x ∩ D).card) : ∃ w ∈ (⋃ b ∈ x ∩ D, atom P b), ¬ P a w := by
  obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (by omega : 1 < (x ∩ D).card) a
  obtain ⟨w, hw⟩ := h.single b hb
  exact ⟨w, Set.mem_biUnion hb ((hw b hb).2 rfl), fun hPa ↦ hba ((hw a ha).1 hPa).symm⟩

-- (6b)
theorem not_of_notMem_biUnion {w : W} (hw : w ∉ ⋃ b ∈ x ∩ D, atom P b) {a : Atom}
    (ha : a ∈ x ∩ D) : ¬ P a w :=
  fun hPa ↦ hw (Set.mem_biUnion ha hPa)

-- With a conjunctive alternative, as a floating quantifier would supply, no homogeneity.
theorem not_forall_of_mem_exhIEII_insert_iInter (h : Separating D x P) (h2 : 2 ≤ (x ∩ D).card)
    {w : W} (hw : w ∈ exhIEII (insert (⋂ a ∈ x ∩ D, atom P a) (supClosure (atom P '' ↑(x ∩ D))))
      (⋃ b ∈ x ∩ D, atom P b)) : ¬ ∀ a ∈ x ∩ D, P a w :=
  fun hall ↦ hw.2.1 _ (isInnocentlyExcludable_iInter_of_insert (p := atom P) h.single h2)
    (Set.mem_iInter₂.2 fun a ha ↦ hall a ha)

/-! ### Non-maximality by pruning -/

variable (D x P) in
/-- (63): the readings of *the kids laughed* are the results of exhaustifying over a set of
subdomain alternatives that only weakens the result of exhaustifying over all of them. -/
def readings : Set (Set W) :=
  (exhIEII · (⋃ b ∈ x ∩ D, atom P b)) '' {C | C ⊆ supClosure (atom P '' ↑(x ∩ D)) ∧
    exhIEII (supClosure (atom P '' ↑(x ∩ D))) (⋃ b ∈ x ∩ D, atom P b) ⊆
      exhIEII C (⋃ b ∈ x ∩ D, atom P b)}

-- A pruning is licit exactly when it leaves nothing innocently excludable, and then
-- exhaustification asserts every alternative it keeps.
theorem mem_readings_iff (h : Separating D x P) (hne : (x ∩ D).Nonempty) {r : Set W} :
    r ∈ readings D x P ↔ ∃ C ⊆ supClosure (atom P '' ↑(x ∩ D)),
      (∀ q, ¬ IsInnocentlyExcludable C (⋃ b ∈ x ∩ D, atom P b) q) ∧
        (⋃ b ∈ x ∩ D, atom P b) ∩ ⋂₀ C = r := by
  simp only [readings, Set.mem_image, Set.mem_ofPred_eq,
    exhIEII_supClosure (p := atom P) h.single hne h.all, and_assoc]
  refine exists_congr fun C ↦ and_congr_right fun hC ↦ ?_
  rw [iInter_subset_exhIEII_iff hC hne h.all]
  exact and_congr_right fun hIE ↦ by rw [exhIEII_eq_inter_sInter hC hne h.all hIE]

theorem subset_biUnion_of_mem_readings {r : Set W} (hr : r ∈ readings D x P) :
    r ⊆ ⋃ b ∈ x ∩ D, atom P b := by
  obtain ⟨C, -, rfl⟩ := hr
  exact fun _ hw ↦ hw.1

theorem forall_subset_of_mem_readings (h : Separating D x P) (hne : (x ∩ D).Nonempty)
    {r : Set W} (hr : r ∈ readings D x P) : {w | ∀ a ∈ x, a ∈ D → P a w} ⊆ r := by
  obtain ⟨C, ⟨-, hC⟩, rfl⟩ := hr
  rwa [exhIEII_eq_universal h hne] at hC

theorem biUnion_mem_readings (h : Separating D x P) (hne : (x ∩ D).Nonempty) :
    (⋃ b ∈ x ∩ D, atom P b) ∈ readings D x P :=
  ⟨{⋃ b ∈ x ∩ D, atom P b}, ⟨Set.singleton_subset_iff.2 (biUnion_mem_supClosure hne),
    (exhIEII_singleton (h.biUnion_nonempty hne)).symm ▸ fun _ hw ↦ hw.1⟩,
    exhIEII_singleton (h.biUnion_nonempty hne)⟩

theorem forall_mem_readings (h : Separating D x P) (hne : (x ∩ D).Nonempty) :
    {w | ∀ a ∈ x, a ∈ D → P a w} ∈ readings D x P :=
  ⟨_, ⟨subset_rfl, subset_rfl⟩, exhIEII_eq_universal h hne⟩

private theorem inter_sInter_mem_infClosure {S C : Set (Set W)} {φ : Set W} (hφ : φ ∈ S)
    (hfin : C.Finite) (hC : C ⊆ S) : φ ∩ ⋂₀ C ∈ infClosure S := by
  induction C, hfin using Set.Finite.induction_on with
  | empty => simpa using subset_infClosure hφ
  | @insert a C _ _ ih =>
    rw [Set.sInter_insert, Set.inter_left_comm]
    exact infClosed_infClosure (subset_infClosure (hC (Set.mem_insert _ _)))
      (ih ((Set.subset_insert _ _).trans hC))

theorem readings_subset_infClosure (h : Separating D x P) (hne : (x ∩ D).Nonempty) :
    readings D x P ⊆ infClosure (supClosure (atom P '' ↑(x ∩ D))) := by
  intro r hr
  obtain ⟨C, hC, -, rfl⟩ := (mem_readings_iff h hne).1 hr
  exact inter_sInter_mem_infClosure (biUnion_mem_supClosure hne)
    (((x ∩ D).finite_toSet.image _).supClosure.subset hC) hC

-- The readings are among Križ and Spector's candidate meanings.
theorem readings_subset_readings (h : Separating D x P) (hne : (x ∩ D).Nonempty) :
    readings D x P ⊆ Homogeneity.readings (fun z ↦ {w | ∀ a ∈ z, P a w}) x := by
  rw [Homogeneity.readings_eq_latticeClosure (hne.mono Finset.inter_subset_left)]
  exact (readings_subset_infClosure h hne).trans (infClosure_min (supClosure_min
    ((Set.image_mono (Finset.coe_subset.2 Finset.inter_subset_left)).trans subset_latticeClosure)
    isSublattice_latticeClosure.supClosed) isSublattice_latticeClosure.infClosed)

-- A conjunction of alternatives that is not itself a proper alternative is derived by keeping
-- every alternative it entails.
theorem infClosure_diff_subset_readings (h : Separating D x P) (hne : (x ∩ D).Nonempty) :
    infClosure (supClosure (atom P '' ↑(x ∩ D))) \
      (supClosure (atom P '' ↑(x ∩ D)) \ {⋃ b ∈ x ∩ D, atom P b}) ⊆ readings D x P := by
  rintro r ⟨⟨t, ht, hts, hrt⟩, hr⟩
  have hrC : (⋃ b ∈ x ∩ D, atom P b) ∩ ⋂₀ {q ∈ supClosure (atom P '' ↑(x ∩ D)) | r ⊆ q} = r := by
    refine Set.Subset.antisymm (fun w hw ↦ ?_)
      (Set.subset_inter ?_ (Set.subset_sInter fun _ hq ↦ hq.2))
    · rw [← hrt, Finset.inf'_eq_inf, Finset.inf_set_eq_iInter]
      exact Set.mem_iInter₂.2 fun q hq ↦ Set.mem_sInter.1 hw.2 q
        ⟨hts hq, hrt ▸ Finset.inf'_le id hq⟩
    · obtain ⟨q, hq⟩ := ht
      exact (hrt ▸ Finset.inf'_le id hq).trans (subset_biUnion_of_mem_supClosure (hts hq))
  refine (mem_readings_iff h hne).2 ⟨_, fun _ hq ↦ hq.1, fun q hIE ↦ ?_, hrC⟩
  have hfin := ((x ∩ D).finite_toSet.image (atom P)).supClosure.subset
    (fun _ hq ↦ hq.1 : {q ∈ supClosure (atom P '' ↑(x ∩ D)) | r ⊆ q} ⊆ _)
  have hmw := (isInnocentlyExcludable_iff_exhMW_subset_compl _ _ q hIE.1).1 hIE
  obtain ⟨hqS, hrq⟩ := hIE.1
  obtain ⟨s, -, hsx, rfl⟩ := Set.mem_supClosure_image.1 hqS
  have hmin : ∀ q' ∈ {q ∈ supClosure (atom P '' ↑(x ∩ D)) | r ⊆ q},
      ⋃ i ∈ s, atom P i ⊆ q' := by
    intro q' hq'
    obtain ⟨s', -, hs'x, rfl⟩ := Set.mem_supClosure_image.1 hq'.1
    refine Set.biUnion_subset_biUnion_left (s := (s : Set Atom)) (s' := (s' : Set Atom)) fun i hi ↦
      by_contra fun hi' ↦ ?_
    obtain ⟨wi, hwi⟩ := h.single i (hsx hi)
    obtain ⟨u, hu, hle⟩ := exists_mem_exhMW_le hfin
      (Set.mem_biUnion (hsx hi) ((hwi i (hsx hi)).2 rfl))
    obtain ⟨j, hj, huj⟩ := Set.mem_iUnion₂.1 hu.1
    rcases (hle ⟨⟨supClosed_supClosure hq'.1 (subset_supClosure (Set.mem_image_of_mem _ hj)),
      hq'.2.trans Set.subset_union_left⟩, Or.inr huj⟩).2 with hw | hw
    · obtain ⟨k, hk, hwk⟩ := Set.mem_iUnion₂.1 hw
      exact hi' ((hwi k (hs'x hk)).1 hwk ▸ hk)
    · exact hmw hu (Set.mem_biUnion hi ((hwi j hj).1 hw ▸ huj))
  have hrs : r = ⋃ i ∈ s, atom P i :=
    hrC ▸ Set.Subset.antisymm (Set.inter_subset_right.trans (Set.sInter_subset_of_mem ⟨hqS, hrq⟩))
      (Set.subset_inter (subset_biUnion_of_mem_supClosure hqS) (Set.subset_sInter hmin))
  have hrφ : r = ⋃ b ∈ x ∩ D, atom P b := by_contra fun hne' ↦ hr ⟨hrs ▸ hqS, hne'⟩
  obtain ⟨u, hu⟩ := exhMW_nonempty hfin (h.biUnion_nonempty hne)
  exact hmw hu (by rw [← hrs, hrφ]; exact hu.1)

-- When the atomic predications are independent, no proper alternative is a reading.
theorem eq_biUnion_of_mem_readings_of_mem_supClosure
    (hind : ∀ T ⊆ x ∩ D, ∃ w, ∀ a ∈ x ∩ D, P a w ↔ a ∈ T) (hne : (x ∩ D).Nonempty) {r : Set W}
    (hr : r ∈ readings D x P) (hrS : r ∈ supClosure (atom P '' ↑(x ∩ D))) :
    r = ⋃ b ∈ x ∩ D, atom P b := by
  obtain ⟨C, hC, hIE, rfl⟩ := (mem_readings_iff (.of_forall_subset hind) hne).1 hr
  obtain ⟨s, -, hsx, hs⟩ := Set.mem_supClosure_image.1 hrS
  by_contra hneq
  obtain ⟨j, hj, hjs⟩ : ∃ j ∈ x ∩ D, j ∉ s := by
    by_contra hcon
    push Not at hcon
    exact hneq (Set.Subset.antisymm Set.inter_subset_left
      (hs ▸ Set.biUnion_subset_biUnion_left (s := ((x ∩ D : Finset Atom) : Set Atom))
        (s' := (s : Set Atom)) fun j hj ↦ hcon j hj))
  obtain ⟨v, hv⟩ := hind ((x ∩ D).filter (· ∉ s)) (Finset.filter_subset _ _)
  have hvφ : v ∈ ⋃ b ∈ x ∩ D, atom P b :=
    Set.mem_biUnion hj ((hv j hj).2 (Finset.mem_filter.2 ⟨hj, hjs⟩))
  have hvs : v ∉ ⋃ i ∈ s, atom P i := fun hmem ↦
    let ⟨i, hi, hvi⟩ := Set.mem_iUnion₂.1 hmem
    (Finset.mem_filter.1 ((hv i (hsx hi)).1 hvi)).2 hi
  obtain ⟨q₀, hq₀, hvq₀⟩ : ∃ q₀ ∈ C, v ∉ q₀ := by
    by_contra hcon
    push Not at hcon
    exact hvs (by rw [hs]; exact ⟨hvφ, Set.mem_sInter.2 hcon⟩)
  obtain ⟨s₀, -, hs₀x, rfl⟩ := Set.mem_supClosure_image.1 (hC hq₀)
  have hs₀ : ⋃ k ∈ s₀, atom P k = (⋃ b ∈ x ∩ D, atom P b) ∩ ⋂₀ C :=
    Set.Subset.antisymm (hs ▸ Set.biUnion_subset_biUnion_left (s := (s₀ : Set Atom))
      (s' := (s : Set Atom)) fun k hk ↦ by_contra fun hks ↦ hvq₀ (Set.mem_biUnion hk
        ((hv k (hs₀x hk)).2 (Finset.mem_filter.2 ⟨hs₀x hk, hks⟩))))
      (Set.inter_subset_right.trans (Set.sInter_subset_of_mem hq₀))
  have hnIE := hIE (⋃ k ∈ s₀, atom P k)
  rw [isInnocentlyExcludable_iff_exhMW_subset_compl C _ _ hq₀, Set.not_subset] at hnIE
  obtain ⟨u, hu, huq⟩ := hnIE
  exact hvq₀ (hu.2 hvφ (fun q hq ↦ ⟨hq.1, Set.mem_sInter.1
    (hs₀ ▸ not_not.1 huq : u ∈ (⋃ b ∈ x ∩ D, atom P b) ∩ ⋂₀ C).2 q hq.1⟩) ⟨hq₀, not_not.1 huq⟩).2

/-- (64): when the atomic predications are independent, the readings are the conjunctions of
subdomain alternatives, barring the alternatives themselves other than the prejacent. -/
theorem readings_eq (hind : ∀ T ⊆ x ∩ D, ∃ w, ∀ a ∈ x ∩ D, P a w ↔ a ∈ T)
    (hne : (x ∩ D).Nonempty) :
    readings D x P = infClosure (supClosure (atom P '' ↑(x ∩ D))) \
      (supClosure (atom P '' ↑(x ∩ D)) \ {⋃ b ∈ x ∩ D, atom P b}) :=
  Set.Subset.antisymm (fun _ hr ↦ ⟨readings_subset_infClosure (.of_forall_subset hind) hne hr,
    fun hrS ↦ hrS.2 (eq_biUnion_of_mem_readings_of_mem_supClosure hind hne hr hrS.1)⟩)
    (infClosure_diff_subset_readings (.of_forall_subset hind) hne)

/-! ### Relevance -/

variable (D x P) in
/-- (69): the reading a partition selects is the strongest reading it determines. -/
def IsReading (Q : Setoid W) (q : Set W) : Prop :=
  IsLeast {r ∈ readings D x P | Q.Determines r} q

theorem IsReading.unique {Q : Setoid W} {q r : Set W} (hq : IsReading D x P Q q)
    (hr : IsReading D x P Q r) : q = r :=
  IsLeast.unique hq hr

-- A reading that is the cell of a world where every atom satisfies `P` is the one selected.
theorem isReading_of_cell_eq (h : Separating D x P) (hne : (x ∩ D).Nonempty) {Q : Setoid W}
    {q : Set W} (hq : q ∈ readings D x P) {w : W} (hw : ∀ a ∈ x, a ∈ D → P a w)
    (hQ : Q.cell w = q) : IsReading D x P Q q := by
  subst hQ
  exact ⟨⟨hq, Setoid.determines_cell w⟩, fun _ hr ↦
    hr.2.cell_subset (forall_subset_of_mem_readings h hne hr.1 hw)⟩

/-- Every reading is the one selected by the polar question whether it holds. -/
theorem isReading_polar (h : Separating D x P) (hne : (x ∩ D).Nonempty) {q : Set W}
    (hq : q ∈ readings D x P) : IsReading D x P (Setoid.polar q) q := by
  obtain ⟨w, hw⟩ := h.all
  have hw' : ∀ a ∈ x, a ∈ D → P a w := fun a ha haD ↦ hw a (Finset.mem_inter.2 ⟨ha, haD⟩)
  exact isReading_of_cell_eq h hne hq hw'
    (Setoid.polar_cell_of_mem (forall_subset_of_mem_readings h hne hq hw'))

/-! ### Gappiness -/

variable (D x P) in
/-- A world is gappy when it is true on the reading some partition selects and false on another's.
-/
def Gappy (w : W) : Prop :=
  (∃ (Q : Setoid W) (q : Set W), IsReading D x P Q q ∧ w ∈ q) ∧
    ∃ (Q : Setoid W) (q : Set W), IsReading D x P Q q ∧ w ∉ q

theorem gappy_iff (h : Separating D x P) (hne : (x ∩ D).Nonempty) (w : W) :
    Gappy D x P w ↔ (∃ a ∈ x ∩ D, P a w) ∧ ∃ a ∈ x ∩ D, ¬ P a w := by
  constructor
  · rintro ⟨⟨_, q, hq, hwq⟩, ⟨_, q', hq', hwq'⟩⟩
    obtain ⟨a, ha, hPa⟩ := Set.mem_iUnion₂.1 (subset_biUnion_of_mem_readings hq.1.1 hwq)
    refine ⟨⟨a, ha, hPa⟩, by_contra fun hcon ↦ ?_⟩
    push Not at hcon
    exact hwq' (forall_subset_of_mem_readings h hne hq'.1.1
      fun a ha haD ↦ hcon a (Finset.mem_inter.2 ⟨ha, haD⟩))
  · rintro ⟨⟨a, ha, hPa⟩, ⟨b, hb, hPb⟩⟩
    exact ⟨⟨_, _, isReading_polar h hne (biUnion_mem_readings h hne), Set.mem_biUnion ha hPa⟩,
      ⟨_, _, isReading_polar h hne (forall_mem_readings h hne),
        fun hall ↦ hPb (hall b (Finset.mem_inter.1 hb).1 (Finset.mem_inter.1 hb).2)⟩⟩

section Decidable

variable [∀ a w, Decidable (P a w)]

/-- A plain positive definite plural is gappy exactly where [kriz-2016]'s trivalent plural
predication is undefined, where the accounts agree. -/
theorem gappy_iff_barePlural_eq_undefined (h : Separating D x P) (hne : (x ∩ D).Nonempty)
    (w : W) : Gappy D x P w ↔ Homogeneity.barePlural P (x ∩ D) w = .undefined := by
  rw [gappy_iff h hne, Homogeneity.barePlural, Trivalent.supervaluation_eq_undefined_iff]

-- Trivalent plural predication is true where the exhaustified sentence is, and false where
-- the unexhaustified one is.
theorem barePlural_eq_true_iff_mem_exhIEII (h : Separating D x P) (hne : (x ∩ D).Nonempty)
    (w : W) : Homogeneity.barePlural P (x ∩ D) w = .true ↔
      w ∈ exhIEII (supClosure (atom P '' ↑(x ∩ D))) (⋃ b ∈ x ∩ D, atom P b) := by
  rw [exhIEII_supClosure (p := atom P) h.single hne h.all, Homogeneity.barePlural,
    Trivalent.supervaluation_eq_true_iff, Set.mem_iInter₂]
  rfl

theorem barePlural_eq_false_iff_notMem_biUnion (hne : (x ∩ D).Nonempty) (w : W) :
    Homogeneity.barePlural P (x ∩ D) w = .false ↔ w ∉ ⋃ b ∈ x ∩ D, atom P b := by
  rw [Homogeneity.barePlural, Trivalent.supervaluation_eq_false_iff, Set.mem_iUnion₂]
  simp [hne, atom]

-- At a gappy world the trivalent negation is still undefined, while the negative sentence with
-- negation over `∃-PL`, exhaustified over any of its alternatives, is plainly false, where the
-- accounts part.
theorem compl_barePlural_eq_undefined_and_notMem_exhIEII_compl (h : Separating D x P)
    (hne : (x ∩ D).Nonempty) {w : W} (hw : Gappy D x P w) (C : Set (Set W)) :
    (Homogeneity.barePlural P (x ∩ D) w)ᶜ = .undefined ∧
      w ∉ exhIEII C (⋃ b ∈ x ∩ D, atom P b)ᶜ := by
  refine ⟨Trivalent.compl_eq_undefined_iff.2
    ((gappy_iff_barePlural_eq_undefined h hne w).1 hw), ?_⟩
  obtain ⟨a, ha, hPa⟩ := ((gappy_iff h hne w).1 hw).1
  exact fun hmem ↦ hmem.1 (Set.mem_biUnion ha hPa)

/-! ### Threshold readings -/

variable (D x P) in
/-- How many atoms of the plurality satisfy `P` at `w`. -/
def count (w : W) : ℕ := ((x ∩ D).filter (P · w)).card

variable (D x P) in
/-- "At least `k` of the kids laughed". -/
def atLeast (k : ℕ) : Set W := {w | k ≤ count D x P w}

@[simp] theorem mem_atLeast {k : ℕ} {w : W} : w ∈ atLeast D x P k ↔ k ≤ count D x P w := Iff.rfl

theorem count_le_card (w : W) : count D x P w ≤ (x ∩ D).card := Finset.card_filter_le _ _

theorem atLeast_antitone : Antitone (atLeast D x P) :=
  fun _ _ hkl _ hw ↦ hkl.trans hw

theorem atLeast_card : atLeast D x P (x ∩ D).card = {w | ∀ a ∈ x, a ∈ D → P a w} := by
  ext w
  simp only [mem_atLeast, count, Set.mem_ofPred_eq]
  refine ⟨fun h a ha haD ↦ ?_, fun h ↦ ?_⟩
  · have := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) h
    rw [Finset.filter_eq_self] at this
    exact this a (Finset.mem_inter.2 ⟨ha, haD⟩)
  · rw [Finset.filter_true_of_mem fun a ha ↦
      h a (Finset.mem_inter.1 ha).1 (Finset.mem_inter.1 ha).2]

theorem gappy_iff_count (h : Separating D x P) (hne : (x ∩ D).Nonempty) (w : W) :
    Gappy D x P w ↔ 0 < count D x P w ∧ count D x P w < (x ∩ D).card := by
  rw [gappy_iff h hne, count, Finset.card_pos, Finset.filter_nonempty_iff, ← Finset.filter_ssubset]
  exact and_congr_right fun _ ↦ ⟨Finset.card_lt_card, fun hlt ↦ Finset.ssubset_iff_subset_ne.2
    ⟨Finset.filter_subset _ _, ne_of_apply_ne _ hlt.ne⟩⟩

-- (62): exhaustifying over the size-`m` alternatives yields "at least `n + 1 - m` of the kids
-- laughed".
theorem exhIEII_pruned_eq_atLeast (h : Separating D x P) {m : ℕ} (hm : 0 < m)
    (hmn : m ≤ (x ∩ D).card) :
    exhIEII (subDisjsOfCard (x ∩ D) (atom P) m) (⋃ b ∈ x ∩ D, atom P b) =
      atLeast D x P ((x ∩ D).card + 1 - m) := by
  rw [exhIEII_subDisjsOfCard (p := atom P) h.single h.all hm hmn]
  ext w
  change (x ∩ D).card < m + count D x P w ↔ (x ∩ D).card + 1 - m ≤ count D x P w
  omega

theorem atLeast_mem_readings (h : Separating D x P) {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ (x ∩ D).card) : atLeast D x P k ∈ readings D x P := by
  have hne : (x ∩ D).Nonempty := Finset.card_pos.1 (hk.trans_le hkn)
  have hm : (x ∩ D).card + 1 - k ≤ (x ∩ D).card := by omega
  have hC := subDisjsOfCard_subset_supClosure (p := atom P) hne
    (by omega : 0 < (x ∩ D).card + 1 - k)
  have he := exhIEII_pruned_eq_atLeast h (by omega) hm
  rw [show (x ∩ D).card + 1 - ((x ∩ D).card + 1 - k) = k by omega] at he
  refine ⟨_, ⟨hC, ?_⟩, he⟩
  rw [he, exhIEII_eq_universal h hne, ← atLeast_card]
  exact atLeast_antitone hkn

theorem isReading_polar_atLeast (h : Separating D x P) {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ (x ∩ D).card) :
    IsReading D x P (Setoid.polar (atLeast D x P k)) (atLeast D x P k) :=
  isReading_polar h (Finset.card_pos.1 (hk.trans_le hkn)) (atLeast_mem_readings h hk hkn)

end Decidable

/-! ### The model whose worlds record who laughed -/

section Model

/-- In the model whose worlds are the sets of atoms satisfying the predicate, `a` satisfies it at
the world `w` when `a ∈ w`. -/
abbrev holds (a : Atom) (w : Finset Atom) : Prop := a ∈ w

variable (D x)

theorem forall_subset_exists_holds_iff :
    ∀ T ⊆ x ∩ D, ∃ w, ∀ a ∈ x ∩ D, holds a w ↔ a ∈ T :=
  fun T _ ↦ ⟨T, fun _ _ ↦ Iff.rfl⟩

theorem separating_holds : Separating D x holds :=
  .of_forall_subset (forall_subset_exists_holds_iff D x)

theorem count_holds (w : Finset Atom) : count D x holds w = (x ∩ D ∩ w).card := by
  rw [count, Finset.filter_mem_eq_inter]

theorem isReading_polar_atLeast_holds {k : ℕ} (hk : 0 < k) (hkn : k ≤ (x ∩ D).card) :
    IsReading D x holds (Setoid.polar (atLeast D x holds k)) (atLeast D x holds k) :=
  isReading_polar_atLeast (separating_holds D x) hk hkn

end Model

/-! ### The paper's examples -/

/-- Kelly, Jane and Bill. -/
inductive Kid | kelly | jane | bill
  deriving DecidableEq, Fintype

/-- The kids. -/
def kids : Finset Kid := Finset.univ

/-- Kelly and Jane, the kids of (41). -/
def pair : Finset Kid := {.kelly, .jane}

/-- *Kelly laughed*. -/
abbrev kellyLaughed : Set (Finset Kid) := atom holds .kelly

/-- *Jane laughed*. -/
abbrev janeLaughed : Set (Finset Kid) := atom holds .jane

-- (41a): *Kelly or Jane laughed*, whose alternatives include the conjunction, is strengthened
-- to "not both".
theorem disjunction_not_both :
    exhIEII {kellyLaughed ∪ janeLaughed, kellyLaughed, janeLaughed, kellyLaughed ∩ janeLaughed}
        (kellyLaughed ∪ janeLaughed) =
      (kellyLaughed ∪ janeLaughed) \ (kellyLaughed ∩ janeLaughed) :=
  BarLevFox2020.exhIEII_pair_inter le_rfl
    ⟨{.kelly}, ⟨Or.inl (Finset.mem_singleton_self _), Finset.mem_singleton_self _⟩, by decide⟩
    ⟨{.jane}, ⟨Or.inr (Finset.mem_singleton_self _), Finset.mem_singleton_self _⟩, by decide⟩

-- (41b): *The kids laughed*, whose alternatives are the subdomain alternatives alone, is
-- strengthened to "both".
theorem plural_both :
    exhIEII (supClosure (atom holds '' pair)) (⋃ b ∈ pair, atom holds b) = {w | pair ⊆ w} := by
  have := exhIEII_eq_universal (separating_holds pair pair) (by decide)
  rw [Finset.inter_self] at this
  exact this.trans (Set.ext fun w ↦ ⟨fun h _ ha ↦ h _ ha ha, fun h a ha _ ↦ h ha⟩)

-- Given the partition (66), *the kids laughed* means that at least two of the kids laughed.
theorem reading_66 :
    IsReading kids kids holds (Setoid.polar (atLeast kids kids holds 2))
      (atLeast kids kids holds 2) :=
  isReading_polar_atLeast_holds kids kids (by decide) (by decide)

/-- The ten books on the reading list. -/
abbrev Book := Fin 10

/-- The books. -/
def books : Finset Book := Finset.univ

-- In the context of (80), *Mary read the books* means that she read at least five of them.
theorem reading_80 :
    IsReading books books holds (Setoid.polar (atLeast books books holds 5))
      (atLeast books books holds 5) :=
  isReading_polar_atLeast_holds books books (by decide) (by decide)

-- In the context of (81), where only reading all ten passes, *Mary read the books* has its
-- maximal reading.
theorem reading_81 :
    IsReading books books holds (Setoid.polar (atLeast books books holds 10))
      (atLeast books books holds 10) :=
  isReading_polar_atLeast_holds books books (by decide) (by decide)

/-! ### Križ and Chemla's unembedded displays

An unembedded display of [kriz-chemla-2015] shows nine symbols, some number of which have the
target color, so its worlds are the sets of target-colored symbols. -/

section KrizChemla

open KrizChemla2015 (items gapTests)

/-- The symbols of a display. -/
abbrev Symbol := Fin 9

private theorem krizChemla_unembedded : ∀ i ∈ items, i.embedding = .unembedded →
    ∀ n ∈ i.cells, (0 < n ∧ n < 9 ↔ i.condition = .gap) := by
  decide

-- On Križ and Chemla's unembedded displays the positive sentence is gappy exactly at the GAP
-- displays, where every experiment found a gap (Table 2).
theorem gappy_iff_krizChemla_gap :
    (∀ i ∈ items, i.embedding = .unembedded → ∀ w : Finset Symbol, i.cells = [w.card] →
      (Gappy Finset.univ Finset.univ holds w ↔ i.condition = .gap)) ∧
    ∀ t ∈ gapTests, t.embedding = .unembedded → t.found = .yes := by
  refine ⟨fun i hi he w hw ↦ ?_, by decide⟩
  have h := krizChemla_unembedded i hi he w.card (by simp [hw])
  rw [gappy_iff_count (separating_holds _ _) ⟨0, by simp⟩, count_holds]
  simpa using h

-- Under negation every GAP display is false whatever is pruned, though Table 2 found a gap
-- there in Experiments A1 and B1.
theorem krizChemla_negation_residue :
    (∀ i ∈ items, i.embedding = .unembedded → i.condition = .gap → ∀ w : Finset Symbol,
      i.cells = [w.card] → ∀ C, w ∉ exhIEII C (⋃ b ∈ Finset.univ, atom holds b)ᶜ) ∧
    ∀ t ∈ gapTests, t.embedding = .negation → t.found = .yes := by
  refine ⟨fun i hi he hc w hw C ↦ ?_, by decide⟩
  have hg := (gappy_iff_krizChemla_gap.1 i hi he w hw).2 hc
  simpa only [Finset.inter_self] using (compl_barePlural_eq_undefined_and_notMem_exhIEII_compl
    (separating_holds _ _) ⟨0, by simp⟩ hg C).2

end KrizChemla

end BarLev2021
