module

public import Studies.BarLev2021
public import Linglib.Semantics.Exhaustification.Presuppositional
public import Linglib.Semantics.Presupposition.Context
public import Linglib.Data.Examples.GuerriniWehbe2025

/-!
# Guerrini and Wehbe (2025): Homogeneity as presuppositional exhaustification

Guerrini and Wehbe derive homogeneity by presuppositional exhaustification. A plural definite
contributes Bar-Lev's existential pluralization, and the operator `pex` of Del Pinal, Bassi and
Sauerland asserts it while presupposing that its subdomain alternatives are all true or all false.
Accommodating the presupposition yields the universal reading as long as no alternative for a
single atom is pruned (`pexPlural_eq_one_iff`), and pruning those yields non-maximal readings, all
but `m - 1` of the atoms for the alternatives over `m` of them
(`pexPlural_subDisjsOfCard_eq_one_iff`), at least two of three students for the pairs of (21)
(`pexPlural_pairs_eq_one_iff`). Under negation the presupposition projects and the negated
existential already entails it, so pruning has no effect (`pexPlural_eq_neg_one_iff`).
Non-maximality under negation needs local accommodation below negation and a second `pex` over the
negated universal, which is the positive case for the negated predicate
(`localAccommodation_nonMaximal`).

Homogeneity is thus a presupposition, which a constraint on accommodation detects: a sentence is
felicitous only if its assertion is informative once its presupposition is accommodated
(`Presupposition.PostAccommodationInformative`, the paper's (8)). *She read the books* is
infelicitous where Mary is known to have read some of them, *the candidates lost* where at most one
candidate can win, and their negations where the universal is known to fail, while the quantified
counterparts are fine (`judgments_10`, `judgments_13`).

## Implementation notes

A plurality is the domain of Bar-Lev's existential pluralization, the disjunction of its atoms,
and the alternatives are his subdomain alternatives, the sub-disjunctions, all of which are
innocently includable (`Exhaustification.II_eq_self_of_subset_supClosure`).
The common ground is a set of worlds and accommodation intersects it with the presupposition.
The higher `pex` of (24) and (27) does not change the truth conditions of a negated plural and
is not modelled.

## TODO

* The comparison with Križ and Chemla's gap judgments (§5.1) and with Paillé (§5.2).
* Projection from non-monotonic quantifiers, free choice and the modal cases of §6.

## References

* [guerrini-wehbe-2025]
* [bar-lev-2021]
* [delpinal-bassi-sauerland-2024]
* [bar-lev-fox-2020]
* [crnic-chemla-fox-2015]
-/

@[expose] public section

namespace GuerriniWehbe2025

open Exhaustification Homogeneity BarLev2021 Presupposition

/-! ### Presuppositional exhaustification of plural predication (§4) -/

section Plural

variable {Atom W : Type*} [DecidableEq Atom] {D x : Finset Atom} {P : Atom → W → Prop}
  {R : Set (Set W)} {w : W}

variable (D x P) in
/-- A plural predication under `pex`, (19), asserts Bar-Lev's existential pluralization and
presupposes that its relevant subdomain alternatives are homogeneous. -/
noncomputable abbrev pexPlural (R : Set (Set W)) : W → SignType :=
  pexIEII (supClosure (atom P '' ↑(x ∩ D))) (⋃ b ∈ x ∩ D, atom P b) R

/-- The presupposition (19b) is that the relevant subdomain alternatives are all true or all
false. -/
theorem pexPlural_ne_zero_iff (h : Separating D x P) (hne : (x ∩ D).Nonempty) :
    pexPlural D x P R w ≠ 0 ↔
      Homogeneous (supClosure (atom P '' ↑(x ∩ D)) \ {(⋃ b ∈ x ∩ D, atom P b)} ∩ R) w := by
  rw [pexIEII_ne_zero_iff,
    II_eq_self_of_subset_supClosure (p := atom P) le_rfl hsplit_supClosure h.single hne h.all]
  exact and_iff_right fun ψ hψ ↦
    absurd hψ (not_isInnocentlyExcludable_of_subset_supClosure le_rfl hsplit_supClosure h.single ψ)

/-- In (20), after accommodation, a plural predication is universal as long as no alternative for
a single atom is pruned. -/
theorem pexPlural_eq_one_iff (h : Separating D x P) (hcard : 1 < (x ∩ D).card)
    (hR : ∀ a ∈ x ∩ D, atom P a ∈ R) :
    pexPlural D x P R w = 1 ↔ ∀ a ∈ x, a ∈ D → P a w := by
  have hne : (x ∩ D).Nonempty := Finset.card_pos.1 (by omega)
  have hsing : ∀ a ∈ x ∩ D,
      atom P a ∈ supClosure (atom P '' ↑(x ∩ D)) \ {⋃ b ∈ x ∩ D, atom P b} ∩ R := by
    intro a ha
    refine ⟨⟨subset_supClosure (Set.mem_image_of_mem _ ha), fun heq ↦ ?_⟩, hR a ha⟩
    obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne hcard a
    obtain ⟨wb, hwb⟩ := h.single b hb
    have hin : wb ∈ ⋃ b ∈ x ∩ D, atom P b := Set.mem_biUnion hb ((hwb b hb).2 rfl)
    rw [← Set.mem_singleton_iff.1 heq] at hin
    exact hba ((hwb a ha).1 hin).symm
  rw [pexIEII_eq_one_iff, pexPlural_ne_zero_iff h hne]
  constructor
  · rintro ⟨hhom | hhom, hw⟩
    · exact fun b hbx hbD ↦ hhom _ (hsing b (Finset.mem_inter.2 ⟨hbx, hbD⟩))
    · obtain ⟨a, ha, hPa⟩ := Set.mem_iUnion₂.1 hw
      exact absurd hPa (hhom _ (hsing a ha))
  · intro hall
    have hall' (a) (ha : a ∈ x ∩ D) : P a w :=
      hall a (Finset.mem_inter.1 ha).1 (Finset.mem_inter.1 ha).2
    refine ⟨.inl ?_, ?_⟩
    · rintro _ ⟨⟨hq, -⟩, -⟩
      obtain ⟨S, ⟨c, hc⟩, hS, rfl⟩ := Set.mem_supClosure_image.1 hq
      exact Set.mem_biUnion hc (hall' c (hS hc))
    · obtain ⟨a, ha⟩ := hne
      exact Set.mem_biUnion ha (hall' a ha)

/-- In (25) and (28), a negated plural predication is true exactly where no atom satisfies the
predicate, however the alternatives are pruned. -/
theorem pexPlural_eq_neg_one_iff : pexPlural D x P R w = -1 ↔ ∀ a ∈ x, a ∈ D → ¬ P a w := by
  have hout (hnone : ∀ a ∈ x, a ∈ D → ¬ P a w) :
      ∀ q ∈ supClosure (atom P '' ↑(x ∩ D)), w ∉ q := by
    intro q hq hw
    obtain ⟨S, -, hS, rfl⟩ := Set.mem_supClosure_image.1 hq
    obtain ⟨c, hc, hPc⟩ := Set.mem_iUnion₂.1 hw
    exact hnone c (Finset.mem_inter.1 (hS hc)).1 (Finset.mem_inter.1 (hS hc)).2 hPc
  rw [pexIEII_eq_neg_one_iff, pexIEII_ne_zero_iff]
  refine ⟨fun ⟨_, hna⟩ a hax haD hPa ↦ hna (Set.mem_biUnion (Finset.mem_inter.2 ⟨hax, haD⟩) hPa),
    fun hnone ↦ ⟨⟨fun ψ hψ _ ↦ hout hnone ψ hψ.1, .inr fun α hα ↦ hout hnone α hα.1.1.1⟩,
      fun hw ↦ ?_⟩⟩
  obtain ⟨a, ha, hPa⟩ := Set.mem_iUnion₂.1 hw
  exact hnone a (Finset.mem_inter.1 ha).1 (Finset.mem_inter.1 ha).2 hPa

private theorem biUnion_ne_of_card_lt (h : Separating D x P) {T : Finset Atom} (hT : T ⊆ x ∩ D)
    (hlt : T.card < (x ∩ D).card) : ⋃ i ∈ T, atom P i ≠ ⋃ i ∈ x ∩ D, atom P i := by
  intro heq
  obtain ⟨b, hb, hbT⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨wb, hwb⟩ := h.single b hb
  have hin : wb ∈ ⋃ i ∈ x ∩ D, atom P i := Set.mem_biUnion hb ((hwb b hb).2 rfl)
  rw [← heq] at hin
  obtain ⟨i, hi, hPi⟩ := Set.mem_iUnion₂.1 hin
  exact hbT (((hwb i (hT hi)).1 hPi) ▸ hi)

section Pruning

variable [∀ a w, Decidable (P a w)]

/-- With the alternatives over `m` atoms, as in (21), `pex` makes the plural true after
accommodation iff all but at most `m - 1` atoms satisfy the predicate. -/
theorem pexPlural_subDisjsOfCard_eq_one_iff (h : Separating D x P) {m : ℕ} (hm : 0 < m)
    (hmn : m ≤ (x ∩ D).card) :
    pexPlural D x P (subDisjsOfCard (x ∩ D) (atom P) m) w = 1 ↔
      w ∈ atLeast D x P ((x ∩ D).card + 1 - m) := by
  have hne : (x ∩ D).Nonempty := Finset.card_pos.1 (by omega)
  rw [pexIEII_eq_one_iff, pexPlural_ne_zero_iff h hne, mem_atLeast, count]
  have key := forall_card_eq_exists_mem_iff (I := x ∩ D) (T := (x ∩ D).filter (P · w))
    (Finset.filter_subset _ _) (m := m)
  simp only [Finset.mem_filter] at key
  have hS : subDisjsOfCard (x ∩ D) (atom P) m ⊆ supClosure (atom P '' ↑(x ∩ D)) :=
    subDisjsOfCard_subset_supClosure hne hm
  constructor
  · rintro ⟨hhom, hw⟩
    suffices ∀ T ⊆ x ∩ D, T.card = m → ∃ i ∈ T, i ∈ x ∩ D ∧ P i w by
      have := key.1 this; omega
    intro T hT hcard
    rcases hmn.lt_or_eq with hlt | rfl
    · have hmem (T : Finset Atom) (hT : T ⊆ x ∩ D) (hcard : T.card = m) :
          ⋃ i ∈ T, atom P i ∈ supClosure (atom P '' ↑(x ∩ D)) \ {⋃ i ∈ x ∩ D, atom P i} ∩
            subDisjsOfCard (x ∩ D) (atom P) m :=
        have hR : ⋃ i ∈ T, atom P i ∈ subDisjsOfCard (x ∩ D) (atom P) m := .inr ⟨T, hT, hcard, rfl⟩
        ⟨⟨hS hR, biUnion_ne_of_card_lt h hT (hcard ▸ hlt)⟩, hR⟩
      rcases hhom with hall | hnone
      · obtain ⟨i, hi, hPi⟩ := Set.mem_iUnion₂.1 (hall _ (hmem T hT hcard))
        exact ⟨i, hi, hT hi, hPi⟩
      · obtain ⟨a, ha, hPa⟩ := Set.mem_iUnion₂.1 hw
        obtain ⟨T', haT', hT', hcard'⟩ := Finset.exists_subsuperset_card_eq
          (Finset.singleton_subset_iff.2 ha) (by rw [Finset.card_singleton]; exact hm) hlt.le
        exact absurd (Set.mem_biUnion (haT' (Finset.mem_singleton_self a)) hPa)
          (hnone _ (hmem T' hT' hcard'))
    · obtain ⟨a, ha, hPa⟩ := Set.mem_iUnion₂.1 hw
      rw [Finset.eq_of_subset_of_card_le hT hcard.ge]
      exact ⟨a, ha, ha, hPa⟩
  · intro hk
    have hall := key.2 (by omega)
    have hw : w ∈ ⋃ i ∈ x ∩ D, atom P i := by
      obtain ⟨i, hi⟩ := Finset.card_pos.1 (show 0 < ((x ∩ D).filter (P · w)).card by omega)
      exact Set.mem_biUnion (Finset.mem_filter.1 hi).1 (Finset.mem_filter.1 hi).2
    refine ⟨.inl ?_, hw⟩
    rintro α ⟨-, rfl | ⟨T, hT, hcard, rfl⟩⟩
    · exact hw
    · obtain ⟨i, hi, -, hPi⟩ := hall T hT hcard
      exact Set.mem_biUnion hi hPi

end Pruning

end Plural

/-! ### Post-Accommodation Informativity (§3) -/

section Informativity

variable {W : Type*}

variable {Atom : Type*} [DecidableEq Atom] {D x : Finset Atom} {P : Atom → W → Prop}
  {R : Set (Set W)}

/-- Where the existential is common ground, a plural predication asserts nothing new, (10a) and
(13d). -/
theorem not_informative_pexPlural :
    ¬ PostAccommodationInformative (⋃ b ∈ x ∩ D, atom P b) (pexPlural D x P R) := fun h ↦
  let ⟨_, hw, h⟩ := postAccommodationInformative_iff.1 h
  (pexIEII_eq_neg_one_iff.1 h).2 hw

/-- Where the universal is known to fail, the negated plural predication asserts nothing new once
homogeneity is accommodated, (10b), (12b), (13c) and (23). -/
theorem not_informative_neg (h : Separating D x P) (hcard : 1 < (x ∩ D).card)
    (hR : ∀ a ∈ x ∩ D, atom P a ∈ R) :
    ¬ PostAccommodationInformative {w | ¬ ∀ a ∈ x, a ∈ D → P a w} (-pexPlural D x P R) := fun hi ↦
  let ⟨_, hw, hf⟩ := postAccommodationInformative_iff.1 hi
  hw ((pexPlural_eq_one_iff h hcard hR).1 (SignType.neg_eq_neg_one_iff.1 hf))

end Informativity

/-! ### Three students (§4, §5)

Worlds record who smiled, and `holds a w` says that `a` smiled at `w`. -/

section Students

/-- In (21), pruning to pairs of the three students makes *the students smiled* true after
accommodation iff at least two smiled. -/
theorem pexPlural_pairs_eq_one_iff (w : Finset (Fin 3)) :
    pexPlural Finset.univ Finset.univ holds (subDisjsOfCard Finset.univ (atom holds) 2) w = 1 ↔
      2 ≤ w.card := by
  have h := pexPlural_subDisjsOfCard_eq_one_iff (w := w) (separating_holds Finset.univ
    Finset.univ) (m := 2) two_pos (by simp)
  simpa [Finset.inter_self, count_holds] using h

/-- Student `a` did not smile at `w`. -/
abbrev notSmiled (a : Fin 3) (w : Finset (Fin 3)) : Prop := a ∉ w

private theorem separating_not : Separating Finset.univ Finset.univ notSmiled :=
  ⟨by decide, by decide⟩

/-- In (31), with homogeneity accommodated below negation and no pruning, *the students didn't
smile* is true where none of them smiled. -/
theorem localAccommodation_eq_one_iff (w : Finset (Fin 3)) :
    pexPlural Finset.univ Finset.univ notSmiled
      (supClosure (Set.range (atom notSmiled))) w = 1 ↔ w = ∅ := by
  rw [pexPlural_eq_one_iff separating_not (by decide)
    fun a _ ↦ subset_supClosure (Set.mem_range_self a), Finset.eq_empty_iff_forall_notMem]
  simp

/-- In (32)–(34), pruning the alternative for the third student makes *the students didn't smile*
true when only that student smiled, a non-maximal reading under negation. -/
theorem localAccommodation_nonMaximal :
    pexPlural Finset.univ Finset.univ notSmiled
      (supClosure (Set.range (atom notSmiled)) \ {atom notSmiled 2}) {2} = 1 := by
  rw [pexIEII_eq_one_iff, pexPlural_ne_zero_iff separating_not ⟨0, by simp⟩]
  refine ⟨.inl ?_, Set.mem_biUnion (x := 0) (by simp) (by decide)⟩
  rintro _ ⟨-, hq, hne⟩
  obtain ⟨S, ⟨c, hc⟩, rfl⟩ := Set.mem_supClosure_range.1 hq
  by_contra hout
  refine hne (Set.mem_singleton_iff.2
    ((congrArg (fun S ↦ ⋃ b ∈ S, atom notSmiled b) ?_).trans (Finset.set_biUnion_singleton 2 _)))
  ext a
  refine ⟨fun ha ↦ ?_, fun ha ↦ ?_⟩
  · by_contra h2
    exact hout (Set.mem_biUnion ha (by simpa [atom, notSmiled] using h2))
  · rw [Finset.mem_singleton.1 ha]
    by_contra h2
    have hc2 : c ≠ 2 := fun h ↦ h2 (h ▸ hc)
    exact hout (Set.mem_biUnion hc (by simpa [atom, notSmiled] using hc2))

end Students

/-! ### The judgments of §3

Each sentence is judged against the common ground its context sets up. Worlds record which books
Mary read, which teammates John is married to, which candidates won, or which students smiled. -/

section Judgments

open Finset

/-- In (9), with John's kids known to be adopted, *all 10 of John's kids are adopted* is
uninformative after accommodation and *John has 10 adopted kids* informative. -/
theorem judgments_9 :
    (Examples.ex_9a.judgment = .acceptable ↔
      PostAccommodationInformative {w : ℕ × Bool | w.2 = true}
        ({w | w.1 = 10}.indicator fun w ↦ SignType.ofProp (w.2 = true))) ∧
    (Examples.ex_9b.judgment = .acceptable ↔
      PostAccommodationInformative {w : ℕ × Bool | w.2 = true}
        fun w ↦ SignType.ofProp (w.1 = 10 ∧ w.2 = true)) :=
  ⟨iff_of_false (by decide) fun h ↦ by
      obtain ⟨_, hw, h⟩ := postAccommodationInformative_iff.1 h
      simp_all,
    iff_of_true (by decide) (postAccommodationInformative_iff.2 ⟨(3, true), rfl, by decide⟩)⟩

private theorem subset_not_forall {n : ℕ} :
    {w : Finset (Fin n) | w ≠ univ} ⊆ {w | ¬ ∀ a ∈ univ, a ∈ univ → holds a w} :=
  fun _ hw hall ↦ hw (eq_univ_of_forall fun a ↦ hall a (mem_univ a) (mem_univ a))

/-- In (10), *she read the books* is uninformative given that Mary read some of them, and *she
didn't read the books* given that she did not read all. -/
theorem judgments_10 :
    (Examples.ex_10a.judgment = .acceptable ↔
      PostAccommodationInformative {w : Finset (Fin 2) | w.Nonempty}
        (pexPlural univ univ holds (supClosure (Set.range (atom holds))))) ∧
    (Examples.ex_10b.judgment = .acceptable ↔
      PostAccommodationInformative {w : Finset (Fin 2) | w ≠ univ}
        (-pexPlural univ univ holds (supClosure (Set.range (atom holds))))) :=
  ⟨iff_of_false (by decide) fun h ↦ not_informative_pexPlural
      (h.mono fun _ ⟨a, ha⟩ ↦ Set.mem_biUnion (by simp) ha),
    iff_of_false (by decide) fun h ↦ not_informative_neg (separating_holds _ _) (by decide)
      (fun a _ ↦ subset_supClosure (Set.mem_range_self a)) (h.mono subset_not_forall)⟩

/-- In (12), *John isn't married to any of his teammates* is informative, and *John isn't married to
his teammates* is not once homogeneity is accommodated. -/
theorem judgments_12 :
    (Examples.ex_12a.judgment = .acceptable ↔
      PostAccommodationInformative {w : Finset (Fin 2) | w ≠ univ}
        fun w ↦ SignType.ofProp (w = ∅)) ∧
    (Examples.ex_12b.judgment = .acceptable ↔
      PostAccommodationInformative {w : Finset (Fin 2) | w ≠ univ}
        (-pexPlural univ univ holds (supClosure (Set.range (atom holds))))) :=
  ⟨iff_of_true (by decide) (postAccommodationInformative_iff.2 ⟨{0}, by decide, by decide⟩),
    iff_of_false (by decide) fun h ↦ not_informative_neg (separating_holds _ _) (by decide)
      (fun a _ ↦ subset_supClosure (Set.mem_range_self a)) (h.mono subset_not_forall)⟩

/-- In (13), with at most one winner, *none of the candidates won* and *all of the candidates lost*
are informative, and their plural-definite counterparts are not. -/
theorem judgments_13 :
    (Examples.ex_13a.judgment = .acceptable ↔
      PostAccommodationInformative {w : Finset (Fin 2) | w.card ≤ 1}
        fun w ↦ SignType.ofProp (w = ∅)) ∧
    (Examples.ex_13b.judgment = .acceptable ↔
      PostAccommodationInformative {w : Finset (Fin 2) | w.card ≤ 1}
        fun w ↦ SignType.ofProp (∀ a, a ∉ w)) ∧
    (Examples.ex_13c.judgment = .acceptable ↔
      PostAccommodationInformative {w : Finset (Fin 2) | w.card ≤ 1}
        (-pexPlural univ univ holds (supClosure (Set.range (atom holds))))) ∧
    (Examples.ex_13d.judgment = .acceptable ↔
      PostAccommodationInformative {w : Finset (Fin 2) | w.card ≤ 1}
        (pexPlural univ univ (fun (a : Fin 2) (w : Finset (Fin 2)) ↦ a ∉ w)
          (supClosure (Set.range (atom fun a w ↦ a ∉ w))))) :=
  ⟨iff_of_true (by decide) (postAccommodationInformative_iff.2 ⟨{0}, by decide, by decide⟩),
    iff_of_true (by decide) (postAccommodationInformative_iff.2 ⟨{0}, by decide, by decide⟩),
    iff_of_false (by decide) fun h ↦ not_informative_neg (separating_holds _ _) (by decide)
      (fun a _ ↦ subset_supClosure (Set.mem_range_self a))
      (h.mono fun w hw hall ↦ by
        rw [eq_univ_of_forall fun a ↦ hall a (mem_univ a) (mem_univ a)] at hw
        exact absurd hw (by decide)),
    iff_of_false (by decide) fun h ↦ not_informative_pexPlural (h.mono fun w hw ↦ by
      obtain ⟨a, -, ha⟩ := exists_mem_notMem_of_card_lt_card (s := w) (t := univ)
        ((Set.mem_ofPred_eq.mp hw).trans_lt (by decide))
      exact Set.mem_biUnion (by simp) ha)⟩

/-- In (23), with the students known not to have all smiled, *the students didn't smile* asserts
nothing new once homogeneity is accommodated. -/
theorem judgments_23 :
    Examples.ex_23.judgment = .acceptable ↔
      PostAccommodationInformative {w : Finset (Fin 3) | w ≠ univ}
        (-pexPlural univ univ holds (supClosure (Set.range (atom holds)))) :=
  iff_of_false (by decide) fun h ↦ not_informative_neg (separating_holds _ _) (by decide)
    (fun a _ ↦ subset_supClosure (Set.mem_range_self a)) (h.mono subset_not_forall)

end Judgments

end GuerriniWehbe2025
