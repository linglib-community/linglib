module

public import Studies.BarLevFox2020
public import Linglib.Semantics.Alternatives.Pruning
public import Linglib.Semantics.Homogeneity.Plural
public import Linglib.Data.Statistics.KrizChemla2015

/-!
# Bar-Lev (2021): An Implicature Account of Homogeneity and Non-Maximality

Bar-Lev derives homogeneity as an implicature. A plural definite means existential
pluralization, that some atom of the plurality in a domain has the property, and its alternatives
replace the domain by its subsets, so that they are the disjunctions of the atomic predications
with no conjunction among them. Exhaustifying over all of them
[gives the universal reading](##exhIEII_eq_universal), while under negation
[exhaustification is vacuous](##Exhaustification.exhIEII_compl_biUnion). Non-maximal readings
come from pruning: a set of alternatives may replace the whole set when exhaustifying over it
only weakens the universal reading, which holds exactly when it makes no alternative innocently
excludable, and the readings so derived are [the conjunctions of alternatives that are not
themselves alternatives, and the plain existential
one](##Alternatives.prunedReadings_eq). They include "at least `k`" for every `k` and lie
among Križ and Spector's candidate meanings. The question the context raises selects the
strongest reading it determines; [every reading is selected by the question whether it
holds](##Alternatives.isPrunedReading_polar), and a world is gappy, true on the reading one
question selects and false on another's, [exactly where trivalent plural predication is
undefined](##gappy_iff_barePlural_eq_undefined).

## Implementation notes

The prejacent and the alternatives are the disjunction of the atomic predications over the atoms
of the plurality and its closure under disjunction, the form the paper adopts once the domain is
assumed to hold every part of the plurality; the general theory of exhaustifying and pruning such
a disjunction is `Exhaustification.exhIEII_supClosure` and `Alternatives.prunedReadings`.
`Gappy` ranges over all partitions and is context-free; that a context fixing the partition
removes the gap is carried by `reading_80` and `reading_81`.

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

open Exhaustification Alternatives

variable {Atom W : Type*} {x : Finset Atom} {P : Atom → W → Prop}

/-! ### Existential pluralization and its subdomain alternatives

The existential pluralization `∃-PL_D` of `P` over a plurality is the disjunction of its atoms in
the domain `D`. A subdomain `D' ⊆ D` leaves some of the atoms, so with `x` the atoms of the
plurality in the domain, the prejacent is `⋃ a ∈ x, atom P a` and the subdomain alternatives are
the closure of the atoms under disjunction, `supClosure (atom P '' ↑x)`. -/

variable (P) in
/-- The proposition `a` satisfies `P`. -/
def atom (a : Atom) : Set W := {w | P a w}

instance [∀ a w, Decidable (P a w)] (w : W) (a : Atom) : Decidable (w ∈ atom P a) :=
  inferInstanceAs (Decidable (P a w))

-- Each subdomain alternative is one of Križ and Spector's candidate meanings.
theorem supClosure_subset_readings :
    supClosure (atom P '' ↑x) ⊆ Homogeneity.readings (fun z ↦ {w | ∀ a ∈ z, P a w}) x := by
  intro q hq
  obtain ⟨S, ⟨a, ha⟩, hS, -⟩ := Set.mem_supClosure_image.1 hq
  rw [Homogeneity.readings_eq_latticeClosure ⟨a, hS ha⟩]
  exact supClosure_min subset_latticeClosure isSublattice_latticeClosure.supClosed hq

-- So is each reading that pruning derives.
theorem prunedReadings_subset_readings (h : Separating x (atom P)) (hne : x.Nonempty) :
    prunedReadings (supClosure (atom P '' ↑x)) (⋃ a ∈ x, atom P a) ⊆
      Homogeneity.readings (fun z ↦ {w | ∀ a ∈ z, P a w}) x := by
  rw [Homogeneity.readings_eq_latticeClosure hne]
  exact (prunedReadings_subset_infClosure h hne).trans (infClosure_min (supClosure_min
    subset_latticeClosure isSublattice_latticeClosure.supClosed)
    isSublattice_latticeClosure.infClosed)

/-! ### Homogeneity -/

/-- Exhaustifying `∃-PL` over its subdomain alternatives gives the universal reading, the
maximality implicature. -/
theorem exhIEII_eq_universal (h : Separating x (atom P)) (hne : x.Nonempty) :
    exhIEII (supClosure (atom P '' ↑x)) (⋃ a ∈ x, atom P a) = {w | ∀ a ∈ x, P a w} := by
  rw [exhIEII_supClosure h hne]
  ext w; simp [atom]

-- (6a)
theorem exists_mem_biUnion_and_not (h : Separating x (atom P)) {a : Atom} (ha : a ∈ x)
    (h2 : 2 ≤ x.card) : ∃ w ∈ (⋃ b ∈ x, atom P b), ¬ P a w := by
  obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (by omega : 1 < x.card) a
  obtain ⟨w, hw⟩ := h.single b hb
  exact ⟨w, Set.mem_biUnion hb ((hw b hb).2 rfl), fun hPa ↦ hba ((hw a ha).1 hPa).symm⟩

-- (6b)
theorem not_of_notMem_biUnion {w : W} (hw : w ∉ ⋃ b ∈ x, atom P b) {a : Atom} (ha : a ∈ x) :
    ¬ P a w :=
  fun hPa ↦ hw (Set.mem_biUnion ha hPa)

-- With a conjunctive alternative, as a floating quantifier would supply, no homogeneity.
theorem not_forall_of_mem_exhIEII_insert_iInter (h : Separating x (atom P)) (h2 : 2 ≤ x.card)
    {w : W} (hw : w ∈ exhIEII (insert (⋂ a ∈ x, atom P a) (supClosure (atom P '' ↑x)))
      (⋃ b ∈ x, atom P b)) : ¬ ∀ a ∈ x, P a w :=
  fun hall ↦ hw.2.1 _ (isInnocentlyExcludable_iInter_of_insert h.single h2)
    (Set.mem_iInter₂.2 fun a ha ↦ hall a ha)

/-! ### Gappiness -/

variable (x P) in
/-- A world is gappy when it is true on the reading some partition selects and false on another's.
-/
def Gappy (w : W) : Prop :=
  (∃ (Q : Setoid W) (q : Set W),
      IsPrunedReading (supClosure (atom P '' ↑x)) (⋃ a ∈ x, atom P a) Q q ∧ w ∈ q) ∧
    ∃ (Q : Setoid W) (q : Set W),
      IsPrunedReading (supClosure (atom P '' ↑x)) (⋃ a ∈ x, atom P a) Q q ∧ w ∉ q

theorem gappy_iff (h : Separating x (atom P)) (hne : x.Nonempty) (w : W) :
    Gappy x P w ↔ (∃ a ∈ x, P a w) ∧ ∃ a ∈ x, ¬ P a w := by
  constructor
  · rintro ⟨⟨_, q, hq, hwq⟩, ⟨_, q', hq', hwq'⟩⟩
    obtain ⟨a, ha, hPa⟩ := Set.mem_iUnion₂.1 (subset_of_mem_prunedReadings hq.1.1 hwq)
    refine ⟨⟨a, ha, hPa⟩, by_contra fun hcon ↦ ?_⟩
    push Not at hcon
    exact hwq' (iInter_subset_of_mem_prunedReadings h hne hq'.1.1 (Set.mem_iInter₂.2 hcon))
  · rintro ⟨⟨a, ha, hPa⟩, ⟨b, hb, hPb⟩⟩
    have hne' := exhIEII_supClosure_nonempty h hne
    exact ⟨⟨_, _, isPrunedReading_polar hne' (self_mem_prunedReadings
        (biUnion_mem_supClosure hne) (h.biUnion_nonempty hne)), Set.mem_biUnion ha hPa⟩,
      ⟨_, _, isPrunedReading_polar hne' (iInter_mem_prunedReadings h hne),
        fun hall ↦ hPb (Set.mem_iInter₂.1 hall b hb)⟩⟩

section Decidable

variable [∀ a w, Decidable (P a w)]

/-- A plain positive definite plural is gappy exactly where [kriz-2016]'s trivalent plural
predication is undefined, where the accounts agree. -/
theorem gappy_iff_barePlural_eq_undefined (h : Separating x (atom P)) (hne : x.Nonempty)
    (w : W) : Gappy x P w ↔ Homogeneity.barePlural P x w = .undefined := by
  rw [gappy_iff h hne, Homogeneity.barePlural, Trivalent.supervaluation_eq_undefined_iff]

-- Trivalent plural predication is true where the exhaustified sentence is, and false where
-- the unexhaustified one is.
theorem barePlural_eq_true_iff_mem_exhIEII (h : Separating x (atom P)) (hne : x.Nonempty)
    (w : W) : Homogeneity.barePlural P x w = .true ↔
      w ∈ exhIEII (supClosure (atom P '' ↑x)) (⋃ b ∈ x, atom P b) := by
  rw [exhIEII_supClosure h hne, Homogeneity.barePlural, Trivalent.supervaluation_eq_true_iff,
    Set.mem_iInter₂]
  rfl

theorem barePlural_eq_false_iff_notMem_biUnion (hne : x.Nonempty) (w : W) :
    Homogeneity.barePlural P x w = .false ↔ w ∉ ⋃ b ∈ x, atom P b := by
  rw [Homogeneity.barePlural, Trivalent.supervaluation_eq_false_iff, Set.mem_iUnion₂]
  simp [hne, atom]

-- At a gappy world the trivalent negation is still undefined, while the negative sentence with
-- negation over `∃-PL`, exhaustified over any of its alternatives, is plainly false, where the
-- accounts part.
theorem compl_barePlural_eq_undefined_and_notMem_exhIEII_compl (h : Separating x (atom P))
    (hne : x.Nonempty) {w : W} (hw : Gappy x P w) (C : Set (Set W)) :
    (Homogeneity.barePlural P x w)ᶜ = .undefined ∧ w ∉ exhIEII C (⋃ b ∈ x, atom P b)ᶜ := by
  refine ⟨Trivalent.compl_eq_undefined_iff.2
    ((gappy_iff_barePlural_eq_undefined h hne w).1 hw), ?_⟩
  obtain ⟨a, ha, hPa⟩ := ((gappy_iff h hne w).1 hw).1
  exact fun hmem ↦ hmem.1 (Set.mem_biUnion ha hPa)

theorem gappy_iff_trueCount (h : Separating x (atom P)) (hne : x.Nonempty) (w : W) :
    Gappy x P w ↔ 0 < trueCount x (atom P) w ∧ trueCount x (atom P) w < x.card := by
  rw [gappy_iff h hne, trueCount_pos, (trueCount_le_card w).lt_iff_ne, ne_eq, trueCount_eq_card]
  simp [atom]

end Decidable

/-! ### The model whose worlds record who laughed -/

section Model

/-- In the model whose worlds are the sets of atoms satisfying the predicate, `a` satisfies it at
the world `w` when `a ∈ w`. -/
abbrev holds (a : Atom) (w : Finset Atom) : Prop := a ∈ w

variable (x)

theorem forall_subset_exists_holds_iff :
    ∀ T ⊆ x, T.Nonempty → ∃ w, ∀ a ∈ x, w ∈ atom holds a ↔ a ∈ T :=
  fun T _ _ ↦ ⟨T, fun _ _ ↦ Iff.rfl⟩

theorem separating_holds : Separating x (atom holds) :=
  ⟨fun a _ ↦ ⟨{a}, fun _ _ ↦ Finset.mem_singleton⟩, ⟨x, fun _ ↦ id⟩⟩

variable [DecidableEq Atom]

theorem trueCount_holds (w : Finset Atom) : trueCount x (atom holds) w = (x ∩ w).card := by
  change (x.filter (· ∈ w)).card = _
  rw [Finset.filter_mem_eq_inter]

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
    exhIEII (supClosure (atom holds '' pair)) (⋃ b ∈ pair, atom holds b) = {w | pair ⊆ w} :=
  exhIEII_eq_universal (separating_holds pair) (by decide)

-- *Kelly laughed* is an alternative of *the kids laughed* and so not a reading of it.
theorem kellyLaughed_notMem_prunedReadings :
    kellyLaughed ∉
      prunedReadings (supClosure (atom holds '' ↑kids)) (⋃ a ∈ kids, atom holds a) := by
  rw [prunedReadings_eq (forall_subset_exists_holds_iff kids) ⟨.kelly, Finset.mem_univ _⟩]
  refine fun h ↦ h.2 ⟨subset_supClosure (Set.mem_image_of_mem _ (Finset.mem_univ _)), fun heq ↦ ?_⟩
  have hj : ({.jane} : Finset Kid) ∈ kellyLaughed :=
    heq ▸ Set.mem_biUnion (Finset.mem_univ Kid.jane) (Finset.mem_singleton_self _)
  exact absurd hj (by decide)

-- Given the partition (66), *the kids laughed* means that at least two of the kids laughed.
theorem reading_66 :
    IsPrunedReading (supClosure (atom holds '' ↑kids)) (⋃ a ∈ kids, atom holds a)
      (Setoid.polar (atLeastTrue kids (atom holds) 2))
      (atLeastTrue kids (atom holds) 2) :=
  isPrunedReading_polar_atLeastTrue (separating_holds kids) (by decide) (by decide)

/-- The ten books on the reading list. -/
abbrev Book := Fin 10

/-- The books. -/
def books : Finset Book := Finset.univ

-- In the context of (80), *Mary read the books* means that she read at least five of them.
theorem reading_80 :
    IsPrunedReading (supClosure (atom holds '' ↑books)) (⋃ a ∈ books, atom holds a)
      (Setoid.polar (atLeastTrue books (atom holds) 5))
      (atLeastTrue books (atom holds) 5) :=
  isPrunedReading_polar_atLeastTrue (separating_holds books) (by decide) (by decide)

-- In the context of (81), where only reading all ten passes, *Mary read the books* has its
-- maximal reading.
theorem reading_81 :
    IsPrunedReading (supClosure (atom holds '' ↑books)) (⋃ a ∈ books, atom holds a)
      (Setoid.polar (atLeastTrue books (atom holds) 10))
      (atLeastTrue books (atom holds) 10) :=
  isPrunedReading_polar_atLeastTrue (separating_holds books) (by decide) (by decide)

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
      (Gappy Finset.univ holds w ↔ i.condition = .gap)) ∧
    ∀ t ∈ gapTests, t.embedding = .unembedded → t.found = .yes := by
  refine ⟨fun i hi he w hw ↦ ?_, by decide⟩
  have h := krizChemla_unembedded i hi he w.card (by simp [hw])
  rw [gappy_iff_trueCount (separating_holds _) ⟨0, by simp⟩, trueCount_holds]
  simpa using h

-- Under negation every GAP display is false whatever is pruned, though Table 2 found a gap
-- there in Experiments A1 and B1.
theorem krizChemla_negation_residue :
    (∀ i ∈ items, i.embedding = .unembedded → i.condition = .gap → ∀ w : Finset Symbol,
      i.cells = [w.card] → ∀ C, w ∉ exhIEII C (⋃ b ∈ Finset.univ, atom holds b)ᶜ) ∧
    ∀ t ∈ gapTests, t.embedding = .negation → t.found = .yes := by
  refine ⟨fun i hi he hc w hw C ↦ ?_, by decide⟩
  have hg := (gappy_iff_krizChemla_gap.1 i hi he w hw).2 hc
  exact (compl_barePlural_eq_undefined_and_notMem_exhIEII_compl
    (separating_holds _) ⟨0, by simp⟩ hg C).2

end KrizChemla

end BarLev2021
