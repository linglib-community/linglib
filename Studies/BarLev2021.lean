module

public import Linglib.Semantics.Exhaustification.Disjunctive
public import Linglib.Semantics.Questions.Partition.Basic
public import Linglib.Semantics.Homogeneity.Plural
public import Linglib.Data.Experiments.KrizChemla2015
public import Linglib.Data.Examples.BarLev2021

/-!
# Bar-Lev (2021): An Implicature Account of Homogeneity and Non-Maximality

Bar-Lev derives homogeneity as an implicature. A plural definite means existential
pluralization, that some atom of the plurality in a domain has the property, and its alternatives
replace the domain by its subsets; each alternative is one of the readings of the plural
predication (`supClosure_subset_readings`). Exhaustifying over them gives the universal
reading, while under negation exhaustification is vacuous. Pruning the alternatives to subdomains
of a fixed size gives the threshold readings of non-maximality, which are readings of the plural
predication as well (`readings_subset_readings`); the question the context raises selects among
them, and a world is gappy when it verifies the reading one question selects and falsifies
another's.

## Main results

* `exhIEII_eq_universal`, `exhIEII_compl_biUnion`: the maximality implicature, and its absence
  under negation.
* `exhIEII_pruned_eq_atLeast`, `isReading_polar_atLeast`: pruning yields the threshold
  readings, and a polar question on a threshold selects it.
* `gappy_iff_barePlural_eq_zero`: the gappy worlds are those where Križ's trivalent plural is
  undefined; `neg_barePlural_eq_zero_and_notMem_exhIEII_compl`: the accounts part under negation.
* `gappy_iff_krizChemla_gap`, `krizChemla_negation_residue`: on Križ and Chemla's unembedded
  displays the account predicts their gaps for the positive sentence and misses those under
  negation.
* `disjunction_not_both`, `plural_both`, `reading_66`, `reading_80`, `reading_81`: the paper's
  examples.

## Implementation notes

`readings` are the threshold readings, obtained by pruning to a fixed subdomain size; the
paper's asymmetric conjunctions of alternatives are omitted, so `IsReading` agrees with the
paper's selection on the partitions whose only decided readings are thresholds, which
includes the polar questions of (66), (80) and (81). The maximality constraint on prunings
is not formalized. `Gappy` ranges over all partitions and is context-free; that a context
fixing the partition removes the gap is carried by `reading_80` and `reading_81`.

## TODO

* The negative sentence is modelled only at the LF with negation over `∃-PL`; the LF with
  `∃-PL` over negation and the cover-restricted `∃-PL` of §5.3, the paper's source of the
  marginal negative non-maximal readings and of Križ and Chemla's negative gaps, are not
  formalized.
* The paper's full set of readings, and the non-distributive extension of §8.

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
  obtain ⟨S, -, hS, rfl⟩ := Set.mem_supClosure_image.1 hq'
  exact Set.compl_subset_compl.2 (Set.biUnion_subset_biUnion_left hS)

/-- The existential basic meaning does not entail that a given kid laughed, (6a). -/
theorem exists_mem_biUnion_and_not (h : Separating D x P) {a : Atom} (ha : a ∈ x ∩ D)
    (h2 : 2 ≤ (x ∩ D).card) : ∃ w ∈ (⋃ b ∈ x ∩ D, atom P b), ¬ P a w := by
  obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (by omega : 1 < (x ∩ D).card) a
  obtain ⟨w, hw⟩ := h.single b hb
  exact ⟨w, Set.mem_biUnion hb ((hw b hb).2 rfl), fun hPa ↦ hba ((hw a ha).1 hPa).symm⟩

/-- Its negation entails that no given kid laughed, (6b). -/
theorem not_of_notMem_biUnion {w : W} (hw : w ∉ ⋃ b ∈ x ∩ D, atom P b) {a : Atom}
    (ha : a ∈ x ∩ D) : ¬ P a w :=
  fun hPa ↦ hw (Set.mem_biUnion ha hPa)

theorem not_forall_of_mem_exhIEII_insert_iInter (h : Separating D x P) (h2 : 2 ≤ (x ∩ D).card)
    {w : W} (hw : w ∈ exhIEII (insert (⋂ a ∈ x ∩ D, atom P a) (supClosure (atom P '' ↑(x ∩ D))))
      (⋃ b ∈ x ∩ D, atom P b)) : ¬ ∀ a ∈ x ∩ D, P a w :=
  fun hall ↦ hw.2.1 _ (isInnocentlyExcludable_iInter_of_insert (p := atom P) h.single h2)
    (Set.mem_iInter₂.2 fun a ha ↦ hall a ha)

/-! ### Non-maximality by pruning -/

variable (D x P) in
/-- The readings of *the kids laughed* are the maximal one and the pruned ones. -/
def readings : Set (Set W) :=
  {q | ∃ m, 0 < m ∧ m ≤ (x ∩ D).card ∧
    q = exhIEII (subDisjsOfCard (x ∩ D) (atom P) m) (⋃ b ∈ x ∩ D, atom P b)}

variable (D x P) in
/-- The reading a partition selects is the strongest reading it decides. -/
def IsReading (Q : Setoid W) (q : Set W) : Prop :=
  q ∈ readings D x P ∧ Q.Decides q ∧ ∀ r ∈ readings D x P, Q.Decides r → q ⊆ r

theorem IsReading.unique {Q : Setoid W} {q r : Set W} (hq : IsReading D x P Q q)
    (hr : IsReading D x P Q r) : q = r :=
  subset_antisymm (hq.2.2 r hr.1 hr.2.1) (hr.2.2 q hq.1 hq.2.1)

section Pruning

variable [∀ a w, Decidable (P a w)]

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

/-- Exhaustifying over the size-`m` alternatives yields "at least `n + 1 - m` of the kids
laughed". -/
theorem exhIEII_pruned_eq_atLeast (h : Separating D x P) {m : ℕ} (hm : 0 < m)
    (hmn : m ≤ (x ∩ D).card) :
    exhIEII (subDisjsOfCard (x ∩ D) (atom P) m) (⋃ b ∈ x ∩ D, atom P b) =
      atLeast D x P ((x ∩ D).card + 1 - m) := by
  rw [exhIEII_subDisjsOfCard (p := atom P) h.single h.all hm hmn]
  ext w
  change (x ∩ D).card < m + count D x P w ↔ (x ∩ D).card + 1 - m ≤ count D x P w
  omega

theorem mem_readings_iff (h : Separating D x P) {q : Set W} :
    q ∈ readings D x P ↔ ∃ k, 0 < k ∧ k ≤ (x ∩ D).card ∧ q = atLeast D x P k := by
  constructor
  · rintro ⟨m, hm, hmn, rfl⟩
    exact ⟨_, by omega, by omega, exhIEII_pruned_eq_atLeast h hm hmn⟩
  · rintro ⟨k, hk, hkn, rfl⟩
    refine ⟨(x ∩ D).card + 1 - k, by omega, by omega, ?_⟩
    rw [exhIEII_pruned_eq_atLeast h (by omega) (by omega)]
    congr 1; omega

theorem readings_subset_readings (h : Separating D x P) :
    readings D x P ⊆ Homogeneity.readings (fun z ↦ {w | ∀ a ∈ z, P a w}) x := by
  intro q hq
  obtain ⟨k, hk, hkn, rfl⟩ := (mem_readings_iff h).1 hq
  refine ⟨⟨{z | k ≤ (z ∩ D).card}, fun _ _ hzz hz ↦ hz.trans
    (Finset.card_le_card (Finset.inter_subset_inter_right hzz))⟩, hkn, Set.ext fun w ↦ ⟨?_, ?_⟩⟩
  · intro hw
    refine ⟨(x ∩ D).filter (P · w), ?_, (Finset.filter_subset _ _).trans Finset.inter_subset_left,
      isBot_iff_eq_bot.not.2 (Finset.nonempty_iff_ne_empty.1 (Finset.card_pos.1 (hk.trans_le hw))),
      fun a ha ↦ (Finset.mem_filter.1 ha).2⟩
    show k ≤ ((x ∩ D).filter (P · w) ∩ D).card
    rw [Finset.inter_eq_left.2 ((Finset.filter_subset _ _).trans Finset.inter_subset_right)]
    exact hw
  · rintro ⟨z, hz, hzx, -, hP⟩
    refine hz.trans (Finset.card_le_card fun a ha ↦ ?_)
    rw [Finset.mem_inter] at ha
    exact Finset.mem_filter.2 ⟨Finset.mem_inter.2 ⟨hzx ha.1, ha.2⟩, hP a ha.1⟩

theorem exhIEII_supClosure_subset_exhIEII_subDisjsOfCard (h : Separating D x P)
    (hne : (x ∩ D).Nonempty) {m : ℕ} (hm : 0 < m) (hmn : m ≤ (x ∩ D).card) :
    exhIEII (supClosure (atom P '' ↑(x ∩ D))) (⋃ b ∈ x ∩ D, atom P b) ⊆
      exhIEII (subDisjsOfCard (x ∩ D) (atom P) m) (⋃ b ∈ x ∩ D, atom P b) := by
  rw [exhIEII_eq_universal h hne, exhIEII_pruned_eq_atLeast h hm hmn, ← atLeast_card]
  exact atLeast_antitone (by omega)

/-! ### Relevance and gappiness -/

/-- Given the polar question whether at least `k` of the kids laughed, *the kids laughed* means
that at least `k` did, provided every number of laughers is realized at some world. -/
theorem isReading_polar_atLeast (h : Separating D x P)
    (hcount : ∀ k ≤ (x ∩ D).card, ∃ w, count D x P w = k) {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ (x ∩ D).card) :
    IsReading D x P (Setoid.polar (atLeast D x P k)) (atLeast D x P k) := by
  refine ⟨(mem_readings_iff h).2 ⟨k, hk, hkn, rfl⟩, Setoid.polar_decides, fun r hr hQ ↦ ?_⟩
  obtain ⟨l, hl, hln, rfl⟩ := (mem_readings_iff h).1 hr
  refine atLeast_antitone (not_lt.1 fun hkl ↦ ?_)
  obtain ⟨w, hw⟩ := hcount l hln
  obtain ⟨v, hv⟩ := hcount k hkn
  have := hQ.iff (w := w) (v := v) (Setoid.polar_iff.2 (by simp only [mem_atLeast]; omega))
  simp only [mem_atLeast, hw, hv] at this
  omega

variable (D x P) in
/-- A world is gappy when it is true on the reading some partition selects and false on another's.
-/
def Gappy (w : W) : Prop :=
  (∃ (Q : Setoid W) (q : Set W), IsReading D x P Q q ∧ w ∈ q) ∧
    ∃ (Q : Setoid W) (q : Set W), IsReading D x P Q q ∧ w ∉ q

theorem gappy_iff (h : Separating D x P) (hcount : ∀ k ≤ (x ∩ D).card, ∃ w, count D x P w = k)
    (w : W) : Gappy D x P w ↔ 0 < count D x P w ∧ count D x P w < (x ∩ D).card := by
  constructor
  · rintro ⟨⟨_, q, ⟨hq, -, -⟩, hwq⟩, ⟨_, q', ⟨hq', -, -⟩, hwq'⟩⟩
    obtain ⟨k, hk, hkn, rfl⟩ := (mem_readings_iff h).1 hq
    obtain ⟨l, hl, hln, rfl⟩ := (mem_readings_iff h).1 hq'
    simp only [mem_atLeast, not_le] at hwq hwq'
    omega
  · rintro ⟨hpos, hlt⟩
    exact ⟨⟨_, _, isReading_polar_atLeast h hcount hpos (count_le_card w), mem_atLeast.2 le_rfl⟩,
      ⟨_, _, isReading_polar_atLeast h hcount (Nat.succ_pos _) hlt, by simp⟩⟩

/-- A plain positive definite plural is gappy exactly where [kriz-2016]'s trivalent plural
predication is undefined, where the accounts agree. -/
theorem gappy_iff_barePlural_eq_zero (h : Separating D x P)
    (hcount : ∀ k ≤ (x ∩ D).card, ∃ w, count D x P w = k) (w : W) :
    Gappy D x P w ↔ Homogeneity.barePlural P (x ∩ D) w = 0 := by
  rw [gappy_iff h hcount, Homogeneity.barePlural, SignType.supervaluation_eq_zero_iff, count,
    ← Finset.filter_ssubset, ← Finset.filter_nonempty_iff, Finset.card_pos]
  exact and_congr_right fun _ ↦ ⟨fun hlt ↦ Finset.ssubset_iff_subset_ne.2
    ⟨Finset.filter_subset _ _, ne_of_apply_ne _ hlt.ne⟩, Finset.card_lt_card⟩

/-- At a gappy world the trivalent negation is still undefined, while the negative sentence with
negation over `∃-PL`, exhaustified over any of its alternatives, is plainly false, where the
accounts part. -/
theorem neg_barePlural_eq_zero_and_notMem_exhIEII_compl (h : Separating D x P)
    (hcount : ∀ k ≤ (x ∩ D).card, ∃ w, count D x P w = k) {w : W} (hw : Gappy D x P w)
    (C : Set (Set W)) :
    -Homogeneity.barePlural P (x ∩ D) w = 0 ∧
      w ∉ exhIEII C (⋃ b ∈ x ∩ D, atom P b)ᶜ := by
  refine ⟨SignType.neg_eq_zero_iff.2 ((gappy_iff_barePlural_eq_zero h hcount w).1 hw), ?_⟩
  obtain ⟨a, ha⟩ := Finset.card_pos.1 ((gappy_iff h hcount w).1 hw).1
  obtain ⟨ha, hPa⟩ := Finset.mem_filter.1 ha
  exact fun hmem ↦ hmem.1 (Set.mem_biUnion ha hPa)

end Pruning

/-! ### The model whose worlds record who laughed -/

section Model

/-- In the model whose worlds are the sets of atoms satisfying the predicate, `a` satisfies it at
the world `w` when `a ∈ w`. -/
abbrev holds (a : Atom) (w : Finset Atom) : Prop := a ∈ w

variable (D x)

theorem separating_holds : Separating D x holds :=
  ⟨fun a _ ↦ ⟨{a}, fun _ _ ↦ Finset.mem_singleton⟩, ⟨x ∩ D, fun _ ↦ id⟩⟩

theorem count_holds (w : Finset Atom) : count D x holds w = (x ∩ D ∩ w).card := by
  rw [count, Finset.filter_mem_eq_inter]

theorem exists_count_holds_eq (k : ℕ) (hk : k ≤ (x ∩ D).card) : ∃ w, count D x holds w = k := by
  obtain ⟨S, hS, rfl⟩ := Finset.exists_subset_card_eq hk
  exact ⟨S, by rw [count_holds, Finset.inter_eq_right.2 hS]⟩

theorem isReading_polar_atLeast_holds {k : ℕ} (hk : 0 < k) (hkn : k ≤ (x ∩ D).card) :
    IsReading D x holds (Setoid.polar (atLeast D x holds k)) (atLeast D x holds k) :=
  isReading_polar_atLeast (separating_holds D x) (exists_count_holds_eq D x) hk hkn

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

/-- *Kelly or Jane laughed*, (41a), whose alternatives include the conjunction, is strengthened
to "not both". -/
theorem disjunction_not_both :
    exhIEII {kellyLaughed ∪ janeLaughed, kellyLaughed, janeLaughed, kellyLaughed ∩ janeLaughed}
        (kellyLaughed ∪ janeLaughed) =
      (kellyLaughed ∪ janeLaughed) \ (kellyLaughed ∩ janeLaughed) :=
  exhIEII_pair_inter le_rfl
    ⟨{.kelly}, ⟨Or.inl (Finset.mem_singleton_self _), Finset.mem_singleton_self _⟩, by decide⟩
    ⟨{.jane}, ⟨Or.inr (Finset.mem_singleton_self _), Finset.mem_singleton_self _⟩, by decide⟩

/-- *The kids laughed*, (41b), whose alternatives are the subdomain alternatives alone, is
strengthened to "both". -/
theorem plural_both :
    exhIEII (supClosure (atom holds '' pair)) (⋃ b ∈ pair, atom holds b) = {w | pair ⊆ w} := by
  have := exhIEII_eq_universal (separating_holds pair pair) (by decide)
  rw [Finset.inter_self] at this
  exact this.trans (Set.ext fun w ↦ ⟨fun h _ ha ↦ h _ ha ha, fun h a ha _ ↦ h ha⟩)

/-- Given the partition (66) — at most one kid laughed, or two or three did — *the kids
laughed* means that at least two of the kids laughed. -/
theorem reading_66 :
    IsReading kids kids holds (Setoid.polar (atLeast kids kids holds 2))
      (atLeast kids kids holds 2) :=
  isReading_polar_atLeast_holds kids kids (by decide) (by decide)

/-- The ten books on the reading list. -/
abbrev Book := Fin 10

/-- The books. -/
def books : Finset Book := Finset.univ

/-- In the context of (80), where reading any five of the ten books passes the test, *Mary
read the books* means that she read at least five of them; the paper offers the prediction
that a fixed partition removes the gap tentatively. -/
theorem reading_80 :
    IsReading books books holds (Setoid.polar (atLeast books books holds 5))
      (atLeast books books holds 5) :=
  isReading_polar_atLeast_holds books books (by decide) (by decide)

/-- In the context of (81), where only reading all ten passes, *Mary read the books* has its
maximal reading. -/
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

/-- On Križ and Chemla's unembedded displays the account makes the positive sentence gappy
exactly at the GAP displays, and every experiment that tested them found a gap there (Table 2).
-/
theorem gappy_iff_krizChemla_gap :
    (∀ i ∈ items, i.embedding = .unembedded → ∀ w : Finset Symbol, i.cells = [w.card] →
      (Gappy Finset.univ Finset.univ holds w ↔ i.condition = .gap)) ∧
    ∀ t ∈ gapTests, t.embedding = .unembedded → t.found = .yes := by
  refine ⟨fun i hi he w hw ↦ ?_, by decide⟩
  have h := krizChemla_unembedded i hi he w.card (by simp [hw])
  rw [gappy_iff (separating_holds _ _) (exists_count_holds_eq _ _), count_holds]
  simpa using h

/-- Under negation the account, with negation over `∃-PL`, makes every GAP display plainly false
whatever is pruned, while Table 2 found a gap there in Experiments A1 and B1, the residue the
paper attributes to the LF with `∃-PL` over negation. -/
theorem krizChemla_negation_residue :
    (∀ i ∈ items, i.embedding = .unembedded → i.condition = .gap → ∀ w : Finset Symbol,
      i.cells = [w.card] → ∀ C, w ∉ exhIEII C (⋃ b ∈ Finset.univ, atom holds b)ᶜ) ∧
    ∀ t ∈ gapTests, t.embedding = .negation → t.found = .yes := by
  refine ⟨fun i hi he hc w hw C ↦ ?_, by decide⟩
  have hg := (gappy_iff_krizChemla_gap.1 i hi he w hw).2 hc
  simpa only [Finset.inter_self] using (neg_barePlural_eq_zero_and_notMem_exhIEII_compl
    (separating_holds _ _) (exists_count_holds_eq _ _) hg C).2

end KrizChemla

/-- The paper's examples report gappiness for positive sentences and reduced gappiness for the
negative (82b), the asymmetry `neg_barePlural_eq_zero_and_notMem_exhIEII_compl` idealizes. -/
theorem rows_gappiness_positive : ∀ e ∈ Examples.all,
    e.feature? "gappiness" = some "yes" → e.feature? "polarity" = some "positive" := by
  decide

end BarLev2021
