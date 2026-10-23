module

public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Semantics.Exhaustification.Pointwise
public import Linglib.Data.Examples.BylininaNouwen2018
public import Mathlib.Data.Set.Card
public import Linglib.Semantics.Plurality.Algebra
public import Linglib.Fragments.English.PolarityItems
public import Linglib.Semantics.Polarity.Licensing

/-!
# Bylinina and Nouwen (2018): On *zero* and semantic plurality

This file formalizes the argument of Bylinina and Nouwen that *zero* is a numeral, not a negative
quantifier like *no*, and that its semantics needs an empty plurality. A numeral contributes a
cardinality, `∃x[#x = n ∧ A(x) ∧ B(x)]`, with an at least reading ((20)–(28)). With Link's
pluralization `*` ((29)), which excludes the sum of the empty set, *zero A B* is a contradiction
((36)); with the full lattice `×` ((30)), which has the empty plurality `⊥`, it is a tautology
((37), (39)), and exhaustifying it against the higher numerals gives *no A B* ((40)).

The polarity of *zero* follows from the split between the two meanings. Weak negative polarity
items need their environment non-trivially downward entailing, downward and not upward entailing,
in the meaning below the exhaustivity operator, and strong items in the meaning above it as well
((53)). Below the operator *zero A B* is a tautology, downward and upward entailing at once, so
*zero* licenses neither kind of item ((54)), while *few* licenses weak items only ((48)) and *no*
both. An analysis with a basic exactly meaning has no such split: Kennedy's degree quantifier
*zero*, `λP. max(P) = 0`, is *no A B* under `×` ((73)) and never true under `*` ((72)), and as *no*
it licenses both kinds of item (Section 6.3).

The empty plurality is needed elsewhere: under `×` a downward monotone degree quantifier such as
*fewer than ten* is downward monotone in its scope, under `*` it is not ((65), (66)). On scope the
two analyses agree (Section 6.2): exhaustifying the lower bound at a site and raising Kennedy's
quantifier to that site give the same reading, so the split-scope reading (77b) of *every student
read zero books*, which the sentence lacks ((78)), is blocked only for the degree quantifier, by
the Heim-Kennedy generalization ((80)).

## Main results

* `exhAgainst_zero_iff_no`, `zero_mem_countDegrees`: exhaustified *zero* is *no*, and the
  unexhaustified *zero* is a tautology.
* `not_licenses_zero`, `rows_predicted`: *zero* licenses no polarity item, *few* weak ones only
  and *no* both, as the paper's judgments have it.
* `kennedyZero_eq_nobody`: Kennedy's *zero* is the context of *no*.
* `antitone_maxIn_countDegrees`, `not_antitone_maxIn_countDegrees_sdiff`: *fewer than ten* is
  downward monotone with `×` and not with `*`.
* `countDegrees_plural_eq_Iic_comp`: a count's measured degree property is that of its
  pluralities under `×`.

## Implementation notes

* Pluralities are the finite sets of atoms, and `plural Z` is `Mereology.FullAlgClosure` of
  the singletons of `Z`, the full lattice `×Z`; without the empty sum it is Link's `*Z`,
  `Mereology.AlgClosure` of them (`plural_sdiff_empty`). A distributive predicate `B` holds of a
  plurality that is in `plural B`.
* Degrees are natural numbers; Kennedy's numeral is `Degree.MaxIn {n}` and its two scopes are
  `Degree.LowScope` and `Degree.HighScope`. Exhaustification against the higher numerals is
  `Exhaustification.exhAgainst (· < ·)`.
* Licensing is the library's: *zero* is a scalar `PolarityItem.Licenser`, and every item
  needs the meaning below the exhaustivity operator non-trivially downward entailing. For strong
  items the library asks Zwarts's anti-additivity of the meaning above it where (53) asks for
  non-trivial downward entailment; *zero* fails the first condition, so the two agree on it.

## TODO

The tag-question and neg-inversion contrasts (Section 2), the existential operator `E` for bare
plurals ((58)), plural definites with `⊥` ((60)–(64)), and the stipulation `max(∅) = 0` that would
let the de-Fregean analysis do without `⊥` (Section 6.1) are not formalized.

## References

* [bylinina-nouwen-2018]
* [link-1983]
* [gajewski-2011]
* [lahiri-1998]
* [kennedy-2015]
* [heim-2000]
-/

@[expose] public section
namespace BylininaNouwen2018

open Degree Exhaustification Quantifier Quantifier.GQ Set Mereology

variable {α : Type*} [DecidableEq α]

/-! ### Pluralities and numerals -/

/-- The pluralities of members of `Z`, the full closure `×Z` of its singletons ((30)), are the sums
`⊔X` of the subsets `X ⊆ Z`, the empty sum `⊥` among them. -/
def plural (Z : Set α) : Set (Finset α) := {x | FullAlgClosure (· ∈ ({·} : α → Finset α) '' Z) x}

@[simp] theorem mem_plural {Z : Set α} {x : Finset α} : x ∈ plural Z ↔ ↑x ⊆ Z :=
  fullAlgClosure_image_singleton Z x

/-- Without the empty sum `×Z` is Link's `*Z` ((29)). -/
theorem plural_sdiff_empty (Z : Set α) :
    plural Z \ {∅} = {x | AlgClosure (· ∈ ({·} : α → Finset α) '' Z) x} := by
  ext x
  simp only [mem_sdiff, mem_plural, mem_singleton_iff, mem_ofPred_eq, algClosure_image_singleton,
    Finset.nonempty_iff_ne_empty]
  exact and_comm

theorem plural_inter (A B : Set α) : plural A ∩ plural B = plural (A ∩ B) := by
  ext
  simp [subset_inter_iff]

/-- The degree property `λi. ∃x[#x = i ∧ A(x) ∧ C(x)]` of the pluralities of members of `A` that
are `C`, which a numeral `n` holds of at its lower bound ((27)) and Kennedy's numeral quantifies
over ((71)). -/
def countDegrees (A : Set α) (C : Set (Finset α)) : Set ℕ := Finset.card '' (plural A ∩ C)

/-- With a distributive predicate the degree property is a lower set, so the numeral has an at
least reading ((20), (22)). -/
theorem isLowerSet_countDegrees_plural (A B : Set α) : IsLowerSet (countDegrees A (plural B)) := by
  rw [countDegrees, plural_inter]
  rintro d e hed ⟨x, hx, rfl⟩
  obtain ⟨y, hyx, rfl⟩ := Finset.exists_subset_card_eq hed
  exact ⟨y, mem_plural.2 ((Finset.coe_subset.2 hyx).trans (mem_plural.1 hx)), rfl⟩

theorem countDegrees_singleton {A : Set α} {s : Finset α} (hs : ↑s ⊆ A) :
    countDegrees A {s} = {s.card} := by
  rw [countDegrees, inter_eq_right.2 (singleton_subset_iff.2 (mem_plural.2 hs)), image_singleton]

/-- With `A ∩ B` finite, the degree property under `×` is `{0, …, n}` for `n` its cardinality (73).
-/
theorem countDegrees_plural_eq_Iic {A B : Set α} (h : (A ∩ B).Finite) :
    countDegrees A (plural B) = Iic (A ∩ B).ncard := by
  rw [countDegrees, plural_inter]
  exact card_image_fullAlgClosure h

/-! ### *Zero*

Under `*` the at least *zero* is a contradiction and under `×` a tautology; exhaustification
against the higher numerals turns the tautology into *no*. -/

/-- Under `*`, *zero A B* is a contradiction ((36)). -/
theorem zero_notMem_countDegrees_sdiff (A B : Set α) :
    0 ∉ countDegrees A (plural B \ {∅}) :=
  fun ⟨_, ⟨_, _, hne⟩, hx⟩ ↦ hne (Finset.card_eq_zero.1 hx)

/-- Under `×`, *zero A B* is a tautology ((37), (39)). -/
theorem zero_mem_countDegrees (A B : Set α) : 0 ∈ countDegrees A (plural B) :=
  ⟨∅, ⟨mem_plural.2 (by simp), mem_plural.2 (by simp)⟩, Finset.card_empty⟩

theorem maxIn_singleton_iff_exhAgainst {D : Type*} [LinearOrder D] {P : Set D} {n : D} :
    MaxIn {n} P ↔ exhAgainst (· < ·) (· ∈ P) n :=
  maxIn_singleton.trans <| and_congr_right' ⟨fun h _ hm hmP ↦ (h hmP).not_gt hm,
    fun h m hmP ↦ not_lt.1 fun hm ↦ h m hm hmP⟩

/-- Under `×`, Kennedy's *zero A B* is *no A B* ((73)). -/
theorem maxIn_zero_countDegrees_iff {A B : Set α} :
    MaxIn {0} (countDegrees A (plural B)) ↔ GQ.no A B := by
  refine maxIn_singleton.trans ⟨fun h a ha hb ↦ ?_, fun h ↦ ⟨zero_mem_countDegrees A B, ?_⟩⟩
  · have : 1 ≤ 0 := h.2 ⟨{a}, ⟨mem_plural.2 (Finset.coe_singleton a ▸ singleton_subset_iff.2 ha),
      mem_plural.2 (Finset.coe_singleton a ▸ singleton_subset_iff.2 hb)⟩, Finset.card_singleton a⟩
    omega
  · rintro _ ⟨x, ⟨hA, hB⟩, rfl⟩
    exact Nat.le_zero.2 <| Finset.card_eq_zero.2 <| Finset.eq_empty_of_forall_notMem
      fun a hx ↦ h a (mem_plural.1 hA hx) (mem_plural.1 hB hx)

/-- Under `*`, Kennedy's *zero A B* is never true ((72)), since the degree property lacks `0`. -/
theorem not_maxIn_zero_countDegrees_sdiff (A B : Set α) :
    ¬ MaxIn {0} (countDegrees A (plural B \ {∅})) :=
  fun h ↦ zero_notMem_countDegrees_sdiff A B (maxIn_singleton.1 h).1

/-- Exhaustified *zero A B* is *no A B* ((40)). -/
theorem exhAgainst_zero_iff_no {A B : Set α} :
    exhAgainst (· < ·) (· ∈ countDegrees A (plural B)) 0 ↔ GQ.no A B :=
  maxIn_singleton_iff_exhAgainst.symm.trans maxIn_zero_countDegrees_iff

/-! ### Negative polarity items

*Zero* is a scalar licenser, the at least numeral below the exhaustivity operator and the numeral
exhaustified against the higher numerals above it, so the library's licensing applies to it as
stated in (53). -/

section Polarity

open PolarityItem (LicensingContext NonemptyPredicate)
open PolarityItem.LicensingContext
open scoped Classical

/-- *Zero* NP over a restrictor, the at least numeral and its exhaustification against the higher
numerals ((39), (40)). -/
def zero : PolarityItem.Licenser :=
  .scalar ⟨⟨NonemptyPredicate, fun p ↦ p.ι → Prop, fun _ ↦ Prop,
      fun p B ↦ 0 ∈ countDegrees p.A (plural B)⟩,
    fun p B ↦ exhAgainst (· < ·) (· ∈ countDegrees p.A (plural B)) 0⟩

/-- Above the exhaustivity operator *zero* is *no*, non-trivially downward entailing ((54a)). -/
theorem exhaustified_zero : zero.exhaustified = nobody.licenser := by
  simp only [zero, licenser, PolarityItem.Licenser.exhaustified]
  congr
  funext p B
  exact propext exhAgainst_zero_iff_no

/-- Below it *zero* is a tautology, downward and upward entailing at once ((54b)). -/
theorem isStrawsonUE_zero : zero.IsStrawsonUE :=
  fun p _ B _ _ ↦ zero_mem_countDegrees p.A B

/-- So *zero* licenses no negative polarity item, weak or strong. -/
@[simp] theorem not_licenses_zero (e : PolarityItem) : ¬ zero.Licenses e := by
  rintro (⟨_, _, h⟩ | ⟨h, _⟩ | ⟨h, _⟩)
  exacts [h.weak.2 isStrawsonUE_zero, h.elim, h.elim]

instance : DecidablePred zero.Licenses := fun e ↦ isFalse (not_licenses_zero e)

/-- Kennedy's *zero*, with its exactly meaning basic and so no exhaustivity operator to split its
meaning. -/
def kennedyZero : PolarityItem.Licenser :=
  .classical ⟨NonemptyPredicate, fun p ↦ p.ι → Prop, fun _ ↦ Prop,
    fun p B ↦ MaxIn {0} (countDegrees p.A (plural B))⟩

/-- Kennedy's *zero* is *no* ((73)), so it licenses what *no* licenses, strong items included,
against (13), (15) and (16) (Section 6.3). -/
theorem kennedyZero_eq_nobody : kennedyZero = nobody.licenser := by
  simp only [kennedyZero, licenser]
  congr
  funext p B
  exact propext maxIn_zero_countDegrees_iff

/-- The paper's licensers. -/
inductive Licenser
  | no | few | zero
  deriving DecidableEq, Repr

/-- The library's operator for each licenser. -/
noncomputable def Licenser.denote : Licenser → PolarityItem.Licenser
  | .no => LicensingContext.nobody.licenser
  | .few => LicensingContext.few.licenser
  | .zero => BylininaNouwen2018.zero

instance (L : Licenser) : DecidablePred L.denote.Licenses := by
  cases L <;> dsimp only [Licenser.denote] <;> infer_instance

/-- A sentence of the paper records its licenser, its polarity item as an entry of the English
fragment, and the judgment. -/
structure Row where
  licenser : Licenser
  item : PolarityItem
  judgment : Judgment

/-- A sentence gives a row for each of its polarity items, as entries of the English fragment. -/
def Row.ofDatum (ex : Datum) : List Row :=
  match ex.parse? "licenser"
      ([("no", .no), ("few", .few), ("zero", .zero)] :
        List (String × BylininaNouwen2018.Licenser)) with
  | some L => (ex.features "npi").filterMap fun npi ↦
      ((List.lookup npi [("in years", English.PolarityItems.inYears),
        ("ever", English.PolarityItems.ever), ("anything", English.PolarityItems.any),
        ("any", English.PolarityItems.any)]).map fun e ↦ ⟨L, e, ex.judgment⟩)
  | none => []

def rows : List Row := Examples.all.flatMap Row.ofDatum

/-- Every judgment is the library's verdict, a sentence being acceptable exactly when its licenser
licenses its item. -/
theorem rows_predicted :
    ∀ r ∈ rows, (r.judgment = .acceptable ↔ r.licenser.denote.Licenses r.item) := by
  decide

end Polarity

/-! ### Downward monotone degree quantifiers

A degree quantifier at a lower set, *fewer than ten* or *at most ten*, is downward monotone in its
scope under `×`, since `0` keeps the degree property nonempty, and not under `*` ((65), (66)). -/

theorem antitone_maxIn_countDegrees {U : Set ℕ} (hU : IsLowerSet U) {A : Set α} (hA : A.Finite) :
    Antitone fun B ↦ MaxIn U (countDegrees A (plural B)) := fun _ _ hB h ↦ by
  dsimp only at h ⊢
  rw [countDegrees_plural_eq_Iic (hA.inter_of_left _), maxIn_Iic] at h ⊢
  exact hU (ncard_le_ncard (inter_subset_inter_right A hB) (hA.inter_of_left _)) h

/-- Under `*`, *fewer than ten students passed* is false when no student passed. -/
theorem not_antitone_maxIn_countDegrees_sdiff :
    ¬ Antitone fun B : Set Unit ↦ MaxIn (Iio 10) (countDegrees univ (plural B \ {∅})) := by
  intro h
  obtain ⟨_, -, ⟨x, ⟨-, hx, hne⟩, -⟩, -⟩ := h (empty_subset univ) ⟨1, by decide,
    ⟨{()}, ⟨mem_plural.2 (subset_univ _), mem_plural.2 (subset_univ _), by simp⟩, rfl⟩,
    fun _ ⟨x, _, hx⟩ ↦ hx ▸ Finset.card_le_univ x⟩
  exact hne (Finset.eq_empty_of_forall_notMem fun a ha ↦ mem_plural.1 hx ha)

/-! ### Scope

Exhaustifying the lower bound at a site and raising Kennedy's quantifier to that site give the same
reading ((75), (76)), whatever degree property the scope abstracts, so the analyses differ only in
the sites they reach. -/

section Scope

variable {ι : Type*} {Q : NP ι} {P : ι → Set ℕ} {n : ℕ}

theorem exhAgainst_iff_highScope :
    exhAgainst (· < ·) (fun m ↦ Q fun x ↦ m ∈ P x) n ↔ HighScope (MaxIn {n}) Q P :=
  maxIn_singleton_iff_exhAgainst.symm

theorem exhAgainst_iff_lowScope :
    (Q fun x ↦ exhAgainst (· < ·) (· ∈ P x) n) ↔ LowScope (MaxIn {n}) Q P := by
  simp only [LowScope, maxIn_singleton_iff_exhAgainst]

end Scope

/-- A count's measured degree property is that of its full pluralities. With finitely many members
of each `A ∩ B i`, the pluralities of `A` that are `B i` have the degrees `Iic` of their number,
so `Degree.LowScope` and `Degree.HighScope` at `Iic ∘` the count are the readings of the plural
model. -/
theorem countDegrees_plural_eq_Iic_comp {ι : Type*} {A : Set α} {B : ι → Set α}
    (h : ∀ i, (A ∩ B i).Finite) :
    (fun i ↦ countDegrees A (plural (B i))) = Iic ∘ fun i ↦ (A ∩ B i).ncard :=
  funext fun i ↦ countDegrees_plural_eq_Iic (h i)

/-- Over *every student*, the split-scope reading (77b) is true and the reading (77a) false when one
student read none and another four (78). -/
theorem highScope_every_not_lowScope :
    HighScope (MaxIn {0}) (every fun _ ↦ True) (Iic ∘ fun i : Fin 2 ↦ 4 * (i : ℕ)) ∧
      ¬ LowScope (MaxIn {0}) (every fun _ ↦ True) (Iic ∘ fun i : Fin 2 ↦ 4 * (i : ℕ)) :=
  ⟨highScope_maxIn_singleton_every.2 ⟨fun _ _ ↦ Nat.zero_le _, fun _ hb ↦ hb ⟨0, trivial, rfl⟩⟩,
    fun h ↦ absurd (lowScope_maxIn.1 h 1 trivial) (by simp)⟩

end BylininaNouwen2018
