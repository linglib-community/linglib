module

public import Studies.Bobaljik2012
public import Linglib.Morphology.Exponence.Containment.Contiguity
public import Linglib.Syntax.Person.Features
public import Linglib.Syntax.Agreement.PersonCaseConstraint
public import Mathlib.Tactic.TFAE

/-!
# Graf (2019): Monotonicity as an Effective Theory of Morphosyntactic Variation

Graf explains typological gaps in adjectival gradation (*ABA), person-pronoun syncretism and the
Person Case Constraint by two components: a fixed base hierarchy of prominence relations, and the
requirement that the map from it to surface forms be feasibly monotonic, his definition (6). Over
a linear hierarchy feasible monotonicity coincides with contiguity, Elsewhere-generability and
Superset-spellability, so the effective theory and the two insertion mechanisms are one
constraint. A Person Case Constraint is a monotone map from the reduced dual person hierarchy
(27) to the truth values.

## Main definitions

* `FeasiblyMonotone`: definition (6), some monotone score identifies the cells the map
  identifies.

## Implementation notes

The person hierarchy is `Person.prominence`, Zwicky's order 1 > 2 > 3, which on the three persons
is the inclusion order of Nevins's privative bundles, as the paper observes
(`Person.prominence_le_iff_subset`). Table 2's paradigms index the persons ascending from the
first, the dual order, equivalent for feasible monotonicity by the paper's footnote 1. A
combination of indirect and direct object is a scenario (`Clause.Scenario`), the diagonal
excluded as the paper does, so the reduced dual hierarchy (27) is the order on scenarios read on
the person hierarchy and the naive one (23) the product order. A constraint is a map from the six
combinations to the truth values; Table 4's constraints are those of Pancheva and Zubizarreta's
grammars.

## TODO

The case-layer hierarchy (13) and the Gender Case Constraint are partial orders whose maps
need a partial-order generalization of `Paradigm`: the ban (14) on multiple cross-level case
syncretisms and the nominative stem-allomorphy generalization (16) remain.

## References

* [graf-2019]
* [bobaljik-2012]
* [bobaljik-sauerland-2018]
* [harbour-2015]
* [zwicky-1977b]
* [caha-2009]
* [nevins-2007]
* [pancheva-zubizarreta-2018]
-/

@[expose] public section

namespace Graf2019

open Morphology Morphology.Exponence Morphology.Containment

/-! ### Feasible monotonicity -/

/-- A map is feasibly monotone, definition (6), if some monotone map to `ℕ` has the same
kernel. -/
def FeasiblyMonotone {ι F : Type*} [Preorder ι] (p : ι → F) : Prop :=
  ∃ g : ι → ℕ, Monotone g ∧ ∀ i j, p i = p j ↔ g i = g j

theorem isContiguous_iff_feasiblyMonotone {ι F : Type*} [LinearOrder ι]
    [LocallyFiniteOrderBot ι] (p : ι → F) : IsContiguous p ↔ FeasiblyMonotone p :=
  isContiguous_iff_exists_monotone p

/-! ### Four characterizations coincide over a linear hierarchy -/

/-- On a linear containment hierarchy, contiguity, feasible monotonicity (6), Elsewhere generability
([bobaljik-2012]) and Superset spellability ([caha-2009]) are equivalent. -/
theorem isContiguous_tfae {n : ℕ} {F : Type*} (p : Paradigm n F) :
    [IsContiguous p,
     FeasiblyMonotone p,
     ElsewhereGenerable p,
     SupersetSpellable p].TFAE := by
  tfae_have 1 ↔ 2 := isContiguous_iff_feasiblyMonotone p
  tfae_have 1 ↔ 3 := isContiguous_iff_generable p
  tfae_have 1 ↔ 4 := isContiguous_iff_spelloutGenerable p
  tfae_finish

/-! ### Table 1: adjectival gradation -/

/-- Every adjectival triple of [bobaljik-2012]'s Table 4.1 but the Basque doublet is feasibly
monotonic, as Table 1's attested rows AAA *smart* and ABB *good* are. -/
theorem feasiblyMonotone_of_ne_basque {r : CLDF.Wordlist.RootClasses Bobaljik2012.Wordlist.Cell}
    (hr : r ∈ Bobaljik2012.Wordlist.rootClasses) (hq : ¬ Bobaljik2012.Quantifier r)
    (hb : r.id ≠ Bobaljik2012.Wordlist.eus_good_on.roots.id) :
    FeasiblyMonotone (Bobaljik2012.rootPattern r) :=
  (isContiguous_iff_feasiblyMonotone _).1 ((Bobaljik2012.isContiguous_iff_ne_basque r hr hq).2 hb)

/-- No order on the forms makes *good, better, goodest* monotone, whatever the order of the
codomain, so the *ABA row is unattested. -/
theorem aba_not_feasiblyMonotone : ¬ FeasiblyMonotone Paradigm.aba := by
  rw [← isContiguous_iff_feasiblyMonotone]
  decide

/-! ### Table 2: person-pronoun syncretism

Section 3.1 runs the same hierarchy over person, `1 > 2 > 3`, against [harbour-2015]'s survey:
attested are 1|2|3 (Jarawa, Kiowa), 1|23 (Damin), and 12|3 (Winnebago), an AAB shape, while
13|2 is missing, as monotonicity predicts. -/

/-- Jarawa and Kiowa distinguish all three persons (1|2|3). -/
def personJarawa : Paradigm 3 ℕ := Paradigm.abc

/-- In Damin the second and third persons share a form (1|23). -/
def personDamin : Paradigm 3 ℕ := Paradigm.abb

/-- In Winnebago the first and second persons share a form (12|3), an AAB shape. -/
def personWinnebago : Paradigm 3 ℕ := Paradigm.aab

/-- The unattested partition 13|2 makes the first and third persons syncretic to the exclusion
of the second. -/
def personGap : Paradigm 3 ℕ := Paradigm.aba

/-- The attested person partitions are feasibly monotonic over `1 > 2 > 3`. -/
theorem person_attested_feasiblyMonotone :
    FeasiblyMonotone personJarawa ∧ FeasiblyMonotone personDamin ∧
      FeasiblyMonotone personWinnebago := by
  simp only [← isContiguous_iff_feasiblyMonotone]
  decide

/-- The missing partition is the non-monotonic one. -/
theorem personGap_not_feasiblyMonotone : ¬ FeasiblyMonotone personGap := by
  rw [← isContiguous_iff_feasiblyMonotone]
  decide

/-! ### The AAB division of labor

Monotonicity cannot exclude both ABA and AAB, and the paper welcomes this: AAB is attested in
person (Winnebago) though not in adjectival gradation, where its absence has to be stipulated,
for instance in terms of syntactic containment. -/

/-- AAB is feasibly monotonic. -/
theorem aab_feasiblyMonotone : FeasiblyMonotone Paradigm.aab := by
  rw [← isContiguous_iff_feasiblyMonotone]
  decide

/-- Under antihomophony, [bobaljik-2012]'s markedness condition and adjacency no vocabulary
realizes an AAB pattern, so the gradation-side exclusion is carried by the realization engine,
not by monotonicity. -/
theorem aab_not_realizable {v : RuleSet (SpanRule 3 ℕ)} {a b : ℕ} (hAH : v.Antihomophonous)
    (hM : Markedness v) (hA : Adjacent v) (hab : a ≠ b) :
    realize v ≠ ![some a, some a, some b] := by
  intro h
  have h01 : realize v 0 = realize v 1 := by simp [h]
  have h2 : (realize v 2).isSome := by simp [h]
  have h12 := realize_const_of_markedness hAH hM hA h01 h2
  rw [h] at h12
  exact hab (by simpa using h12)

/-! ### Section 4: the Person Case Constraint as a monotone map -/

open Clause (Scenario)

/-- A clitic combination is a scenario of the indirect over the direct object on two distinct
persons of the tripartition. -/
def Combination : Type := {s : Scenario Person // s ∈ PCC.distinctPairs}

instance : Fintype Combination := inferInstanceAs (Fintype {s // s ∈ PCC.distinctPairs})

instance : DecidableEq Combination := inferInstanceAs (DecidableEq {s // s ∈ PCC.distinctPairs})

/-- The reduced dual person hierarchy (27) orders combinations as scenarios on the person
hierarchy, the product of the hierarchy with its dual, so a combination is below another when its
indirect object is at most as prominent and its direct object at least as prominent, `1, 3` being
the top and `3, 1` the bottom. -/
instance : PartialOrder Combination :=
  PartialOrder.lift (fun p ↦ p.1.map Person.prominence) (by decide)

instance : DecidableLE Combination := fun p q ↦
  inferInstanceAs (Decidable (p.1.map Person.prominence ≤ q.1.map Person.prominence))

/-- The combinations under the naive reduced hierarchy (23), which the paper rejects. -/
def NaiveCombination : Type := Combination

instance : Fintype NaiveCombination := inferInstanceAs (Fintype Combination)

/-- The naive hierarchy is the product of the person hierarchy with itself. -/
instance : PartialOrder NaiveCombination :=
  PartialOrder.lift (fun p : Combination ↦ (p.1.high.prominence, p.1.low.prominence)) (by decide)

instance : DecidableLE NaiveCombination := fun p q ↦
  inferInstanceAs (Decidable ((p.1.high.prominence, p.1.low.prominence) ≤
    ((q : Combination).1.high.prominence, (q : Combination).1.low.prominence)))

/-- A Person Case Constraint is a map from the combinations to the truth values, true on the
well-formed ones, Table 4's cells. -/
abbrev PCC := Combination → Bool

theorem card_pcc : Fintype.card PCC = 64 := by decide

/-- `PCC.ofGrammar g` is the constraint a grammar of the P-Constraint family predicts. -/
def PCC.ofGrammar (g : _root_.PCC.Grammar) : PCC := fun p ↦ decide (_root_.PCC.IsLicit g p.1)

/-- `sPCC` is the Strong constraint (19a). -/
def sPCC : PCC := .ofGrammar _root_.PCC.strongGrammar

/-- `uPCC` is the Ultrastrong constraint (19b). -/
def uPCC : PCC := .ofGrammar _root_.PCC.ultraStrongGrammar

/-- `wPCC` is the Weak constraint (19c). -/
def wPCC : PCC := .ofGrammar _root_.PCC.weakGrammar

/-- `mPCC` is the Me-first constraint (19d). -/
def mPCC : PCC := .ofGrammar _root_.PCC.meFirstGrammar

/-- Table 4 gives the strong, ultrastrong, weak and me-first PCCs as stated in (19). -/
theorem table4 :
    (∀ p, sPCC p = true ↔ p.1.low = .third) ∧
      (∀ p, uPCC p = true ↔ p.1.low.prominence < p.1.high.prominence) ∧
      (∀ p, wPCC p = true ↔ (p.1.high = .third → p.1.low = .third)) ∧
      ∀ p, mPCC p = true ↔ (p.1.high ≠ .first → p.1.low ≠ .first) := by
  decide

/-- `fPCC` allows free combination, as in German. -/
def fPCC : PCC := fun _ ↦ true

/-- `iPCC` is indiscriminate, no clitics combining, as in Cairene Arabic. -/
def iPCC : PCC := fun _ ↦ false

/-- In Choctaw as reanalyzed in (31) only a first-person indirect object combines. -/
def cPCC : PCC := fun p ↦ p.1.high = .first

/-- In the first constraint of (32) only `1, 3` is licit. -/
def only13 : PCC := fun p ↦ p.1 = ⟨.first, .third⟩

/-- In the second constraint of (32) only `3, 1` is illicit. -/
def allBut31 : PCC := fun p ↦ p.1 ≠ ⟨.third, .first⟩

/-- The constraints with an attested pattern are Table 4's, the free and indiscriminate ones of
(28), and Choctaw's. -/
def attested : List PCC := [sPCC, uPCC, wPCC, mPCC, fPCC, iPCC, cPCC]

/-- Exactly nine constraints are monotone over the hierarchy (27), the seven attested ones and
the two of (32) (section 4.3) (Table 4). -/
theorem monotone_iff :
    ∀ c : PCC, Monotone c ↔ c ∈ attested ++ [only13, allBut31] := by
  decide

/-- The two monotone constraints without an attested pattern are exactly those whose class of
well-formed or of ill-formed combinations is a singleton. -/
theorem unattested_singleton_class :
    ∀ c : PCC, Monotone c →
      (c ∉ attested ↔ (Finset.univ.filter fun p ↦ c p = true).card = 1 ∨
        (Finset.univ.filter fun p ↦ c p = false).card = 1) := by
  decide

/-- Over the naive hierarchy (23) the ultrastrong constraint is neither monotone nor antitone, while
the weak one is monotone (25). -/
theorem uPCC_not_monotone_naive :
    ¬ Monotone (α := NaiveCombination) uPCC ∧ ¬ Antitone (α := NaiveCombination) uPCC ∧
      Monotone (α := NaiveCombination) wPCC := by
  decide

end Graf2019
