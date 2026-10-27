module

public import Linglib.Semantics.Mereology
public import Linglib.Syntax.Minimalist.ExtendedProjection
public import Mathlib.Data.Finset.Card

/-!
# Borer (2005): In Name Only

This file formalizes the count structure of [borer-2005]. Noun stems denote cumulative stuff and
are mass by default; the mass/count distinction is not lexical but structural, with two open
values in the nominal spine assigned range by the functional lexicon. The classifier head ⟨e⟩div
divides the stuff, and plural inflection is the head feature that assigns it range, so a bare
plural is divided but not counted (27). The quantity head ⟨e⟩# counts the divisions or measures
undivided mass, *much salt* projecting no classifier phrase (28). Cardinals other than *one* and
the plural-taking quantifiers are pure counters, which is why *two meat* and *two boy* fail (29),
while *a*, *one*, *every* and *each* are portmanteau morphemes assigning range to both open
values (30), as are the cardinals of Hungarian, Turkish and Armenian, which never co-occur with
plural inflection (36) to (38); *all* takes a mass or a plural restriction and, dividing nothing,
has no count reading on a bare stem (35). Each open value takes range once, so *every boys* and
*several a boy* are out, and the distribution of the determiner classes of (20) over bare stems
and plurals follows. Division creates no individuals: a reticule may have no complete cell, as
in *zero apples* and *0.5 apples*, and individuals emerge only when a counter selects a reticule
with the requisite number of cells, so *more than three circles* presupposes circles where bare
*circles* does not.

## Main definitions

* `Determiner`: what a range assigner does at ⟨e⟩#, counting, measuring or either, and whether it
  also assigns range to ⟨e⟩div.
* `Nominal`: a nominal by its determiner, if any, and its plural inflection, with `Divided` and
  `WellFormed`, the two principles of range assignment.
* `IsDivision`, `count`: a reticule over stuff, a finset of cells, and the number of its complete
  cells.
* `status`: the mereological type a nominal spine composes bottom-up.

## Implementation notes

The two open values ⟨e⟩div and ⟨e⟩# are the heads `Q` and `Num` of the substrate's nominal
sequence. The existential closure and generic binding of ⟨e⟩d, the Hebrew and Chinese systems
and the measure phrases of the later chapters are not formalized.

## References

* [borer-2005]
* [krifka-1998]
* [chierchia-1998]
-/

@[expose] public section

namespace Borer2005

open Mereology Minimalist

/-! ### Range assignment to the two open values -/

/-- The range a determiner assigns to ⟨e⟩#, which is a count over the cells of a division, a
measure over undivided mass, or either. -/
inductive Quantity
  | count
  | measure
  | either
  deriving DecidableEq, Repr

/-- A range assigner from the functional lexicon, by the quantity it assigns to ⟨e⟩# and whether
it also assigns range to ⟨e⟩div, as the portmanteau morphemes of (30) do. -/
structure Determiner where
  quantity : Quantity
  divides : Bool
  deriving DecidableEq, Repr

/-- *much* and *little* measure undivided mass (28). -/
def much : Determiner := ⟨.measure, false⟩

/-- Cardinals other than *one*, *zero* included, and the plural-taking quantifiers *several*,
*many*, *few*, *a few* and *both* are pure counters over a division established before them
(30b). -/
def cardinal : Determiner := ⟨.count, false⟩

/-- *a* and *one* divide and count at once, the dividing and counting functions being one for
singulars (30a). -/
def indefArticle : Determiner := ⟨.count, true⟩

/-- *every* and *each* are portmanteau dividers and counters over a bare stem (30c). -/
def every : Determiner := ⟨.count, true⟩

/-- The cardinals of Hungarian, Turkish and Armenian divide as well as count (38a). -/
def hungarianCardinal : Determiner := ⟨.count, true⟩

/-- *all*, *a lot of* and *most* take a mass or a plural restriction and divide nothing (35). -/
def all : Determiner := ⟨.either, false⟩

/-- A nominal, by its determiner, if any, and whether it carries plural inflection, the head
feature that assigns range to ⟨e⟩div. -/
structure Nominal where
  det : Option Determiner
  plural : Bool
  deriving DecidableEq, Repr

namespace Nominal

variable (n : Nominal)

/-- ⟨e⟩div has range, from plural inflection or from a dividing determiner, so the nominal is
count; a bare stem is mass. -/
def Divided : Prop := n.plural = true ∨ ∃ d ∈ n.det, d.divides = true

/-- The two principles of range assignment. No open value takes range twice, so plural inflection
and a divider exclude each other, and a range assigner to ⟨e⟩# finds the restriction it needs, a
counter a division and a measure undivided mass. -/
def WellFormed : Prop :=
  ¬ (n.plural = true ∧ ∃ d ∈ n.det, d.divides = true) ∧
    ∀ d ∈ n.det, (d.quantity = .count → n.Divided) ∧ (d.quantity = .measure → ¬ n.Divided)

instance : Decidable n.Divided := inferInstanceAs (Decidable (_ ∨ _))

instance : Decidable n.WellFormed := inferInstanceAs (Decidable (_ ∧ _))

end Nominal

/-- A pure counter needs the division that plural inflection supplies: *three boys* and *several
meats* but not *two meat* or *two boy* (29). -/
theorem wellFormed_counter_iff {d : Determiner} (hq : d.quantity = .count)
    (hd : d.divides = false) (p : Bool) : Nominal.WellFormed ⟨some d, p⟩ ↔ p = true := by
  cases p <;> simp [Nominal.WellFormed, Nominal.Divided, hq, hd]

/-- A divider never co-occurs with plural inflection, so neither *a boys* nor a Hungarian cardinal
with a plural is possible (38). -/
theorem not_wellFormed_of_divides {d : Determiner} (hd : d.divides = true) :
    ¬ Nominal.WellFormed ⟨some d, true⟩ := fun h ↦ h.1 ⟨rfl, d, rfl, hd⟩

-- (30a)
theorem wellFormed_divider {d : Determiner} (hq : d.quantity = .count) (hd : d.divides = true) :
    Nominal.WellFormed ⟨some d, false⟩ := by
  simp [Nominal.WellFormed, Nominal.Divided, hq, hd]

/-- A measure takes undivided mass alone: *much salt* but not *much boys* (28). -/
theorem wellFormed_measure_iff {d : Determiner} (hq : d.quantity = .measure)
    (hd : d.divides = false) (p : Bool) : Nominal.WellFormed ⟨some d, p⟩ ↔ p = false := by
  cases p <;> simp [Nominal.WellFormed, Nominal.Divided, hq, hd]

/-- A determiner indifferent to quantity takes mass and plurals alike and divides only a plural
(35). -/
theorem wellFormed_neutral {d : Determiner} (hq : d.quantity = .either) (hd : d.divides = false)
    (p : Bool) : Nominal.WellFormed ⟨some d, p⟩ ∧ (Nominal.Divided ⟨some d, p⟩ ↔ p = true) := by
  cases p <;> simp [Nominal.WellFormed, Nominal.Divided, hq, hd]

-- (20)
theorem determiner_classes :
    (Nominal.WellFormed ⟨some much, false⟩ ∧ ¬ Nominal.WellFormed ⟨some much, true⟩) ∧
      (¬ Nominal.WellFormed ⟨some cardinal, false⟩ ∧ Nominal.WellFormed ⟨some cardinal, true⟩) ∧
      (Nominal.WellFormed ⟨some indefArticle, false⟩ ∧
        ¬ Nominal.WellFormed ⟨some indefArticle, true⟩) ∧
      (Nominal.WellFormed ⟨some every, false⟩ ∧ ¬ Nominal.WellFormed ⟨some every, true⟩) ∧
      (Nominal.WellFormed ⟨some all, false⟩ ∧ Nominal.WellFormed ⟨some all, true⟩) ∧
      (Nominal.WellFormed ⟨some hungarianCardinal, false⟩ ∧
        ¬ Nominal.WellFormed ⟨some hungarianCardinal, true⟩) := by
  decide

/-! ### Dividing without individuating

Assigning range to ⟨e⟩div superimposes reticules on a mass denotation; a reticule carves cells,
none of which need be a canonical unit, and the counter at ⟨e⟩# selects among the reticules one
with the number of complete cells it requires. -/

variable {α : Type*} {P : α → Prop}

/-- A finset of cells is a division of the `P`-stuff when every cell is carved from it. -/
def IsDivision (P : α → Prop) (d : Finset α) : Prop := ∀ x ∈ d, P x

/-- Divided stuff is still stuff: the sum of the cells of a cumulative root satisfies the root,
apples plus apples being apples, the cumulativity bare plurals share with mass nouns. -/
theorem sup'_mem [SemilatticeSup α] (hCum : CUM P) {d : Finset α} (hne : d.Nonempty)
    (hd : IsDivision P d) : P (d.sup' hne id) :=
  hCum.finsetSup'_mem hne hd

section Units

variable (unit : α → Prop)

/-- Plural marking presupposes no singulars: whenever the stuff has a noncanonical portion, some
nonempty division contains no unit, the reticules behind *zero apples* and *0.5 apples*. -/
theorem exists_division_without_units (h : ∃ x, P x ∧ ¬ unit x) :
    ∃ d : Finset α, IsDivision P d ∧ d.Nonempty ∧ ∀ x ∈ d, ¬ unit x :=
  let ⟨x, hP, hu⟩ := h
  ⟨{x}, by simpa [IsDivision] using hP, Finset.singleton_nonempty x, by simpa using hu⟩

variable [DecidablePred unit]

/-- The number of complete cells of a division, those that are canonical units, by which a
counter at ⟨e⟩# selects a reticule. -/
def count (d : Finset α) : ℕ := (d.filter unit).card

/-- Individuals emerge at ⟨e⟩#: a division with a positive count contains a canonical unit of
the stuff, so *more than three circles* cannot be true without individual circles, though bare
*circles* can. -/
theorem exists_unit_of_count_pos {d : Finset α} (hd : IsDivision P d) (h : 0 < count unit d) :
    ∃ x, unit x ∧ P x :=
  let ⟨x, hx⟩ := Finset.card_pos.1 h
  ⟨x, (Finset.mem_filter.1 hx).2, hd x (Finset.mem_filter.1 hx).1⟩

end Units

/-! ### The nominal spine -/

/-- The mereological type of a nominal denotation along the spine, which is cumulative stuff,
divided stuff, or a quantity. -/
inductive Status
  | stuff
  | divided
  | quantity
  deriving DecidableEq, Repr

/-- The semantically active heads are ⟨e⟩div, the head `Q`, which divides stuff, and ⟨e⟩#, the
head `Num`, which counts a division or measures undivided stuff; the other heads are
transparent, and nothing divides a quantity. -/
def steps : Cat → Status → Option Status
  | .Q, .stuff => some .divided
  | .Q, _ => none
  | .Num, .quantity => none
  | .Num, _ => some .quantity
  | _, s => some s

/-- The type of a spine's denotation, composed bottom-up from cumulative stuff, or `none` when a
head has no well-typed input. -/
def status (spine : List Cat) : Option Status :=
  spine.foldl (fun s c ↦ s.bind (steps c)) (some .stuff)

/-- Dividing feeds counting and nothing divides a quantity, so the only well-typed order puts the
dividing head below the quantity head, the order (27) draws. -/
theorem q_below_num : status [.N, .n, .Q, .Num] = some .quantity ∧
    status [.N, .n, .Num, .Q] = none := by
  decide

-- (28)
theorem quantified_mass : status [.N, .n, .Num] = some .quantity := by decide

-- (27)
theorem status_truncations :
    status [.N, .n] = some .stuff ∧ status [.N, .n, .Q] = some .divided := by
  decide

theorem asymmRel_Q_Num : AsymmRel Cat.ExtendsTo .Q .Num := by decide +kernel

end Borer2005
