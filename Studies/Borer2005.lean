module

public import Linglib.Data.Examples.Borer2005
public import Linglib.Languages.English.Determiners
public import Linglib.Syntax.Minimalist.ExtendedProjection
public import Mathlib.Order.Partition.Finpartition

/-!
# Borer (2005): In Name Only

For [borer-2005] the mass and count distinction is structural and not lexical. A noun stem denotes
stuff, and the nominal spine has two open values, ⟨e⟩DIV at the classifier head and ⟨e⟩# at the
quantity head, to which the functional lexicon assigns range. Plural inflection assigns range to
⟨e⟩DIV alone and so divides without counting; cardinals and the plural-taking quantifiers assign
range to ⟨e⟩# alone; *a*, *one*, *every*, *each* and the cardinals of Hungarian are portmanteau
morphemes that assign range to both. An open value takes range once, so
[two assigners to one value exclude each other](##not_wellFormed_pair_of_mem), and a counter
counts the cells of a division, of which an undivided stem has none: among the pure counters
[only *zero* takes a bare stem](##wellFormed_cardinal_iff). It follows that
[no determiner selects both singulars and plurals](##not_wellFormed_div_of_divided), and the
conditions [sort the judged nominals of the chapter](##wellFormed_iff_judgment). Dividing creates
no individuals: a portion that is no unit has [a reticule without a complete
cell](##exists_finpartition_filter_eq_empty), and individuals
[emerge only under a counter](##exists_pairwiseDisjoint_of_card_filter).

## Implementation notes

The open values ⟨e⟩DIV and ⟨e⟩# are the heads `Q` and `Num` of the substrate's nominal sequence,
and a range assigner is the set of heads whose value it assigns together with its row of the
typology of determiners. A nominal is the list of its range assigners, plural inflection among
them. A cardinal carries the number of complete cells it counts, which is what lets *zero*, a
counter, take undivided mass; the vague standards of *several*, *many* and *few* and the
fractional counts of the decimals are not represented. A reticule on a portion of stuff is a
`Finpartition` of it, a finite set of pairwise disjoint cells that sum to the portion. The
determiners the typology takes to be ambiguous (*some*, *any*, *no*) and the definite article,
the existential closure and generic binding of ⟨e⟩d, the Hebrew and Chinese systems and the
measure phrases of the later chapters are not formalized.

## References

* [borer-2005]
-/

@[expose] public section

namespace Borer2005

open Minimalist Finset Function

/-! ### Range assignment to the two open values -/

/-- (40): the quantity a range assigner gives ⟨e⟩#, the ±Count column of the typology of
determiners. -/
inductive Quantity
  /-- A cardinal, which selects the reticules with `n` complete cells. -/
  | cardinal (n : ℕ)
  /-- A counting quantifier, +Count. -/
  | count
  /-- A measure of undivided mass, −Count. -/
  | measure
  /-- Unspecified for ±Count. -/
  | unspecified
  deriving DecidableEq, Repr

namespace Quantity

/-- The quantity can be assigned over a division: every quantity but a measure, whose nominal
projects no classifier phrase. -/
def Counts : Quantity → Prop
  | measure => False
  | _ => True

/-- The quantity can be assigned over an undivided stem, which has no cells: a counter cannot,
unless it is the cardinal that counts none. -/
def Measures : Quantity → Prop
  | cardinal n => n = 0
  | count => False
  | _ => True

instance : DecidablePred Counts
  | cardinal _ | count | unspecified => isTrue trivial
  | measure => isFalse id

instance : DecidablePred Measures
  | cardinal n => inferInstanceAs (Decidable (n = 0))
  | count => isFalse id
  | measure | unspecified => isTrue trivial

end Quantity

/-- A range assigner, an f-morph or a head feature of the functional lexicon. -/
structure Assigner where
  /-- The heads whose open value it assigns range to. -/
  values : Finset Cat
  /-- The quantity it gives ⟨e⟩#. -/
  quantity : Quantity := .unspecified
  deriving DecidableEq

namespace Assigner

/-- (40d): the head feature ⟨div⟩, spelled out as plural inflection, assigns range to ⟨e⟩DIV
alone. -/
def div : Assigner := ⟨{.Q}, .unspecified⟩

/-- An assigner of range to ⟨e⟩# alone. -/
def pure (q : Quantity) : Assigner := ⟨{.Num}, q⟩

/-- (30a): a portmanteau morpheme, which assigns range to ⟨e⟩DIV and to ⟨e⟩#. -/
def portmanteau (q : Quantity) : Assigner := ⟨{.Q, .Num}, q⟩

end Assigner

/-- ⟨e⟩DIV has range, so that the nominal is count; a nominal that is not divided is mass. -/
def Divided (n : List Assigner) : Prop := ∃ a ∈ n, Cat.Q ∈ a.values

instance : DecidablePred Divided := fun n ↦ inferInstanceAs (Decidable (∃ a ∈ n, _))

/-- A nominal, the list of its range assigners, is well formed when range assignment succeeds. -/
@[mk_iff]
structure WellFormed (n : List Assigner) : Prop where
  /-- No open value takes range twice. -/
  pairwise_disjoint : n.Pairwise (Disjoint on Assigner.values)
  /-- Each quantity finds its restriction, a division or undivided mass. -/
  quantity : ∀ a ∈ n, if Divided n then a.quantity.Counts else a.quantity.Measures

instance : DecidablePred WellFormed := fun n ↦
  haveI : DecidableRel (Disjoint on Assigner.values) := fun a b ↦
    inferInstanceAs (Decidable (Disjoint a.values b.values))
  decidable_of_iff' _ (wellFormed_iff n)

variable {a b : Assigner} {c : Cat}

-- A determiner on a bare stem.
theorem wellFormed_singleton :
    WellFormed [a] ↔ if Cat.Q ∈ a.values then a.quantity.Counts else a.quantity.Measures := by
  simp [wellFormed_iff, Divided]

-- A determiner on a plural.
theorem wellFormed_div_cons :
    WellFormed [.div, a] ↔ Cat.Q ∉ a.values ∧ a.quantity.Counts := by
  simp [wellFormed_iff, Divided, Assigner.div, Quantity.Counts, onFun]

-- (34): an open value takes range once, so the two counters of *zero a cat* exclude each other.
theorem not_wellFormed_pair_of_mem (ha : c ∈ a.values) (hb : c ∈ b.values) :
    ¬ WellFormed [a, b] := fun h ↦
  Finset.disjoint_left.1 (List.rel_of_pairwise_cons h.pairwise_disjoint List.mem_cons_self) ha hb

/-- (29), (31): of the pure cardinals only *zero*, whose count the absence of divisions meets,
takes a bare stem; the others need the division that plural inflection supplies. -/
theorem wellFormed_cardinal_iff {k : ℕ} : WellFormed [.pure (.cardinal k)] ↔ k = 0 := by
  simp [wellFormed_singleton, Assigner.pure, Quantity.Measures]

-- (30b)
theorem wellFormed_div_cardinal (k : ℕ) : WellFormed [.div, .pure (.cardinal k)] := by
  simp [wellFormed_div_cons, Assigner.pure, Quantity.Counts]

/-- No determiner selects both singulars and plurals: one that divides a bare stem assigns range
to ⟨e⟩DIV, which plural inflection has assigned already, as with the cardinals of Hungarian
(38). -/
theorem not_wellFormed_div_of_divided (h : Divided [a]) : ¬ WellFormed [.div, a] := fun hw ↦
  (wellFormed_div_cons.1 hw).1 (by simpa [Divided] using h)

-- (35): a determiner unspecified for ±Count takes mass and plurals, and divides neither.
theorem wellFormed_unspecified :
    WellFormed [.pure .unspecified] ∧ WellFormed [.div, .pure .unspecified] ∧
      ¬ Divided [.pure .unspecified] := by
  decide

/-! ### The judged nominals -/

namespace Examples.Determiner

/-- (40), (38a): the range a determiner assigns. -/
def assigner : Examples.Determiner → Assigner
  | .much => .pure .measure
  | .two => .pure (.cardinal 2)
  | .three => .pure (.cardinal 3)
  | .zero => .pure (.cardinal 0)
  | .decimal | .several | .many | .aFew | .both => .pure .count
  | .a | .one | .egy => .portmanteau (.cardinal 1)
  | .ket => .portmanteau (.cardinal 2)
  | .every | .each | .minden => .portmanteau .count
  | .all => .pure .unspecified

end Examples.Determiner

/-- The range assigners of a row, plural inflection first. -/
def nominal (e : Datum) : List Assigner :=
  (if Examples.stem e = some .plural then [.div] else []) ++
    (Examples.determiners e).map (·.assigner)

/-- A row is acceptable exactly when its range assignment is well formed and, where the judgment
is of a singular reading, divides the stem. -/
theorem wellFormed_iff_judgment :
    ∀ e ∈ Examples.all, (WellFormed (nominal e) ∧
      (Examples.construal e = some .singular → Divided (nominal e))) ↔
        e.judgment = .acceptable := by
  decide

/-! ### The English language file -/

/-- The selection a language file records for a quantifier is the one an assigner predicts: a
singular
where the assigner divides a bare stem, a plural or dual where it takes plural inflection, and
mass where it takes an undivided stem. -/
@[mk_iff]
structure Predicts (a : Assigner) (q : QuantificationalDeterminer) : Prop where
  singular : q.numberRestriction = some .singular ↔ WellFormed [a] ∧ Divided [a]
  plural : (q.numberRestriction = some .plural ∨ q.numberRestriction = some .dual) ↔
    WellFormed [.div, a]
  mass : q.selectsMass = true ↔ WellFormed [a] ∧ ¬ Divided [a]

-- (40b), (40d), (40e)
open English.Determiners in
theorem predicts_fragment :
    (∀ q ∈ [every, each], Predicts (.portmanteau .count) q) ∧
      (∀ q ∈ [many, few, both], Predicts (.pure .count) q) ∧
      ∀ q ∈ [all, most], Predicts (.pure .unspecified) q := by
  simp [predicts_iff, every, each, many, few, both, all, most, wellFormed_singleton,
    wellFormed_div_cons, Divided, Assigner.pure, Assigner.portmanteau, Quantity.Counts,
    Quantity.Measures]

/-! ### Dividing without individuating

Assigning range to ⟨e⟩DIV superimposes reticules on a portion of stuff; a reticule carves cells,
none of which need be a canonical unit, and a cardinal at ⟨e⟩# selects the reticules with the
number of complete cells it counts. -/

section Reticules

variable {α : Type*} [Lattice α] [OrderBot α] {m : α} (unit : α → Prop) [DecidablePred unit]

/-- Plural marking presupposes no singulars: a portion that is not itself a unit has a reticule
without a complete cell, the one *zero apples* and *0.5 apples* select. -/
theorem exists_finpartition_filter_eq_empty (hm : m ≠ ⊥) (h : ¬ unit m) :
    ∃ r : Finpartition m, {c ∈ r.parts | unit c} = ∅ :=
  ⟨.indiscrete hm, by simpa [filter_eq_empty_iff] using h⟩

/-- Individuals emerge at ⟨e⟩#: a reticule with `n` complete cells holds `n` pairwise disjoint
units within the portion, so *more than three circles* cannot be true without individual circles,
though bare *circles* can. -/
theorem exists_pairwiseDisjoint_of_card_filter {n : ℕ} (r : Finpartition m)
    (h : #{c ∈ r.parts | unit c} = n) :
    ∃ s : Finset α, #s = n ∧ (s : Set α).PairwiseDisjoint id ∧ ∀ x ∈ s, unit x ∧ x ≤ m :=
  ⟨_, h, r.disjoint.subset (coe_subset.2 (filter_subset _ _)), fun _ hx ↦
    ⟨(mem_filter.1 hx).2, r.le (mem_filter.1 hx).1⟩⟩

end Reticules

/-! ### The nominal spine -/

-- (27): the quantity head is above the dividing head.
theorem asymmRel_Q_Num : AsymmRel Cat.ExtendsTo .Q .Num := by decide +kernel

end Borer2005
