module

public import Linglib.Data.Examples.Kiparsky1998
public import Linglib.Data.Examples.Readers
public import Linglib.Fragments.Finnish.Case
public import Linglib.Semantics.Mereology

/-!
# Kiparsky (1998): Partitive Case and Aspect

This file formalizes Kiparsky's account of the Finnish partitive object: partitive case licenses
unboundedness of the verb phrase. A predicate is *unbounded* if it is divisive, cumulative and
not diverse, the first two relative to atoms and suprema; a verb phrase is unbounded if its verb
or its object is, and the object of an unbounded verb phrase is partitive. Diversity is
[Krifka's quantization](##isDiverse_iff_qua), Krifka's mass reference [is
unbounded](##isUnbounded_of_cum_of_div), and the [bounded quantities](##classification) are
bounded for the reasons Kiparsky gives, bare plurals being unbounded [only on the inclusive
reading](##not_isDivisive_exclusive). The case rule derives [the acceptability of the paper's
paradigm](##paradigm_checks) from the boundedness of the objects' denotations, which [classing
the verbs by resultativity fails](##not_fits_resultativity).

## Implementation notes

* Page numbers follow the manuscript; example numbers are the paper's.
* The verbs' boundedness is the paper's lexical classification; the objects' is computed in a
  model of four individuals, whose null individual no predicate contains.
* 'Few' and 'many' are pluralities of at most two and at least three individuals.
* The paradigm does not separate unboundedness from non-quantization, which fits it as well.

## TODO

* The partitive subjects of presentational verbs, and the coercion of bounded predicates.

## References

* [kiparsky-1998]
-/

@[expose] public section

namespace Kiparsky1998

open Mereology

/-! ### Boundedness -/

section Boundedness

variable {α : Type*} [PartialOrder α] (P : α → Prop)

/-- A predicate is *divisive* if each of its members that is not an atom has a proper part in
it ((35a), cited as (36a); p. 17). -/
def IsDivisive : Prop := ∀ x, P x → ¬ Atom x → ∃ y, y < x ∧ P y

/-- A predicate is *cumulative* if each of its members that is not its supremum is a proper part
of a member ((35b), cited as (36b)). -/
def IsCumulative : Prop := ∀ x, P x → ¬ (∀ y, P y → y ≤ x) → ∃ y, x < y ∧ P y

/-- A predicate is *diverse* if no member is a proper part of another ((35c), cited as (36c)). -/
def IsDiverse : Prop := ∀ x y, P x → P y → x ≠ y → ¬ x < y ∧ ¬ y < x

/-- A predicate is *unbounded* if it is divisive and cumulative and not diverse ((36), p. 18). -/
@[mk_iff]
structure IsUnbounded : Prop where
  divisive : IsDivisive P
  cumulative : IsCumulative P
  not_diverse : ¬ IsDiverse P

variable {P}

theorem isDivisive_iff : IsDivisive P ↔ ∀ x, Minimal P x → Atom x := by
  refine ⟨fun h x hx ↦ by_contra fun ha ↦ ?_, fun h x hx ha ↦ ?_⟩
  · obtain ⟨y, hyx, hy⟩ := h x hx.1 ha
    exact hyx.not_ge (hx.2 hy hyx.le)
  · obtain ⟨y, hy, hyx, hxy⟩ := (not_minimal_iff hx).1 (mt (h x) ha)
    exact ⟨y, lt_of_le_not_ge hyx hxy, hy⟩

theorem isCumulative_iff : IsCumulative P ↔ ∀ x, Maximal P x → ∀ y, P y → y ≤ x := by
  refine ⟨fun h x hx ↦ by_contra fun hg ↦ ?_, fun h x hx hg ↦ ?_⟩
  · obtain ⟨y, hxy, hy⟩ := h x hx.1 hg
    exact hxy.not_ge (hx.2 hy hxy.le)
  · obtain ⟨y, hy, hxy, hyx⟩ := (not_maximal_iff hx).1 (mt (h x) hg)
    exact ⟨y, lt_of_le_not_ge hxy hyx, hy⟩

/-- Diversity is Krifka's quantization: no member is a proper part of another. -/
theorem isDiverse_iff_qua : IsDiverse P ↔ QUA P :=
  ⟨fun h _ hx _ hy hne hle ↦ (h _ _ hx hy hne).1 (hle.lt_of_ne hne),
    fun h _ _ hx hy hne ↦ ⟨fun hlt ↦ h hx hy hne hlt.le, fun hlt ↦ h hy hx hne.symm hlt.le⟩⟩

theorem IsDivisive.of_div (hd : DIV P) (hb : ∀ x : α, ¬ IsBot x) : IsDivisive P :=
  isDivisive_iff.2 fun _ hx ↦ ⟨hb _, fun _ _ hyx ↦ hx.2 (hd hyx hx.1) hyx⟩

theorem IsCumulative.of_cum {α : Type*} [SemilatticeSup α] {P : α → Prop} (hc : CUM P) :
    IsCumulative P :=
  isCumulative_iff.2 fun _ hx ↦ ((cum_maximal_iff_isGreatest hc).1 hx).2

/-- Krifka's mass reference, cumulative and divisive but not quantized, is unbounded over a
carrier with no null individual. -/
theorem isUnbounded_of_cum_of_div {α : Type*} [SemilatticeSup α] {P : α → Prop} (hc : CUM P)
    (hd : DIV P) (hq : ¬ QUA P) (hb : ∀ x : α, ¬ IsBot x) : IsUnbounded P :=
  ⟨.of_div hd hb, .of_cum hc, mt isDiverse_iff_qua.1 hq⟩

variable [Fintype α] [DecidableEq α] [DecidableLE α] [DecidableLT α] [DecidablePred P]

instance : DecidablePred (Atom (α := α)) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ ∀ ⦃_⦄, _ → _ → _))

instance : Decidable (IsDivisive P) := inferInstanceAs (Decidable (∀ _, _ → _ → ∃ _, _ ∧ _))

instance : Decidable (IsCumulative P) := inferInstanceAs (Decidable (∀ _, _ → _ → ∃ _, _ ∧ _))

instance : Decidable (IsDiverse P) := inferInstanceAs (Decidable (∀ _ _, _ → _ → _ → _))

instance : Decidable (IsUnbounded P) := decidable_of_iff _ (isUnbounded_iff P).symm

end Boundedness

/-! ### Quantities -/

section Quantities

open Finset

/-- The pluralities of four individuals whose number satisfies `p`. -/
def ofCard (p : ℕ → Prop) [DecidablePred p] : Finset (Finset (Fin 4)) :=
  univ.filter fun s ↦ p s.card

/-- *Bears*, on the inclusive reading of the bare plural: any plurality, atoms included. -/
def bears : Finset (Finset (Fin 4)) := ofCard (1 ≤ ·)

/-- *Bears* on the exclusive reading: pluralities of at least two. -/
def exclusiveBears : Finset (Finset (Fin 4)) := ofCard (2 ≤ ·)

/-- *A bear*. -/
def aBear : Finset (Finset (Fin 4)) := ofCard (· = 1)

/-- *The bear*. -/
def theBear : Finset (Finset (Fin 4)) := {{0}}

/-- *Two bears*. -/
def twoBears : Finset (Finset (Fin 4)) := ofCard (· = 2)

/-- *The two bears*. -/
def theTwoBears : Finset (Finset (Fin 4)) := {{0, 1}}

/-- *The bears*. -/
def theBears : Finset (Finset (Fin 4)) := {univ}

/-- *Few bears*. -/
def fewBears : Finset (Finset (Fin 4)) := ofCard fun n ↦ 1 ≤ n ∧ n ≤ 2

/-- *Many bears*. -/
def manyBears : Finset (Finset (Fin 4)) := ofCard (3 ≤ ·)

/-- The bounded quantities of (37b) are bounded for the reasons the paper gives: bare plurals are
unbounded, *few* is divisive but not cumulative, *many* cumulative but not divisive, *two*
neither, and the cardinal and definite quantities are diverse. -/
theorem classification :
    IsUnbounded (· ∈ bears) ∧
      (IsDivisive (· ∈ fewBears) ∧ ¬ IsCumulative (· ∈ fewBears)) ∧
      (IsCumulative (· ∈ manyBears) ∧ ¬ IsDivisive (· ∈ manyBears)) ∧
      (¬ IsDivisive (· ∈ twoBears) ∧ ¬ IsCumulative (· ∈ twoBears)) ∧
      IsDiverse (· ∈ aBear) ∧ IsDiverse (· ∈ theBear) ∧ IsDiverse (· ∈ twoBears) ∧
      IsDiverse (· ∈ theTwoBears) ∧ IsDiverse (· ∈ theBears) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem not_isDivisive_exclusive : ¬ IsDivisive (· ∈ exclusiveBears) := by
  decide +kernel

-- (37b.c) lists 'a bomb' and 'the food' among the predicates meeting neither (36a) nor (36b),
-- but by (35) a predicate of atoms is divisive and a predicate of one member cumulative, both
-- vacuously; diversity alone bounds them, as the remark on 'Fred' after (36) says.
theorem aBear_isDivisive_theBears_isCumulative :
    IsDivisive (· ∈ aBear) ∧ IsCumulative (· ∈ theBears) := by
  decide +kernel

end Quantities

/-! ### The case of the object -/

/-- A reading of a verb, bounded or unbounded ([+B] and [−B]). -/
inductive Reading
  | bounded | unbounded
  deriving DecidableEq, Repr

/-- The object case `c` is licensed under the verb reading `r` and the object denotation `d` if
it is the partitive exactly when the verb phrase is unbounded, that is, when the verb or the
object is ((38) and (41), pp. 18-19). -/
def Licenses (r : Reading) (d : Finset (Finset (Fin 4))) (c : Finnish.Case) : Prop :=
  c = .part ↔ r = .unbounded ∨ IsUnbounded (· ∈ d)

instance (r : Reading) (d : Finset (Finset (Fin 4))) (c : Finnish.Case) :
    Decidable (Licenses r d c) :=
  inferInstanceAs (Decidable (_ ↔ _))

/-- The verbs of (1)-(4) by their readings: *ampua* 'shoot (dead), shoot at' has both, *saada*
'get' and *omistaa* 'own' only a bounded one and *etsiä* 'seek' only an unbounded one. -/
def verbReadings : List (String × List Reading) :=
  [("ampua", [.bounded, .unbounded]), ("saada", [.bounded]), ("etsiä", [.unbounded]),
    ("omistaa", [.bounded])]

/-- The readings of the objects of (1)-(4): 'the (a) bear', '(the) two bears', and the plural
'bears' or 'the bears'. -/
def objectReadings : List (String × List (Finset (Finset (Fin 4)))) :=
  [("singular", [aBear, theBear]), ("numeral", [twoBears, theTwoBears]),
    ("plural", [bears, theBears])]

/-- A row of (1)-(4) read through tables of verb and object readings: the readings of its verb
and its object, and its object case. -/
def cell? (verbs : List (String × List Reading))
    (objects : List (String × List (Finset (Finset (Fin 4))))) (e : Datum) :
    Option (List Reading × List (Finset (Finset (Fin 4))) × Finnish.Case) := do
  let v ← e.parse? "verb" verbs
  let o ← e.parse? "object" objects
  let c ← e.parse? "case" [("part", Finnish.Case.part), ("acc", .acc)]
  some (v, o, c)

/-- The rows of (1)-(4), all 24 read, are acceptable exactly when a reading of the verb and a
reading of the object license the case. -/
def Fits (verbs : List (String × List Reading))
    (objects : List (String × List (Finset (Finset (Fin 4))))) : Prop :=
  Datum.Checks (cell? verbs objects)
    (fun x ↦ Judgment.Band.ofProp (∃ r ∈ x.1, ∃ d ∈ x.2.1, Licenses r d x.2.2)) Examples.all 24

instance (verbs : List (String × List Reading))
    (objects : List (String × List (Finset (Finset (Fin 4))))) : Decidable (Fits verbs objects) :=
  inferInstanceAs (Decidable (Datum.Checks _ _ _ _))

/-- The case rule derives the acceptability of the paradigm of *shoot*, *get*, *seek* and *own*
from the verbs' readings and the boundedness of the objects' denotations. -/
theorem paradigm_checks : Fits verbReadings objectReadings := by
  decide +kernel

/-- Resultativity is not the criterion: classing *omistaa* 'own', which is irresultative, with
*etsiä* 'seek' rather than with *saada* 'get' fails the paradigm. -/
theorem not_fits_resultativity :
    ¬ Fits [("ampua", [.bounded, .unbounded]), ("saada", [.bounded]), ("etsiä", [.unbounded]),
      ("omistaa", [.unbounded])] objectReadings := by
  decide +kernel

-- The paradigm needs the inclusive bare plural: on the exclusive reading *saa-n karhu-j-a* 'I'll
-- get bears' is predicted unacceptable.
theorem not_fits_exclusive :
    ¬ Fits verbReadings [("singular", [aBear, theBear]), ("numeral", [twoBears, theTwoBears]),
      ("plural", [exclusiveBears, theBears])] := by
  decide +kernel

end Kiparsky1998
