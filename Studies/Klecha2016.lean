module

public import Linglib.Semantics.Modality.HistoricalAlternatives
public import Linglib.Semantics.Tense.Embedding
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Data.Examples.Klecha2016

/-!
# Klecha (2016): Modality and Embedded Temporal Operators

Klecha accounts for the temporal orientation of finite clauses under attitude verbs through
their modal bases. His new data, (2) and (3), are past-under-past sentences with *hope* and
*pray* whose embedded event follows the attitude, readings Abusch's Upper Limit Constraint
forbids and *think* lacks, (6). The modal base pronouns of (35) carry the constraint: `dox`
returns actual histories, ending at the evaluation time, and `cir` future histories,
beginning after it, so each base is the substrate's base oriented by a tense cell. A
past-under-past clause has an underlying past or non-past, and its readings are the
orientations its attitude's modal bases and its tense both admit: *think* takes `dox` alone,
*hope* either.

## Implementation notes

* Histories are the substrate's indices, the temporal component of a history reduced to the
  time of its index, so the definedness of τ(k|t) in (54) and (55) is membership of the
  embedded time in the base.
* The aktionsart restriction that rules out the episodic simultaneous reading of (7a) is not
  represented; the study states the orientations that tense and modal base leave open.

## References

* [klecha-2016]
* [abusch-1997]
-/

@[expose] public section

namespace Klecha2016

open scoped Denotes

open Tense HistoricalAlternatives English English.Verbs Kaplan

variable {W T : Type*}

/-- The modal base pronouns of (35), `dox` returning the actual histories 𝒜_t, which end at the
evaluation time, and `cir` the future histories ℱ_t, which begin after it. -/
inductive Background
  | dox
  | cir
  deriving DecidableEq, Repr

namespace Background

/-- The orientations a modal base admits for the reference time of its prejacent relative to
the evaluation time are past and present under `dox` and future under `cir` (Table 1). -/
def orientations : Background → Finset Ordering
  | .dox => ⟦past⟧ ∪ ⟦present⟧
  | .cir => ⟦future⟧

/-- The situations a modal base makes accessible from `s`, (35), the alternatives at the times
its orientations admit. -/
def base [LT T] (m : Background) (history : HistoricalAlternatives W T) (s : Index W T) :
    Set (Index W T) :=
  orientedBase history s m.orientations

theorem base_dox_cir [LT T] (history : HistoricalAlternatives W T) (s : Index W T) :
    dox.base history s = actualHistoryBase history s ∧
      cir.base history s = futureHistoryBase history s :=
  ⟨by rw [base, orientations, actualHistoryBase, ← past_sup_present]; rfl, rfl⟩

/-- The time of a situation accessible from `s` bears an admitted orientation to the evaluation time
((53)–(55)). -/
theorem compare_mem_orientations [LinearOrder T] (m : Background)
    (history : HistoricalAlternatives W T) {s s' : Index W T} (h : s' ∈ m.base history s) :
    compare s'.time s.time ∈ m.orientations :=
  compare_mem_of_mem_orientedBase h

/-- The doxastic modal base admits exactly the orientations of the Upper Limit Constraint of
[abusch-1997] (§4.2). -/
theorem orientations_dox : dox.orientations = upperLimitConstraint := by decide

theorem upperLimitConstraint_of_mem_dox [LinearOrder T] (history : HistoricalAlternatives W T)
    {s s' : Index W T} (h : s' ∈ dox.base history s) :
    compare s'.time s.time ∈ upperLimitConstraint :=
  orientations_dox ▸ compare_mem_orientations .dox history h

/-- With `dox` a past is past and a non-past simultaneous (55), and with `cir` a non-past is future
(53) and a past empty (§3.3, (43)). -/
theorem cells :
    dox.orientations ∩ ⟦past⟧ = ⟦past⟧ ∧ dox.orientations ∩ nonpast = ⟦present⟧ ∧
      cir.orientations ∩ nonpast = ⟦future⟧ ∧ cir.orientations ∩ ⟦past⟧ = ∅ := by
  decide

end Background

/-! ### Attitude verbs, §3.1 -/

/-- A doxastic verb combines with `dox` alone and a preferential verb with either modal base,
(34). -/
def modalBases : Attitude → Finset Background
  | .doxastic _ => {.dox}
  | .preferential _ _ => {.dox, .cir}

/-- The orientations open to a clause of underlying tense `τ` embedded under an attitude of
class `a` are those admitted both by one of the attitude's modal bases and by the tense. -/
def readings (a : Attitude) (τ : Finset Ordering) : Finset Ordering :=
  (modalBases a).biUnion (·.orientations ∩ τ)

/-- The readings of a past-under-past clause are those of past-under-present and
present-under-present together ((4)–(7)). -/
theorem readings_union (a : Attitude) (τ₁ τ₂ : Finset Ordering) :
    readings a (τ₁ ∪ τ₂) = readings a τ₁ ∪ readings a τ₂ := by
  ext o
  simp only [readings, Finset.mem_biUnion, Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨m, hm, ho, h | h⟩
    · exact Or.inl ⟨m, hm, ho, h⟩
    · exact Or.inr ⟨m, hm, ho, h⟩
  · rintro (⟨m, hm, ho, h⟩ | ⟨m, hm, ho, h⟩)
    · exact ⟨m, hm, ho, Or.inl h⟩
    · exact ⟨m, hm, ho, Or.inr h⟩

theorem past_union_nonpast : ⟦past⟧ ∪ nonpast = Finset.univ := by decide

/-- Under *think* an embedded clause is past or simultaneous, never future, and a present under a
present is simultaneous only ((6), (7) and (7a)). -/
theorem think_readings : ∀ a ∈ think.attitude.toList,
    readings a Finset.univ = ⟦past⟧ ∪ ⟦present⟧ ∧ readings a nonpast = ⟦present⟧ := by
  decide +kernel

/-- Under *hope* a past-under-past clause has every orientation, the future through `cir`
((48)–(54)), and a past under a present is past ((4), (5)). -/
theorem hope_readings : ∀ a ∈ hope.attitude.toList,
    readings a Finset.univ = Finset.univ ∧ readings a nonpast = nonpast ∧
      readings a ⟦past⟧ = ⟦past⟧ := by
  decide +kernel

/-- A matrix non-past has present reference only, which rules out (45a) \**It rains tomorrow*
(§3.2). -/
theorem matrix_nonpast_present : Background.dox.orientations ∩ nonpast = ⟦present⟧ := by decide

/-! ### The data, (1)–(3) -/

/-- The attitude verb of a row, from the fragment. -/
def verbOf : String → Option English.Verbs.Verb
  | "think" => some think
  | "hope" => some hope
  | "pray" => some pray
  | _ => none

/-- The orientation cells a row reports on. -/
def cells : List (String × Finset Ordering) :=
  [("past", ⟦past⟧), ("present", ⟦present⟧), ("future", ⟦future⟧)]

/-- An orientation a row reports available under its verb is among that verb's past-under-past
readings, and one reported unavailable is not ((1), (2), (3)). -/
theorem rows_readings :
    ∀ e ∈ Examples.all, ∀ v ∈ (e.feature? "verb" >>= verbOf).toList, ∀ a ∈ v.attitude.toList,
      ∀ c ∈ cells, ∀ j ∈ (e.feature? c.1).toList,
        (j = "available" ↔ c.2 ⊆ readings a Finset.univ) := by
  decide +kernel

end Klecha2016
