module

public import Linglib.Semantics.Modality.HistoricalAlternatives
public import Linglib.Semantics.Tense.Embedding
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Data.Examples.Klecha2016
public import Linglib.Data.Examples.Readers

/-!
# Klecha (2016): Modality and Embedded Temporal Operators

[klecha-2016] derives the temporal orientation of a clause under an attitude verb from the verb's
modal bases. Under *hope* and *pray* a past under a past may follow the attitude, which Abusch's
Upper Limit Constraint forbids and *think* does not allow. The base `dox` returns the actual
histories, which end at the evaluation time, so it [carries the
constraint](##Background.upperLimitConstraint_of_mem_dox), and `cir` the future histories, which
begin after it. A clause's readings are the orientations its attitude's bases and its tense both
admit: [*think* leaves the past and the present](##think_readings), [*hope* every
orientation](##hope_readings), as [the corpus sentences show](##rows_readings).

## Implementation notes

* Histories are the substrate's indices, the temporal component of a history reduced to the
  time of its index, so the definedness of τ(k|t) in (54) and (55) is membership of the
  embedded time in the base.
* The aktionsart restriction that rules out the episodic simultaneous reading of (7a) is not
  represented; the study states the orientations that tense and modal base leave open.
* The paper gives the entries of *think* and *hope* an open modal base argument and leaves the
  mechanism pairing verbs with bases unformalized. That a doxastic verb takes `dox` alone and a
  preferential verb either, extended from *think* and *hope* to the verbs of their classes, is
  this study's assumption, the one the readings of *think* rest on.

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

/-- (35): the orientations a modal base admits for the reference time of its prejacent relative
to the evaluation time are past and present under `dox`, whose actual histories end at the
evaluation time, and future under `cir`, whose future histories depart from it. -/
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

-- (53), (55)
theorem compare_mem_orientations [LinearOrder T] (m : Background)
    (history : HistoricalAlternatives W T) {s s' : Index W T} (h : s' ∈ m.base history s) :
    compare s'.time s.time ∈ m.orientations :=
  compare_mem_of_mem_orientedBase h

-- §4.2 [abusch-1997]
theorem orientations_dox : dox.orientations = upperLimitConstraint := by decide

/-- The modal base `dox` carries the Upper Limit Constraint: its situations are never later than
the evaluation time. -/
theorem upperLimitConstraint_of_mem_dox [LinearOrder T] (history : HistoricalAlternatives W T)
    {s s' : Index W T} (h : s' ∈ dox.base history s) :
    compare s'.time s.time ∈ upperLimitConstraint :=
  orientations_dox ▸ compare_mem_orientations .dox history h

-- (55), (53), §3.3, (43), (45a), §3.2
theorem cells :
    dox.orientations ∩ ⟦past⟧ = ⟦past⟧ ∧ dox.orientations ∩ nonpast = ⟦present⟧ ∧
      cir.orientations ∩ nonpast = ⟦future⟧ ∧ cir.orientations ∩ ⟦past⟧ = ∅ := by
  decide

end Background

/-! ### Attitude verbs, §3.1 -/

/-- The modal bases a verb of each class combines with: a doxastic verb `dox` alone and a
preferential verb either. Klecha's derivations give *hope* `cir`, (49), and `dox`, (55), and
*think* `dox`; what rules out *think* with `cir` he leaves open, so the restriction is this
study's. -/
def modalBases : Attitude → Finset Background
  | .doxastic _ => {.dox}
  | .preferential _ _ => {.dox, .cir}

/-- The orientations open to a clause of underlying tense `τ` embedded under an attitude of
class `a` are those admitted both by one of the attitude's modal bases and by the tense. -/
def readings (a : Attitude) (τ : Finset Ordering) : Finset Ordering :=
  (modalBases a).biUnion (·.orientations ∩ τ)

-- (4), (7)
theorem readings_union (a : Attitude) (τ₁ τ₂ : Finset Ordering) :
    readings a (τ₁ ∪ τ₂) = readings a τ₁ ∪ readings a τ₂ := by
  simp only [readings, Finset.inter_union_distrib_left, Finset.biUnion_union]

/-- (6), (7), (7a): under *think* a past under a past, of underlying past or non-past, is before
or at the attitude, and of underlying non-past at it. -/
theorem think_readings : ∀ a ∈ think.attitude.toList,
    readings a (⟦past⟧ ∪ nonpast) = ⟦past⟧ ∪ ⟦present⟧ ∧ readings a nonpast = ⟦present⟧ := by
  decide +kernel

/-- (48), (54), (4), (5): under *hope* a past under a past, of underlying past or non-past, may
take every orientation, its underlying non-past the present and the future, and its underlying
past the past. -/
theorem hope_readings : ∀ a ∈ hope.attitude.toList,
    readings a (⟦past⟧ ∪ nonpast) = Finset.univ ∧ readings a nonpast = nonpast ∧
      readings a ⟦past⟧ = ⟦past⟧ := by
  decide +kernel

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

/-- (1), (2), (3): an orientation of a corpus sentence is available exactly when its attitude's
readings admit it. -/
theorem rows_readings :
    ∀ e ∈ Examples.all, ∀ v ∈ (e.feature? "verb" >>= verbOf).toList, ∀ a ∈ v.attitude.toList,
      ∀ c ∈ cells, ∀ j ∈ (e.feature? c.1).toList,
        (j = "available" ↔ c.2 ⊆ readings a Finset.univ) := by
  decide +kernel

end Klecha2016
