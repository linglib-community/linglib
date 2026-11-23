module

public import Linglib.Semantics.Evidentiality.Paradigm
public import Linglib.Fragments.Kashaya.Evidentiality
public import Linglib.Data.Examples.Oswalt1986
public import Linglib.Data.Examples.Readers

/-!
# Oswalt (1986): The Evidential System of Kashaya

This file formalizes Oswalt's description of the Kashaya evidential suffixes, recorded
in `Fragments/Kashaya/Evidentiality.lean` as the columns of his Table 1. The suffixes of a
column are mutually exclusive, only one appearing on a verb, and cover disjoint sources, so
every column is a well-formed paradigm (`paradigm_wellFormed`). A response to another's words
drops the performative pair, the factual-visual pair taking its place (`paradigm_responsive`,
`performative_notMem_responsive`). The narrative construction simplifies the distinctions to
two, personal experience against the quotative: as a partition of the sources a spontaneous
remark expresses, every column is a coarsening of the spontaneous column
(`spontaneous_le`), the spontaneous column making four distinctions of source and the
narrative and remote columns two (`card_parts_spontaneous`, `card_parts_narrative`). The rows
of the table are a hierarchy, Performative > Factual-Visual > Auditory > Inferential >
Quotative, each with priority over those below it, so the evidential a speaker uses is the
first of the column covering a source at hand (`Evidential.preferred`). Seeing takes precedence over every
other source (`preferred_of_visual_mem`), the quotative is used exactly when report is at hand
and no other row covers a source at hand (`preferred_eq_quotative_iff`), and the performative
is never chosen on the strength of a parameter (`preferred_ne_performative`). Inferential II
must be followed by another suffix and belongs to no column (`inferentialII_notMem`). The
chapter's examples name the evidential they illustrate and, for the suffixes of the paradigm,
the mode; each lies in the paradigm of its mode for the aspect of its stem
(`examples_mem_paradigm`).

## References

* [oswalt-1986]
-/

@[expose] public section

namespace Oswalt1986

open Evidential Aspect Kashaya.Evidentiality

/-! ### The columns of Table 1 -/

theorem paradigm_wellFormed (m : Mode) (a : Perfectivity) : WellFormed (paradigm m a) := by
  cases m <;> cases a <;> decide

theorem paradigm_responsive (a : Perfectivity) :
    paradigm .responsive a = (paradigm .spontaneous a).erase (performative a) := by
  cases a <;> rfl

theorem performative_notMem_responsive (a : Perfectivity) :
    performative a ∉ paradigm .responsive a := by
  cases a <;> decide

theorem inferentialII_notMem (m : Mode) (a : Perfectivity) : inferentialII ∉ paradigm m a := by
  cases m <;> cases a <;> decide

/-! ### The narrative simplification -/

theorem expressed_spontaneous_subset (m : Mode) (a : Perfectivity) :
    expressed (paradigm .spontaneous a) ⊆ expressed (paradigm m a) := by
  cases m <;> cases a <;> decide

theorem spontaneous_le (m : Mode) (a : Perfectivity) :
    Evidential.finpartition (paradigm .spontaneous a) (paradigm_wellFormed _ _) ≤
      (Evidential.finpartition (paradigm m a) (paradigm_wellFormed _ _)).restrict
        (expressed_spontaneous_subset m a) := by
  cases m <;> cases a <;> (show ∀ b ∈ _, ∃ c ∈ _, b ≤ c; decide)

theorem card_parts_spontaneous (a : Perfectivity) :
    (Evidential.finpartition (paradigm .spontaneous a) (paradigm_wellFormed _ _)).parts.card =
      4 := by
  cases a <;> decide

theorem card_parts_narrative (a : Perfectivity) :
    (Evidential.finpartition (paradigm .narrative a) (paradigm_wellFormed _ _)).parts.card = 2 ∧
    (Evidential.finpartition (paradigm .remote a) (paradigm_wellFormed _ _)).parts.card = 2 := by
  cases a <;> decide

/-! ### The hierarchy -/

theorem preferred_of_visual_mem (a : Perfectivity) {S : Finset Parameter} (h : .visual ∈ S) :
    preferred (paradigm .spontaneous a) S = some (factualVisual a) := by
  cases a <;> simp [preferred, paradigm, List.find?, performative, factualVisual, h]

theorem preferred_eq_quotative_iff (a : Perfectivity) (S : Finset Parameter) :
    preferred (paradigm .spontaneous a) S = some quotative ↔
      ¬ Disjoint quotative.covers S ∧
        ∀ e ∈ paradigm .spontaneous a, e ≠ quotative → Disjoint e.covers S := by
  have hne : quotative ∉ [performative a, factualVisual a, auditory, inferential] := by
    cases a <;> decide
  rw [show paradigm .spontaneous a =
      [performative a, factualVisual a, auditory, inferential] ++ [quotative] from rfl,
    preferred_append_singleton_eq_some hne]
  refine and_congr_right fun _ ↦ ⟨fun h e he hq ↦ ?_,
    fun h e he ↦ h e (List.mem_append_left _ he) (ne_of_mem_of_not_mem he hne)⟩
  rcases List.mem_append.1 he with he | he
  exacts [h e he, (hq (List.mem_singleton.1 he)).elim]

theorem preferred_ne_performative (a : Perfectivity) (S : Finset Parameter) :
    preferred (paradigm .spontaneous a) S ≠ some (performative a) := fun h ↦ by
  have := List.find?_some h
  cases a <;> simp [performative] at this

/-! ### The examples -/

/-- The mode of the fragment an example's mode names. -/
def Examples.Mode.toMode : Examples.Mode → Kashaya.Evidentiality.Mode
  | .spontaneous => .spontaneous
  | .responsive => .responsive
  | .narrative => .narrative
  | .remote => .remote

/-- The aspects an example's stem may have, the one the example fixes or else either. -/
def aspects (r : Datum) : List Perfectivity :=
  match Examples.aspect r with
  | some .imperfective => [.imperfective]
  | some .perfective => [.perfective]
  | none => [.imperfective, .perfective]

/-- The evidential a row of Table 1 names, for a stem of the given aspect. -/
def Examples.Marker.evidential : Examples.Marker → Perfectivity → Evidential
  | .performative, a => Kashaya.Evidentiality.performative a
  | .factualVisual, a => Kashaya.Evidentiality.factualVisual a
  | .auditory, _ => Kashaya.Evidentiality.auditory
  | .inferential, _ => Kashaya.Evidentiality.inferential
  | .quotative, _ => Kashaya.Evidentiality.quotative
  | .inferentialII, _ => Kashaya.Evidentiality.inferentialII
  | .personalExperience, _ => Kashaya.Evidentiality.personalExperience
  | .remotePast, _ => Kashaya.Evidentiality.remotePast

theorem examples_named :
    ∀ r ∈ Examples.all, (Examples.marker r).isSome ∧
      (Examples.marker r ≠ some .inferentialII → (Examples.mode r).isSome) := by
  decide

theorem examples_mem_paradigm :
    ∀ r ∈ Examples.all, ∀ m ∈ Examples.mode r, ∀ a ∈ aspects r, ∀ k ∈ Examples.marker r,
      k.evidential a ∈ paradigm m.toMode a := by
  decide

end Oswalt1986
