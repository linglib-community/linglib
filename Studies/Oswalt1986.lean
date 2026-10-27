module

public import Linglib.Semantics.Evidential.Basic
public import Linglib.Fragments.Kashaya.Evidentiality
public import Linglib.Data.Examples.Oswalt1986

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
first of the column covering a source at hand (`preferred`). Seeing takes precedence over every
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

/-- The evidential a column prefers for the sources at hand is its first suffix covering one of
them, the rows of Table 1 being ordered so that each has priority over those below. -/
def preferred (es : List Evidential) (sources : Finset Parameter) : Option Evidential :=
  es.find? fun e ↦ (e.covers ∩ sources).Nonempty

theorem preferred_of_visual_mem (a : Perfectivity) {S : Finset Parameter} (h : .visual ∈ S) :
    preferred (paradigm .spontaneous a) S = some (factualVisual a) := by
  cases a <;> simp [preferred, paradigm, List.find?, performative, factualVisual,
    Finset.Nonempty, h]

theorem preferred_append_singleton_eq_some {es : List Evidential} {e : Evidential} (he : e ∉ es)
    (S : Finset Parameter) :
    preferred (es ++ [e]) S = some e ↔
      ¬ Disjoint e.covers S ∧ ∀ x ∈ es, Disjoint x.covers S := by
  simp only [preferred, List.find?_append, ← Finset.not_disjoint_iff_nonempty_inter]
  cases h : es.find? (fun x ↦ !Disjoint x.covers S) with
  | none => simp_all [List.find?_eq_none]
  | some x =>
    have hx := List.mem_of_find?_eq_some h
    have := List.find?_some h
    simp only [Option.some_or, Option.some.injEq]
    exact ⟨fun hxe ↦ (he (hxe ▸ hx)).elim, fun ⟨_, hall⟩ ↦ by simp_all⟩

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

/-- The mode an example's `mode` feature names. -/
def mode? (r : Datum) : Option Mode :=
  match r.feature? "mode" with
  | some "spontaneous" => some .spontaneous
  | some "responsive" => some .responsive
  | some "narrative" => some .narrative
  | some "remote" => some .remote
  | _ => none

/-- The aspects an example's stem may have, the one its `aspect` feature names or else either. -/
def aspects (r : Datum) : List Perfectivity :=
  match r.feature? "aspect" with
  | some "imperfective" => [.imperfective]
  | some "perfective" => [.perfective]
  | _ => [.imperfective, .perfective]

/-- The evidential an example's `evidential` feature names, for a stem of the given aspect. -/
def evidential? (r : Datum) (a : Perfectivity) : Option Evidential :=
  match r.feature? "evidential" with
  | some "performative" => some (performative a)
  | some "factualVisual" => some (factualVisual a)
  | some "auditory" => some auditory
  | some "inferential" => some inferential
  | some "quotative" => some quotative
  | some "inferentialII" => some inferentialII
  | some "personalExperience" => some personalExperience
  | some "remotePast" => some remotePast
  | _ => none

theorem examples_named :
    ∀ r ∈ Examples.all, ∀ a ∈ aspects r,
      (evidential? r a).isSome ∧ (evidential? r a ≠ some inferentialII → (mode? r).isSome) := by
  decide

theorem examples_mem_paradigm :
    ∀ r ∈ Examples.all, ∀ m ∈ mode? r, ∀ a ∈ aspects r, ∀ e ∈ evidential? r a,
      e ∈ paradigm m a := by
  decide

end Oswalt1986
