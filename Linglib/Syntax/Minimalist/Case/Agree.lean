module

public import Linglib.Syntax.Minimalist.Case.Dependent
public import Linglib.Syntax.Minimalist.Feature.Valuation

/-!
# Case valued under Agree

`Minimalist.agreeValue` values a case on the highest nominal of a domain whose case is unvalued. It
works on a case valuation, the list of nominals from the highest down with the case each has
received so far. This file shows that it is Agree over feature states from a case assigner.

A case valuation is read as a feature state over positions, in which the nominal at each position
bears case, unvalued where the valuation gives it no value, and the assigner bears its case valued.
A valued probe matches the goals whose slot is unvalued, so the probe of the assigner matches
exactly the nominals with unvalued case. Both Agrees are the one Agree of `Probe/Agree.lean` with a
probe that interacts with the goals it is satisfied by, so each copies once, at the goal its
search finds, and [Agree from the assigner over the nominals of a domain leaves the state that
`agreeValue` gives](##Minimalist.agree_toFeatureState).

## Main definitions

* `Case.Valuation.toFeatureState`: a case valuation with an assigner, as a feature state.

## References

* [chomsky-2000]
-/

@[expose] public section

open Minimalist

namespace Case.Valuation

variable {α : Type*}

/-- The feature state of a case valuation `s` with an assigner of case `v`. The assigner, `none`,
bears case valued `v`, and the nominal at position `i` bears case, unvalued if `s` gives it no
value. -/
def toFeatureState (v : Case) (s : Valuation α Case) : FeatureState (Option ℕ)
  | none => .single .case v
  | some i => Function.update ⊥ .case ((s[i]?.bind Prod.snd).elim .unvalued .valued)

end Case.Valuation

namespace Minimalist

open Case.Valuation

variable {α : Type*} {P : α → Prop} [DecidablePred P] {v : Case} {s : Case.Valuation α Case}

/-- Agree from a case assigner over the nominals of the domain `P`, highest first, leaves the
feature state of the valuation that `agreeValue` gives. -/
theorem agree_toFeatureState :
    (((s.toFeatureState v).probe none .case fun _ ↦ True).agree
        (fun g σ ↦ σ.value none .case g) (s.toFeatureState v)
        ((s.zipIdx.filter fun e ↦ decide (P e.1.1)).map fun e ↦ some e.2)).state =
      (agreeValue P v s).toFeatureState v := by
  rw [Probe.agree_state_eq_elim fun _ ↦ and_iff_left trivial, agreeValue, Probe.agreeList,
    Probe.agree_state_eq_elim fun _ ↦ Iff.rfl]
  have hsat : ∀ e ∈ s.zipIdx.filter (fun e ↦ decide (P e.1.1)),
      ((s.toFeatureState v).probe none .case fun _ ↦ True).sat (some e.2) ↔ e.1.2.isNone := by
    intro e he
    have hget := List.mem_zipIdx_iff_getElem?.1 (List.mem_filter.1 he).1
    obtain ⟨⟨x, o⟩, i⟩ := e
    cases o <;> simp_all [FeatureState.probe, FeatureState.Matches, toFeatureState]
  have hsearch := Probe.search_map (p := Probe.relativized fun e : (α × Option Case) × ℕ ↦
    e.1.2.isNone) (fun e ↦ some e.2) hsat
  have hfilt : (Probe.relativized fun e : (α × Option Case) × ℕ ↦ e.1.2.isNone).search
      (s.zipIdx.filter fun e ↦ decide (P e.1.1)) =
      ((Probe.relativized fun q : α × Option Case ↦ q.2.isNone ∧ P q.1).comap Prod.fst).search
        s.zipIdx := by
    simp only [Probe.search, List.find?_filter]
    congr 1
    funext e
    simp [and_comm]
  rw [hsearch, hfilt]
  cases hr : ((Probe.relativized fun q : α × Option Case ↦ q.2.isNone ∧ P q.1).comap
      Prod.fst).search s.zipIdx with
  | none => rfl
  | some e =>
    have hget := List.mem_zipIdx_iff_getElem?.1 (Probe.mem_of_search_eq_some hr)
    have he := Probe.sat_of_search_eq_some hr
    obtain ⟨⟨x, o⟩, i⟩ := e
    simp only [Probe.comap_sat, Probe.relativized_sat] at he
    obtain ⟨ho, -⟩ := he
    obtain rfl : o = none := Option.isNone_iff_eq_none.1 ho
    obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.1 hget
    simp only [Option.map_some, Option.elim_some]
    funext y
    rcases y with _ | j
    · simp [FeatureState.value, toFeatureState, hget, FeatureBundle.valueFrom]
    · rcases eq_or_ne j i with rfl | hj
      · simp [FeatureState.value, toFeatureState, hi, hx, FeatureBundle.valueFrom,
          FeatureBundle.valueAt]
      · simp [FeatureState.value, toFeatureState, hj, Ne.symm hj]

end Minimalist
