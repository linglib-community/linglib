module

public import Linglib.Discourse.Gameboard.Defs
public import Mathlib.Data.Finset.SDiff

/-!
# Contextual instantiation

An utterance's contextual parameters are the values its context must supply, and grounding the
utterance witnesses them. We define contextual instantiation, which removes the parameters that
have been witnessed, and prove that the utterances it produces are exactly the contextual
extensions of an utterance: those that differ from it at most in having fewer parameters.

## Main definitions

* `Gameboard.LocutionaryProposition.instantiate`: the utterance with the parameters labelled in
  a set witnessed.

## Main results

* `Gameboard.LocutionaryProposition.instantiate_instantiate`: instantiating twice instantiates
  the union.
* `Gameboard.LocutionaryProposition.exists_eq_instantiate_iff`: contextual instantiation yields
  exactly the contextual extensions of an utterance.

## References

* [ginzburg-2012]
-/

@[expose] public section

namespace Gameboard

variable {Φ K Λ Δ C : Type*}

namespace LocutionaryProposition

variable [DecidableEq Λ] (w u : LocutionaryProposition Φ K Λ Δ C) (s t : Finset Λ)

/-- Contextual instantiation ([ginzburg-2012] (48) p. 178): the parameters labelled in `s` have
been witnessed and leave the utterance's contextual parameters. -/
def instantiate : LocutionaryProposition Φ K Λ Δ C :=
  { u with parameters := u.parameters \ s }

@[simp] theorem parameters_instantiate : (u.instantiate s).parameters = u.parameters \ s := rfl

@[simp] theorem form_instantiate : (u.instantiate s).form = u.form := rfl

@[simp] theorem category_instantiate : (u.instantiate s).category = u.category := rfl

@[simp] theorem content_instantiate : (u.instantiate s).content = u.content := rfl

@[simp] theorem constituents_instantiate :
    (u.instantiate s).constituents = u.constituents := rfl

@[simp] theorem instantiate_empty : u.instantiate ∅ = u := by
  simp [instantiate]

theorem instantiate_instantiate : (u.instantiate s).instantiate t = u.instantiate (s ∪ t) := by
  simp [instantiate, sdiff_sdiff_left]

/-- Contextual instantiation yields exactly the contextual extensions of [ginzburg-2012] (47) p.
178. -/
theorem exists_eq_instantiate_iff :
    (∃ s, w = u.instantiate s) ↔ w.form = u.form ∧ w.category = u.category ∧
      w.content = u.content ∧ w.constituents = u.constituents ∧ w.parameters ⊆ u.parameters := by
  refine ⟨?_, fun ⟨hf, hc, hn, hs, hp⟩ ↦ ⟨u.parameters \ w.parameters, ?_⟩⟩
  · rintro ⟨s, rfl⟩
    exact ⟨rfl, rfl, rfl, rfl, Finset.sdiff_subset⟩
  · cases w
    simp_all [instantiate, Finset.sdiff_sdiff_eq_self hp]

end LocutionaryProposition

end Gameboard
