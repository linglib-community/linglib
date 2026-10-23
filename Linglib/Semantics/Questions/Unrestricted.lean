module

public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Order.Minimal

/-!
# Unrestricted inquisitive propositions

In the unrestricted inquisitive semantics of Ciardelli, Groenendijk and Roelofsen a proposition is
a set of possibilities, sets of worlds, that need not be closed downward, so a possibility may sit
inside another and still count. A proposition is inquisitive when it has two maximal
possibilities, attentive when it has a non-maximal one, and informative when its possibilities
do not cover every world. Having more than one possibility, interactivity in Coppock and
Brochhagen's term, is `Set.Nontrivial`, and it is exactly being inquisitive or attentive.

The library's `Question` and the support semantics of `Logic/Team/Inquisitive.lean` are closed
downward, so they identify a proposition with its maximal possibilities and lose the non-maximal
ones; this file keeps the raw `Set (Set W)`.

## Main definitions

* `Inquisitive.Unrestricted.IsInquisitive`, `IsAttentive`, `IsInformative`.
* `Inquisitive.Unrestricted.restrict`: a proposition restricted to an information set.
* `Inquisitive.Unrestricted.exh`: exhaustification against a question.

## Main results

* `Inquisitive.Unrestricted.nontrivial_iff`: a proposition has more than one possibility just in
  case it is inquisitive or attentive.

## References

* [ciardelli-groenendijk-roelofsen-2009]
* [roelofsen-vangool-2010]
* [coppock-brochhagen-2013]
-/

@[expose] public section

namespace Inquisitive.Unrestricted

open Set

variable {W : Type*} (P : Set (Set W))

/-- A proposition is a nonempty set of possibilities that omits the empty possibility unless it
is the contradictory proposition `{∅}`. -/
def IsProposition : Prop := P.Nonempty ∧ (∅ ∉ P ∨ P = {∅})

/-- A proposition is inquisitive when it has at least two maximal possibilities. -/
def IsInquisitive : Prop := {p | Maximal (· ∈ P) p}.Nontrivial

/-- A proposition is informative when its possibilities do not cover every world. -/
def IsInformative : Prop := ⋃₀ P ≠ univ

/-- A proposition is attentive when it has a non-maximal possibility. -/
def IsAttentive : Prop := ∃ p ∈ P, ¬ Maximal (· ∈ P) p

/-- A proposition has more than one possibility just in case it is inquisitive or attentive. -/
theorem nontrivial_iff : P.Nontrivial ↔ IsInquisitive P ∨ IsAttentive P := by
  constructor
  · rintro ⟨p, hp, q, hq, hne⟩
    by_cases hmp : Maximal (· ∈ P) p
    · by_cases hmq : Maximal (· ∈ P) q
      · exact Or.inl ⟨p, hmp, q, hmq, hne⟩
      · exact Or.inr ⟨q, hq, hmq⟩
    · exact Or.inr ⟨p, hp, hmp⟩
  · rintro (⟨p, hp, q, hq, hne⟩ | ⟨p, hp, hnm⟩)
    · exact ⟨p, hp.prop, q, hq.prop, hne⟩
    · simp only [Maximal, hp, true_and, not_forall, exists_prop] at hnm
      obtain ⟨q, hq, hpq, hqp⟩ := hnm
      exact ⟨p, hp, q, hq, fun h ↦ hqp (h ▸ le_rfl)⟩

open Classical in
/-- The propositional closure removes the empty possibility from any proposition but `{∅}`. -/
noncomputable def pro : Set (Set W) := if P = {∅} then P else P \ {∅}

/-- A proposition restricted to an information set `k` keeps the part of each possibility that
lies in `k`. -/
noncomputable def restrict (k : Set W) : Set (Set W) := pro ((k ∩ ·) '' P)

/-- Exhaustification against a question `Q` removes from each possibility the worlds of the
alternatives it does not entail ([coppock-brochhagen-2013]'s (77)). -/
def exh (P Q : Set (Set W)) : Set (Set W) := (fun p ↦ p \ ⋃₀ {q ∈ Q | ¬ p ⊆ q}) '' P

variable {P}

theorem pro_eq_singleton {k : Set W} (hk : k ≠ ∅) (hkP : k ∈ P) (hP : P ⊆ {k, ∅}) :
    pro P = {k} := by
  have hne : P ≠ {∅} := fun h ↦ hk (mem_singleton_iff.1 (h ▸ hkP))
  simp only [pro, hne, ↓reduceIte]
  ext p
  refine ⟨fun ⟨hp, hp0⟩ ↦ ?_, ?_⟩
  · rcases hP hp with rfl | rfl
    · rfl
    · exact absurd rfl hp0
  · rintro rfl
    exact ⟨hkP, hk⟩

end Inquisitive.Unrestricted
