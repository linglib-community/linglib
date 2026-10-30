module

public import Linglib.Semantics.Reference.ChoiceFunction
public import Linglib.Logic.Modal.Defs
public import Mathlib.Tactic.DeriveFintype

/-!
# Mirrazi (2024): Indefinites in Negated Intensional Contexts

*Rodica does not think that Carl read some of the books* has, in Farsi, a reading on which the
indefinite scopes above the negation but below *think*: Rodica believes that there are books Carl
did not read, without believing of any particular book that he did not read it. No syntactic
position is at once above the negation and below the attitude, so Mirrazi derives the reading
from a choice function closed above the negation whose world argument the attitude binds,
(44), and likewise for a modal, (48). An intensional choice function, applied to the intension
of its restrictor but not skolemized to a world, gives only the de re reading when the
restrictor is the same set in every belief world, (41)–(42): the fixed-set problem.

## Implementation notes

* Negation is below the attitude, as the paper's excluded-middle presupposition yields; the
  attitude and the modal are a box over an accessibility relation.
* The noun's world argument is bound together with the determiner's, as the paper assumes.
* The paper fixes only the books the function picks in three belief worlds, (45); the scenario
  makes those books the unread ones, one per world.

## References

* [mirrazi-2024]
-/

@[expose] public section

namespace Mirrazi2024

open Quantifier ModalLogic SetRel

variable {W E : Type*} {R : SetRel W W} {w₀ : W} {VP : E → W → Prop}

/-- A world-skolemized choice function closed above negation makes the sentence true iff every
accessible world has a restrictor member failing the predicate ((44), (48)). -/
theorem skolemized_iff {N : W → E → Prop} (hN : ∀ w, ∃ x, N w x) :
    (∃ F : W → ChoiceFunction E, Box R (fun w ↦ ¬ VP (F w (N w)) w) w₀) ↔
      Box R (fun w ↦ Det.some {x | N w x} {x | ¬ VP x w}) w₀ := by
  refine (ChoiceFunction.exists_pi_apply_iff hN fun w x ↦ w₀ ~[R] w → ¬ VP x w).trans <|
    forall_congr' fun w ↦ ?_
  obtain ⟨b, hb⟩ := hN w
  refine ⟨fun ⟨x, hx, h⟩ hw ↦ ⟨x, hx, h hw⟩, fun h ↦ ?_⟩
  by_cases hw : w₀ ~[R] w
  · obtain ⟨x, hx, h'⟩ := h hw
    exact ⟨x, hx, fun _ ↦ h'⟩
  · exact ⟨b, hb, (absurd · hw)⟩

/-- On a restrictor fixed across accessible worlds, an intensional choice function gives the de re
reading ((41), (42)). -/
theorem intensional_iff_of_fixed {N : W → E → Prop} {B : E → Prop} (hB : ∃ x, B x)
    (hN : ∀ w, w₀ ~[R] w → N w = B) :
    (∃ f : ChoiceFunction E, Box R (fun w ↦ ¬ VP (f (N w)) w) w₀) ↔
      Det.some {x | B x} {x | Box R (¬ VP x ·) w₀} := by
  refine Iff.trans ?_ (ChoiceFunction.exists_apply_iff_some hB fun x ↦ Box R (¬ VP x ·) w₀)
  exact exists_congr fun f ↦ forall₂_congr fun w hw ↦
    iff_of_eq (congrArg (fun N' ↦ ¬ VP (f N') w) (hN w hw))

/-! ### The context of (40) -/

namespace Scenario40

/-- The five books Carl has to read. -/
inductive Book where
  | a | b | c | d | e
  deriving DecidableEq, Fintype

/-- The actual world and three of Rodica's belief worlds. -/
inductive World where
  | actual | w₁ | w₂ | w₃
  deriving DecidableEq, Fintype

/-- Rodica's belief worlds are the three non-actual ones. -/
def beliefs : SetRel World World := {p | p.1 = .actual ∧ p.2 ≠ .actual}

instance : DecidableRel (· ~[beliefs] ·) := fun _ _ ↦
  inferInstanceAs (Decidable (_ ∧ _))

/-- The book Carl did not read in each belief world, as the function picks in (45). -/
def unread : World → Book → Prop
  | .w₁, x => x = .a
  | .w₂, x => x = .c
  | .w₃, x => x = .e
  | .actual, _ => False

instance : DecidableRel unread
  | .w₁, _ | .w₂, _ | .w₃, _ => inferInstanceAs (Decidable (_ = _))
  | .actual, _ => inferInstanceAs (Decidable False)

/-- Carl read the books other than the unread one. -/
def Read (x : Book) (w : World) : Prop := ¬ unread w x

/-- Some world-skolemized function makes (40) true in its context. -/
theorem skolemized :
    ∃ F : World → ChoiceFunction Book,
      Box beliefs (fun w ↦ ¬ Read (F w fun _ ↦ True) w) .actual :=
  (skolemized_iff (N := fun _ _ ↦ True) fun _ ↦ ⟨.a, trivial⟩).mpr <| by
    simp only [Box, Det.some, Set.Nonempty, Set.mem_inter_iff, Set.mem_ofPred_eq, Read, not_not]
    decide

/-- No intensional choice function makes (40) true in its context. -/
theorem not_intensional :
    ¬ ∃ f : ChoiceFunction Book, Box beliefs (fun w ↦ ¬ Read (f fun _ ↦ True) w) .actual := by
  rw [intensional_iff_of_fixed (N := fun _ _ ↦ True) (B := fun _ ↦ True) ⟨.a, trivial⟩
    fun _ _ ↦ rfl]
  simp only [Box, Det.some, Set.Nonempty, Set.mem_inter_iff, Set.mem_ofPred_eq, Read, not_not]
  decide

/-- The reading with the indefinite below the negation, that Rodica thinks Carl read none of the
books, is false in the context of (40). -/
theorem not_narrow : ¬ Box beliefs (fun w ↦ ¬ ∃ x, Read x w) .actual := by
  simp only [Box, Read]
  decide

end Scenario40

end Mirrazi2024
