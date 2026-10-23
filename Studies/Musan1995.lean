module

public import Linglib.Semantics.Tense.Quantificational
public import Mathlib.Order.Nat

/-!
# Musan (1995): On the Temporal Interpretation of Noun Phrases

Musan's dissertation accounts pragmatically for life-time effects in its second chapter. Out
of the blue, *Gregory was from America* suggests that Gregory is dead
while *Gregory was silent* does not. Tenses quantify existentially over times, every
predicate carries a life-time presupposition that its argument exists at the predication
time (`holdsAt`), and an individual-level predicate holds of an individual at every time of
its life if at any (`IndividualLevel`). The present-tense sentence is then more informative
than the past-tense one, entailing it without being entailed by it (`present_entails_past`,
`past_not_entails_present`), so a speaker choosing the past tense implicates that the
property is over, and for an individual-level predicate that is to implicate that the
individual no longer exists (`lifetime_effect`); a stage-level predicate supports the first
implicature but not the second (`no_lifetime_effect_of_stage_level`).

## Implementation notes

Times are the points of a linear order, the past tense is the quantificational past of
`Semantics/Tense/Quantificational.lean`, and the present tense is evaluation at the utterance
time, where the dissertation quantifies over intervals surrounding it. The neutralization of
life-time effects in temporally specific contexts, the existence-independent predicates, and
the third chapter's account of the predication times of noun phrases are not represented.

## References

* [musan-1995]
-/

@[expose] public section

namespace Musan1995

open Semantics Tense ModalLogic

variable {T : Type*} [LinearOrder T]

/-- `holdsAt alive P` is the predicate `P` with its life-time presupposition, holding at a time
only of an individual alive at that time. -/
def holdsAt (alive P : T → Prop) (t : T) : Prop := alive t ∧ P t

/-- An individual-level predicate holds throughout the individual's life if it holds at all. -/
def IndividualLevel (alive P : T → Prop) : Prop :=
  (∃ t, holdsAt alive P t) → ∀ t, alive t → P t

variable {alive P : T → Prop} {now : T}

theorem present_entails_past (hP : IndividualLevel alive P) (hborn : ∃ t < now, alive t)
    (h : holdsAt alive P now) : ◇[toSetRel ⟦past⟧] (holdsAt alive P) now :=
  let ⟨t, ht, hat⟩ := hborn
  ⟨t, by simpa using ht, hat, hP ⟨now, h⟩ t hat⟩

theorem past_not_entails_present :
    ∃ alive P : ℕ → Prop, IndividualLevel alive P ∧
      ◇[toSetRel ⟦past⟧] (holdsAt alive P) 1 ∧ ¬ holdsAt alive P 1 :=
  ⟨(· = 0), fun _ ↦ True, fun _ _ _ ↦ trivial, ⟨0, by decide, rfl, trivial⟩,
    fun h ↦ Nat.one_ne_zero h.1⟩

theorem lifetime_effect (hP : IndividualLevel alive P)
    (h : ◇[toSetRel ⟦past⟧] (holdsAt alive P) now) (hover : ¬ P now) : ¬ alive now :=
  fun hnow ↦ hover (hP (let ⟨t, _, ht⟩ := h; ⟨t, ht⟩) now hnow)

theorem no_lifetime_effect_of_stage_level :
    ∃ alive P : ℕ → Prop, ◇[toSetRel ⟦past⟧] (holdsAt alive P) 1 ∧ ¬ P 1 ∧ alive 1 :=
  ⟨fun _ ↦ True, (· = 0), ⟨0, by decide, trivial, rfl⟩, Nat.one_ne_zero, trivial⟩

end Musan1995
