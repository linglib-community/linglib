module

public import Linglib.Semantics.Events.Lifespan
public import Linglib.Semantics.Tense.Quantificational
public import Mathlib.Order.Nat

/-!
# Musan (1995): On the Temporal Interpretation of Noun Phrases

Musan's dissertation accounts pragmatically for life-time effects in its second chapter. Out
of the blue, *Gregory was from America* suggests that Gregory is dead
while *Gregory was silent* does not. Tenses quantify existentially over times, every
predicate carries a life-time presupposition that its argument exists at the predication
time (`holdsAt`), and an individual-level predicate holds of an individual at every time of
its life if at any (`IndividualLevel`). Given that the individual was born before now, the
present-tense sentence is then more informative than the past-tense one, entailing it without
being entailed by it (`present_entails_past`, `past_not_entails_present`), so a speaker choosing
the past tense implicates that the property is over, and for an individual-level predicate that
is to implicate that the individual is dead, its life span ending before now (`lifetime_effect`);
a stage-level predicate supports the first implicature but not the second
(`no_lifetime_effect_of_stage_level`).

## Implementation notes

Times are the points of a linear order, the past tense is the quantificational past of
`Semantics/Tense/Quantificational.lean`, and the present tense is evaluation at the utterance
time, where the dissertation quantifies over intervals surrounding it. Life spans are intervals
`τ x` of `Semantics/Events/Lifespan.lean`, as in (12), where the times at which *Gregory was from
America* is true start at or after Gregory's birth and the longest ends at his death. That
Gregory was born before now is his pre-existing now (`Event.PreExists`), and an individual-level
predicate is `Event.Permanent` of the predicate with its presupposition (10), (17g). The
neutralization of life-time effects in temporally specific contexts, the existence-independent
predicates, and the third chapter's account of the predication times of noun phrases are not
represented.

## References

* [musan-1995]
-/

@[expose] public section

namespace Musan1995

open Tense ModalLogic Event
open scoped Denotes

variable {X T : Type*} [LinearOrder T]

/-- `holdsAt τ P x` is the predicate `P` of `x` with its life-time presupposition (10), holding at a
time only if the time is in the life span `τ x`. -/
def holdsAt (τ : X → NonemptyInterval T) (P : X → T → Prop) (x : X) (t : T) : Prop :=
  t ∈ τ x ∧ P x t

/-- An individual-level predicate holds of an individual throughout its life if it holds of it at
all (17g). -/
abbrev IndividualLevel (τ : X → NonemptyInterval T) (P : X → T → Prop) : Prop :=
  Permanent τ (holdsAt τ P)

variable {τ : X → NonemptyInterval T} {P : X → T → Prop} {g : X} {now : T}

theorem present_entails_past (hP : IndividualLevel τ P) (hborn : PreExists τ (· = g) (.pure now))
    (h : holdsAt τ P g now) : ◇[toSetRel ⟦past⟧] (holdsAt τ P g) now :=
  have hfst : (τ g).fst ∈ τ g := ⟨le_rfl, (τ g).fst_le_snd⟩
  ⟨(τ g).fst, by simpa using hborn, hP g ⟨now, h⟩ _ hfst⟩

theorem past_not_entails_present :
    ∃ (τ : Unit → NonemptyInterval ℕ) (P : Unit → ℕ → Prop), IndividualLevel τ P ∧
      ◇[toSetRel ⟦past⟧] (holdsAt τ P ()) 1 ∧ ¬ holdsAt τ P () 1 :=
  ⟨fun _ ↦ .pure 0, fun _ _ ↦ True, fun _ _ _ ht ↦ ⟨ht, trivial⟩,
    ⟨0, by decide, ⟨le_rfl, le_rfl⟩, trivial⟩, fun h ↦ absurd h.1.2 (by decide)⟩

/-- The life-time effect (17g): if an individual-level predicate held of Gregory in the past and
does not hold of him now, his life span precedes now. -/
theorem lifetime_effect (hP : IndividualLevel τ P) (h : ◇[toSetRel ⟦past⟧] (holdsAt τ P g) now)
    (hover : ¬ P g now) : (τ g).Precedes (.pure now) :=
  let ⟨_, hlt, ht⟩ := h
  hP.precedes_pure ht.1 ht (by simpa using hlt) fun h ↦ hover h.2

/-- Gregory, alive from `0` to `1` and from America while alive, was from America at `2` and is
not now. -/
example :
    IndividualLevel (fun _ : Unit ↦ (⟨(0, 1), zero_le_one⟩ : NonemptyInterval ℕ))
        (fun _ t ↦ t ≤ 1) ∧
      ◇[toSetRel ⟦past⟧] (holdsAt (fun _ ↦ ⟨(0, 1), zero_le_one⟩) (fun _ t ↦ t ≤ 1) ()) 2 ∧
      ¬ (2 : ℕ) ≤ 1 :=
  ⟨fun _ _ _ ht ↦ ⟨ht, ht.2⟩, ⟨0, by decide, ⟨le_rfl, zero_le_one⟩, zero_le_one⟩, by decide⟩

theorem no_lifetime_effect_of_stage_level :
    ∃ (τ : Unit → NonemptyInterval ℕ) (P : Unit → ℕ → Prop),
      ◇[toSetRel ⟦past⟧] (holdsAt τ P ()) 1 ∧ ¬ P () 1 ∧ 1 ∈ τ () :=
  ⟨fun _ ↦ ⟨(0, 1), zero_le_one⟩, fun _ ↦ (· = 0), ⟨0, by decide, ⟨le_rfl, zero_le_one⟩, rfl⟩,
    Nat.one_ne_zero, ⟨zero_le_one, le_rfl⟩⟩

end Musan1995
