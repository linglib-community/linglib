module

public import Linglib.Semantics.Reference.Context.Basic
public import Linglib.Core.Order.SupCon
public import Linglib.Semantics.Mereology.Atomic

/-!
# The participants of a referent

At a context of utterance the participants of a referent are the discourse roles whose holders
are part of it, so that a referent is of the first person when the agent is part of it. A larger
referent [has at least the participants](##SpeechAct.Context.monotone_participants) of a smaller
one. Forming a group from two referents is their sum, and
[the participants of a sum are those of its summands](##SpeechAct.Context.participants_sup_iff)
exactly when each holder is an individual, part of a sum only by being part of a summand,
[as an atom is](##SpeechAct.Context.participants_sup_of_atom). Person
is then [a congruence for group formation](##SpeechAct.Context.personCon), which is why the
person of a coordination is a function of its conjuncts' persons, their union as sets of roles.

## References

* [dalrymple-kaplan-2000]
-/

@[expose] public section

namespace SpeechAct.Context


variable {W E P T : Type*} [PartialOrder E] (c : Context W E P T) (x : E)

open Classical in
/-- The participants of a referent at a context are the discourse roles whose holders are part of
it. -/
noncomputable def participants : Finset SpeechAct.Role :=
  Finset.univ.filter fun r ↦ c.holder r ≤ x

variable {c x} in
theorem mem_participants {r : SpeechAct.Role} : r ∈ c.participants x ↔ c.holder r ≤ x := by
  simp [participants]

@[simp] theorem speaker_mem_participants : .speaker ∈ c.participants x ↔ c.agent ≤ x :=
  mem_participants

@[simp] theorem addressee_mem_participants :
    .addressee ∈ c.participants x ↔ c.addressee ≤ x :=
  mem_participants

/-! ### Group formation

Forming a group from two referents is their sum. Person is a congruence for it and atomicity is
not, so the person of a coordination is a function of its conjuncts' persons while its number is
not a function of their numbers. -/

section SemilatticeSup

variable {W E P T : Type*} [SemilatticeSup E] (c : Context W E P T)

/-- A larger referent has at least the participants of a smaller one. -/
theorem monotone_participants : Monotone c.participants :=
  fun _ _ h _ hr ↦ mem_participants.2 ((mem_participants.1 hr).trans h)

/-- Forming a group is union on participants exactly when each role's holder is part of a sum
only by being part of a summand. -/
theorem participants_sup_iff :
    (∀ x y, c.participants (x ⊔ y) = c.participants x ∪ c.participants y) ↔
      ∀ r ⦃x y⦄, c.holder r ≤ x ⊔ y → c.holder r ≤ x ∨ c.holder r ≤ y := by
  refine ⟨fun h r x y hr ↦ ?_, fun h x y ↦ ?_⟩
  · have := mem_participants.2 hr
    rw [h, Finset.mem_union] at this
    exact this.imp mem_participants.1 mem_participants.1
  · ext r
    simp only [mem_participants, Finset.mem_union]
    exact ⟨fun hr ↦ h r hr, fun hr ↦ hr.elim le_sup_of_le_left le_sup_of_le_right⟩

/-- Where joins are sums, atomic holders are part of a sum only by being part of a summand. -/
theorem participants_sup_of_atom [Mereology.SupIsSum E] (hc : ∀ r, Mereology.Atom (c.holder r))
    (x y : E) : c.participants (x ⊔ y) = c.participants x ∪ c.participants y :=
  c.participants_sup_iff.2 (fun r _ _ ↦ (hc r).le_sup_iff.1) x y

variable (h : ∀ r ⦃x y⦄, c.holder r ≤ x ⊔ y → c.holder r ≤ x ∨ c.holder r ≤ y)

/-- The participants of a referent, as a map preserving sums. It is noncomputable as
`participants` is. -/
noncomputable def participantsHom : SupHom E (Finset SpeechAct.Role) where
  toFun := c.participants
  map_sup' := c.participants_sup_iff.2 h

@[simp] theorem participantsHom_apply (x : E) : c.participantsHom h x = c.participants x := rfl

/-- Person as a congruence for group formation: the referents with the same participants. -/
noncomputable def personCon : SupCon E := SupCon.ker (c.participantsHom h)

end SemilatticeSup

end SpeechAct.Context
