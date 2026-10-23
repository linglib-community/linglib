module

public import Mathlib.Order.Disjoint
public import Mathlib.Data.Finset.Lattice.Basic
public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.ThetaRole
public import Linglib.Syntax.Category.Verb.ArgumentFrame.Basic

/-!
# Linked frames and fusion

This file defines argument structures as linked frames and the fusion of one argument structure
with another. A linked frame is an argument frame whose slots are linked to the thematic roles they
admit, each slot either required of whatever fills the frame or open. A verb's lexical argument
structure and the meaning of an argument structure construction are both linked frames. A clause
arises when the verb's argument structure is fused with an event structure: a correspondence
between their slots under which every pair of corresponding slots admits a common role, every slot
the verb requires is fused, and every slot the event structure requires is filled. The slots of
the event structure that nothing fuses with are contributed by it.

## Main definitions

* `RoleSlot`, `LinkedFrame`: a slot's admitted roles, and a frame with its slots linked
* `LinkedFrame.IsProfiled`: a slot is profiled when it is a core slot of the frame
* `LinkedFrame.Extends`: one argument structure admits at least the roles of another
* `IsFusion`: a correspondence of slots obeying coherence and the two obligations
* `contributed`: the slots of the event structure no slot of the verb fuses with
* `SubeventRelation`: how the verb's event relates to the event structure's

## Main results

* `IsFusion.exists_fused`: an event structure with a required slot shares a participant with every
  verb fused with it
* `isFusion_refl`: the identity correspondence fuses an argument structure with itself

## Implementation notes

The roles a slot admits form a set of `ThetaRole` labels, and two slots are compatible when their
sets meet. A correspondence is a map from slots to optional slots; `IsFusionOn` restates `IsFusion`
over the verb's slots so that it can be decided, and `ofFin` builds a correspondence from a map
between slot indices.

## References

* [goldberg-1995]
* [goldberg-jackendoff-2004]
* [levin-rappaport-hovav-2005]
-/

@[expose] public section

namespace ArgumentStructure

open ArgumentFrame (Slot)

/-- A `RoleSlot` records the thematic roles a slot admits and whether the slot is required,
whether of a verb that must express it or of a construction that must fuse it with a role of the
verb, a solid line in [goldberg-1995]'s diagrams (p. 51). -/
structure RoleSlot where
  /-- The roles the slot admits. -/
  admits : Finset ThetaRole
  /-- Whether the slot is required. -/
  obligatory : Bool := true
  deriving DecidableEq

/-- A `LinkedFrame` is an argument structure, an argument frame with the role each of its slots is
linked to. A verb's lexical argument structure (`Verb.linkedFrame?`) and the meaning of an argument
structure construction ([goldberg-1995] Fig. 2.4) are linked frames. -/
structure LinkedFrame where
  /-- The frame. -/
  frame : ArgumentFrame
  /-- The slots linked to roles. -/
  roles : List (Slot × RoleSlot)
  deriving DecidableEq

namespace LinkedFrame

variable (L : LinkedFrame)

/-- `L.admits s` is the set of roles the slot `s` admits, empty when `s` is not linked. -/
def admits (s : Slot) : Finset ThetaRole :=
  ((L.roles.lookup s).map (·.admits)).getD ∅

/-- `L.obligatory` lists the required slots. -/
def obligatory : List Slot :=
  (L.roles.filter fun x ↦ x.2.obligatory).map (·.1)

/-- A slot is profiled when it is a core slot of the frame, a subject or a nominal complement:
"Every argument role linked to a direct grammatical relation (SUBJ, OBJ, or OBJ2) is
constructionally profiled" ([goldberg-1995], p. 48). -/
abbrev IsProfiled (s : Slot) : Prop := s ∈ L.frame.coreSlots

/-- A linked frame is well formed when every slot it links is a slot of its frame. -/
def WF : Prop := ∀ x ∈ L.roles, x.1 ∈ L.frame.slots

instance : Decidable L.WF := inferInstanceAs (Decidable (∀ x ∈ L.roles, _))

/-- `L.Extends L'` holds when `L'` has the frame of `L` and admits at each slot every role `L`
admits there, as a paper's construal of a verb extends the argument structure its lexical entry
derives. -/
def Extends (L' : LinkedFrame) : Prop :=
  L.frame = L'.frame ∧ ∀ x ∈ L.roles, x.2.admits ⊆ L'.admits x.1

instance (L' : LinkedFrame) : Decidable (L.Extends L') := inferInstanceAs (Decidable (_ ∧ _))

end LinkedFrame

/-- A `SubeventRelation` is how the event a verb designates relates to the event structure it is
fused with ([goldberg-1995], p. 65; [goldberg-jackendoff-2004] §3). -/
inductive SubeventRelation where
  /-- The verb's event is a subtype of the event structure's, what the diagrams of
  [goldberg-1995] label "instance". -/
  | subtype
  /-- The verb's event is the means of the event structure's. -/
  | means
  /-- The verb's event is the result of the event structure's. -/
  | result
  /-- The verb's event is a precondition of the event structure's. -/
  | precondition
  /-- The verb's event is the manner of the event structure's. -/
  | manner
  /-- The verb's event is the means of identifying the event structure's. -/
  | identification
  /-- The verb's event is the intended result of the event structure's. -/
  | intendedResult
  /-- The two events merely co-occur ([goldberg-jackendoff-2004] (18a)). -/
  | coOccurrence
  deriving DecidableEq, Repr

variable (V C : LinkedFrame) (σ : Slot → Option Slot)

/-- `IsFusion V C σ` holds when `σ` fuses the argument structure `V` with the event structure `C`:
corresponding slots admit a common role, the Semantic Coherence Principle of [goldberg-1995]
(p. 50), `σ` lands in `C`'s frame, and every required slot on either side takes part. -/
structure IsFusion : Prop where
  /-- Corresponding slots admit a common role. -/
  coherent : ∀ s t, σ s = some t → ¬ Disjoint (V.admits s) (C.admits t)
  /-- The correspondence lands in the frame of the event structure. -/
  mem_target : ∀ s t, σ s = some t → t ∈ C.frame.slots
  /-- Every required slot of the verb is fused. -/
  obligatory_source : ∀ s ∈ V.obligatory, (σ s).isSome
  /-- Every required slot of the event structure is fused with a slot of the verb. -/
  obligatory_target : ∀ t ∈ C.obligatory, ∃ s ∈ V.frame.slots, σ s = some t

/-- `contributed V C σ` lists the slots of `C` that no slot of `V` fuses with, the roles a
construction contributes to a verb ([goldberg-1995], p. 54). -/
def contributed : List Slot :=
  C.frame.slots.filter fun t ↦ V.frame.slots.all fun s ↦ σ s != some t

/-- `IsFusionOn V C σ` restates `IsFusion V C σ` over the slots of `V`, a decidable form. -/
def IsFusionOn : Prop :=
  (∀ s ∈ V.frame.slots, ∀ t ∈ σ s, ¬ Disjoint (V.admits s) (C.admits t) ∧ t ∈ C.frame.slots) ∧
    (∀ s ∈ V.obligatory, (σ s).isSome) ∧ ∀ t ∈ C.obligatory, ∃ s ∈ V.frame.slots, σ s = some t

instance : Decidable (IsFusionOn V C σ) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- `ofFin vs cs f` is the correspondence that sends the `i`th slot of `vs` to the `f i`th slot of
`cs`, and every other slot nowhere. -/
def ofFin (vs cs : List Slot) (f : Fin vs.length → Option (Fin cs.length)) :
    Slot → Option Slot := fun s ↦
  match vs.idxOf? s with
  | some i => if hi : i < vs.length then (f ⟨i, hi⟩).map fun j ↦ cs[j] else none
  | none => none

variable {V C σ}

theorem mem_contributed_iff {t : Slot} :
    t ∈ contributed V C σ ↔ t ∈ C.frame.slots ∧ ∀ s ∈ V.frame.slots, σ s ≠ some t := by
  simp [contributed]

theorem isFusionOn_iff_isFusion (hσ : ∀ s, s ∉ V.frame.slots → σ s = none) :
    IsFusionOn V C σ ↔ IsFusion V C σ := by
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨fun s t hst ↦ ?_, fun s t hst ↦ ?_, h₂, h₃⟩
    · by_cases hs : s ∈ V.frame.slots
      · exact (h₁ s hs t hst).1
      · simp [hσ s hs] at hst
    · by_cases hs : s ∈ V.frame.slots
      · exact (h₁ s hs t hst).2
      · simp [hσ s hs] at hst
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨fun s _ t hst ↦ ⟨h₁ s t hst, h₂ s t hst⟩, h₃, h₄⟩

/-- An event structure with an obligatory role shares a participant with every verb fused with it,
the Shared Participant Condition of [goldberg-1995] (p. 65). -/
theorem IsFusion.exists_fused (h : IsFusion V C σ) (ha : C.obligatory ≠ []) :
    ∃ s t, σ s = some t :=
  let ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ ha
  let ⟨s, _, hs⟩ := h.obligatory_target t ht
  ⟨s, t, hs⟩

/-- The identity correspondence fuses a well-formed argument structure whose slots all admit some
role with itself, the case in which a verb's own argument structure is the clause's. -/
theorem isFusion_refl (hV : V.WF) (hne : ∀ s ∈ V.frame.slots, (V.admits s).Nonempty) :
    IsFusion V V fun s ↦ if s ∈ V.frame.slots then some s else none where
  coherent s t hst := by
    split_ifs at hst with hs
    cases hst
    exact fun hd ↦ (hne s hs).ne_empty (disjoint_self.mp hd)
  mem_target s t hst := by
    split_ifs at hst with hs
    cases hst
    exact hs
  obligatory_source s hs := by
    have : s ∈ V.frame.slots := by
      simp only [LinkedFrame.obligatory, List.mem_map, List.mem_filter] at hs
      obtain ⟨x, ⟨hx, _⟩, rfl⟩ := hs
      exact hV x hx
    simp [this]
  obligatory_target t ht := by
    have : t ∈ V.frame.slots := by
      simp only [LinkedFrame.obligatory, List.mem_map, List.mem_filter] at ht
      obtain ⟨x, ⟨hx, _⟩, rfl⟩ := ht
      exact hV x hx
    exact ⟨t, this, by simp [this]⟩

end ArgumentStructure
