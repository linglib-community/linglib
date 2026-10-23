module

public import Mathlib.Order.Disjoint
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Defs
public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.ThetaRole
public import Linglib.Syntax.Category.Verb.ArgumentFrame.Basic

/-!
# Linked frames and fusion

This file defines argument structures as linked frames, argument frames whose slots are linked to
the thematic roles they admit, and the fusion of a verb's argument structure with an event
structure in the sense of [goldberg-1995]. A fusion is the set of lines in Goldberg's diagrams,
each joining a slot of the verb to a slot of the event structure: a partial one-to-one
correspondence that joins compatible slots and takes in every required slot on either side.

## Main definitions

* `RoleSlot`, `LinkedFrame`: a slot's admitted roles, and a frame with its slots linked
* `LinkedFrame.IsProfiled`: a slot is profiled when it is a core slot of the frame
* `IsFusion`, `fusions`: fusions of one linked frame with another, and the finite set of them
* `contributed`: the slots of the event structure no line ends at
* `profilingMismatches`, `Corresponds`: the Correspondence Principle of [goldberg-1995]
* `SubeventRelation`: how the verb's event relates to the event structure's

## Main results

* `mem_fusions`: `fusions` lists every fusion
* `IsFusion.nonempty`: an event structure with a required slot shares a participant with every
  verb fused with it
* `isFusion_diag`: the diagonal fuses an argument structure with itself

## Implementation notes

A fusion is a finite set of lines rather than a map so that `fusions` can list every fusion. No
slot is on two lines: two participant roles fuse with one argument role only in a construction
that merges them, as reflexives do ([goldberg-1995], p. 58).

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

theorem mem_slots_of_mem_obligatory {L : LinkedFrame} (hL : L.WF) {s : Slot}
    (hs : s ∈ L.obligatory) : s ∈ L.frame.slots := by
  simp only [obligatory, List.mem_map, List.mem_filter] at hs
  obtain ⟨x, ⟨hx, _⟩, rfl⟩ := hs
  exact hL x hx

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

/-! ### Fusion -/

variable (V C : LinkedFrame) (σ : Finset (Slot × Slot))

/-- `IsFusion V C σ` holds when the lines `σ` fuse the argument structure `V` with the event
structure `C`: each line joins a slot of `V` to a slot of `C` that admits a common role, the
Semantic Coherence Principle of [goldberg-1995] (p. 50), no slot is on two lines, and every
required slot on either side is on a line. -/
structure IsFusion : Prop where
  /-- Each line joins a slot of `V` to a slot of `C`. -/
  subset : σ ⊆ V.frame.slots.toFinset ×ˢ C.frame.slots.toFinset
  /-- The slots a line joins admit a common role. -/
  coherent : ∀ x ∈ σ, ¬ Disjoint (V.admits x.1) (C.admits x.2)
  /-- No slot of `V` is on two lines. -/
  injOn_fst : Set.InjOn Prod.fst (σ : Set (Slot × Slot))
  /-- No slot of `C` is on two lines. -/
  injOn_snd : Set.InjOn Prod.snd (σ : Set (Slot × Slot))
  /-- Every required slot of the verb is fused. -/
  obligatory_source : ∀ s ∈ V.obligatory, s ∈ σ.image Prod.fst
  /-- Every required slot of the event structure is fused with a slot of the verb. -/
  obligatory_target : ∀ t ∈ C.obligatory, t ∈ σ.image Prod.snd

theorem isFusion_iff : IsFusion V C σ ↔
    σ ⊆ V.frame.slots.toFinset ×ˢ C.frame.slots.toFinset ∧
      (∀ x ∈ σ, ¬ Disjoint (V.admits x.1) (C.admits x.2)) ∧
      Set.InjOn Prod.fst (σ : Set (Slot × Slot)) ∧ Set.InjOn Prod.snd (σ : Set (Slot × Slot)) ∧
      (∀ s ∈ V.obligatory, s ∈ σ.image Prod.fst) ∧ ∀ t ∈ C.obligatory, t ∈ σ.image Prod.snd :=
  ⟨fun ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩,
    fun ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩⟩

instance : Decidable (IsFusion V C σ) := decidable_of_iff _ (isFusion_iff V C σ).symm

/-- `fusions V C` is the set of fusions of `V` with `C`. -/
def fusions : Finset (Finset (Slot × Slot)) :=
  (V.frame.slots.toFinset ×ˢ C.frame.slots.toFinset).powerset.filter (IsFusion V C)

/-- `contributed C σ` is the set of slots of `C` that no line of `σ` ends at, the roles a
construction contributes to a verb ([goldberg-1995], p. 54). -/
def contributed : Finset Slot := C.frame.slots.toFinset \ σ.image Prod.snd

/-- `profilingMismatches V C σ` is the set of lines of `σ` from a required slot of `V` to a
nonprofiled slot of `C`, as *put* fuses its place with the oblique goal of caused motion
([goldberg-1995], p. 53). -/
def profilingMismatches : Finset (Slot × Slot) :=
  σ.filter fun x ↦ x.1 ∈ V.obligatory ∧ ¬ C.IsProfiled x.2

/-- `Corresponds V C σ` holds when `σ` obeys the Correspondence Principle of [goldberg-1995]
(p. 50): every line from a required slot of `V` ends at a profiled slot of `C`, except that a
verb with three required slots may have one line end at a nonprofiled slot. -/
def Corresponds : Prop :=
  (profilingMismatches V C σ).card ≤ if V.obligatory.length = 3 then 1 else 0

instance : Decidable (Corresponds V C σ) := inferInstanceAs (Decidable (_ ≤ _))

variable {V C σ}

@[simp]
theorem mem_fusions : σ ∈ fusions V C ↔ IsFusion V C σ := by
  simpa [fusions] using fun h ↦ h.subset

theorem mem_contributed {t : Slot} :
    t ∈ contributed C σ ↔ t ∈ C.frame.slots ∧ ∀ s, (s, t) ∉ σ := by
  simp [contributed]

/-- An event structure with a required slot shares a participant with every verb fused with it,
the Shared Participant Condition of [goldberg-1995] (p. 65). -/
theorem IsFusion.nonempty (h : IsFusion V C σ) (hC : C.obligatory ≠ []) : σ.Nonempty :=
  let ⟨_, ht⟩ := List.exists_mem_of_ne_nil _ hC
  Finset.image_nonempty.mp ⟨_, h.obligatory_target _ ht⟩

/-- The diagonal fuses a well-formed argument structure whose slots all admit some role with
itself, the case in which a verb's own argument structure is the clause's. -/
theorem isFusion_diag (hV : V.WF) (hne : ∀ s ∈ V.frame.slots, (V.admits s).Nonempty) :
    IsFusion V V V.frame.slots.toFinset.diag where
  subset x hx := by
    obtain ⟨h₁, h₂⟩ := Finset.mem_diag.mp hx
    exact Finset.mem_product.mpr ⟨h₁, h₂ ▸ h₁⟩
  coherent x hx := by
    obtain ⟨h₁, h₂⟩ := Finset.mem_diag.mp hx
    exact h₂ ▸ fun hd ↦ (hne _ (List.mem_toFinset.mp h₁)).ne_empty (disjoint_self.mp hd)
  injOn_fst x hx y hy h := by
    simp only [Finset.mem_coe, Finset.mem_diag] at hx hy
    exact Prod.ext h (hx.2.symm.trans (h.trans hy.2))
  injOn_snd x hx y hy h := by
    simp only [Finset.mem_coe, Finset.mem_diag] at hx hy
    exact Prod.ext (hx.2.trans (h.trans hy.2.symm)) h
  obligatory_source s hs := by simpa using LinkedFrame.mem_slots_of_mem_obligatory hV hs
  obligatory_target s hs := by simpa using LinkedFrame.mem_slots_of_mem_obligatory hV hs

end ArgumentStructure
