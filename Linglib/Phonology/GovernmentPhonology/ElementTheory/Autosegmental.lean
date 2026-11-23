/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.GovernmentPhonology.ElementTheory.Basic
public import Linglib.Phonology.Autosegmental.Multiplanar
public import Linglib.Phonology.Autosegmental.Skeleton

/-!
# Elements on their lines

In Element Theory each element lies on a line of its own over the skeleton, and a position of the
skeleton is associated with the elements of its melodic expression. An element associated with a
vocalic position is a vowel, and the same element associated with a consonantal position is a
glide.

We define `Position`, a slot with a melodic expression, and `ofPosition`, its autosegmental
representation: one slot and, on the line of each element of the expression, one token, a head or
a dependent, linked to the slot. A form is a word of positions; `ofForm` concatenates their
representations, as the monoid homomorphism `ofFormHom` does on the free monoid, and its lines do
not cross (`noCrossing_ofForm`). A position of a form reads an element exactly when its
expression contains it (`reads_ofForm_iff`).

Fusion is a change of lines. `fuse w e m n` makes position `n` share the token of `e` of
position `m`, by `Autosegmental.AR.spreadTier`: the slot of `n` is delinked from its own token of
`e` and linked to that of `m`. It crosses no line exactly when no position strictly between the
two has `e` (`noCrossing_fuse_iff`).

## Implementation notes

The lines are the planes of `Autosegmental.Multiplanar` indexed by the elements, each hanging
from the skeleton. Government and licensing, which relate positions of the skeleton to one
another, are not lines and are not represented here.

## References

* [kaye-lowenstamm-vergnaud-1985]
* [backley-2011]
-/

@[expose] public section

open Autosegmental

namespace ElementTheory

/-- A token of an element is the head of its expression or a dependent. -/
inductive Status where
  | head
  | dependent
  deriving DecidableEq, Repr

/-- The status of the element `e` in the expression `m`. -/
def MR.status (m : MR) (e : Element) : Status := if e ∈ m.heads then .head else .dependent

/-- A position of the skeleton with its melodic expression. -/
structure Position where
  /-- The slot, consonantal or vocalic. -/
  slot : Slot
  /-- The melodic expression associated with the slot. -/
  melody : MR

/-- The alphabets of a representation of elements: a status on the line of each element, and
slots on the skeleton. -/
abbrev Lines : Option Element → Type := Multiplanar Element Status Slot

/-- The representation of a position: its slot and, on the line of each element of its
expression, a token linked to the slot. -/
def ofPosition (p : Position) : AR Lines :=
  AR.ofPlanes [p.slot] (fun e ↦ if e ∈ p.melody.elements then [p.melody.status e] else [])
    fun _ ↦ {(0, 0)}

/-- The representation of a form, those of its positions in order. -/
def ofForm (w : List Position) : AR Lines := (w.map ofPosition).prod

/-- `ofForm` as a monoid homomorphism out of the free monoid on the positions. -/
def ofFormHom : FreeMonoid Position →* AR Lines := FreeMonoid.lift ofPosition

@[simp] theorem ofFormHom_ofList (w : List Position) :
    ofFormHom (FreeMonoid.ofList w) = ofForm w :=
  FreeMonoid.lift_ofList _ _

variable {p : Position} {w : List Position} {e : Element} {s : Status} {k m n : ℕ}

theorem length_word_ofPosition_le_one (p : Position) :
    ∀ t, ((ofPosition p).word t).length ≤ 1
  | none => le_rfl
  | some e => by
    show (if e ∈ p.melody.elements then [p.melody.status e] else []).length ≤ 1
    split_ifs <;> simp

theorem noCrossing_ofPosition (p : Position) : (ofPosition p).NoCrossing :=
  fun t' _ ↦ AR.isNonCrossing_lines_iff.2 fun q _ q' _ _ h₂ hlt ↦ by
    have h : q' < ((ofPosition p).word t').length := h₂.lt_left
    have := length_word_ofPosition_le_one p t'
    omega

/-- The lines of a form do not cross. -/
theorem noCrossing_ofForm (w : List Position) : (ofForm w).NoCrossing :=
  AR.NoCrossing.prod fun X hX ↦ by
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hX
    exact noCrossing_ofPosition p

/-- The slot of a position is linked to a token of `e` exactly when its expression contains
`e`. -/
theorem link_ofPosition_iff :
    (ofPosition p).Link (AR.planes.parent (some e)) (some e) 0 0 ↔ e ∈ p.melody.elements := by
  rw [AR.planes_parent, AR.link_comm, ← AR.mem_lines]
  by_cases h : e ∈ p.melody.elements <;> simp [ofPosition, h]

/-- A position reads an element with the status the element has in its expression. -/
theorem reads_ofPosition_iff :
    (ofPosition p).Reads AR.planes 0 (some e) s ↔
      e ∈ p.melody.elements ∧ s = p.melody.status e := by
  rw [AR.reads_planes_iff]
  by_cases h : e ∈ p.melody.elements <;> simp [ofPosition, AR.hostedOn, h]

/-- Position `k` of a form reads the elements of its expression. -/
theorem reads_ofForm_iff :
    (ofForm w).Reads AR.planes k (some e) s ↔
      ∃ hk : k < w.length, e ∈ w[k].melody.elements ∧ s = w[k].melody.status e :=
  (AR.reads_prod_map AR.planes ofPosition fun _ ↦ rfl).trans
    (exists_congr fun _ ↦ reads_ofPosition_iff)

/-- Position `k` of a form reads an element exactly when its expression contains it. -/
theorem exists_reads_ofForm_iff :
    (∃ s, (ofForm w).Reads AR.planes k (some e) s) ↔ ∃ p ∈ w[k]?, e ∈ p.melody.elements := by
  simp only [reads_ofForm_iff, List.getElem?_eq_some_iff, Option.mem_def]
  exact ⟨fun ⟨_, hk, he, _⟩ ↦ ⟨_, ⟨hk, rfl⟩, he⟩, fun ⟨_, ⟨hk, rfl⟩, he⟩ ↦ ⟨_, hk, he, rfl⟩⟩

/-! ### Fusion -/

/-- `fuse w e m n` makes position `n` share the token of `e` of position `m`: the slot of `n` is
delinked from its own token of `e` and linked to that of `m`. -/
def fuse (w : List Position) (e : Element) (m n : ℕ) : AR Lines :=
  AR.spreadTier AR.planes ofPosition w (some e) m n

/-- Fusing an element between two positions crosses no line exactly when no position strictly
between them has the element. -/
theorem noCrossing_fuse_iff (hm : m < w.length) (hn : n < w.length)
    (he : e ∈ w[m].melody.elements) :
    (fuse w e m n).NoCrossing ↔
      ∀ k (hk : k < w.length), k ∈ Set.uIoo m n → e ∉ w[k].melody.elements := by
  refine (AR.noCrossing_spreadTier_iff (T := AR.planes) (g₀ := ofPosition)
    (Option.some_ne_none e) (fun p ↦ length_word_ofPosition_le_one p _)
    (fun p ↦ length_word_ofPosition_le_one p _) hm hn ?_ ?_ (noCrossing_ofForm w)).trans ?_
  · simp [ofPosition, he]
  · simp [ofPosition]
  · exact forall₃_congr fun _ _ _ ↦ not_congr link_ofPosition_iff

end ElementTheory
