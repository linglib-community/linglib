/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Copy.Reading
public import Linglib.Syntax.Minimalist.Derivation.Reconstruction
public import Linglib.Syntax.Minimalist.SyntacticObject.ToTree

/-!
# The tree of a reading

This file sends a reading of a marked object to the constituency tree that the type-driven
composition engine interprets. A chain read high gets a binder under its higher copy, and its lower
copies become the traces that binder binds. [With binders aside](##eraseBinders_toTree) the tree is
the tree of the object the reading gives, and [with no lower copy](##toTree_ofLinearized) the tree
the object has as a linearized object.

## Implementation notes

* A lower copy that is itself the higher copy of a lower one, at an intermediate site of a chain
  read high, gets a trace and a binder, `[t [λ …]]`, which denotes what its second daughter does.
* A trace and its binder share the index of the mark, so a chain with no head has the index-free
  trace, which no binder binds, as `LinearizedSyntacticObject.toTree` promises. A head and a phrase
  it projects share an index, and capture each other if the head leaves the phrase and the phrase
  then moves above the head.
* A remnant read high, with a chain that moved out of it also read high, leaves a free trace and a
  vacuous binder. `PhraseStructure.Tree.Closed` tells such a reading from one the engine can close.
* Marcolli, Chomsky and Berwick apply their quotients to the lower copy. Deleting the higher copy is
  their deletion quotient applied to the copy object at the other occurrence, which they do not do
  (`Marked.mem_cutSummandsDN_lf`); it is the reading of Collins's work on the passive and on
  reconstruction.
* Binding at a reading is not in general binding at the copy object: an object that moves from
  itself, read low, comes to c-command the sister of its movement node. The reading `carrying` is
  the one that does agree with it (`Derivation.bindsAtReading_carrying_iff`).

## References

* [heim-kratzer-1998]
* [marcolli-chomsky-berwick-2025]
* [collins-2005]
* [collins-2026]
-/

@[expose] public section

namespace PhraseStructure.Tree

variable {C W : Type*}

/-- The tree with its binders removed, each binder giving way to its body. -/
def eraseBinders : Tree C W → Tree C W :=
  RoseTree.fold fun l cs ↦
    match l, cs with
    | .bind _ _, [c] => c
    | l, cs => RoseTree.node l cs

theorem eraseBinders_node {l : Tree.Label C W} (hl : ∀ n c, l ≠ .bind n c)
    (cs : List (Tree C W)) :
    eraseBinders (RoseTree.node l cs) = RoseTree.node l (cs.map eraseBinders) := by
  rw [eraseBinders, RoseTree.fold_node]
  cases l <;> first | rfl | exact absurd rfl (hl _ _)

@[simp] theorem eraseBinders_bind (n : ℕ) (c : C) (y : Tree C W) :
    eraseBinders (.bind n c y) = eraseBinders y := by
  simp [eraseBinders, RoseTree.fold_node]

end PhraseStructure.Tree

namespace Minimalist.LinearizedSyntacticObject.Marked

open RoseTree SyntacticObject PhraseStructure

/-- The constituency tree of a reading, the binder of a mark `some a` having the index of the trace
of `a`, and the index-free trace no binder. -/
def toTree (ι : LexicalItem.Token → ℕ) (t : Marked) (low : Finset SyntacticObject) :
    Tree Unit LexicalItem.Token :=
  reading (ReadLow low) (fun _ l ↦ RoseTree.node (Vertex.toLabel ι (.inr l)) [])
    (fun v cs ↦ RoseTree.node (Vertex.toLabel ι v) cs)
    (fun l y ↦ l.elim y fun a ↦ .bind (ι a + 1) () y) (fun _ _ y ↦ y) t.val

/-- An object with no lower copy has the tree it has as a linearized object. -/
@[simp] theorem toTree_ofLinearized (ι : LexicalItem.Token → ℕ) (p : LinearizedSyntacticObject)
    (low : Finset SyntacticObject) :
    (ofLinearized p).toTree ι low = p.toTree ι := by
  obtain ⟨s, hs⟩ := p
  simp only [toTree, ofLinearized, LinearizedSyntacticObject.toTree]
  clear hs
  induction s with
  | node a cs ih =>
    rw [map_node, reading_node]
    simp only [readStep, List.map_map, map_node]
    rcases cs with _ | ⟨x, _ | ⟨y, _ | ⟨z, zs⟩⟩⟩ <;>
      simp_all [lowerCopy?_map_none, Function.comp_def, Vertex.toLabel]

/-! ### Trees and objects -/

theorem toLabel_ne_bind (ι : LexicalItem.Token → ℕ) (v : Vertex) (n : ℕ) (c : Unit) :
    Vertex.toLabel ι v ≠ .bind n c := by
  rcases v with (_ | _) | (_ | _) <;> simp [Vertex.toLabel]

@[simp] theorem eraseBinders_elim (ι : LexicalItem.Token → ℕ) (l : Option LexicalItem.Token)
    (y : Tree Unit LexicalItem.Token) :
    Tree.eraseBinders (l.elim y fun a ↦ .bind (ι a + 1) () y) = Tree.eraseBinders y := by
  cases l <;> simp

/-- The tree of a reading is the tree of the object it gives, binders aside. -/
theorem eraseBinders_toTree (ι : LexicalItem.Token → ℕ) (t : Marked)
    (low : Finset SyntacticObject) :
    Tree.eraseBinders (t.toTree ι low) = (t.lf low).toTree ι := by
  obtain ⟨s, hs⟩ := t
  simp only [toTree, lf, LinearizedSyntacticObject.toTree]
  clear hs
  induction s with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    simp only [lfTree, lfBy] at ih ⊢
    rw [reading_node, reading_node]
    simp only [readStep]
    rcases cs with _ | ⟨x, _ | ⟨y, _ | ⟨z, zs⟩⟩⟩ <;> cases k <;> simp only [List.map] <;>
      (try split) <;> (try split) <;> (try split_ifs) <;>
      simp_all [Tree.eraseBinders_node, toLabel_ne_bind, map_node, Function.comp_def]

end Minimalist.LinearizedSyntacticObject.Marked

namespace Minimalist.Derivation

open SyntacticObject PhraseStructure
open LinearizedSyntacticObject (Marked)

variable {d : Derivation} {x y : SyntacticObject}

/-- The object a reading of the derivation gives. -/
def lf? (d : Derivation) (low : Finset SyntacticObject) : Option LinearizedSyntacticObject :=
  d.replayWithCopies?.map (·.current.lf low)

/-- The constituency tree of a reading of the derivation. -/
def toTree? (ι : LexicalItem.Token → ℕ) (d : Derivation) (low : Finset SyntacticObject) :
    Option (Tree Unit LexicalItem.Token) :=
  d.replayWithCopies?.map (·.current.toTree ι low)

/-- `x` c-commands `y` in the object a reading of the derivation gives. -/
def BindsAtReading (d : Derivation) (low : Finset SyntacticObject) (x y : SyntacticObject) : Prop :=
  ∃ p ∈ d.lf? low, CCommands p x y

instance (d : Derivation) (low : Finset SyntacticObject) (x y : SyntacticObject) :
    Decidable (d.BindsAtReading low x y) := by
  unfold BindsAtReading; infer_instance

/-- With no chain read low, a reading of the derivation gives what it externalizes. -/
@[simp] theorem lf?_empty (d : Derivation) : d.lf? ∅ = d.externalize? := by
  rw [lf?, externalize?, ← map_contract_replayWithCopies?, Option.map_map]
  exact Option.map_congr fun c _ ↦ Marked.lf_empty c.current

/-- Binding at the reading with no chain read low is surface binding. -/
theorem bindsAtReading_empty_iff : d.BindsAtReading ∅ x y ↔ d.BindsAtSurface x y := by
  simp [BindsAtReading, BindsAtSurface, CCommandsAt]

end Minimalist.Derivation
