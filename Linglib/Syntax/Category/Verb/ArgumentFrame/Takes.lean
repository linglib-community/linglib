/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Category.Verb.ArgumentFrame.Basic
public import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Frames and complementizers

Which complementizers a clausal position takes. A clausal position and a complementizer each have
a selection, the complement types, sentence types and subject realizations of a clause, and a
position takes a complementizer when its selection takes the complementizer's
(`Clause.Selection.Takes`): some clause is admitted by both, and both restrict a common respect.
A frame takes a complementizer when some complement does. A complement whose subject is
unpronounced takes no complementizer requiring a pronounced one, as *for* requires an overt
accusative subject. The selection of a valency is in `Syntax/Category/Verb/Takes.lean`.

Selection is by these three respects alone, so two complementizers with the same selection are
taken by the same positions; a lexical restriction beyond them, as of Bulgarian *deto* to some
emotive factives, is a list the language file records.

## Main definitions

* `ArgumentFrame.Position.Takes`: a position takes a complementizer.
* `ArgumentFrame.Takes`: a frame takes a complementizer.
* `ArgumentFrame.typedBy`: the frame whose one complement is the clause a complementizer types.

## Main results

* `ArgumentFrame.Position.exists_takes_iff`: some position takes a complementizer exactly when its
  selection admits a clause and restricts some respect.

## References

* [noonan-2007]
-/

@[expose] public section

namespace ArgumentFrame.Position

variable {p q : Position} {z : Complementizer} {s : Finset Clause.EmbeddedSubject}

/-- The clausal position `z` types, with `z`'s selection and the subject realizations narrowed
to those the selecting predicate admits. -/
def typedBy (z : Complementizer) (s : Finset Clause.EmbeddedSubject := Finset.univ) : Position :=
  .clausal { z.toSelection with subject := z.subject ∩ s }

@[simp] theorem kind_typedBy : (typedBy z s).kind = .clausal := rfl

@[simp] theorem selection_typedBy :
    (typedBy z s).selection = { z.toSelection with subject := z.subject ∩ s } := rfl

theorem selection_typedBy_univ : (typedBy z).selection = z.toSelection := by
  simp [typedBy, selection]

/-- The position takes the complementizer `z` when its selection takes `z`'s. A position that is
not clausal restricts no respect of a clause and takes nothing. -/
def Takes (p : Position) (z : Complementizer) : Prop := p.selection.Takes z.toSelection

instance : Decidable (p.Takes z) := inferInstanceAs (Decidable (Clause.Selection.Takes _ _))

/-- A position taking a complementizer is clausal. -/
theorem Takes.isClausal (h : p.Takes z) : p.IsClausal := by
  cases p <;> first | rfl | exact absurd h Clause.Selection.not_top_takes

/-- No position takes a complementizer restricting nothing. -/
theorem not_takes_of_eq_top (hz : z.toSelection = ⊤) : ¬ p.Takes z := by
  rw [Takes, hz]
  exact Clause.Selection.not_takes_top

/-- Some position takes a complementizer exactly when its selection admits a clause and restricts
some respect. -/
theorem exists_takes_iff :
    (∃ p : Position, p.Takes z) ↔ z.toSelection.admits.Nonempty ∧ z.toSelection ≠ ⊤ :=
  ⟨fun ⟨_, h⟩ ↦ ⟨by
      have h' := h.1
      rw [Finset.not_disjoint_iff] at h'
      exact h'.imp fun _ ha ↦ ha.2,
    fun hz ↦ not_takes_of_eq_top hz h⟩,
   fun h ↦ ⟨typedBy z, by
      rw [Takes, selection_typedBy_univ]
      exact Clause.Selection.takes_self_iff.2 h⟩⟩

end ArgumentFrame.Position

namespace ArgumentFrame

variable {fr fr' : ArgumentFrame} {z : Complementizer} {s : Finset Clause.EmbeddedSubject}

/-- The frame takes `z` when some complement does. -/
def Takes (fr : ArgumentFrame) (z : Complementizer) : Prop :=
  ∃ p ∈ fr.complements, p.Takes z

instance : Decidable (fr.Takes z) := inferInstanceAs (Decidable (∃ p ∈ fr.complements, _))

/-- Taking is monotone under complement extension. -/
theorem Takes.mono (hsub : fr.complements ⊆ fr'.complements) (h : fr.Takes z) : fr'.Takes z :=
  h.imp fun _ ⟨hp, ht⟩ ↦ ⟨hsub hp, ht⟩

/-- A frame taking a complementizer has a clausal complement. -/
theorem Takes.hasClausal (h : fr.Takes z) : fr.HasClausal :=
  h.imp fun _ ⟨hp, ht⟩ ↦ ⟨hp, ht.isClausal⟩

/-- No frame takes a complementizer restricting nothing. -/
theorem not_takes_of_eq_top (hz : z.toSelection = ⊤) : ¬ fr.Takes z :=
  fun ⟨_, _, h⟩ ↦ Position.not_takes_of_eq_top hz h

/-- Small clauses take no complementizer. -/
theorem not_takes_smallClause (z : Complementizer) : ¬ smallClause.Takes z := by
  rintro ⟨p, hp, ht⟩
  rw [List.mem_singleton.1 hp] at ht
  exact Clause.Selection.not_top_takes ht

/-- The frame whose one complement is the clause `z` types, with the subject realizations
narrowed to `s`: the frame a language file derives from its complementizer entry, where it would
otherwise retype the complementizer's selection. -/
def typedBy (z : Complementizer) (s : Finset Clause.EmbeddedSubject := Finset.univ) :
    ArgumentFrame :=
  ⟨some .nominal, [.typedBy z s]⟩

@[simp] theorem complements_typedBy : (typedBy z s).complements = [.typedBy z s] := rfl

end ArgumentFrame
