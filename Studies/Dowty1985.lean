/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.ArgumentStructure.Control

/-!
# Dowty (1985): On Recent Analyses of the Semantics of Control

Dowty compares two analyses of the infinitive complements of Equi and Raising verbs. On the
first the complement denotes a proposition, whose subject the rules of control supply; on the
second, Montague's, it denotes a property like any other verb phrase, and control is an entailment
of the verb. He argues that nothing in the semantics favours the first. A relation to a
proposition whose subject must be the matrix argument is [a relation to a property and that
argument](##Dowty1985.rAnalysis_iff), "a function of just two things after all". Raising verbs
are the relations to a property that depend only on the proposition it forms with the subject,
which may be said by positing a property of propositions or [without
one](##Dowty1985.postulate13_iff_postulate15), and they are a proper subclass of the relations
of their type. An Equi verb entails something of its subject as such; [a verb with the raising
property entails of its subject only what it entails of everything](##Dowty1985.postulate9_trivial),
so the two classes are told apart by lexical entailments, not by logical type.

## Implementation notes

Propositions are sets of worlds, so the necessary equivalence of two propositions in the
postulates is their equality. A noun-phrase meaning is left as any type `N`: the postulates for
Raising verbs range over noun-phrase meanings in general, those for Equi verbs over the
sublimations of individuals, and the difference plays no part in the results here. The paper's
arguments from scope, from dummy subjects and from mixed Raising-Equi verbs are not formalized.

## References

* [dowty-1985]
-/

@[expose] public section

namespace Dowty1985

open ArgumentStructure

variable {W N : Type*}

/-- (8): the R-analysis of an intransitive Equi verb, a relation between a proposition and a
noun-phrase meaning, taken at the proposition the complement forms with that noun-phrase
meaning. -/
def ofRAnalysis (r : (W → Prop) → N → W → Prop) : (N → W → Prop) → N → W → Prop :=
  fun P a ↦ r (P a) a

-- p. 299
/-- A relation between a property and a noun-phrase meaning comes from an R-analysis exactly when
it reads the property only at that noun-phrase meaning, so the R-analysis describes a function of
two things. -/
theorem rAnalysis_iff {δ : (N → W → Prop) → N → W → Prop} :
    (∃ r, δ = ofRAnalysis r) ↔ IsControlledAt δ (id : N → N) :=
  isControlledAt_coe_iff.trans
    (exists_congr fun _ ↦ by simp only [funext_iff, ofRAnalysis, id]) |>.symm

/-- (13): the meaning of a Raising verb is a property `S` of the proposition its complement forms
with its subject. -/
def Postulate13 (δ : (N → W → Prop) → N → W → Prop) : Prop :=
  ∃ S : (W → Prop) → W → Prop, ∀ a P w, δ P a w ↔ S (P a) w

/-- (15): whenever two complements form necessarily equivalent propositions with two subjects, the
verb forms necessarily equivalent propositions with them. -/
def Postulate15 (δ : (N → W → Prop) → N → W → Prop) : Prop :=
  ∀ a b P Q, (∀ w, P a w ↔ Q b w) → ∀ w, δ P a w ↔ δ Q b w

theorem postulate15_iff_isRaisingAt {δ : (N → W → Prop) → N → W → Prop} :
    Postulate15 δ ↔ IsRaisingAt δ id :=
  ⟨fun h P Q a b hPQ ↦ funext fun w ↦ propext (h a b P Q (fun w ↦ iff_of_eq (congrFun hPQ w)) w),
    fun h _ _ _ _ hPQ w ↦ iff_of_eq (congrFun (h (funext fun w ↦ propext (hPQ w))) w)⟩

/-- The restriction on Raising verbs is the same whether or not it mentions a property of
propositions. -/
theorem postulate13_iff_postulate15 {δ : (N → W → Prop) → N → W → Prop} :
    Postulate13 δ ↔ Postulate15 δ := by
  rw [postulate15_iff_isRaisingAt, isRaisingAt_iff]
  exact exists_congr fun S ↦ ⟨fun h P a ↦ funext fun w ↦ propext (h a P w),
    fun h a P w ↦ iff_of_eq (congrFun (h P a) w)⟩

-- (16)
theorem Postulate15.passive {δ : (N → W → Prop) → N → W → Prop} (h : Postulate15 δ) {a b : N}
    {P Q : N → W → Prop} (hPQ : ∀ w, P a w ↔ Q b w) (w : W) : δ P a w ↔ δ Q b w :=
  h a b P Q hPQ w

-- (9), (19)
/-- A verb that satisfies the Raising postulate has only trivial entailments about its subject:
what it entails of its subject at a world, it entails there of every noun-phrase meaning. -/
theorem postulate9_trivial {δ : (N → W → Prop) → N → W → Prop} (h : Postulate15 δ)
    {α : N → W → Prop} (hα : ∀ P a w, δ P a w → α a w) {P : N → W → Prop} {a : N} {w : W}
    (hδ : δ P a w) (b : N) : α b w :=
  (postulate15_iff_isRaisingAt.1 h).le_of_le (fun P a w ↦ hα P a w) P a b w hδ

-- p. 304
/-- The Raising relations are a proper subclass of the relations between a property and a
noun-phrase meaning: the relation that holds when the subject has the property and is `true` reads
its subject as such. -/
example : ¬ Postulate15 fun (P : Bool → Unit → Prop) (a : Bool) w ↦ P a w ∧ a = true := fun h ↦ by
  have := h true false (fun _ _ ↦ True) (fun _ _ ↦ True) (fun _ ↦ Iff.rfl) ()
  simp at this

end Dowty1985
