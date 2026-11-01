/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Binding.Basic
public import Linglib.Syntax.Tree.Command

/-!
# Binding configurations of phrase-structure trees

On a phrase-structure tree a position commands another when it c-commands it in Reinhart's sense,
neither dominating the other and every branching node above the first dominating the second. The
binding domain of a position is bounded by a set of nodes: it holds the positions that every
bounding node properly dominating the position dominates, the cone of the lowest such node.
Theories of binding differ in the bounding nodes, which may depend on the position. With the
clause nodes the domain is the minimal clause, the governing category of Government and Binding
approximated; with the spell-out domains of phases it is the domain of Charnavel and Sportiche.
The pronominal domain is bounded the same way by a second set of nodes, by default the first.
More bounding nodes give smaller domains.

## Main definitions

* `PhraseStructure.Tree.configuration`: c-command with the two domains of each position bounded
  by sets of nodes.
* `PhraseStructure.Tree.clauseConfiguration`: the configuration bounded by the clause nodes.
* `PhraseStructure.Tree.Accessible`, `PhraseStructure.Tree.withAccessibleSubject`: a subject
  accessible to a position, and the nodes that have one, which bound the domain of Government and
  Binding.

## Main statements

* `PhraseStructure.Tree.configuration_anti`: the configuration is antitone in the bounding nodes.

## References

* [reinhart-1976]
* [chomsky-1981]
* [barker-pullum-1990]
* [charnavel-sportiche-2016]
-/

@[expose] public section

namespace PhraseStructure.Tree

open Core.Order

variable {C W : Type*} (t : Tree C W) {P P' Q Q' : TreePath → Set TreePath}

/-- The binding configuration of `t` bounded by `P` and `Q` takes c-command as its command
relation and gives a position `b` the binding domain that every node of `P b` properly dominating
it dominates, and the pronominal domain that every node of `Q b` does. -/
def configuration (P : TreePath → Set TreePath) (Q : TreePath → Set TreePath := P) :
    Binding.Configuration TreePath where
  commands := t.CCommands
  domain b := {a | (b, a) ∈ commandRelation (P b)}
  pronominalDomain b := {a | (b, a) ∈ commandRelation (Q b)}

instance : DecidableRel (t.configuration P Q).commands :=
  inferInstanceAs (DecidableRel t.CCommands)

instance [∀ b, DecidablePred (· ∈ P b)] (b : TreePath) :
    DecidablePred (· ∈ (t.configuration P Q).domain b) :=
  fun a ↦ inferInstanceAs (Decidable ((b, a) ∈ commandRelation (P b)))

instance [∀ b, DecidablePred (· ∈ Q b)] (b : TreePath) :
    DecidablePred (· ∈ (t.configuration P Q).pronominalDomain b) :=
  fun a ↦ inferInstanceAs (Decidable ((b, a) ∈ commandRelation (Q b)))

/-- More bounding nodes give smaller domains and the same command. -/
theorem configuration_anti (h : ∀ b, P b ⊆ P' b) (h' : ∀ b, Q b ⊆ Q' b) :
    t.configuration P' Q' ≤ t.configuration P Q :=
  ⟨le_rfl, fun b _ ha ↦ upperPolar_anti _ (h b) ha, fun b _ ha ↦ upperPolar_anti _ (h' b) ha⟩

/-- The clause configuration of `t` is bounded by the clause nodes, so the binding domain of a
position is the minimal clause containing it. -/
abbrev clauseConfiguration {W : Type*} (t : Tree Cat W) : Binding.Configuration TreePath :=
  t.configuration fun _ ↦ labeled t {.S}

/-! ### Accessible subjects

A binding domain can be the smallest category containing a subject accessible to the position, one
that c-commands it and whose index the position could take without lying inside or around a node
that already bears that index. -/

variable (subject link : TreePath → Option TreePath)

/-- The subject `s` is accessible to the position `b` when it c-commands `b` and `b` neither lies
properly inside nor properly contains the node `link s` that bears the index of `s`. -/
def Accessible (s b : TreePath) : Prop := t.CCommands s b ∧ ∀ x ∈ link s, ¬ x < b ∧ ¬ b < x

instance (s b : TreePath) : Decidable (t.Accessible link s b) :=
  inferInstanceAs (Decidable (_ ∧ ∀ _ ∈ _, _))

/-- The nodes whose subject, as `subject` assigns them, is accessible to `b`. -/
def withAccessibleSubject (b : TreePath) : Set TreePath :=
  {m | ∃ s ∈ subject m, t.Accessible link s b}

instance (b : TreePath) : DecidablePred (· ∈ t.withAccessibleSubject subject link b) :=
  fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

end PhraseStructure.Tree
