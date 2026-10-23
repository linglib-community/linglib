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
More bounding nodes give smaller domains.

## Main definitions

* `PhraseStructure.Tree.configuration`: c-command with the domain of each position bounded by a
  set of nodes.
* `PhraseStructure.Tree.clauseConfiguration`: the configuration bounded by the clause nodes.

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

variable {C W : Type*} (t : Tree C W) {P Q : TreePath → Set TreePath}

/-- The binding configuration of `t` bounded by `P` takes c-command as its command relation and
gives a position `b` the domain that every node of `P b` properly dominating it dominates. -/
def configuration (P : TreePath → Set TreePath) : Binding.Configuration TreePath where
  commands := t.CCommands
  domain b := {a | (b, a) ∈ commandRelation (P b)}

instance : DecidableRel (t.configuration P).commands :=
  inferInstanceAs (DecidableRel t.CCommands)

instance [∀ b, DecidablePred (· ∈ P b)] (b : TreePath) :
    DecidablePred (· ∈ (t.configuration P).domain b) :=
  fun a ↦ inferInstanceAs (Decidable ((b, a) ∈ commandRelation (P b)))

/-- More bounding nodes give smaller domains and the same command. -/
theorem configuration_anti (h : ∀ b, P b ⊆ Q b) : t.configuration Q ≤ t.configuration P :=
  ⟨le_rfl, fun b _ ha ↦ upperPolar_anti _ (h b) ha⟩

/-- The clause configuration of `t` is bounded by the clause nodes, so the binding domain of a
position is the minimal clause containing it. -/
abbrev clauseConfiguration {W : Type*} (t : Tree Cat W) : Binding.Configuration TreePath :=
  t.configuration fun _ ↦ labeled t {.S}

end PhraseStructure.Tree
