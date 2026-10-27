/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Binding.Tree
public import Studies.Reinhart1976
public import Linglib.Fragments.English.Nouns
public import Linglib.Fragments.English.Pronouns
public import Linglib.Fragments.English.Verbs.Inventory

/-!
# Chomsky (1981): the binding theory

This file formalizes the binding theory of Government and Binding as an instance of the
framework-neutral conditions of `Syntax/Binding`. A noun phrase binds another when the two are
coindexed and the first c-commands the second; an anaphor is bound in its governing category
(Principle A), a pronominal is free there (Principle B), and an R-expression is free
(Principle C). The positions are the noun phrases of a phrase-structure tree, the command
relation is Reinhart's c-command, the binding domain of a noun phrase is the minimal clause
containing it (`PhraseStructure.Tree.clauseConfiguration`), the dependency is coindexation, and no
anaphor is exempt. An indexing is licit when coindexed noun phrases agree in φ-features
and it satisfies the three principles, and a tree is grammatical when some indexing is licit.

Since nothing is exempt, an anaphor that nothing in its clause c-commands is out under every
indexing, which excludes an anaphoric subject. For two noun phrases coindexed with each other
alone, Principle C is Reinhart's restriction (10b) read with c-command. The textbook paradigm
checks the instance: a reflexive object must corefer with its subject and agree with it, a
pronominal object cannot corefer with it, locality separates the two in an embedded clause, and
an R-expression cannot corefer with a c-commanding pronoun at any distance.

## Main definitions

* `Chomsky1981.configuration`: c-command and the minimal clause on the noun phrases of a tree.
* `Chomsky1981.Licit`, `Grammatical`, `CanCorefer`, `MustCorefer`.

## Implementation notes

A one-word noun phrase is a terminal of category `NP`, and the positions are those terminals.
The governing category is approximated by the minimal clause: the governor and the accessible
subject that refine it are not modelled, nor are noun phrases with subjects. Indexings range
over maps from the noun phrases to themselves, which realize every partition of them.

## TODO

The paradigm is the textbook one; check each sentence against Chapter 3 of the book, which was
not available, and move the verified ones to `Data/Examples`.

## References

* [N. Chomsky, *Lectures on government and binding* (1981)][chomsky-1981]
* [T. Reinhart, *The syntactic domain of anaphora* (1976)][reinhart-1976]
-/
@[expose] public section

namespace Chomsky1981

open Morphology (Word)
open Core.Order PhraseStructure PhraseStructure.Tree Binding
open RoseTree (CCommands)

/-! ### Clauses and their noun phrases -/

/-- `np w` is the one-word noun phrase `w`. -/
def np (w : Word) : Tree Cat Word := .terminal .N w

/-- `clause subj v comp` is the clause with subject `subj`, verb `v` and complement `comp`. -/
def clause (subj v : Word) (comp : Tree Cat Word) : Tree Cat Word :=
  .node .S [np subj, .node .V [.terminal .V v, comp]]

/-- `nominals t` lists the noun phrases of `t`, each with its position. -/
def nominals (t : Tree Cat Word) : List (TreePath × Word) :=
  t.positionedTerminals.filterMap fun x ↦ if x.2.1 = .N then some (x.1, x.2.2) else none

/-- `Nominal t` is the type of noun phrases of `t`. -/
abbrev Nominal (t : Tree Cat Word) : Type := {x // x ∈ nominals t}

variable {t : Tree Cat Word}

/-! ### The binding configuration -/

/-- The configuration on the noun phrases of `t` is the clause configuration of `t` restricted
to them. -/
abbrev configuration (t : Tree Cat Word) : Configuration (Nominal t) :=
  t.clauseConfiguration.comap (·.1.1)

/-- The binding class of a noun phrase is the binding class of its word. -/
def classOf (x : Nominal t) : Option BindingClass := bindingClassOf x.1.2

/-- An indexing is licit when coindexed noun phrases agree and coindexation satisfies the three
principles, with no anaphor exempt. -/
def Licit (t : Tree Cat Word) {κ : Type*} (idx : Nominal t → κ) : Prop :=
  (∀ a b, idx a = idx b → HasPhi.Agree a.1.2 b.1.2) ∧
    (configuration t).Satisfies (fun a b ↦ idx a = idx b) ∅ classOf

instance {κ : Type*} [DecidableEq κ] (idx : Nominal t → κ) : Decidable (Licit t idx) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A tree is grammatical when some indexing of its noun phrases is licit. -/
def Grammatical (t : Tree Cat Word) : Prop := ∃ idx : Nominal t → Nominal t, Licit t idx

/-- The noun phrases at `p` and `q` can corefer when some licit indexing coindexes them. -/
def CanCorefer (t : Tree Cat Word) (p q : TreePath) : Prop :=
  ∃ idx : Nominal t → Nominal t, Licit t idx ∧ ∀ a b, a.1.1 = p → b.1.1 = q → idx a = idx b

/-- The noun phrases at `p` and `q` must corefer when every licit indexing coindexes them. -/
def MustCorefer (t : Tree Cat Word) (p q : TreePath) : Prop :=
  ∀ idx : Nominal t → Nominal t, Licit t idx → ∀ a b, a.1.1 = p → b.1.1 = q → idx a = idx b

instance : Decidable (Grammatical t) := inferInstanceAs (Decidable (∃ _, _))

instance (p q : TreePath) : Decidable (CanCorefer t p q) := inferInstanceAs (Decidable (∃ _, _))

instance (p q : TreePath) : Decidable (MustCorefer t p q) := inferInstanceAs (Decidable (∀ _, _))

/-! ### Principle A without exemption -/

/-- An anaphor that nothing in its clause c-commands violates Principle A under every indexing,
so the tree is out. -/
theorem not_grammatical_of_not_locallyCommanded {b : Nominal t} {c : BindingClass}
    (hb : classOf b = some c) (hc : c.IsAnaphor)
    (hl : ¬ (configuration t).LocallyCommanded b) : ¬ Grammatical t :=
  fun ⟨_, _, h⟩ ↦ hl ((Configuration.condition_empty_iff hc).1 (h b c hb)).2

/-! ### Principle C and Reinhart's restriction -/

/-- For two noun phrases coindexed with each other alone, Principle C is Reinhart's restriction
(10b) with c-command. -/
theorem permits_iff {a b : Nominal t} (hab : a ≠ b) (pron : List TreePath) :
    Reinhart1976.Permits (CCommands t) pron a.1.1 b.1.1 ↔
      (b.1.1 ∉ pron → ¬ (configuration t).Bound (pair a b) b) ∧
        (a.1.1 ∉ pron → ¬ (configuration t).Bound (pair a b) a) := by
  rw [Configuration.bound_pair_iff hab, pair_comm, Configuration.bound_pair_iff hab.symm]
  simp only [Reinhart1976.Permits, not_imp_not]
  rfl

/-! ### The paradigm -/

section Paradigm

open English

private abbrev john := Nouns.john.toWord
private abbrev mary := Nouns.mary.toWord
private abbrev he := Pronouns.he.toWord
private abbrev him := Pronouns.him.toWord
private abbrev himself := Pronouns.himself.toWord
private abbrev herself := Pronouns.herself.toWord
private abbrev they := Pronouns.they.toWord
private abbrev themselves := Pronouns.themselves.toWord
private abbrev sees := Verbs.see.toWord .thirdSg
private abbrev see := Verbs.see.toWord .plainPresent
private abbrev likes := Verbs.like.toWord .thirdSg
private abbrev thinks := Verbs.think.toWord .thirdSg

/-- *John sees himself* is licit, and its reflexive must be coindexed with the subject. -/
example : Grammatical (clause john sees (np himself)) ∧
    MustCorefer (clause john sees (np himself)) ⟨[0]⟩ ⟨[1, 1]⟩ := by
  decide

/-- In *They see themselves* a plural subject licenses the plural reflexive. -/
example : Grammatical (clause they see (np themselves)) := by decide

/-- \**Himself sees John* is out, since nothing c-commands the subject anaphor. -/
example : ¬ Grammatical (clause himself sees (np john)) := by decide

/-- \**John sees herself* is out, since coindexation fails agreement and disjoint indexing fails
Principle A. -/
example : ¬ Grammatical (clause john sees (np herself)) := by decide

/-- *John sees him* is licit, but only with disjoint reference, by Principle B. -/
example : Grammatical (clause john sees (np him)) ∧
    ¬ CanCorefer (clause john sees (np him)) ⟨[0]⟩ ⟨[1, 1]⟩ := by
  decide

/-- *He sees John* is licit, but by Principle C the name cannot corefer with the pronoun that
c-commands it. -/
example : Grammatical (clause he sees (np john)) ∧
    ¬ CanCorefer (clause he sees (np john)) ⟨[0]⟩ ⟨[1, 1]⟩ := by
  decide

/-- In *John thinks Mary likes him* the pronoun is free in its own clause, so it may corefer
with the matrix subject. -/
example : CanCorefer (clause john thinks (clause mary likes (np him))) ⟨[0]⟩ ⟨[1, 1, 1, 1]⟩ := by
  decide

/-- \**John thinks Mary likes himself* is out, since the reflexive's domain is the embedded
clause, whose subject does not agree with it. -/
example : ¬ Grammatical (clause john thinks (clause mary likes (np himself))) := by decide

/-- In *He thinks Mary likes John* the name cannot corefer with the matrix pronoun, Principle C
not being local. -/
example : ¬ CanCorefer (clause he thinks (clause mary likes (np john))) ⟨[0]⟩ ⟨[1, 1, 1, 1]⟩ := by
  decide

/-- An embedding has three noun phrases, the matrix subject and the embedded subject and object. -/
example : (nominals (clause john thinks (clause mary likes (np him)))).map Prod.fst =
    [⟨[0]⟩, ⟨[1, 1, 0]⟩, ⟨[1, 1, 1, 1]⟩] := by decide

end Paradigm

end Chomsky1981
