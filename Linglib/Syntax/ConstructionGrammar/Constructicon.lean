/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.ConstructionGrammar.Basic
public import Linglib.Core.Data.List.Forall2
public import Linglib.Core.Relation.ReflTransGen

/-!
# The constructicon

This file defines the constructicon, the network in which construction grammar stores
grammatical knowledge. Each node of a `Constructicon ι Sem` carries a construction; its
inheritance links run up to the constructions it inherits from, its mothers, and its horizontal
links relate it to constructions at its own level of abstraction, which motivate it without
passing information down. The inheritance links of an acyclic network generate a partial order,
Goldberg's directed acyclic graph of dominance, and default inheritance over that order is her
normal mode. A link may record one of her four relations, each of which constrains the forms it
joins, and a network is well typed when every inheritance link respects its relation.

## Main definitions

* `LinkType`, `LinkType.Admits`: the relations an inheritance link records, and what each
  requires of the forms it joins
* `Slot.Refines`: a slot specializes a slot of the construction it instantiates
* `Constructicon`: constructions at nodes, with inheritance and horizontal links
* `Constructicon.IsMother`, `Constructicon.partialOrder`, `Constructicon.decidableLE`: the
  inheritance order of an acyclic network
* `Constructicon.WellTyped`: every inheritance link respects the relation it records

## Main results

* `LinkType.Admits.inverse_subpart`: an instance link entails an inverse subpart link

## Implementation notes

Every node carries its construction in full, Goldberg's real copying, so a link's constraint
compares materialized forms; a horizontal link records a relation without being constrained by
it, since motivation passes no information.

## References

* [goldberg-1995]
* [diessel-2023]
* [goldberg-shirtz-2025]
* [ten-wolde-2023]
-/

@[expose] public section

namespace ConstructionGrammar

/-! ### Link types -/

/-- The relation an inheritance link records: [goldberg-1995]'s four major link types
(§3.3.2, p. 75). -/
inductive LinkType where
  /-- I_P: from a central sense to an extension, which inherits the syntax but differs in meaning
  (the senses of the ditransitive, pp. 75–77). -/
  | polysemy
  /-- I_M: source and target related by a systematic metaphor (caused motion to the resultative,
  change of state as change of location, p. 81). -/
  | metaphorical
  /-- I_S: the linked construction is a proper subpart of the other (intransitive motion inside
  caused motion, p. 78). -/
  | subpart
  /-- I_I: the linked construction is a more fully specified version of the other (*drive*-crazy
  as an instance of the resultative, p. 79). -/
  | instance
  deriving DecidableEq, Repr

variable {Lex : Type*}

/-- A slot refines a slot of the construction it instantiates when the two are equal, or the
latter is open and they differ at most in their fillers: an instance is a "partially lexically
filled" version of its construction ([goldberg-1995] p. 79), so refinement only fills open
fillers, keeping headedness, function and constraints; the category of the filling lexeme is not
checked. -/
def Slot.Refines (s t : Slot Lex) : Prop :=
  s = t ∨ (t.filler.IsOpen ∧ { s with filler := t.filler } = t)

instance [DecidableEq Lex] (s t : Slot Lex) : Decidable (s.Refines t) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- What a link type requires of the form `c` of the linked construction, given the form `m` of
the construction it inherits from: a polysemous extension keeps the central sense's form, a
metaphorical extension may change its form freely, a subpart's slots sit inside the whole's up
to refinement, and an instance refines its construction's slots one for one. -/
def LinkType.Admits : LinkType → TypedForm Lex → TypedForm Lex → Prop
  | .polysemy, c, m => c = m
  | .metaphorical, _, _ => True
  | .subpart, c, m => List.SublistForall₂ (fun s t ↦ Slot.Refines t s) c m ∧ c ≠ m
  | .instance, c, m => List.Forall₂ Slot.Refines c m ∧ c ≠ m

instance [DecidableEq Lex] : ∀ (t : LinkType) (c m : TypedForm Lex), Decidable (t.Admits c m)
  | .polysemy, c, m => inferInstanceAs (Decidable (c = m))
  | .metaphorical, _, _ => .isTrue trivial
  | .subpart, c, m =>
    inferInstanceAs (Decidable (List.SublistForall₂ (fun s t ↦ Slot.Refines t s) c m ∧ c ≠ m))
  | .instance, c, m => inferInstanceAs (Decidable (List.Forall₂ Slot.Refines c m ∧ c ≠ m))

/-- "Because an instance link always entails an inverse subpart link, only instance links will
be represented in the diagrams that follow" ([goldberg-1995] pp. 80–81): a form that refines
another slot for slot contains it as a proper subpart, so an instance and its construction
dominate each other, as Figure 3.5 draws *drive*-crazy and the resultative. The inverse link is
derived rather than listed among a network's `mothers`, which keeps the network acyclic. -/
theorem LinkType.Admits.inverse_subpart {c m : TypedForm Lex}
    (h : LinkType.instance.Admits c m) : LinkType.subpart.Admits m c :=
  ⟨List.sublistForall₂_iff.2 ⟨c, h.1.flip, List.Sublist.refl c⟩, h.2.symm⟩

/-! ### The network -/

/-- A constructicon over the nodes `ι`: the construction at each node, the inheritance links from
a node up to its mothers, and the horizontal links from a node to constructions at its level,
each with the relation it records if any. -/
structure Constructicon (ι Sem : Type*) where
  /-- The construction at each node. -/
  cxn : ι → Construction Sem
  /-- The mothers of each node, the constructions it inherits from. -/
  mothers : ι → List (ι × Option LinkType)
  /-- The constructions each node is related to at its own level, without inheritance. -/
  related : ι → List (ι × Option LinkType) := fun _ ↦ []

namespace Constructicon

variable {ι Sem : Type*} (N : Constructicon ι Sem)

/-- `m` is a mother of `c`: `c` inherits from `m` by an inheritance link. -/
def IsMother (c m : ι) : Prop := m ∈ (N.mothers c).map Prod.fst

instance [DecidableEq ι] : DecidableRel N.IsMother :=
  fun c m ↦ inferInstanceAs (Decidable (m ∈ (N.mothers c).map Prod.fst))

/-- The inheritance order of an acyclic network: `c ≤ m` when `c` inherits from `m` through a
chain of links. Acyclicity is [goldberg-1995]'s own condition on the network, a directed acyclic
graph of dominance (p. 73), and default inheritance over this order is her normal mode: a node
takes each property from the most specific nodes above it that specify one
(`DefaultInheritance.inherited`). -/
abbrev partialOrder (h : ∀ c, ¬ Relation.TransGen N.IsMother c c) : PartialOrder ι :=
  partialOrderOfAcyclic N.IsMother h

/-- The inheritance order is decidable given a list of every mother. -/
abbrev decidableLE [DecidableEq ι] (nodes : List ι) (h : ∀ c m, N.IsMother c m → m ∈ nodes)
    (c m : ι) : Decidable (Relation.ReflTransGen N.IsMother c m) :=
  decidableLEOfCovers nodes h c m

/-- Every inheritance link respects the relation it records. -/
def WellTyped : Prop :=
  ∀ c, ∀ e ∈ N.mothers c, ∀ t ∈ e.2, t.Admits (N.cxn c).form (N.cxn e.1).form

instance [Fintype ι] : Decidable N.WellTyped :=
  inferInstanceAs <| Decidable <|
    ∀ c, ∀ e ∈ N.mothers c, ∀ t ∈ e.2, t.Admits (N.cxn c).form (N.cxn e.1).form

end Constructicon

end ConstructionGrammar
