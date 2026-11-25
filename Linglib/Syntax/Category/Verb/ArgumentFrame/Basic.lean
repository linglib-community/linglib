/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Clause.Basic
public import Linglib.Syntax.Clause.Complementation
public import Linglib.Syntax.Clause.ArgumentRole
public import Linglib.Syntax.Category.Adposition.Basic
public import Linglib.Core.Order.Flat
public import Linglib.Core.Data.List.Forall2

/-! # Argument frames

An *argument frame* of a predicate lists the positions it selects: its subject, if it selects one,
and its complements in order. The frame of a verb of putting is a nominal subject, a nominal
complement and a spatial adpositional complement. The subject is the complement external to the
verb phrase and the others are internal to it, in the terms of the Cambridge Grammar, whatever
participant fills it: the sole argument of an unaccusative verb is the subject of its frame.

A *position* is nominal, adpositional, clausal, implicit, incorporated or expletive, and records
what the predicate selects there: the type of case marked, in Blake's sense, and the adposition of
an adpositional position; Noonan's complement type, the sentence types and the subject of a
clausal one; the interpretation of an implicit one. Each record is optional. A position `q`
refines `p`, written `p ≤ q`, when the two are of one kind and `q` records everything `p` does,
and a frame refines another when the two have the same slots and it refines the other at each. A
schematic frame therefore lies below every frame instantiating it: the frame with an infinitival
complement lies below the frame whose infinitival complement has an unpronounced subject.

The core slots of a frame are those realized as nominals, and the comparative roles S, A, P, R
and T of its core slots are computed from their number and order.

## Main definitions

* `ArgumentFrame.Position`: an argument position, with what the predicate selects there.
* `ArgumentFrame.Position.axes`: what a position records, as a family of partial values.
* `ArgumentFrame`: a subject and complements, ordered by refinement.
* `ArgumentFrame.argumentRole`: the comparative role of a core slot.
* `ArgumentFrame.Site`: a slot of a frame or the subject of one of its complements.

## Implementation notes

* The subject is the subject position of the surface clause, `none` for a predicate that selects
  none, as an impersonal passive; a raising predicate selects a subject that none of its
  participants fills. Whether a verb's sole argument is an external or an internal argument in
  the thematic sense is a property of the verb's diatheses and voice, which the frame leaves
  open.
* The type of case of an adpositional position is that of the value its use marks, not of every
  value the adposition marks, since a grammaticised preposition has no meaning independent of its
  construction.
* The order compares what two positions record as flat partial values, through `Position.axes`,
  so that a position and a clause-typer are bundles of one type and selection between them is
  consistency of bundles.
* The roles S, A, P, R and T are computed from the frame, never stored.
* `ArgumentFrame` is not under `Verb` because complement-taking is cross-categorial: Noonan's
  complement-taking predicates include adjectives and nouns.
* A frame records positions and nothing of the dependencies between them: control is recorded on
  a diathesis, and attitude and opacity on `Clause.Embedding.Reading`.

## References

* [blake-2001]
* [bruening-2021]
* [comrie-1978]
* [creissels-2024]
* [fillmore-1986]
* [huddleston-pullum-2002]
* [levin-1993]
* [noonan-2007]
-/

@[expose] public section

/-- The interpretation of an unexpressed argument, after Fillmore and Bruening, with Levin's
understood-object alternations. -/
inductive ImplicitInterp where
  /-- An existentially bound argument, an unspecified someone or something. -/
  | indef
  /-- A pragmatically recoverable definite. -/
  | def
  /-- Understood as the subject itself (*Mary dressed*). -/
  | reflexive
  /-- Understood as the subject's members, each of the other (*Anne and Cathy met*). -/
  | reciprocal
  /-- Understood as a body part of the subject (*Mary waved*). -/
  | bodyPart
  deriving DecidableEq, Fintype, Repr

namespace ArgumentFrame

/-- An argument slot of a frame is that of the subject, `external`, or of the `i`-th
complement. -/
inductive Slot where
  | external
  | complement (i : ℕ)
  deriving DecidableEq, Repr

/-- An argument position of a frame is nominal; adpositional, with the type of case marked and the
adposition selected; clausal, with the coding, the sentence types and the realization of its
subject selected;
implicit, an unexpressed argument with its interpretation; incorporated, a bare noun incorporated
or pseudo-incorporated into the verb, expressing the argument without projecting a noun phrase
([creissels-2024] §17.1); or expletive. Every axis is optional, and `none` or `⊥`
selects nothing. -/
inductive Position where
  | nominal
  | adpositional (relation : Option Case.Kind := none)
      (adposition : Option Adposition := none)
  | clausal (coding : Option Clause.ComplementType := none)
      (types : Clause.Selection := ⊥)
      (subject : Option Clause.EmbeddedSubject := none)
  | implicit (interp : Option ImplicitInterp := none)
  | incorporated
  | expletive
  deriving DecidableEq, Repr

namespace Position

/-- The adpositional position selecting `p` in a use marking `c`, a function `p` marks, or no
function, as for the grammatically selected *at* of *laugh at* ([huddleston-pullum-2002] p. 654);
its type of case is that of `c`. -/
def adposition (p : Option Adposition := none) (c : Option Case.Function := none)
    (_h : ∀ a ∈ p, ∀ x ∈ c, x ∈ a.functions := by decide) : Position :=
  .adpositional (c.map Case.Function.kind) p

/-- The position's recorded coding, if clausal. -/
def coding? : Position → Option Clause.ComplementType
  | clausal c _ _ => c
  | _ => none

/-- The sentence types the position selects, if clausal; nothing otherwise. -/
def types : Position → Clause.Selection
  | clausal _ t _ => t
  | _ => ⊥

/-- The position's recorded subject realization, if clausal. -/
def subject? : Position → Option Clause.EmbeddedSubject
  | clausal _ _ e => e
  | _ => none

/-- The position's recorded relation, if adpositional. -/
def relation? : Position → Option Case.Kind
  | adpositional r _ => r
  | _ => none

/-- The position's recorded adposition, if adpositional. -/
def adposition? : Position → Option Adposition
  | adpositional _ p => p
  | _ => none

/-- The position's recorded interpretation, if implicit. -/
def interp? : Position → Option ImplicitInterp
  | implicit i => i
  | _ => none

/-! ### Kind -/

/-- The category of a position. -/
inductive Kind where
  | nominal
  | adpositional
  | clausal
  | implicit
  | incorporated
  | expletive
  deriving DecidableEq, Repr

/-- The category of the position. -/
def kind : Position → Kind
  | nominal => .nominal
  | adpositional .. => .adpositional
  | clausal .. => .clausal
  | implicit _ => .implicit
  | incorporated => .incorporated
  | expletive => .expletive

/-- The position is nominal, the core case. -/
abbrev IsNominal (p : Position) : Prop := p.kind = .nominal

/-- The position is adpositional. -/
abbrev IsAdpositional (p : Position) : Prop := p.kind = .adpositional

/-- The position is clausal. -/
abbrev IsClausal (p : Position) : Prop := p.kind = .clausal

/-- The position is expressed when it is nominal, adpositional or clausal. -/
abbrev IsExpressed (p : Position) : Prop := p.IsNominal ∨ p.IsAdpositional ∨ p.IsClausal

/-- The position is a finite clause when its coding is finite. -/
def IsFinite (p : Position) : Prop := ∃ c ∈ p.coding?, c.IsFinite

instance : DecidablePred IsFinite := fun p ↦ inferInstanceAs (Decidable (∃ c ∈ p.coding?, _))

/-! ### Axes and the refinement order -/

/-- The selectional axes a position records. A clausal position and a clause-typer share
`coding`, `types` and `subject`. -/
inductive Axis where
  | coding
  | types
  | subject
  | relation
  | adposition
  | interp
  deriving DecidableEq, Fintype, Repr

/-- An enumerated axis takes an optional value in the flat order, and the `types` axis takes a
selection of sentence types. -/
def Axis.Carrier : Axis → Type
  | coding => Flat Clause.ComplementType
  | types => Clause.Selection
  | subject => Flat Clause.EmbeddedSubject
  | relation => Flat Case.Kind
  | adposition => Flat Adposition
  | interp => Flat ImplicitInterp

instance : ∀ a : Axis, PartialOrder a.Carrier
  | .coding => inferInstanceAs (PartialOrder (Flat Clause.ComplementType))
  | .types => inferInstanceAs (PartialOrder Clause.Selection)
  | .subject => inferInstanceAs (PartialOrder (Flat Clause.EmbeddedSubject))
  | .relation => inferInstanceAs (PartialOrder (Flat Case.Kind))
  | .adposition => inferInstanceAs (PartialOrder (Flat Adposition))
  | .interp => inferInstanceAs (PartialOrder (Flat ImplicitInterp))

instance : ∀ a : Axis, OrderBot a.Carrier
  | .coding => inferInstanceAs (OrderBot (Flat Clause.ComplementType))
  | .types => inferInstanceAs (OrderBot Clause.Selection)
  | .subject => inferInstanceAs (OrderBot (Flat Clause.EmbeddedSubject))
  | .relation => inferInstanceAs (OrderBot (Flat Case.Kind))
  | .adposition => inferInstanceAs (OrderBot (Flat Adposition))
  | .interp => inferInstanceAs (OrderBot (Flat ImplicitInterp))

instance : ∀ a : Axis, DecidableEq a.Carrier
  | .coding => inferInstanceAs (DecidableEq (Flat Clause.ComplementType))
  | .types => inferInstanceAs (DecidableEq Clause.Selection)
  | .subject => inferInstanceAs (DecidableEq (Flat Clause.EmbeddedSubject))
  | .relation => inferInstanceAs (DecidableEq (Flat Case.Kind))
  | .adposition => inferInstanceAs (DecidableEq (Flat Adposition))
  | .interp => inferInstanceAs (DecidableEq (Flat ImplicitInterp))

instance : ∀ (a : Axis) (x y : a.Carrier), Decidable (Compat x y)
  | .coding => inferInstanceAs (∀ x y : Flat Clause.ComplementType, Decidable (Compat x y))
  | .types => inferInstanceAs (∀ x y : Clause.Selection, Decidable (Compat x y))
  | .subject => inferInstanceAs (∀ x y : Flat Clause.EmbeddedSubject, Decidable (Compat x y))
  | .relation => inferInstanceAs (∀ x y : Flat Case.Kind, Decidable (Compat x y))
  | .adposition => inferInstanceAs (∀ x y : Flat Adposition, Decidable (Compat x y))
  | .interp => inferInstanceAs (∀ x y : Flat ImplicitInterp, Decidable (Compat x y))

instance : ∀ a : Axis, DecidableLE a.Carrier
  | .coding => inferInstanceAs (DecidableLE (Flat Clause.ComplementType))
  | .types => inferInstanceAs (DecidableLE Clause.Selection)
  | .subject => inferInstanceAs (DecidableLE (Flat Clause.EmbeddedSubject))
  | .relation => inferInstanceAs (DecidableLE (Flat Case.Kind))
  | .adposition => inferInstanceAs (DecidableLE (Flat Adposition))
  | .interp => inferInstanceAs (DecidableLE (Flat ImplicitInterp))

/-- A family of partial axis values, ordered pointwise by extension. Unification is the join of
a pair and consistency is `Compat`. -/
abbrev Axes := ∀ a : Axis, a.Carrier

/-- The axes the position records. -/
def axes (p : Position) : Axes
  | .coding => p.coding?
  | .types => p.types
  | .subject => p.subject?
  | .relation => p.relation?
  | .adposition => p.adposition?
  | .interp => p.interp?

theorem eq_of_kind_eq_of_axes_eq {p q : Position} (hk : p.kind = q.kind)
    (ha : p.axes = q.axes) : p = q := by
  have h := fun a ↦ congrFun ha a
  have hc := h .coding
  have hf := h .types
  have he := h .subject
  have hr := h .relation
  have hp := h .adposition
  have hi := h .interp
  cases p <;> cases q <;>
    simp_all [kind, axes, coding?, types, subject?, relation?, adposition?, interp?]

/-- A position `q` refines `p`, `p ≤ q`, when the two are of one kind and every axis `p`
records, `q` records with the same value. -/
instance : PartialOrder Position where
  le p q := p.kind = q.kind ∧ p.axes ≤ q.axes
  le_refl _ := ⟨rfl, le_rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := eq_of_kind_eq_of_axes_eq h₁.1 (h₁.2.antisymm h₂.2)

theorem le_def {p q : Position} : p ≤ q ↔ p.kind = q.kind ∧ p.axes ≤ q.axes := Iff.rfl

theorem axes_mono : Monotone axes := fun _ _ h ↦ h.2

/-- `Position.axes` as a monotone map. -/
@[simps]
def axesHom : Position →o Axes := ⟨axes, axes_mono⟩

instance : DecidableLE Position := fun p q ↦
  inferInstanceAs (Decidable (p.kind = q.kind ∧ ∀ a, p.axes a ≤ q.axes a))

end Position

end ArgumentFrame

/-- An argument frame is the subject position, if any, and the complement positions in order: the
complement external to the verb phrase and those internal to it ([huddleston-pullum-2002]
p. 216). -/
@[ext]
structure ArgumentFrame where
  /-- The subject position; `none` for a predicate that selects no subject. -/
  external : Option ArgumentFrame.Position := some .nominal
  /-- The complement positions in order. -/
  complements : List ArgumentFrame.Position
  deriving DecidableEq, Repr

namespace ArgumentFrame

/-- A frame `g` refines `f`, `f ≤ g`, when both or neither has a subject and the subject and the
complements of `g` refine those of `f` one for one. -/
instance : PartialOrder ArgumentFrame where
  le f g := List.Forall₂ (· ≤ ·) f.external.toList g.external.toList ∧
    List.Forall₂ (· ≤ ·) f.complements g.complements
  le_refl _ := ⟨List.forall₂_refl _, List.forall₂_refl _⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm f g h₁ h₂ := by
    have h := h₁.1.antisymm h₂.1
    refine ArgumentFrame.ext ?_ (h₁.2.antisymm h₂.2)
    cases hf : f.external <;> cases hg : g.external <;> simp_all

theorem le_def {f g : ArgumentFrame} : f ≤ g ↔
    List.Forall₂ (· ≤ ·) f.external.toList g.external.toList ∧
      List.Forall₂ (· ≤ ·) f.complements g.complements := Iff.rfl

instance : DecidableLE ArgumentFrame := fun _ _ ↦
  inferInstanceAs (Decidable (List.Forall₂ _ _ _ ∧ List.Forall₂ _ _ _))

/-! ### Slots -/

variable (fr : ArgumentFrame)

/-- The position at a slot. -/
def get? : Slot → Option Position
  | .external => fr.external
  | .complement i => fr.complements[i]?

/-- The filled slots, external first. -/
def slots : List Slot :=
  (fr.external.map fun _ ↦ Slot.external).toList ++
    (List.range fr.complements.length).map .complement

/-- The core argument slots are those realized as nominals. -/
def coreSlots : List Slot :=
  fr.slots.filter fun s ↦ (fr.get? s).any fun p ↦ decide p.IsNominal

/-- The number of core arguments. -/
def valency : ℕ := fr.coreSlots.length

/-- A frame is transitive when it has two or more core arguments. -/
def IsTransitive : Prop := 2 ≤ fr.valency

instance : Decidable fr.IsTransitive := inferInstanceAs (Decidable (_ ≤ _))

/-- The core objects are the core complements. -/
def coreObjects : List Slot := fr.coreSlots.filter (· != .external)

/-- The comparative argument role of a core slot, computed from the frame. A nominal subject is S
without a core object and A with one; a sole core object is P; of two core objects, the first is R
and the second T. -/
def argumentRole : Slot → Option ArgumentRole
  | .external => if .external ∈ fr.coreSlots then some (if fr.coreObjects = [] then .S else .A)
      else none
  | s => match fr.coreObjects.length, fr.coreObjects.idxOf? s with
    | 1, some 0 => some .P
    | 2, some 0 => some .R
    | 2, some 1 => some .T
    | _, _ => none

/-! ### Shape predicates -/

/-- The frame has no complement. -/
def IsIntransitive : Prop := fr.complements = []

instance : Decidable fr.IsIntransitive := inferInstanceAs (Decidable (_ = _))

/-- Some complement of the frame is nominal. -/
def HasNominal : Prop := ∃ p ∈ fr.complements, p.IsNominal

instance : Decidable fr.HasNominal := inferInstanceAs (Decidable (∃ p ∈ _, _))

/-- Some complement of the frame is adpositional. -/
def HasAdpositional : Prop := ∃ p ∈ fr.complements, p.IsAdpositional

instance : Decidable fr.HasAdpositional := inferInstanceAs (Decidable (∃ p ∈ _, _))

/-- Some complement of the frame is clausal. -/
def HasClausal : Prop := ∃ p ∈ fr.complements, p.IsClausal

instance : Decidable fr.HasClausal := inferInstanceAs (Decidable (∃ p ∈ _, _))

/-- The subject of the frame is clausal, as in the clausal-subject frame of an object-experiencer
psychological verb. -/
def HasClausalSubject : Prop := ∃ p ∈ fr.external, p.IsClausal

instance : Decidable fr.HasClausalSubject := inferInstanceAs (Decidable (∃ p ∈ _, _))

/-- Some complement of the frame is a finite clause. -/
def HasFinite : Prop := ∃ p ∈ fr.complements, p.IsFinite

instance : Decidable fr.HasFinite := inferInstanceAs (Decidable (∃ p ∈ _, _))

/-- The frame with its `i`-th complement left unexpressed, interpreted as `a`. -/
def leaveImplicit (i : ℕ) (a : Option ImplicitInterp := none) : ArgumentFrame :=
  { fr with complements := fr.complements.set i (.implicit a) }

/-- Add a nominal object before the complements of a frame, as for an object-control or causative
verb before its infinitive or small clause in *persuade him to leave* or *make him leave*. -/
def withObject : ArgumentFrame := { fr with complements := .nominal :: fr.complements }

/-- A site of a frame, for a dependency between positions: one of its slots, or the subject of its
`i`-th complement. -/
inductive Site where
  | slot (s : Slot)
  | subjectOf (i : ℕ)
  deriving DecidableEq, Repr

/-- The indices of the frame's clausal complements. -/
def clausalIndices : List ℕ :=
  (List.range fr.complements.length).filter fun i ↦
    (fr.complements[i]?.map (·.kind)) = some .clausal

/-- The [noonan-2007] codings recorded across the frame's complements. -/
def codings : List Clause.ComplementType := fr.complements.filterMap (·.coding?)

/-- Some complement of the frame selects the sentence type `t`. -/
def hasType (t : Clause.SentenceType) : Prop := ∃ p ∈ fr.complements, t ∈ p.types

instance (t : Clause.SentenceType) : Decidable (fr.hasType t) :=
  inferInstanceAs (Decidable (∃ p ∈ _, _))

/-! ### Smart constructors -/

/-- The intransitive frame has a subject and no complement. -/
def intransitive : ArgumentFrame := ⟨some .nominal, []⟩

/-- The impersonal frame has an expletive subject and no complement. -/
def impersonal : ArgumentFrame := ⟨some .expletive, []⟩

/-- The transitive frame has one nominal complement. -/
def np : ArgumentFrame := ⟨some .nominal, [.nominal]⟩

/-- The object-drop frame is the transitive frame with its object left unexpressed, with
interpretation `a`. -/
def objectDrop (a : Option ImplicitInterp := none) : ArgumentFrame := np.leaveImplicit 0 a

/-- The double-object frame has two nominal complements. -/
def np_np : ArgumentFrame := ⟨some .nominal, [.nominal, .nominal]⟩

/-- The PP frame has one adpositional complement, selecting `p` in a use marking `c` when given. -/
def pp (p : Option Adposition := none) (c : Option Case.Function := none)
    (h : ∀ a ∈ p, ∀ x ∈ c, x ∈ a.functions := by decide) : ArgumentFrame :=
  ⟨some .nominal, [.adposition p c h]⟩

/-- The spatial PP frame has one spatial adpositional complement, whatever its adposition, as the
locative or directional phrase a verb of motion selects. -/
def spatialPP : ArgumentFrame := ⟨some .nominal, [.adpositional (some .spatial)]⟩

/-- The NP + PP frame has a nominal plus an adpositional complement, selecting `p` in a use marking
`c` when given. -/
def np_pp (p : Option Adposition := none) (c : Option Case.Function := none)
    (h : ∀ a ∈ p, ∀ x ∈ c, x ∈ a.functions := by decide) : ArgumentFrame :=
  ⟨some .nominal, [.nominal, .adposition p c h]⟩

/-- The NP + spatial PP frame has a nominal and a spatial adpositional complement, whatever its
adposition, as the destination of a verb of putting or the path of an induced action. -/
def np_spatialPP : ArgumentFrame := ⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩

/-- Finite declarative clause. -/
def finiteClause : ArgumentFrame :=
  ⟨some .nominal, [.clausal (coding := some .indicative) (types := .only .declarative)]⟩

/-- Finite declarative clause in the subjunctive. -/
def subjunctiveClause : ArgumentFrame :=
  ⟨some .nominal, [.clausal (coding := some .subjunctive) (types := .only .declarative)]⟩

/-- The clausal-subject frame has a finite declarative clause as its subject and a nominal
complement, as an object-experiencer psychological verb (*It worried Peti that ...*). -/
def clausalSubject : ArgumentFrame :=
  ⟨some (.clausal (coding := some .indicative) (types := .only .declarative)), [.nominal]⟩

/-- Infinitival clause, its subject unrecorded. Its subject is equi-deleted, raised, or marked by an
adposition ([noonan-2007] §1.3.4), depending on a slot of the frame under equi and raising. -/
def infinitival : ArgumentFrame := ⟨some .nominal, [.clausal (coding := some .infinitive)]⟩

/-- Gerund / nominalized clause. -/
def gerund : ArgumentFrame := ⟨some .nominal, [.clausal (coding := some .nominalized)]⟩

/-- Small clause (*consider X happy*; causative *make X leave*). It falls outside [noonan-2007]'s
inventory of complement types, so the position records nothing. -/
def smallClause : ArgumentFrame := ⟨some .nominal, [.clausal]⟩

/-- The frame of an embedded question. The sentence type is orthogonal to the [noonan-2007]
complement type, so `coding` stays `none`. -/
def question : ArgumentFrame := ⟨some .nominal, [.clausal (types := .interrogatives)]⟩

/-! ### The refinement order on frames -/

example : infinitival ≤ ⟨some .nominal, [.clausal (some .infinitive) ⊥ (some .null)]⟩ := by
  decide

example : (⟨some .clausal, [.nominal]⟩ : ArgumentFrame) ≤ clausalSubject := by decide

example : ¬ intransitive ≤ np := by decide

example : ¬ (⟨none, []⟩ : ArgumentFrame) ≤ intransitive := by decide

end ArgumentFrame
