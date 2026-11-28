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
public import Linglib.Core.Data.List.Forall2

/-! # Argument frames

An *argument frame* of a predicate lists the positions it selects: its subject, if it selects one,
and its complements in order. The frame of a verb of putting is a nominal subject, a nominal
complement and a spatial adpositional complement. The subject is the complement external to the
verb phrase and the others are internal to it, in the terms of the Cambridge Grammar, whatever
participant fills it: the sole argument of an unaccusative verb is the subject of its frame.

A *position* is nominal, adpositional, clausal, implicit, incorporated or expletive, and says what
may fill it: the types of case, in Blake's sense, that an adpositional position admits, and the
adposition it selects, if it selects one; the selection of a clausal position, the complement
types, sentence types and subject realizations of its clause; the interpretations an implicit
position admits. A set left out admits everything. A position is at most another, `p ≤ q`, when
the two are of one kind and `p` admits at most what `q` does, and a frame is at most another when
the two have the same slots and it is at most the other at each. The more specific frame is the
smaller: the frame whose infinitival complement has an unpronounced subject lies below the frame
with an infinitival complement, and a frame instantiates a schematic one by lying below it.

The core slots of a frame are those realized as nominals, and the comparative roles S, A, P, R
and T of its core slots are computed from their number and order.

## Main definitions

* `ArgumentFrame.Position`: an argument position, with what may fill it.
* `ArgumentFrame.Position.selection`: the selection of a clausal position.
* `ArgumentFrame`: a subject and complements, ordered slot by slot.
* `ArgumentFrame.argumentRole`: the comparative role of a core slot.
* `ArgumentFrame.Site`: a slot of a frame or the subject of one of its complements.

## Implementation notes

* The subject is the subject position of the surface clause, `none` for a predicate that selects
  none, as an impersonal passive; a raising predicate selects a subject that none of its
  participants fills. Whether a verb's sole argument is an external or an internal argument in
  the thematic sense is a property of the verb's diatheses and voice, which the frame leaves
  open.
* What a position admits is a set of values, not an optional value, so a verb taking the
  indicative or the subjunctive has one position admitting both, and the order is inclusion. A
  frame that records nothing of an axis admits everything on it; `ArgumentFrame.hasType` and
  `ArgumentFrame.codings` read only the positions that restrict the axis.
* The adposition is a lexical item of a type that is not finite, so the position records the item
  selected, and a position selecting none admits every adposition.
* The type of case of an adpositional position is that of the value its use marks, not of every
  value the adposition marks, since a grammaticised preposition has no meaning independent of its
  construction.
* The roles S, A, P, R and T are computed from the frame, never stored.
* `ArgumentFrame` is not under `Verb` because complement-taking is cross-categorial: Noonan's
  complement-taking predicates include adjectives and nouns.
* A frame records positions and nothing of the dependencies between them: control is recorded on
  a diathesis, and attitude and factivity on `Clause.Embedding.Reading`.

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

instance : Repr (Finset ImplicitInterp) :=
  ⟨fun s _ ↦ repr (ImplicitInterp.enumList.filter (· ∈ s))⟩

instance : Repr (Finset Case.Kind) :=
  ⟨fun s _ ↦ repr (Case.Kind.enumList.filter (· ∈ s))⟩

/-- An argument position of a frame is nominal; adpositional, with the types of case admitted and
the adposition selected, if one is; clausal, with the selection of its clause; implicit, an
unexpressed argument with the interpretations admitted; incorporated, a bare noun incorporated or
pseudo-incorporated into the verb, expressing the argument without projecting a noun phrase
([creissels-2024] §17.1); or expletive. A set left out admits everything. -/
inductive Position where
  | nominal
  | adpositional (relation : Finset Case.Kind := Finset.univ)
      (adposition : Option Adposition := none)
  | clausal (selection : Clause.Selection := ⊤)
  | implicit (interp : Finset ImplicitInterp := Finset.univ)
  | incorporated
  | expletive
  deriving DecidableEq, Repr

namespace Position

/-- The adpositional position selecting `p` in a use marking `c`, a function `p` marks, or no
function, as for the grammatically selected *at* of *laugh at* ([huddleston-pullum-2002] p. 654);
its type of case is that of `c`. -/
def adposition (p : Option Adposition := none) (c : Option Case.Function := none)
    (_h : ∀ a ∈ p, ∀ x ∈ c, x ∈ a.functions := by decide) : Position :=
  .adpositional (c.elim Finset.univ fun x ↦ {x.kind}) p

/-- The selection of the position's clause, if clausal; the selection admitting everything
otherwise. -/
def selection : Position → Clause.Selection
  | clausal k => k
  | _ => ⊤

/-- The types of case the position admits, if adpositional; every type otherwise. -/
def relation : Position → Finset Case.Kind
  | adpositional r _ => r
  | _ => Finset.univ

/-- The adposition the position selects, if adpositional and selecting one. -/
def adposition? : Position → Option Adposition
  | adpositional _ p => p
  | _ => none

/-- The interpretations the position admits, if implicit; every interpretation otherwise. -/
def interp : Position → Finset ImplicitInterp
  | implicit i => i
  | _ => Finset.univ

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

/-- The position is a finite clause when every complement type it admits is finite. -/
def IsFinite (p : Position) : Prop := ∀ c ∈ p.selection.coding, c.IsFinite

instance : DecidablePred IsFinite :=
  fun p ↦ inferInstanceAs (Decidable (∀ c ∈ p.selection.coding, _))

/-! ### The order -/

variable {p q : Position}

/-- A position is determined by its kind and what it admits. -/
theorem eq_of_kind_eq (hk : p.kind = q.kind) (hs : p.selection = q.selection)
    (hr : p.relation = q.relation) (ha : p.adposition? = q.adposition?)
    (hi : p.interp = q.interp) : p = q := by
  cases p <;> cases q <;> simp_all [kind, selection, relation, adposition?, interp]

/-- A position is at most another, `p ≤ q`, when the two are of one kind and `p` admits at most
what `q` does: its clause's selection, its types of case and its interpretations are at most
those of `q`, and it selects the adposition `q` selects, if `q` selects one. -/
instance : PartialOrder Position where
  le p q := p.kind = q.kind ∧ p.selection ≤ q.selection ∧ p.relation ⊆ q.relation ∧
    (∀ a ∈ q.adposition?, a ∈ p.adposition?) ∧ p.interp ⊆ q.interp
  le_refl _ := ⟨rfl, le_rfl, subset_rfl, fun _ h ↦ h, subset_rfl⟩
  le_trans _ _ _ := fun ⟨hk, hs, hr, ha, hi⟩ ⟨hk', hs', hr', ha', hi'⟩ ↦
    ⟨hk.trans hk', hs.trans hs', hr.trans hr', fun a h ↦ ha a (ha' a h), hi.trans hi'⟩
  le_antisymm _ _ := fun ⟨hk, hs, hr, ha, hi⟩ ⟨_, hs', hr', ha', hi'⟩ ↦
    eq_of_kind_eq hk (hs.antisymm hs') (hr.antisymm hr')
      (Option.ext fun a ↦ ⟨ha' a, ha a⟩) (hi.antisymm hi')

theorem le_def : p ≤ q ↔ p.kind = q.kind ∧ p.selection ≤ q.selection ∧
    p.relation ⊆ q.relation ∧ (∀ a ∈ q.adposition?, a ∈ p.adposition?) ∧
      p.interp ⊆ q.interp := Iff.rfl

instance : DecidableLE Position := fun p q ↦
  inferInstanceAs (Decidable (p.kind = q.kind ∧ p.selection ≤ q.selection ∧
    p.relation ⊆ q.relation ∧ (∀ a ∈ q.adposition?, a ∈ p.adposition?) ∧
      p.interp ⊆ q.interp))

theorem kind_eq_of_le (h : p ≤ q) : p.kind = q.kind := h.1

theorem selection_mono : Monotone selection := fun _ _ h ↦ h.2.1

/-- `Position.selection` as a monotone map. -/
@[simps]
def selectionHom : Position →o Clause.Selection := ⟨selection, selection_mono⟩

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

/-- A frame is at most another, `f ≤ g`, when both or neither has a subject and the subject and
the complements of `f` are at most those of `g` one for one. -/
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

/-- The frame with its `i`-th complement left unexpressed, with the interpretations `a`. -/
def leaveImplicit (i : ℕ) (a : Finset ImplicitInterp := Finset.univ) : ArgumentFrame :=
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

/-- The [noonan-2007] complement types the frame's complements are restricted to: those admitted
by a complement that does not admit them all. -/
def codings : Finset Clause.ComplementType :=
  Finset.univ.filter fun c ↦
    ∃ p ∈ fr.complements, p.selection.coding ≠ Finset.univ ∧ c ∈ p.selection.coding

/-- Some complement of the frame restricts the sentence types of its clause and admits `t`. -/
def hasType (t : Clause.SentenceType) : Prop :=
  ∃ p ∈ fr.complements, p.selection.types ≠ Finset.univ ∧ t ∈ p.selection.types

instance (t : Clause.SentenceType) : Decidable (fr.hasType t) :=
  inferInstanceAs (Decidable (∃ p ∈ _, _ ∧ _))

/-! ### Smart constructors -/

/-- The intransitive frame has a subject and no complement. -/
def intransitive : ArgumentFrame := ⟨some .nominal, []⟩

/-- The impersonal frame has an expletive subject and no complement. -/
def impersonal : ArgumentFrame := ⟨some .expletive, []⟩

/-- The transitive frame has one nominal complement. -/
def np : ArgumentFrame := ⟨some .nominal, [.nominal]⟩

/-- The object-drop frame is the transitive frame with its object left unexpressed, with the
interpretations `a`. -/
def objectDrop (a : Finset ImplicitInterp := Finset.univ) : ArgumentFrame := np.leaveImplicit 0 a

/-- The double-object frame has two nominal complements. -/
def np_np : ArgumentFrame := ⟨some .nominal, [.nominal, .nominal]⟩

/-- The PP frame has one adpositional complement, selecting `p` in a use marking `c` when given. -/
def pp (p : Option Adposition := none) (c : Option Case.Function := none)
    (h : ∀ a ∈ p, ∀ x ∈ c, x ∈ a.functions := by decide) : ArgumentFrame :=
  ⟨some .nominal, [.adposition p c h]⟩

/-- The spatial PP frame has one spatial adpositional complement, whatever its adposition, as the
locative or directional phrase a verb of motion selects. -/
def spatialPP : ArgumentFrame := ⟨some .nominal, [.adpositional {.spatial}]⟩

/-- The NP + PP frame has a nominal plus an adpositional complement, selecting `p` in a use marking
`c` when given. -/
def np_pp (p : Option Adposition := none) (c : Option Case.Function := none)
    (h : ∀ a ∈ p, ∀ x ∈ c, x ∈ a.functions := by decide) : ArgumentFrame :=
  ⟨some .nominal, [.nominal, .adposition p c h]⟩

/-- The NP + spatial PP frame has a nominal and a spatial adpositional complement, whatever its
adposition, as the destination of a verb of putting or the path of an induced action. -/
def np_spatialPP : ArgumentFrame := ⟨some .nominal, [.nominal, .adpositional {.spatial}]⟩

/-- Finite declarative clause. -/
def finiteClause : ArgumentFrame :=
  ⟨some .nominal, [.clausal { coding := {.indicative}, types := {.declarative} }]⟩

/-- Finite declarative clause in the subjunctive. -/
def subjunctiveClause : ArgumentFrame :=
  ⟨some .nominal, [.clausal { coding := {.subjunctive}, types := {.declarative} }]⟩

/-- The clausal-subject frame has a finite declarative clause as its subject and a nominal
complement, as an object-experiencer psychological verb (*It worried Peti that ...*). -/
def clausalSubject : ArgumentFrame :=
  ⟨some (.clausal { coding := {.indicative}, types := {.declarative} }), [.nominal]⟩

/-- Infinitival clause, its subject unrestricted. Its subject is equi-deleted, raised, or marked by
an adposition ([noonan-2007] §1.3.4), depending on a slot of the frame under equi and raising. -/
def infinitival : ArgumentFrame := ⟨some .nominal, [.clausal { coding := {.infinitive} }]⟩

/-- Gerund / nominalized clause. -/
def gerund : ArgumentFrame := ⟨some .nominal, [.clausal { coding := {.nominalized} }]⟩

/-- Small clause (*consider X happy*; causative *make X leave*). It falls outside [noonan-2007]'s
inventory of complement types, so the position restricts nothing. -/
def smallClause : ArgumentFrame := ⟨some .nominal, [.clausal]⟩

/-- The frame of an embedded question. The sentence type is orthogonal to the [noonan-2007]
complement type, so every complement type is admitted. -/
def question : ArgumentFrame :=
  ⟨some .nominal, [.clausal { types := Clause.SentenceType.interrogatives }]⟩

/-! ### The order on frames -/

example : (⟨some .nominal, [.clausal { coding := {.infinitive}, subject := {.null} }]⟩ :
    ArgumentFrame) ≤ infinitival := by decide

example : clausalSubject ≤ ⟨some .clausal, [.nominal]⟩ := by decide

example : ¬ infinitival ≤ question := by decide

example : ¬ np ≤ intransitive := by decide

example : ¬ intransitive ≤ ⟨none, []⟩ := by decide

end ArgumentFrame
