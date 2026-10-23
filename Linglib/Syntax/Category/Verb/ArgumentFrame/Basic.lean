module

public import Linglib.Syntax.Clause.Basic
public import Linglib.Syntax.Clause.Complementation
public import Linglib.Syntax.Clause.ArgumentRole
public import Linglib.Syntax.Category.Adposition.Basic
public import Linglib.Core.Order.Flat
public import Linglib.Core.Data.List.Forall2

/-! # Argument frames

An *argument frame* of a predicate is its external argument, if any, and its complement
positions in order. A *position* is nominal, adpositional, clausal, implicit or expletive, and
records what the predicate selects there: the type of case (in Blake's sense) and the adposition
of an adpositional position; Noonan's coding, the sentence types and the subject requirement of a
clausal one; the interpretation of an implicit one. Positions and frames are partially ordered by
refinement, so a schematic frame lies below every frame instantiating it.

## Main definitions

* `ImplicitInterp`: the interpretation of an unexpressed argument.
* `ArgumentFrame.Position`: an argument position, with its selectional axes.
* `ArgumentFrame.Position.kind`, `Position.axes`: a position's category and recorded axes.
* `ArgumentFrame`: an external argument and complements, ordered by refinement.
* `ArgumentFrame.Slot`, `ArgumentFrame.coreSlots`, `ArgumentFrame.argumentRole`: argument slots,
  the core ones, and their comparative S/A/P/R/T roles.
* `ArgumentFrame.leaveImplicit`, `withObject`: a complement left unexpressed; an object added.
* `ArgumentFrame.intransitive`, `ArgumentFrame.np`, `ArgumentFrame.finiteClause`, …: frames.

## Implementation notes

The external argument is the subject position of the surface clause, `none` for a predicate that
selects no subject (an impersonal passive, a raising predicate). An unaccusative verb's sole
argument is its subject; unaccusativity is a property of the verb's diatheses
(`Verb.IsUnaccusative`). The roles S, A, P, R and T are computed from the frame's coding
(`ArgumentFrame.argumentRole`), never stored. `ArgumentFrame` is not under `Verb` because
complement-taking is cross-categorial: Noonan's complement-taking predicates include adjectives
and nouns. Control is a participant of a diathesis (`Diathesis.controller`); attitude and opacity
are recorded on `Verb.Reading`, the selection of clause-typers on `Verb.Takes`, and Deal's
CP-external shells in `Studies/Deal2026.lean`.

## References

* [blake-2001]
* [bruening-2021]
* [comrie-1978]
* [deal-2026]
* [fillmore-1986]
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

/-- An argument position of a frame is nominal; adpositional, with the type of case marked and the
adposition selected; clausal, with the coding, the sentence types and the subject requirement
selected; implicit, an unexpressed argument with its interpretation; or expletive. Every axis is
optional, and `none` or `⊥` selects nothing. -/
inductive Position where
  | nominal
  | adpositional (relation : Option Case.Kind := none)
      (adposition : Option Adposition := none)
  | clausal (coding : Option Clause.ComplementType := none)
      (types : Clause.Selection := ⊥)
      (embeddedSubject : Option Clause.EmbeddedSubject := none)
  | implicit (interp : Option ImplicitInterp := none)
  | expletive
  deriving DecidableEq, Repr

namespace Position

/-- The adpositional position selecting `p`, with the type of case `p` marks when it marks
one type. -/
def adposition (p : Adposition) : Position := .adpositional p.kind? (some p)

/-- The position's recorded coding, if clausal. -/
def coding? : Position → Option Clause.ComplementType
  | clausal c _ _ => c
  | _ => none

/-- The sentence types the position selects, if clausal; nothing otherwise. -/
def types : Position → Clause.Selection
  | clausal _ t _ => t
  | _ => ⊥

/-- The position's recorded subject requirement, if clausal. -/
def embeddedSubject? : Position → Option Clause.EmbeddedSubject
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
  | expletive
  deriving DecidableEq, Repr

/-- The category of the position. -/
def kind : Position → Kind
  | nominal => .nominal
  | adpositional .. => .adpositional
  | clausal .. => .clausal
  | implicit _ => .implicit
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

/-- The selectional axes a position records. A clausal position and a
    clause-typer share `coding` and `types` (`Complementizer.axes`). -/
inductive Axis where
  | coding
  | types
  | embeddedSubject
  | relation
  | adposition
  | interp
  deriving DecidableEq, Fintype, Repr

/-- An enumerated axis takes an optional value in the flat order, and the `types` axis takes a
selection of sentence types. -/
def Axis.Carrier : Axis → Type
  | coding => Flat Clause.ComplementType
  | types => Clause.Selection
  | embeddedSubject => Flat Clause.EmbeddedSubject
  | relation => Flat Case.Kind
  | adposition => Flat Adposition
  | interp => Flat ImplicitInterp

instance : ∀ a : Axis, PartialOrder a.Carrier
  | .coding => inferInstanceAs (PartialOrder (Flat Clause.ComplementType))
  | .types => inferInstanceAs (PartialOrder Clause.Selection)
  | .embeddedSubject => inferInstanceAs (PartialOrder (Flat Clause.EmbeddedSubject))
  | .relation => inferInstanceAs (PartialOrder (Flat Case.Kind))
  | .adposition => inferInstanceAs (PartialOrder (Flat Adposition))
  | .interp => inferInstanceAs (PartialOrder (Flat ImplicitInterp))

instance : ∀ a : Axis, OrderBot a.Carrier
  | .coding => inferInstanceAs (OrderBot (Flat Clause.ComplementType))
  | .types => inferInstanceAs (OrderBot Clause.Selection)
  | .embeddedSubject => inferInstanceAs (OrderBot (Flat Clause.EmbeddedSubject))
  | .relation => inferInstanceAs (OrderBot (Flat Case.Kind))
  | .adposition => inferInstanceAs (OrderBot (Flat Adposition))
  | .interp => inferInstanceAs (OrderBot (Flat ImplicitInterp))

instance : ∀ a : Axis, PartialUnify a.Carrier
  | .coding => inferInstanceAs (PartialUnify (Flat Clause.ComplementType))
  | .types => inferInstanceAs (PartialUnify Clause.Selection)
  | .embeddedSubject => inferInstanceAs (PartialUnify (Flat Clause.EmbeddedSubject))
  | .relation => inferInstanceAs (PartialUnify (Flat Case.Kind))
  | .adposition => inferInstanceAs (PartialUnify (Flat Adposition))
  | .interp => inferInstanceAs (PartialUnify (Flat ImplicitInterp))

instance : ∀ a : Axis, DecidableEq a.Carrier
  | .coding => inferInstanceAs (DecidableEq (Flat Clause.ComplementType))
  | .types => inferInstanceAs (DecidableEq Clause.Selection)
  | .embeddedSubject => inferInstanceAs (DecidableEq (Flat Clause.EmbeddedSubject))
  | .relation => inferInstanceAs (DecidableEq (Flat Case.Kind))
  | .adposition => inferInstanceAs (DecidableEq (Flat Adposition))
  | .interp => inferInstanceAs (DecidableEq (Flat ImplicitInterp))

instance : ∀ a : Axis, DecidableLE a.Carrier
  | .coding => inferInstanceAs (DecidableLE (Flat Clause.ComplementType))
  | .types => inferInstanceAs (DecidableLE Clause.Selection)
  | .embeddedSubject => inferInstanceAs (DecidableLE (Flat Clause.EmbeddedSubject))
  | .relation => inferInstanceAs (DecidableLE (Flat Case.Kind))
  | .adposition => inferInstanceAs (DecidableLE (Flat Adposition))
  | .interp => inferInstanceAs (DecidableLE (Flat ImplicitInterp))

/-- A family of partial axis values, ordered pointwise by extension. Unification is
    `PartialUnify.unify` and consistency is `Compat`. -/
abbrev Axes := ∀ a : Axis, a.Carrier

/-- The axes the position records. -/
def axes (p : Position) : Axes
  | .coding => p.coding?
  | .types => p.types
  | .embeddedSubject => p.embeddedSubject?
  | .relation => p.relation?
  | .adposition => p.adposition?
  | .interp => p.interp?

theorem eq_of_kind_eq_of_axes_eq {p q : Position} (hk : p.kind = q.kind)
    (ha : p.axes = q.axes) : p = q := by
  have h := fun a ↦ congrFun ha a
  have hc := h .coding
  have hf := h .types
  have he := h .embeddedSubject
  have hr := h .relation
  have hp := h .adposition
  have hi := h .interp
  cases p <;> cases q <;>
    simp_all [kind, axes, coding?, types, embeddedSubject?, relation?, adposition?, interp?]

/-- A position refines another, `p ≤ q`, when the two are of one kind and every axis `p`
    records, `q` records with the same value. -/
instance : PartialOrder Position where
  le p q := p.kind = q.kind ∧ p.axes ≤ q.axes
  le_refl _ := ⟨rfl, le_rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := eq_of_kind_eq_of_axes_eq h₁.1 (h₁.2.antisymm h₂.2)

theorem le_def {p q : Position} : p ≤ q ↔ p.kind = q.kind ∧ p.axes ≤ q.axes := Iff.rfl

instance : DecidableLE Position := fun p q ↦
  inferInstanceAs (Decidable (p.kind = q.kind ∧ ∀ a, p.axes a ≤ q.axes a))

end Position

end ArgumentFrame

/-- An argument frame is the external argument, if any, and the complement positions in
    order. -/
@[ext]
structure ArgumentFrame where
  /-- The external argument; `none` for a predicate that selects no subject. -/
  external : Option ArgumentFrame.Position := some .nominal
  /-- The complement positions in order. -/
  complements : List ArgumentFrame.Position
  deriving DecidableEq, Repr

namespace ArgumentFrame

/-- A frame refines another when it has the same external argument and complements refined
    pointwise. -/
instance : PartialOrder ArgumentFrame where
  le f g := f.external = g.external ∧ List.Forall₂ (· ≤ ·) f.complements g.complements
  le_refl _ := ⟨rfl, List.forall₂_refl _⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := ArgumentFrame.ext h₁.1 (h₁.2.antisymm h₂.2)

theorem le_def {f g : ArgumentFrame} : f ≤ g ↔
    f.external = g.external ∧ List.Forall₂ (· ≤ ·) f.complements g.complements := Iff.rfl

instance : DecidableLE ArgumentFrame := fun f g ↦
  inferInstanceAs (Decidable (f.external = g.external ∧ List.Forall₂ _ _ _))

/-! ### Slots -/

/-- An argument slot of a frame is the external argument or the `i`-th complement. -/
inductive Slot where
  | external
  | complement (i : ℕ)
  deriving DecidableEq, Repr

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

/-- The comparative argument role of a core slot, computed from the frame. A nominal subject is
    S without a core object and A with one; a sole core object is P; of two core objects, the
    first is R and the second T. -/
def argumentRole : Slot → Option ArgumentRole
  | .external => if .external ∈ fr.coreSlots then some (if fr.coreObjects = [] then .S else .A)
      else none
  | s => match fr.coreObjects.length, fr.coreObjects.idxOf? s with
    | 1, some 0 => some .P
    | 2, some 0 => some .R
    | 2, some 1 => some .T
    | _, _ => none

/-- The slot that carries object entailments is the last core object, which is the sole object of a
monotransitive frame and the second object of a double-object frame. -/
def objectSlot? : Option Slot := fr.coreObjects.getLast?

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

/-- The external argument of the frame is clausal, as in the clausal-subject frame of an
object-experiencer psychological verb. -/
def HasClausalSubject : Prop := ∃ p ∈ fr.external, p.IsClausal

instance : Decidable fr.HasClausalSubject := inferInstanceAs (Decidable (∃ p ∈ _, _))

/-- Some complement of the frame is a finite clause. -/
def HasFinite : Prop := ∃ p ∈ fr.complements, p.IsFinite

instance : Decidable fr.HasFinite := inferInstanceAs (Decidable (∃ p ∈ _, _))

/-- Some complement of the frame is implicit, an argument left unexpressed. -/
def HasImplicit : Prop := ∃ p ∈ fr.complements, p.kind = .implicit

instance : Decidable fr.HasImplicit := inferInstanceAs (Decidable (∃ p ∈ _, _))

/-- The frame with its `i`-th complement left unexpressed, interpreted as `a`. -/
def leaveImplicit (i : ℕ) (a : Option ImplicitInterp := none) : ArgumentFrame :=
  { fr with complements := fr.complements.set i (.implicit a) }

/-- Add a nominal object before the complements of a frame, as for an object-control or causative
verb before its infinitive or small clause in *persuade him to leave* or *make him leave*. -/
def withObject : ArgumentFrame := { fr with complements := .nominal :: fr.complements }

/-- The [noonan-2007] codings recorded across the frame's complements. -/
def codings : List Clause.ComplementType := fr.complements.filterMap (·.coding?)

/-- Some complement of the frame selects the sentence type `t`. -/
def hasType (t : Clause.SentenceType) : Prop := ∃ p ∈ fr.complements, t ∈ p.types

instance (t : Clause.SentenceType) : Decidable (fr.hasType t) :=
  inferInstanceAs (Decidable (∃ p ∈ _, _))

/-! ### Smart constructors -/

/-- The intransitive frame has an external argument and no complement. -/
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

/-- The PP frame has one adpositional complement, selecting `p` when given, with the type of
    case `p` marks when it marks one type. -/
def pp (p : Option Adposition := none) : ArgumentFrame :=
  ⟨some .nominal, [.adpositional (p.bind Adposition.kind?) p]⟩

/-- The spatial PP frame has one spatial adpositional complement, whatever its adposition, as
    the locative or directional phrase a verb of motion selects. -/
def spatialPP : ArgumentFrame := ⟨some .nominal, [.adpositional (some .spatial)]⟩

/-- The NP + PP frame has a nominal plus an adpositional complement, selecting `p`
    when given, with the type of case `p` marks when it marks one type. -/
def np_pp (p : Option Adposition := none) : ArgumentFrame :=
  ⟨some .nominal, [.nominal, .adpositional (p.bind Adposition.kind?) p]⟩

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

/-- Infinitival clause. Who the embedded subject is varies by verb (equi-deletion, raising, or
    adposition-marked overt subjects, [noonan-2007] §1.3.4), so it is recorded on the verb's
    diathesis (`Diathesis.controller`), not here. -/
def infinitival : ArgumentFrame := ⟨some .nominal, [.clausal (coding := some .infinitive)]⟩

/-- The raising frame has an infinitival clause and no external argument. -/
def raising : ArgumentFrame := ⟨none, [.clausal (coding := some .infinitive)]⟩

/-- Gerund / nominalized clause. -/
def gerund : ArgumentFrame := ⟨some .nominal, [.clausal (coding := some .nominalized)]⟩

/-- Small clause (*consider X happy*; causative *make X leave*). It falls outside
    [noonan-2007]'s coding inventory, which classifies complements by the part of speech of
    their predicate, so the position records nothing. -/
def smallClause : ArgumentFrame := ⟨some .nominal, [.clausal]⟩

/-- The frame of an embedded question. The sentence type is orthogonal to the
    [noonan-2007] coding, so `coding` stays `none`. -/
def question : ArgumentFrame := ⟨some .nominal, [.clausal (types := .interrogatives)]⟩

end ArgumentFrame
