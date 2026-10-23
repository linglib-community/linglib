module

public import Mathlib.Order.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Pustejovsky (1995): The Generative Lexicon

This file formalizes the type coercion of the seventh chapter of [pustejovsky-1995]. Type
coercion (16) converts an argument to the type a function expects where application would
otherwise fail, and function application with coercion (17) applies a function either
directly, when the argument has the selected type, or through one of the shifting operators
available to the argument, and otherwise produces a type error (`Shifter`, `Applies`). The
available operators are of two kinds. Subtype coercion (23) follows the inferences of a
single type lattice, the one of Figure 6.1 extended by the chains of §7.1.2, so that *drive*
accepts *a Honda* through Honda ≤ car ≤ vehicle (`SemType`, `subtype_readings`,
`subtype_within_lattice`). True complement coercion (§7.1.3) instead
reaches through the qualia: *begin* selects an event, *a book* is a dot object of
information and physical object whose telic and agentive qualia name reading and writing
events (29), and the two event readings of *John began a book* (27) are exactly the two
qualia projections (`begin_book_readings`), each leaving the type lattice
(`book_qualia_leave_lattice`). The coerced complement embeds the noun phrase in the event
expression (31), and on a model where a reading of the book is not a writing of it the two
readings differ (`telic_ne_agentive`). Where the noun has no event-typed alias, *Mary began
the rock* of the fourth chapter, coercion fails (`begin_rock_no_reading`).

## Implementation notes

Types are the sorts of the paper's examples with an explicit ancestor list each, the dot
object *book* inheriting from both information and physical object; a quale enters coercion
by the type it projects, its relational content only in the model of (31), and the formal and
constitutive qualia project no alias. The *want* and *believe* paradigms of §7.1 and the
aspectual coercion of the ninth chapter are not formalized.

## References

* [pustejovsky-1995]
-/

@[expose] public section

namespace Pustejovsky1995

/-! ### The type lattice (Figure 6.1, §7.1.2) -/

/-- The types of Figure 6.1 and of the examples of §7.1: the top `nomrqs` above entity, event,
and proposition; abstract, physical object, and information below entity; the chains of
(19), vehicle above car above Honda and text above book above the *Tractatus*, book being a
dot object of information and physical object; and rock, a plain physical object. -/
inductive SemType where
  | nomrqs
  | entity
  | event
  | proposition
  | abstract
  | physObj
  | information
  | vehicle
  | car
  | honda
  | text
  | book
  | tractatus
  | rock
  deriving DecidableEq, Repr, Fintype

/-- A type with its ancestors in the lattice, itself first. -/
def SemType.ancestors : SemType → List SemType
  | .nomrqs => [.nomrqs]
  | .entity => [.entity, .nomrqs]
  | .event => [.event, .nomrqs]
  | .proposition => [.proposition, .nomrqs]
  | .abstract => [.abstract, .entity, .nomrqs]
  | .physObj => [.physObj, .entity, .nomrqs]
  | .information => [.information, .entity, .nomrqs]
  | .vehicle => [.vehicle, .physObj, .entity, .nomrqs]
  | .car => [.car, .vehicle, .physObj, .entity, .nomrqs]
  | .honda => [.honda, .car, .vehicle, .physObj, .entity, .nomrqs]
  | .text => [.text, .information, .entity, .nomrqs]
  | .book => [.book, .text, .information, .physObj, .entity, .nomrqs]
  | .tractatus => [.tractatus, .book, .text, .information, .physObj, .entity, .nomrqs]
  | .rock => [.rock, .physObj, .entity, .nomrqs]

/-- Subtyping: `a ≤ b` when `b` is an ancestor of `a`. -/
instance : PartialOrder SemType where
  le a b := b ∈ a.ancestors
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableRel (α := SemType) (· ≤ ·) :=
  λ a b => inferInstanceAs (Decidable (b ∈ a.ancestors))

/-- The chains of (19) and (24): a Honda is a car is a vehicle, and the *Tractatus* is a book
is a text. -/
theorem chains :
    SemType.honda ≤ .car ∧ SemType.car ≤ .vehicle ∧ SemType.honda ≤ .vehicle ∧
      SemType.tractatus ≤ .book ∧ SemType.book ≤ .text := by
  decide

/-! ### Qualia and shifting operators -/

/-- The four qualia roles (§6.1). -/
inductive QualeRole where
  | constitutive
  | formal
  | telic
  | agentive
  deriving DecidableEq, Repr

/-- A lexical entry as coercion sees it: its type, and the type each quale projects where the
quale is specified. -/
structure Entry where
  type : SemType
  quale : QualeRole → Option SemType

/-- *book* (29): a dot object whose telic quale, *read*, and agentive quale, *write*, both name
events. -/
def book : Entry :=
  ⟨.book, λ | .telic => some .event | .agentive => some .event | _ => none⟩

/-- *Honda* (21): a car whose telic quale is driving and whose agentive quale is its creation. -/
def honda : Entry :=
  ⟨.honda, λ | .telic => some .event | .agentive => some .event | _ => none⟩

/-- The *Tractatus*: a book. -/
def tractatus : Entry :=
  ⟨.tractatus, λ | .telic => some .event | .agentive => some .event | _ => none⟩

/-- *rock*: a physical object naming no event in its qualia. -/
def rock : Entry := ⟨.rock, λ _ => none⟩

/-- A shifting operator available to an expression, the paper's Σ_α: the subtype coercion
(23) to a type of the lattice, or the projection of a quale. -/
inductive Shifter where
  | subtype (target : SemType)
  | quale (r : QualeRole)
  deriving DecidableEq, Repr

/-- The type a shifter yields on an entry, where it applies: a subtype coercion yields its target
when the entry's type lies below it, and a quale its projected type. -/
def Shifter.result (α : Entry) : Shifter → Option SemType
  | .subtype t => if α.type ≤ t then some t else none
  | .quale r => α.quale r

/-- An alias of type `t` is available to `α` when some shifter yields it. -/
def Alias (α : Entry) (t : SemType) : Prop := ∃ σ : Shifter, σ.result α = some t

/-- Function application with coercion (17): a function of type ⟨a, b⟩ applies to `α` directly
when `α` has type `a`, or through a shifter yielding `a`; each route is a reading. -/
def Applies (f : SemType × SemType) (α : Entry) : Option Shifter → Prop
  | none => α.type = f.1
  | some σ => σ.result α = some f.1

instance (f : SemType × SemType) (α : Entry) : DecidablePred (Applies f α) := λ σ => by
  cases σ <;> unfold Applies <;> infer_instance

theorem exists_coerced_iff_alias (f : SemType × SemType) (α : Entry) :
    (∃ σ, Applies f α (some σ)) ↔ Alias α f.1 :=
  Iff.rfl

theorem subtype_within_lattice (α : Entry) {t t' : SemType}
    (h : (Shifter.subtype t).result α = some t') : α.type ≤ t' := by
  by_cases hle : α.type ≤ t
  · simp [Shifter.result, hle] at h
    exact h ▸ hle
  · simp [Shifter.result, hle] at h

/-! ### Subtype coercion (§7.1.2) and true complement coercion (§7.1.3) -/

/-- *drive* selects a vehicle. -/
def drive : SemType × SemType := (.vehicle, .proposition)

/-- *read* selects a text. -/
def read : SemType × SemType := (.text, .proposition)

/-- *begin* selects an event (28). -/
def begin : SemType × SemType := (.event, .proposition)

/-- (19) and (24): *drive a Honda* and *read the Tractatus* have exactly one reading each, the
subtype coercion along the chain. -/
theorem subtype_readings :
    (∀ σ, Applies drive honda σ ↔ σ = some (.subtype .vehicle)) ∧
      ∀ σ, Applies read tractatus σ ↔ σ = some (.subtype .text) := by
  refine ⟨λ σ => ?_, λ σ => ?_⟩ <;> cases σ with
  | none => decide
  | some σ => cases σ with
    | subtype t => cases t <;> decide
    | quale r => cases r <;> decide

/-- (27), (29): *John began a book* has exactly two readings, the telic and the agentive
projections of the qualia of *book*, reading it and writing it. -/
theorem begin_book_readings (σ : Option Shifter) :
    Applies begin book σ ↔ σ = some (.quale .telic) ∨ σ = some (.quale .agentive) := by
  cases σ with
  | none => decide
  | some σ => cases σ with
    | subtype t => cases t <;> decide
    | quale r => cases r <;> decide

theorem book_qualia_leave_lattice (r : QualeRole) {t : SemType}
    (h : (Shifter.quale r).result book = some t) : ¬ book.type ≤ t := by
  cases r <;> simp [Shifter.result, book] at h <;> subst h <;> decide

/-- With no event in its qualia, *began the rock* is a type error, clause (iii) of (17). -/
theorem begin_rock_no_reading (σ : Option Shifter) : ¬ Applies begin rock σ := by
  cases σ with
  | none => decide
  | some σ => cases σ with
    | subtype t => cases t <;> decide
    | quale r => cases r <;> decide

/-! ### The coerced complement (31) -/

/-- A model of the coerced complement: events, individuals, and the reading and writing
relations the qualia of *book* name. -/
structure Model where
  Event : Type
  Entity : Type
  read : Event → Entity → Entity → Prop
  write : Event → Entity → Entity → Prop

/-- *a book* coerced through its telic quale, λx λe [read(e, x, a_book)] (31). -/
def Model.telicReading (M : Model) (b : M.Entity) : M.Entity → M.Event → Prop :=
  λ x e => M.read e x b

/-- *a book* coerced through its agentive quale, λx λe [write(e, x, a_book)]. -/
def Model.agentiveReading (M : Model) (b : M.Entity) : M.Entity → M.Event → Prop :=
  λ x e => M.write e x b

theorem telic_ne_agentive (M : Model) {b x : M.Entity} {e : M.Event} (h : M.read e x b)
    (h' : ¬ M.write e x b) : M.telicReading b ≠ M.agentiveReading b := by
  intro heq
  have := congrFun (congrFun heq x) e
  simp only [Model.telicReading, Model.agentiveReading] at this
  exact h' (this ▸ h)

end Pustejovsky1995
