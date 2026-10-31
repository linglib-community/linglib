module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Semantic types and denotation domains

In Montague semantics every expression has a *semantic type*, which fixes the kind of thing it
denotes: an individual ($e$), a truth value ($t$), a world ($s$), or a function from denotations
of type $a$ to denotations of type $b$ ($\langle a,b\rangle$). An *intension*, of type
$\langle s,a\rangle$, is a function from worlds; Montague's intensional logic has no type $s$ of
its own, and the two-sorted type theory of Gallin adds it. Later work adds sorts for degrees,
cardinalities, and events and states. Each type has a *domain* of possible denotations, built from
a set of individuals and a set of worlds, and the domain of a type that ends in $t$ is a Boolean
algebra, pointwise. A *computation type* is the type of a computation with an effect, such as
reading an environment or returning one of a set of alternatives, and its domain is the effect's
carrier of its result's domain.

## Main definitions

* `Montague.Ty`: semantic types.
* `Montague.Ty.intens`: intensions, the functions from worlds.
* `Montague.Sorts`: the carriers of the degree and eventuality sorts.
* `Montague.Eff`: the effects of computation types.
* `Montague.Ty.Domain E W ty S`, `Montague.Eff.F`: the denotation domain of `ty`, and an
  effect's carrier.
* `Montague.Eff.map`, `Montague.Eff.pure`, `Montague.Eff.seq`, `Montague.Eff.join`: an effect's
  map, unit, application of a computed function to a computed argument, and flattening.
* `Montague.Denotation E W M S`: a semantic type with an `M`-computation in its domain.
* `Montague.Ty.Conjoinable`: the types that end in `t`.
* `Montague.Ty.Domain.completeBooleanAlgebra`: the pointwise complete Boolean algebra of a
  conjoinable type.

## Implementation notes

`Ty.Domain` is reducible: a denotation of type `⟨e,t⟩` *is* an `E → Prop` to every tactic and
instance, and the Boolean algebra of a type that ends in `t` is mathlib's `Pi` instance.
`Ty.Domain.completeBooleanAlgebra` builds that algebra by recursion on a type known to be
conjoinable, for statements about a type that is not concrete. The reader's carrier is the
function type itself, not `ReaderT`, and the carrier of alternatives is `Set`, not `SetM`, so that
a domain is a function type or a set to instance search; their map, unit and application are
therefore explicit. A set of alternatives is not conjoinable: two sets of alternatives coordinate
alternative by alternative, through the modes, and not by intersection.

## References

* [montague-1970]
* [montague-1973]
* [D. Dowty, R. Wall, S. Peters, *Introduction to Montague Semantics*
  (1981)][dowty-wall-peters-1981]
* [D. Gallin, *Intensional and Higher-Order Modal Logic* (1975)][gallin-1975]
* [B. Partee, M. Rooth, *Generalized Conjunction and Type Ambiguity* (1983)][partee-rooth-1983]
* [bumford-charlow-2026]
-/

@[expose] public section

namespace Montague

mutual

/-- The semantic types are the entities `e`, the truth values `t`, the worlds `s`, and the
functions `fn a b` (⟨a,b⟩) of two-sorted type theory ([gallin-1975]), in which Montague's
intensions ⟨s,a⟩ are the functions from worlds (`Ty.intens`), together with the degree sort `d`
([heim-2001], [wellwood-2015]), the cardinality sort `n` ([sudo-2016], [scontras-2014],
[little-moroney-royer-2022]), and the eventuality sort `v` ([davidson-1967], [parsons-1990]).
Kratzer's type `s` of events, of which actions and states are subkinds ([kratzer-1996]), is `v`,
not the worlds `s`, as are Hanink and Koontz-Garboden's states ([hanink-koontz-garboden-2025]);
events and states are distinguished within it ([yu-ausensi-smith-2023]), not as two types. A
computation type `comp f a` is a computation with the effect `f` whose result is of type `a`
([bumford-charlow-2026]). -/
inductive Ty where
  /-- Entities. -/
  | e
  /-- Truth values. -/
  | t
  /-- Degrees, denoting in the model's scale. -/
  | d
  /-- Cardinalities, denoting in `ℕ`. -/
  | n
  /-- Eventualities, events and states alike. -/
  | v
  /-- Worlds, or situations: the indices of evaluation. -/
  | s
  /-- Functions `⟨a,b⟩`. -/
  | fn : Ty → Ty → Ty
  /-- Computations with an effect. -/
  | comp : Eff → Ty → Ty
  deriving Repr, DecidableEq

/-- The effects of computation types ([bumford-charlow-2026]): the reader of an environment of a
type, a computation that reads a value of that type, as an intension reads a world, and
indeterminacy, a computation with a set of alternative results, as an indefinite has. -/
inductive Eff where
  /-- The reader of an environment of type `ι`. -/
  | reader : Ty → Eff
  /-- Indeterminacy, a set of alternatives. -/
  | set : Eff
  deriving Repr, DecidableEq

end

@[inherit_doc] scoped infixr:25 " ⇒ " => Ty.fn

/-- Intensions `⟨s,a⟩`, the functions from worlds. -/
@[match_pattern] abbrev Ty.intens (a : Ty) : Ty := .fn .s a

/-- `⟨e,t⟩`, properties of individuals. -/
abbrev Ty.et : Ty := .e ⇒ .t
/-- `⟨e,⟨e,t⟩⟩`, relations between individuals. -/
abbrev Ty.eet : Ty := .e ⇒ .e ⇒ .t
/-- `⟨v,t⟩`, predicates of eventualities. -/
abbrev Ty.vt : Ty := .v ⇒ .t
/-- `⟨e,⟨v,t⟩⟩`, relations of individuals to eventualities, as thematic roles are. -/
abbrev Ty.evt : Ty := .e ⇒ .v ⇒ .t
/-- `⟨⟨e,t⟩,t⟩`, generalized quantifiers. -/
abbrev Ty.ett : Ty := (.e ⇒ .t) ⇒ .t
/-- `⟨⟨e,t⟩,⟨⟨e,t⟩,t⟩⟩`, determiners. -/
abbrev Ty.det : Ty := (.e ⇒ .t) ⇒ ((.e ⇒ .t) ⇒ .t)

/-- The carriers of the sorts beyond Montague's entities and indices, the scale of degrees and
the eventualities, which are empty unless a model supplies them. -/
structure Sorts where
  /-- The scale of degrees. -/
  degree : Type := ℝ
  /-- The eventualities. -/
  eventuality : Type := Empty

mutual

/-- The type `e` denotes in `E`, `t` in `Prop`, `d` in the scale of degrees, `n` in `ℕ`, `v` in
the eventualities, `s` in `W`, `⟨a,b⟩` in `Ty.Domain a → Ty.Domain b`, so that an intension
`⟨s,a⟩` denotes in `W → Ty.Domain a`, and a computation type in its effect's carrier. -/
abbrev Ty.Domain (E W : Type) (ty : Ty) (S : Sorts := {}) : Type :=
  match ty with
  | .e => E
  | .t => Prop
  | .d => S.degree
  | .n => ℕ
  | .v => S.eventuality
  | .s => W
  | .fn a b => Ty.Domain E W a S → Ty.Domain E W b S
  | .comp f a => Eff.F E W f S (Ty.Domain E W a S)

/-- The carrier of an effect: a computation that reads an environment of type `ι` is a function
from its denotations, and an indeterminate computation is the set of its alternatives. -/
abbrev Eff.F (E W : Type) (f : Eff) (S : Sorts := {}) (α : Type) : Type :=
  match f with
  | .reader ι => Ty.Domain E W ι S → α
  | .set => Set α

end

/-- An effect's map, a function applied to the result of a computation. -/
def Eff.map {E W : Type} {S : Sorts} {α β : Type} : (f : Eff) → (α → β) → Eff.F E W f S α →
    Eff.F E W f S β
  | .reader _, g, x => fun i ↦ g (x i)
  | .set, g, x => g '' x

/-- An effect's unit, the computation with no effect that returns a value. -/
def Eff.pure {E W : Type} {S : Sorts} {α : Type} : (f : Eff) → α → Eff.F E W f S α
  | .reader _, a => fun _ ↦ a
  | .set, a => {a}

/-- An effect's application `⊛` of a computed function to a computed argument
([bumford-charlow-2026]): the reader reads one environment for both, and indeterminacy applies
every alternative function to every alternative argument. -/
def Eff.seq {E W : Type} {S : Sorts} {α β : Type} :
    (f : Eff) → Eff.F E W f S (α → β) → Eff.F E W f S α → Eff.F E W f S β
  | .reader _, g, x => fun i ↦ g i (x i)
  | .set, g, x => Set.seq g x

/-- An effect's join `μ` ([bumford-charlow-2026]), flattening a computation of a computation: the
reader reads one environment for both, and indeterminacy unions the sets of alternatives. -/
def Eff.join {E W : Type} {S : Sorts} {α : Type} :
    (f : Eff) → Eff.F E W f S (Eff.F E W f S α) → Eff.F E W f S α
  | .reader _, x => fun i ↦ x i i
  | .set, x => ⋃₀ x

/-- A denotation in the Montague type system is a semantic type together with an `M`-computation
in the domain of that type. `M := Id` is the pure [heim-kratzer-1998] carrier; effectful
denotations supply `M`. -/
abbrev Denotation (E W : Type) (M : Type → Type := Id) (S : Sorts := {}) : Type :=
  (ty : Ty) × M (Ty.Domain E W ty S)

/-- A type is conjoinable when it ends in `t` ([partee-rooth-1983]). -/
def Ty.Conjoinable : Ty → Prop
  | .t => True
  | .fn _ b => b.Conjoinable
  | .comp (.reader _) b => b.Conjoinable
  | .comp .set _ | .e | .d | .n | .v | .s => False

instance Ty.decidableConjoinable : DecidablePred Ty.Conjoinable
  | .t => .isTrue trivial
  | .fn _ b => Ty.decidableConjoinable b
  | .comp (.reader _) b => Ty.decidableConjoinable b
  | .comp .set _ | .e | .d | .n | .v | .s => .isFalse id

/-- The domain of a conjoinable type carries the pointwise complete Boolean algebra
([partee-rooth-1983]). At a concrete type it is the instance `Pi.instCompleteBooleanAlgebra` finds
statically. -/
@[instance_reducible]
def Ty.Domain.completeBooleanAlgebra (E W : Type) :
    (ty : Ty) → ty.Conjoinable → (S : Sorts := {}) → CompleteBooleanAlgebra (Ty.Domain E W ty S)
  | .t, _, _ => inferInstanceAs (CompleteBooleanAlgebra Prop)
  | .fn _ b, h, S => letI := completeBooleanAlgebra E W b h S; inferInstance
  | .comp (.reader _) b, h, S => letI := completeBooleanAlgebra E W b h S; inferInstance
  | .comp .set _, h, _ | .e, h, _ | .d, h, _ | .n, h, _ | .v, h, _ | .s, h, _ => h.elim

end Montague
