module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Semantic types and denotation domains

In Montague semantics every expression has a *semantic type*, which fixes the kind of thing it
denotes: an individual ($e$), a truth value ($t$), a function from denotations of type $a$ to
denotations of type $b$ ($\langle a,b\rangle$), or an *intension* ($\langle s,a\rangle$), a
function from worlds to denotations of type $a$. Later work adds sorts for degrees, cardinalities,
and events and states. Each type has a *domain* of possible denotations, built from a set of
individuals and a set of worlds, and the domain of a type that ends in $t$ is a Boolean algebra,
pointwise.

## Main definitions

* `Montague.Ty`: semantic types.
* `Montague.Sorts`: the carriers of the degree and eventuality sorts.
* `Montague.Ty.Domain E W ty S`: the denotation domain of `ty`.
* `Montague.Denotation E W M S`: a semantic type with an `M`-computation in its domain.
* `Montague.Ty.Domain.completeBooleanAlgebra?`: the pointwise complete Boolean algebra of a
  type that ends in `t`, `none` on any other type.

## Implementation notes

`Ty.Domain` is reducible: a denotation of type `⟨e,t⟩` *is* an `E → Prop` to every tactic and
instance, and the Boolean algebra of a type that ends in `t` is mathlib's `Pi` instance.
`Ty.Domain.completeBooleanAlgebra?` computes that algebra by recursion on the type, for the
composition engine's dispatch on types at run time.

## References

* [montague-1970]
* [montague-1973]
* [D. Dowty, R. Wall, S. Peters, *Introduction to Montague Semantics*
  (1981)][dowty-wall-peters-1981]
* [D. Gallin, *Intensional and Higher-Order Modal Logic* (1975)][gallin-1975]
* [B. Partee, M. Rooth, *Generalized Conjunction and Type Ambiguity* (1983)][partee-rooth-1983]
-/

@[expose] public section

namespace Montague

/-- The semantic types are Montague's `e`, `t`, `fn a b` (⟨a,b⟩) and `intens a` (⟨s,a⟩), the
degree sort `d` ([heim-2001], [wellwood-2015]), the cardinality sort `n` ([sudo-2016],
[scontras-2014], [little-moroney-royer-2022]), and the eventuality sort `v` ([davidson-1967],
[parsons-1990]). Kratzer's type `s` of events, of which actions and states are subkinds
([kratzer-1996]), is `v`, as are Hanink and Koontz-Garboden's states
([hanink-koontz-garboden-2025]); events and states are distinguished within it
([yu-ausensi-smith-2023]), not as two types. -/
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
  /-- Functions `⟨a,b⟩`. -/
  | fn : Ty → Ty → Ty
  /-- Intensions `⟨s,a⟩`. -/
  | intens : Ty → Ty
  deriving Repr, DecidableEq

@[inherit_doc] scoped infixr:25 " ⇒ " => Ty.fn

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

/-- The type `e` denotes in `E`, `t` in `Prop`, `d` in the scale of degrees, `n` in `ℕ`, `v` in
the eventualities, `⟨a,b⟩` in `Ty.Domain a → Ty.Domain b` and `⟨s,a⟩` in `W → Ty.Domain a`. -/
abbrev Ty.Domain (E W : Type) (ty : Ty) (S : Sorts := {}) : Type :=
  match ty with
  | .e => E
  | .t => Prop
  | .d => S.degree
  | .n => ℕ
  | .v => S.eventuality
  | .fn a b => Ty.Domain E W a S → Ty.Domain E W b S
  | .intens a => W → Ty.Domain E W a S

/-- A denotation in the Montague type system is a semantic type together with an `M`-computation
in the domain of that type. `M := Id` is the pure [heim-kratzer-1998] carrier; effectful
denotations supply `M`. -/
abbrev Denotation (E W : Type) (M : Type → Type := Id) (S : Sorts := {}) : Type :=
  (ty : Ty) × M (Ty.Domain E W ty S)

/-- The domain of a conjoinable type carries the pointwise complete Boolean algebra
([partee-rooth-1983]), computed by recursion on the type and `none` exactly when the type does
not end in `t`. At a concrete type it is the instance `Pi.instCompleteBooleanAlgebra` finds
statically. -/
def Ty.Domain.completeBooleanAlgebra? (E W : Type) (ty : Ty) (S : Sorts := {}) :
    Option (CompleteBooleanAlgebra (Ty.Domain E W ty S)) :=
  match ty with
  | .t => some inferInstance
  | .fn _ b =>
    (completeBooleanAlgebra? E W b S).map fun (i : CompleteBooleanAlgebra (Ty.Domain E W b S)) =>
      letI := i; inferInstance
  | .intens a =>
    (completeBooleanAlgebra? E W a S).map fun (i : CompleteBooleanAlgebra (Ty.Domain E W a S)) =>
      letI := i; inferInstance
  | _ => none

end Montague
