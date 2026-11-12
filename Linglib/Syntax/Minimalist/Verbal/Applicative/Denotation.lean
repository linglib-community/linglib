/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Verbal.Applicative
public import Linglib.Syntax.Minimalist.Verbal.Voice.Denotation

/-!
# The denotation of applicative heads

An applicative head has a semantic type and a denotation, read off what it relates the applied
argument to. The high head denotes a relation between an individual and an eventuality, of type
`⟨e,⟨v,t⟩⟩`, and [combines with a verb phrase by Event
Identification](##Minimalist.Appl.binary_high), as thematic Voice does; with its variable bound
existentially it is a predicate of eventualities, the defective head that licenses no specifier,
in parallel with passive Voice. The low head relates two individuals: it takes the theme, the
applied argument and a verb with an open object, and asserts that the theme is the verb's and
stands to the applied argument in a relation of possession, toward it, away from it or static. A
low applicative phrase therefore [takes a transitive verb as its
argument](##Minimalist.Appl.binary_lowApplP) and [composes with no predicate of
eventualities](##Minimalist.Appl.low_not_composes_vt), and over a constituent whose open argument
is the agent it [holds of no eventuality](##Minimalist.Appl.lowAppl_eventIdentification_eq_bot_iff)
where no agent is the theme of what it does. The relations are a model's, so a study that
interprets a Minimalist object supplies the model, not the head's meaning.

## References

* [pylkkanen-2008]
* [cuervo-2003]
* [kratzer-1996]
-/

@[expose] public section

namespace Minimalist.Appl

open ManySorted Interpreter ArgumentStructure

/-- The low applicative relates the theme `x` to the applied argument `y` by the possession
relation `poss` and asserts that `x` is the theme of the verb `f`. -/
def lowAppl {Entity V : Type*} (theme : Entity → V → Prop) (poss : Entity → Entity → Prop)
    (x y : Entity) (f : Entity → V → Prop) : V → Prop :=
  fun e ↦ f x e ∧ theme x e ∧ poss x y

/-- Over a constituent whose open argument is the agent, the low applicative holds of no
eventuality exactly when, if `x` stands in the possession relation to `y`, `x` is the theme of no
eventuality of which it is the agent. -/
theorem lowAppl_eventIdentification_eq_bot_iff {Entity V : Type*}
    {agent theme : Entity → V → Prop} {poss : Entity → Entity → Prop} {run : V → Prop}
    {x y : Entity} :
    lowAppl theme poss x y (eventIdentification agent run) = ⊥ ↔
      (poss x y → ∀ e, run e → agent x e → ¬ theme x e) := by
  refine ⟨fun h hp e hr ha ht ↦ (congrFun h e).mp ⟨⟨ha, hr⟩, ht, hp⟩,
    fun h ↦ funext fun e ↦ eq_false fun ⟨⟨ha, hr⟩, ht, hp⟩ ↦ h hp e hr ha ht⟩

/-- The semantic type of an applicative head: `⟨e,⟨v,t⟩⟩` for the high head and
`⟨e,⟨e,⟨⟨e,⟨v,t⟩⟩,⟨v,t⟩⟩⟩⟩` for a low one. -/
def Head.ty : Head → Ty Base
  | .high => .evt
  | .low _ => .e ⇒ .e ⇒ .evt ⇒ .vt

variable {E W : Type} {S : Sorts} (appl theme : E → S.eventuality → Prop)
  (poss : LowRelation → E → E → Prop)

/-- The high head denotes the model's relation `appl` between the applied argument and the
eventuality, and a low head the low applicative of the model's theme relation and of the
possession relation `poss r` of its relation `r`. -/
def Head.denote : (h : Head) → h.ty.Domain E W S
  | .high => appl
  | .low r => lowAppl theme (poss r)

/-- The defective high head, its variable bound existentially: some individual stands in the
relation `appl` to the eventuality. -/
def implicit : S.eventuality → Prop := fun e ↦ ∃ x, appl x e

/-- The high head and a predicate of eventualities combine by Event Identification and no other
rule. -/
theorem binary_high :
    (typeDriven Voice.grammar).binary () Head.high.ty .vt = [⟨.evt, .inr .left⟩] :=
  rfl

/-- A low applicative phrase takes a verb with an open object by Functional Application. -/
theorem binary_lowApplP :
    (typeDriven Voice.grammar).binary () (.evt ⇒ .vt) .evt = [⟨.vt, .inl (.inl .fa)⟩] :=
  rfl

/-- No rule combines a low applicative, at any stage of saturation, with a predicate of
eventualities, the type of an unergative verb. -/
theorem low_not_composes_vt (r : LowRelation) :
    ∀ τ ∈ [(Head.low r).ty, .e ⇒ .evt ⇒ .vt, .evt ⇒ .vt], ∀ u,
      IsEmpty (Voice.grammar.Binary τ .vt u) ∧ IsEmpty (Voice.grammar.Binary .vt τ u) := by
  intro τ hτ u
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
  rcases hτ with rfl | rfl | rfl <;>
    exact ⟨⟨by rintro ((m | m) | m) <;> cases m⟩, ⟨by rintro ((m | m) | m) <;> cases m⟩⟩

end Minimalist.Appl
