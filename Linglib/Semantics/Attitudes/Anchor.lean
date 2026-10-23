module

public import Linglib.Logic.Modal.Defs

/-!
# Clauses as predicates of anchors

On the standard analysis a *that*-clause denotes a proposition. On the projection analysis of
Hacquard and Kratzer, a clause instead denotes a predicate of *anchors*, individuals from which a
propositional domain is projected: the complementizer identifies the clause's proposition with the
projection of the anchor. Content individuals, such as beliefs and claims, project their content;
situation individuals, such as cases and circumstances, project the situations they refer to. The
two sorts are distinct types, so that a verb's selection of content or situation clauses, as in
Greek *oti* against *pu*, is type selection, while the compositional machinery is shared. An
anchor noun combines with a clause by predicate modification, and a clause-selecting verb takes
the anchor as an argument that existential closure binds. With Moulton's doxastic verb, which
requires every accessible index to project from the anchor, the closed report is Hintikka's
universal modal whenever every proposition is the projection of some anchor.

## Main definitions

* `Anchor`: a sort of anchors with its projection.
* `Anchor.comp`, `Anchor.nounComp`, `Anchor.existsClosure`: the complementizer, predicate
  modification of an anchor noun, and existential closure of a verb's anchor argument.
* `Anchor.ofAccessibility`: Moulton's doxastic verb.
* `ContentIndividual`, `SituationIndividual`: the two sorts of anchors.

## Main statements

* `Anchor.existsClosure_ofAccessibility`: with a surjective projection, an existentially closed
  report with Moulton's verb is the universal modal.
* `ContentIndividual.eq_implies_entails`, `ContentIndividual.entails_not_implies_eq`: identity of
  content, Kratzer's and Moulton's relation, is strictly stronger than entailment, Hintikka's.

## Implementation notes

A content individual has its content as its only field, so two individuals with the same content
are identified; the difference between my belief that `p` and yours is not captured. Kratzer's
shape, an atom with a content at each world, would capture it once a study needs the distinction.
The situation sort carries no parthood order, so consumers choose their own situation type.

## References

* [hacquard-2006]
* [kratzer-2006]
* [kratzer-2013]
* [moulton-2015]
* [bondarenko-2022]
* [moltmann-2021]
* [angelopoulos-2026]
* [heim-kratzer-1998]
* [hintikka-1962]
* [kratzer-1989]
* [liefke-2024]
* [moltmann-2019]
* [moltmann-2024]
-/

@[expose] public section

/-- An anchor sort is a type of individuals each of which projects a propositional domain over
the indices `I`. -/
class Anchor (α : Type*) (I : outParam Type*) where
  /-- `proj x` is the domain the anchor `x` projects. -/
  proj : α → I → Prop

namespace Anchor

open scoped ModalLogic SetRel

variable {α I E : Type*} [Anchor α I]

/-- The complementizer holds of an anchor whose projection is the clause's proposition. -/
def comp (q : I → Prop) (x : α) : Prop :=
  proj x = q

/-- An anchor noun combines with a clause by predicate modification. -/
def nounComp (noun : α → I → Prop) (q : I → Prop) : α → I → Prop :=
  fun x i ↦ noun x i ∧ comp q x

/-- Existential closure at the edge of the verb phrase binds the anchor argument of a
clause-selecting verb. -/
def existsClosure (verb : E → α → I → Prop) (agent : E) (q : I → Prop) (i : I) : Prop :=
  ∃ x : α, verb agent x i ∧ comp q x

/-- Moulton's doxastic verb relates the agent to an anchor at `i` when every index accessible
from `i` lies in the anchor's projection. -/
def ofAccessibility (R : E → SetRel I I) : E → α → I → Prop :=
  fun agent x i ↦ ∀ i', i ~[R agent] i' → proj x i'

theorem existsClosure_ofAccessibility (R : E → SetRel I I) (a : E) (q : I → Prop) (i : I)
    (hp : Function.Surjective (proj : α → I → Prop)) :
    existsClosure (ofAccessibility (α := α) R) a q i ↔ □[R a] q i :=
  ⟨fun ⟨_, hsub, hc⟩ v hv ↦ hc ▸ hsub v hv,
   fun h ↦ (hp q).elim fun x hx ↦ ⟨x, fun i' hi' ↦ hx.symm ▸ h i' hi', hx⟩⟩

end Anchor

/-! ### Content individuals

A content individual is a mental state or speech act with propositional content, the denotation
of content nominals such as *John's belief that p*, *the claim* or *every rumor*. Beliefs, desires
and percepts share the sort; what distinguishes them is the attitude relation that embeds them
[liefke-2024]. -/

/-- A content individual carries a propositional content. -/
structure ContentIndividual (W : Type*) where
  /-- The content of the individual. -/
  cont : W → Prop

namespace ContentIndividual

variable {W : Type*}

instance : Anchor (ContentIndividual W) W :=
  ⟨cont⟩

theorem cont_surjective : Function.Surjective (cont : ContentIndividual W → W → Prop) :=
  fun p ↦ ⟨⟨p⟩, rfl⟩

/-- A content individual entails `p` when every world of its content is a `p`-world. -/
def entails (xc : ContentIndividual W) (p : W → Prop) : Prop :=
  ∀ w, xc.cont w → p w

theorem eq_implies_entails (xc : ContentIndividual W) (p : W → Prop) :
    xc.cont = p → xc.entails p :=
  fun h _ hw ↦ h ▸ hw

theorem entails_not_implies_eq :
    ¬ ∀ (p : Bool → Prop) (xc : ContentIndividual Bool), xc.entails p → xc.cont = p :=
  fun h ↦ (iff_of_eq (congrFun (h (fun _ ↦ True) ⟨fun _ ↦ False⟩ fun _ hw ↦ hw.elim)
    true)).mpr trivial

end ContentIndividual

/-! ### Situation individuals

A situation individual refers to situations in Kratzer's sense [kratzer-1989], the denotation of
situation nominals such as *the case that the father is absent*. Bondarenko observes that verbs
selecting content clauses, such as *say* and *believe*, reject situation clauses, and verbs
selecting situation clauses, such as *regret*, reject content clauses [bondarenko-2022]; see also
[moltmann-2019] and [moltmann-2024]. -/

/-- A situation individual refers to a set of situations. -/
structure SituationIndividual (S : Type*) where
  /-- The situations the individual refers to. -/
  sit : S → Prop

instance {S : Type*} : Anchor (SituationIndividual S) S :=
  ⟨SituationIndividual.sit⟩

theorem SituationIndividual.sit_surjective {S : Type*} :
    Function.Surjective (SituationIndividual.sit : SituationIndividual S → S → Prop) :=
  fun p ↦ ⟨⟨p⟩, rfl⟩
