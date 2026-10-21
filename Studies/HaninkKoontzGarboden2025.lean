module

public import Linglib.Semantics.Composition.Ty
public import Linglib.Semantics.Possession.Relationalizer
public import Linglib.Semantics.ArgumentStructure.EventStructure.Interpretation
public import Linglib.Fragments.Washo.PropertyConcepts
public import Linglib.Data.Examples.HaninkKoontzGarboden2025

/-!
# Hanink and Koontz-Garboden (2025): Variation in the Lexical Semantics of Property Concept Roots

Hanink and Koontz-Garboden argue from Washo that property concept roots vary in meaning within
a language, against Menon and Pancheva's universal quality-denoting root. Washo property
concepts are verbs of three shapes (Table 1): a bare root inflected like any intransitive, a
bound root with the suffix *-iʔ*, and a reduplicated bound root flanked by *ʔil-* and *-iʔ*,
`Washo.Shape`. The paper reads the morphology at face value: *-iʔ* is the possessive light verb
of ordinary possession (31), true of the possessors of something satisfying its argument,
`vHave`, which takes a predicate of states (34); so a root that needs it denotes a quality, a
predicate of states (33), while a bare root denotes a relation between individuals and states
(27). The reduplicated roots denote
relations too, since they alone serve as bare finals of resultative bipartite verbs (38), whose
change-of-state head takes a relation (43a); being bound, they reach *-iʔ* through *ʔil-*, which
returns the range of a relation (57), `nabla`, a Duke-of-York derivation that gives back the
root's own predication when possessing a state is holding it, `vHave_nabla_self`. One assignment
of types to shapes, `RootType.ofShape`, then derives the morphology of each shape as its shortest
well-typed verbalization, `derivation_minimal`, and the bipartite gap for the suffixed roots
(49), `wellTyped_become_iff`. The change-of-state head is Beavers and Koontz-Garboden's
inchoative operator, and the resultative entails the result state of its theme (46). The
seventy stems of the appendix are the rows of `Washo.propertyConcepts`, on which Dixon's
categories predict the shape only for color; the examples are the rows of
`Data.Examples.HaninkKoontzGarboden2025`.

## Implementation notes

Types are the substrate's `Ty`, with `.v` the paper's type of states and events of change alike
(43), and the composability claims are stated at the type level, since Lean's own typing enforces
them in the semantic definitions. Possession relates a possessor to a possessum of any type, so
ordinary possession (67) and the possession of a state (35) are one operator. Causation and change
are interpreted by the substrate's `EventStructure.Interpretation`, whose heads `vBecome` and
`vCause` are the paper's (43) and whose effector stands for the paper's AGENT.

## References

* [hanink-koontz-garboden-2025]
* [menon-pancheva-2014]
* [francez-koontz-garboden-2017]
* [beavers-koontz-garboden-2020]
* [dixon-1982]
* [jacobsen-1980]
-/

@[expose] public section

namespace HaninkKoontzGarboden2025

open Semantics Montague Possession Washo

/-! ### The two root meanings, section 4 -/

/-- A property concept root means either a relation between individuals and states or a
predicate of states alone, a quality. -/
inductive RootType where
  | relation
  | quality
  deriving DecidableEq, Repr

/-- The semantic type of each meaning. -/
def RootType.ty : RootType → Ty
  | .relation => .e ⇒ .v ⇒ .t
  | .quality => .v ⇒ .t

/-- On the analysis bare and prefixed roots denote relations and suffixed roots qualities. -/
def RootType.ofShape : Shape → RootType
  | .bare => .relation
  | .suffixed => .quality
  | .prefixed => .relation

/-- The two meanings are distinguished within Washo, the existence proof against a universal
root meaning. -/
theorem exists_rootType_ne :
    ∃ e₁ ∈ propertyConcepts, ∃ e₂ ∈ propertyConcepts,
      RootType.ofShape e₁.shape ≠ RootType.ofShape e₂.shape :=
  ⟨ihuk, by decide, iyel, by decide, by decide⟩

/-! ### The verbalizing heads and their types -/

/-- The heads that build a verb from a root are zero categorization, which keeps a relation,
the possessive light verb *-iʔ*, which takes a predicate of states, the prefix *ʔil-*, which
takes a relation to a predicate of states, and the change-of-state head of a bipartite verb,
which takes a relation. -/
inductive Head where
  | zero
  | possess
  | attr
  | become
  deriving DecidableEq, Repr

/-- The type a head takes. -/
def Head.input : Head → Ty
  | .zero => .e ⇒ .v ⇒ .t
  | .possess => .v ⇒ .t
  | .attr => .e ⇒ .v ⇒ .t
  | .become => .e ⇒ .v ⇒ .t

/-- The type a head returns is a predicate of individuals and states for the verbalizers, a
predicate of states for *ʔil-*, and a relation of individuals to events of change for the bipartite
head, of the same type, since states and events of change are both of type `v` (43). -/
def Head.output : Head → Ty
  | .zero => .e ⇒ .v ⇒ .t
  | .possess => .e ⇒ .v ⇒ .t
  | .attr => .v ⇒ .t
  | .become => .e ⇒ .v ⇒ .t

/-- A sequence of heads composes with a type when each takes what the last returns. -/
def WellTyped : Ty → List Head → Prop
  | _, [] => True
  | τ, h :: hs => h.input = τ ∧ WellTyped h.output hs

instance decWellTyped : (τ : Ty) → (hs : List Head) → Decidable (WellTyped τ hs)
  | _, [] => isTrue trivial
  | τ, h :: hs =>
    haveI := decWellTyped h.output hs
    inferInstanceAs (Decidable (h.input = τ ∧ WellTyped h.output hs))

/-- The type a sequence of heads returns. -/
def output (τ : Ty) : List Head → Ty
  | [] => τ
  | h :: hs => output h.output hs

/-- A verbalization of a root is a sequence of at least one head that is well-typed and returns
a stative predicate, one without the change-of-state head, with zero categorization open only to
a free root. -/
def Verbalizes (sh : Shape) (hs : List Head) : Prop :=
  hs ≠ [] ∧ WellTyped (RootType.ofShape sh).ty hs ∧
    output (RootType.ofShape sh).ty hs = (.e ⇒ .v ⇒ .t) ∧ Head.become ∉ hs ∧
      (Head.zero ∈ hs → sh = .bare)

instance (sh : Shape) (hs : List Head) : Decidable (Verbalizes sh hs) := by
  unfold Verbalizes; infer_instance

/-- The morphology of each shape is the bare root, the root with *-iʔ*, or the root with *ʔil-*
and then *-iʔ*. -/
def derivation : Shape → List Head
  | .bare => [.zero]
  | .suffixed => [.possess]
  | .prefixed => [.attr, .possess]

theorem derivation_verbalizes : ∀ sh, Verbalizes sh (derivation sh) := by decide

/-- *-iʔ* composes directly with a root only if the root is a suffixed one, whose meaning is a
quality. -/
theorem wellTyped_possess_iff (sh : Shape) :
    WellTyped (RootType.ofShape sh).ty [.possess] ↔ sh = .suffixed := by
  cases sh <;> decide

/-- The change-of-state head of a bipartite verb composes with a root iff the root is not a
suffixed one, the gap in the resultative bipartite verbs. -/
theorem wellTyped_become_iff (sh : Shape) :
    WellTyped (RootType.ofShape sh).ty [.become] ↔ sh ≠ .suffixed := by
  cases sh <;> decide

/-- Each shape's morphology is a shortest verbalization of its root. The prefixed roots need
two heads, being bound relations that neither zero categorization nor *-iʔ* alone can take. -/
theorem derivation_minimal (sh : Shape) (hs : List Head) (h : Verbalizes sh hs) :
    (derivation sh).length ≤ hs.length := by
  cases sh
  · exact List.length_pos_of_ne_nil h.1
  · exact List.length_pos_of_ne_nil h.1
  · rcases hs with _ | ⟨h₁, _ | ⟨h₂, t⟩⟩
    · exact absurd rfl h.1
    · cases h₁ <;> simp [Verbalizes, WellTyped, output, Head.input, Head.output,
        RootType.ofShape, RootType.ty] at h
    · show 2 ≤ t.length + 1 + 1
      omega

/-! ### The operators -/

variable {E Y St : Type*}

/-- The possessive light verb *-iʔ* (34) holds of the possessors of a `P`, which is ordinary
possession when the possessum is an entity and the possession of a state when it is a quality. -/
def vHave (P : Y → Prop) (R : E → Y → Prop) : E → Prop := dom P R

/-- The prefix *ʔil-* (57) takes the range of a relation, the states some individual bears it
to. -/
def nabla (P : E → St → Prop) : St → Prop := ⨆ x, P x

/-- In the Duke-of-York derivation of section 5.2, when possessing a state of the root is bearing
the root's relation to it, the prefixed root under *ʔil-* and *-iʔ* predicates what the bare
relation does (28), the meaning its bipartite uses show it to have. -/
theorem vHave_nabla_self (P : E → St → Prop) (x : E) : vHave (nabla P) P x ↔ ∃ s, P x s :=
  dom_iSup_self P x

/-! ### Resultative bipartite verbs, section 5.1 -/

variable {Event : Type*} (M : ArgumentStructure.EventStructure.Interpretation E St Event)

/-- A resultative bipartite verb, the causative head over the initial's manner and the
change-of-state head over the final's root, entails the result state of its theme, the bare
predication of the final's root. -/
theorem exists_state_of_vCause {P : E → St → Prop} {manner : Event → Prop} {x : E} {v : Event}
    (h : M.vCause (fun e ↦ manner e ∧ M.vBecome P x e) v) : ∃ s, P x s :=
  let ⟨_, _, _, s, _, hs⟩ := h
  ⟨s, hs⟩

/-! ### The stems of the appendix -/

/-- The only category whose members share a shape is color, all of whose stems are prefixed
(appendix). -/
theorem color_prefixed : ∀ e ∈ propertyConcepts, e.category = .color → e.shape = .prefixed := by
  decide

/-- [dixon-1982]'s categories do not predict the shape, since the antonyms *MiLe* 'old' and
*ešlut’* 'young' differ. -/
theorem category_not_predictive :
    ∃ e₁ ∈ propertyConcepts, ∃ e₂ ∈ propertyConcepts,
      e₁.category = e₂.category ∧ e₁.shape ≠ e₂.shape :=
  ⟨MiLe, by decide, ešlut, by decide, rfl, by decide⟩

end HaninkKoontzGarboden2025
