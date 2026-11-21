module

public import Linglib.Semantics.Composition.Sorts
public import Linglib.Semantics.Possession.Relationalizer
public import Linglib.Semantics.ArgumentStructure.EventStructure.Interpretation
public import Linglib.Fragments.Washo.PropertyConcepts
public import Linglib.Data.Examples.HaninkKoontzGarboden2025
public import Linglib.Data.StructureDataset.Dixon1982

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
(49), `isSome_output?_become_iff`. The change-of-state head is Beavers and Koontz-Garboden's
inchoative operator, and the resultative entails the result state of its theme (46). The
seventy stems of the appendix are the rows of `Washo.propertyConcepts`, whose class is read off
their affixes, `Washo.shape`, and the appendix sorts them by Dixon's semantic types, `stems`.
The types predict neither the class nor the meaning of a root, `not_exists_forall_rootType_eq`,
and color is the only one whose stems share a class, `exists_shape_iff`. The examples are the
rows of `Data.Examples.HaninkKoontzGarboden2025`.

## Implementation notes

Types are the substrate's `Ty`, with `.v` the paper's type of states and events of change alike
(43), and the composability claims are stated at the type level, since Lean's own typing enforces
them in the semantic definitions. Possession relates a possessor to a possessum of any type, so
ordinary possession (67) and the possession of a state (35) are one operator. Causation and change
are interpreted by the substrate's `EventStructure.Interpretation`: possibility along its
`become` and `cause` are the paper's heads (43).

## TODO

The appendix's categories depart from Dixon's English examples: it puts 'heavy' and 'light'
under dimension, which he puts under physical property, and 'fat' and two stems glossed 'thin'
under physical property, which he puts under dimension. On his assignment the conclusions stand,
since color and age are unchanged and dimension and physical property still mix classes. The
appendix also counts 35 Class 3 stems where its table lists 25, the seventy being 30, 15 and 25.

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

open Interpreter Possession Washo

/-! ### The two root meanings, section 4 -/

/-- A property concept root means either a relation between individuals and states or a
predicate of states alone, a quality. -/
inductive RootType where
  | relation
  | quality
  deriving DecidableEq, Repr

/-- The semantic type of each meaning. -/
def RootType.ty : RootType → Ty Base
  | .relation => .e ⇒ .v ⇒ .t
  | .quality => .v ⇒ .t

/-- On the analysis bare and prefixed roots denote relations and suffixed roots qualities. -/
def RootType.ofShape : Shape → RootType
  | .bare => .relation
  | .suffixed => .quality
  | .prefixed => .relation

theorem exists_rootType_ne :
    ∃ e₁ ∈ propertyConcepts, ∃ e₂ ∈ propertyConcepts,
      RootType.ofShape (shape e₁) ≠ RootType.ofShape (shape e₂) :=
  ⟨ihuk, by simp [propertyConcepts], iyel, by simp [propertyConcepts], by decide⟩

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
def Head.input : Head → Ty Base
  | .zero => .e ⇒ .v ⇒ .t
  | .possess => .v ⇒ .t
  | .attr => .e ⇒ .v ⇒ .t
  | .become => .e ⇒ .v ⇒ .t

/-- The type a head returns is a predicate of individuals and states for the verbalizers, a
predicate of states for *ʔil-*, and a relation of individuals to events of change for the bipartite
head, of the same type, since states and events of change are both of type `v` (43). -/
def Head.output : Head → Ty Base
  | .zero => .e ⇒ .v ⇒ .t
  | .possess => .e ⇒ .v ⇒ .t
  | .attr => .v ⇒ .t
  | .become => .e ⇒ .v ⇒ .t

/-- The type a sequence of heads returns from a type, if each takes what the last returns. -/
def output? (τ : Ty Base) (hs : List Head) : Option (Ty Base) :=
  hs.foldlM (fun τ h ↦ if h.input = τ then some h.output else none) τ

/-- A verbalization of a root is a sequence of at least one head that is well-typed and returns
a stative predicate, one without the change-of-state head, with zero categorization open only to
a free root. -/
def Verbalizes (sh : Shape) (hs : List Head) : Prop :=
  hs ≠ [] ∧ output? (RootType.ofShape sh).ty hs = some (.e ⇒ .v ⇒ .t) ∧ Head.become ∉ hs ∧
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

theorem isSome_output?_possess_iff (sh : Shape) :
    (output? (RootType.ofShape sh).ty [.possess]).isSome ↔ sh = .suffixed := by
  cases sh <;> decide

theorem isSome_output?_become_iff (sh : Shape) :
    (output? (RootType.ofShape sh).ty [.become]).isSome ↔ sh ≠ .suffixed := by
  cases sh <;> decide

theorem derivation_minimal (sh : Shape) (hs : List Head) (h : Verbalizes sh hs) :
    (derivation sh).length ≤ hs.length := by
  cases sh
  · exact List.length_pos_of_ne_nil h.1
  · exact List.length_pos_of_ne_nil h.1
  · rcases hs with _ | ⟨h₁, _ | ⟨h₂, t⟩⟩
    · exact absurd rfl h.1
    · cases h₁ <;> simp [Verbalizes, output?, Head.input, Head.output,
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

/-- In the Duke-of-York derivation of section 5.2, the prefixed root under *ʔil-* and *-iʔ*
predicates what the bare relation does (28). -/
theorem vHave_nabla_self (P : E → St → Prop) (x : E) : vHave (nabla P) P x ↔ ∃ s, P x s :=
  dom_iSup_self P x

/-! ### Resultative bipartite verbs, section 5.1 -/

variable {Event : Type*} (M : ArgumentStructure.EventStructure.Interpretation St Event)

theorem exists_state_of_diamond_cause {P : E → St → Prop} {manner : Event → Prop} {x : E}
    {v : Event}
    (h : ModalLogic.Diamond M.cause (fun e ↦ manner e ∧ ModalLogic.Diamond M.become (P x) e) v) :
    ∃ s, P x s :=
  let ⟨_, _, _, s, _, hs⟩ := h
  ⟨s, hs⟩

/-! ### Dixon's categories, appendix -/

/-- The stems of the appendix under each of Dixon's semantic types, in the order of Table A1. -/
def stems : Dixon1982.StructureDataset.SemanticType → List Verb
  | .age => [MiLe, ešlut]
  | .color => [leleg, pilpil, popo, šošoŋ, yiŋyiŋ]
  | .dimension => [beheziŋ, wgohat, lupdep, udaw, iyel, hamham, šišiš]
  | .humanPropensity =>
    [bišapu, gumbiis, gumyol, kiwil, Lokaš, meleyik, melotik, šašiw, tesu, yaha, yomuŋ, yumil,
      gumsutim, musiw, tamugayl]
  | .value => [aŋaw, muaŋ, nuš, umbiic]
  | .physicalProperty =>
    [golgoš, ibik, ihuk, keše, metu, mipil, mosot, mucucu, wihl, yakaš, yasaŋ, yayaŋ, gucu,
      gumbeyécik, kakt, Loyaw, nuuš, wkuli, yacim, babab, huhu, kawkaw, kunkun, kaykay, kuškuš,
      lotlot, mukmuk, naynay, pepel, pipi, šapšap, šišip, sinsin, siwsiw, tetep, tintin, witwit]
  | .speed => []

theorem propertyConcepts_eq :
    propertyConcepts = stems .age ++ stems .color ++ stems .dimension ++ stems .humanPropensity ++
      stems .value ++ stems .physicalProperty :=
  rfl

-- (74)
theorem stems_speed : stems .speed = [] :=
  rfl

theorem not_exists_forall_rootType_eq :
    ¬ ∃ f : Dixon1982.StructureDataset.SemanticType → RootType,
      ∀ c, ∀ e ∈ stems c, RootType.ofShape (shape e) = f c := fun ⟨_, h⟩ ↦
  absurd ((h .age MiLe (by simp [stems])).trans (h .age ešlut (by simp [stems])).symm) (by decide)

theorem not_exists_forall_shape_eq :
    ¬ ∃ f : Dixon1982.StructureDataset.SemanticType → Shape, ∀ c, ∀ e ∈ stems c, shape e = f c :=
  fun ⟨f, h⟩ ↦ not_exists_forall_rootType_eq
    ⟨fun c ↦ .ofShape (f c), fun c e he ↦ congrArg RootType.ofShape (h c e he)⟩

theorem color_prefixed : ∀ e ∈ stems .color, shape e = .prefixed := by
  decide

theorem exists_shape_iff {c : Dixon1982.StructureDataset.SemanticType} (hc : c ≠ .speed) :
    (∃ s, ∀ e ∈ stems c, shape e = s) ↔ c = .color := by
  revert hc
  cases c <;> decide

end HaninkKoontzGarboden2025
