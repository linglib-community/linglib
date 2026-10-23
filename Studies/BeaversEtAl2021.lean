module

public import Studies.BeaversKoontzGarboden2020
public import Linglib.Data.Examples.BeaversEtAl2021
public import Mathlib.Data.Fintype.Basic

/-!
# Beavers et al. (2021): States and Changes of State

This file formalizes the argument of Beavers and colleagues that some roots entail change. A
property-concept root, such as that of *bright*, describes a state that need not have come
about. A result root, such as that of *shatter*, describes a state that always arises from a
change (`EventStructure.Interpretation.EntailsChange`). This contradicts the Bifurcation Thesis,
on which change is introduced by the verbal template and never by a root.

A root entails change exactly when its stative cannot be conjoined with a denial of change
(`entailsChange_iff_forall_not_deniesChange`), and with such a root restitutive *again*
presupposes an earlier change. A root passes either diagnostic in some model that respects its
signature exactly when it does not entail change (`passes_iff`), and the examples agree outside
the expected lexical variation (`rows`). The morphology follows from a default realization rule:
a verb is unmarked iff its root entails change, and a stative is unmarked iff its complement does
not, and in a model that respects a root's signature the rule agrees with the semantics
(`entailsChange_of_verbRealization_eq_unmarked`). A language that spells out the unmarked form
only when it spells out the marked one belongs to one of the three attested types
(`Exponence.trichotomy`).

## Implementation notes

* The semantics is stated on `EventStructure.Interpretation`, which interprets the primitives of
  Beavers and Koontz-Garboden's book, and *again* is `Presupposition.again`.
* The realization rule reads whether a root entails change off its kind signature.
* The tables of the typological survey are not represented. Its coding of markedness is
  (`Code.IsMarked`).

## References

* [beavers-etal-2021]
* [beavers-koontz-garboden-2020]
* [embick-2009]
* [arad-2005]
* [haspelmath-1993]
-/

@[expose] public section

namespace BeaversEtAl2021

open Semantics Presupposition
open scoped SetRel ModalLogic

/-! ### State predicates that entail change -/

section Model

open ArgumentStructure BeaversKoontzGarboden2020

universe u

variable {Entity : Type*} {State Event : Type u}
  (M : EventStructure.Interpretation Entity State Event)
  {R : SetRel Event Event} {P : Entity → State → Prop} {y x : Entity} {s : State}

/-- The deverbal stative of `P` holds of the states of which `P` holds and that a change gave
rise to. -/
def resultStative (P : Entity → State → Prop) (x : Entity) : State → Prop :=
  P x ⊓ ◇[M.become] ⊤

/-- The stative description `P` holds of `x` in the state `s`, and no change gave rise to `s`. -/
def DeniesChange (P : Entity → State → Prop) (x : Entity) : State → Prop :=
  P x ⊓ (◇[M.become] ⊤)ᶜ

theorem not_deniesChange_resultStative : ¬ DeniesChange M (resultStative M P) x s :=
  fun h ↦ h.2 h.1.2

theorem entailsChange_iff_forall_not_deniesChange :
    M.EntailsChange P ↔ ∀ x s, ¬ DeniesChange M P x s :=
  forall₂_congr fun _ _ ↦ not_and_not_right.symm

theorem resultStative_iff (h : M.EntailsChange P) : resultStative M P x s ↔ P x s :=
  and_iff_left_of_imp (h x s)

theorem diamond_become_of_againAt_achievement_ne_zero {e : Event}
    (hp : againAt M .achievement R P y x e ≠ 0) : ◇[R] (◇[M.become.inv] ⊤) e :=
  ModalLogic.diamond_mono R (fun w ↦ ModalLogic.diamond_mono _ le_top w) e
    (again_ne_zero_iff.1 hp)

end Model

/-! ### A knife forged sharp -/

/-- A knife forged sharp is sharp in its first state `false`, and in its later state `true`,
which a sharpening gave rise to. -/
def forged : ArgumentStructure.EventStructure.Interpretation Unit Bool Unit where
  become := {p | p.1 = true}
  cause := ⊥
  effector := ⊥

/-- The knife is sharp in both of its states. -/
def sharp (_ : Unit) (_ : Bool) : Prop := True

theorem forged_deniesChange : DeniesChange forged sharp () false :=
  ⟨trivial, fun ⟨_, h, _⟩ ↦ Bool.false_ne_true h⟩

theorem not_entailsChange_sharp : ¬ forged.EntailsChange sharp :=
  fun h ↦ (entailsChange_iff_forall_not_deniesChange forged).1 h () false forged_deniesChange

theorem forged_restitutive :
    BeaversKoontzGarboden2020.againAt forged .state {p | p.2 < p.1} sharp () () true ≠ 0 ∧
      ¬ ◇[{p | p.2 < p.1}] (◇[forged.become] ⊤) true :=
  ⟨again_ne_zero_iff.2 ⟨false, Bool.false_lt_true, trivial⟩,
    fun ⟨_, hlt, _, h, _⟩ ↦ by cases (h : _ = true); exact lt_irrefl true hlt⟩

/-! ### Default realization -/

/-- The realization of a head in a category is the form for the unmarked semantic association
or the form for the marked one. -/
inductive Markedness
  | unmarked
  | marked
  deriving DecidableEq, Repr

/-- The two structures of a stative. -/
inductive AdjectivalStructure
  /-- The stative head over the bare root. -/
  | basic
  /-- The stative head over a `vbecome` phrase. -/
  | result
  deriving DecidableEq, Repr

/-- The default realization of `vbecome` over a root is unmarked iff the root entails change. -/
def verbRealization (r : Root) : Markedness :=
  if Root.Kind.result ∈ r.closedKinds then .unmarked else .marked

/-- The default realization of the stative head is marked iff its complement entails change, as
a `vbecome` phrase always does. -/
def stativeRealization (r : Root) : AdjectivalStructure → Markedness
  | .basic => if Root.Kind.result ∈ r.closedKinds then .marked else .unmarked
  | .result => .marked

variable {r p : Root}

theorem verbRealization_ne_stativeRealization_basic :
    verbRealization r ≠ stativeRealization r .basic := by
  unfold verbRealization stativeRealization; split_ifs <;> decide

theorem stativeRealization_eq_unmarked_iff {a : AdjectivalStructure} :
    stativeRealization r a = .unmarked ↔ a = .basic ∧ Root.Kind.result ∉ r.closedKinds := by
  cases a <;> simp [stativeRealization]

theorem entailsChange_of_verbRealization_eq_unmarked {Entity State Event : Type*}
    {M : ArgumentStructure.EventStructure.Interpretation Entity State Event}
    {P : Entity → State → Prop} {Q : Event → Prop} (h : M.Respects P Q r.kinds)
    (hr : verbRealization r = .unmarked) :
    M.EntailsChange P :=
  h.entailsChange (by unfold verbRealization at hr; split_ifs at hr with hk; exact hk)

/-- A language's spell-out of the two realizations, in which the unmarked one is overt only if
the marked one is. -/
structure Exponence where
  /-- The realization is spelled out overtly. -/
  Overt : Markedness → Prop
  /-- The unmarked realization is overt only if the marked one is. -/
  overt_marked : Overt .unmarked → Overt .marked

theorem Exponence.trichotomy (L : Exponence) :
    (¬ L.Overt .unmarked ∧ L.Overt .marked) ∨ (L.Overt .unmarked ∧ L.Overt .marked) ∨
      (¬ L.Overt .unmarked ∧ ¬ L.Overt .marked) := by
  have := L.overt_marked; tauto

theorem Exponence.not_reverse_asymmetric (L : Exponence)
    (hr : Root.Kind.result ∈ r.closedKinds) (hp : Root.Kind.result ∉ p.closedKinds) :
    ¬ (L.Overt (verbRealization r) ∧ ¬ L.Overt (verbRealization p)) := by
  simp only [verbRealization, hr, hp, ite_true, ite_false]
  exact fun ⟨h, hn⟩ ↦ hn (L.overt_marked h)

/-! ### The coding of the survey -/

/-- The five positions of a root's paradigm. -/
inductive ParadigmPosition
  | underlyingRoot
  | simpleStative
  | inchoative
  | causative
  | resultStative
  deriving DecidableEq, Fintype, Repr

/-- The relation of a form `X` to a member `Y` of its paradigm. -/
inductive MorphRelation
  /-- The code `i` says that `X` is the input to a rule forming `Y`. -/
  | input
  /-- The code `d` says that `X` is the output of a rule on `Y`. -/
  | derived
  /-- The code `t` says that `X` is related to `Y` through a series of input and output pairs. -/
  | transitive
  /-- The code `l` says that `X` and `Y` are labile. -/
  | labile
  /-- The code `e` says that `X` and `Y` are equipollent. -/
  | equipollent
  /-- The code `u` says that no other relation applies. -/
  | unrelated
  /-- The code `n` says that `Y` is unattested. -/
  | unattested
  /-- The code `s` says that `X` is `Y`. -/
  | same
  deriving DecidableEq, Repr

/-- The code of a form gives its relation to each position of its paradigm. -/
abbrev Code := ParadigmPosition → MorphRelation

/-- The code with the given relations to the five positions, in their order. -/
def Code.of (a b c d e : MorphRelation) : Code
  | .underlyingRoot => a
  | .simpleStative => b
  | .inchoative => c
  | .causative => d
  | .resultStative => e

/-- A form is marked when it is derived from or equipollent to another member of its paradigm;
a form with only the other relations is unmarked. -/
def Code.IsMarked (c : Code) : Prop := ∃ k, c k = .derived ∨ c k = .equipollent

instance : DecidablePred Code.IsMarked := fun _ ↦ inferInstanceAs (Decidable (∃ _, _))

/-- A root's verbal paradigm is marked when its inchoative and its causative both are. -/
def VerbalParadigmMarked (inchoative causative : Code) : Prop :=
  inchoative.IsMarked ∧ causative.IsMarked

instance (i c : Code) : Decidable (VerbalParadigmMarked i c) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem tzeltal_small :
    ¬ (Code.of .unattested .same .input .transitive .transitive).IsMarked ∧
      VerbalParadigmMarked (.of .unattested .derived .same .input .input)
        (.of .unattested .transitive .derived .same .equipollent) ∧
      (Code.of .unattested .transitive .derived .equipollent .same).IsMarked := by
  decide

theorem oromo_long :
    (Code.of .derived .same .equipollent .equipollent .unattested).IsMarked ∧
      VerbalParadigmMarked (.of .derived .equipollent .same .equipollent .unattested)
        (.of .derived .equipollent .equipollent .same .unattested) := by
  decide

/-! ### The judgments -/

/-- The two diagnostics of a root's change entailment. -/
inductive Diagnostic
  /-- The stative survives a denial that a change gave rise to its state. -/
  | changeDenial
  /-- *Again* at the state presupposes an earlier state, and no earlier change. -/
  | restitutive
  deriving DecidableEq

section Diagnostics

open ModalLogic

universe u

variable {Entity : Type*} {State Event : Type u}

/-- The state description `P` of a root, applied to `x`, passes the diagnostic, with `R`
relating a state to the earlier ones. -/
def Diagnostic.Passes (M : ArgumentStructure.EventStructure.Interpretation Entity State Event)
    (R : SetRel State State) (P : Entity → State → Prop) (x : Entity) : Diagnostic → Prop
  | .changeDenial => ∃ s, DeniesChange M P x s
  | .restitutive => ∃ s, BeaversKoontzGarboden2020.againAt M .state R P x x s ≠ 0 ∧
      ¬ ◇[R] (◇[M.become] ⊤) s

end Diagnostics

/-- A root of signature `ks` passes the diagnostic when its state description passes it in some
model that respects the signature, with some manner. -/
def Passes (ks : Root.Kinds) (g : Diagnostic) : Prop :=
  ∃ (State Event : Type) (M : ArgumentStructure.EventStructure.Interpretation Unit State Event)
    (P : Unit → State → Prop) (Q : Event → Prop) (R : SetRel State State),
    M.Respects P Q ks ∧ g.Passes M R P ()

theorem passes_iff {ks : Root.Kinds} (g : Diagnostic) :
    Passes ks g ↔ Root.Kind.result ∉ Root.Kinds.close ks := by
  refine ⟨fun ⟨_, _, M, P, Q, R, hR, hg⟩ hr ↦ ?_, fun hr ↦ ⟨Bool, Unit, forged, sharp, ⊥,
    {p | p.2 < p.1}, fun p hp ↦ ?_, ?_⟩⟩
  · have hc := hR.entailsChange hr
    cases g with
    | changeDenial =>
      obtain ⟨s, hs⟩ := hg
      exact (entailsChange_iff_forall_not_deniesChange M).1 hc () s hs
    | restitutive =>
      obtain ⟨s, ha, hn⟩ := hg
      exact hn (BeaversKoontzGarboden2020.diamond_become_of_againAt_state_ne_zero hc ha)
  · have hcause : Root.Kind.cause ∉ ks :=
      fun hk ↦ hr (Root.Kinds.mem_close.2 ⟨_, hk, .result_cause⟩)
    cases p with
    | change =>
      exact absurd (Root.Kinds.mem_close.2 ⟨_, Finset.singleton_subset_iff.1 hp, le_rfl⟩) hr
    | cause => exact absurd (Finset.singleton_subset_iff.1 hp) hcause
    | manner => exact fun _ h ↦ h.elim
    | mannerOfCause => exact absurd (Finset.insert_subset_iff.1 hp).2 (by simpa using hcause)
  · cases g with
    | changeDenial => exact ⟨false, forged_deniesChange⟩
    | restitutive => exact ⟨true, forged_restitutive⟩

/-- The signature of a row's root, the least of its class. -/
def kinds? (d : Datum) : Option Root.Kinds :=
  d.parse? "root class"
    [("property concept", Root.Kinds.propertyConcept), ("result", Root.Kinds.pureResult)]

/-- The diagnostic a row tests. -/
def diagnostic? (d : Datum) : Option Diagnostic :=
  d.parse? "diagnostic" [("change denial", .changeDenial), ("restitutive again", .restitutive)]

/-- A row is accepted exactly when its root passes its diagnostic, setting aside the expected
variation: (13), acceptable to the speakers for whom *broken* has drifted to a 'not functioning'
sense, and Kakataibo, whose result root in (26) means 'not alive'. -/
theorem rows : ∀ d ∈ Examples.all, ∀ ks ∈ kinds? d, ∀ g ∈ diagnostic? d,
    (d.judgment = .acceptable ↔ Passes ks g) ∨ d.feature? "judgedBy" = some "some speakers" ∨
      d.language = "cash1251" := by
  simp only [passes_iff]
  decide

end BeaversEtAl2021
