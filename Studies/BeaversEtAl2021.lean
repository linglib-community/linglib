module

public import Studies.BeaversKoontzGarboden2020
public import Linglib.Data.Examples.BeaversEtAl2021
public import Mathlib.Data.Fintype.Basic

/-!
# Beavers et al. (2021): States and Changes of State

Beavers and colleagues argue that some roots entail change, against the Bifurcation Thesis. Under
the diagnostics of change of Beavers and Koontz-Garboden, the property-concept roots of the
examples pass and the result roots fail [outside](##rows) two judgments that
[vary](##rows_exceptions). A default realization rule makes the verb of a root unmarked iff the
root entails change, and in a model that respects the root's signature the rule
[agrees with the semantics](##entailsChange_of_verbRealization_eq_unmarked). A language that spells
out the unmarked form only when it spells out the marked one
[is of one of three types](##Exponence.trichotomy).

## Implementation notes

* The semantics is stated on `EventStructure.Interpretation`, which interprets the primitives of
  Beavers and Koontz-Garboden's book, and *again* is `Presupposition.again`. The diagnostics, and
  the readers of a row's root class and diagnostic, are those of
  `Studies/BeaversKoontzGarboden2020.lean`.
* The realization rule reads whether a root entails change off its kind signature.
* The tables of the typological survey are not represented. Its coding of markedness is
  (`Code.IsMarked`). The Modern Greek row of additive restitutive *again* is not read.

## References

* [beavers-etal-2021]
* [beavers-koontz-garboden-2020]
* [embick-2009]
* [arad-2005]
* [haspelmath-1993]
-/

@[expose] public section

namespace BeaversEtAl2021

open Presupposition ArgumentStructure
open BeaversKoontzGarboden2020 (DeniesChange Passes passes_iff kinds? diagnostic? againAt)
open scoped SetRel ModalLogic

/-! ### State predicates that entail change -/

section Model

universe u

variable {Entity : Type*} {State Event : Type u}
  (M : EventStructure.Interpretation Entity State Event)
  {R : SetRel Event Event} {P : Entity → State → Prop} {y x : Entity} {s : State}

/-- The deverbal stative of `P` holds of the states of which `P` holds and that a change gave
rise to. -/
def resultStative (P : Entity → State → Prop) (x : Entity) : State → Prop :=
  P x ⊓ ◇[M.become] ⊤

theorem not_deniesChange_resultStative : ¬ DeniesChange M (resultStative M P) x s :=
  fun h ↦ h.2 h.1.2

theorem resultStative_iff (h : M.EntailsChange P) : resultStative M P x s ↔ P x s :=
  and_iff_left_of_imp (h x s)

theorem diamond_become_of_againAt_achievement_ne_zero {e : Event}
    (hp : againAt M .achievement R P y x e ≠ 0) : ◇[R] (◇[M.become.inv] ⊤) e :=
  ModalLogic.diamond_mono R (fun w ↦ ModalLogic.diamond_mono _ le_top w) e
    (again_ne_zero_iff.1 hp)

end Model

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

/-- A row is accepted exactly when its root passes its diagnostic, except for (13), which only
some speakers accept, and Kakataibo (26). -/
theorem rows : ∀ d ∈ Examples.all, ∀ ks ∈ kinds? d, ∀ g ∈ diagnostic? d,
    (d.judgment = .acceptable ↔ Passes ks g) ∨ d = Examples.beavers_etal2021_13 ∨
      d = Examples.beavers_etal2021_26 := by
  simp only [passes_iff]
  decide

-- (13), (26): the two judgments the result roots' failure of the diagnostics mispredicts
theorem rows_exceptions :
    ∀ d ∈ [Examples.beavers_etal2021_13, Examples.beavers_etal2021_26], ∀ ks ∈ kinds? d,
      ∀ g ∈ diagnostic? d, ¬ (d.judgment = .acceptable ↔ Passes ks g) := by
  simp only [passes_iff]
  decide

end BeaversEtAl2021
