/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.HPSG.Subinterpretation
public import Linglib.Core.Data.Fin.VecNotation
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Binding.Basic
public import Linglib.Syntax.Feature.Bundle

/-!
# HPSG binding theory in RSRL

This file states Principles A and B of HPSG binding theory as RSRL descriptions. A nominal
object has an index, and an index has a person, a number and a gender. Two nominal objects are
coindexed when their indices are the same entity. One argument locally o-commands another when
both are on the same argument structure and the first is less oblique, and it locally o-binds
the other when, in addition, the two are coindexed. Principle A requires a locally o-commanded
anaphor to be locally o-bound, and Principle B requires a personal pronoun to be locally
o-free.

Since the agreement features are attributes of the index, coindexed nominal objects have one
person, number and gender between them. The agreement bundle of a nominal object,
`HPSG.RSRL.Binding.agreement`, reads the three off the sorts of its index's values, a more
specific sort giving a more specific slot (`HPSG.RSRL.Binding.Srt.antitone_toGender`), and
coindexed nominal objects have the same agreement bundle
(`HPSG.RSRL.Binding.agreement_eq_of_coindexed`). The binding principles therefore mention no
agreement: an anaphor whose index differs from its antecedent's in person, number or gender is
not coindexed with it.

At the root of an interpretation the two principles are the framework-neutral Conditions A and B
of `Syntax/Binding` over local o-command, with the anaphors that nothing locally o-commands
exempt (`HPSG.RSRL.Binding.satisfies_grammar_iff`).

## Implementation notes

The argument structure of the verb is flattened into the attributes `SUBJ` and `OBJ`, and each
model interprets local o-command directly. Worked models of a transitive clause are in
`Studies/SagWasowBender2003`.

## References

* [pollard-sag-1994]
* [richter-2000]
* [muller-2024-binding]
-/

@[expose] public section

namespace HPSG.RSRL.Binding

/-! ### The signature -/

/-- The sorts are signs, the nominal objects with their three species, referential indices, and
the person, number and gender values. -/
inductive Srt
  | top | sign | synsem | ana | ppro | npro | idx
  | person | first | second | third | number | sing | plur | gender | masc | fem | neut
  deriving DecidableEq, Fintype, Repr

/-- The attributes are the two arguments of a sign, the index of a nominal object, and the
person, number and gender of an index. -/
inductive Attr | SUBJ | OBJ | IDX | PER | NUM | GEND
  deriving DecidableEq, Fintype, Repr

/-- The one relation symbol is local o-command. -/
inductive Rel | locO
  deriving DecidableEq, Fintype, Repr

/-- The immediate supersort of each sort other than `top`. -/
def Srt.parent : Srt → Option Srt
  | .top => none
  | .sign | .synsem | .idx | .person | .number | .gender => some .top
  | .ana | .ppro | .npro => some .synsem
  | .first | .second | .third => some .person
  | .sing | .plur => some .number
  | .masc | .fem | .neut => some .gender

/-- The depth of a sort below `top`. -/
def Srt.rank : Srt → ℕ
  | .top => 0
  | .sign | .synsem | .idx | .person | .number | .gender => 1
  | .ana | .ppro | .npro | .first | .second | .third | .sing | .plur | .masc | .fem | .neut => 2

instance : PartialOrder Srt :=
  partialOrderOfCovers (fun σ τ : Srt ↦ σ.parent = some τ) Srt.rank (by decide)

instance : DecidableLE Srt :=
  decidableLEOfRank (covers := fun σ τ : Srt ↦ σ.parent = some τ) (·.parent.toList) Srt.rank
    (fun _ _ ↦ by simp) (by decide)

/-- A sign introduces the subject and the object, a nominal object introduces the index, and an
index introduces the person, the number and the gender. -/
def Attr.decl : Attr → List (Srt × Srt)
  | .SUBJ | .OBJ => [(.sign, .synsem)]
  | .IDX => [(.synsem, .idx)]
  | .PER => [(.idx, .person)]
  | .NUM => [(.idx, .number)]
  | .GEND => [(.idx, .gender)]

/-- The signature of the binding fragment. -/
@[reducible] def sig : Signature Srt := .ofDecl Attr Rel (fun _ ↦ 2) Attr.decl (by decide)

/-- The three species of nominal object inherit the index that `synsem` introduces, a sign has
none, and the gender is the index's. -/
example : sig.approp .ana .IDX = some .idx ∧ sig.approp .sign .IDX = none ∧
    sig.approp .idx .GEND = some .gender ∧ sig.approp .ana .GEND = none := by decide

/-! ### Principles A and B -/

/-- The entities at the variables `x` and `y` are coindexed when they share their index. -/
def coindexed (x y : ℕ) : Formula sig :=
  .pathEq (.feat (.var x) .IDX) (.feat (.var y) .IDX)

/-- The entity at `y` locally o-binds the entity at `x` when it locally o-commands it and is
coindexed with it. -/
def locallyOBinds (y x : ℕ) : Formula sig :=
  .and (.rel .locO ![y, x]) (coindexed y x)

/-- Principle A says that a locally o-commanded anaphor is locally o-bound. -/
def principleA : Formula sig :=
  .all 0 (.imp (.and (.sortAssign (.var 0) .ana) (.ex 1 (.rel .locO ![1, 0])))
    (.ex 1 (locallyOBinds 1 0)))

/-- Principle B says that a personal pronoun is locally o-free. -/
def principleB : Formula sig :=
  .all 0 (.imp (.sortAssign (.var 0) .ppro) (.neg (.ex 1 (locallyOBinds 1 0))))

/-- The grammar of the binding fragment. -/
abbrev grammar : Grammar sig := .ofList [⟨principleA, by decide⟩, ⟨principleB, by decide⟩]

example : (locallyOBinds 1 0).freeVars = {0, 1} := by decide

/-! ### The framework-neutral conditions -/

variable {U : Type*} (I : Interpretation sig U)

/-- Local o-command gives a binding configuration on the entities of an interpretation, in which
every domain is the whole universe, local o-command being local already. -/
def configuration : _root_.Binding.Configuration U where
  commands a b := ![a, b] ∈ I.R .locO
  domain _ := Set.univ

/-- Two entities are coindexed when they share their index. -/
def Coindexed (x y : U) : Prop := ∃ v ∈ I.A .IDX x, v ∈ I.A .IDX y

instance [DecidableEq U] (x y : U) : Decidable (Coindexed I x y) :=
  inferInstanceAs (Decidable (∃ v ∈ I.A .IDX x, v ∈ I.A .IDX y))

/-- The binding class of a sort, under which an anaphor falls under Condition A, a personal
pronoun under Condition B, and a nonpronoun under none, since the fragment states no
Principle C. -/
def Srt.bindingClass : Srt → Option _root_.Binding.BindingClass
  | .ana => some .reflexive
  | .ppro => some .pronoun
  | _ => none

theorem Srt.bindingClass_eq_some_iff {σ : Srt} {c : _root_.Binding.BindingClass} :
    σ.bindingClass = some c ↔ σ = .ana ∧ c = .reflexive ∨ σ = .ppro ∧ c = .pronoun := by
  cases σ <;> cases c <;> simp [Srt.bindingClass]

private theorem le_ana_iff (σ : Srt) : σ ≤ .ana ↔ σ = .ana := by revert σ; decide

private theorem le_ppro_iff (σ : Srt) : σ ≤ .ppro ↔ σ = .ppro := by revert σ; decide

variable {I} {r : U}

open _root_.Binding.Configuration

theorem satisfies_principleA_iff (hr : I.IsRootedAt r) (g : ℕ → U) :
    I.Satisfies g r principleA ↔ ∀ x, I.S x = .ana → ∀ y, ![y, x] ∈ I.R .locO →
      ∃ z, ![z, x] ∈ I.R .locO ∧ Coindexed I z x := by
  simp [principleA, locallyOBinds, coindexed, hr _, le_ana_iff, Matrix.comp_vec2',
    Coindexed]

theorem satisfies_principleB_iff (hr : I.IsRootedAt r) (g : ℕ → U) :
    I.Satisfies g r principleB ↔ ∀ x, I.S x = .ppro → ∀ y, ![y, x] ∈ I.R .locO →
      ¬ Coindexed I y x := by
  simp [principleB, locallyOBinds, coindexed, hr _, le_ppro_iff, Matrix.comp_vec2',
    Coindexed]

/-- At a root of which every entity is a component, and with nothing locally o-commanding
itself, the principles hold exactly when coindexation satisfies the framework-neutral Conditions
A and B over local o-command, with the anaphors that nothing locally o-commands exempt. -/
theorem satisfies_grammar_iff (hr : I.IsRootedAt r) (hirr : ∀ x, ![x, x] ∉ I.R .locO) :
    (∀ d ∈ grammar, I.Satisfies (fun _ ↦ r) r d) ↔
      (configuration I).Satisfies (Coindexed I) (configuration I).exempt
        fun x ↦ (I.S x).bindingClass := by
  have hne {a b : U} (h : ![a, b] ∈ I.R .locO) : a ≠ b := fun e ↦ hirr b (e ▸ h)
  simp only [grammar, Grammar.mem_ofList, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq,
    satisfies_principleA_iff hr, satisfies_principleB_iff hr, Satisfies,
    Srt.bindingClass_eq_some_iff]
  refine ⟨fun ⟨hA, hB⟩ x c hc ↦ ?_, fun h ↦ ⟨fun x hx y hy ↦ ?_, fun x hx y hy hc ↦ ?_⟩⟩
  · obtain ⟨hx, rfl⟩ | ⟨hx, rfl⟩ := hc
    · refine (condition_exempt_iff (.inl rfl)).2 fun ⟨y, _, _, _, hy⟩ ↦ ?_
      obtain ⟨z, hz, hc⟩ := hA x hx y hy
      exact ⟨z, trivial, hne hz, hc, hz⟩
    · exact fun ⟨y, _, _, hc, hy⟩ ↦ hB x hx y hy hc
  · obtain ⟨z, -, -, hc, hz⟩ := (condition_exempt_iff (.inl rfl)).1 (h x _ (.inl ⟨hx, rfl⟩))
      ⟨y, trivial, hne hy, trivial, hy⟩
    exact ⟨z, hz, hc⟩
  · exact h x _ (.inr ⟨hx, rfl⟩) ⟨y, trivial, hne hy, hc, hy⟩

theorem satisfies_of_models (hI : I.Models grammar) (hr : I.IsRootedAt r)
    (hirr : ∀ x, ![x, x] ∉ I.R .locO) :
    (configuration I).Satisfies (Coindexed I) (configuration I).exempt
      fun x ↦ (I.S x).bindingClass :=
  (satisfies_grammar_iff hr hirr).1 fun d hd ↦ hI d hd _ r

theorem Coindexed.of_generated {r : U} {x y : {v // I.IsComponentOf r v}}
    (h : Coindexed (I.generated r) x y) : Coindexed I x y := by
  obtain ⟨v, hx, hy⟩ := h
  refine ⟨v, ?_, ?_⟩
  · rw [← Interpretation.map_val_generated_A, Option.mem_def.1 hx]; rfl
  · rw [← Interpretation.map_val_generated_A, Option.mem_def.1 hy]; rfl

/-- In a model of the grammar, an anaphor that something locally o-commands is coindexed with
something that locally o-commands it, when all are components of one entity. -/
theorem exists_coindexed_of_models (hI : I.Models grammar) {x y : U}
    (hx : I.IsComponentOf r x) (hy : I.IsComponentOf r y) (hana : I.S x = .ana)
    (hloc : ![y, x] ∈ I.R .locO) : ∃ z, ![z, x] ∈ I.R .locO ∧ Coindexed I z x := by
  have hA := (satisfies_principleA_iff (I := I.generated r) Interpretation.isRootedAt_generated
    fun _ ↦ ⟨r, .refl⟩).1 ((hI.generated r) ⟨principleA, by decide⟩
      (by simp [grammar, Grammar.mem_ofList]) _ _)
  have hval (a b : {v // I.IsComponentOf r v}) :
      ![a, b] ∈ (I.generated r).R .locO ↔ ![(a : U), (b : U)] ∈ I.R .locO := by
    show (fun i ↦ ((![a, b] i : {v // I.IsComponentOf r v}) : U)) ∈ I.R .locO ↔ _
    rw [show (fun i ↦ ((![a, b] i : {v // I.IsComponentOf r v}) : U)) = ![(a : U), (b : U)] from
      funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)]
  obtain ⟨z, hz, hc⟩ := hA ⟨x, hx⟩ hana ⟨y, hy⟩ ((hval _ _).2 hloc)
  exact ⟨z, (hval _ _).1 hz, hc.of_generated⟩

/-! ### Agreement -/

/-- The person a sort specifies: that of a person species, and nothing above the species. -/
def Srt.toPerson : Srt → Person.Specification
  | .first => .first
  | .second => .second
  | .third => .third
  | _ => ⊥

/-- The number a sort specifies. -/
def Srt.toNumber : Srt → Flat Number
  | .sing => ↑Number.singular
  | .plur => ↑Number.plural
  | _ => ⊥

/-- The gender a sort specifies. -/
def Srt.toGender : Srt → Flat UD.Gender
  | .masc => ↑UD.Gender.Masc
  | .fem => ↑UD.Gender.Fem
  | .neut => ↑UD.Gender.Neut
  | _ => ⊥

/-- A more specific sort specifies a more specific person. -/
theorem Srt.antitone_toPerson : Antitone Srt.toPerson := by unfold Antitone; decide

theorem Srt.antitone_toNumber : Antitone Srt.toNumber := by unfold Antitone; decide

theorem Srt.antitone_toGender : Antitone Srt.toGender := by unfold Antitone; decide

variable (I) in
/-- The agreement bundle of a nominal object: the person, number and gender that the sorts of its
index's `PER`, `NUM` and `GEND` values specify. -/
def agreement (x : U) : Agreement.Bundle
  | .person => ((I.A .IDX x).bind (I.A .PER)).elim ⊥ fun v ↦ (I.S v).toPerson
  | .number => ((I.A .IDX x).bind (I.A .NUM)).elim ⊥ fun v ↦ (I.S v).toNumber
  | .gender => ((I.A .IDX x).bind (I.A .GEND)).elim ⊥ fun v ↦ (I.S v).toGender
  | .case | .definiteness => ⊥

/-- Coindexed nominal objects have the same agreement bundle, the agreement features being
attributes of the index they share. -/
theorem agreement_eq_of_coindexed {x y : U} (h : Coindexed I x y) :
    agreement I x = agreement I y := by
  obtain ⟨v, hx, hy⟩ := h
  funext d
  cases d <;> simp [agreement, Option.mem_def.1 hx, Option.mem_def.1 hy]

/-- Coindexed nominal objects agree. -/
theorem compat_agreement_of_coindexed {x y : U} (h : Coindexed I x y) :
    Compat (agreement I x) (agreement I y) :=
  agreement_eq_of_coindexed h ▸ compat_self _

end HPSG.RSRL.Binding
