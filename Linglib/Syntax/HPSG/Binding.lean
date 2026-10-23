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

/-!
# HPSG binding theory in RSRL

This file states Principles A and B of HPSG binding theory as RSRL descriptions. One argument
locally o-commands another when both are on the same argument structure and the first is less
oblique. It locally o-binds the other when, in addition, the two share their index and agree in
gender and number. Principle A requires a locally o-commanded anaphor to be locally o-bound, and
Principle B requires a personal pronoun to be locally o-free. At the root of an interpretation the
two principles are the framework-neutral Conditions A and B of `Syntax/Binding` over local
o-command, with the anaphors that nothing locally o-commands exempt.

## Main definitions

* `HPSG.RSRL.Binding.bindingSig`: the signature, with nominal-object sorts, indices, gender and
  number values, and the relation of local o-command.
* `HPSG.RSRL.Binding.principleA`: Principle A.
* `HPSG.RSRL.Binding.principleB`: Principle B.
* `HPSG.RSRL.Binding.configuration`: local o-command as a framework-neutral binding
  configuration.

## Main results

* `HPSG.RSRL.Binding.satisfies_grammar_iff`: at a root of which every entity is a component,
  the principles hold exactly when codependence satisfies the framework-neutral Conditions A and
  B over local o-command, with the anaphors that nothing locally o-commands exempt.

## Implementation notes

Coindexation and agreement are token identity of the `IDX`, `GEND` and `NUM` values, so a
coindexed anaphor that clashes with its antecedent in gender or number is not bound. The
argument structure of the verb is flattened into the attributes `SUBJ` and `OBJ`, and each model
interprets local o-command directly. Worked models of a transitive clause are in
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
the gender and number values. -/
inductive Srt
  | top | sign | synsem | ana | ppro | npro | idx
  | gender | masc | fem | number | sing | plur
  deriving DecidableEq, Fintype, Repr

/-- The attributes are the two arguments of a sign and the index, gender and number of a nominal
object. -/
inductive Attr | SUBJ | OBJ | IDX | GEND | NUM
  deriving DecidableEq, Fintype, Repr

/-- The one relation symbol is local o-command. -/
inductive Rel | locO
  deriving DecidableEq, Fintype, Repr

/-- The immediate supersort of each sort other than `top`. -/
def Srt.parent : Srt → Option Srt
  | .top => none
  | .sign | .synsem | .idx | .gender | .number => some .top
  | .ana | .ppro | .npro => some .synsem
  | .masc | .fem => some .gender
  | .sing | .plur => some .number

/-- The depth of a sort below `top`. -/
def Srt.rank : Srt → ℕ
  | .top => 0
  | .sign | .synsem | .idx | .gender | .number => 1
  | .ana | .ppro | .npro | .masc | .fem | .sing | .plur => 2

instance : PartialOrder Srt :=
  partialOrderOfCovers (fun σ τ : Srt ↦ σ.parent = some τ) Srt.rank (by decide)

instance : DecidableLE Srt :=
  decidableLEOfRank (covers := fun σ τ : Srt ↦ σ.parent = some τ) (·.parent.toList) Srt.rank
    (fun _ _ ↦ by simp) (by decide)

/-- A sign introduces the subject and the object, and a nominal object introduces the index, the
gender and the number. -/
def Attr.decl : Attr → List (Srt × Srt)
  | .SUBJ | .OBJ => [(.sign, .synsem)]
  | .IDX => [(.synsem, .idx)]
  | .GEND => [(.synsem, .gender)]
  | .NUM => [(.synsem, .number)]

/-- The signature of the binding fragment. -/
@[reducible] def sig : Signature Srt := .ofDecl Attr Rel (fun _ ↦ 2) Attr.decl (by decide)

/-- The three species of nominal object inherit the index that `synsem` introduces, and a sign
has none. -/
example : sig.approp .ana .IDX = some .idx ∧ sig.approp .sign .IDX = none := by decide

/-! ### Principles A and B -/

/-- The entities at the variables `x` and `y` are coindexed when they share their index. -/
def coindexed (x y : ℕ) : Desc sig :=
  .pathEq (.feat (.var x) .IDX) (.feat (.var y) .IDX)

/-- The entities at the variables `x` and `y` agree when they share their gender and their
number. -/
def agrees (x y : ℕ) : Desc sig :=
  .and (.pathEq (.feat (.var x) .GEND) (.feat (.var y) .GEND))
    (.pathEq (.feat (.var x) .NUM) (.feat (.var y) .NUM))

/-- The entity at `y` locally o-binds the entity at `x` when it locally o-commands it, is
coindexed with it, and agrees with it. -/
def locallyOBinds (y x : ℕ) : Desc sig :=
  .and (.rel .locO ![y, x]) (.and (coindexed y x) (agrees y x))

/-- Principle A says that a locally o-commanded anaphor is locally o-bound. -/
def principleA : Desc sig :=
  .all 0 (.imp (.and (.sortAssign (.var 0) .ana) (.ex 1 (.rel .locO ![1, 0])))
    (.ex 1 (locallyOBinds 1 0)))

/-- Principle B says that a personal pronoun is locally o-free. -/
def principleB : Desc sig :=
  .all 0 (.imp (.sortAssign (.var 0) .ppro) (.neg (.ex 1 (locallyOBinds 1 0))))

/-- The grammar of the binding fragment. -/
def grammar : Grammar sig := [principleA, principleB]

theorem freeVars_grammar : ∀ d ∈ grammar, d.freeVars = ∅ := by decide

example : (locallyOBinds 1 0).freeVars = {0, 1} := by decide

/-! ### The framework-neutral conditions -/

variable {U : Type*} (I : Interpretation sig U)

/-- Local o-command gives a binding configuration on the entities of an interpretation, in which
every domain is the whole universe, local o-command being local already. -/
def configuration : _root_.Binding.Configuration U where
  commands a b := I.R .locO ![a, b]
  domain _ := Set.univ

/-- Two entities are codependent when they share their index, gender and number, that is, when
they are coindexed and agree. -/
def Codependent (x y : U) : Prop :=
  (∃ v ∈ I.A .IDX x, v ∈ I.A .IDX y) ∧ (∃ v ∈ I.A .GEND x, v ∈ I.A .GEND y) ∧
    ∃ v ∈ I.A .NUM x, v ∈ I.A .NUM y

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
    I.Satisfies g r principleA ↔ ∀ x, I.S x = .ana → ∀ y, I.R .locO ![y, x] →
      ∃ z, I.R .locO ![z, x] ∧ Codependent I z x := by
  simp [principleA, locallyOBinds, coindexed, agrees, hr _, le_ana_iff, Matrix.comp_vec2',
    Codependent]

theorem satisfies_principleB_iff (hr : I.IsRootedAt r) (g : ℕ → U) :
    I.Satisfies g r principleB ↔ ∀ x, I.S x = .ppro → ∀ y, I.R .locO ![y, x] →
      ¬ Codependent I y x := by
  simp [principleB, locallyOBinds, coindexed, agrees, hr _, le_ppro_iff, Matrix.comp_vec2',
    Codependent]

/-- At a root of which every entity is a component, and with nothing locally o-commanding
itself, the principles hold exactly when codependence satisfies the framework-neutral Conditions
A and B over local o-command, with the anaphors that nothing locally o-commands exempt. -/
theorem satisfies_grammar_iff (hr : I.IsRootedAt r) (hirr : ∀ x, ¬ I.R .locO ![x, x]) :
    (∀ d ∈ grammar, I.Satisfies (fun _ ↦ r) r d) ↔
      (configuration I).Satisfies (Codependent I) (configuration I).exempt
        fun x ↦ (I.S x).bindingClass := by
  have hne {a b : U} (h : I.R .locO ![a, b]) : a ≠ b := fun e ↦ hirr b (e ▸ h)
  simp only [grammar, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    satisfies_principleA_iff hr, satisfies_principleB_iff hr, Satisfies,
    Srt.bindingClass_eq_some_iff]
  refine ⟨fun ⟨hA, hB⟩ x c hc ↦ ?_, fun h ↦ ⟨fun x hx y hy ↦ ?_, fun x hx y hy hc ↦ ?_⟩⟩
  · obtain ⟨hx, rfl⟩ | ⟨hx, rfl⟩ := hc
    · refine (condition_exempt_iff (.inl rfl)).2 fun ⟨y, _, _, hy⟩ ↦ ?_
      obtain ⟨z, hz, hc⟩ := hA x hx y hy
      exact ⟨z, trivial, hne hz, hc, hz⟩
    · exact fun ⟨y, _, _, hc, hy⟩ ↦ hB x hx y hy hc
  · obtain ⟨z, -, -, hc, hz⟩ := (condition_exempt_iff (.inl rfl)).1 (h x _ (.inl ⟨hx, rfl⟩))
      ⟨y, trivial, hne hy, hy⟩
    exact ⟨z, hz, hc⟩
  · exact h x _ (.inr ⟨hx, rfl⟩) ⟨y, trivial, hne hy, hc, hy⟩

theorem satisfies_of_models (hI : I.Models grammar) (hr : I.IsRootedAt r)
    (hirr : ∀ x, ¬ I.R .locO ![x, x]) :
    (configuration I).Satisfies (Codependent I) (configuration I).exempt
      fun x ↦ (I.S x).bindingClass :=
  (satisfies_grammar_iff hr hirr).1 (hI r)

end HPSG.RSRL.Binding
