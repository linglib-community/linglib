/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.HPSG.Subinterpretation
public import Linglib.Syntax.HPSG.FeatureStructure
public import Linglib.Core.Data.Fin.VecNotation
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Binding.Basic
public import Linglib.Syntax.Feature.Bundle

/-!
# HPSG binding theory in RSRL

This file states Principles A and B of HPSG binding theory as RSRL descriptions. A nominal
object has an index, and an index has a person, a number and a gender. Two nominal objects are
coindexed when their indices are the same entity. A word has an argument structure, a list, and
one of its members locally o-commands another when it precedes it there, being less oblique; it
locally o-binds the other when, in addition, the two are coindexed. Local o-command is not a
relation symbol of the signature: the description `HPSG.RSRL.Binding.locallyOCommands` follows
the `ARG-ST` of some word to two of its members by paths of `REST` and `FIRST`, and
`HPSG.RSRL.Binding.LocallyOCommands` is the relation it describes in an interpretation
(`HPSG.RSRL.Binding.satisfies_locallyOCommands_iff`). Principle A requires a locally o-commanded
anaphor to be locally o-bound, and Principle B requires a personal pronoun to be locally
o-free.

Since the agreement features are attributes of the index, coindexed nominal objects have one
person, number and gender between them. The agreement bundle of a nominal object,
`HPSG.RSRL.Binding.agreement`, reads the three off the sorts of its index's values, a more
specific sort giving a more specific slot (`HPSG.RSRL.Binding.Srt.antitone_toGender`), and
coindexed nominal objects have the same agreement bundle
(`HPSG.RSRL.Binding.agreement_eq_of_coindexed`). The bundle is monotone in information: a nominal
object that subsumes another has the less specific bundle
(`HPSG.RSRL.Binding.agreement_le_of_subsumes`). The binding principles therefore mention no
agreement: an anaphor whose index differs from its antecedent's in person, number or gender is
not coindexed with it.

At the root of an interpretation the two principles are the framework-neutral Conditions A and B
of `Syntax/Binding` over local o-command, with the anaphors that nothing locally o-commands
exempt (`HPSG.RSRL.Binding.satisfies_grammar_iff`).

## Implementation notes

An argument structure is read to its third member, which is as far as the description of local
o-command reaches without a relation defined by recursion on lists. The requirements that the
commander be referential and that the two have distinct `LOCAL` values are not stated; the
fragment has no expletives and no nonlocal dependencies. A phrase is given by the list of its
daughters, with no constituent structure. Worked models are in `Studies/SagWasowBender2003`.

## References

* [pollard-sag-1994]
* [richter-2000]
* [muller-2024-binding]
-/

@[expose] public section

namespace HPSG.RSRL.Binding

/-! ### The signature -/

/-- The sorts are signs, which are phrases or words, lists, the nominal objects with their three
species and the verbal objects, referential indices, and the person, number and gender values. -/
inductive Srt
  | top | sign | phrase | word | list | elist | nelist
  | synsem | nom | ana | ppro | npro | verbal | idx
  | person | first | second | third | number | sing | plur | gender | masc | fem | neut
  deriving DecidableEq, Fintype, Repr

/-- The attributes are the daughters of a phrase, the argument structure of a word, the first
member and the rest of a nonempty list, the index of a nominal object, and the person, number
and gender of an index. -/
inductive Attr | DTRS | ARGST | FIRST | REST | IDX | PER | NUM | GEND
  deriving DecidableEq, Fintype, Repr

/-- The immediate supersort of each sort other than `top`. -/
def Srt.parent : Srt → Option Srt
  | .top => none
  | .sign | .list | .synsem | .idx | .person | .number | .gender => some .top
  | .phrase | .word => some .sign
  | .elist | .nelist => some .list
  | .nom | .verbal => some .synsem
  | .ana | .ppro | .npro => some .nom
  | .first | .second | .third => some .person
  | .sing | .plur => some .number
  | .masc | .fem | .neut => some .gender

/-- The depth of a sort below `top`. -/
def Srt.rank : Srt → ℕ
  | .top => 0
  | .sign | .list | .synsem | .idx | .person | .number | .gender => 1
  | .phrase | .word | .elist | .nelist | .nom | .verbal | .first | .second | .third | .sing
  | .plur | .masc | .fem | .neut => 2
  | .ana | .ppro | .npro => 3

instance : PartialOrder Srt :=
  partialOrderOfCovers (fun σ τ : Srt ↦ σ.parent = some τ) Srt.rank (by decide)

instance : DecidableLE Srt :=
  decidableLEOfRank (covers := fun σ τ : Srt ↦ σ.parent = some τ) (·.parent.toList) Srt.rank
    (fun _ _ ↦ by simp) (by decide)

/-- A phrase introduces its daughters, a word its argument structure, a nonempty list its first
member and its rest, a nominal object its index, and an index its person, number and gender. -/
def Attr.decl : Attr → List (Srt × Srt)
  | .DTRS => [(.phrase, .list)]
  | .ARGST => [(.word, .list)]
  | .FIRST => [(.nelist, .top)]
  | .REST => [(.nelist, .list)]
  | .IDX => [(.nom, .idx)]
  | .PER => [(.idx, .person)]
  | .NUM => [(.idx, .number)]
  | .GEND => [(.idx, .gender)]

/-- The signature of the binding fragment. It has no relation symbols. -/
@[reducible] def sig : Signature Srt := .ofDecl Attr Empty Empty.elim Attr.decl (by decide)

instance {U : Type*} (I : Interpretation sig U) (ρ : sig.Rel) : DecidablePred (· ∈ I.R ρ) :=
  ρ.elim

/-- The three species of nominal object inherit the index that `nom` introduces, a word has
none, and the gender is the index's. -/
example : sig.approp .ana .IDX = some .idx ∧ sig.approp .word .IDX = none ∧
    sig.approp .idx .GEND = some .gender ∧ sig.approp .ana .GEND = none := by decide

/-! ### Principles A and B -/

/-- The term for the member at position `m` of the argument structure of the entity at the
variable `w`: its `ARG-ST`, then `REST` `m` times, then `FIRST`. -/
def arg (w m : ℕ) : Term sig := .feat ((·.feat .REST)^[m] (.feat (.var w) .ARGST)) .FIRST

/-- The entities at the variables `x` and `y` are coindexed when they share their index. -/
def coindexed (x y : ℕ) : Formula sig :=
  .pathEq (.feat (.var x) .IDX) (.feat (.var y) .IDX)

/-- The entity at `y` locally o-commands the entity at `x` when it precedes it on the argument
structure of some word, here among the first three members. The variable `2` is bound, so `y`
and `x` are other variables. -/
def locallyOCommands (y x : ℕ) : Formula sig :=
  .ex 2 (.or (.and (.pathEq (arg 2 0) (.var y)) (.pathEq (arg 2 1) (.var x)))
    (.or (.and (.pathEq (arg 2 0) (.var y)) (.pathEq (arg 2 2) (.var x)))
      (.and (.pathEq (arg 2 1) (.var y)) (.pathEq (arg 2 2) (.var x)))))

/-- The entity at `y` locally o-binds the entity at `x` when it locally o-commands it and is
coindexed with it. -/
def locallyOBinds (y x : ℕ) : Formula sig :=
  .and (locallyOCommands y x) (coindexed y x)

/-- Principle A says that a locally o-commanded anaphor is locally o-bound. -/
def principleA : Formula sig :=
  .all 0 (.imp (.and (.sortAssign (.var 0) .ana) (.ex 1 (locallyOCommands 1 0)))
    (.ex 1 (locallyOBinds 1 0)))

/-- Principle B says that a personal pronoun is locally o-free. -/
def principleB : Formula sig :=
  .all 0 (.imp (.sortAssign (.var 0) .ppro) (.neg (.ex 1 (locallyOBinds 1 0))))

/-- The grammar of the binding fragment. -/
abbrev grammar : Grammar sig := .ofList [⟨principleA, by decide⟩, ⟨principleB, by decide⟩]

example : (locallyOBinds 1 0).freeVars = {0, 1} := by decide

/-! ### Local o-command in an interpretation -/

variable {U : Type*} (I : Interpretation sig U)

/-- The member at position `m` of the argument structure of `w`, if there is one. -/
def argAt (w : U) (m : ℕ) : Option U :=
  ((·.bind (I.A .REST))^[m] (I.A .ARGST w)).bind (I.A .FIRST)

/-- The entity `y` locally o-commands `x` when it precedes it among the first three members of
the argument structure of some word. -/
def LocallyOCommands (y x : U) : Prop :=
  ∃ w, ∃ m n : Fin 3, m < n ∧ argAt I w m = some y ∧ argAt I w n = some x

instance [Fintype U] [DecidableEq U] (y x : U) : Decidable (LocallyOCommands I y x) :=
  inferInstanceAs (Decidable (∃ w, ∃ m n : Fin 3,
    m < n ∧ argAt I w m = some y ∧ argAt I w n = some x))

variable {I}

theorem locallyOCommands_iff {y x : U} :
    LocallyOCommands I y x ↔ ∃ w, argAt I w 0 = some y ∧ argAt I w 1 = some x ∨
      argAt I w 0 = some y ∧ argAt I w 2 = some x ∨
        argAt I w 1 = some y ∧ argAt I w 2 = some x := by
  simp only [LocallyOCommands, Fin.exists_fin_succ]
  simp [or_assoc]

theorem termDenot_arg (g : ℕ → U) (u : U) (w m : ℕ) :
    I.termDenot g (arg w m) u = argAt I (g w) m := by
  have key : ∀ m, I.termDenot g ((·.feat .REST)^[m] (.feat (.var w) .ARGST)) u =
      (·.bind (I.A .REST))^[m] (I.A .ARGST (g w)) := fun m ↦ by
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Interpretation.termDenot_feat, ih]
  rw [arg, Interpretation.termDenot_feat, key, argAt]

variable (I)

/-- Local o-command gives a binding configuration on the entities of an interpretation, in which
every domain is the whole universe, local o-command being local already. -/
def configuration : _root_.Binding.Configuration U where
  commands a b := LocallyOCommands I a b
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

theorem satisfies_locallyOCommands_iff (hr : I.IsRootedAt r) (g : ℕ → U) {y x : ℕ}
    (hy : y ≠ 2) (hx : x ≠ 2) :
    I.Satisfies g r (locallyOCommands y x) ↔ LocallyOCommands I (g y) (g x) := by
  simp [locallyOCommands, termDenot_arg, locallyOCommands_iff, hr _, Function.update_of_ne hy,
    Function.update_of_ne hx, eq_comm]

theorem satisfies_principleA_iff (hr : I.IsRootedAt r) (g : ℕ → U) :
    I.Satisfies g r principleA ↔ ∀ x, I.S x = .ana → ∀ y, LocallyOCommands I y x →
      ∃ z, LocallyOCommands I z x ∧ Coindexed I z x := by
  simp [principleA, locallyOBinds, locallyOCommands, coindexed, termDenot_arg,
    locallyOCommands_iff, hr _, le_ana_iff, Coindexed, eq_comm]

theorem satisfies_principleB_iff (hr : I.IsRootedAt r) (g : ℕ → U) :
    I.Satisfies g r principleB ↔ ∀ x, I.S x = .ppro → ∀ y, LocallyOCommands I y x →
      ¬ Coindexed I y x := by
  simp [principleB, locallyOBinds, locallyOCommands, coindexed, termDenot_arg,
    locallyOCommands_iff, hr _, le_ppro_iff, Coindexed, eq_comm]

/-- At a root of which every entity is a component, and with nothing locally o-commanding
itself, the principles hold exactly when coindexation satisfies the framework-neutral Conditions
A and B over local o-command, with the anaphors that nothing locally o-commands exempt. -/
theorem satisfies_grammar_iff (hr : I.IsRootedAt r) (hirr : ∀ x, ¬ LocallyOCommands I x x) :
    (∀ d ∈ grammar, I.Satisfies (fun _ ↦ r) r d) ↔
      (configuration I).Satisfies (Coindexed I) (configuration I).exempt
        fun x ↦ (I.S x).bindingClass := by
  have hne {a b : U} (h : LocallyOCommands I a b) : a ≠ b := fun e ↦ hirr b (e ▸ h)
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
    (hirr : ∀ x, ¬ LocallyOCommands I x x) :
    (configuration I).Satisfies (Coindexed I) (configuration I).exempt
      fun x ↦ (I.S x).bindingClass :=
  (satisfies_grammar_iff hr hirr).1 fun d hd ↦ hI d hd _ r

theorem Coindexed.of_generated {r : U} {x y : {v // I.IsComponentOf r v}}
    (h : Coindexed (I.generated r) x y) : Coindexed I x y := by
  obtain ⟨v, hx, hy⟩ := h
  refine ⟨v, ?_, ?_⟩
  · rw [← Interpretation.map_val_generated_A, Option.mem_def.1 hx]; rfl
  · rw [← Interpretation.map_val_generated_A, Option.mem_def.1 hy]; rfl

theorem map_val_argAt_generated (w : {v // I.IsComponentOf r v}) (m : ℕ) :
    (argAt (I.generated r) w m).map Subtype.val = argAt I w m := by
  have key : ∀ m, ((·.bind ((I.generated r).A .REST))^[m] ((I.generated r).A .ARGST w)).map
      Subtype.val = (·.bind (I.A .REST))^[m] (I.A .ARGST w) := fun m ↦ by
    induction m with
    | zero => exact Interpretation.map_val_generated_A _
    | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, Option.map_bind,
        Option.bind_map]
      exact congrArg _ (funext fun v ↦ Interpretation.map_val_generated_A _)
  rw [argAt, argAt, ← key, Option.map_bind, Option.bind_map]
  exact congrArg _ (funext fun v ↦ Interpretation.map_val_generated_A _)

theorem LocallyOCommands.of_generated {y x : {v // I.IsComponentOf r v}}
    (h : LocallyOCommands (I.generated r) y x) : LocallyOCommands I y x := by
  obtain ⟨w, m, n, hmn, hy, hx⟩ := h
  exact ⟨w, m, n, hmn, by rw [← map_val_argAt_generated, hy]; rfl,
    by rw [← map_val_argAt_generated, hx]; rfl⟩

/-- The entity `y` locally o-commands `x` within `r` when it precedes it among the first three
members of the argument structure of a word that is a component of `r`. -/
def LocallyOCommandsWithin (I : Interpretation sig U) (r y x : U) : Prop :=
  ∃ w, I.IsComponentOf r w ∧ ∃ m n : Fin 3, m < n ∧ argAt I w m = some y ∧ argAt I w n = some x

theorem LocallyOCommandsWithin.locallyOCommands {y x : U} (h : LocallyOCommandsWithin I r y x) :
    LocallyOCommands I y x :=
  let ⟨w, _, h⟩ := h; ⟨w, h⟩

theorem isComponentOf_of_argAt {w y : U} {m : ℕ} (hw : I.IsComponentOf r w)
    (h : argAt I w m = some y) : I.IsComponentOf r y := by
  have key : ∀ (m : ℕ) (l : U), (·.bind (I.A .REST))^[m] (I.A .ARGST w) = some l →
      I.IsComponentOf r l := fun m ↦ by
    induction m with
    | zero => exact fun l hl ↦ hw.tail ⟨.ARGST, hl⟩
    | succ m ih =>
      intro l hl
      rw [Function.iterate_succ_apply'] at hl
      obtain ⟨l', hl', hl⟩ := Option.bind_eq_some_iff.1 hl
      exact (ih l' hl').tail ⟨.REST, hl⟩
  obtain ⟨l, hl, hy⟩ := Option.bind_eq_some_iff.1 h
  exact (key m l hl).tail ⟨.FIRST, hy⟩

theorem locallyOCommands_generated_iff {y x : {v // I.IsComponentOf r v}} :
    LocallyOCommands (I.generated r) y x ↔ LocallyOCommandsWithin I r y x := by
  refine ⟨fun ⟨w, m, n, hmn, hy, hx⟩ ↦ ⟨w, w.2, m, n, hmn,
      by rw [← map_val_argAt_generated, hy]; rfl, by rw [← map_val_argAt_generated, hx]; rfl⟩,
    fun ⟨w, hw, m, n, hmn, hy, hx⟩ ↦ ⟨⟨w, hw⟩, m, n, hmn, ?_, ?_⟩⟩
  · obtain ⟨y', hy', e⟩ := Option.map_eq_some_iff.1
      ((map_val_argAt_generated ⟨w, hw⟩ m).trans hy)
    rw [hy', Subtype.ext e]
  · obtain ⟨x', hx', e⟩ := Option.map_eq_some_iff.1
      ((map_val_argAt_generated ⟨w, hw⟩ n).trans hx)
    rw [hx', Subtype.ext e]

theorem coindexed_generated_iff {x y : {v // I.IsComponentOf r v}} :
    Coindexed (I.generated r) x y ↔ Coindexed I x y := by
  refine ⟨Coindexed.of_generated, fun ⟨v, hx, hy⟩ ↦ ?_⟩
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1
    ((Interpretation.map_val_generated_A (I := I) (r := r) (v := x) .IDX).trans hx)
  obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.1
    ((Interpretation.map_val_generated_A (I := I) (r := r) (v := y) .IDX).trans hy)
  exact ⟨a, ha, by rw [Option.mem_def, hb, Subtype.ext e]⟩

/-- An entity satisfies the binding principles, the quantifiers ranging over its components,
exactly when every anaphor among them that something locally o-commands is locally o-bound and
every personal pronoun among them is locally o-free, local o-command being within the entity. -/
theorem satisfies_grammar_iff_within (r : U) :
    (∀ d ∈ grammar, I.Satisfies (fun _ ↦ r) r d) ↔
      (∀ x, I.IsComponentOf r x → I.S x = .ana → ∀ y, LocallyOCommandsWithin I r y x →
        ∃ z, LocallyOCommandsWithin I r z x ∧ Coindexed I z x) ∧
      ∀ x, I.IsComponentOf r x → I.S x = .ppro → ∀ y, LocallyOCommandsWithin I r y x →
        ¬ Coindexed I y x := by
  have hg (d : Formula sig) : I.Satisfies (fun _ ↦ r) r d ↔
      (I.generated r).Satisfies (fun _ ↦ ⟨r, .refl⟩) ⟨r, .refl⟩ d :=
    (Interpretation.satisfies_generated (v := ⟨r, .refl⟩)
      (g := fun _ ↦ (⟨r, .refl⟩ : {v // I.IsComponentOf r v})) (d := d)).symm
  have hc {y x : U} (h : LocallyOCommandsWithin I r y x) : I.IsComponentOf r y :=
    let ⟨_, hw, _, _, _, hy, _⟩ := h; isComponentOf_of_argAt hw hy
  simp only [grammar, Grammar.mem_ofList, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, hg,
    satisfies_principleA_iff Interpretation.isRootedAt_generated,
    satisfies_principleB_iff Interpretation.isRootedAt_generated]
  refine and_congr ⟨fun h x hx hana y hy ↦ ?_, fun h x hana y hy ↦ ?_⟩
    ⟨fun h x hx hp y hy hco ↦ ?_, fun h x hp y hy hco ↦ ?_⟩
  · obtain ⟨z, hz, hco⟩ := h ⟨x, hx⟩ hana ⟨y, hc hy⟩ (locallyOCommands_generated_iff.2 hy)
    exact ⟨z, locallyOCommands_generated_iff.1 hz, coindexed_generated_iff.1 hco⟩
  · obtain ⟨z, hz, hco⟩ := h x x.2 hana y (locallyOCommands_generated_iff.1 hy)
    exact ⟨⟨z, hc hz⟩, locallyOCommands_generated_iff.2 hz, coindexed_generated_iff.2 hco⟩
  · exact h ⟨x, hx⟩ hp ⟨y, hc hy⟩ (locallyOCommands_generated_iff.2 hy)
      (coindexed_generated_iff.2 hco)
  · exact h x x.2 hp y (locallyOCommands_generated_iff.1 hy) (coindexed_generated_iff.1 hco)

/-- In a model of the grammar, an anaphor that follows something on the argument structure of a
word is coindexed with something that locally o-commands it, when the word and the anaphor are
components of one entity. -/
theorem exists_coindexed_of_models (hI : I.Models grammar) {w x y : U} {m n : Fin 3}
    (hw : I.IsComponentOf r w) (hmn : m < n) (hy : argAt I w m = some y)
    (hx : argAt I w n = some x) (hana : I.S x = .ana) :
    ∃ z, LocallyOCommands I z x ∧ Coindexed I z x := by
  have hA := (satisfies_principleA_iff (I := I.generated r) Interpretation.isRootedAt_generated
    fun _ ↦ ⟨r, .refl⟩).1 ((hI.generated r) ⟨principleA, by decide⟩
      (by simp [grammar, Grammar.mem_ofList]) _ _)
  obtain ⟨y', hy', rfl⟩ := Option.map_eq_some_iff.1
    ((map_val_argAt_generated ⟨w, hw⟩ m).trans hy)
  obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.1
    ((map_val_argAt_generated ⟨w, hw⟩ n).trans hx)
  obtain ⟨z, hz, hc⟩ := hA x' hana y' ⟨⟨w, hw⟩, m, n, hmn, hy', hx'⟩
  exact ⟨z, hz.of_generated, hc.of_generated⟩

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

private theorem elim_le_elim_of_subsumes {γ : Type*} [PartialOrder γ] [OrderBot γ]
    {V : Type*} {J : Interpretation sig V} {h : U → V} {x : U} {f : Srt → γ} (hf : Antitone f)
    (hS : ∀ q, I.IsComponentOf x q → J.S (h q) ≤ I.S q)
    (hA : ∀ α q q', I.IsComponentOf x q → I.A α q = some q' → J.A α (h q) = some (h q'))
    (β : Attr) :
    ((I.A .IDX x).bind (I.A β)).elim ⊥ (fun v ↦ f (I.S v)) ≤
      ((J.A .IDX (h x)).bind (J.A β)).elim ⊥ fun v ↦ f (J.S v) := by
  rcases hi : I.A .IDX x with _ | i
  · simp
  · have hxi : I.IsComponentOf x i := .single ⟨.IDX, hi⟩
    rw [hA .IDX x i .refl hi, Option.bind_some, Option.bind_some]
    rcases hv : I.A β i with _ | v
    · simp
    · rw [hA β i v hxi hv]
      exact hf (hS v (hxi.tail ⟨β, hv⟩))

/-- A nominal object that subsumes another has the less specific agreement bundle: the map from
the feature structures of the fragment to agreement bundles is monotone in information. -/
theorem agreement_le_of_subsumes {V : Type*} {J : Interpretation sig V} {x : U} {y : V}
    (h : I.Subsumes J x y) : agreement I x ≤ agreement J y := by
  obtain ⟨f, rfl, hS, hA⟩ := h
  intro d
  cases d
  · exact elim_le_elim_of_subsumes Srt.antitone_toPerson hS hA .PER
  · exact elim_le_elim_of_subsumes Srt.antitone_toNumber hS hA .NUM
  · exact elim_le_elim_of_subsumes Srt.antitone_toGender hS hA .GEND
  · exact le_rfl
  · exact le_rfl

end HPSG.RSRL.Binding
