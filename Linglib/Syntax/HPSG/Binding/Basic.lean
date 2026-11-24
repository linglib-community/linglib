/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.RSRL.Interpretation
public import Linglib.Core.Data.Fin.VecNotation
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Binding.Basic
public import Linglib.Syntax.Feature.Bundle

/-!
# HPSG binding theory

Binding theory says which noun phrases a pronoun can refer back to: in *Susan likes herself* the
reflexive must refer to Susan, and in *Susan likes her* the pronoun cannot. This file states the
two principles of HPSG that account for this.

A word lists its arguments on its argument structure, the subject first. One argument *locally
o-commands* another when it comes earlier on the argument structure of the same word, and
*locally o-binds* it when the two also have the same index.

* Principle A: an anaphor that something locally o-commands is locally o-bound.
* Principle B: a personal pronoun is not locally o-bound.

Among the arguments of one word, local o-command is their order wherever no other argument
structure lists them differently (`HPSG.Binding.locallyOCommands_iff_lt`).

`HPSG.Binding.principleA_and_principleB_iff` says that the two principles hold exactly when
coindexation satisfies Conditions A and B of `Syntax/Binding` over local o-command. Person,
number and gender belong to the index, so coindexed nominal objects agree
(`HPSG.Binding.agreement_eq_of_coindexed`).

## Implementation notes

The principles are propositions about an interpretation of the signature. Their statement as
descriptions of RSRL is in `Syntax/HPSG/Binding/Description`. An argument structure is read up
to its third member. Pollard and Sag also require the commanding argument to be referential and
to differ in its `LOCAL` value; neither condition is stated. A phrase is given by the list of
its daughters. Worked examples are in `Studies/SagWasowBender2003`.

## References

* [pollard-sag-1994]
* [muller-2024-binding]
-/

@[expose] public section

namespace HPSG.Binding

open HPSG.RSRL

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

/-! ### Local o-command -/

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

variable {w : U} {f : Fin 3 → U}

/-- The members of one argument structure locally o-command one another in their order. -/
theorem locallyOCommands_of_lt (hf : ∀ m : Fin 3, argAt I w m = some (f m)) {i j : Fin 3}
    (hij : i < j) : LocallyOCommands I (f i) (f j) :=
  ⟨w, i, j, hij, hf i, hf j⟩

/-- Where every argument structure that lists two arguments of a word lists them in the word's
order, local o-command among those arguments is their order: the earlier commands the later. -/
theorem locallyOCommands_iff_lt (hf : ∀ m : Fin 3, argAt I w m = some (f m))
    (hord : ∀ w' (m n i j : Fin 3), argAt I w' m = some (f i) → argAt I w' n = some (f j) →
      m < n → i < j) {i j : Fin 3} :
    LocallyOCommands I (f i) (f j) ↔ i < j :=
  ⟨fun ⟨w', m, n, hmn, hm, hn⟩ ↦ hord w' m n i j hm hn hmn, locallyOCommands_of_lt hf⟩

/-- Two words, their argument structures and two nominal objects. -/
private inductive Swap | w₁ | w₂ | l₁ | l₁' | l₂ | l₂' | a | b

/-- The two words list the same two arguments in opposite orders. -/
private def swap : Interpretation sig Swap where
  S | .w₁ | .w₂ => .word | .a | .b => .npro | _ => .nelist
  A | .ARGST, .w₁ => some .l₁ | .ARGST, .w₂ => some .l₂
    | .FIRST, .l₁ => some .a | .REST, .l₁ => some .l₁' | .FIRST, .l₁' => some .b
    | .FIRST, .l₂ => some .b | .REST, .l₂ => some .l₂' | .FIRST, .l₂' => some .a
    | _, _ => none
  R := nofun

/-- Without the hypothesis of `locallyOCommands_iff_lt` each of two arguments can locally
o-command the other. -/
example : LocallyOCommands swap .a .b ∧ LocallyOCommands swap .b .a :=
  ⟨⟨.w₁, 0, 1, by decide, rfl, rfl⟩, ⟨.w₂, 0, 1, by decide, rfl, rfl⟩⟩

variable (I)

/-- The binding configuration of local o-command, in which every domain is the whole universe. -/
def configuration : _root_.Binding.Configuration U where
  commands a b := LocallyOCommands I a b
  domain _ := Set.univ

/-- Two entities are coindexed when they share their index. -/
def Coindexed (x y : U) : Prop := ∃ v ∈ I.A .IDX x, v ∈ I.A .IDX y

instance [DecidableEq U] (x y : U) : Decidable (Coindexed I x y) :=
  inferInstanceAs (Decidable (∃ v ∈ I.A .IDX x, v ∈ I.A .IDX y))

/-- The binding class of a sort: reflexive for an anaphor, pronoun for a personal pronoun, and none
for any other sort. -/
def Srt.bindingClass : Srt → Option _root_.Binding.BindingClass
  | .ana => some .reflexive
  | .ppro => some .pronoun
  | _ => none

theorem Srt.bindingClass_eq_some_iff {σ : Srt} {c : _root_.Binding.BindingClass} :
    σ.bindingClass = some c ↔ σ = .ana ∧ c = .reflexive ∨ σ = .ppro ∧ c = .pronoun := by
  cases σ <;> cases c <;> simp [Srt.bindingClass]

theorem Srt.le_ana_iff (σ : Srt) : σ ≤ .ana ↔ σ = .ana := by revert σ; decide

theorem Srt.le_ppro_iff (σ : Srt) : σ ≤ .ppro ↔ σ = .ppro := by revert σ; decide

/-! ### Principles A and B -/

/-- Principle A: an anaphor that something locally o-commands is locally o-bound. -/
def PrincipleA : Prop :=
  ∀ x, I.S x = .ana → ∀ y, LocallyOCommands I y x →
    ∃ z, LocallyOCommands I z x ∧ Coindexed I z x

/-- Principle B: a personal pronoun is not locally o-bound. -/
def PrincipleB : Prop :=
  ∀ x, I.S x = .ppro → ∀ y, LocallyOCommands I y x → ¬ Coindexed I y x

variable {I}

open _root_.Binding.Configuration

/-- When nothing locally o-commands itself, Principles A and B hold exactly when coindexation
satisfies Conditions A and B of `Syntax/Binding` over local o-command, with the anaphors that
nothing locally o-commands exempt. -/
theorem principleA_and_principleB_iff (hirr : ∀ x, ¬ LocallyOCommands I x x) :
    PrincipleA I ∧ PrincipleB I ↔
      (configuration I).Satisfies (Coindexed I) (configuration I).exempt
        fun x ↦ (I.S x).bindingClass := by
  have hne {a b : U} (h : LocallyOCommands I a b) : a ≠ b := fun e ↦ hirr b (e ▸ h)
  simp only [PrincipleA, PrincipleB, Satisfies, Srt.bindingClass_eq_some_iff]
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

/-- Coindexed nominal objects have the same agreement bundle. -/
theorem agreement_eq_of_coindexed {x y : U} (h : Coindexed I x y) :
    agreement I x = agreement I y := by
  obtain ⟨v, hx, hy⟩ := h
  funext d
  cases d <;> simp [agreement, Option.mem_def.1 hx, Option.mem_def.1 hy]

/-- Coindexed nominal objects agree. -/
theorem compat_agreement_of_coindexed {x y : U} (h : Coindexed I x y) :
    Compat (agreement I x) (agreement I y) :=
  agreement_eq_of_coindexed h ▸ compat_self _

private theorem elim_le_elim_of_simulatedBy {γ : Type*} [PartialOrder γ] [OrderBot γ]
    {V : Type*} {J : Interpretation sig V} {h : U → V} {x : U} {f : Srt → γ} (hf : Antitone f)
    (hS : ∀ q, I.toPartialMoore.Reaches x q → J.S (h q) ≤ I.S q)
    (hA : ∀ α q q', I.toPartialMoore.Reaches x q → I.A α q = some q' →
      J.A α (h q) = some (h q')) (β : Attr) :
    ((I.A .IDX x).bind (I.A β)).elim ⊥ (fun v ↦ f (I.S v)) ≤
      ((J.A .IDX (h x)).bind (J.A β)).elim ⊥ fun v ↦ f (J.S v) := by
  rcases hi : I.A .IDX x with _ | i
  · simp
  · have hxi : I.toPartialMoore.Reaches x i := PartialMoore.Reaches.refl.step hi
    rw [hA .IDX x i .refl hi, Option.bind_some, Option.bind_some]
    rcases hv : I.A β i with _ | v
    · simp
    · rw [hA β i v hxi hv]
      exact hf (hS v (hxi.step hv))

/-- If the machine at `x` is simulated by the machine at `y`, then the agreement bundle of `x` is at
most that of `y`. -/
theorem agreement_le_of_simulatedBy {V : Type*} {J : Interpretation sig V} {x : U} {y : V}
    (h : I.toPartialMoore.SimulatedBy J.toPartialMoore x y) :
    agreement I x ≤ agreement J y := by
  obtain ⟨f, rfl, hO, hA⟩ := h
  have hS q (hq : I.toPartialMoore.Reaches x q) : J.S (f q) ≤ I.S q :=
    OrderDual.toDual_le_toDual.1 (hO q hq)
  intro d
  cases d
  · exact elim_le_elim_of_simulatedBy Srt.antitone_toPerson hS hA .PER
  · exact elim_le_elim_of_simulatedBy Srt.antitone_toNumber hS hA .NUM
  · exact elim_le_elim_of_simulatedBy Srt.antitone_toGender hS hA .GEND
  · exact le_rfl
  · exact le_rfl

end HPSG.Binding
