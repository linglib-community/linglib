/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Assignment
public import Linglib.Semantics.Composition.Ty
public import Linglib.Semantics.Reference.Rigidity
public import Linglib.Semantics.Quantification.Polyadic
public import Mathlib.Data.Fin.VecNotation

/-!
# Montague (1973): The Proper Treatment of Quantification in Ordinary English

Montague's fragment of English builds its sentences by analysis trees, which record the rules
used, so a sentence with two readings has two trees. An interpretation gives every word a sense,
its extension at each index (a possible world at a moment). Nouns and verbs apply to individual
concepts, functions from indices to individuals, so *the temperature* can name something whose
value changes over time. Montague's meaning postulates single out the logically possible
interpretations. In these, names and ordinary nouns concern only constant concepts, those with
the same value at every index, and most verbs depend only on the current values of their
arguments. One sentence entails another when every logically possible interpretation makes the
second true wherever it makes the first true.

## Implementation notes

Montague translates each tree into intensional logic and then interprets the logic;
`Analysis.realize` does both steps at once, as his footnote 13 allows. One index type stands for
his world–moment pairs, and tense is omitted. Of his nine meaning postulates, only the five that
mention no word outside the fragment are imposed.

## References

* [montague-1973]
-/

@[expose] public section

namespace Montague1973

open Montague Quantifier Polyadic

/-! ### Categories and the category-to-type map -/

/-- The syntactic categories are `e`, `t`, and the functor categories `A/B` and `A//B`, which
are distinct categories with the same type. -/
inductive Cat where
  | e | t
  | slash : Cat → Cat → Cat
  | dslash : Cat → Cat → Cat
  deriving DecidableEq, Repr

namespace Cat

/-- IV = t/e is the category of intransitive verb phrases. -/
abbrev IV : Cat := .slash .t .e
/-- T = t/IV is the category of terms. -/
abbrev T : Cat := .slash .t IV
/-- TV = IV/T is the category of transitive verb phrases. -/
abbrev TV : Cat := .slash IV T
/-- CN = t//e is the category of common noun phrases. -/
abbrev CN : Cat := .dslash .t .e

/-- The category-to-type map `f` sends `e` to `e`, `t` to `t`, and both `A/B` and `A//B` to
`⟨⟨s, f(B)⟩, f(A)⟩`. -/
abbrev ty : Cat → Ty
  | .e => .e
  | .t => .t
  | .slash a b | .dslash a b => .intens b.ty ⇒ a.ty

example : T.ty = (.intens (.intens .e ⇒ .t) ⇒ .t) := rfl
example : CN.ty = IV.ty := rfl

end Cat

/-! ### Basic expressions and analysis trees -/

/-- T1(d) translates the proper nouns through the constants `j`, `m`, `b`, `n` of type `e`. -/
inductive ProperNoun where
  | john | mary | bill | ninety

/-- `Basic A` holds the basic expressions of category `A` in the domain of `g` that the examples
use, which T1(a) translates into constants. *be*, *necessarily* and the basic terms are outside
the domain of `g`. -/
inductive Basic : Cat → Type
  | man : Basic .CN
  | woman : Basic .CN
  | unicorn : Basic .CN
  | price : Basic .CN
  | temperature : Basic .CN
  | walk : Basic .IV
  | rise : Basic .IV
  | love : Basic .TV
  | find : Basic .TV
  | seek : Basic .TV

/-- `Analysis A` is the type of analysis trees of category `A` built by the rules the examples
use. The leaves are the basic expressions of S1, split as T1 translates them into the domain of
`g`, the proper nouns, the pronouns `heₙ` and *be*; the nodes are the determiners of S2,
subject–predicate `F₄` (S4), verb–object `F₅` (S5) and quantifying-in `F₁₀,ₙ` (S14). -/
inductive Analysis : Cat → Type
  | basic {A : Cat} : Basic A → Analysis A
  | name : ProperNoun → Analysis .T
  | he (n : ℕ) : Analysis .T
  | be : Analysis .TV
  | every : Analysis .CN → Analysis .T
  | the : Analysis .CN → Analysis .T
  | a : Analysis .CN → Analysis .T
  | f4 : Analysis .T → Analysis .IV → Analysis .t
  | f5 : Analysis .TV → Analysis .T → Analysis .IV
  | f10 (n : ℕ) : Analysis .T → Analysis .t → Analysis .t

/-! ### Interpretations and the induced interpretation of English -/

variable (E W : Type)

/-- An interpretation `⟨A, I, J, ≤, F⟩` of the fragment's constants has one type `W` of points of
reference, and `F` gives each constant a sense, an extension at every index. -/
structure Interp where
  /-- `F` assigns each of the constants `j`, `m`, `b`, `n` an individual concept. -/
  name : ProperNoun → W → E
  /-- `F` assigns the constant `g(α)` a sense of type `f(A)`. -/
  const {A : Cat} : Basic A → W → Ty.Domain E W A.ty

variable {E W}

/-- `φ.realize M g i` is the extension at index `i`, under the assignment `g` of the
individual-concept variables `xₙ`, of the translation of `φ` by T1, T2, T4, T5 and T14. The
proper nouns translate to `j*`, …, that is `P̂ P{^j}`; `heₙ` to `P̂ P{xₙ}`; *be* to
`𝒫̂ x̂ 𝒫{ŷ [ˇx = ˇy]}`; the determiners to the quantifiers *every*, *the* and *some* over
individual concepts; the rules of functional application to `δ'(^β')`; and quantifying-in to
`α'(x̂ₙ φ')`. -/
def Analysis.realize (M : Interp E W) :
    {A : Cat} → Analysis A → Assignment (W → E) → W → Ty.Domain E W A.ty
  | _, .basic α, _, i => M.const α i
  | _, .name α, _, i => fun P ↦ P i (M.name α)
  | _, .he n, g, i => fun P ↦ P i (g n)
  | _, .be, _, i => fun Q x ↦ Q i fun j y ↦ x j = y j
  | _, .every ζ, g, i => fun P ↦ GQ.every (ζ.realize M g i) (P i)
  | _, .the ζ, g, i => fun P ↦ GQ.the (ζ.realize M g i) (P i)
  | _, .a ζ, g, i => fun P ↦ GQ.some (ζ.realize M g i) (P i)
  | _, .f4 α δ, g, i => α.realize M g i fun j ↦ δ.realize M g j
  | _, .f5 δ β, g, i => δ.realize M g i fun j ↦ β.realize M g j
  | _, .f10 n α φ, g, i => α.realize M g i fun j x ↦ φ.realize M (Function.update g n x) j

/-! ### `*`-counterparts and extensional senses

`rigidCN`, `extIV` and `extTV` build a sense from a set of individuals or a relation between
them, and `δ*` recovers the set or relation from the sense. -/

/-- `starIV δ` is `δ*` for `δ` of type `f(IV) = f(CN)`, the set `û δ(^u)` of individuals whose
constant concept is in `δ`. -/
def starIV (δ : Ty.Domain E W (.intens .e ⇒ .t)) : E → Prop := fun u ↦ δ fun _ ↦ u

/-- `starTV δ` is `δ*` for `δ` of type `f(TV)`, the relation `v̂ û δ(^u, ^v*)` with the object
first, so `starTV δ v u` says that `u` bears `δ` to `v`. -/
def starTV (δ : Ty.Domain E W Cat.TV.ty) : E → E → Prop :=
  fun v u ↦ δ (fun j P ↦ P j fun _ ↦ v) fun _ ↦ u

/-- `rigidCN m` is the common-noun sense holding of the constant concepts of members of `m`, the
form postulate (2) gives an ordinary noun. -/
def rigidCN (m : W → E → Prop) : W → Ty.Domain E W Cat.CN.ty := fun i x ↦ IsRigid x ∧ m i (x i)

/-- `extIV m` is the intransitive-verb sense `x̂ M{ˇx}` of a property `M` of individuals, the
form postulate (3) requires. -/
def extIV (m : W → E → Prop) : W → Ty.Domain E W Cat.IV.ty := fun i x ↦ m i (x i)

/-- `extTV S` is the transitive-verb sense `𝒫̂ x̂ 𝒫{ŷ S{ˇx, ˇy}}` of a relation-in-intension `S`
between individuals, object first, the form postulate (4) requires. -/
def extTV (S : W → E → E → Prop) : W → Ty.Domain E W Cat.TV.ty :=
  fun i Q x ↦ Q i fun j y ↦ S j (y j) (x j)

@[simp] theorem starIV_rigidCN (m : W → E → Prop) (i : W) : starIV (rigidCN m i) = m i :=
  funext fun u ↦ propext ⟨And.right, And.intro (isRigid_const u)⟩

@[simp] theorem starIV_extIV (m : W → E → Prop) (i : W) : starIV (extIV m i) = m i := rfl

@[simp] theorem starTV_extTV (S : W → E → E → Prop) (i : W) : starTV (extTV S i) = S i := rfl

-- (4)
theorem realize_be (M : Interp E W) (g : Assignment (W → E)) :
    (fun i ↦ (Analysis.be : Analysis .TV).realize M g i) = extTV fun _ v u ↦ u = v :=
  rfl

/-! ### Meaning postulates and logical consequence -/

/-- An interpretation is logically possible when the meaning postulates (1)–(5) hold. The proper
nouns are rigid, the ordinary common nouns (all but *price* and *temperature*) hold only of
constant concepts, the intransitive verbs other than *rise* and the transitive verbs other than
*seek* are extensional, and *seek* is extensional in subject position. -/
structure Interp.LogicallyPossible (M : Interp E W) : Prop where
  /-- Postulate (1) is `∨u □[u = α]`. -/
  name_rigid (α : ProperNoun) : IsRigid (M.name α)
  /-- Postulate (2) is `□[δ(x) → ∨u x = ^u]`. -/
  noun_rigid (α : Basic .CN) : α ≠ .price → α ≠ .temperature →
    ∀ i x, M.const α i x → IsRigid x
  /-- Postulate (3) is `∨M ∧x □[δ(x) ↔ M{ˇx}]`. -/
  iv_ext (α : Basic .IV) : α ≠ .rise → M.const α ∈ Set.range extIV
  /-- Postulate (4) is `∨S ∧x ∧𝒫 □[δ(x, 𝒫) ↔ 𝒫{ŷ S{ˇx, ˇy}}]`. -/
  tv_ext (α : Basic .TV) : α ≠ .seek → M.const α ∈ Set.range extTV
  /-- Postulate (5) is `∧𝒫 ∨M ∧x □[δ(x, 𝒫) ↔ M{ˇx}]`. -/
  seek_ext (Q : W → Ty.Domain E W Cat.T.ty) : (fun i ↦ M.const .seek i Q) ∈ Set.range extIV

/-- `Γ` entails `ψ` when every logically possible interpretation makes `ψ` true at every index
at which it makes every member of `Γ` true, a sentence being true at an index when its
translation is true there under every assignment. -/
def Entails (Γ : Set (Analysis .t)) (ψ : Analysis .t) : Prop :=
  ∀ ⦃E W : Type⦄ (M : Interp E W), M.LogicallyPossible → ∀ i,
    (∀ φ ∈ Γ, ∀ g, φ.realize M g i) → ∀ g, ψ.realize M g i

namespace Interp.LogicallyPossible

variable {M : Interp E W} (h : M.LogicallyPossible)
include h

theorem rigidCN_starIV {α : Basic .CN} (h₁ : α ≠ .price) (h₂ : α ≠ .temperature) :
    rigidCN (fun i ↦ starIV (M.const α i)) = M.const α := by
  refine funext fun i ↦ funext fun x ↦ propext ⟨fun ⟨hr, hx⟩ ↦ ?_, fun hx ↦ ?_⟩
  · rwa [hr.eq_const i]
  · have hr := h.noun_rigid α h₁ h₂ i x hx
    rw [hr.eq_const i] at hx
    exact ⟨hr, hx⟩

theorem extIV_starIV {α : Basic .IV} (hα : α ≠ .rise) :
    extIV (fun i ↦ starIV (M.const α i)) = M.const α := by
  obtain ⟨m, hm⟩ := h.iv_ext α hα
  rw [← hm]
  rfl

/-- A transitive verb other than *seek* is definable from its `*`-counterpart,
`□[δ(x, 𝒫) ↔ 𝒫{ŷ δ*(ˇx, ˇy)}]`. -/
theorem extTV_starTV {α : Basic .TV} (hα : α ≠ .seek) :
    extTV (fun i ↦ starTV (M.const α i)) = M.const α := by
  obtain ⟨S, hS⟩ := h.tv_ext α hα
  rw [← hS]
  rfl

end Interp.LogicallyPossible

/-! ### Quantifying over constant concepts

When a quantifier's restriction holds only of constant concepts, as an ordinary noun does,
quantifying over the concepts is quantifying over individuals. -/

section Rigid

variable [Nonempty W] {R S : (W → E) → Prop}

theorem every_iff_of_rigid (hR : ∀ x, R x → IsRigid x) :
    GQ.every R S ↔ GQ.every (starIV R) (starIV S) := by
  obtain ⟨i⟩ := ‹Nonempty W›
  refine ⟨fun H u hu ↦ H _ hu, fun H x hx ↦ ?_⟩
  have e := (hR x hx).eq_const i
  rw [e]
  exact H _ (e ▸ hx)

theorem some_iff_of_rigid (hR : ∀ x, R x → IsRigid x) :
    GQ.some R S ↔ GQ.some (starIV R) (starIV S) := by
  obtain ⟨i⟩ := ‹Nonempty W›
  refine ⟨fun ⟨x, hx, hs⟩ ↦ ?_, fun ⟨u, hu, hs⟩ ↦ ⟨_, hu, hs⟩⟩
  have e := (hR x hx).eq_const i
  exact ⟨x i, e ▸ hx, e ▸ hs⟩

theorem the_iff_of_rigid (hR : ∀ x, R x → IsRigid x) :
    GQ.the R S ↔ GQ.the (starIV R) (starIV S) := by
  obtain ⟨i⟩ := ‹Nonempty W›
  constructor
  · rintro ⟨y, hy, hs⟩
    have e := (hR y ((hy y).2 rfl)).eq_const i
    rw [e] at hy hs
    exact ⟨y i, fun u ↦ (hy _).trans ⟨fun e ↦ congrFun e i, congrArg fun v _ ↦ v⟩, hs⟩
  · rintro ⟨v, hv, hs⟩
    refine ⟨fun _ ↦ v, fun x ↦ ⟨fun hx ↦ ?_, fun e ↦ e ▸ (hv v).2 rfl⟩, hs⟩
    have e := (hR x hx).eq_const i
    rw [e]
    exact congrArg (fun w _ ↦ w) ((hv _).1 (e ▸ hx))

end Rigid

/-! ### The examples of §4: extensional cases -/

open Analysis Basic ProperNoun

section Extensional

variable {M : Interp E W} (h : M.LogicallyPossible) (g : Assignment (W → E)) (i : W)
include h

theorem bill_walks_iff :
    (f4 (name bill) (basic walk)).realize M g i ↔ starIV (M.const walk i) (M.name bill i) :=
  iff_of_eq (congrArg (M.const walk i) ((h.name_rigid bill).eq_const i))

/-- *a man walks* translates to `∨u[man'*(u) ∧ walk'*(u)]`. -/
theorem a_man_walks_iff :
    (f4 (a (basic man)) (basic walk)).realize M g i ↔
      GQ.some (starIV (M.const man i)) (starIV (M.const walk i)) :=
  have := Nonempty.intro i
  some_iff_of_rigid (h.noun_rigid man nofun nofun i)

/-- *every man walks* translates to `∧u[man'*(u) → walk'*(u)]`. -/
theorem every_man_walks_iff :
    (f4 (every (basic man)) (basic walk)).realize M g i ↔
      GQ.every (starIV (M.const man i)) (starIV (M.const walk i)) :=
  have := Nonempty.intro i
  every_iff_of_rigid (h.noun_rigid man nofun nofun i)

/-- *the man walks* translates to `∨v∧u[[man'*(u) ↔ u = v] ∧ walk'*(v)]`. -/
theorem the_man_walks_iff :
    (f4 (the (basic man)) (basic walk)).realize M g i ↔
      GQ.the (starIV (M.const man i)) (starIV (M.const walk i)) :=
  have := Nonempty.intro i
  the_iff_of_rigid (h.noun_rigid man nofun nofun i)

theorem john_finds_a_unicorn_iff :
    (f4 (name john) (f5 (basic find) (a (basic unicorn)))).realize M g i ↔
      GQ.some (starIV (M.const unicorn i)) (starTV (M.const find i) · (M.name john i)) := by
  have := Nonempty.intro i
  obtain ⟨S, hS⟩ := h.tv_ext find nofun
  simp only [realize, ← hS]
  rw [(h.name_rigid john).eq_const i]
  exact some_iff_of_rigid (h.noun_rigid unicorn nofun nofun i)

omit h in
theorem bill_is_mary_iff :
    (f4 (name bill) (f5 be (name mary))).realize M g i ↔ M.name bill i = M.name mary i :=
  Iff.rfl

theorem bill_is_a_man_iff :
    (f4 (name bill) (f5 be (a (basic man)))).realize M g i ↔
      starIV (M.const man i) (M.name bill i) := by
  have := Nonempty.intro i
  refine (some_iff_of_rigid (h.noun_rigid man nofun nofun i)).trans
    ⟨fun ⟨_, hu, e⟩ ↦ ?_, fun hb ↦ ⟨_, hb, rfl⟩⟩
  obtain rfl : M.name bill i = _ := e
  exact hu

end Extensional

/-! ### *A woman loves every man*: two analysis trees -/

/-- The direct analysis of *a woman loves every man* is `F₄(a woman, F₅(love, every man))`. -/
def aWomanLovesEveryMan.direct : Analysis .t :=
  f4 (a (basic woman)) (f5 (basic love) (every (basic man)))

/-- The quantifying-in analysis of *a woman loves every man* is
`F₁₀,₀(every man, F₄(a woman, F₅(love, he₀)))`. -/
def aWomanLovesEveryMan.quantifiedIn : Analysis .t :=
  f10 0 (every (basic man)) (f4 (a (basic woman)) (f5 (basic love) (he 0)))

namespace aWomanLovesEveryMan

section

variable {M : Interp E W} (h : M.LogicallyPossible) (g : Assignment (W → E)) (i : W)
include h

theorem direct_iff :
    direct.realize M g i ↔ surfaceScope GQ.some GQ.every (starIV (M.const woman i))
      (starIV (M.const man i)) (flip (starTV (M.const love i))) := by
  have := Nonempty.intro i
  obtain ⟨S, hS⟩ := h.tv_ext love nofun
  simp only [direct, realize, ← hS]
  exact (some_iff_of_rigid (h.noun_rigid woman nofun nofun i)).trans <|
    exists_congr fun _ ↦ and_congr_right fun _ ↦
      every_iff_of_rigid (h.noun_rigid man nofun nofun i)

theorem quantifiedIn_iff :
    quantifiedIn.realize M g i ↔ inverseScope GQ.some GQ.every (starIV (M.const woman i))
      (starIV (M.const man i)) (flip (starTV (M.const love i))) := by
  have := Nonempty.intro i
  obtain ⟨S, hS⟩ := h.tv_ext love nofun
  simp only [quantifiedIn, realize, Function.update_self, ← hS]
  exact (every_iff_of_rigid (h.noun_rigid man nofun nofun i)).trans <|
    forall_congr' fun _ ↦ imp_congr_right fun _ ↦
      some_iff_of_rigid (h.noun_rigid woman nofun nofun i)

end

end aWomanLovesEveryMan

/-! ### Countermodels over one index -/

/-- `staticInterp` has a single index and four individuals, the men `0` and `1` and the women `2`
and `3`. Each man is loved by a woman, no woman loves both men, nothing is a unicorn, and John
seeks everything. -/
def staticInterp : Interp ℕ Unit where
  name
    | .john => fun _ ↦ 0
    | .bill => fun _ ↦ 1
    | .mary => fun _ ↦ 2
    | .ninety => fun _ ↦ 90
  const
    | .man => rigidCN fun _ u ↦ u = 0 ∨ u = 1
    | .woman => rigidCN fun _ u ↦ u = 2 ∨ u = 3
    | .unicorn | .price | .temperature => rigidCN fun _ _ ↦ False
    | .walk | .rise => extIV fun _ _ ↦ False
    | .love => extTV fun _ v u ↦ u = 2 ∧ v = 0 ∨ u = 3 ∧ v = 1
    | .find => extTV fun _ _ _ ↦ False
    | .seek => fun _ _ _ ↦ True

theorem staticInterp_logicallyPossible : staticInterp.LogicallyPossible where
  name_rigid _ := isRigid_of_subsingleton _
  noun_rigid _ _ _ _ _ _ := isRigid_of_subsingleton _
  iv_ext
    | .walk, _ => ⟨fun _ _ ↦ False, rfl⟩
  tv_ext
    | .love, _ => ⟨fun _ v u ↦ u = 2 ∧ v = 0 ∨ u = 3 ∧ v = 1, rfl⟩
    | .find, _ => ⟨fun _ _ _ ↦ False, rfl⟩
  seek_ext _ := ⟨fun _ _ ↦ True, rfl⟩

/-- *A woman loves every man* is ambiguous, since its quantifying-in reading does not entail its
direct one. -/
theorem aWomanLovesEveryMan.not_entails : ¬ Entails {quantifiedIn} direct := fun H ↦ by
  have h := staticInterp_logicallyPossible
  have hd := H staticInterp h () (fun φ hφ g ↦ by
    rw [Set.mem_singleton_iff.1 hφ, quantifiedIn_iff h]
    rintro v ⟨-, rfl | rfl⟩
    · exact ⟨2, ⟨isRigid_const _, Or.inl rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨3, ⟨isRigid_const _, Or.inr rfl⟩, Or.inr ⟨rfl, rfl⟩⟩) fun _ _ ↦ 0
  obtain ⟨u, -, hu⟩ := (direct_iff h _ ()).1 hd
  have h0 := hu 0 ⟨isRigid_const _, Or.inl rfl⟩
  have h1 := hu 1 ⟨isRigid_const _, Or.inr rfl⟩
  simp only [flip, starTV_extTV, staticInterp] at h0 h1
  omega

/-! ### *John seeks a unicorn*: de dicto and de re -/

/-- The de dicto analysis of *John seeks a unicorn* is `F₄(John, F₅(seek, a unicorn))`. -/
def johnSeeksAUnicorn.deDicto : Analysis .t :=
  f4 (name john) (f5 (basic seek) (a (basic unicorn)))

/-- The de re analysis of *John seeks a unicorn* is
`F₁₀,₀(a unicorn, F₄(John, F₅(seek, he₀)))`. -/
def johnSeeksAUnicorn.deRe : Analysis .t :=
  f10 0 (a (basic unicorn)) (f4 (name john) (f5 (basic seek) (he 0)))

namespace johnSeeksAUnicorn

section

variable {M : Interp E W} (h : M.LogicallyPossible) (g : Assignment (W → E)) (i : W)
include h

theorem deDicto_iff :
    deDicto.realize M g i ↔ M.const seek i (fun j P ↦ GQ.some (starIV (M.const unicorn j))
      (starIV (P j))) (M.name john) :=
  have := Nonempty.intro i
  iff_of_eq <| congrArg (M.const seek i · _) <| funext fun j ↦ funext fun _ ↦
    propext (some_iff_of_rigid (h.noun_rigid unicorn nofun nofun j))

theorem deRe_iff :
    deRe.realize M g i ↔
      GQ.some (starIV (M.const unicorn i)) (starTV (M.const seek i) · (M.name john i)) := by
  have := Nonempty.intro i
  simp only [deRe, realize, Function.update_self]
  rw [(h.name_rigid john).eq_const i]
  exact some_iff_of_rigid (h.noun_rigid unicorn nofun nofun i)

/-- The de re reading entails that there are unicorns. -/
theorem exists_unicorn_of_deRe (H : deRe.realize M g i) : ∃ u, starIV (M.const unicorn i) u :=
  ((deRe_iff h g i).1 H).imp fun _ ↦ And.left

end

theorem deDicto_without_unicorns (g : Assignment (Unit → ℕ)) :
    deDicto.realize staticInterp g () ∧ ∀ u, ¬ starIV (staticInterp.const unicorn ()) u :=
  ⟨trivial, fun _ h ↦ h.2⟩

/-- *John seeks a unicorn* is ambiguous, since its de dicto reading does not entail its de re
one. -/
theorem not_entails : ¬ Entails {deDicto} deRe := fun H ↦ by
  have h := staticInterp_logicallyPossible
  obtain ⟨u, hu⟩ := exists_unicorn_of_deRe h _ _ <| H staticInterp h ()
    (fun _ hφ g ↦ by rw [Set.mem_singleton_iff.1 hφ]; exact (deDicto_without_unicorns g).1)
    fun _ _ ↦ 0
  exact (deDicto_without_unicorns fun _ _ ↦ 0).2 u hu

end johnSeeksAUnicorn

/-! ### The temperature puzzle -/

/-- *the temperature is ninety* is analysed as `F₄(the temperature, F₅(be, ninety))`. -/
def theTemperatureIsNinety : Analysis .t := f4 (the (basic temperature)) (f5 be (name ninety))

/-- *the temperature rises* is analysed as `F₄(the temperature, rise)`. -/
def theTemperatureRises : Analysis .t := f4 (the (basic temperature)) (basic rise)

/-- *ninety rises* is analysed as `F₄(ninety, rise)`. -/
def ninetyRises : Analysis .t := f4 (name ninety) (basic rise)

section Symbolizations

variable (M : Interp E W) (g : Assignment (W → E)) (i : W)

theorem theTemperatureIsNinety_iff :
    theTemperatureIsNinety.realize M g i ↔
      GQ.the (M.const temperature i) fun y ↦ y i = M.name ninety i :=
  Iff.rfl

theorem theTemperatureRises_iff :
    theTemperatureRises.realize M g i ↔ GQ.the (M.const temperature i) (M.const rise i) :=
  Iff.rfl

theorem ninetyRises_iff : ninetyRises.realize M g i ↔ M.const rise i (M.name ninety) :=
  Iff.rfl

theorem a_price_rises_iff :
    (f4 (a (basic price)) (basic rise)).realize M g i ↔
      GQ.some (M.const price i) (M.const rise i) :=
  Iff.rfl

end Symbolizations

/-- `temperatureConcept` is a temperature of `90` at the first moment and `95` at the second. -/
def temperatureConcept : Fin 2 → ℕ := ![90, 95]

/-- `temperatureInterp` interprets the fragment over numbers and two moments. *price* and
*temperature* hold of the one concept `temperatureConcept`, a concept *rises* at a moment if its
value is larger at a later one, and nothing else holds of anything. -/
def temperatureInterp : Interp ℕ (Fin 2) where
  name
    | .ninety => fun _ ↦ 90
    | _ => fun _ ↦ 0
  const
    | .man | .woman | .unicorn => rigidCN fun _ _ ↦ False
    | .price | .temperature => fun _ x ↦ x = temperatureConcept
    | .walk => extIV fun _ _ ↦ False
    | .rise => fun i x ↦ ∃ j, i < j ∧ x i < x j
    | .love | .find | .seek => extTV fun _ _ _ ↦ False

theorem temperatureInterp_logicallyPossible : temperatureInterp.LogicallyPossible where
  name_rigid
    | .ninety | .john | .mary | .bill => isRigid_const _
  noun_rigid
    | .man, _, _, _, _, h | .woman, _, _, _, _, h | .unicorn, _, _, _, _, h => h.1
  iv_ext
    | .walk, _ => ⟨fun _ _ ↦ False, rfl⟩
  tv_ext
    | .love, _ | .find, _ => ⟨fun _ _ _ ↦ False, rfl⟩
  seek_ext Q := ⟨fun i _ ↦ Q i fun _ _ ↦ False, rfl⟩

/-- Partee's argument is invalid, since at the first moment of `temperatureInterp` *the
temperature is ninety* and *the temperature rises* are true and *ninety rises* is false. -/
theorem not_entails_ninetyRises :
    ¬ Entails {theTemperatureIsNinety, theTemperatureRises} ninetyRises := fun H ↦ by
  obtain ⟨_, _, hlt⟩ := H temperatureInterp temperatureInterp_logicallyPossible 0 (by
    rintro φ (hφ | hφ) g <;> rw [hφ]
    · exact ⟨_, fun _ ↦ Iff.rfl, rfl⟩
    · exact ⟨_, fun _ ↦ Iff.rfl, 1, by decide, by decide⟩) fun _ _ ↦ 0
  exact lt_irrefl _ hlt

/-- *a price rises* is true at the first moment of `temperatureInterp` while its
individual-variable symbolization `∨u[price'*(u) ∧ rise'*(u)]` is false, so unlike *a man walks*
it needs individual-concept variables. -/
theorem a_price_rises_needs_concepts (g : Assignment (Fin 2 → ℕ)) :
    (f4 (a (basic price)) (basic rise)).realize temperatureInterp g 0 ∧
      ¬ GQ.some (starIV (temperatureInterp.const price 0))
        (starIV (temperatureInterp.const rise 0)) :=
  ⟨⟨_, rfl, 1, by decide, by decide⟩, fun ⟨_, _, _, _, hlt⟩ ↦ lt_irrefl _ hlt⟩

end Montague1973
