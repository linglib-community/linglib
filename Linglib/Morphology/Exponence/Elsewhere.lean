module

public import Linglib.Morphology.Exponence.Basic
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Data.Set.Finite.Basic

/-!
# The Elsewhere Condition

An Elsewhere winner of a rule set at a context is a rule that applies there and is minimal, among
the rules that apply, in specificity. Specificity is read through a key into an ordered type, as
closeness is for a probe: Kiparsky's specificity is the key `applySet`, a rule being more specific
when it applies in fewer contexts, and other theories choose other keys. This file defines Elsewhere
winners and the prediction relation they induce.

## Main definitions

* `RuleSet.IsElsewhereWinner`: an applicable rule of a rule set at a context that no applicable
  rule is more specific than.
* `RuleSet.Coherent`: rules equally specific carry the same exponent.
* `RuleSet.Realizes`: some Elsewhere winner carries the given exponent.
* `RuleSet.Antihomophonous`: distinct rules carry distinct exponents.

## Main results

* `RuleSet.Realizes.eq`: where the Elsewhere winners form a chain, Pāṇinian Determinism, a
  coherent rule set makes a unique prediction.
* `RuleSet.Realizes.of_realizes`: no ABA pattern across nested contexts.

## References

* [kiparsky-1973]
* [bobaljik-2012]
-/

@[expose] public section

namespace Morphology.Exponence.RuleSet

variable {Ctx E : Type*} {R : Type*} [Rule R Ctx E] {κ : Type*} [Preorder κ] {key : R → κ}
variable {v : RuleSet R} {c : Ctx} {r s : R} {φ : E}

/-! ### Elsewhere winners -/

theorem _root_.MinimalFor.antisymmRel {ι α : Type*} [Preorder α] {P : ι → Prop} {f : ι → α}
    {i j : ι} (hi : MinimalFor P f i) (hj : MinimalFor P f j) (h : f j ≤ f i ∨ f i ≤ f j) :
    AntisymmRel (· ≤ ·) (f i) (f j) :=
  h.elim (fun h ↦ ⟨hi.le_of_le hj.1 h, h⟩) (fun h ↦ ⟨h, hj.le_of_le hi.1 h⟩)

/-- An applicable rule of `v` at `c` that no applicable rule is more specific than, specificity
read through `key`. -/
abbrev IsElsewhereWinner (v : RuleSet R) (key : R → κ) (c : Ctx) (r : R) : Prop :=
  MinimalFor (fun s ↦ s ∈ v ∧ Applies s c) key r

/-- A rule set is coherent if rules equally specific carry the same exponent. -/
def Coherent (v : RuleSet R) (key : R → κ) : Prop :=
  ∀ r ∈ v, ∀ s ∈ v, AntisymmRel (· ≤ ·) (key r) (key s) → exponent r = exponent s

theorem IsElsewhereWinner.exponent_eq (hv : v.Coherent key) (hr : v.IsElsewhereWinner key c r)
    (hs : v.IsElsewhereWinner key c s) (h : key s ≤ key r ∨ key r ≤ key s) :
    exponent r = exponent s :=
  hv r hr.1.1 s hs.1.1 (hr.antisymmRel hs h)

theorem exists_isElsewhereWinner (h : ∃ r ∈ v, Applies r c) :
    ∃ r, v.IsElsewhereWinner key c r :=
  (v.finite_toSet.subset fun _ hr ↦ hr.1).exists_minimalFor key _ h

/-! ### The prediction relation -/

/-- `φ` is realized at `c` when some Elsewhere winner carries it. -/
def Realizes (v : RuleSet R) (key : R → κ) (c : Ctx) (φ : E) : Prop :=
  ∃ r, v.IsElsewhereWinner key c r ∧ exponent r = φ

/-- Over a coherent rule set whose Elsewhere winners form a chain, Stump's Pāṇinian
Determinism, the prediction is unique. -/
theorem Realizes.eq {ψ : E} (hv : v.Coherent key)
    (hc : IsChain (fun r s ↦ key r ≤ key s) {s | v.IsElsewhereWinner key c s})
    (hφ : v.Realizes key c φ) (hψ : v.Realizes key c ψ) : φ = ψ := by
  obtain ⟨r, hr, rfl⟩ := hφ
  obtain ⟨s, hs, rfl⟩ := hψ
  exact hr.exponent_eq hv hs (hc.total hs hr)

/-! ### Containment -/

/-- A rule set is **antihomophonous** when distinct rules carry distinct exponents, the
Antihomophony assumption of [bobaljik-2012] that sets accidental homophony aside. -/
def Antihomophonous (v : RuleSet R) : Prop :=
  Set.InjOn exponent {r | r ∈ v}

instance [DecidableEq R] [DecidableEq E] (v : RuleSet R) : Decidable v.Antihomophonous :=
  inferInstanceAs (Decidable (∀ r ∈ v, ∀ s ∈ v, exponent r = exponent s → r = s))

theorem IsElsewhereWinner.of_applies {c' : Ctx} (h : ∀ s ∈ v, Applies s c' → Applies s c)
    (hr : v.IsElsewhereWinner key c r) (hc' : Applies r c') : v.IsElsewhereWinner key c' r :=
  hr.anti (fun s hs ↦ ⟨hs.1, h s hs.1 hs.2⟩) ⟨hr.1.1, hc'⟩

/-- There is no ABA across nested contexts. Over an antihomophonous rule set, an exponent
realized at the smallest and the largest of three nested contexts is realized at the middle
one. -/
theorem Realizes.of_realizes {c₁ c₂ : Ctx} (hv : v.Antihomophonous)
    (h₁ : ∀ s ∈ v, Applies s c₁ → Applies s c₂) (h₂ : ∀ s ∈ v, Applies s c₂ → Applies s c)
    (hr₁ : v.Realizes key c₁ φ) (hr : v.Realizes key c φ) : v.Realizes key c₂ φ := by
  obtain ⟨t, ht, rfl⟩ := hr
  obtain ⟨u, hu, hut⟩ := hr₁
  obtain rfl := hv hu.1.1 ht.1.1 hut
  exact ⟨_, ht.of_applies h₂ (h₁ _ hu.1.1 hu.1.2), rfl⟩

end Morphology.Exponence.RuleSet
