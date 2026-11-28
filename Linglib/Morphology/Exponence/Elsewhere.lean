module

public import Linglib.Morphology.Exponence.Basic
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Data.Set.Finite.Basic

/-!
# The Elsewhere Condition

An Elsewhere winner of a rule set at a context is a rule that applies there and is minimal, among
the rules that apply, in specificity. Specificity is read through a key into a preordered type:
Kiparsky's specificity is the key `applySet`, a rule being more specific when it applies in fewer
contexts, and other theories choose other keys. This file defines Elsewhere winners and the
prediction relation they induce.

## Main definitions

* `RuleSet.IsElsewhereWinner`: an applicable rule of a rule set at a context that no applicable
  rule is more specific than.
* `RuleSet.Coherent`: rules equally specific carry the same exponent.
* `RuleSet.Realizes`: some Elsewhere winner carries the given exponent.
* `RuleSet.Antihomophonous`: distinct rules carry distinct exponents.

## Main results

* `RuleSet.Realizes.eq`: where the Elsewhere winners are pairwise comparable, a coherent rule set
  makes a unique prediction.
* `RuleSet.Realizes.of_applies`: no ABA pattern across a context that takes in the rules the outer
  two share and whose rules all reach one of them.

## Implementation notes

Kiparsky's condition orders two rules disjunctively when the contexts of one are among those of the
other and their structural changes are identical or incompatible. Two exponents competing for one
position are always one or the other, so only the inclusion of contexts is formalized.

Stump's Pāṇinian Determinism Hypothesis requires that among the rules of a block applicable at a
cell one be narrower than all the others. The hypothesis used here is that the Elsewhere winners at
a context are pairwise comparable, which that rule ensures and which also holds where no rule
applies.

## References

* [kiparsky-1973]
* [stump-2001]
* [bobaljik-2012]
-/

@[expose] public section

namespace Morphology.RuleSet

variable {Ctx E : Type*} {R : Type*} [ExponenceRule R Ctx E] {κ : Type*} [Preorder κ] {key : R → κ}
variable {v : RuleSet R} {c : Ctx} {r s : R} {φ : E}

/-! ### Elsewhere winners -/

/-- An applicable rule of `v` at `c` that no applicable rule is more specific than, specificity
read through `key`. -/
abbrev IsElsewhereWinner (v : RuleSet R) (key : R → κ) (c : Ctx) (r : R) : Prop :=
  MinimalFor (fun s ↦ s ∈ v ∧ Applies s c) key r

/-- A rule set is coherent if rules equally specific carry the same exponent. -/
def Coherent (v : RuleSet R) (key : R → κ) : Prop :=
  ∀ r ∈ v, ∀ s ∈ v, AntisymmRel (· ≤ ·) (key r) (key s) → exponent r = exponent s

/-- Comparable Elsewhere winners are equally specific. -/
theorem IsElsewhereWinner.antisymmRel (hr : v.IsElsewhereWinner key c r)
    (hs : v.IsElsewhereWinner key c s) (h : key s ≤ key r ∨ key r ≤ key s) :
    AntisymmRel (· ≤ ·) (key r) (key s) :=
  h.elim (fun h ↦ ⟨hr.le_of_le hs.1 h, h⟩) fun h ↦ ⟨h, hs.le_of_le hr.1 h⟩

theorem exists_isElsewhereWinner (h : ∃ r ∈ v, Applies r c) :
    ∃ r, v.IsElsewhereWinner key c r :=
  (v.finite_toSet.sep _).exists_minimalFor key _ h

/-! ### The prediction relation -/

/-- `φ` is realized at `c` when some Elsewhere winner carries it. -/
def Realizes (v : RuleSet R) (key : R → κ) (c : Ctx) (φ : E) : Prop :=
  ∃ r, v.IsElsewhereWinner key c r ∧ exponent r = φ

/-- Over a coherent rule set whose Elsewhere winners are pairwise comparable, the prediction is
unique. -/
theorem Realizes.eq {ψ : E} (hv : v.Coherent key)
    (hc : IsChain (fun r s ↦ key r ≤ key s) {s | v.IsElsewhereWinner key c s})
    (hφ : v.Realizes key c φ) (hψ : v.Realizes key c ψ) : φ = ψ := by
  obtain ⟨r, hr, rfl⟩ := hφ
  obtain ⟨s, hs, rfl⟩ := hψ
  exact hv r hr.1.1 s hs.1.1 (hr.antisymmRel hs (hc.total hs hr))

/-! ### Containment -/

/-- A rule set is **antihomophonous** when distinct rules carry distinct exponents, setting
accidental homophony aside. This generalizes [bobaljik-2012]'s Antihomophony, which bars only a
contextual allomorph homophonous with the default; homophonous contextual allomorphs break
contiguity from four nested contexts on. -/
def Antihomophonous (v : RuleSet R) : Prop :=
  Set.InjOn exponent {r | r ∈ v}

instance [DecidableEq R] [DecidableEq E] (v : RuleSet R) : Decidable v.Antihomophonous :=
  inferInstanceAs (Decidable (∀ r ∈ v, ∀ s ∈ v, exponent r = exponent s → r = s))

/-- A map of rules that keeps exponents keeps antihomophony. -/
theorem Antihomophonous.map {R' Ctx' : Type*} [ExponenceRule R' Ctx' E] {f : R → R'}
    (hv : v.Antihomophonous) (hf : ∀ r, exponent (f r) = exponent r) :
    Antihomophonous (v.map f) := by
  rintro _ hfr _ hfs h
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hfr
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hfs
  exact congrArg f (hv hr hs (by rwa [hf, hf] at h))

theorem IsElsewhereWinner.of_applies {c' : Ctx} (h : ∀ s ∈ v, Applies s c' → Applies s c)
    (hr : v.IsElsewhereWinner key c r) (hc' : Applies r c') : v.IsElsewhereWinner key c' r :=
  hr.anti (fun s hs ↦ ⟨hs.1, h s hs.1 hs.2⟩) ⟨hr.1.1, hc'⟩

/-- There is no ABA across a middle context `c₂` that takes in the rules `c₁` and `c₃` share and
whose rules all reach `c₃`. Over an antihomophonous rule set, an exponent realized at `c₁` and `c₃`
is then realized at `c₂`. Nested contexts are the case where every rule of `c₁` reaches `c₂`; the
rules of `c₁` need not all do so. -/
theorem Realizes.of_applies {c₁ c₂ c₃ : Ctx} (hv : v.Antihomophonous)
    (h₁ : ∀ s ∈ v, Applies s c₁ → Applies s c₃ → Applies s c₂)
    (h₂ : ∀ s ∈ v, Applies s c₂ → Applies s c₃)
    (hr₁ : v.Realizes key c₁ φ) (hr₃ : v.Realizes key c₃ φ) : v.Realizes key c₂ φ := by
  obtain ⟨t, ht, rfl⟩ := hr₃
  obtain ⟨u, hu, hut⟩ := hr₁
  obtain rfl := hv hu.1.1 ht.1.1 hut
  exact ⟨_, ht.of_applies h₂ (h₁ _ hu.1.1 hu.1.2 ht.1.2), rfl⟩

end Morphology.RuleSet
