module

public import Linglib.Core.Data.List.Find
public import Linglib.Core.Data.List.MinMax
public import Linglib.Morphology.Exponence.Elsewhere
public import Linglib.Morphology.Paradigm.Contiguity

/-!
# Elsewhere selection

This file defines selection by a specificity score (`selectBy`) and over the
specificity preorder (`selectMinimal`), and proves that both produce Elsewhere
winners. Selection by a score keeps its choice when the competition shrinks around the winner,
so rules applicable on upper sets of ordered contexts realize contiguous patterns. Minimal
selection does the same, and agrees with selection by a score, where Stump's Pāṇinian
Determinism holds, the Elsewhere winners forming a chain. The exponent of the minimal selection,
falling back on a default where no rule applies, is the shape shared by Stump's rules of
paradigm linkage over a root and by Bonami and Stump's rules of basic stem choice.

## Main definitions

* `RuleSet.selectBy`, `RuleSet.realize`: the applicable rule of greatest score, and its
  exponent.
* `RuleSet.selectMinimal`, `RuleSet.realizeMinimal`: the first applicable rule that no
  applicable rule strictly undercuts, and its exponent.
* `RuleSet.realizeMinimalD`: the exponent of the minimal selection, or a fallback where
  no rule applies.

## Main results

* `RuleSet.selectBy_eq_some_of_applies`: selection by a score is consistent under
  contraction, so the rule selected in a context stays selected in any context with fewer
  applicable rules where it still applies.
* `RuleSet.selectBy_eq_head?_applicable`: on a rule set listed by non-increasing score,
  selection takes the first applicable rule.
* `RuleSet.selectBy_map`: selection commutes with a map of rules preserving applicability
  and the comparison of scores.
* `RuleSet.isContiguous_realize_of_monotone`, `RuleSet.isContiguous_realize_of_antitone`:
  rules applicable on upper sets, or on lower sets, of ordered contexts realize contiguous
  patterns when distinct rules carry distinct exponents.
* `RuleSet.selectBy_isElsewhereWinner`, `RuleSet.selectMinimal_isElsewhereWinner`: both
  selections produce Elsewhere winners.
* `RuleSet.selectMinimal_eq_some_of_applies`,
  `RuleSet.isContiguous_realizeMinimal_of_monotone`: under Pāṇinian Determinism minimal
  selection is consistent under contraction and realizes contiguous patterns.
* `RuleSet.realizeMinimal_eq_realize`: under Pāṇinian Determinism minimal selection realizes
  what selection on any score strictly reversing specificity realizes.
* `RuleSet.selectMinimal_factorsThrough`, `RuleSet.realizeMinimal_factorsThrough`,
  `RuleSet.realizeMinimalD_factorsThrough`: selection, realization, and realization with a
  fallback, factor through any map on contexts that every rule's applicability (and the
  fallback) factors through.
* `RuleSet.realizeMinimalD_eq_of_isElsewhereWinner`: over a coherent rule set under
  Pāṇinian Determinism, realization with a fallback is the exponent of any
  Elsewhere winner, whatever the order of the rule set.

## References

* [bonami-stump-2016]
* [stump-2006]
-/

@[expose] public section

namespace Morphology.Exponence.RuleSet

variable {Ctx E : Type*} {R : Type*} [Rule R Ctx E]
variable [DecidableRel (Applies : R → Ctx → Prop)]
variable {v : RuleSet R} {c c' : Ctx} {r s : R} {φ : E}

/-! ### Score selection -/

/-- The rules of `v` applicable at `c`, in the order of `v`. -/
def applicable (v : RuleSet R) (c : Ctx) : List R :=
  v.filter (fun r ↦ Applies r c)

@[simp] theorem mem_applicable :
    r ∈ v.applicable c ↔ r ∈ v ∧ Applies r c := by
  simp only [applicable, List.mem_filter, decide_eq_true_eq]

variable {α : Type*} [LinearOrder α] {f : R → α}

/-- The applicable rule of greatest score `f`, ties broken by the order of
the rule set; scores to be minimized pass through `OrderDual`. -/
def selectBy (v : RuleSet R) (f : R → α) (c : Ctx) : Option R :=
  (v.applicable c).argmax f

theorem selectBy_mem (h : v.selectBy f c = some r) : r ∈ v :=
  (mem_applicable.mp (List.argmax_mem h)).1

theorem selectBy_applies (h : v.selectBy f c = some r) : Applies r c :=
  (mem_applicable.mp (List.argmax_mem h)).2

theorem selectBy_eq_none_iff : v.selectBy f c = none ↔ v.applicable c = [] :=
  List.argmax_eq_none

/-- On a rule set listed by non-increasing score, selection takes the first applicable rule. -/
theorem selectBy_eq_head?_applicable (h : v.Pairwise fun r s ↦ f s ≤ f r) :
    v.selectBy f c = (v.applicable c).head? :=
  List.argmax_eq_head? (h.filter _)

theorem selectBy_isSome_iff : (v.selectBy f c).isSome ↔ ∃ r ∈ v, Applies r c := by
  simp [← Option.ne_none_iff_isSome, selectBy_eq_none_iff, applicable, List.filter_eq_nil_iff]

/-- Contexts with the same applicable rules select the same rule. -/
theorem selectBy_congr (h : v.applicable c = v.applicable c') :
    v.selectBy f c = v.selectBy f c' := by
  rw [selectBy, selectBy, h]

/-- The exponent of the rule selected by `selectBy`. -/
def realize (v : RuleSet R) (f : R → α) (c : Ctx) : Option E :=
  (v.selectBy f c).map exponent

theorem realize_eq_none_iff : v.realize f c = none ↔ v.applicable c = [] :=
  Option.map_eq_none_iff.trans selectBy_eq_none_iff

theorem realize_congr (h : v.applicable c = v.applicable c') :
    v.realize f c = v.realize f c' :=
  congrArg (Option.map exponent) (selectBy_congr h)

/-- The selected rule scores at least as high as every applicable rule. -/
theorem le_of_selectBy_eq_some (h : v.selectBy f c = some r) (hs : s ∈ v) (hsc : Applies s c) :
    f s ≤ f r :=
  List.le_of_mem_argmax (mem_applicable.mpr ⟨hs, hsc⟩) h

/-- On a rule set sorted by decreasing score, the selected rule is the first applicable one. -/
theorem selectBy_eq_head? (h : v.Pairwise fun r s ↦ f s ≤ f r) :
    v.selectBy f c = (v.applicable c).head? :=
  List.argmax_eq_head? (h.filter _)

/-- An applicable rule scoring at least as high as every applicable rule is realized, provided
the applicable rules with its score share its exponent. -/
theorem realize_eq_of_forall_le (hr : r ∈ v) (hrc : Applies r c)
    (hle : ∀ s ∈ v, Applies s c → f s ≤ f r)
    (heq : ∀ s ∈ v, Applies s c → f s = f r → exponent s = exponent r) :
    v.realize f c = some (exponent r) := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (selectBy_isSome_iff (f := f).mpr ⟨r, hr, hrc⟩)
  have hw' := selectBy_mem hw
  have hwc := selectBy_applies hw
  rw [realize, hw, Option.map_some,
    heq w hw' hwc ((hle w hw' hwc).antisymm (le_of_selectBy_eq_some hw hr hrc))]

/-! ### Contraction -/

theorem applicable_eq_filter (h : ∀ s ∈ v, Applies s c → Applies s c') :
    v.applicable c = (v.applicable c').filter (fun s ↦ Applies s c) := by
  rw [applicable, applicable, List.filter_filter]
  exact List.filter_congr fun s hs ↦ by by_cases hc : Applies s c <;> simp [hc, h s hs]

/-- Selection by a score is consistent under contraction. The rule selected at `c'` is selected
at any context whose applicable rules are among those at `c'`, as long as it applies there. -/
theorem selectBy_eq_some_of_applies (h : ∀ s ∈ v, Applies s c → Applies s c')
    (hr : v.selectBy f c' = some r) (hrc : Applies r c) : v.selectBy f c = some r := by
  rw [selectBy, applicable_eq_filter h]
  exact List.argmax_filter_of_mem hr (by simpa using hrc)

theorem selectBy_eq_none_of_applies (h : ∀ s ∈ v, Applies s c → Applies s c')
    (hr : v.selectBy f c' = none) : v.selectBy f c = none := by
  rw [selectBy_eq_none_iff, applicable_eq_filter h, selectBy_eq_none_iff.mp hr, List.filter_nil]

/-- Selection admits no ABA. Across three contexts whose applicable rules are nested, an
antihomophonous rule set that realizes one exponent at both outer contexts realizes it at the
middle one. -/
theorem realize_eq_of_applies {c₁ c₂ c₃ : Ctx} (hv : v.Antihomophonous)
    (h₁ : ∀ s ∈ v, Applies s c₁ → Applies s c₂) (h₂ : ∀ s ∈ v, Applies s c₂ → Applies s c₃)
    (h : v.realize f c₁ = v.realize f c₃) : v.realize f c₂ = v.realize f c₁ := by
  rcases h₃ : v.selectBy f c₃ with - | r
  · rw [realize, realize, selectBy_eq_none_of_applies h₂ h₃,
      selectBy_eq_none_of_applies h₁ (selectBy_eq_none_of_applies h₂ h₃)]
  · obtain ⟨r₁, hr₁, he⟩ : ∃ r₁, v.selectBy f c₁ = some r₁ ∧ exponent r₁ = exponent r := by
      simpa [realize, h₃] using h
    obtain rfl := hv (selectBy_mem hr₁) (selectBy_mem h₃) he
    rw [realize, realize, hr₁,
      selectBy_eq_some_of_applies h₂ h₃ (h₁ _ (selectBy_mem hr₁) (selectBy_applies hr₁))]

section Contiguity

variable [Preorder Ctx]

/-- Rules applicable on upper sets of contexts realize contiguous patterns. -/
theorem isContiguous_realize_of_monotone (hv : v.Antihomophonous)
    (h : ∀ r ∈ v, Monotone (Applies r)) : IsContiguous (v.realize f) :=
  fun _ _ _ hij hjk he ↦
    (realize_eq_of_applies hv (fun s hs ↦ h s hs hij) (fun s hs ↦ h s hs hjk) he).symm

/-- Rules applicable on lower sets of contexts realize contiguous patterns. -/
theorem isContiguous_realize_of_antitone (hv : v.Antihomophonous)
    (h : ∀ r ∈ v, Antitone (Applies r)) : IsContiguous (v.realize f) :=
  fun _ _ _ hij hjk he ↦ he.trans
    (realize_eq_of_applies hv (fun s hs ↦ h s hs hjk) (fun s hs ↦ h s hs hij) he.symm).symm

end Contiguity

/-! ### Loss of rules -/

theorem applicable_filter (p : R → Bool) :
    applicable (v.filter p) c = (v.applicable c).filter p := by
  simp only [applicable, List.filter_filter, Bool.and_comm]

/-- The selected rule is selected from any filtering of the rule set that keeps it. -/
theorem selectBy_filter_of_mem {p : R → Bool} (h : v.selectBy f c = some r) (hp : p r) :
    selectBy (v.filter p) f c = some r := by
  rw [selectBy, applicable_filter]
  exact List.argmax_filter_of_mem h hp

/-- An antihomophonous rule set that loses rules keeps realizing an exponent wherever it did, as
long as it still realizes the exponent somewhere. -/
theorem realize_filter_eq_some (hv : v.Antihomophonous) {p : R → Bool}
    (h : v.realize f c = some φ) (h' : realize (v.filter p) f c' = some φ) :
    realize (v.filter p) f c = some φ := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨r', hr', he⟩ := Option.map_eq_some_iff.mp h'
  have hm := List.mem_filter.mp (selectBy_mem hr')
  obtain rfl := hv hm.1 (selectBy_mem hr) he
  rw [realize, selectBy_filter_of_mem hr hm.2, Option.map_some]

/-! ### Transport -/

section Map

variable {R' Ctx' E' : Type*} [Rule R' Ctx' E'] [DecidableRel (Applies : R' → Ctx' → Prop)]
  {β : Type*} [LinearOrder β] {f' : R' → β} {g : R → R'} {c' : Ctx'}

/-- Selection commutes with a map of rules that preserves applicability and the comparison of
scores. -/
theorem selectBy_map (happ : ∀ r ∈ v, Applies (g r) c' ↔ Applies r c)
    (hf : ∀ r ∈ v, ∀ s ∈ v, f' (g r) ≤ f' (g s) ↔ f r ≤ f s) :
    selectBy (v.map g) f' c' = (v.selectBy f c).map g := by
  have happ' : applicable (v.map g) c' = (v.applicable c).map g := by
    rw [applicable, applicable, List.filter_map]
    exact congrArg _ (List.filter_congr fun r hr ↦ by simp [happ r hr])
  rw [selectBy, happ', List.argmax_map, selectBy]
  exact congrArg _ (List.argmax_congr fun r hr s hs ↦
    hf r (mem_applicable.mp hr).1 s (mem_applicable.mp hs).1)

end Map

/-! ### Soundness -/

variable [Preorder R]

/-- A score strictly antitone on the applicable rules selects an
Elsewhere winner. -/
theorem selectBy_isElsewhereWinner
    (hf : StrictAntiOn f {r | r ∈ v.applicable c})
    (h : v.selectBy f c = some r) : v.IsElsewhereWinner c r := by
  refine ⟨mem_applicable.mp (List.argmax_mem h), fun s hs hsr ↦ ?_⟩
  by_contra hrs
  exact absurd (List.le_of_mem_argmax (mem_applicable.mpr hs) h)
    (not_le_of_gt (hf (mem_applicable.mpr hs) (List.argmax_mem h)
      (lt_of_le_not_ge hsr hrs)))

/-- Realized exponents satisfy `Realizes`. -/
theorem realize_realizes (hf : StrictAntiOn f {r | r ∈ v.applicable c})
    (h : v.realize f c = some φ) : v.Realizes c φ := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨r, selectBy_isElsewhereWinner hf hr, rfl⟩

/-! ### Order selection -/

variable [DecidableRel (· < · : R → R → Prop)]

/-- The first applicable rule that no applicable rule strictly undercuts. -/
def selectMinimal (v : RuleSet R) (c : Ctx) : Option R :=
  (v.applicable c).find? (fun r ↦ (v.applicable c).all (fun s ↦ decide (¬ s < r)))

/-- Minimal selection picks the first rule of the rule set that applies and that no applicable
rule strictly undercuts. -/
theorem selectMinimal_eq_find? : v.selectMinimal c =
    v.find? (fun r ↦ decide (Applies r c ∧ ∀ s ∈ v.applicable c, ¬ s < r)) := by
  unfold selectMinimal
  nth_rewrite 2 [applicable]
  rw [List.find?_filter]
  exact List.find?_congr fun r _ ↦ by simp only [decide_eq_true_eq, List.all_eq_true]

/-- `selectMinimal` returns an Elsewhere winner. -/
theorem selectMinimal_isElsewhereWinner
    (h : v.selectMinimal c = some r) : v.IsElsewhereWinner c r := by
  have hall := List.find?_some h
  simp only [List.all_eq_true, decide_eq_true_eq, mem_applicable] at hall
  exact minimal_iff_forall_lt.mpr
    ⟨mem_applicable.mp (List.mem_of_find?_eq_some h), fun s hlt hs ↦ hall s hs hlt⟩

theorem selectMinimal_mem (h : v.selectMinimal c = some r) : r ∈ v :=
  (selectMinimal_isElsewhereWinner h).prop.1

theorem selectMinimal_applies (h : v.selectMinimal c = some r) : Applies r c :=
  (selectMinimal_isElsewhereWinner h).prop.2

/-- `selectMinimal` succeeds iff some rule applies. -/
theorem selectMinimal_isSome_iff :
    (v.selectMinimal c).isSome ↔ ∃ r ∈ v, Applies r c := by
  rw [selectMinimal, List.find?_isSome]
  simp only [List.all_eq_true, decide_eq_true_eq, mem_applicable]
  exact ⟨fun ⟨r, hr, _⟩ ↦ ⟨r, hr⟩, fun h ↦ (exists_isElsewhereWinner h).imp
    fun w hw ↦ ⟨hw.1, fun s hs ↦ hw.not_lt hs⟩⟩

theorem selectMinimal_eq_none_iff :
    v.selectMinimal c = none ↔ v.applicable c = [] := by
  rw [← Option.not_isSome_iff_eq_none, selectMinimal_isSome_iff]
  simp [applicable, List.filter_eq_nil_iff]

/-- Contexts with the same applicable rules select the same rule. -/
theorem selectMinimal_congr (h : v.applicable c = v.applicable c') :
    v.selectMinimal c = v.selectMinimal c' := by
  rw [selectMinimal, selectMinimal, h]

/-- A rule system sensitive only to what `A` sees selects the same rule in
contexts that `A` identifies. -/
theorem selectMinimal_factorsThrough {V : Type*} {A : Ctx → V}
    (h : ∀ r ∈ v, ∀ ⦃c c'⦄, A c = A c' → (Applies r c ↔ Applies r c')) :
    v.selectMinimal.FactorsThrough A :=
  fun _ _ hA ↦ selectMinimal_congr <| List.filter_congr fun r hr ↦ by simp [h r hr hA]

/-- The exponent of the rule selected by `selectMinimal`, the order-based counterpart of
`realize`. -/
def realizeMinimal (v : RuleSet R) (c : Ctx) : Option E :=
  (v.selectMinimal c).map exponent

/-- A rule system sensitive only to what `A` sees realizes the same exponent in contexts that `A`
identifies. -/
theorem realizeMinimal_factorsThrough {V : Type*} {A : Ctx → V}
    (h : ∀ r ∈ v, ∀ ⦃c c'⦄, A c = A c' → (Applies r c ↔ Applies r c')) :
    v.realizeMinimal.FactorsThrough A :=
  fun _ _ hA ↦ congrArg (Option.map exponent) (selectMinimal_factorsThrough h hA)

theorem realizeMinimal_eq_none_iff : v.realizeMinimal c = none ↔ v.applicable c = [] :=
  Option.map_eq_none_iff.trans selectMinimal_eq_none_iff

theorem realizeMinimal_isSome_iff : (v.realizeMinimal c).isSome ↔ ∃ r ∈ v, Applies r c := by
  rw [realizeMinimal, Option.isSome_map]
  exact selectMinimal_isSome_iff

/-- Contexts with the same applicable rules realize the same exponent. -/
theorem realizeMinimal_congr (h : v.applicable c = v.applicable c') :
    v.realizeMinimal c = v.realizeMinimal c' :=
  congrArg (Option.map exponent) (selectMinimal_congr h)

/-- Minimally realized exponents satisfy `Realizes`. -/
theorem realizeMinimal_realizes (h : v.realizeMinimal c = some φ) : v.Realizes c φ := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨r, selectMinimal_isElsewhereWinner hr, rfl⟩

/-- Over a coherent rule set whose Elsewhere winners form a chain, the minimally realized
exponent is that of any Elsewhere winner, so it does not depend on the order of the
rule set. -/
theorem realizeMinimal_eq_of_isElsewhereWinner (hv : v.Coherent)
    (hc : IsChain (· ≤ ·) {s | v.IsElsewhereWinner c s}) (hr : v.IsElsewhereWinner c r) :
    v.realizeMinimal c = some (exponent r) := by
  obtain ⟨φ, hφ⟩ := Option.isSome_iff_exists.mp
    (realizeMinimal_isSome_iff.mpr ⟨r, hr.prop.1, hr.prop.2⟩)
  rw [hφ, (realizeMinimal_realizes hφ).eq hv hc ⟨r, hr, rfl⟩]

/-- Under Pāṇinian Determinism a coherent rule set realizes by minimal selection what it
realizes by selection on any score strictly reversing specificity. -/
theorem realizeMinimal_eq_realize (hv : v.Coherent)
    (hc : IsChain (· ≤ ·) {s | v.IsElsewhereWinner c s})
    (hf : StrictAntiOn f {r | r ∈ v.applicable c}) : v.realizeMinimal c = v.realize f c := by
  rcases hs : v.selectBy f c with - | r
  · rw [realize, hs, Option.map_none, realizeMinimal_eq_none_iff,
      ← selectBy_eq_none_iff (f := f), hs]
  · rw [realize, hs, Option.map_some,
      realizeMinimal_eq_of_isElsewhereWinner hv hc (selectBy_isElsewhereWinner hf hs)]

/-! ### Contraction under Pāṇinian Determinism -/

/-- Minimal selection is consistent under contraction where the Elsewhere winners of the smaller
context form a chain, Stump's Pāṇinian Determinism. The rule selected at `c'` is then selected
at any context whose applicable rules are among those at `c'`, as long as it applies there. -/
theorem selectMinimal_eq_some_of_applies (h : ∀ s ∈ v, Applies s c → Applies s c')
    (hc : IsChain (· ≤ ·) {s | v.IsElsewhereWinner c s}) (hr : v.selectMinimal c' = some r)
    (hrc : Applies r c) : v.selectMinimal c = some r := by
  have hwr' := selectMinimal_isElsewhereWinner hr
  have hwr : v.IsElsewhereWinner c r := hwr'.of_applies h hrc
  rw [selectMinimal_eq_find?] at hr ⊢
  refine List.find?_eq_some_of_imp hr ?_ fun x hx hpx ↦ ?_
  · exact decide_eq_true ⟨hrc, fun s hs hlt ↦ hwr.not_lt (mem_applicable.mp hs) hlt⟩
  obtain ⟨hxc, hxmin⟩ := of_decide_eq_true hpx
  have hwx : v.IsElsewhereWinner c x := minimal_iff_forall_lt.mpr
    ⟨⟨hx, hxc⟩, fun s hlt hs ↦ hxmin s (mem_applicable.mpr hs) hlt⟩
  have hxr : x ≤ r := by
    by_contra hxr
    exact hxmin r (mem_applicable.mpr hwr.prop)
      (lt_of_le_not_ge ((hc.total hwx hwr).resolve_left hxr) hxr)
  exact decide_eq_true ⟨h x hx hxc,
    fun s hs hlt ↦ hwr'.not_lt (mem_applicable.mp hs) (lt_of_lt_of_le hlt hxr)⟩

theorem selectMinimal_eq_none_of_applies (h : ∀ s ∈ v, Applies s c → Applies s c')
    (hr : v.selectMinimal c' = none) : v.selectMinimal c = none := by
  rw [selectMinimal_eq_none_iff, applicable_eq_filter h, selectMinimal_eq_none_iff.mp hr,
    List.filter_nil]

/-- Minimal selection admits no ABA where Pāṇinian Determinism holds at the middle context.
Across three contexts whose applicable rules are nested, an antihomophonous rule set that
realizes one exponent at both outer contexts realizes it at the middle one. -/
theorem realizeMinimal_eq_of_applies {c₁ c₂ c₃ : Ctx} (hv : v.Antihomophonous)
    (hc : IsChain (· ≤ ·) {s | v.IsElsewhereWinner c₂ s})
    (h₁ : ∀ s ∈ v, Applies s c₁ → Applies s c₂) (h₂ : ∀ s ∈ v, Applies s c₂ → Applies s c₃)
    (h : v.realizeMinimal c₁ = v.realizeMinimal c₃) :
    v.realizeMinimal c₂ = v.realizeMinimal c₁ := by
  rcases h₃ : v.selectMinimal c₃ with - | r
  · rw [realizeMinimal, realizeMinimal, selectMinimal_eq_none_of_applies h₂ h₃,
      selectMinimal_eq_none_of_applies h₁ (selectMinimal_eq_none_of_applies h₂ h₃)]
  · obtain ⟨r₁, hr₁, he⟩ : ∃ r₁, v.selectMinimal c₁ = some r₁ ∧ exponent r₁ = exponent r := by
      simpa [realizeMinimal, h₃] using h
    obtain rfl := hv (selectMinimal_mem hr₁) (selectMinimal_mem h₃) he
    rw [realizeMinimal, realizeMinimal, hr₁, selectMinimal_eq_some_of_applies h₂ hc h₃
      (h₁ _ (selectMinimal_mem hr₁) (selectMinimal_applies hr₁))]

section Contiguity

variable [Preorder Ctx]

/-- Under Pāṇinian Determinism, rules applicable on upper sets of contexts realize contiguous
patterns by minimal selection. -/
theorem isContiguous_realizeMinimal_of_monotone (hv : v.Antihomophonous)
    (hc : ∀ c, IsChain (· ≤ ·) {s | v.IsElsewhereWinner c s})
    (h : ∀ r ∈ v, Monotone (Applies r)) : IsContiguous v.realizeMinimal :=
  fun _ _ _ hij hjk he ↦ (realizeMinimal_eq_of_applies hv (hc _)
    (fun s hs ↦ h s hs hij) (fun s hs ↦ h s hs hjk) he).symm

/-- Under Pāṇinian Determinism, rules applicable on lower sets of contexts realize contiguous
patterns by minimal selection. -/
theorem isContiguous_realizeMinimal_of_antitone (hv : v.Antihomophonous)
    (hc : ∀ c, IsChain (· ≤ ·) {s | v.IsElsewhereWinner c s})
    (h : ∀ r ∈ v, Antitone (Applies r)) : IsContiguous v.realizeMinimal :=
  fun _ _ _ hij hjk he ↦ he.trans (realizeMinimal_eq_of_applies hv (hc _)
    (fun s hs ↦ h s hs hjk) (fun s hs ↦ h s hs hij) he.symm).symm

end Contiguity

/-! ### Realization with a fallback -/

/-- `v.realizeMinimalD fallback c` is the exponent of the rule selected by `selectMinimal`, or
`fallback c` where no rule of `v` applies at `c`. -/
def realizeMinimalD (v : RuleSet R) (fallback : Ctx → E) (c : Ctx) : E :=
  (v.realizeMinimal c).getD (fallback c)

variable {fallback : Ctx → E}

/-- With no rules, realization is the fallback. -/
@[simp] theorem realizeMinimalD_nil (fallback : Ctx → E) :
    realizeMinimalD ([] : RuleSet R) fallback = fallback :=
  funext fun _ ↦ rfl

theorem realizeMinimalD_eq_of_selectMinimal_eq_some (h : v.selectMinimal c = some r) :
    v.realizeMinimalD fallback c = exponent r := by
  simp [realizeMinimalD, realizeMinimal, h]

theorem realizeMinimalD_eq_fallback_of_selectMinimal_eq_none (h : v.selectMinimal c = none) :
    v.realizeMinimalD fallback c = fallback c := by
  simp [realizeMinimalD, realizeMinimal, h]

/-- The realized value is the fallback or the exponent of one of the rules. -/
theorem realizeMinimalD_eq_fallback_or_mem : v.realizeMinimalD fallback c = fallback c ∨
    ∃ r ∈ v, v.realizeMinimalD fallback c = exponent r :=
  match h : v.selectMinimal c with
  | none => .inl (realizeMinimalD_eq_fallback_of_selectMinimal_eq_none h)
  | some r => .inr ⟨r, selectMinimal_mem h, realizeMinimalD_eq_of_selectMinimal_eq_some h⟩

/-- A property of the fallback and of every rule's exponent holds of the realized value. -/
theorem realizeMinimalD_induction (q : E → Prop) (hd : q (fallback c))
    (hv : ∀ r ∈ v, q (exponent r)) : q (v.realizeMinimalD fallback c) := by
  obtain h | ⟨r, hr, h⟩ :=
    realizeMinimalD_eq_fallback_or_mem (v := v) (fallback := fallback) (c := c)
  · exact h ▸ hd
  · exact h ▸ hv r hr

/-- Contexts with the same applicable rules and the same fallback realize the same value. -/
theorem realizeMinimalD_congr (h : v.applicable c = v.applicable c')
    (hd : fallback c = fallback c') :
    v.realizeMinimalD fallback c = v.realizeMinimalD fallback c' := by
  rw [realizeMinimalD, realizeMinimalD, realizeMinimal_congr h, hd]

/-- Rules whose applicability sees only what `A` sees, with a fallback that factors through
`A`, realize values that factor through `A`. This is the reasoning of Stump 2006 (§5.5), by
which a rule of paradigm linkage sensitive to number alone makes number an absolute correlate of
heteroclisis. -/
theorem realizeMinimalD_factorsThrough {V : Type*} {A : Ctx → V}
    (hd : fallback.FactorsThrough A)
    (h : ∀ r ∈ v, ∀ ⦃c c'⦄, A c = A c' → (Applies r c ↔ Applies r c')) :
    (v.realizeMinimalD fallback).FactorsThrough A :=
  fun _ _ hA ↦ by rw [realizeMinimalD, realizeMinimalD, realizeMinimal, realizeMinimal,
    selectMinimal_factorsThrough h hA, hd hA]

/-- Over a coherent rule set whose Elsewhere winners form a chain, the realized value is the
exponent of any Elsewhere winner, so it does not depend on the order of the rule set. -/
theorem realizeMinimalD_eq_of_isElsewhereWinner (hv : v.Coherent)
    (hc : IsChain (· ≤ ·) {s | v.IsElsewhereWinner c s}) (hr : v.IsElsewhereWinner c r) :
    v.realizeMinimalD fallback c = exponent r := by
  rw [realizeMinimalD, realizeMinimal_eq_of_isElsewhereWinner hv hc hr, Option.getD_some]

end Morphology.Exponence.RuleSet
