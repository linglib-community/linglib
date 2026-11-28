module

public import Linglib.Core.Data.List.Find
public import Linglib.Core.Data.List.MinMax
public import Linglib.Morphology.Exponence.Elsewhere
public import Linglib.Core.Order.OrdConnected

/-!
# Elsewhere selection

Minimal selection takes the first applicable rule of a rule set that no applicable rule strictly
undercuts under a specificity key, and so returns an Elsewhere winner. Where Stump's Pāṇinian
Determinism holds, the Elsewhere winners being equally specific, it keeps its choice when the
competition shrinks around the winner, so rules applicable on upper sets of ordered contexts realize
contiguous patterns. Selection by a score in a linear order is minimal selection under the key that
reverses the score; a linear key is always deterministic, so its contraction and contiguity hold
outright. The exponent of the minimal selection, falling back on a default where no rule applies,
is the shape shared by Stump's rules of paradigm linkage over a root and by Bonami and Stump's rules
of basic stem choice.

## Main definitions

* `RuleSet.selectBy`, `RuleSet.realize`: the applicable rule of greatest score, and its
  exponent.
* `RuleSet.selectMinimal`, `RuleSet.realizeMinimal`: the first applicable rule that no
  applicable rule strictly undercuts, and its exponent.
* `RuleSet.realizeMinimalD`: the exponent of the minimal selection, or a fallback where
  no rule applies.

## Main results

* `RuleSet.selectBy_eq_selectMinimal`: selection by a score is minimal selection under the key
  that reverses the score.
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
* `RuleSet.realizeMinimal_eq_some_iff`: under Pāṇinian Determinism minimal selection over a
  coherent rule set realizes exactly the exponents of the Elsewhere winners.
* `RuleSet.realizeMinimal_eq_realize`: under Pāṇinian Determinism minimal selection realizes
  what selection on any score strictly reversing specificity realizes.
* `RuleSet.selectMinimal_factorsThrough`, `RuleSet.realizeMinimal_factorsThrough`,
  `RuleSet.realizeMinimalD_factorsThrough`: selection, realization, and realization with a
  fallback, factor through any map on contexts that every rule's applicability (and the
  fallback) factors through.

## References

* [bonami-stump-2016]
* [stump-2006]
-/

@[expose] public section

namespace Morphology.RuleSet

variable {Ctx E : Type*} {R : Type*} [ExponenceRule R Ctx E]
variable [DecidableRel (Applies : R → Ctx → Prop)]
variable {v : RuleSet R} {c c' : Ctx} {r s : R} {φ : E}

/-! ### Applicable rules -/

/-- The rules of `v` applicable at `c`, in the order of `v`. -/
def applicable (v : RuleSet R) (c : Ctx) : List R :=
  v.filter (fun r ↦ Applies r c)

@[simp] theorem mem_applicable :
    r ∈ v.applicable c ↔ r ∈ v ∧ Applies r c := by
  simp only [applicable, List.mem_filter, decide_eq_true_eq]

theorem applicable_eq_filter (h : ∀ s ∈ v, Applies s c → Applies s c') :
    v.applicable c = (v.applicable c').filter (fun s ↦ Applies s c) := by
  rw [applicable, applicable, List.filter_filter]
  exact List.filter_congr fun s hs ↦ by by_cases hc : Applies s c <;> simp [hc, h s hs]

/-! ### Minimal selection -/

variable {κ : Type*} [Preorder κ] {key : R → κ}

section Minimal

variable [DecidableRel (· < · : κ → κ → Prop)]

/-- The first applicable rule that no applicable rule is strictly more specific than,
specificity read through `key`. -/
def selectMinimal (v : RuleSet R) (key : R → κ) (c : Ctx) : Option R :=
  (v.applicable c).find? (fun r ↦ (v.applicable c).all (fun s ↦ decide (¬ key s < key r)))

/-- `selectMinimal` returns an Elsewhere winner. -/
theorem selectMinimal_isElsewhereWinner
    (h : v.selectMinimal key c = some r) : v.IsElsewhereWinner key c r := by
  have hall := List.find?_some h
  simp only [List.all_eq_true, decide_eq_true_eq, mem_applicable] at hall
  exact minimalFor_iff_forall_lt.mpr
    ⟨mem_applicable.mp (List.mem_of_find?_eq_some h), fun s hlt hs ↦ hall s hs hlt⟩

theorem selectMinimal_mem (h : v.selectMinimal key c = some r) : r ∈ v :=
  (selectMinimal_isElsewhereWinner h).prop.1

theorem selectMinimal_isSome_iff :
    (v.selectMinimal key c).isSome ↔ ∃ r ∈ v, Applies r c := by
  rw [selectMinimal, List.find?_isSome]
  simp only [List.all_eq_true, decide_eq_true_eq, mem_applicable]
  exact ⟨fun ⟨r, hr, _⟩ ↦ ⟨r, hr⟩, fun h ↦ (exists_isElsewhereWinner (key := key) h).imp
    fun w hw ↦ ⟨hw.1, fun s hs ↦ hw.not_lt hs⟩⟩

theorem selectMinimal_eq_none_iff :
    v.selectMinimal key c = none ↔ v.applicable c = [] := by
  rw [← Option.not_isSome_iff_eq_none, selectMinimal_isSome_iff]
  simp [applicable, List.filter_eq_nil_iff]

theorem selectMinimal_congr (h : v.applicable c = v.applicable c') :
    v.selectMinimal key c = v.selectMinimal key c' := by
  rw [selectMinimal, selectMinimal, h]

/-- A rule system sensitive only to what `A` sees selects the same rule in
contexts that `A` identifies. -/
theorem selectMinimal_factorsThrough {V : Type*} {A : Ctx → V}
    (h : ∀ r ∈ v, ∀ ⦃c c'⦄, A c = A c' → (Applies r c ↔ Applies r c')) :
    (v.selectMinimal key).FactorsThrough A :=
  fun _ _ hA ↦ selectMinimal_congr <| List.filter_congr fun r hr ↦ by simp [h r hr hA]

/-- The exponent of the rule selected by `selectMinimal`, the order-based counterpart of
`realize`. -/
def realizeMinimal (v : RuleSet R) (key : R → κ) (c : Ctx) : Option E :=
  (v.selectMinimal key c).map exponent

/-- A rule system sensitive only to what `A` sees realizes the same exponent in contexts that `A`
identifies. -/
theorem realizeMinimal_factorsThrough {V : Type*} {A : Ctx → V}
    (h : ∀ r ∈ v, ∀ ⦃c c'⦄, A c = A c' → (Applies r c ↔ Applies r c')) :
    (v.realizeMinimal key).FactorsThrough A :=
  fun _ _ hA ↦ congrArg (Option.map exponent) (selectMinimal_factorsThrough h hA)

theorem realizeMinimal_eq_none_iff : v.realizeMinimal key c = none ↔ v.applicable c = [] :=
  Option.map_eq_none_iff.trans selectMinimal_eq_none_iff

theorem realizeMinimal_congr (h : v.applicable c = v.applicable c') :
    v.realizeMinimal key c = v.realizeMinimal key c' :=
  congrArg (Option.map exponent) (selectMinimal_congr h)

/-! ### Contraction under Pāṇinian Determinism -/

/-- Minimal selection is consistent under contraction where the rule set is Pāṇinian at the smaller
context. The rule selected at `c'` is then selected at any context whose applicable rules are among
those at `c'`, as long as it applies there. -/
theorem selectMinimal_eq_some_of_applies (h : ∀ s ∈ v, Applies s c → Applies s c')
    (hc : v.IsPaninian key c)
    (hr : v.selectMinimal key c' = some r)
    (hrc : Applies r c) : v.selectMinimal key c = some r := by
  have hwr' := selectMinimal_isElsewhereWinner hr
  have hwr : v.IsElsewhereWinner key c r := hwr'.of_applies h hrc
  rw [selectMinimal] at hr ⊢
  nth_rewrite 2 [applicable_eq_filter h]
  rw [List.find?_filter]
  refine List.find?_eq_some_of_imp hr ?_ fun x hx hpx ↦ ?_
  · simpa [hrc] using fun s hs hlt ↦ hwr.not_lt (mem_applicable.mp hs) hlt
  simp only [decide_eq_true_eq, List.all_eq_true] at hpx
  obtain ⟨hxc, hxmin⟩ := hpx
  have hwx : v.IsElsewhereWinner key c x := minimalFor_iff_forall_lt.mpr
    ⟨⟨(mem_applicable.mp hx).1, hxc⟩, fun s hlt hs ↦ hxmin s (mem_applicable.mpr hs) hlt⟩
  have hxr : key x ≤ key r := hc hwx hwr
  simpa using fun s hs hlt ↦ hwr'.not_lt (mem_applicable.mp hs) (lt_of_lt_of_le hlt hxr)

theorem selectMinimal_eq_none_of_applies (h : ∀ s ∈ v, Applies s c → Applies s c')
    (hr : v.selectMinimal key c' = none) : v.selectMinimal key c = none := by
  rw [selectMinimal_eq_none_iff, applicable_eq_filter h, selectMinimal_eq_none_iff.mp hr,
    List.filter_nil]

theorem realizeMinimal_eq_of_applies {c₁ c₂ c₃ : Ctx} (hv : v.Antihomophonous)
    (hc : v.IsPaninian key c₂)
    (h₁ : ∀ s ∈ v, Applies s c₁ → Applies s c₃ → Applies s c₂)
    (h₂ : ∀ s ∈ v, Applies s c₂ → Applies s c₃)
    (h : v.realizeMinimal key c₁ = v.realizeMinimal key c₃) :
    v.realizeMinimal key c₂ = v.realizeMinimal key c₁ := by
  rcases h₃ : v.selectMinimal key c₃ with - | r
  · rw [h, realizeMinimal, realizeMinimal, h₃, selectMinimal_eq_none_of_applies h₂ h₃]
  · obtain ⟨r₁, hr₁, he⟩ : ∃ r₁, v.selectMinimal key c₁ = some r₁ ∧ exponent r₁ = exponent r := by
      simpa [realizeMinimal, h₃] using h
    obtain rfl := hv (selectMinimal_mem hr₁) (selectMinimal_mem h₃) he
    rw [realizeMinimal, realizeMinimal, hr₁, selectMinimal_eq_some_of_applies h₂ hc h₃
      (h₁ _ (selectMinimal_mem hr₁) (selectMinimal_isElsewhereWinner hr₁).prop.2
        (selectMinimal_isElsewhereWinner h₃).prop.2)]

section Contiguity

variable [Preorder Ctx]

/-- Under Pāṇinian Determinism, rules applicable on upper sets of contexts realize contiguous
patterns by minimal selection. -/
theorem isContiguous_realizeMinimal_of_monotone (hv : v.Antihomophonous)
    (hc : ∀ c, v.IsPaninian key c)
    (h : ∀ r ∈ v, Monotone (Applies r)) : IsContiguous (v.realizeMinimal key) :=
  fun _ _ _ hij hjk he ↦ (realizeMinimal_eq_of_applies hv (hc _)
    (fun s hs hi _ ↦ h s hs hij hi) (fun s hs ↦ h s hs hjk) he).symm

theorem isContiguous_realizeMinimal_of_antitone (hv : v.Antihomophonous)
    (hc : ∀ c, v.IsPaninian key c)
    (h : ∀ r ∈ v, Antitone (Applies r)) : IsContiguous (v.realizeMinimal key) :=
  fun _ _ _ hij hjk he ↦ he.trans (realizeMinimal_eq_of_applies hv (hc _)
    (fun s hs hk _ ↦ h s hs hjk hk) (fun s hs ↦ h s hs hij) he.symm).symm

end Contiguity

end Minimal

/-! ### Score selection -/

variable {α : Type*} [LinearOrder α] {f : R → α}

/-- The applicable rule of greatest score `f`, ties broken by the order of
the rule set; scores to be minimized pass through `OrderDual`. -/
def selectBy (v : RuleSet R) (f : R → α) (c : Ctx) : Option R :=
  (v.applicable c).argmax f

/-- Selection by a score is minimal selection under the key that reverses the score. -/
theorem selectBy_eq_selectMinimal (v : RuleSet R) (f : R → α) :
    v.selectBy f = v.selectMinimal (OrderDual.toDual ∘ f) := by
  funext c
  simp [selectBy, selectMinimal, List.argmax_eq_find?]

theorem selectBy_mem (h : v.selectBy f c = some r) : r ∈ v :=
  selectMinimal_mem (selectBy_eq_selectMinimal v f ▸ h)

theorem selectBy_applies (h : v.selectBy f c = some r) : Applies r c :=
  (selectMinimal_isElsewhereWinner (selectBy_eq_selectMinimal v f ▸ h)).prop.2

theorem selectBy_eq_none_iff : v.selectBy f c = none ↔ v.applicable c = [] :=
  selectBy_eq_selectMinimal v f ▸ selectMinimal_eq_none_iff

/-- On a rule set listed by non-increasing score, selection takes the first applicable rule. -/
theorem selectBy_eq_head?_applicable (h : v.Pairwise fun r s ↦ f s ≤ f r) :
    v.selectBy f c = (v.applicable c).head? :=
  List.argmax_eq_head? (h.filter _)

theorem selectBy_isSome_iff : (v.selectBy f c).isSome ↔ ∃ r ∈ v, Applies r c :=
  selectBy_eq_selectMinimal v f ▸ selectMinimal_isSome_iff

theorem selectBy_congr (h : v.applicable c = v.applicable c') :
    v.selectBy f c = v.selectBy f c' := by
  rw [selectBy, selectBy, h]

/-- The exponent of the rule selected by `selectBy`. -/
def realize (v : RuleSet R) (f : R → α) (c : Ctx) : Option E :=
  (v.selectBy f c).map exponent

/-- Realization by a score is minimal realization under the key that reverses the score. -/
theorem realize_eq_realizeMinimal (v : RuleSet R) (f : R → α) :
    v.realize f = v.realizeMinimal (OrderDual.toDual ∘ f) :=
  funext fun c ↦ congrArg (Option.map exponent) (congrFun (selectBy_eq_selectMinimal v f) c)

theorem realize_eq_none_iff : v.realize f c = none ↔ v.applicable c = [] :=
  Option.map_eq_none_iff.trans selectBy_eq_none_iff

theorem realize_congr (h : v.applicable c = v.applicable c') :
    v.realize f c = v.realize f c' :=
  congrArg (Option.map exponent) (selectBy_congr h)

/-- A rule set sensitive only to what `A` sees selects the same rule by score in contexts that `A`
identifies. -/
theorem selectBy_factorsThrough {V : Type*} {A : Ctx → V}
    (h : ∀ r ∈ v, ∀ ⦃c c'⦄, A c = A c' → (Applies r c ↔ Applies r c')) :
    (v.selectBy f).FactorsThrough A :=
  selectBy_eq_selectMinimal v f ▸ selectMinimal_factorsThrough h

/-- A rule set sensitive only to what `A` sees realizes the same exponent by score in contexts
that `A` identifies. -/
theorem realize_factorsThrough {V : Type*} {A : Ctx → V}
    (h : ∀ r ∈ v, ∀ ⦃c c'⦄, A c = A c' → (Applies r c ↔ Applies r c')) :
    (v.realize f).FactorsThrough A :=
  realize_eq_realizeMinimal v f ▸ realizeMinimal_factorsThrough h

theorem le_of_selectBy_eq_some (h : v.selectBy f c = some r) (hs : s ∈ v) (hsc : Applies s c) :
    f s ≤ f r :=
  List.le_of_mem_argmax (mem_applicable.mpr ⟨hs, hsc⟩) h

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

/-- Selection by a score is consistent under contraction. The rule selected at `c'` is selected
at any context whose applicable rules are among those at `c'`, as long as it applies there. A
linear key is deterministic, so this is the contraction of minimal selection. -/
theorem selectBy_eq_some_of_applies (h : ∀ s ∈ v, Applies s c → Applies s c')
    (hr : v.selectBy f c' = some r) (hrc : Applies r c) : v.selectBy f c = some r := by
  rw [selectBy_eq_selectMinimal] at hr ⊢
  exact selectMinimal_eq_some_of_applies h (isPaninian_of_linearOrder _ _ _) hr hrc

theorem selectBy_eq_none_of_applies (h : ∀ s ∈ v, Applies s c → Applies s c')
    (hr : v.selectBy f c' = none) : v.selectBy f c = none := by
  rw [selectBy_eq_selectMinimal] at hr ⊢
  exact selectMinimal_eq_none_of_applies h hr

/-- An antihomophonous rule set realizing one exponent at `c₁` and `c₃` realizes it at `c₂`, if `c₂`
takes in the rules `c₁` and `c₃` share and its rules all reach `c₃`. The rules of `c₁` need not all
reach `c₂`. -/
theorem realize_eq_of_applies {c₁ c₂ c₃ : Ctx} (hv : v.Antihomophonous)
    (h₁ : ∀ s ∈ v, Applies s c₁ → Applies s c₃ → Applies s c₂)
    (h₂ : ∀ s ∈ v, Applies s c₂ → Applies s c₃)
    (h : v.realize f c₁ = v.realize f c₃) : v.realize f c₂ = v.realize f c₁ := by
  rw [realize_eq_realizeMinimal] at h ⊢
  exact realizeMinimal_eq_of_applies hv (isPaninian_of_linearOrder _ _ _) h₁ h₂ h

section Contiguity

variable [Preorder Ctx]

/-- Rules applicable on upper sets of contexts realize contiguous patterns. -/
theorem isContiguous_realize_of_monotone (hv : v.Antihomophonous)
    (h : ∀ r ∈ v, Monotone (Applies r)) : IsContiguous (v.realize f) :=
  realize_eq_realizeMinimal v f ▸
    isContiguous_realizeMinimal_of_monotone hv (fun _ ↦ isPaninian_of_linearOrder _ _ _) h

/-- Rules applicable on lower sets of contexts realize contiguous patterns. -/
theorem isContiguous_realize_of_antitone (hv : v.Antihomophonous)
    (h : ∀ r ∈ v, Antitone (Applies r)) : IsContiguous (v.realize f) :=
  realize_eq_realizeMinimal v f ▸
    isContiguous_realizeMinimal_of_antitone hv (fun _ ↦ isPaninian_of_linearOrder _ _ _) h

end Contiguity

/-! ### Transport -/

section Map

variable {R' Ctx' E' : Type*} [ExponenceRule R' Ctx' E'] [DecidableRel (Applies : R' → Ctx' → Prop)]
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

/-- A score that strictly reverses specificity on the applicable rules selects an Elsewhere
winner. -/
theorem selectBy_isElsewhereWinner
    (hf : ∀ r ∈ v.applicable c, ∀ s ∈ v.applicable c, key r < key s → f s < f r)
    (h : v.selectBy f c = some r) : v.IsElsewhereWinner key c r := by
  refine minimalFor_iff_forall_lt.2 ⟨mem_applicable.mp (List.argmax_mem h), fun s hsr hs ↦ ?_⟩
  exact absurd (List.le_of_mem_argmax (mem_applicable.mpr hs) h)
    (not_le_of_gt (hf _ (mem_applicable.mpr hs) _ (List.argmax_mem h) hsr))

theorem realize_realizes
    (hf : ∀ r ∈ v.applicable c, ∀ s ∈ v.applicable c, key r < key s → f s < f r)
    (h : v.realize f c = some φ) : v.Realizes key c φ := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨r, selectBy_isElsewhereWinner hf hr, rfl⟩

variable [DecidableRel (· < · : κ → κ → Prop)]

/-- Under Pāṇinian Determinism minimal selection over a coherent rule set realizes exactly what
the Elsewhere winners carry, whatever the order of the rule set. -/
theorem realizeMinimal_eq_some_iff (hv : v.Coherent key)
    (hc : v.IsPaninian key c) :
    v.realizeMinimal key c = some φ ↔ v.Realizes key c φ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨r, selectMinimal_isElsewhereWinner hr, rfl⟩
  · obtain ⟨r, hr, -⟩ := id h
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp
      (selectMinimal_isSome_iff (key := key).mpr ⟨r, hr.prop.1, hr.prop.2⟩)
    rw [realizeMinimal, ht, Option.map_some,
      Realizes.eq hv hc ⟨t, selectMinimal_isElsewhereWinner ht, rfl⟩ h]

/-- Under Pāṇinian Determinism a coherent rule set realizes by minimal selection what it
realizes by selection on any score strictly reversing specificity. -/
theorem realizeMinimal_eq_realize (hv : v.Coherent key)
    (hc : v.IsPaninian key c)
    (hf : ∀ r ∈ v.applicable c, ∀ s ∈ v.applicable c, key r < key s → f s < f r) :
    v.realizeMinimal key c = v.realize f c := by
  rcases hs : v.realize f c with - | φ
  · rwa [realizeMinimal_eq_none_iff, ← realize_eq_none_iff (f := f)]
  · exact (realizeMinimal_eq_some_iff hv hc).mpr (realize_realizes hf hs)

/-! ### Realization with a fallback -/

/-- `v.realizeMinimalD key fallback c` is the exponent of the rule selected by `selectMinimal`, or
`fallback c` where no rule of `v` applies at `c`. -/
def realizeMinimalD (v : RuleSet R) (key : R → κ) (fallback : Ctx → E) (c : Ctx) : E :=
  (v.realizeMinimal key c).getD (fallback c)

variable {fallback : Ctx → E}

@[simp] theorem realizeMinimalD_nil (fallback : Ctx → E) :
    realizeMinimalD ([] : RuleSet R) key fallback = fallback :=
  funext fun _ ↦ rfl

theorem realizeMinimalD_eq_of_selectMinimal_eq_some (h : v.selectMinimal key c = some r) :
    v.realizeMinimalD key fallback c = exponent r := by
  simp [realizeMinimalD, realizeMinimal, h]

theorem realizeMinimalD_eq_fallback_of_selectMinimal_eq_none (h : v.selectMinimal key c = none) :
    v.realizeMinimalD key fallback c = fallback c := by
  simp [realizeMinimalD, realizeMinimal, h]

/-- Under Pāṇinian Determinism realization with a fallback over a coherent rule set returns the
exponent of any Elsewhere winner, whatever the order of the rule set. -/
theorem Realizes.realizeMinimalD_eq (hv : v.Coherent key)
    (hc : v.IsPaninian key c)
    (h : v.Realizes key c φ) : v.realizeMinimalD key fallback c = φ := by
  rw [realizeMinimalD, (realizeMinimal_eq_some_iff hv hc).mpr h, Option.getD_some]

theorem realizeMinimalD_eq_fallback_or_mem : v.realizeMinimalD key fallback c = fallback c ∨
    ∃ r ∈ v, v.realizeMinimalD key fallback c = exponent r :=
  match h : v.selectMinimal key c with
  | none => .inl (realizeMinimalD_eq_fallback_of_selectMinimal_eq_none h)
  | some r => .inr ⟨r, selectMinimal_mem h, realizeMinimalD_eq_of_selectMinimal_eq_some h⟩

theorem realizeMinimalD_induction (q : E → Prop) (hd : q (fallback c))
    (hv : ∀ r ∈ v, q (exponent r)) : q (v.realizeMinimalD key fallback c) := by
  obtain h | ⟨r, hr, h⟩ :=
    realizeMinimalD_eq_fallback_or_mem (v := v) (key := key) (fallback := fallback) (c := c)
  · exact h ▸ hd
  · exact h ▸ hv r hr

/-- Rules whose applicability factors through `A`, with a fallback that does too, realize values
that factor through `A` (Stump 2006, §5.5). -/
theorem realizeMinimalD_factorsThrough {V : Type*} {A : Ctx → V}
    (hd : fallback.FactorsThrough A)
    (h : ∀ r ∈ v, ∀ ⦃c c'⦄, A c = A c' → (Applies r c ↔ Applies r c')) :
    (v.realizeMinimalD key fallback).FactorsThrough A :=
  fun _ _ hA ↦ by rw [realizeMinimalD, realizeMinimalD, realizeMinimal, realizeMinimal,
    selectMinimal_factorsThrough h hA, hd hA]

end Morphology.RuleSet
