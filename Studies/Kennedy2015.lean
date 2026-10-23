module

public import Linglib.Fragments.English.NumeralModifiers
public import Linglib.Semantics.Quantification.Numerals.Basic
public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Pragmatics.NeoGricean.Basic

/-!
# Kennedy (2015): A "de-Fregean" Semantics (and Neo-Gricean Pragmatics) for Modified and Unmodified Numerals

This file formalizes the de-Fregean semantics of Kennedy: a numeral, bare or modified,
is a quantifier over degree properties, true of a property when its greatest degree stands in
the numeral's relation to the number, `max{n | D(n)} = m` for the bare numeral ((29)), `> m` and
`< m` for the Class A modifiers *more than* and *fewer than* ((41)), `≥ m` and `≤ m` for the
Class B modifiers *at least* and *at most* ((42)); this is the substrate's degree quantifier
`Degree.MaxIn` at the comparison's interval. Applied to the degrees a count reaches it is the
comparison of the count, so bare numerals are two-sided without a Horn scale
(`maxIn_interval_Iic`), and the one-sided readings of numerals under root modals ((31)–(34)) are
matters of scope, `Degree.HighScope`: a bare numeral scoping over a necessity modal names the
least count the modal requires and over a possibility modal the greatest it allows
(`necessity_wide_iff`, `possibility_wide_iff`).

The two classes of Nouwen differ in the ordering they express ((4)), exclusive for
Class A and inclusive for Class B. Over the English modifiers, whose class the Fragment reads
off the construction, this is a fact about every reading, stated in Kamp's classes of modifiers:
a Class A reading is disjoint from the number's two-sided meaning and a Class B reading is
extensive (`classA_exclusive`, `classB_inclusive`).

The ignorance inferences of the Class B modifiers are Sauerland's primary implicatures ((43))
over Kennedy's single alternative set, the five forms of one numeral ((46)): *at least m* is
asymmetrically entailed by the bare numeral and by *more than m* and by no other alternative,
*at most m* by the bare numeral and *fewer than m* ((47)), while the bare numeral and the
Class A forms are entailed by no alternative at all (`interval_ssubset_iff`, `stronger_ge`,
`stronger_gt`, and the rest); and neither primary implicature of a Class B form
strengthens to a secondary one ((44)), each contradicting the assertion together with the other
(`not_isSecondaryImplicature_ge`, `not_isSecondaryImplicature_le`).

## Implementation notes

The worlds of the pragmatics are counts, so a form's content is the set `c.interval m` of counts,
the alternatives are the five forms of the numeral, one for each `Degree.Comparison`, and the
neo-Gricean operators are `NeoGricean.commitment` and `NeoGricean.IsSecondaryImplicature`. A
root modal is the quantifier `every R` or `GQ.some R` over its accessible worlds `R`, and
the numeral's two scopes are `Degree.LowScope` and `Degree.HighScope` of `MaxIn {m}` over it. The
interactions of Class B modifiers with root modals (Section 4.2) are not formalized.

## References

* [kennedy-2015]
* [sauerland-2004]
* [nouwen-2010]
-/

@[expose] public section

namespace Kennedy2015

open Degree Numerals NeoGricean Quantifier Quantifier.GQ Set

/-! ### The de-Fregean semantics (Section 3)

(29), (41), (42): the numeral form `c m` is true of a degree property when its greatest degree
stands in the relation `c` to `m`, the substrate's `MaxIn (c.interval m)`. -/

theorem maxIn_interval_Iic (c : Comparison) (m n : ℕ) :
    MaxIn (c.interval m) (Iic n) ↔ n ∈ c.interval m :=
  maxIn_Iic

/-! ### The two classes (Section 1) -/

section Classes

open English.NumeralModifiers Semantics

attribute [local simp] moreThan fewerThan over under atLeast atMost minimally maximally upTo from_
  exactly precisely about around approximately roughly almost nearly approximator shortOf

/-- Each reading of a Class A modifier (4a) is disjoint from the two-sided meaning of its number. -/
theorem classA_exclusive : ∀ w ∈ inventory, w.modifierClass = some .classA →
    ∀ m ∈ ⟦w⟧, ∀ n, Disjoint (m {n}) {n} := by
  simp [inventory, NumeralModifier.modifierClass, ModifierKind.modifierClass]

/-- A Class B modifier (4b) expresses an inclusive ordering, so each of its readings is extensive:
the number satisfies the modified numeral. -/
theorem classB_inclusive : ∀ w ∈ inventory, w.modifierClass = some .classB →
    ∀ m ∈ ⟦w⟧, Modifier.IsExtensive m := by
  simp [inventory, NumeralModifier.modifierClass, ModifierKind.modifierClass,
    Comparison.isExtensive_modifier_iff, Comparison.IsStrict]

end Classes

section Modals

variable {W : Type*} (R : W → Prop) (count : W → ℕ) (m : ℕ)

/-- Under a modal the bare numeral keeps its two-sided content in each accessible
world ((33a), (34a)). -/
theorem narrow_scope_two_sided (Q : NP W) :
    LowScope (MaxIn {m}) Q (Iic ∘ count) ↔ Q fun w ↦ count w = m :=
  lowScope_maxIn

private theorem isGLB_iff_isLeast {s : Set ℕ} : IsGLB s m ↔ IsLeast s m :=
  ⟨fun h ↦ h.isLeast <| by_contra fun hm ↦ absurd
      (h.2 (show m + 1 ∈ lowerBounds s from
        fun x hx ↦ Nat.lt_of_le_of_ne (h.1 hx) fun e ↦ hm (e ▸ hx))) (by omega),
    IsLeast.isGLB⟩

/-- Over a necessity modal the bare numeral is lower-bounded (33b), `m` being the least count the
modal requires. -/
theorem necessity_wide_iff :
    HighScope (MaxIn {m}) (every R) (Iic ∘ count) ↔ IsLeast (count '' {w | R w}) m :=
  highScope_maxIn_singleton_every.trans (isGLB_iff_isLeast m)

/-- Over a possibility modal the bare numeral is upper-bounded (34b), `m` being the greatest count
the modal allows. -/
theorem possibility_wide_iff :
    HighScope (MaxIn {m}) (GQ.some R) (Iic ∘ count) ↔ IsGreatest (count '' {w | R w}) m :=
  highScope_maxIn_singleton_some

end Modals

/-! ### Ignorance implicatures (Section 4.1) -/

/-- The alternatives of a numeral form (46) are the five forms of the same numeral, one for each
comparison, as sets of counts. -/
def alternatives (m : ℕ) : Set (Set ℕ) := Set.range fun c : Comparison ↦ c.interval m

/-- The alternatives that asymmetrically entail a form (43), as comparisons, give the form's
primary implicatures as their negated knowledge. -/
def stronger (m : ℕ) (c : Comparison) : Set Comparison :=
  {c' | c'.interval m ⊂ c.interval m}

private theorem interval_subset_iff (c c' : Comparison) {m : ℕ} (hm : 0 < m) :
    c.interval m ⊆ c'.interval m ↔
      (c.Rel 0 m → c'.Rel 0 m) ∧ (c.Rel m m → c'.Rel m m) ∧
        (c.Rel (m + 1) m → c'.Rel (m + 1) m) := by
  simp only [Set.subset_def, Comparison.mem_interval]
  refine ⟨fun h ↦ ⟨h 0, h m, h (m + 1)⟩, fun ⟨h0, hm', h1⟩ x hx ↦ ?_⟩
  cases c <;> cases c' <;>
    simp only [Comparison.Rel, imp_iff_not_or, not_true_eq_false, false_or] at h0 hm' h1 hx ⊢ <;>
    omega

theorem interval_ssubset_iff {m : ℕ} (hm : 0 < m) (c c' : Comparison) :
    c.interval m ⊂ c'.interval m ↔
      (c, c') ∈ [(Comparison.eq, Comparison.ge), (.eq, .le), (.gt, .ge), (.lt, .le)] := by
  rw [Set.ssubset_def, interval_subset_iff c c' hm, interval_subset_iff c' c hm]
  cases c <;> cases c' <;> simp [Comparison.Rel, imp_iff_not_or] <;> omega

/-- *At least m* (47a) is asymmetrically entailed by the bare numeral and by *more than m*, so
its primary implicatures are ignorance of both. -/
theorem stronger_ge {m : ℕ} (hm : 0 < m) : stronger m .ge = {.eq, .gt} := by
  ext c
  simp only [stronger, Set.mem_ofPred_eq, interval_ssubset_iff hm]
  cases c <;> simp

/-- *At most m* (47b) is asymmetrically entailed by the bare numeral and by *fewer than m*. -/
theorem stronger_le {m : ℕ} (hm : 0 < m) : stronger m .le = {.eq, .lt} := by
  ext c
  simp only [stronger, Set.mem_ofPred_eq, interval_ssubset_iff hm]
  cases c <;> simp

theorem stronger_eq {m : ℕ} (hm : 0 < m) : stronger m .eq = ∅ := by
  ext c
  simp only [stronger, Set.mem_ofPred_eq, interval_ssubset_iff hm]
  cases c <;> simp

theorem stronger_gt {m : ℕ} (hm : 0 < m) : stronger m .gt = ∅ := by
  ext c
  simp only [stronger, Set.mem_ofPred_eq, interval_ssubset_iff hm]
  cases c <;> simp

theorem stronger_lt {m : ℕ} (hm : 0 < m) : stronger m .lt = ∅ := by
  ext c
  simp only [stronger, Set.mem_ofPred_eq, interval_ssubset_iff hm]
  cases c <;> simp

/-- The strengthening (44) fails for *at least m*, leaving the ignorance unstrengthened. -/
theorem not_isSecondaryImplicature_ge (m : ℕ) :
    ¬ IsSecondaryImplicature (Comparison.ge.interval m) (alternatives m)
        (Comparison.eq.interval m) ∧
      ¬ IsSecondaryImplicature (Comparison.ge.interval m) (alternatives m)
        (Comparison.gt.interval m) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine (isSecondaryImplicature_iff.mp h).2 (Comparison.gt.interval m)
      ⟨_, rfl⟩ fun n ⟨h1, h2⟩ ↦ ?_
    simp only [Comparison.mem_interval, Comparison.Rel] at *
    omega
  · refine (isSecondaryImplicature_iff.mp h).2 (Comparison.eq.interval m)
      ⟨_, rfl⟩ fun n ⟨h1, h2⟩ ↦ ?_
    simp only [Comparison.mem_interval, Comparison.Rel] at *
    omega

/-- (44) fails for *at most m* the same way, with *fewer than m* in place of *more than m*. -/
theorem not_isSecondaryImplicature_le (m : ℕ) :
    ¬ IsSecondaryImplicature (Comparison.le.interval m) (alternatives m)
        (Comparison.eq.interval m) ∧
      ¬ IsSecondaryImplicature (Comparison.le.interval m) (alternatives m)
        (Comparison.lt.interval m) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine (isSecondaryImplicature_iff.mp h).2 (Comparison.lt.interval m)
      ⟨_, rfl⟩ fun n ⟨h1, h2⟩ ↦ ?_
    simp only [Comparison.mem_interval, Comparison.Rel] at *
    omega
  · refine (isSecondaryImplicature_iff.mp h).2 (Comparison.eq.interval m)
      ⟨_, rfl⟩ fun n ⟨h1, h2⟩ ↦ ?_
    simp only [Comparison.mem_interval, Comparison.Rel] at *
    omega

end Kennedy2015
