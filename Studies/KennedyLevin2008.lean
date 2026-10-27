module

public import Linglib.Semantics.Degree.Boundedness
public import Mathlib.Algebra.Order.Group.PosPart
public import Studies.HayKennedyLevin1999

/-!
# Kennedy and Levin (2008): Measure of Change

This file formalizes Kennedy and Levin's account of variable telicity in degree achievements.
Following Kennedy and McNally, a comparative such as *wider than the carpet* is the positive form
of a difference function, which measures on the part of its adjective's scale from the comparative
standard up. A degree achievement is built on a measure of change, the difference function at the
degree its argument has when the event begins, applied when it ends. The scale of a measure of
change always has a least degree and inherits any greatest degree of the adjective's scale, so
Interpretive Economy admits a minimum standard for every degree achievement, giving the atelic
comparative reading, and a maximum standard, giving the telic reading, exactly when the adjective's
scale is closed above. The telic reading is the positive form of the adjective at the end of the
event, entails the atelic one and is preferred. *Widen* thus has no telic reading and never means
*become wide*.

On every set of positive difference values the measure of change agrees with Hay, Kennedy and
Levin's difference value, so the two accounts differ only in the values a modifier names: a measure
phrase requires at least its degree of change here and exactly that degree there. The English
fragment's degree achievements take the Vendler class that Interpretive Economy gives their base
scales.

## Implementation notes

* The difference function of `m` at `d` is `Set.projIci d ∘ m`, onto the ray `Set.Ici d` whose `⊥`
  and `⊤` are the derived zero and the inherited maximum, and `measureOfChange m x i` is the
  difference function of `m x` at the degree `x` has at the time `i`. The paper applies `m` to the
  initial and final intervals of the event. The verbal positive form (26) at the minimum and
  maximum standards is the preimage of `Set.Ioi ⊥` and of `Set.Ici ⊤`, as for adjectives.
* The amount of change is the distance above the derived zero, the positive part of the
  difference (`coe_measureOfChange_sub`), as the paper glosses the difference function (23). A
  verbal degree modifier compares it with a degree, and on positive values it then has the reading
  of Hay, Kennedy and Levin's modifier with the same comparison (`describes_interval_iff`); their
  measure phrase compares by `Degree.Comparison.eq` and the one here by `Degree.Comparison.ge`.
* The minimum standard is read strictly, `⊥ < ·`, after the prose and Kennedy's positive form,
  though the verbal positive form is printed with `⪰`. An argument that begins with the greatest
  degree meets the maximum standard without changing, so the theorems relating the two readings
  assume it does not.
* An ordered additive group with a greatest element is trivial, so the comparison with Hay,
  Kennedy and Levin's additive difference values is stated against a maximal degree `top`, as
  their study does, not `⊤`.
* As printed, the denotation of *slightly* in (34b) has both relations reversed; the file follows
  the prose, a degree above the minimum and at most a small one.

## TODO

* Derive the telicity of the two readings from their truth conditions rather than from the
  standard. The atelic reading lacks `Aspect.HasSubintervalProperty`, since nothing changes over
  a point interval, so the atelic half needs a subinterval property relative to a minimal
  duration.

## References

* [C. Kennedy and B. Levin, *Measure of Change: The Adjectival Core of Degree Achievements*
  (2008)][kennedy-levin-2008]
* [C. Kennedy and L. McNally, *Scale Structure, Degree Modification, and the Semantics of Gradable
  Predicates* (2005)][kennedy-mcnally-2005]
* [J. Hay, C. Kennedy and B. Levin, *Scalar Structure Underlies Telicity in “Degree
  Achievements”* (1999)][hay-kennedy-levin-1999]
* [C. Kennedy, *Vagueness and Grammar: The Semantics of Relative and Absolute Gradable Adjectives*
  (2007)][kennedy-2007]
-/

@[expose] public section

namespace KennedyLevin2008

open Degree Aspect Set

/-! ### The measure of change (25) -/

section MeasureOfChange

variable {α δ T : Type*} [LinearOrder δ]

/-- The measure of change of `m` for `x` from the time `i` (25) is the difference function of
`m x` at the degree `x` has at `i`. Its value at a later time is how far `x` has moved up the
scale, and the derived zero when it has not moved up. -/
def measureOfChange (m : α → T → δ) (x : α) (i : T) : T → Ici (m x i) :=
  projIci (m x i) ∘ m x

variable (m : α → T → δ) (x : α) (i : T)

-- §7.3.3
theorem admits_iff {s : PositiveStandard} :
    (Boundedness.ofOrder (Ici (m x i))).Admits s ↔
      s = .minEndpoint ∨ s = .maxEndpoint ∧ (Boundedness.ofOrder δ).HasMax := by
  rw [Boundedness.ofOrder_Ici, Boundedness.admits_withMin_iff]

-- (6)
theorem admits_iff_of_noMaxOrder [NoMaxOrder δ] {s : PositiveStandard} :
    (Boundedness.ofOrder (Ici (m x i))).Admits s ↔ s = .minEndpoint := by
  simp [admits_iff]

theorem defaultStandard_eq :
    (Boundedness.ofOrder (Ici (m x i))).defaultStandard =
      if (Boundedness.ofOrder δ).HasMax then .maxEndpoint else .minEndpoint := by
  rw [Boundedness.ofOrder_Ici, Boundedness.defaultStandard_withMin]

end MeasureOfChange

/-! ### The readings of a degree achievement (26)–(27) -/

section Readings

variable {α δ T : Type*} [LinearOrder δ] {m : α → T → δ} {x : α} {i f : T}

-- (27)
theorem preimage_measureOfChange_Ioi_bot :
    measureOfChange m x i ⁻¹' Set.Ioi ⊥ = m x ⁻¹' Set.Ioi (m x i) :=
  preimage_projIci_comp_Ioi_bot

variable [OrderTop δ]

-- (27), §7.3.3
theorem preimage_measureOfChange_Ici_top (h : m x i ≠ ⊤) :
    measureOfChange m x i ⁻¹' Set.Ici ⊤ = m x ⁻¹' Set.Ici ⊤ :=
  preimage_projIci_comp_Ici_top h

-- §7.3.3
theorem preimage_measureOfChange_Ici_top_subset (h : m x i ≠ ⊤) :
    measureOfChange m x i ⁻¹' Set.Ici ⊤ ⊆ measureOfChange m x i ⁻¹' Set.Ioi ⊥ :=
  Set.preimage_mono (Set.Ici_subset_Ioi.2 h.lt_top)

end Readings

/-! ### Measure phrases and degree modifiers (32)–(34) -/

section Modifiers

open HayKennedyLevin1999

variable {α δ T : Type*} [AddCommGroup δ] [LinearOrder δ] [IsOrderedAddMonoid δ]
  {m : α → T → δ} {x : α} {i f : T}

/-- The amount of change is the positive part of the difference between the final and initial
degrees (23). -/
theorem coe_measureOfChange_sub : (measureOfChange m x i f : δ) - m x i = (m x f - m x i)⁺ := by
  rw [measureOfChange, Function.comp_apply, coe_projIci, max_comm, sup_eq_add_posPart_sub,
    add_sub_cancel_left]

-- [hay-kennedy-levin-1999]
theorem describes_iff_of_subset_Ioi {D : Set δ} (hD : D ⊆ Ioi 0) :
    Describes m x D i f ↔ (measureOfChange m x i f : δ) - m x i ∈ D := by
  rw [describes_iff_sub_mem, coe_measureOfChange_sub]
  rcases le_or_gt (m x f - m x i) 0 with h | h
  · rw [posPart_eq_zero.2 h]
    exact iff_of_false (fun hd ↦ (mem_Ioi.1 (hD hd)).not_ge h)
      fun hd ↦ lt_irrefl _ (mem_Ioi.1 (hD hd))
  · rw [posPart_eq_self.2 h.le]

/-- A modifier that compares the amount of change with a degree `n` by `c` is the reading of
[hay-kennedy-levin-1999] whose difference values stand in `c` to `n`, when these are positive. -/
theorem describes_interval_iff {c : Comparison} {n : δ} (hc : c.interval n ⊆ Ioi 0) :
    Describes m x (c.interval n) i f ↔ c.Rel ((measureOfChange m x i f : δ) - m x i) n := by
  rw [describes_iff_of_subset_Ioi hc, Comparison.mem_interval]

-- [hay-kennedy-levin-1999]
theorem mem_preimage_Ioi_bot_iff_describes_someAmount :
    f ∈ measureOfChange m x i ⁻¹' Set.Ioi ⊥ ↔ Describes m x someAmount i f := by
  rw [preimage_measureOfChange_Ioi_bot, Set.mem_preimage, Set.mem_Ioi, describes_iff_sub_mem,
    someAmount, Comparison.mem_interval, Comparison.rel_gt, sub_pos]

-- (32), (33)
theorem le_coe_measureOfChange_sub_iff {n : δ} (hn : 0 < n) :
    n ≤ (measureOfChange m x i f : δ) - m x i ↔ Describes m x (Comparison.ge.interval n) i f :=
  (describes_interval_iff (c := .ge) (Ici_subset_Ioi.2 hn)).symm

-- [hay-kennedy-levin-1999]
theorem describes_measurePhrase_iff {n : δ} (hn : 0 < n) :
    Describes m x (measurePhrase n) i f ↔ (measureOfChange m x i f : δ) - m x i = n :=
  describes_interval_iff (c := .eq) (singleton_subset_iff.2 hn)

-- [hay-kennedy-levin-1999]
theorem le_coe_measureOfChange_sub_of_describes_measurePhrase {n : δ} (hn : 0 < n)
    (h : Describes m x (measurePhrase n) i f) : n ≤ (measureOfChange m x i f : δ) - m x i :=
  ((describes_measurePhrase_iff hn).1 h).ge

-- (34a) [hay-kennedy-levin-1999]
theorem coe_measureOfChange_eq_iff_describes_completely {top : δ} (h : m x i < top) :
    (measureOfChange m x i f : δ) = top ↔ Describes m x (completely top (m x i)) i f := by
  rw [completely, describes_measurePhrase_iff (sub_pos.2 h), sub_left_inj]

-- (34b) [hay-kennedy-levin-1999]
theorem mem_preimage_Ioi_bot_and_le_iff_describes_slightly (s : Ici (m x i)) :
    f ∈ measureOfChange m x i ⁻¹' Set.Ioi ⊥ ∧ measureOfChange m x i f ≤ s ↔
      Describes m x (slightly ((s : δ) - m x i)) i f := by
  rw [slightly, describes_iff_of_subset_Ioi (D := Comparison.le.interval _ ∩ someAmount)
    inter_subset_right, mem_inter_iff, Comparison.mem_interval, Comparison.rel_le,
    sub_le_sub_iff_right, Subtype.coe_le_coe, someAmount, Comparison.mem_interval,
    Comparison.rel_gt, sub_pos, and_comm]
  rfl

end Modifiers

/-! ### The English degree achievements -/

theorem defaultVendlerClass_eq {α T : Type*} (d : ScalarDimension) (m : α → T → d.Scale)
    (x : α) (i : T) :
    d.defaultVendlerClass =
      if (Boundedness.ofOrder (Ici (m x i))).defaultStandard = .maxEndpoint then .accomplishment
      else .activity := by
  simp only [Boundedness.ofOrder_Ici, Boundedness.ofOrder_degreeShape]
  rfl

/-- `daVerbs` lists the fragment's degree achievements. -/
def daVerbs : List Verb :=
  [English.Verbs.bend.toVerb, English.Verbs.boil.toVerb,
   English.Verbs.rust.toVerb, English.Verbs.increase.toVerb,
   English.Verbs.clean.toVerb, English.Verbs.dry.toVerb, English.Verbs.straighten.toVerb,
   English.Verbs.flatten.toVerb, English.Verbs.open_.toVerb,
   English.Verbs.lengthen.toVerb, English.Verbs.widen.toVerb,
   English.Verbs.cool.toVerb, English.Verbs.warm.toVerb]

theorem da_vendler_classes_agree :
    ∀ v ∈ daVerbs, v.vendlerClass = v.changeScale.map (·.defaultVendlerClass) := by
  decide

/-- The adjective–verb pairs of the fragment are *clean*, *dry*, *straight*, *flat* and *open*
with closed scales, and *long*, *wide*, *cool* and *warm* with open ones. -/
def pairs : List (GradableAdjective × Verb) :=
  [(English.Adjectives.clean, English.Verbs.clean.toVerb),
   (English.Adjectives.dry, English.Verbs.dry.toVerb),
   (English.Adjectives.straight, English.Verbs.straighten.toVerb),
   (English.Adjectives.flat, English.Verbs.flatten.toVerb),
   (English.Adjectives.open_, English.Verbs.open_.toVerb),
   (English.Adjectives.long, English.Verbs.lengthen.toVerb),
   (English.Adjectives.wide, English.Verbs.widen.toVerb),
   (English.Adjectives.cool, English.Verbs.cool.toVerb),
   (English.Adjectives.warm, English.Verbs.warm.toVerb)]

theorem adjective_verb_scales :
    ∀ p ∈ pairs, p.2.changeScale = some p.1.boundedness := by
  decide

-- (1), (6)
theorem inX_iff_hasMax (b : Boundedness) :
    (inXPrediction b.defaultVendlerClass = .accept ↔ b.HasMax) ∧
      (forXPrediction b.defaultVendlerClass = .accept ↔ ¬ b.HasMax) := by
  cases b <;> decide

theorem diagnostics :
    ∀ v ∈ daVerbs, ∃ b ∈ v.changeScale,
      (v.vendlerClass.map inXPrediction = some .accept ↔ b.HasMax) ∧
        (v.vendlerClass.map forXPrediction = some .accept ↔ ¬ b.HasMax) := by
  decide

end KennedyLevin2008
