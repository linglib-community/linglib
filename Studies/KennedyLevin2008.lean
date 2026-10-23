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
  maximum standards is `Degree.MinStandardPos` and `Degree.MaxStandardPos`, as for adjectives.
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

/-- Interpretive Economy admits the minimum standard on the scale of a measure of change, the
maximum exactly when the adjective's scale has a greatest degree, and never the contextual
standard (§7.3.3). -/
theorem admits_iff {s : PositiveStandard} :
    (Boundedness.ofOrder (Ici (m x i))).Admits s ↔
      s = .minEndpoint ∨ s = .maxEndpoint ∧ (Boundedness.ofOrder δ).HasMax := by
  rw [Boundedness.ofOrder_Ici, Boundedness.admits_withMin_iff]

/-- Without a greatest degree only the minimum standard is admitted, so *widen* has no telic
reading and does not mean *become wide* ((6)). -/
theorem admits_iff_of_noMaxOrder [NoMaxOrder δ] {s : PositiveStandard} :
    (Boundedness.ofOrder (Ici (m x i))).Admits s ↔ s = .minEndpoint := by
  simp [admits_iff]

/-- The preferred standard on the scale of a measure of change is the maximum when the
adjective's scale has one, and the minimum otherwise. -/
theorem defaultStandard_eq :
    (Boundedness.ofOrder (Ici (m x i))).defaultStandard =
      if (Boundedness.ofOrder δ).HasMax then .maxEndpoint else .minEndpoint := by
  rw [Boundedness.ofOrder_Ici, Boundedness.defaultStandard_withMin]

end MeasureOfChange

/-! ### The readings of a degree achievement (26)–(27) -/

section Readings

variable {α δ T : Type*} [LinearOrder δ] {m : α → T → δ} {x : α} {i f : T}

/-- The minimum-standard reading of a degree achievement (27) has the truth conditions of the
comparative, the argument ending the event with more of the property than it began with. -/
theorem minStandardPos_measureOfChange_iff :
    MinStandardPos (measureOfChange m x i) f ↔ m x i < m x f :=
  minStandardPos_projIci_comp_iff

variable [OrderTop δ]

/-- Unless the argument begins with the greatest degree, the maximum-standard reading of a degree
achievement (27) is the positive form of its adjective at the end of the event, so *straighten*
and *straight* share their standard (§7.3.3). -/
theorem maxStandardPos_measureOfChange_iff (h : m x i ≠ ⊤) :
    MaxStandardPos (measureOfChange m x i) f ↔ MaxStandardPos (m x) f :=
  maxStandardPos_projIci_comp_iff h

/-- Unless the argument begins with the greatest degree, the telic reading entails the atelic
one, which is why it is preferred (§7.3.3). -/
theorem minStandardPos_of_maxStandardPos (h : m x i ≠ ⊤)
    (hmax : MaxStandardPos (measureOfChange m x i) f) :
    MinStandardPos (measureOfChange m x i) f :=
  hmax.minStandardPos h.lt_top

end Readings

/-! ### Measure phrases and degree modifiers (32)–(34) -/

section Modifiers

open HayKennedyLevin1999

variable {α δ T : Type*} [AddCommGroup δ] [LinearOrder δ] [IsOrderedAddMonoid δ]
  {m : α → T → δ} {x : α} {i f : T}

/-- The amount of change, the distance of the measure of change above its derived zero, is the
positive part of the difference between the final and the initial degree: a positive value when
there is a positive difference, and zero otherwise, as the paper glosses (23). -/
theorem coe_measureOfChange_sub : (measureOfChange m x i f : δ) - m x i = (m x f - m x i)⁺ := by
  rw [measureOfChange, Function.comp_apply, coe_projIci, max_comm, sup_eq_add_posPart_sub,
    add_sub_cancel_left]

/-- On positive difference values the two accounts agree: a description of
[hay-kennedy-levin-1999] whose difference values are all positive holds exactly when the amount of
change is one of them. -/
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

/-- The minimum-standard reading is the reading of [hay-kennedy-levin-1999] with the difference
value "some amount". -/
theorem minStandardPos_measureOfChange_iff_describes_someAmount :
    MinStandardPos (measureOfChange m x i) f ↔ Describes m x someAmount i f := by
  rw [minStandardPos_measureOfChange_iff, describes_iff_sub_mem, someAmount,
    Comparison.mem_interval, Comparison.rel_gt, sub_pos]

/-- For a positive degree `n`, the amount of change is at least `n`, as a measure phrase requires
((32)–(33)), exactly when the event is described by the difference values of at least `n`. -/
theorem le_coe_measureOfChange_sub_iff {n : δ} (hn : 0 < n) :
    n ≤ (measureOfChange m x i f : δ) - m x i ↔ Describes m x (Comparison.ge.interval n) i f :=
  (describes_interval_iff (c := .ge) (Ici_subset_Ioi.2 hn)).symm

/-- The measure phrase of [hay-kennedy-levin-1999] fixes the amount of change at exactly its
degree, comparing by `Comparison.eq` where the measure phrase here compares by `Comparison.ge`. -/
theorem describes_measurePhrase_iff {n : δ} (hn : 0 < n) :
    Describes m x (measurePhrase n) i f ↔ (measureOfChange m x i f : δ) - m x i = n :=
  describes_interval_iff (c := .eq) (singleton_subset_iff.2 hn)

/-- The exact difference value that [hay-kennedy-levin-1999] give a measure phrase entails the
at-least reading. -/
theorem le_coe_measureOfChange_sub_of_describes_measurePhrase {n : δ} (hn : 0 < n)
    (h : Describes m x (measurePhrase n) i f) : n ≤ (measureOfChange m x i f : δ) - m x i :=
  ((describes_measurePhrase_iff hn).1 h).ge

/-- Against a maximal degree `top` above the initial degree, the maximum-standard reading, which
*completely* also gives ((34a)), is the reading of [hay-kennedy-levin-1999] with *completely*. -/
theorem coe_measureOfChange_eq_iff_describes_completely {top : δ} (h : m x i < top) :
    (measureOfChange m x i f : δ) = top ↔ Describes m x (completely top (m x i)) i f := by
  rw [completely, describes_measurePhrase_iff (sub_pos.2 h), sub_left_inj]

/-- *Slightly*, a positive change up to a small degree `s` ((34b)), is the reading of
[hay-kennedy-levin-1999] with *slightly*. -/
theorem minStandardPos_and_le_iff_describes_slightly (s : Ici (m x i)) :
    MinStandardPos (measureOfChange m x i) f ∧ measureOfChange m x i f ≤ s ↔
      Describes m x (slightly ((s : δ) - m x i)) i f := by
  rw [slightly, describes_iff_of_subset_Ioi (D := Comparison.le.interval _ ∩ someAmount)
    inter_subset_right, mem_inter_iff, Comparison.mem_interval, Comparison.rel_le,
    sub_le_sub_iff_right, Subtype.coe_le_coe, someAmount, Comparison.mem_interval,
    Comparison.rel_gt, sub_pos, and_comm]
  rfl

end Modifiers

/-! ### The English degree achievements -/

/-- For any measure function into a dimension's degrees, a degree achievement on the dimension
is by default an accomplishment when the preferred standard on the scale of its measure of
change is the maximum, and an activity otherwise. -/
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

/-- Every degree achievement's Vendler class is the default of its base scale. -/
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

/-- A degree achievement measures on its adjective's scale. -/
theorem adjective_verb_scales :
    ∀ p ∈ pairs, p.2.changeScale = some p.1.boundedness := by
  decide

/-- A degree achievement takes *in X* exactly when its scale is closed above, and *for X*
otherwise ((1), (6)). -/
theorem inX_iff_hasMax (b : Boundedness) :
    (inXPrediction b.defaultVendlerClass = .accept ↔ b.HasMax) ∧
      (forXPrediction b.defaultVendlerClass = .accept ↔ ¬ b.HasMax) := by
  cases b <;> decide

/-- On the fragment, *bend*, *boil*, *clean*, *dry*, *straighten*, *flatten* and *open* take
*in X*, and *rust*, *increase*, *lengthen*, *widen*, *cool* and *warm* take *for X*. -/
theorem diagnostics :
    ∀ v ∈ daVerbs, ∃ b ∈ v.changeScale,
      (v.vendlerClass.map inXPrediction = some .accept ↔ b.HasMax) ∧
        (v.vendlerClass.map forXPrediction = some .accept ↔ ¬ b.HasMax) := by
  decide

end KennedyLevin2008
