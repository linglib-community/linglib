module

public import Linglib.Semantics.Homogeneity.Plural
public import Linglib.Semantics.Plurality.Algebra
public import Linglib.Data.Examples.BarLev2025

/-!
# Bar-Lev (2025): Homogeneity, underspecification, and ambiguity in plural predication

Plural predication is homogeneous: if only half of the four kids laughed, neither *the four kids
laughed* nor its negation can be truthfully uttered. Bar-Lev traces homogeneity to pluralization by
a trivalent version of Link's star operator, which makes a plural predicate true of a sum of
pluralities that satisfy it and false of a plurality no part of which does. Relativized to a cover
of the parts that matter in the context, the operator yields three meaning types, his Table 1. A
cover by all the parts gives an underspecified reading with total homogeneity, as with *lift the
table*. A cover by the atoms gives a distributive reading with homogeneity over the atoms, and a
cover by the plurality itself a collective reading with no homogeneity, as with *weigh exactly
250 lbs*.

The truth and falsity conditions of the trivalent star are the two ends of the readings of the
plural predication (`sUnion_readings_coverStar`), which is how the paper's appendix places the
account in Križ and Spector's framework. The models check the paper's contrasts. When half of the
kids lift the table together, *the four kids (didn't) lift the table* has no truth value
(`lift_half_gap`), where homogeneity over the atoms would make the negation true
(`distributive_half_false`). Lifting individually, together, or in two halves makes the sentence
true (`lift_true`), so that *the four kids didn't lift the table but they did together* is
contradictory. *These two people don't weigh 250 lbs* is true both when they weigh 125 lbs each and
when they weigh 250 lbs each, which needs the two minimal covers (`weigh_ambiguous`), since under
a cover by all the parts the positive sentence is true in both situations
(`weigh_true_of_power_cover`).

## Implementation notes

Pluralities are nonempty finite sets of individuals, sum is union, and the atoms are the
singletons. A cover is a set of pluralities with no empty one; the minimal covers of (24b) are the
atoms of `x` and `{x}` itself (`eq_atoms_of_minimal`, `eq_singleton_of_minimal`). A sentence is
true where all of its readings are and false where none is; Bar-Lev states this trivalence as a
presupposition, which the readings leave open.

## TODO

* The co-distributive two-place operator of §6.1 and upward homogeneity by overlap, §6.2.
* The context dependence of cover choice argued for in §7.

## References

* [bar-lev-2025]
* [link-1983]
* [schwarzschild-1994]
* [gajewski-2005]
* [kriz-2015]
* [kriz-spector-2021]
-/

@[expose] public section

namespace BarLev2025

open Homogeneity Mereology

/-! ### Covers and the trivalent star (§2, §4, §5) -/

section Covers

variable {α W : Type*}

private theorem not_isBot_iff {z : Finset α} : ¬ IsBot z ↔ z.Nonempty :=
  isBot_iff_eq_bot.not.trans Finset.nonempty_iff_ne_empty.symm

variable [DecidableEq α]

/-- Plural predication relative to a cover `C`, (25) and (30), holds of a plurality that is a sum
of pluralities in `C` that satisfy `P`. -/
def coverStar (C : Set (Finset α)) (P : Finset α → W → Prop) (z : Finset α) : Set W :=
  {w | AlgClosure (fun y ↦ y ∈ C ∧ P y w) z}

variable {C : Set (Finset α)} {P : Finset α → W → Prop} {x : Finset α}

/-- By the trivalent star, (12) and (31b), the plural predication is false exactly where no part
of `x` in the cover satisfies `P`. -/
theorem sUnion_readings_coverStar (hC : ∀ z ∈ C, z.Nonempty) :
    ⋃₀ readings (coverStar C P) x = {w | ∃ z ∈ C, z ⊆ x ∧ P z w} := by
  rw [sUnion_readings]
  ext w
  constructor
  · rintro ⟨z, hzx, -, hz⟩
    obtain ⟨a, ⟨haC, hPa⟩, haz⟩ := algClosure_has_base hz
    exact ⟨a, haC, haz.trans hzx, hPa⟩
  · rintro ⟨z, hzC, hzx, hP⟩
    exact ⟨z, hzx, not_isBot_iff.2 (hC z hzC), .base ⟨hzC, hP⟩⟩

/-- A minimal cover containing the atoms of `x`, (24b-i), consists of the atoms of `x`. -/
theorem eq_atoms_of_minimal (hx : x.Nonempty)
    (hmin : Minimal (fun C : Set (Finset α) ↦ AlgClosure (· ∈ C) x) C) (hat : ∀ a ∈ x, {a} ∈ C) :
    C = (fun a ↦ {a}) '' ↑x :=
  (hmin.eq_of_le ((algClosure_image_singleton _ x).2 ⟨hx, subset_rfl⟩)
    (by rintro _ ⟨a, ha, rfl⟩; exact hat a ha)).symm

theorem eq_singleton_of_minimal (hmin : Minimal (fun C : Set (Finset α) ↦ AlgClosure (· ∈ C) x) C)
    (hxC : x ∈ C) : C = {x} :=
  (hmin.eq_of_le (y := {x}) (.base (Set.mem_singleton x)) (Set.singleton_subset_iff.2 hxC)).symm

/-- Under a cover by all parts of `x` (32), the reading is `⋆P` itself, false only where no part of
`x` satisfies `P`. -/
theorem power_cover (hx : x.Nonempty) (hC : ∀ z ∈ C, z.Nonempty)
    (hpow : ∀ y ⊆ x, y.Nonempty → y ∈ C) (hP : ∀ w, ¬ P ∅ w) :
    ⋂₀ readings (coverStar C P) x = {w | AlgClosure (P · w) x} ∧
      ⋃₀ readings (coverStar C P) x = {w | ∃ z ⊆ x, z.Nonempty ∧ P z w} := by
  refine ⟨?_, ?_⟩
  · rw [sInter_readings (not_isBot_iff.2 hx)]
    ext w
    simp only [coverStar, Set.mem_ofPred_eq]
    refine ⟨fun h ↦ algClosure_mono (fun y (hy : y ∈ C ∧ P y w) ↦ hy.2) x h, fun h ↦ ?_⟩
    suffices ∀ z, AlgClosure (P · w) z → z ⊆ x → AlgClosure (fun y ↦ y ∈ C ∧ P y w) z from
      this x h subset_rfl
    intro z hz
    induction hz with
    | base hPa =>
      exact fun hax ↦ .base ⟨hpow _ hax (Finset.nonempty_iff_ne_empty.2 fun h ↦ hP w (h ▸ hPa)),
        hPa⟩
    | sum _ _ iha ihb =>
      exact fun hab ↦ .sum (iha (le_sup_left.trans hab)) (ihb (le_sup_right.trans hab))
  · rw [sUnion_readings_coverStar hC]
    ext w
    exact ⟨fun ⟨z, hzC, hzx, hPz⟩ ↦ ⟨z, hzx, hC z hzC, hPz⟩,
      fun ⟨z, hzx, hz, hPz⟩ ↦ ⟨z, hpow z hzx hz, hzx, hPz⟩⟩

/-- Under the cover by the atoms of `x` (33), the reading is distributive, false only where no atom
of `x` satisfies `P`. -/
theorem atomic_cover (hx : x.Nonempty) :
    ⋂₀ readings (coverStar ((fun a ↦ {a}) '' ↑x) P) x = {w | ∀ a ∈ x, P {a} w} ∧
      ⋃₀ readings (coverStar ((fun a ↦ {a}) '' ↑x) P) x = {w | ∃ a ∈ x, P {a} w} := by
  refine ⟨?_, ?_⟩
  · rw [sInter_readings (not_isBot_iff.2 hx)]
    ext w
    rw [coverStar, Set.mem_ofPred_eq, Set.mem_ofPred_eq, algClosure_iff_of_subset_range_singleton
      (by rintro _ ⟨⟨a, -, rfl⟩, -⟩; exact ⟨a, rfl⟩)]
    simp only [hx, true_and, Set.mem_image, Finset.mem_coe, Finset.singleton_inj, exists_eq_right]
    exact forall₂_congr fun _ ha ↦ and_iff_right ha
  · rw [sUnion_readings_coverStar (by rintro _ ⟨a, -, rfl⟩; exact Finset.singleton_nonempty a)]
    ext w
    simp

/-- Under the cover by `x` itself (34), the reading is collective, true exactly where `x` satisfies
`P`. -/
theorem singleton_cover (hx : x.Nonempty) :
    ⋂₀ readings (coverStar {x} P) x = {w | P x w} ∧
      ⋃₀ readings (coverStar {x} P) x = {w | P x w} := by
  refine ⟨?_, ?_⟩
  · rw [sInter_readings (not_isBot_iff.2 hx)]
    ext w
    simp only [coverStar, Set.mem_ofPred_eq]
    refine ⟨fun h ↦ ((algClosure_of_cum ?_).1 h).2, fun h ↦ .base ⟨rfl, h⟩⟩
    rintro a ⟨ha, -⟩ b ⟨hb, hPb⟩
    rw [Set.mem_singleton_iff] at ha hb
    subst ha hb
    simpa using hPb
  · rw [sUnion_readings_coverStar (by rintro z rfl; exact hx)]
    ext w
    simp

end Covers

/-! ### *lift the table*: underspecification and total homogeneity (§2, §3) -/

section Lift

/-- Four kids. -/
abbrev Kid := Fin 4

/-- In the situations of (3), (13) and §3, the kids lift the table individually, all together,
in two halves, or half of them together while the other half does nothing. -/
inductive Lifting
  | individually
  | together
  | halves
  | half
  deriving DecidableEq

/-- Which pluralities of kids lifted the table in each situation. -/
def lifted : Finset Kid → Lifting → Prop
  | z, .individually => z.card = 1
  | z, .together => z = Finset.univ
  | z, .halves => z = {0, 1} ∨ z = {2, 3}
  | z, .half => z = {0, 1}

instance (z : Finset Kid) (w : Lifting) : Decidable (lifted z w) := by
  cases w <;> unfold lifted <;> infer_instance

private theorem lifted_empty (w : Lifting) : ¬ lifted ∅ w := by cases w <;> decide

/-- A homogeneity presupposition on the atoms, Gajewski's distributivity operator (7), makes the
sentence false in the same situation, so that its negation would be true. -/
theorem distributive_half_false :
    Lifting.half ∉
      ⋃₀ readings (fun z ↦ {w | ∀ a ∈ z, lifted {a} w}) (Finset.univ : Finset Kid) := by
  rw [sUnion_readings]
  rintro ⟨z, -, hz, hP⟩
  obtain ⟨a, ha⟩ := not_isBot_iff.1 hz
  exact absurd (hP a ha) (by decide +revert)

variable {C : Set (Finset Kid)} (hC : ∀ z ∈ C, z.Nonempty)
  (hpow : ∀ y : Finset Kid, y.Nonempty → y ∈ C)
include hC hpow

/-- Under a cover by all parts, *the four kids lifted the table* is true if they lifted it
individually, together, or in halves (13), §3. -/
theorem lift_true :
    ∀ w ∈ [Lifting.individually, .together, .halves],
      w ∈ ⋂₀ readings (coverStar C lifted) (Finset.univ : Finset Kid) := by
  rw [(power_cover Finset.univ_nonempty hC (fun y _ hy ↦ hpow y hy) lifted_empty).1]
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq]
  rintro w (rfl | rfl | rfl)
  · rw [algClosure_iff_of_subset_range_singleton (P := (lifted · .individually))
      fun z hz ↦ (Finset.card_eq_one.1 hz).imp fun _ h ↦ h.symm]
    simp [lifted]
  · exact .base rfl
  · exact (by decide : ({0, 1} ⊔ {2, 3} : Finset Kid) = Finset.univ) ▸
      .sum (.base (.inl rfl)) (.base (.inr rfl))

/-- When half of the kids lift the table together and the rest do nothing (3), the sentence is
neither true nor false. -/
theorem lift_half_gap :
    Lifting.half ∉ ⋂₀ readings (coverStar C lifted) (Finset.univ : Finset Kid) ∧
      Lifting.half ∈ ⋃₀ readings (coverStar C lifted) (Finset.univ : Finset Kid) := by
  obtain ⟨htrue, hfalse⟩ := power_cover Finset.univ_nonempty hC (fun y _ hy ↦ hpow y hy)
    lifted_empty
  rw [htrue, hfalse]
  refine ⟨fun h ↦ ?_, ⟨{0, 1}, Finset.subset_univ _, by decide, rfl⟩⟩
  have hcum : CUM (lifted · .half) := by
    rintro a rfl b rfl
    exact sup_idem _
  exact absurd ((algClosure_of_cum hcum).1 h) (by decide)

end Lift

/-! ### *weigh exactly 250 lbs*: ambiguity (§3) -/

section Weigh

/-- The two people of (17) weigh 125 lbs each or 250 lbs each. -/
inductive Weighing
  | each125
  | each250
  deriving DecidableEq

/-- Which pluralities of the two people weigh exactly 250 lbs. -/
def weighs250 : Finset (Fin 2) → Weighing → Prop
  | z, .each125 => z = Finset.univ
  | z, .each250 => z.card = 1

instance (z : Finset (Fin 2)) (w : Weighing) : Decidable (weighs250 z w) := by
  cases w <;> unfold weighs250 <;> infer_instance

/-- Under a cover by all parts, *these two people weigh 250 lbs* is true in both situations, so its
negation (17) is true in neither. -/
theorem weigh_true_of_power_cover {C : Set (Finset (Fin 2))} (hC : ∀ z ∈ C, z.Nonempty)
    (hpow : ∀ y : Finset (Fin 2), y.Nonempty → y ∈ C) (w : Weighing) :
    w ∈ ⋂₀ readings (coverStar C weighs250) (Finset.univ : Finset (Fin 2)) := by
  rw [(power_cover Finset.univ_nonempty hC (fun y _ hy ↦ hpow y hy)
    (by intro w; cases w <;> decide)).1]
  cases w
  · exact .base rfl
  · exact (by decide : ({0} ⊔ {1} : Finset (Fin 2)) = Finset.univ) ▸ .sum (.base rfl) (.base rfl)

/-- Under the minimal covers by the atoms and by the pair, (17) is true in both situations. -/
theorem weigh_ambiguous :
    Weighing.each125 ∉ ⋃₀ readings (coverStar ((fun a ↦ {a}) '' ↑(Finset.univ : Finset (Fin 2)))
      weighs250) Finset.univ ∧
    Weighing.each250 ∉
      ⋃₀ readings (coverStar {Finset.univ} weighs250) (Finset.univ : Finset (Fin 2)) := by
  rw [(atomic_cover Finset.univ_nonempty).2, (singleton_cover Finset.univ_nonempty).2]
  decide

end Weigh

/-! ### The paper's judgments -/

section Judgments

variable {C : Set (Finset Kid)} (hC : ∀ z ∈ C, z.Nonempty)
  (hpow : ∀ y : Finset Kid, y.Nonempty → y ∈ C)
include hC hpow

/-- The model reproduces the judgments of (3) on (3a) and its negation (3b). -/
theorem judgments_lift_the_table :
    (Examples.ex_3a.readings.lookup "true if half of the kids lifted the table together and the \
        other half did nothing" = some .acceptable ↔
      Lifting.half ∈ ⋂₀ readings (coverStar C lifted) (Finset.univ : Finset Kid)) ∧
    (Examples.ex_3b.readings.lookup "true if half of the kids lifted the table together and the \
        other half did nothing" = some .acceptable ↔
      Lifting.half ∉ ⋃₀ readings (coverStar C lifted) (Finset.univ : Finset Kid)) ∧
    (Examples.ex_3a.readings.lookup "true if half of the kids lifted the table together and the \
        other half did too" = some .acceptable ↔
      Lifting.halves ∈ ⋂₀ readings (coverStar C lifted) (Finset.univ : Finset Kid)) :=
  ⟨iff_of_false (by decide) (lift_half_gap hC hpow).1,
    iff_of_false (by decide) fun h ↦ h (lift_half_gap hC hpow).2,
    iff_of_true (by decide) (lift_true hC hpow _ (by simp))⟩

/-- *The four kids didn't lift the table but they did together*, (13), is contradictory: lifting
the table together makes the negated sentence false. -/
theorem judgments_13 :
    (Examples.ex_13_together.judgment = .acceptable ↔
      Lifting.together ∉ ⋃₀ readings (coverStar C lifted) (Finset.univ : Finset Kid)) ∧
    (Examples.ex_13_individually.judgment = .acceptable ↔
      Lifting.individually ∉ ⋃₀ readings (coverStar C lifted) (Finset.univ : Finset Kid)) := by
  have hne : ∀ w, w ∈ ⋂₀ readings (coverStar C lifted) (Finset.univ : Finset Kid) →
      w ∈ ⋃₀ readings (coverStar C lifted) Finset.univ := fun w h ↦
    ⟨_, ⟨⊥, trivial, rfl⟩, h _ ⟨⊥, trivial, rfl⟩⟩
  exact ⟨iff_of_false (by decide) fun h ↦ h (hne _ (lift_true hC hpow _ (by simp))),
    iff_of_false (by decide) fun h ↦ h (hne _ (lift_true hC hpow _ (by simp)))⟩

end Judgments

/-- Both versions of (17), *these two people don't weigh 250 lbs but they do together
(individually)*, are consistent. -/
theorem judgments_17 :
    (Examples.ex_17_together.judgment = .acceptable ↔
      Weighing.each125 ∉ ⋃₀ readings (coverStar ((fun a ↦ {a}) '' ↑(Finset.univ : Finset (Fin 2)))
        weighs250) Finset.univ ∧ weighs250 Finset.univ .each125) ∧
    (Examples.ex_17_individually.judgment = .acceptable ↔
      Weighing.each250 ∉ ⋃₀ readings (coverStar {Finset.univ} weighs250) Finset.univ ∧
        ∀ a, weighs250 {a} .each250) :=
  ⟨iff_of_true (by decide) ⟨weigh_ambiguous.1, rfl⟩,
    iff_of_true (by decide) ⟨weigh_ambiguous.2, fun _ ↦ Finset.card_singleton _⟩⟩

end BarLev2025
