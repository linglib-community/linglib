module

public import Linglib.Data.Examples.CoppockBrochhagen2013
public import Linglib.Data.Examples.Readers
public import Linglib.Languages.English.NumeralModifiers
public import Linglib.Semantics.Focus.Inquisitive

/-!
# Coppock and Brochhagen (2013): Raising and resolving issues with scalar modifiers

The superlative modifiers *at least* and *at most* range over the answers to the question under
discussion, ranked by strength: *at least `i`* is `Focus.atLeast`, what *only `i`* presupposes,
and *at most `i`* is `Focus.atMost`, what it asserts. For the question of how many under a measure
`μ`, the two-sided answers are the fibres `μ ⁻¹' {i}` and the one-sided answers are
`μ ⁻¹' Ici i`. On either reading the number `μ w` is the strongest answer true at `w`, so
*at least `a`* is `μ ⁻¹' Ici a` and *at most `a`* is `μ ⁻¹' Iic a`, and the one-sided answers are
*at least* of the two-sided ones.

In unrestricted inquisitive semantics the modifiers raise the possibilities
`Inquisitive.Unrestricted.atLeast` and `Inquisitive.Unrestricted.atMost`. Over two-sided answers
*at least `a`* is inquisitive and not attentive, and over one-sided answers it is attentive. A
speaker who knows the number restricts *at least `a`* to one possibility on either reading, which
violates the Maxim of Interactive Sincerity, while the comparative *more than* raises one
possibility with the same union. In the model of who snores, exhaustifying *Ann snores* against
the question excludes that Bill snores, and exhaustifying the possibilities of *at least Ann
snores* does not.

## Implementation notes

* The question of a measure `μ` has its answers indexed by number, and the scale ranks the
  indices. The paper's assumption of one world for each number is surjectivity of `μ`; the truth
  conditions hold without it, and only the results that need two distinct answers assume it.
* The choice-function entries are modelled by the sets of possibilities they denote, which is what
  applying them pointwise yields.
* Exhaustification against the question is `Exhaustification.exh` applied to each possibility,
  whose printed form is `Exhaustification.exh_eq_sdiff`.

## TODO

The interaction with modals is not formalized: the authoritative and speaker-insecurity readings
of *at least* under deontic modals and the missing readings of *at most* under *may*, which the
paper derives with Hackl's *-many*.

## References

* [E. Coppock and T. Brochhagen, *Raising and resolving issues with scalar modifiers*
  (2013)][coppock-brochhagen-2013]
* [E. Coppock and D. Beaver, *Principles of the exclusive muddle* (2014)][coppock-beaver-2014]
* [I. Ciardelli, J. Groenendijk and F. Roelofsen, *Attention! 'Might' in Inquisitive Semantics*
  (2009)][ciardelli-groenendijk-roelofsen-2009]
-/

@[expose] public section

namespace CoppockBrochhagen2013

open Focus Inquisitive Exhaustification Set Function
open Inquisitive.Unrestricted hiding atLeast atMost atLeast_ge_univ atMost_ge_univ

/-! ### Truth conditions (§2.6) -/

section Measure

variable {W α : Type*} [LinearOrder α] {μ : W → α}

/-- The two-sided answers to the question of how many, by the measure `μ`. -/
abbrev twoSided (μ : W → α) (i : α) : Set W := μ ⁻¹' {i}

/-- The one-sided answers to the question of how many, by the measure `μ`. -/
abbrev oneSided (μ : W → α) (i : α) : Set W := μ ⁻¹' Ici i

omit [LinearOrder α] in
theorem twoSided_injective (hμ : Surjective μ) : Injective (twoSided μ) :=
  hμ.preimage_injective.comp singleton_injective

omit [LinearOrder α] in
theorem isAntichain_range_twoSided (hμ : Surjective μ) :
    IsAntichain (· ⊆ ·) (range (twoSided μ)) := by
  rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩ hne hle
  obtain ⟨w, rfl⟩ := hμ c
  exact hne (congrArg _ (show μ w = d from hle (rfl : μ w ∈ ({μ w} : Set α))))

theorem antitone_oneSided : Antitone (oneSided μ) :=
  fun _ _ h ↦ preimage_mono (Ici_subset_Ici.2 h)

theorem oneSided_injective (hμ : Surjective μ) : Injective (oneSided μ) :=
  hμ.preimage_injective.comp Ici_injective

theorem strictAnti_oneSided (hμ : Surjective μ) : StrictAnti (oneSided μ) :=
  antitone_oneSided.strictAnti_of_injective (oneSided_injective hμ)

/-- On either reading of the numeral, the number is the strongest true answer to the question of
how many. -/
theorem isGreatest_twoSided (w : W) : IsGreatest {i ∈ univ | w ∈ twoSided μ i} (μ w) := by
  simp [IsGreatest, upperBounds]

theorem isGreatest_oneSided (w : W) : IsGreatest {i ∈ univ | w ∈ oneSided μ i} (μ w) := by
  simp [IsGreatest, upperBounds]

-- (30)
theorem atLeast_twoSided : atLeast (· ≥ ·) univ (twoSided μ) = oneSided μ :=
  funext (atLeast_ge_of_isGreatest isGreatest_twoSided)

-- (30), one-sided
theorem atLeast_oneSided : atLeast (· ≥ ·) univ (oneSided μ) = oneSided μ :=
  funext (atLeast_ge_of_isGreatest isGreatest_oneSided)

-- (31)
theorem atMost_twoSided (a : α) : atMost (· ≥ ·) univ (twoSided μ) a = μ ⁻¹' Iic a :=
  atMost_ge_of_isGreatest isGreatest_twoSided a

-- (31), one-sided
theorem atMost_oneSided (a : α) : atMost (· ≥ ·) univ (oneSided μ) a = μ ⁻¹' Iic a :=
  atMost_ge_of_isGreatest isGreatest_oneSided a

-- (59)
theorem twoSided_ssubset_atLeast (hμ : Surjective μ) {a b : α} (hab : a < b) :
    twoSided μ a ⊂ atLeast (· ≥ ·) univ (twoSided μ) a := by
  rw [atLeast_twoSided]
  obtain ⟨w, rfl⟩ := hμ b
  exact ⟨preimage_mono (singleton_subset_iff.2 le_rfl), fun h ↦ hab.ne' (h (hab.le : μ w ∈ Ici a))⟩

end Measure

section Fragment

open scoped Denotes

variable {W : Type*} {μ : W → ℕ}

-- On the question of how many, each modifier is the language file's reading of the numeral it
-- modifies, pulled back along the count.
theorem atLeast_fragment (n : ℕ) :
    ∀ m ∈ ⟦English.NumeralModifiers.atLeast⟧,
      atLeast (· ≥ ·) univ (twoSided μ) n = μ ⁻¹' m {n} := by
  rintro m (rfl : m = _)
  rw [atLeast_twoSided, Comparison.modifier_singleton, Comparison.interval_ge]

theorem atMost_fragment (n : ℕ) :
    ∀ m ∈ ⟦English.NumeralModifiers.atMost⟧,
      atMost (· ≥ ·) univ (twoSided μ) n = μ ⁻¹' m {n} := by
  rintro m (rfl : m = _)
  rw [atMost_twoSided, Comparison.modifier_singleton, Comparison.interval_le]

end Fragment

/-! ### The inquisitive entries (§3.3) -/

section Inquisitive

variable {W α : Type*} [LinearOrder α] {μ : W → α} {a b : α}

-- (53)
theorem range_choice_apply {T : Set (Set W)} (hT : T.Nonempty) :
    range (fun f : {f : Set (Set W) → Set W // ∀ U : Set (Set W), U.Nonempty → f U ∈ U} ↦
      f.val T) = T := by
  classical
  ext p
  refine ⟨fun ⟨f, hf⟩ ↦ hf ▸ f.property T hT, fun hp ↦ ?_⟩
  refine ⟨⟨fun U ↦ if p ∈ U then p else if hU : U.Nonempty then hU.some else ∅, fun U hU ↦ ?_⟩, ?_⟩
  · by_cases h : p ∈ U
    · simp [h]
    · simpa [h, hU] using hU.some_mem
  · simp [hp]

-- (58)
theorem isAttentive_atLeast_oneSided (hμ : Surjective μ) (hab : a < b) :
    IsAttentive (Unrestricted.atLeast (· ≥ ·) univ (oneSided μ) a) :=
  isAttentive_atLeast_ge hab.le (strictAnti_oneSided hμ hab)

-- (59b)
theorem not_isAttentive_atLeast_twoSided (hμ : Surjective μ) (a : α) :
    ¬ IsAttentive (Unrestricted.atLeast (· ≥ ·) univ (twoSided μ) a) :=
  not_isAttentive_atLeast (isAntichain_range_twoSided hμ)

-- (59b)
theorem isInquisitive_atLeast_twoSided (hμ : Surjective μ) (hab : a < b) :
    IsInquisitive (Unrestricted.atLeast (· ≥ ·) univ (twoSided μ) a) := by
  rw [Unrestricted.atLeast_ge_univ,
    isInquisitive_iff_nontrivial ((isAntichain_range_twoSided hμ).subset (image_subset_range _ _))]
  exact (nontrivial_of_lt self_mem_Ici hab.le hab).image (twoSided_injective hμ)

-- (63)
theorem possibilities_atMost_twoSided (a : α) :
    Unrestricted.atMost (· ≥ ·) univ (twoSided μ) a = twoSided μ '' Iic a := by
  rw [atMost_of_pairwiseDisjoint (pairwiseDisjoint_fiber μ univ)]; congr 1; ext; simp

-- (64)
theorem possibilities_atMost_oneSided (a : α) :
    Unrestricted.atMost (· ≥ ·) univ (oneSided μ) a = (fun i ↦ μ ⁻¹' Icc i a) '' Iic a := by
  rw [Unrestricted.atMost_ge_univ, atMost_oneSided, image_image]
  simp only [oneSided, ← preimage_inter, Ici_inter_Iic]

-- (64)
theorem possibilities_atMost_id (a : ℕ) :
    Unrestricted.atMost (· ≥ ·) univ (oneSided (id : ℕ → ℕ)) a = (Icc · a) '' Iic a :=
  possibilities_atMost_oneSided a

-- (73)
theorem sUnion_atLeast_succ [SuccOrder α] [NoMaxOrder α] (a : α) :
    ⋃₀ Unrestricted.atLeast (· ≥ ·) univ (twoSided μ) (Order.succ a) = μ ⁻¹' Ioi a := by
  rw [sUnion_atLeast, atLeast_twoSided]
  exact congrArg _ (Order.Ici_succ a)

end Inquisitive

/-! ### Ignorance (§3.4.1) -/

section Ignorance

variable {ι W α : Type*} {S : ι → ι → Prop} {C : Set ι} {μ : W → α} {b : α} {k : Set W}

theorem subset_or_disjoint_preimage (hk : k ⊆ μ ⁻¹' {b}) (s : Set α) :
    k ⊆ μ ⁻¹' s ∨ Disjoint k (μ ⁻¹' s) := by
  by_cases hb : b ∈ s
  · exact .inl fun w hw ↦ by rw [mem_preimage, show μ w = b from hk hw]; exact hb
  · exact .inr (disjoint_left.2 fun w hw hws ↦ hb (by rw [← show μ w = b from hk hw]; exact hws))

/-- A speaker who knows the number restricts *at least*, over answers about the number, to at
most one possibility. -/
theorem subsingleton_restrict_atLeast_of_subset_fiber (s : ι → Set α) (i : ι)
    (hk : k ⊆ μ ⁻¹' {b}) :
    (restrict (Unrestricted.atLeast S C (fun j ↦ μ ⁻¹' s j) i) k).Subsingleton :=
  subsingleton_restrict_of_subset_or_disjoint <| by
    rintro _ ⟨j, -, rfl⟩
    exact subset_or_disjoint_preimage hk (s j)

variable [LinearOrder α] {a c : α}

/-- (70a): a speaker who knows how many cannot sincerely say *at least `a`* over two-sided
answers. -/
theorem not_interactiveSincerity_atLeast_twoSided (hμ : Surjective μ) (hac : a < c)
    (hk : k ⊆ twoSided μ b) :
    ¬ InteractiveSincerity (Unrestricted.atLeast (· ≥ ·) univ (twoSided μ) a) k :=
  not_interactiveSincerity
    (nontrivial_iff_isInquisitive_or_isAttentive.2 (.inl (isInquisitive_atLeast_twoSided hμ hac)))
    (subsingleton_restrict_atLeast_of_subset_fiber (fun i ↦ {i}) a hk)

-- (70a), with one-sided answers
theorem not_interactiveSincerity_atLeast_oneSided (hμ : Surjective μ) (hac : a < c)
    (hk : k ⊆ twoSided μ b) :
    ¬ InteractiveSincerity (Unrestricted.atLeast (· ≥ ·) univ (oneSided μ) a) k :=
  not_interactiveSincerity
    (nontrivial_iff_isInquisitive_or_isAttentive.2 (.inr (isAttentive_atLeast_oneSided hμ hac)))
    (subsingleton_restrict_atLeast_of_subset_fiber Ici a hk)

end Ignorance

/-! ### The judgments -/

section Judgments

variable {W : Type*}

/-- The possibilities a modified numeral raises on the question of how many: *at least `n`* each
answer from `n` up, and *more than `n`* the one possibility that the number exceeds `n` (72). -/
def Examples.Modifier.raised (μ : W → ℕ) : Examples.Modifier → ℕ → Set (Set W)
  | .atLeast, n => Unrestricted.atLeast (· ≥ ·) univ (twoSided μ) n
  | .moreThan, n => {μ ⁻¹' Ioi n}

/-- Spoken by someone who knows the number, each sentence of (70) is felicitous exactly when it
satisfies the Maxim of Interactive Sincerity. -/
theorem judgment_rows {μ : W → ℕ} (hμ : Surjective μ) {b : ℕ} {k : Set W}
    (hk : k ⊆ twoSided μ b) :
    ∀ e ∈ Examples.all, ∃ m ∈ Examples.modifier e, ∃ n ∈ e.nat? "numeral",
      (e.JudgedFelicitous ↔ InteractiveSincerity (m.raised μ n) k) := by
  intro e he
  rcases List.mem_pair.1 he with rfl | rfl
  · exact ⟨.atLeast, by decide, 5, by decide, iff_of_false (by decide)
      (not_interactiveSincerity_atLeast_twoSided hμ (Nat.lt_succ_self 5) hk)⟩
  · exact ⟨.moreThan, by decide, 4, by decide, iff_of_true (by decide)
      (.of_subsingleton subsingleton_singleton k)⟩

end Judgments

/-! ### Who snores (§3.3, §3.4) -/

section WhoSnores

/-- The worlds of the four-world model of Figures 2 to 4, by whether Ann and whether Bill
snores. -/
abbrev World := Bool × Bool

/-- *Ann snores.* -/
def ann : Set World := {w | w.fst}

/-- *Bill snores.* -/
def bill : Set World := {w | w.snd}

/-- The question who snores, with answers *Ann*, *Bill* and *Ann and Bill* (Figure 3). -/
def whoSnores : Set (Set World) := {ann, bill, ann ∩ bill}

theorem not_ann_subset_bill : ¬ ann ⊆ bill :=
  fun h ↦ by simpa [ann, bill] using h (show (true, false) ∈ ann from rfl)

theorem not_bill_subset_ann : ¬ bill ⊆ ann :=
  fun h ↦ by simpa [ann, bill] using h (show (false, true) ∈ bill from rfl)

-- (58), Figure 2(b)
theorem atLeast_ann : Unrestricted.atLeast (· ⊆ ·) whoSnores id ann = {ann, ann ∩ bill} := by
  rw [Unrestricted.atLeast, image_id]
  ext p
  constructor
  · rintro ⟨rfl | rfl | rfl, h⟩
    · simp
    · exact absurd h not_bill_subset_ann
    · simp
  · rintro (rfl | rfl)
    · exact ⟨by simp [whoSnores], subset_rfl⟩
    · exact ⟨by simp [whoSnores], inter_subset_left⟩

-- Figure 2(b)
theorem isAttentive_atLeast_ann :
    IsAttentive (Unrestricted.atLeast (· ⊆ ·) whoSnores id ann) := by
  rw [atLeast_ann]
  exact isAttentive_of_ssubset (p := ann ∩ bill) (q := ann) (by simp) (by simp)
    ⟨inter_subset_left, fun h ↦ not_ann_subset_bill (h.trans inter_subset_right)⟩

-- (77), Figure 4(a)
theorem exh_whoSnores_ann : exh whoSnores ann = {(true, false)} := by
  rw [whoSnores, exh_insert_of_subset subset_rfl, exh_insert_of_not_subset not_ann_subset_bill,
    exh_singleton_of_not_subset fun h ↦ not_ann_subset_bill (h.trans inter_subset_right)]
  ext ⟨a, b⟩
  cases a <;> cases b <;> simp [ann, bill]

theorem exh_whoSnores_inter : exh whoSnores (ann ∩ bill) = {(true, true)} := by
  rw [exh_eq_self (by
    rintro q (rfl | rfl | rfl)
    exacts [inter_subset_left, inter_subset_right, subset_rfl])]
  ext ⟨a, b⟩
  cases a <;> cases b <;> simp [ann, bill]

-- (69)
theorem not_interactiveSincerity_ann :
    ¬ InteractiveSincerity (Unrestricted.atLeast (· ⊆ ·) whoSnores id ann) {(true, false)} :=
  not_interactiveSincerity_of_only
    (fun w hw ↦ Trivalent.mem_posExt.1 <| by
      rw [posExt_only_subset (by simp [whoSnores]), exh_whoSnores_ann]; exact hw)
    (nontrivial_iff_isInquisitive_or_isAttentive.2 (.inr isAttentive_atLeast_ann))

/-- (77), Figure 4(b): exhaustifying the possibilities of *at least Ann snores* keeps the world
where Bill snores too. -/
theorem exh_whoSnores_atLeast_ann :
    exh whoSnores '' Unrestricted.atLeast (· ⊆ ·) whoSnores id ann =
      {{(true, false)}, {(true, true)}} := by
  rw [atLeast_ann, image_pair, exh_whoSnores_ann, exh_whoSnores_inter]

end WhoSnores

end CoppockBrochhagen2013
