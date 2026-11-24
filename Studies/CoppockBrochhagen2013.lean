module

public import Linglib.Data.Examples.CoppockBrochhagen2013
public import Linglib.Data.Examples.Readers
public import Linglib.Languages.English.NumeralModifiers
public import Linglib.Semantics.Focus.Particles
public import Linglib.Semantics.Questions.Hamblin.Unrestricted

/-!
# Coppock and Brochhagen (2013): Raising and resolving issues with scalar modifiers

The superlative modifiers *at least* and *at most* range over the answers to the question under
discussion, ranked by strength. *At least `i`* holds where some true answer is at least as strong
as `i`, which is `Focus.atLeast`, and *at most `i`* holds where no true answer is stronger, which
is `Focus.atMost`; these are what *only `i`* presupposes and asserts. For answers indexed by a
preorder, with contents `P`, *at least `a`* is `⋃ i ≥ a, P i`, and it leaves the answers unchanged
just in case stronger answers entail weaker ones. For the question of how many under a measure
`μ`, the two-sided answers are the fibres `μ ⁻¹' {i}` and the one-sided answers are
`μ ⁻¹' Ici i`, which are *at least* of the two-sided ones. On either reading *at least `a`* is
`μ ⁻¹' Ici a` and *at most `a`* is `μ ⁻¹' Iic a`.

In unrestricted inquisitive semantics *at least `i`* raises each answer at least as strong as `i`
as a possibility, and *at most `i`* raises each answer at most as strong, cut down to the worlds
where no stronger answer is true; on disjoint answers the cut does nothing. The unions of these
possibilities are the classical meanings. The Maxim of Interactive Sincerity asks that a
proposition with several possibilities keep several when restricted to the speaker's information.
A speaker who knows *only `i`*, or who knows the number, restricts *at least* to one possibility
and so violates the maxim, while the comparative *more than* raises one possibility with the same
union. Exhaustifying each possibility that *at least `p`* raises against the question leaves
their union equal to `p` whenever each world of `p` has a strongest true answer.

## Implementation notes

* The question of a measure `μ` has its answers indexed by number, and the scale ranks the
  indices. The paper's assumption of one world for each number is surjectivity of `μ`; the truth
  conditions hold without it, and only the results that need two distinct answers assume it.
* *At least* and *at most* apply to one prejacent answer. The paper's entry for *at least* takes
  an inquisitive prejacent and collects the answers at least as strong as one of its
  possibilities.
* The choice-function entries are modelled by the sets of possibilities they denote, which is what
  applying them pointwise yields.
* The informational content of inquisitive *at most* is `Focus.atMost` within the common ground of
  the state, the union of its answers.
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

open Focus Inquisitive.Unrestricted Exhaustification Set Function

/-! ### Truth conditions (§2.6) -/

section Indexed

variable {W α : Type*} [Preorder α] {P : α → Set W}

-- (30)
theorem atLeast_ge (a : α) : atLeast (· ≥ ·) univ P a = ⋃ i ∈ Ici a, P i := by
  ext w
  simp only [mem_atLeast, mem_univ, true_and, mem_iUnion, mem_Ici, exists_prop]
  exact ⟨fun ⟨i, hw, hi⟩ ↦ ⟨i, hi, hw⟩, fun ⟨i, hi, hw⟩ ↦ ⟨i, hw, hi⟩⟩

-- (31)
theorem atMost_ge (a : α) : atMost (· ≥ ·) univ P a = (⋃ i ∈ (Iic a)ᶜ, P i)ᶜ := by
  ext w
  simp only [mem_atMost, mem_univ, true_implies, mem_compl_iff, mem_iUnion, mem_Iic,
    exists_prop, not_exists, not_and]
  exact ⟨fun h i hi hw ↦ hi (h i hw), fun h i hw ↦ not_not.1 fun hi ↦ h i hi hw⟩

theorem subset_atLeast_ge (a : α) : P a ⊆ atLeast (· ≥ ·) univ P a :=
  fun _ hw ↦ ⟨a, mem_univ a, hw, le_rfl⟩

theorem antitone_atLeast_ge : Antitone (atLeast (· ≥ ·) univ P) :=
  fun _ _ hab _ ⟨j, hj, hw, hjb⟩ ↦ ⟨j, hj, hw, hab.trans hjb⟩

/-- *At least* leaves every answer unchanged just in case stronger answers entail weaker ones. -/
theorem atLeast_ge_eq_self_iff : atLeast (· ≥ ·) univ P = P ↔ Antitone P :=
  ⟨fun h ↦ by rw [← h]; exact antitone_atLeast_ge, fun h ↦ funext fun a ↦
    (subset_atLeast_ge a).antisymm' fun _ ⟨_, _, hw, hj⟩ ↦ h hj hw⟩

theorem atLeast_ge_atLeast_ge :
    atLeast (· ≥ ·) univ (atLeast (· ≥ ·) univ P) = atLeast (· ≥ ·) univ P :=
  atLeast_ge_eq_self_iff.2 antitone_atLeast_ge

end Indexed

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

theorem atLeast_twoSided : atLeast (· ≥ ·) univ (twoSided μ) = oneSided μ := by
  funext a
  rw [atLeast_ge]
  simp only [twoSided, ← preimage_iUnion₂, biUnion_of_singleton]

theorem atLeast_oneSided : atLeast (· ≥ ·) univ (oneSided μ) = oneSided μ :=
  atLeast_ge_eq_self_iff.2 antitone_oneSided

theorem atMost_twoSided (a : α) : atMost (· ≥ ·) univ (twoSided μ) a = μ ⁻¹' Iic a := by
  rw [atMost_ge]
  simp only [twoSided, ← preimage_iUnion₂, biUnion_of_singleton, ← preimage_compl, compl_compl]

theorem atMost_oneSided (a : α) : atMost (· ≥ ·) univ (oneSided μ) a = μ ⁻¹' Iic a := by
  rw [atMost_ge, compl_Iic]
  simp only [oneSided, ← preimage_iUnion₂, ← preimage_compl]
  congr 1
  ext x
  simp only [mem_compl_iff, mem_iUnion₂, mem_Ici, mem_Ioi, exists_prop, not_exists, not_and,
    mem_Iic]
  exact ⟨fun h ↦ not_lt.1 fun hax ↦ h x hax le_rfl, fun h i hai hix ↦ (hai.trans_le hix).not_ge h⟩

-- (32)
theorem monotone_atMost_twoSided : Monotone (atMost (· ≥ ·) univ (twoSided μ)) := fun a b hab ↦ by
  rw [atMost_twoSided, atMost_twoSided]
  exact preimage_mono (Iic_subset_Iic.2 hab)

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
      Focus.atLeast (· ≥ ·) univ (twoSided μ) n = μ ⁻¹' m {n} := by
  rintro m (rfl : m = _)
  rw [atLeast_twoSided, Comparison.modifier_singleton, Comparison.interval_ge]

theorem atMost_fragment (n : ℕ) :
    ∀ m ∈ ⟦English.NumeralModifiers.atMost⟧,
      Focus.atMost (· ≥ ·) univ (twoSided μ) n = μ ⁻¹' m {n} := by
  rintro m (rfl : m = _)
  rw [atMost_twoSided, Comparison.modifier_singleton, Comparison.interval_le]

end Fragment

/-! ### The inquisitive entries (§3.3) -/

section Inquisitive

variable {ι W : Type*} (S : ι → ι → Prop) (C : Set ι) (P : ι → Set W) (i : ι)

/-- (52): *at least `i`* raises every answer at least as strong as `i`. -/
def atLeastInq : Set (Set W) := P '' {j ∈ C | S j i}

/-- (60): *at most `i`* raises every answer at most as strong as `i`, cut down to the worlds
where no stronger answer is true. -/
def atMostInq : Set (Set W) := (· ∩ atMost S C P i) '' (P '' {j ∈ C | S i j})

-- §3.7
theorem sUnion_atLeastInq : ⋃₀ atLeastInq S C P i = atLeast S C P i := by
  ext w
  simp only [atLeastInq, sUnion_image, mem_iUnion, mem_ofPred_eq, exists_prop, mem_atLeast]
  exact ⟨fun ⟨j, ⟨hj, hs⟩, hw⟩ ↦ ⟨j, hj, hw, hs⟩, fun ⟨j, hj, hw, hs⟩ ↦ ⟨j, ⟨hj, hs⟩, hw⟩⟩

-- §3.7
theorem sUnion_atMostInq : ⋃₀ atMostInq S C P i = atMost S C P i ∩ ⋃ j ∈ C, P j := by
  ext w
  simp only [atMostInq, image_image, sUnion_image, mem_iUnion, mem_ofPred_eq, mem_inter_iff,
    exists_prop]
  constructor
  · rintro ⟨j, ⟨hj, _⟩, hw, hmax⟩
    exact ⟨hmax, j, hj, hw⟩
  · rintro ⟨hmax, j, hj, hw⟩
    exact ⟨j, ⟨hj, hmax j hj hw⟩, hw, hmax⟩

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

variable {S C P i}

-- When no answer is nested in another, *at least* is not attentive (§3.3).
theorem not_isAttentive_atLeastInq (h : IsAntichain (· ⊆ ·) (range P)) :
    ¬ IsAttentive (atLeastInq S C P i) :=
  not_isAttentive_iff.2 (h.subset (image_subset_range _ _))

-- On disjoint answers the cut of *at most* does nothing (§3.3).
theorem atMostInq_of_pairwiseDisjoint (h : C.PairwiseDisjoint P) :
    atMostInq S C P i = P '' {j ∈ C | S i j} := by
  rw [atMostInq, image_image]
  refine image_congr fun j ⟨hj, hij⟩ ↦ inter_eq_left.2 fun w hw j' hj' hw' ↦ ?_
  rwa [h.elim_set hj' hj w hw' hw]

section Indexed

variable {α : Type*} [Preorder α] {P : α → Set W} {a b : α}

-- (58)
theorem atLeastInq_ge (a : α) : atLeastInq (· ≥ ·) univ P a = P '' Ici a := by
  rw [atLeastInq]; congr 1; ext; simp

-- (63), (64)
theorem atMostInq_ge (a : α) :
    atMostInq (· ≥ ·) univ P a = (· ∩ atMost (· ≥ ·) univ P a) '' (P '' Iic a) := by
  rw [atMostInq]; congr 2; ext; simp

theorem isAttentive_atLeastInq_ge (hab : a ≤ b) (h : P b ⊂ P a) :
    IsAttentive (atLeastInq (· ≥ ·) univ P a) := by
  rw [atLeastInq_ge]
  exact isAttentive_of_ssubset (mem_image_of_mem _ hab) (mem_image_of_mem _ self_mem_Ici) h

end Indexed

section Measure

variable {α : Type*} [LinearOrder α] {μ : W → α} {a b : α}

-- (58)
theorem isAttentive_atLeastInq_oneSided (hμ : Surjective μ) (hab : a < b) :
    IsAttentive (atLeastInq (· ≥ ·) univ (oneSided μ) a) :=
  isAttentive_atLeastInq_ge hab.le (strictAnti_oneSided hμ hab)

-- (59b)
theorem not_isAttentive_atLeastInq_twoSided (hμ : Surjective μ) (a : α) :
    ¬ IsAttentive (atLeastInq (· ≥ ·) univ (twoSided μ) a) :=
  not_isAttentive_atLeastInq (isAntichain_range_twoSided hμ)

-- (59b)
theorem isInquisitive_atLeastInq_twoSided (hμ : Surjective μ) (hab : a < b) :
    IsInquisitive (atLeastInq (· ≥ ·) univ (twoSided μ) a) := by
  rw [atLeastInq_ge,
    isInquisitive_iff_nontrivial ((isAntichain_range_twoSided hμ).subset (image_subset_range _ _))]
  exact (nontrivial_of_lt self_mem_Ici hab.le hab).image (twoSided_injective hμ)

-- (63)
theorem atMostInq_twoSided (a : α) :
    atMostInq (· ≥ ·) univ (twoSided μ) a = twoSided μ '' Iic a := by
  rw [atMostInq_of_pairwiseDisjoint (pairwiseDisjoint_fiber μ univ)]; congr 1; ext; simp

-- (64)
theorem atMostInq_oneSided (a : α) :
    atMostInq (· ≥ ·) univ (oneSided μ) a = (fun i ↦ μ ⁻¹' Icc i a) '' Iic a := by
  rw [atMostInq_ge, atMost_oneSided, image_image]
  simp only [oneSided, ← preimage_inter, Ici_inter_Iic]

-- (64)
theorem atMostInq_oneSided_id (a : ℕ) :
    atMostInq (· ≥ ·) univ (oneSided (id : ℕ → ℕ)) a = (Icc · a) '' Iic a :=
  atMostInq_oneSided a

-- (73)
theorem sUnion_atLeastInq_succ [SuccOrder α] [NoMaxOrder α] (a : α) :
    ⋃₀ atLeastInq (· ≥ ·) univ (twoSided μ) (Order.succ a) = μ ⁻¹' Ioi a := by
  rw [sUnion_atLeastInq, atLeast_twoSided]
  exact congrArg _ (Order.Ici_succ a)

end Measure

end Inquisitive

/-! ### Ignorance (§3.4.1) -/

section Ignorance

variable {W : Type*} {Q : Set (Set W)} {k : Set W}

/-- (68): the Maxim of Interactive Sincerity requires a proposition that raises several
possibilities to raise several within the speaker's information set `k`. -/
def InteractiveSincerity (Q : Set (Set W)) (k : Set W) : Prop :=
  Q.Nontrivial → (restrict Q k).Nontrivial

-- (72)
theorem interactiveSincerity_of_subsingleton (hQ : Q.Subsingleton) (k : Set W) :
    InteractiveSincerity Q k :=
  fun h ↦ absurd hQ h.not_subsingleton

theorem interactiveSincerity_iff_of_subsingleton_restrict (h : (restrict Q k).Subsingleton) :
    InteractiveSincerity Q k ↔ ¬ Q.Nontrivial :=
  ⟨fun hs hQ ↦ (hs hQ).not_subsingleton h, fun h hQ ↦ absurd hQ h⟩

theorem interactiveSincerity_singleton_iff (w : W) :
    InteractiveSincerity Q {w} ↔ ¬ Q.Nontrivial :=
  interactiveSincerity_iff_of_subsingleton_restrict (subsingleton_restrict_singleton w)

theorem forall_interactiveSincerity_iff [Nonempty W] :
    (∀ k, InteractiveSincerity Q k) ↔ ¬ Q.Nontrivial :=
  ⟨fun h ↦ (interactiveSincerity_singleton_iff (Classical.arbitrary W)).1 (h _),
    fun h _ hQ ↦ absurd hQ h⟩

variable {ι : Type*} {S : ι → ι → Prop} {C : Set ι} {P : ι → Set W} {i : ι}

theorem subsingleton_restrict_atLeastInq [Std.Antisymm S] (hk : k ⊆ atMost S C P i) :
    (restrict (atLeastInq S C P i) k).Subsingleton := by
  have key : ∀ p ∈ atLeastInq S C P i, (k ∩ p).Nonempty → p = P i := by
    rintro _ ⟨j, ⟨hj, hji⟩, rfl⟩ ⟨w, hwk, hwj⟩
    rw [antisymm hji (hk hwk j hj hwj)]
  exact subsingleton_restrict_iff.2 fun p hp q hq hkp hkq ↦ by rw [key p hp hkp, key q hq hkq]

/-- A speaker who knows *only `i`* cannot sincerely say *at least `i`* when that raises several
possibilities. -/
theorem not_interactiveSincerity_of_only [Std.Antisymm S] (hk : ∀ w ∈ k, only S C P i w = .true)
    (hQ : (atLeastInq S C P i).Nontrivial) : ¬ InteractiveSincerity (atLeastInq S C P i) k :=
  fun h ↦ (h hQ).not_subsingleton
    (subsingleton_restrict_atLeastInq fun w hw ↦ (only_eq_true_iff.1 (hk w hw)).2)

variable {α : Type*} {μ : W → α} {b : α}

theorem subset_or_disjoint_preimage (hk : k ⊆ μ ⁻¹' {b}) (s : Set α) :
    k ⊆ μ ⁻¹' s ∨ Disjoint k (μ ⁻¹' s) := by
  by_cases hb : b ∈ s
  · exact .inl fun w hw ↦ by rw [mem_preimage, show μ w = b from hk hw]; exact hb
  · exact .inr (disjoint_left.2 fun w hw hws ↦ hb (by rw [← show μ w = b from hk hw]; exact hws))

-- A speaker who knows the measure decides every answer about it.
theorem subsingleton_restrict_atLeastInq_preimage (s : ι → Set α) (i : ι) (hk : k ⊆ μ ⁻¹' {b}) :
    (restrict (atLeastInq S C (fun j ↦ μ ⁻¹' s j) i) k).Subsingleton :=
  subsingleton_restrict_of_subset_or_disjoint <| by
    rintro _ ⟨j, -, rfl⟩
    exact subset_or_disjoint_preimage hk (s j)

variable [LinearOrder α] {a c : α}

/-- (70a): a speaker who knows how many cannot sincerely say *at least `a`* over two-sided
answers. -/
theorem not_interactiveSincerity_atLeastInq_twoSided (hμ : Surjective μ) (hac : a < c)
    (hk : k ⊆ twoSided μ b) :
    ¬ InteractiveSincerity (atLeastInq (· ≥ ·) univ (twoSided μ) a) k :=
  fun h ↦ (h (nontrivial_iff_isInquisitive_or_isAttentive.2
    (.inl (isInquisitive_atLeastInq_twoSided hμ hac)))).not_subsingleton
      (subsingleton_restrict_atLeastInq_preimage (fun i ↦ {i}) a hk)

-- (70a), with one-sided answers
theorem not_interactiveSincerity_atLeastInq_oneSided (hμ : Surjective μ) (hac : a < c)
    (hk : k ⊆ twoSided μ b) :
    ¬ InteractiveSincerity (atLeastInq (· ≥ ·) univ (oneSided μ) a) k :=
  fun h ↦ (h (nontrivial_iff_isInquisitive_or_isAttentive.2
    (.inr (isAttentive_atLeastInq_oneSided hμ hac)))).not_subsingleton
      (subsingleton_restrict_atLeastInq_preimage Ici a hk)

end Ignorance

/-! ### The judgments -/

section Judgments

variable {W : Type*}

/-- The possibilities a modified numeral raises on the question of how many: *at least `n`* each
answer from `n` up, and *more than `n`* the one possibility that the number exceeds `n` (72). -/
def Examples.Modifier.raised (μ : W → ℕ) : Examples.Modifier → ℕ → Set (Set W)
  | .atLeast, n => atLeastInq (· ≥ ·) univ (twoSided μ) n
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
      (not_interactiveSincerity_atLeastInq_twoSided hμ (Nat.lt_succ_self 5) hk)⟩
  · exact ⟨.moreThan, by decide, 4, by decide, iff_of_true (by decide)
      (interactiveSincerity_of_subsingleton subsingleton_singleton k)⟩

end Judgments

/-! ### Exhaustivity (§3.4.2) -/

section Exhaustivity

variable {W : Type*} {C : Set (Set W)} {p : Set W}

/-- Exhaustifying each possibility that *at least `p`* raises against the question leaves their
union equal to `p`, when each world of `p` has a strongest true answer. -/
theorem sUnion_exh_atLeastInq (hp : p ∈ C) (h : ∀ w ∈ p, ∃ q, IsLeast {q ∈ C | w ∈ q} q) :
    ⋃₀ (exh C '' atLeastInq (· ⊆ ·) C id p) = p := by
  refine Subset.antisymm (sUnion_subset ?_) fun w hw ↦ ?_
  · rintro _ ⟨_, ⟨q, ⟨-, hqp⟩, rfl⟩, rfl⟩
    exact (exh_subset C q).trans hqp
  · obtain ⟨q, hq⟩ := h w hw
    exact ⟨_, ⟨q, ⟨q, ⟨hq.1.1, hq.2 ⟨hp, hw⟩⟩, rfl⟩, rfl⟩, (mem_exh_iff_isLeast_of_mem hq.1.1).2 hq⟩

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
theorem atLeastInq_ann : atLeastInq (· ⊆ ·) whoSnores id ann = {ann, ann ∩ bill} := by
  rw [atLeastInq, image_id]
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
theorem isAttentive_atLeastInq_ann : IsAttentive (atLeastInq (· ⊆ ·) whoSnores id ann) := by
  rw [atLeastInq_ann]
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
    ¬ InteractiveSincerity (atLeastInq (· ⊆ ·) whoSnores id ann) {(true, false)} :=
  not_interactiveSincerity_of_only
    (fun w hw ↦ Trivalent.mem_posExt.1 <| by
      rw [posExt_only_subset (by simp [whoSnores]), exh_whoSnores_ann]; exact hw)
    (nontrivial_iff_isInquisitive_or_isAttentive.2 (.inr isAttentive_atLeastInq_ann))

-- (77), Figure 4(b)
theorem exh_whoSnores_atLeastInq_ann :
    exh whoSnores '' atLeastInq (· ⊆ ·) whoSnores id ann = {{(true, false)}, {(true, true)}} := by
  rw [atLeastInq_ann, image_pair, exh_whoSnores_ann, exh_whoSnores_inter]

end Exhaustivity

end CoppockBrochhagen2013
