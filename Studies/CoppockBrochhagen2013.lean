module

public import Linglib.Fragments.English.NumeralModifiers
public import Linglib.Semantics.Focus.Particles
public import Linglib.Semantics.Questions.Unrestricted
public import Mathlib.Logic.Relation

/-!
# Coppock and Brochhagen (2013): Raising and resolving issues with scalar modifiers

Coppock and Brochhagen analyse *at least* and *at most* as quantifying over a scale of answers to
the question under discussion: *at least p* is what *only p* presupposes, that some true answer is
at least as strong as `p`, and *at most p* is what *only p* asserts, that no true answer is
stronger. These are `Focus.Particles.atLeast` and `Focus.Particles.atMost`, modifiers of
propositions. On the question of how many, with answers ranked by number, they give the truth
conditions of the modified numerals whether the bare numeral is read two-sidedly or one-sidedly,
and on a scale of mutually exclusive answers, such as academic ranks, *at least* widens its
prejacent.

To explain why superlative modifiers carry ignorance implicatures and no scalar implicatures, the
authors move to unrestricted inquisitive semantics, where *at least p* raises every answer at least
as strong as `p` as a possibility. A speaker who knows the answer cannot sincerely raise several
possibilities, while the comparative *more than* raises one, and exhaustifying the raised
possibilities does not exclude the stronger answers.

## Implementation notes

* A state is a relation on propositions, and the question of a measure `μ` has the answers
  `μ ⁻¹' {i}` (two-sided) or `μ ⁻¹' Ici i` (one-sided), ranked by `i`; the paper's assumption of one
  world for each number is surjectivity of `μ`.
* The choice-function entries (53), (54) and (60) are modelled by the sets of possibilities they
  denote, which is what applying them pointwise yields (`range_choice_apply`).
* The informational content of inquisitive *at most* is `max` within the common ground of the
  state, the union of its answers.
* Exhaustification against the question (77) is `Exhaustification.exh` applied to each possibility,
  whose printed form is `Exhaustification.exh_eq_sdiff`.

## TODO

The interaction with modals is not formalized: the authoritative and speaker-insecurity readings
of *at least* under deontic modals (§3.5) and the missing readings of *at most* under *may*, which
the paper derives with Hackl's *-many* (§3.6).

## References

* [E. Coppock and T. Brochhagen, *Raising and resolving issues with scalar modifiers*
  (2013)][coppock-brochhagen-2013]
* [E. Coppock and D. Beaver, *Principles of the exclusive muddle* (2014)][coppock-beaver-2014]
* [I. Ciardelli, J. Groenendijk and F. Roelofsen, *Attention! 'Might' in Inquisitive Semantics*
  (2009)][ciardelli-groenendijk-roelofsen-2009]
-/

@[expose] public section

namespace CoppockBrochhagen2013

open Focus.Particles Inquisitive.Unrestricted Set

/-! ### Truth conditions (§2.6) -/

section Indexed

variable {W α : Type*} [Preorder α] {P : α → Set W}

/-- The ranking of the answers of an indexed question by their index. -/
abbrev ranking (P : α → Set W) : Set W → Set W → Prop := Relation.Map (· ≥ ·) P P

-- (30)
theorem atLeast_map (hP : Function.Injective P) (a : α) :
    atLeast (ranking P) (range P) (P a) = ⋃ i ∈ Ici a, P i := by
  ext w
  simp only [mem_atLeast, mem_range, exists_exists_eq_and, Relation.map_apply, hP.eq_iff,
    mem_iUnion, mem_Ici, exists_prop]
  constructor
  · rintro ⟨i, hw, i', j', hij, rfl, rfl⟩
    exact ⟨i', hij, hw⟩
  · rintro ⟨i, hai, hw⟩
    exact ⟨i, hw, i, a, hai, rfl, rfl⟩

-- (31)
theorem atMost_map (hP : Function.Injective P) (a : α) :
    atMost (ranking P) (range P) (P a) = (⋃ i ∈ (Iic a)ᶜ, P i)ᶜ := by
  ext w
  simp only [mem_atMost, mem_range, forall_exists_index, forall_apply_eq_imp_iff,
    Relation.map_apply, hP.eq_iff, mem_compl_iff, mem_iUnion, mem_Iic, exists_prop, not_exists,
    not_and]
  constructor
  · rintro h i hi hw
    obtain ⟨i', j', hij, rfl, rfl⟩ := h i hw
    exact hi hij
  · intro h i hw
    exact ⟨a, i, not_not.1 fun hia ↦ h i hia hw, rfl, rfl⟩

end Indexed

section Measure

variable {W α : Type*} [LinearOrder α] {μ : W → α}

/-- The two-sided answers to the question of how many, by the measure `μ`. -/
abbrev twoSided (μ : W → α) (i : α) : Set W := μ ⁻¹' {i}

/-- The one-sided answers to the question of how many, by the measure `μ`. -/
abbrev oneSided (μ : W → α) (i : α) : Set W := μ ⁻¹' Ici i

omit [LinearOrder α] in
theorem twoSided_injective (hμ : Function.Surjective μ) : Function.Injective (twoSided μ) :=
  hμ.preimage_injective.comp singleton_injective

omit [LinearOrder α] in
theorem isAntichain_range_twoSided (hμ : Function.Surjective μ) :
    IsAntichain (· ⊆ ·) (range (twoSided μ)) := by
  rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩ hne hle
  obtain ⟨w, rfl⟩ := hμ c
  exact hne (congrArg _ (show μ w = d from hle (rfl : μ w ∈ ({μ w} : Set α))))

theorem oneSided_injective (hμ : Function.Surjective μ) : Function.Injective (oneSided μ) :=
  hμ.preimage_injective.comp Ici_injective

theorem atLeast_twoSided (hμ : Function.Surjective μ) (a : α) :
    atLeast (ranking (twoSided μ)) (range (twoSided μ)) (twoSided μ a) = μ ⁻¹' Ici a := by
  rw [atLeast_map (twoSided_injective hμ)]
  simp only [twoSided, ← preimage_iUnion₂, biUnion_of_singleton]

theorem atLeast_oneSided (hμ : Function.Surjective μ) (a : α) :
    atLeast (ranking (oneSided μ)) (range (oneSided μ)) (oneSided μ a) = μ ⁻¹' Ici a := by
  rw [atLeast_map (oneSided_injective hμ)]
  simp only [oneSided, ← preimage_iUnion₂]
  congr 1
  ext x
  simp only [mem_iUnion₂, mem_Ici, exists_prop]
  exact ⟨fun ⟨_, hai, hix⟩ ↦ hai.trans hix, fun h ↦ ⟨a, le_rfl, h⟩⟩

theorem atMost_twoSided (hμ : Function.Surjective μ) (a : α) :
    atMost (ranking (twoSided μ)) (range (twoSided μ)) (twoSided μ a) = μ ⁻¹' Iic a := by
  rw [atMost_map (twoSided_injective hμ)]
  simp only [twoSided, ← preimage_iUnion₂, biUnion_of_singleton, ← preimage_compl, compl_compl]

theorem atMost_oneSided (hμ : Function.Surjective μ) (a : α) :
    atMost (ranking (oneSided μ)) (range (oneSided μ)) (oneSided μ a) = μ ⁻¹' Iic a := by
  rw [atMost_map (oneSided_injective hμ), compl_Iic]
  simp only [oneSided, ← preimage_iUnion₂, ← preimage_compl]
  congr 1
  ext x
  simp only [mem_compl_iff, mem_iUnion₂, mem_Ici, mem_Ioi, exists_prop, not_exists, not_and,
    mem_Iic]
  exact ⟨fun h ↦ not_lt.1 fun hax ↦ h x hax le_rfl, fun h i hai hix ↦ (hai.trans_le hix).not_ge h⟩

-- (32)
theorem atMost_twoSided_mono (hμ : Function.Surjective μ) {a b : α} (hab : a ≤ b) :
    atMost (ranking (twoSided μ)) (range (twoSided μ)) (twoSided μ a) ⊆
      atMost (ranking (twoSided μ)) (range (twoSided μ)) (twoSided μ b) := by
  rw [atMost_twoSided hμ, atMost_twoSided hμ]
  exact preimage_mono (Iic_subset_Iic.2 hab)

-- (59)
theorem twoSided_ssubset_atLeast (hμ : Function.Surjective μ) {a b : α} (hab : a < b) :
    twoSided μ a ⊂ atLeast (ranking (twoSided μ)) (range (twoSided μ)) (twoSided μ a) := by
  rw [atLeast_twoSided hμ]
  obtain ⟨w, rfl⟩ := hμ b
  exact ⟨preimage_mono (singleton_subset_iff.2 le_rfl), fun h ↦ hab.ne' (h (hab.le : μ w ∈ Ici a))⟩

theorem atLeast_oneSided_eq (hμ : Function.Surjective μ) (a : α) :
    atLeast (ranking (oneSided μ)) (range (oneSided μ)) (oneSided μ a) = oneSided μ a :=
  atLeast_oneSided hμ a

end Measure

section Fragment

open scoped Denotes

variable {W : Type*} {μ : W → ℕ}

/-- On the question of how many, *at least* is the Fragment's reading of the numeral it modifies,
pulled back along the count. -/
theorem atLeast_fragment (hμ : Function.Surjective μ) (n : ℕ) :
    ∀ m ∈ ⟦English.NumeralModifiers.atLeast⟧,
      Focus.Particles.atLeast (ranking (twoSided μ)) (range (twoSided μ)) (twoSided μ n) =
        μ ⁻¹' m {n} := by
  rintro m (rfl : m = _)
  rw [atLeast_twoSided hμ, Degree.Comparison.modifier_singleton, Degree.Comparison.interval_ge]

/-- On the question of how many, *at most* is the Fragment's reading of the numeral it modifies,
pulled back along the count. -/
theorem atMost_fragment (hμ : Function.Surjective μ) (n : ℕ) :
    ∀ m ∈ ⟦English.NumeralModifiers.atMost⟧,
      Focus.Particles.atMost (ranking (twoSided μ)) (range (twoSided μ)) (twoSided μ n) =
        μ ⁻¹' m {n} := by
  rintro m (rfl : m = _)
  rw [atMost_twoSided hμ, Degree.Comparison.modifier_singleton, Degree.Comparison.interval_le]

end Fragment

/-! ### The inquisitive entries (§3.3) -/

section Inquisitive

variable {W : Type*} (S : Set W → Set W → Prop) (C : Set (Set W)) (p : Set W)

/-- *At least p* raises every answer at least as strong as `p` (52). -/
def atLeastInq : Set (Set W) := {q ∈ C | S q p}

/-- *At most p* raises every answer at most as strong as `p`, cut down to the worlds where no
stronger answer is true (60). -/
def atMostInq : Set (Set W) := (· ∩ atMost S C p) '' {q ∈ C | S p q}

/-- The informational content of inquisitive *at least* is `min` (§3.7). -/
theorem sUnion_atLeastInq : ⋃₀ atLeastInq S C p = atLeast S C p := by
  ext w; simp [atLeastInq, and_assoc, and_comm, and_left_comm]

/-- The informational content of inquisitive *at most* is `max`, within the common ground (§3.7). -/
theorem sUnion_atMostInq : ⋃₀ atMostInq S C p = atMost S C p ∩ ⋃₀ C := by
  ext w
  simp only [atMostInq, sUnion_image, mem_iUnion, mem_ofPred_eq, mem_inter_iff, exists_prop,
    mem_sUnion]
  constructor
  · rintro ⟨q, ⟨hq, _⟩, hw, hmax⟩
    exact ⟨hmax, q, hq, hw⟩
  · rintro ⟨hmax, q, hq, hw⟩
    exact ⟨q, ⟨hq, hmax q hq hw⟩, hw, hmax⟩

-- (53)
theorem range_choice_apply {T : Set (Set W)} (hT : T.Nonempty) :
    range (fun f : {f : Set (Set W) → Set W // ∀ U : Set (Set W), U.Nonempty → f U ∈ U} ↦
      f.1 T) = T := by
  classical
  ext p
  refine ⟨fun ⟨f, hf⟩ ↦ hf ▸ f.2 T hT, fun hp ↦ ?_⟩
  refine ⟨⟨fun U ↦ if p ∈ U then p else if hU : U.Nonempty then hU.some else ∅, fun U hU ↦ ?_⟩, ?_⟩
  · by_cases h : p ∈ U
    · simp [h]
    · simpa [h, hU] using hU.some_mem
  · simp [hp]

variable {S C p}

-- (58)
theorem isAttentive_atLeastInq_oneSided {α : Type*} [LinearOrder α] {μ : W → α}
    (hμ : Function.Surjective μ) {a b : α} (hab : a < b) :
    IsAttentive (atLeastInq (ranking (oneSided μ)) (range (oneSided μ)) (oneSided μ a)) := by
  refine ⟨oneSided μ b, ⟨⟨b, rfl⟩, b, a, hab.le, rfl, rfl⟩, fun hmax ↦ ?_⟩
  obtain ⟨w, rfl⟩ := hμ a
  have hle : oneSided μ b ≤ oneSided μ (μ w) := preimage_mono (Ici_subset_Ici.2 hab.le)
  have := hmax.2 ⟨⟨μ w, rfl⟩, μ w, μ w, le_rfl, rfl, rfl⟩ hle (mem_Ici.2 le_rfl : μ w ∈ Ici (μ w))
  exact (not_le.2 hab) this

-- (59b)
theorem not_isAttentive_atLeastInq_twoSided {α : Type*} [LinearOrder α] {μ : W → α}
    (hμ : Function.Surjective μ) (a : α) :
    ¬ IsAttentive (atLeastInq (ranking (twoSided μ)) (range (twoSided μ)) (twoSided μ a)) :=
  not_isAttentive_iff.2 ((isAntichain_range_twoSided hμ).subset fun _ h ↦ h.1)

-- (59b)
theorem isInquisitive_atLeastInq_twoSided {α : Type*} [LinearOrder α] {μ : W → α}
    (hμ : Function.Surjective μ) {a b : α} (hab : a < b) :
    IsInquisitive (atLeastInq (ranking (twoSided μ)) (range (twoSided μ)) (twoSided μ a)) := by
  refine (nontrivial_iff_isInquisitive_or_isAttentive.1 ?_).resolve_right
    (not_isAttentive_atLeastInq_twoSided hμ a)
  exact ⟨_, ⟨⟨a, rfl⟩, a, a, le_rfl, rfl, rfl⟩, _, ⟨⟨b, rfl⟩, b, a, hab.le, rfl, rfl⟩,
    fun h ↦ hab.ne (twoSided_injective hμ h)⟩

-- (64)
theorem atMostInq_oneSided {α : Type*} [LinearOrder α] {μ : W → α} (hμ : Function.Surjective μ)
    (a : α) :
    atMostInq (ranking (oneSided μ)) (range (oneSided μ)) (oneSided μ a) =
      (fun i ↦ μ ⁻¹' Icc i a) '' Iic a := by
  rw [atMostInq, atMost_oneSided hμ a]
  ext q
  simp only [mem_image, mem_ofPred_eq, mem_range, Relation.map_apply,
    (oneSided_injective hμ).eq_iff, mem_Iic]
  constructor
  · rintro ⟨_, ⟨⟨i, rfl⟩, a', i', hai, ha, hi⟩, rfl⟩
    obtain rfl := ha
    obtain rfl := oneSided_injective hμ hi
    exact ⟨i', hai, by rw [oneSided, ← preimage_inter, Ici_inter_Iic]⟩
  · rintro ⟨i, hia, rfl⟩
    exact ⟨oneSided μ i, ⟨⟨i, rfl⟩, a, i, hia, rfl, rfl⟩,
      by rw [oneSided, ← preimage_inter, Ici_inter_Iic]⟩

-- (63)
theorem atMostInq_twoSided {α : Type*} [LinearOrder α] {μ : W → α} (hμ : Function.Surjective μ)
    (a : α) :
    atMostInq (ranking (twoSided μ)) (range (twoSided μ)) (twoSided μ a) = twoSided μ '' Iic a := by
  rw [atMostInq, atMost_twoSided hμ a]
  ext q
  simp only [mem_image, mem_ofPred_eq, mem_range, Relation.map_apply,
    (twoSided_injective hμ).eq_iff, mem_Iic]
  constructor
  · rintro ⟨_, ⟨⟨i, rfl⟩, a', i', hai, ha, hi⟩, rfl⟩
    obtain rfl := ha
    obtain rfl := twoSided_injective hμ hi
    exact ⟨i', hai, (inter_eq_left.2 (preimage_mono (singleton_subset_iff.2 (mem_Iic.2 hai)))).symm⟩
  · rintro ⟨i, hia, rfl⟩
    exact ⟨twoSided μ i, ⟨⟨i, rfl⟩, a, i, hia, rfl, rfl⟩,
      inter_eq_left.2 (preimage_mono (singleton_subset_iff.2 (mem_Iic.2 hia)))⟩

-- (64)
theorem atMostInq_oneSided_id (a : ℕ) :
    atMostInq (ranking (oneSided (id : ℕ → ℕ))) (range (oneSided id)) (oneSided id a) =
      (Icc · a) '' Iic a :=
  atMostInq_oneSided Function.surjective_id a

end Inquisitive

/-! ### Ignorance (§3.4.1) -/

section Ignorance

variable {W : Type*}

/-- The Maxim of Interactive Sincerity (68) requires a proposition that raises several
possibilities to raise several within the speaker's information set `k`. -/
def InteractiveSincerity (P : Set (Set W)) (k : Set W) : Prop :=
  P.Nontrivial → (restrict P k).Nontrivial

theorem interactiveSincerity_singleton_iff {P : Set (Set W)} (w : W) :
    InteractiveSincerity P {w} ↔ ¬ P.Nontrivial :=
  ⟨fun h hP ↦ (h hP).not_subsingleton (subsingleton_restrict_singleton w), fun h hP ↦ absurd hP h⟩

theorem forall_interactiveSincerity_iff [Nonempty W] {P : Set (Set W)} :
    (∀ k, InteractiveSincerity P k) ↔ ¬ P.Nontrivial :=
  ⟨fun h ↦ (interactiveSincerity_singleton_iff (Classical.arbitrary W)).1 (h _),
    fun h _ hP ↦ absurd hP h⟩

variable {α : Type*} [Preorder α] {P : α → Set W}

/-- A speaker whose information lies within one answer at or above `a`, and decides each answer from
`a` up, restricts *at least `a`* to one possibility (71). -/
theorem restrict_atLeastInq_eq_singleton (hP : Function.Injective P) {a b : α} (hab : a ≤ b)
    {k : Set W} (hk : k ≠ ∅) (hkb : k ⊆ P b)
    (hsplit : ∀ i, a ≤ i → k ∩ P i = k ∨ k ∩ P i = ∅) :
    restrict (atLeastInq (ranking P) (range P) (P a)) k = {k} := by
  apply pro_eq_singleton hk
  · exact ⟨P b, ⟨⟨b, rfl⟩, b, a, hab, rfl, rfl⟩, inter_eq_left.2 hkb⟩
  · rintro _ ⟨q, ⟨⟨i, rfl⟩, i', j', hij, hi, hj⟩, rfl⟩
    rw [hP hi, hP hj] at hij
    rcases hsplit i hij with h | h <;> simp [h]

omit [Preorder α] in
theorem split_twoSided {μ : W → α} {b : α} {k : Set W} (hkb : k ⊆ μ ⁻¹' {b}) (i : α) :
    k ∩ μ ⁻¹' {i} = k ∨ k ∩ μ ⁻¹' {i} = ∅ := by
  by_cases h : i = b
  · exact Or.inl (h ▸ inter_eq_left.2 hkb)
  · exact Or.inr (eq_empty_of_subset_empty fun w ⟨hw, hwi⟩ ↦
      h ((mem_preimage.1 hwi).symm.trans (hkb hw)))

end Ignorance

theorem split_oneSided {W α : Type*} [LinearOrder α] {μ : W → α} {b : α} {k : Set W}
    (hkb : k ⊆ μ ⁻¹' {b}) (i : α) : k ∩ μ ⁻¹' Ici i = k ∨ k ∩ μ ⁻¹' Ici i = ∅ := by
  rcases le_or_gt i b with h | h
  · exact Or.inl (inter_eq_left.2 fun w hw ↦
      mem_preimage.2 (mem_Ici.2 ((hkb hw : μ w = b).symm ▸ h)))
  · exact Or.inr (eq_empty_of_subset_empty fun w ⟨hw, hwi⟩ ↦
      (not_le.2 h) ((hkb hw : μ w = b) ▸ mem_Ici.1 (mem_preimage.1 hwi)))

-- (70a)
theorem not_interactiveSincerity_hexagon {W : Type*} {μ : W → ℕ} (hμ : Function.Surjective μ)
    {k : Set W} (hk : k ≠ ∅) (hk6 : k ⊆ μ ⁻¹' {6}) :
    ¬ InteractiveSincerity (atLeastInq (ranking (twoSided μ)) (range (twoSided μ))
        (twoSided μ 5)) k ∧
      ¬ InteractiveSincerity (atLeastInq (ranking (oneSided μ)) (range (oneSided μ))
        (oneSided μ 5)) k := by
  constructor
  · intro h
    have hr := restrict_atLeastInq_eq_singleton (twoSided_injective hμ) (by decide : 5 ≤ 6) hk hk6
      (fun i _ ↦ split_twoSided hk6 i)
    have := h (nontrivial_iff_isInquisitive_or_isAttentive.2
      (.inl (isInquisitive_atLeastInq_twoSided hμ (by decide : 5 < 6))))
    rw [hr] at this
    exact this.not_subsingleton subsingleton_singleton
  · intro h
    have hr := restrict_atLeastInq_eq_singleton (oneSided_injective hμ) (by decide : 5 ≤ 6) hk
      (fun w hw ↦ mem_preimage.2 (mem_Ici.2 (hk6 hw).ge)) (fun i _ ↦ split_oneSided hk6 i)
    have := h (nontrivial_iff_isInquisitive_or_isAttentive.2
      (.inr (isAttentive_atLeastInq_oneSided hμ (by decide : 5 < 6))))
    rw [hr] at this
    exact this.not_subsingleton subsingleton_singleton

-- (72), (73)
theorem moreThan_interactiveSincerity {W : Type*} {μ : W → ℕ} (hμ : Function.Surjective μ)
    (k : Set W) :
    InteractiveSincerity {μ ⁻¹' Ioi 4} k ∧
      ⋃₀ {μ ⁻¹' Ioi 4} = ⋃₀ atLeastInq (ranking (twoSided μ)) (range (twoSided μ))
        (twoSided μ 5) := by
  refine ⟨fun h ↦ absurd h (not_nontrivial_singleton), ?_⟩
  rw [sUnion_atLeastInq, atLeast_twoSided hμ, sUnion_singleton]
  rfl

/-! ### Exhaustivity (§3.4.2) -/

section Exhaustivity

/-- The worlds of the four-world model of Figure 3, by whether Ann and whether Bill snores. -/
abbrev World := Bool × Bool

/-- *Ann snores*, *Bill snores*, and the question who snores. -/
def ann : Set World := {w | w.1}
def bill : Set World := {w | w.2}
def whoSnores : Set (Set World) := {ann, bill, ann ∩ bill}

-- (77), Figure 4
theorem exh_contrast :
    ⋃₀ (Exhaustification.exh whoSnores '' {ann}) ⊆ billᶜ ∧
      (true, true) ∈ ⋃₀ (Exhaustification.exh whoSnores '' atLeastInq (· ⊆ ·) whoSnores ann) := by
  constructor
  · rw [image_singleton, sUnion_singleton]
    exact Exhaustification.exh_subset_compl (by simp [whoSnores])
      fun h ↦ by simpa [ann, bill] using h (show (true, false) ∈ ann from rfl)
  · refine ⟨_, ⟨ann ∩ bill, ⟨by simp [whoSnores], inter_subset_left⟩, rfl⟩, ⟨rfl, rfl⟩, ?_⟩
    rintro q hq -
    simp only [whoSnores, mem_insert_iff, mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · exact inter_subset_left
    · exact inter_subset_right
    · exact subset_rfl

end Exhaustivity

end CoppockBrochhagen2013
