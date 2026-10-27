module

public import Mathlib.Order.Hom.WithTopBot
public import Mathlib.Order.Interval.Basic

/-!
# Relations between intervals

This file defines the relations between two nonempty intervals of an ordered type that mathlib's
`NonemptyInterval` API leaves implicit, and their counterparts on `Interval`, the intervals with
a null element. Two intervals overlap when neither lies strictly beyond the other, and `i₁`
precedes `i₂` when it ends strictly before `i₂` starts. `During`, `FinalSubinterval` and
`NonfinalSubinterval` refine containment, the last being the subinterval into which a longer one
extends into the future, and `IsPoint` singles out the intervals with a single element. In a linear
order two intervals overlap exactly when neither precedes the other, so their `position` is one of
three.

Containment, the subinterval order and point intervals are mathlib's own (`t ∈ i`, `i₁ ≤ i₂`,
`pure t`); `lt_def` unfolds strict containment to endpoints. On `Interval α`, where `≤` is
inclusion and `⊓` intersection, `Interval.Precedes` is precedence stated pointwise, a left
endpoint is `IsLeast` of the coerced set, `NonemptyInterval.withTop` embeds a bounded interval
into `WithTop α`, and `Interval.Ici a` is the ray `[a, ⊤]`.

## Main definitions

* `NonemptyInterval.Overlaps`, `NonemptyInterval.Precedes`: the order of two intervals, and
  `NonemptyInterval.position` the position of one relative to the other.
* `NonemptyInterval.During`, `NonemptyInterval.FinalSubinterval`,
  `NonemptyInterval.NonfinalSubinterval`: refinements of containment.
* `Interval.Precedes`, `Interval.Ici`: pointwise precedence and rays on intervals with a null
  element.

## Implementation notes

The instances `Decidable (a ∈ s)` and `Decidable (s < t)`, and the lemmas `lt_def`, `notMem_iff`,
`Interval.coe_le_iff`, `Interval.pure_le_iff`, `Interval.mem_inf`, `Interval.isLeast_coe_fst` and
`Interval.notMem_bot`, are `[UPSTREAM]` candidates for `Mathlib/Order/Interval/Basic.lean`.
`Overlaps`, `Precedes` and `position` might be taken in some form. The refinements of containment
and the `WithTop` embedding are vocabulary for the semantics of tense and aspect, which mathlib
would write out.

## References

* [allen-1983]
-/

@[expose] public section

namespace NonemptyInterval

/-! ### Relations between intervals -/

section LE

variable {α : Type*} [LE α] {i₁ i₂ : NonemptyInterval α}

/-- Two intervals overlap when neither lies strictly beyond the other. -/
def Overlaps (i₁ i₂ : NonemptyInterval α) : Prop :=
  i₁.fst ≤ i₂.snd ∧ i₂.fst ≤ i₁.snd

/-- An interval is a point when its endpoints coincide. -/
def IsPoint (i : NonemptyInterval α) : Prop :=
  i.fst = i.snd

/-- `i₁` is a final subinterval of `i₂` when it starts no earlier than `i₂` and ends with it. -/
def FinalSubinterval (i₁ i₂ : NonemptyInterval α) : Prop :=
  i₂.fst ≤ i₁.fst ∧ i₁.snd = i₂.snd

section Decidability

variable [DecidableLE α] [DecidableEq α]

instance : Decidable (i₁.Overlaps i₂) := inferInstanceAs (Decidable (_ ∧ _))
instance {i : NonemptyInterval α} : Decidable i.IsPoint := inferInstanceAs (Decidable (_ = _))
instance : Decidable (i₁.FinalSubinterval i₂) := inferInstanceAs (Decidable (_ ∧ _))

end Decidability

@[simp] theorem overlaps_refl (i : NonemptyInterval α) : i.Overlaps i :=
  ⟨i.fst_le_snd, i.fst_le_snd⟩

theorem overlaps_symm (h : i₁.Overlaps i₂) : i₂.Overlaps i₁ :=
  ⟨h.2, h.1⟩

theorem overlaps_comm (i₁ i₂ : NonemptyInterval α) : i₁.Overlaps i₂ ↔ i₂.Overlaps i₁ :=
  ⟨overlaps_symm, overlaps_symm⟩

end LE

section Preorder

variable {α : Type*} [Preorder α] {i₁ i₂ : NonemptyInterval α}

instance {a : α} {s : NonemptyInterval α} [DecidableLE α] : Decidable (a ∈ s) :=
  decidable_of_iff' _ mem_def

instance {s t : NonemptyInterval α} [DecidableLE α] : Decidable (s < t) :=
  decidable_of_iff' _ lt_iff_le_not_ge

/-- `i₁` precedes `i₂` when `i₁` ends strictly before `i₂` starts. -/
def Precedes (i₁ i₂ : NonemptyInterval α) : Prop :=
  i₁.snd < i₂.fst

/-- `i₁` lies during `i₂` when it is strictly inside `i₂` on both sides. -/
def During (i₁ i₂ : NonemptyInterval α) : Prop :=
  i₂.fst < i₁.fst ∧ i₁.snd < i₂.snd

/-- `i₁` is a nonfinal subinterval of `i₂` when it starts no earlier than `i₂` and ends strictly
before it. -/
def NonfinalSubinterval (i₁ i₂ : NonemptyInterval α) : Prop :=
  i₂.fst ≤ i₁.fst ∧ i₁.snd < i₂.snd

instance [DecidableLE α] : Decidable (i₁.Precedes i₂) :=
  decidable_of_iff' _ lt_iff_le_not_ge

instance [DecidableLE α] : Decidable (i₁.During i₂) :=
  @instDecidableAnd _ _ (decidable_of_iff' _ lt_iff_le_not_ge)
    (decidable_of_iff' _ lt_iff_le_not_ge)

instance [DecidableLE α] : Decidable (i₁.NonfinalSubinterval i₂) :=
  @instDecidableAnd _ _ inferInstance (decidable_of_iff' _ lt_iff_le_not_ge)

theorem NonfinalSubinterval.le (h : i₁.NonfinalSubinterval i₂) : i₁ ≤ i₂ :=
  le_def.2 ⟨h.1, h.2.le⟩

theorem NonfinalSubinterval.lt (h : i₁.NonfinalSubinterval i₂) : i₁ < i₂ :=
  lt_iff_le_not_ge.2 ⟨h.le, fun h' ↦ (le_def.1 h').2.not_gt h.2⟩

theorem NonfinalSubinterval.not_finalSubinterval (h : i₁.NonfinalSubinterval i₂) :
    ¬ i₁.FinalSubinterval i₂ :=
  fun h' ↦ h.2.ne h'.2

theorem during_irrefl (i : NonemptyInterval α) : ¬ i.During i := fun h ↦ lt_irrefl _ h.1

theorem During.not_precedes (h : i₁.During i₂) : ¬ i₁.Precedes i₂ :=
  fun h' ↦ lt_irrefl _ ((h.1.trans_le i₁.fst_le_snd).trans h')

theorem During.not_precedes' (h : i₁.During i₂) : ¬ i₂.Precedes i₁ :=
  fun h' ↦ lt_irrefl _ ((i₁.fst_le_snd.trans_lt h.2).trans h')

@[simp] theorem finalSubinterval_refl (i : NonemptyInterval α) : i.FinalSubinterval i :=
  ⟨le_rfl, rfl⟩

theorem FinalSubinterval.le (h : i₁.FinalSubinterval i₂) : i₁ ≤ i₂ :=
  le_def.2 ⟨h.1, h.2.le⟩

theorem overlaps_of_le (h : i₁ ≤ i₂) : i₁.Overlaps i₂ :=
  ⟨i₁.fst_le_snd.trans (le_def.1 h).2, (le_def.1 h).1.trans i₁.fst_le_snd⟩

theorem precedes_irrefl (i : NonemptyInterval α) : ¬ i.Precedes i :=
  fun h ↦ absurd i.fst_le_snd (not_le_of_gt h)

theorem precedes_asymm (h : i₁.Precedes i₂) : ¬ i₂.Precedes i₁ :=
  fun h' ↦ absurd (i₂.fst_le_snd.trans (h'.le.trans i₁.fst_le_snd)) (not_le_of_gt h)

theorem precedes_trans {i₃ : NonemptyInterval α} (h₁₂ : i₁.Precedes i₂) (h₂₃ : i₂.Precedes i₃) :
    i₁.Precedes i₃ :=
  (h₁₂.trans_le i₂.fst_le_snd).trans h₂₃

theorem precedes_of_le_of_precedes {i₃ : NonemptyInterval α} (h₁ : i₁ ≤ i₂)
    (h₂ : i₂.Precedes i₃) : i₁.Precedes i₃ :=
  (le_def.1 h₁).2.trans_lt h₂

theorem Precedes.not_overlaps (h : i₁.Precedes i₂) : ¬ i₁.Overlaps i₂ :=
  fun ⟨_, h₂⟩ ↦ lt_irrefl _ (h.trans_le h₂)

end Preorder

section LinearOrder

variable {α : Type*} [LinearOrder α] {i₁ i₂ : NonemptyInterval α}

theorem lt_def : i₁ < i₂ ↔ i₁ ≤ i₂ ∧ (i₂.fst < i₁.fst ∨ i₁.snd < i₂.snd) := by
  rw [lt_iff_le_not_ge]
  exact and_congr_right' (by rw [le_def, not_and_or, not_le, not_le])

/-- A nonfinal subinterval is a proper subinterval that is not final. -/
theorem nonfinalSubinterval_iff : i₁.NonfinalSubinterval i₂ ↔ i₁ < i₂ ∧ ¬ i₁.FinalSubinterval i₂ :=
  ⟨fun h ↦ ⟨h.lt, h.not_finalSubinterval⟩, fun ⟨hlt, hfin⟩ ↦
    ⟨(le_def.1 hlt.le).1, (le_def.1 hlt.le).2.lt_of_ne fun h ↦ hfin ⟨(le_def.1 hlt.le).1, h⟩⟩⟩

theorem notMem_iff {a : α} {i : NonemptyInterval α} : a ∉ i ↔ a < i.fst ∨ i.snd < a := by
  rw [mem_def, not_and_or, not_le, not_le]

theorem Overlaps.mono_left {i₁' : NonemptyInterval α} (h : i₁.Overlaps i₂) (hle : i₁ ≤ i₁') :
    i₁'.Overlaps i₂ :=
  ⟨(le_def.1 hle).1.trans h.1, h.2.trans (le_def.1 hle).2⟩

theorem overlaps_iff_not_precedes : i₁.Overlaps i₂ ↔ ¬ i₁.Precedes i₂ ∧ ¬ i₂.Precedes i₁ := by
  simp only [Overlaps, Precedes, not_lt, and_comm]

theorem precedes_iff_forall_mem : i₁.Precedes i₂ ↔ ∀ a ∈ i₁, ∀ b ∈ i₂, a < b :=
  ⟨fun h _ ha _ hb ↦ ((mem_def.1 ha).2.trans_lt h).trans_le (mem_def.1 hb).1,
    fun h ↦ h _ (mem_def.2 ⟨i₁.fst_le_snd, le_rfl⟩) _ (mem_def.2 ⟨le_rfl, i₂.fst_le_snd⟩)⟩

theorem overlaps_iff_exists_mem : i₁.Overlaps i₂ ↔ ∃ a, a ∈ i₁ ∧ a ∈ i₂ :=
  ⟨fun h ↦ ⟨max i₁.fst i₂.fst, mem_def.2 ⟨le_max_left .., max_le i₁.fst_le_snd h.2⟩,
      mem_def.2 ⟨le_max_right .., max_le h.1 i₂.fst_le_snd⟩⟩,
    fun ⟨_, h₁, h₂⟩ ↦ ⟨(mem_def.1 h₁).1.trans (mem_def.1 h₂).2,
      (mem_def.1 h₂).1.trans (mem_def.1 h₁).2⟩⟩

/-- The position of `i₁` relative to `i₂`: `lt` when `i₁` precedes `i₂`, `gt` when `i₂` precedes
`i₁`, and `eq` when the two overlap. -/
def position (i₁ i₂ : NonemptyInterval α) : Ordering :=
  if i₁.Precedes i₂ then .lt else if i₂.Precedes i₁ then .gt else .eq

@[simp] theorem position_eq_lt : i₁.position i₂ = .lt ↔ i₁.Precedes i₂ := by
  unfold position; split_ifs <;> simp [*]

@[simp] theorem position_eq_gt : i₁.position i₂ = .gt ↔ i₂.Precedes i₁ := by
  unfold position
  split_ifs with h h'
  · simp [precedes_asymm h]
  · simp [h']
  · simp [h']

@[simp] theorem position_eq_eq : i₁.position i₂ = .eq ↔ i₁.Overlaps i₂ := by
  rw [overlaps_iff_not_precedes]
  unfold position
  split_ifs <;> simp [*]

@[simp] theorem position_self (i : NonemptyInterval α) : i.position i = .eq :=
  position_eq_eq.2 (overlaps_refl i)

@[simp] theorem position_pure (a b : α) : (pure a).position (pure b) = compare a b := by
  rcases lt_trichotomy a b with h | rfl | h
  · rw [position_eq_lt.2 (by exact h), compare_lt_iff_lt.2 h]
  · rw [position_self, compare_eq_iff_eq.2 rfl]
  · rw [position_eq_gt.2 (by exact h), compare_gt_iff_gt.2 h]

/-- An interval containing `i₁` stands to `i₂` where `i₁` does, or overlaps it. -/
theorem position_eq_or_eq_eq_of_le {i₁' : NonemptyInterval α} (hle : i₁ ≤ i₁') :
    i₁'.position i₂ = i₁.position i₂ ∨ i₁'.position i₂ = .eq := by
  cases h : i₁'.position i₂ with
  | lt => exact .inl (position_eq_lt.2 <| precedes_of_le_of_precedes hle (position_eq_lt.1 h)).symm
  | eq => exact .inr rfl
  | gt => exact .inl (position_eq_gt.2 <| (position_eq_gt.1 h).trans_le (le_def.1 hle).1).symm

end LinearOrder

/-! ### Embedding into `WithTop` -/

section WithTop

variable {α : Type*} [Preorder α]

/-- An interval of `α` as an interval of `WithTop α`. -/
def withTop (i : NonemptyInterval α) : NonemptyInterval (WithTop α) :=
  i.map WithTop.coeOrderHom.toOrderHom

@[simp] theorem fst_withTop (i : NonemptyInterval α) : i.withTop.fst = ↑i.fst := rfl

@[simp] theorem snd_withTop (i : NonemptyInterval α) : i.withTop.snd = ↑i.snd := rfl

@[simp] theorem mem_withTop {i : NonemptyInterval α} {x : WithTop α} :
    x ∈ i.withTop ↔ ↑i.fst ≤ x ∧ x ≤ ↑i.snd :=
  Iff.rfl

@[simp] theorem withTop_le_withTop {i j : NonemptyInterval α} : i.withTop ≤ j.withTop ↔ i ≤ j := by
  simp [le_def]

end WithTop

end NonemptyInterval

/-! ### Intervals with a null element -/

namespace Interval

section PartialOrder

variable {α : Type*} [PartialOrder α] {s t : Interval α} {i j : NonemptyInterval α} {a b x : α}

/-- `s` precedes `t` when every element of `s` is below every element of `t`, Allen's *before*
stated pointwise, vacuously so at the null interval. -/
def Precedes (s t : Interval α) : Prop := ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ t → x < y

@[simp] theorem notMem_bot : x ∉ (⊥ : Interval α) := by
  simp [← SetLike.mem_coe]

theorem coe_le_iff : (↑i : Interval α) ≤ s ↔ i.fst ∈ s ∧ i.snd ∈ s := by
  induction s using recBotCoe with
  | bot =>
    exact iff_of_false (fun h ↦ WithBot.coe_ne_bot (le_bot_iff.1 h)) (fun h ↦ notMem_bot h.1)
  | coe j =>
    refine ⟨fun h ↦ ?_, fun ⟨h₁, h₂⟩ ↦ WithBot.coe_le_coe.2 (NonemptyInterval.le_def.2
      ⟨(NonemptyInterval.mem_def.1 h₁).1, (NonemptyInterval.mem_def.1 h₂).2⟩)⟩
    obtain ⟨h₁, h₂⟩ := NonemptyInterval.le_def.1 (WithBot.coe_le_coe.1 h)
    exact ⟨NonemptyInterval.mem_def.2 ⟨h₁, i.fst_le_snd.trans h₂⟩,
      NonemptyInterval.mem_def.2 ⟨h₁.trans i.fst_le_snd, h₂⟩⟩

@[simp] theorem pure_le_iff : pure a ≤ s ↔ a ∈ s := by
  simp [← coe_subset_coe]

theorem isLeast_coe_fst : IsLeast (↑(↑i : Interval α) : Set α) i.fst :=
  ⟨NonemptyInterval.mem_def.2 ⟨le_rfl, i.fst_le_snd⟩,
    fun _ hx ↦ (NonemptyInterval.mem_def.1 hx).1⟩

theorem precedes_coe_coe : (↑i : Interval α).Precedes ↑j ↔ i.Precedes j :=
  ⟨fun h ↦ h (NonemptyInterval.mem_def.2 ⟨i.fst_le_snd, le_rfl⟩)
      (NonemptyInterval.mem_def.2 ⟨le_rfl, j.fst_le_snd⟩),
    fun h _ hx _ hy ↦ (NonemptyInterval.mem_def.1 hx).2.trans_lt
      (h.trans_le (NonemptyInterval.mem_def.1 hy).1)⟩

end PartialOrder

section Lattice

variable {α : Type*} [Lattice α] {s t : Interval α} {x : α}

theorem not_disjoint_iff : ¬ Disjoint s t ↔ ∃ x, x ∈ s ∧ x ∈ t := by
  simp only [← disjoint_coe, Set.not_disjoint_iff, SetLike.mem_coe]

theorem not_disjoint_coe_coe {i j : NonemptyInterval α} :
    ¬ Disjoint (↑i : Interval α) ↑j ↔ i.Overlaps j := by
  rw [not_disjoint_iff]
  constructor
  · rintro ⟨x, hx, hy⟩
    exact ⟨(NonemptyInterval.mem_def.1 hx).1.trans (NonemptyInterval.mem_def.1 hy).2,
      (NonemptyInterval.mem_def.1 hy).1.trans (NonemptyInterval.mem_def.1 hx).2⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨i.fst ⊔ j.fst, NonemptyInterval.mem_def.2 ⟨le_sup_left, sup_le i.fst_le_snd h₂⟩,
      NonemptyInterval.mem_def.2 ⟨le_sup_right, sup_le h₁ j.fst_le_snd⟩⟩

variable [DecidableLE α]

@[simp] theorem mem_inf : x ∈ s ⊓ t ↔ x ∈ s ∧ x ∈ t := by
  simp [← SetLike.mem_coe]

end Lattice

/-! ### Rays -/

section OrderTop

variable {α : Type*} [PartialOrder α] [OrderTop α] {a b x : α}

/-- The ray `[a, ⊤]`. -/
def Ici (a : α) : Interval α := ↑(⟨(a, ⊤), le_top⟩ : NonemptyInterval α)

@[simp] theorem mem_Ici : x ∈ Ici a ↔ a ≤ x := by
  simp [Ici, NonemptyInterval.mem_def]

@[simp] theorem Ici_le_Ici : Ici a ≤ Ici b ↔ b ≤ a := by
  simp [Ici, NonemptyInterval.le_def]

theorem antitone_Ici : Antitone (Ici : α → Interval α) := fun _ _ h ↦ Ici_le_Ici.2 h

@[simp] theorem pure_le_Ici : pure b ≤ Ici a ↔ a ≤ b := by
  simp

theorem le_Ici_iff {s : Interval α} : s ≤ Ici a ↔ ∀ x ∈ s, a ≤ x := by
  simp [← coe_subset_coe, Set.subset_def]

end OrderTop

section WithTop

variable {α : Type*} [PartialOrder α] {i : NonemptyInterval α} {a : α}

theorem withTop_le_Ici : (↑i.withTop : Interval (WithTop α)) ≤ Ici ↑a ↔ a ≤ i.fst := by
  simp only [coe_le_iff, NonemptyInterval.fst_withTop, NonemptyInterval.snd_withTop, mem_Ici,
    WithTop.coe_le_coe]
  exact ⟨And.left, fun h ↦ ⟨h, h.trans i.fst_le_snd⟩⟩

theorem precedes_withTop_Ici :
    (↑i.withTop : Interval (WithTop α)).Precedes (Ici ↑a) ↔ i.snd < a := by
  rw [Ici, precedes_coe_coe]; simp [NonemptyInterval.Precedes]

theorem precedes_withTop_pure :
    (↑i.withTop : Interval (WithTop α)).Precedes (pure ↑a) ↔ i.snd < a := by
  rw [pure, precedes_coe_coe]; simp [NonemptyInterval.Precedes]

end WithTop

section WithTopLattice

variable {α : Type*} [Lattice α] {i : NonemptyInterval α} {a : α}

theorem not_disjoint_withTop_Ici :
    ¬ Disjoint (↑i.withTop : Interval (WithTop α)) (Ici ↑a) ↔ a ≤ i.snd := by
  rw [Ici, not_disjoint_coe_coe]; simp [NonemptyInterval.Overlaps]

end WithTopLattice

end Interval
