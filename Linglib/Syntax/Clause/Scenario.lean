module

public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Order.Monotone.Basic
public import Linglib.Core.Order.Atoms
public import Mathlib.Tactic.DeriveFintype

/-!
# Scenarios

A scenario is the pair of co-arguments of a clause ordered by role rank, A over P in a
monotransitive clause and R over T in a ditransitive one, each carried as its value on a
referential prominence scale. Scenarios are ordered componentwise with the lower-ranked value
reversed, so a scenario lies above another when its higher-ranked argument is at least as
prominent and its lower-ranked one at most as prominent. The kind of a scenario compares its two
values: downstream when the higher-ranked argument is the more prominent, upstream when it is
the less prominent, and balanced when they tie. The direct and inverse contexts of cyclic Agree,
the IO–DO combinations the person-case constraint restricts, and co-argument-sensitive indexing
are all scenarios over the person scale, and Haspelmath's argument coding splits are scenarios
over his prominence scales.

## Main declarations

* `Clause.Scenario`: the two prominence values, `high` and `low`, with `Scenario.map` and
  `Scenario.equivProd`, ordered with `⊤ = ⟨⊤, ⊥⟩`.
* `Clause.Scenario.Kind`: upstream, balanced, downstream, as a bounded linear order in that
  order.
* `Clause.Scenario.kind`: the kind of a scenario over a linearly ordered scale, monotone
  (`kind_mono`) and unchanged by a strictly monotone map of the scale (`kind_map`).
* `Clause.Scenario.kind_lt_kind_iff`: on a two-element scale one scenario's kind is below
  another's exactly when the scenario is below the other.

## Implementation notes

The kind is the three-way comparison `compare` read into the three labels by
`Kind.ofOrdering`, and the order on kinds, downstream above upstream, is Haspelmath's order of
usualness (11). A scenario over a scale that is not linearly ordered, such as persons, is read
on a rank map `p` as `s.map p`.

## References

* [haspelmath-2021]
* [bejar-rezac-2009]
* [deal-2024]
* [witzlack-makarevich-etal-2016]
-/

@[expose] public section

namespace Clause

/-- A scenario records the prominence values of the two co-arguments of a clause, the
higher-ranked one first. Haspelmath writes `X > Y` for `⟨X, Y⟩`. -/
@[ext]
structure Scenario (α : Type*) where
  /-- The prominence of the higher-ranked argument, A or R. -/
  high : α
  /-- The prominence of the lower-ranked argument, P or T. -/
  low : α
  deriving DecidableEq, Fintype

namespace Scenario

variable {α β : Type*}

/-- Apply a map to both prominence values. -/
def map (f : α → β) (s : Scenario α) : Scenario β := ⟨f s.high, f s.low⟩

@[simp] theorem map_high (f : α → β) (s : Scenario α) : (s.map f).high = f s.high := rfl

@[simp] theorem map_low (f : α → β) (s : Scenario α) : (s.map f).low = f s.low := rfl

/-- A scenario is the pair of its higher- and lower-ranked values. -/
@[simps]
def equivProd : Scenario α ≃ α × α where
  toFun s := (s.high, s.low)
  invFun p := ⟨p.1, p.2⟩

/-! ### The order on scenarios -/

section LE

variable [LE α] {s t : Scenario α}

instance : LE (Scenario α) := ⟨fun s t ↦ s.high ≤ t.high ∧ t.low ≤ s.low⟩

theorem le_def : s ≤ t ↔ s.high ≤ t.high ∧ t.low ≤ s.low := Iff.rfl

instance [DecidableLE α] : DecidableLE (Scenario α) := fun _ _ ↦ decidable_of_iff' _ le_def

/-- The top scenario is `⟨⊤, ⊥⟩` and the bottom one `⟨⊥, ⊤⟩`. -/
instance [BoundedOrder α] : BoundedOrder (Scenario α) where
  top := ⟨⊤, ⊥⟩
  le_top _ := ⟨le_top, bot_le⟩
  bot := ⟨⊥, ⊤⟩
  bot_le _ := ⟨bot_le, le_top⟩

@[simp] theorem top_high [BoundedOrder α] : (⊤ : Scenario α).high = ⊤ := rfl

@[simp] theorem top_low [BoundedOrder α] : (⊤ : Scenario α).low = ⊥ := rfl

@[simp] theorem bot_high [BoundedOrder α] : (⊥ : Scenario α).high = ⊥ := rfl

@[simp] theorem bot_low [BoundedOrder α] : (⊥ : Scenario α).low = ⊤ := rfl

end LE

section Preorder

variable [Preorder α]

instance : Preorder (Scenario α) where
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

instance [DecidableLE α] : DecidableLT (Scenario α) := decidableLTOfDecidableLE

theorem high_mono : Monotone (high : Scenario α → α) := fun _ _ h ↦ h.1

theorem low_anti : Antitone (low : Scenario α → α) := fun _ _ h ↦ h.2

end Preorder

instance [PartialOrder α] : PartialOrder (Scenario α) where
  le_antisymm _ _ h₁ h₂ := Scenario.ext (h₁.1.antisymm h₂.1) (h₂.2.antisymm h₁.2)

/-! ### Kinds -/

/-- The kinds of scenario, in order of usualness, Haspelmath's three kinds of scenarios. A kind
classifies what a scenario means, not how it is coded, so it is not called a direction, the
category that direct and inverse markers realize. -/
inductive Kind where
  | upstream
  | balanced
  | downstream
  deriving DecidableEq, Fintype, Repr

namespace Kind

instance : LinearOrder Kind := LinearOrder.lift' (·.ctorIdx) (by decide)

instance : Nontrivial Kind := ⟨⟨.upstream, .downstream, by decide⟩⟩

/-- `⊥ = upstream`, `⊤ = downstream`. -/
instance : BoundedOrder Kind where
  top := .downstream
  le_top := by decide
  bot := .upstream
  bot_le := by decide

theorem le_balanced_iff {k : Kind} : k ≤ .balanced ↔ k ≠ .downstream := by decide +revert

theorem balanced_le_iff {k : Kind} : .balanced ≤ k ↔ k ≠ .upstream := by decide +revert

/-- The kind a comparison of the higher-ranked argument's prominence with the lower-ranked
one's yields. -/
def ofOrdering : Ordering → Kind
  | .lt => .upstream
  | .eq => .balanced
  | .gt => .downstream

@[simp] theorem ofOrdering_eq_upstream {o : Ordering} : ofOrdering o = .upstream ↔ o = .lt := by
  cases o <;> decide

@[simp] theorem ofOrdering_eq_balanced {o : Ordering} : ofOrdering o = .balanced ↔ o = .eq := by
  cases o <;> decide

@[simp] theorem ofOrdering_eq_downstream {o : Ordering} :
    ofOrdering o = .downstream ↔ o = .gt := by
  cases o <;> decide

end Kind

section LinearOrder

variable [LinearOrder α] {s t : Scenario α}

/-- A scenario is downstream when its higher-ranked argument ranks higher on the scale,
upstream when it ranks lower, and balanced when the two tie. -/
def kind (s : Scenario α) : Kind := .ofOrdering (compare s.high s.low)

theorem kind_eq_downstream_iff : s.kind = .downstream ↔ s.low < s.high := by
  rw [kind, Kind.ofOrdering_eq_downstream, compare_gt_iff_gt]

theorem kind_eq_upstream_iff : s.kind = .upstream ↔ s.high < s.low := by
  rw [kind, Kind.ofOrdering_eq_upstream, compare_lt_iff_lt]

theorem kind_eq_balanced_iff : s.kind = .balanced ↔ s.high = s.low := by
  rw [kind, Kind.ofOrdering_eq_balanced, compare_eq_iff_eq]

theorem kind_le_balanced_iff : s.kind ≤ .balanced ↔ s.high ≤ s.low := by
  rw [Kind.le_balanced_iff, Ne, kind_eq_downstream_iff, not_lt]

theorem balanced_le_kind_iff : .balanced ≤ s.kind ↔ s.low ≤ s.high := by
  rw [Kind.balanced_le_iff, Ne, kind_eq_upstream_iff, not_lt]

theorem kind_mono : Monotone (kind : Scenario α → Kind) := fun s t h ↦ by
  rcases lt_trichotomy t.high t.low with ht | ht | ht
  · rw [kind_eq_upstream_iff.2 ((h.1.trans_lt ht).trans_le h.2), kind_eq_upstream_iff.2 ht]
  · exact (kind_le_balanced_iff.2 (h.1.trans (ht.le.trans h.2))).trans
      (balanced_le_kind_iff.2 ht.ge)
  · exact (kind_eq_downstream_iff.2 ht).symm ▸ le_top

variable [LinearOrder β] {f : α → β}

theorem kind_map (hf : StrictMono f) (s : Scenario α) : (s.map f).kind = s.kind := by
  simp only [kind, map_high, map_low, ← cmp_eq_compare, hf.cmp_map_eq]

theorem map_le_map_iff (hf : StrictMono f) : s.map f ≤ t.map f ↔ s ≤ t := by
  simp only [le_def, map_high, map_low, hf.le_iff_le]

theorem map_lt_map_iff (hf : StrictMono f) : s.map f < t.map f ↔ s < t := by
  simp only [lt_iff_le_not_ge, map_le_map_iff hf]

/-! ### Two-element scales -/

variable [BoundedOrder α] [IsSimpleOrder α]

theorem kind_lt_kind_iff : s.kind < t.kind ↔ s < t := by
  have he := (IsSimpleOrder.orderIsoBool (α := α)).strictMono
  have key : ∀ s t : Scenario Bool, s.kind < t.kind ↔ s < t := by decide
  rw [← kind_map he s, ← kind_map he t, key, map_lt_map_iff he]

theorem kind_eq_downstream_iff_eq_top : s.kind = .downstream ↔ s = ⊤ := by
  rw [kind_eq_downstream_iff, IsSimpleOrder.lt_iff_eq_bot_and_eq_top, Scenario.ext_iff, top_high,
    top_low, and_comm]

end LinearOrder

end Scenario

end Clause
