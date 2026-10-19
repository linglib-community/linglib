module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Preorder.Finite

/-!
# The argmax set of a function on a finset

`Finset.argmax s f` is the finset of elements of `s` at which `f` attains its
maximum over `s`. Mathlib has only the tie-breaking `List.argmax : List α →
Option α`; the set-valued form is the natural companion of `Finset.max'` and
`Finset.exists_max_image`, and the carrier for argmax *correspondences*
(set-valued best responses) in game-theoretic consumers.

[UPSTREAM] candidate: `Mathlib.Data.Finset.Max`.

## Main definitions

* `Finset.argmax s f` — the score-maximal elements of `s`.
* `Finset.argmin s f` — the score-minimal elements of `s`.

## Main statements

* `mem_argmax` — membership characterization (simp normal form).
* `argmax_eq_singleton_iff` — a sole maximizer strictly beats every other element.
* `argmax_nonempty` — nonempty on nonempty input, in a total preorder.
* `argmax_comp_strictMono` — invariance under strictly monotone rescaling.

## Implementation notes

As for `List.argmax`, the definition asks only for a preorder with decidable `≤`, not a linear
order, and the existence and uniqueness lemmas ask for totality on top. A score type whose
`LinearOrder` decides `≤` classically, such as `Lex (Fin n → ℕ)`, can then be scored under a
computable `DecidableLE` instance and evaluated by `decide`. In a preorder that is not total,
`argmax` is the set of elements at which `f` is greatest, which can be empty, not the set of
`MaximalFor` elements. The lemmas stated for linear orders take the order's own decidability, so
they do not apply under such a separate instance.
-/

@[expose] public section

namespace Finset

variable {α β γ : Type*} {s : Finset α} {f : α → β} {a : α}

section Preorder

variable [Preorder β] [DecidableLE β]

/-- The elements of `s` at which `f` attains its maximum over `s`. -/
@[to_dual /-- The elements of `s` at which `f` attains its minimum over `s`. -/]
def argmax (s : Finset α) (f : α → β) : Finset α :=
  s.filter fun a ↦ ∀ b ∈ s, f b ≤ f a

@[to_dual (attr := simp)]
theorem mem_argmax : a ∈ s.argmax f ↔ a ∈ s ∧ ∀ b ∈ s, f b ≤ f a :=
  mem_filter

@[to_dual]
theorem argmax_subset : s.argmax f ⊆ s :=
  filter_subset _ _

@[to_dual (attr := simp)]
theorem argmax_empty : (∅ : Finset α).argmax f = ∅ :=
  filter_empty _

/-- A score that is constant on `s` has all of `s` as argmax. -/
@[to_dual /-- A score that is constant on `s` has all of `s` as argmin. -/]
theorem argmax_eq_self_of_forall_le (h : ∀ a ∈ s, ∀ b ∈ s, f b ≤ f a) : s.argmax f = s :=
  filter_true_of_mem h

@[to_dual (attr := simp)]
theorem argmax_const (c : β) : s.argmax (fun _ ↦ c) = s :=
  argmax_eq_self_of_forall_le fun _ _ _ _ ↦ le_rfl

/-- Scores that order `s` oppositely swap argmin and argmax. -/
theorem argmin_eq_argmax_of_le_iff [Preorder γ] [DecidableLE γ] {f' : α → γ}
    (h : ∀ a ∈ s, ∀ b ∈ s, f a ≤ f b ↔ f' b ≤ f' a) : s.argmin f = s.argmax f' := by
  ext a; simp only [mem_argmin, mem_argmax]
  exact and_congr_right fun ha ↦ forall₂_congr fun b hb ↦ h a ha b hb

/-- Membership in an argmax over `univ`, through a surjection: `a` maximizes
`φ ∘ e` iff `e a` maximizes `φ`. Collapses argmax over a function space to
argmax over values when the objective factors through evaluation. -/
theorem mem_argmax_comp_surjective {α' : Type*} [Fintype α] [Fintype α']
    {e : α → α'} (he : Function.Surjective e) (φ : α' → β) {a : α} :
    a ∈ Finset.univ.argmax (φ ∘ e) ↔ e a ∈ Finset.univ.argmax φ := by
  simp only [mem_argmax, Finset.mem_univ, true_and, Function.comp_apply]
  exact ⟨fun h b ↦ (he b).elim fun a' hb ↦ hb ▸ h a',
    fun h a' ↦ h (e a')⟩

/-- The argmax is the singleton `{a}` iff `a ∈ s` beats every other element of `s`. -/
@[to_dual /-- The argmin is the singleton `{a}` iff `a ∈ s` beats every other element of `s`. -/]
theorem argmax_eq_singleton_iff : s.argmax f = {a} ↔ a ∈ s ∧ ∀ b ∈ s, b ≠ a → f b < f a := by
  refine ⟨fun h ↦ ?_, fun ⟨ha, h⟩ ↦ ?_⟩
  · have ha := mem_argmax.1 (h ▸ mem_singleton_self a)
    refine ⟨ha.1, fun b hb hba ↦ lt_of_le_not_ge (ha.2 b hb) fun hle ↦ hba ?_⟩
    simpa [h] using mem_argmax.2 ⟨hb, fun c hc ↦ (ha.2 c hc).trans hle⟩
  · ext b
    simp only [mem_argmax, mem_singleton]
    refine ⟨fun ⟨hb, hmax⟩ ↦ by_contra fun hba ↦ (h b hb hba).not_ge (hmax a ha), ?_⟩
    rintro rfl
    exact ⟨ha, fun c hc ↦ (eq_or_ne c b).elim (fun h ↦ h ▸ le_rfl) fun hcb ↦ (h c hc hcb).le⟩

section Total

variable [Std.Total (α := β) (· ≤ ·)]

/-- In a total preorder, a nonempty finset has a maximizer. -/
@[to_dual /-- In a total preorder, a nonempty finset has a minimizer. -/]
theorem argmax_nonempty (hs : s.Nonempty) : (s.argmax f).Nonempty := by
  obtain ⟨a, ha, h⟩ := s.exists_maximalFor f hs
  exact ⟨a, mem_argmax.2 ⟨ha, fun b hb ↦ (total_of (· ≤ ·) (f b) (f a)).elim id (h hb)⟩⟩

end Total

end Preorder

section LinearOrder

variable [LinearOrder β] [LinearOrder γ]

/-- The argmax of a score that is positive on a nonempty `t ⊆ s` and zero on
the rest of `s` is the argmax over `t`. -/
theorem argmax_eq_argmax_of_support [Zero β] {t : Finset α} (hts : t ⊆ s) (hne : t.Nonempty)
    (hpos : ∀ a ∈ t, 0 < f a) (hzero : ∀ a ∈ s, a ∉ t → f a = 0) : s.argmax f = t.argmax f := by
  obtain ⟨a₀, ha₀⟩ := hne
  ext a; simp only [mem_argmax]
  constructor
  · rintro ⟨ha, hmax⟩
    have hat : a ∈ t := by
      by_contra hat
      exact absurd (hmax a₀ (hts ha₀)) (not_le.mpr ((hzero a ha hat).symm ▸ hpos a₀ ha₀))
    exact ⟨hat, fun b hb ↦ hmax b (hts hb)⟩
  · rintro ⟨hat, hmax⟩
    refine ⟨hts hat, fun b hb ↦ ?_⟩
    by_cases hbt : b ∈ t
    · exact hmax b hbt
    · exact (hzero b hb hbt).symm ▸ (hpos a hat).le

/-- The argmax set is invariant under strictly monotone rescaling of the
score — inverse-temperature changes do not move the argmax. -/
theorem argmax_comp_strictMono {g : β → γ} (hg : StrictMono g) :
    s.argmax (g ∘ f) = s.argmax f := by
  ext a
  simp only [mem_argmax, Function.comp_apply, hg.le_iff_le]

/-- Membership in the argmax of a coordinatewise sum over a finite pi type:
`g` maximizes `∑ i, φ i (g i)` iff every coordinate maximizes its own
summand. The additive-separability workhorse for best responses in games. -/
theorem mem_argmax_pi_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Y : ι → Type*} [∀ i, Fintype (Y i)] {K : Type*} [AddCommMonoid K]
    [LinearOrder K] [IsOrderedCancelAddMonoid K]
    (φ : ∀ i, Y i → K) {g : ∀ i, Y i} :
    g ∈ Finset.univ.argmax (fun g' : (∀ i, Y i) ↦ ∑ i, φ i (g' i)) ↔
      ∀ i, g i ∈ Finset.univ.argmax (φ i) := by
  simp only [mem_argmax, Finset.mem_univ, true_and, true_implies]
  refine ⟨fun h i b ↦ ?_, fun h g' ↦ Finset.sum_le_sum fun i _ ↦ h i (g' i)⟩
  have key := h (Function.update g i b)
  simp only [Function.apply_update (fun k y ↦ φ k y)] at key
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.erase_eq,
    ← Finset.add_sum_erase _ (fun k ↦ φ k (g k)) (Finset.mem_univ i)] at key
  exact le_of_add_le_add_right key

end LinearOrder

end Finset
