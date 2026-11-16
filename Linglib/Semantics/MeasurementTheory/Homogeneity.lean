module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.Fin.Basic
public import Linglib.Semantics.MeasurementTheory.Invariance

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Homogeneity and uniqueness of order automorphisms

A set of order automorphisms of a linear order is `M`-point homogeneous when it carries any
increasing `M`-tuple to any other, and `N`-point unique when two members agreeing at `N` points
are equal. The largest such `M` and the least such `N` are what measurement theory calls the
scale type of a totally ordered structure, read from its automorphisms. An ordered group acting on
itself by translation is [`1`-point homogeneous](##isPointHomogeneous_one_range_mulLeft) and
[`1`-point unique](##isPointUnique_one_range_mulLeft), the ratio and difference scales. The
positive affine maps of an ordered field have [homogeneity](##homogeneity_positiveAffine) and
[uniqueness](##uniqueness_positiveAffine) `2`, the interval scale. All its order automorphisms are
[homogeneous at every length](##isPointHomogeneous_univ) and [unique at
none](##not_isPointUnique_univ), the ordinal scale.

## Implementation notes

Homogeneity and uniqueness are properties of a set of order automorphisms of a linear order, so
each kind of structure names its automorphisms and no type of relational structures is needed. On
an order with fewer than `M` elements every set is vacuously `M`-point homogeneous.

## References

* [luce-krantz-suppes-tversky-1990]
* [stevens-1946]
-/

@[expose] public section

open Set

variable {A : Type*} [LinearOrder A] {S T : Set (A ≃o A)} {M N : ℕ}

/-! ### Homogeneity and uniqueness -/

/-- A set of order automorphisms is `M`-point homogeneous when it carries any increasing
`M`-tuple to any other. -/
-- [luce-krantz-suppes-tversky-1990] Definition 20.1, p. 115
def IsPointHomogeneous (S : Set (A ≃o A)) (M : ℕ) : Prop :=
  ∀ a b : Fin M → A, StrictMono a → StrictMono b → ∃ g ∈ S, ∀ i, g (a i) = b i

/-- A set of order automorphisms is `N`-point unique when two of its members that agree at `N`
points are equal. -/
-- [luce-krantz-suppes-tversky-1990] Definition 20.1, p. 116
def IsPointUnique (S : Set (A ≃o A)) (N : ℕ) : Prop :=
  ∀ g ∈ S, ∀ h ∈ S, ∀ a : Fin N → A, StrictMono a → (∀ i, g (a i) = h (a i)) → g = h

theorem IsPointHomogeneous.mono (h : S ⊆ T) (hS : IsPointHomogeneous S M) :
    IsPointHomogeneous T M := fun a b ha hb ↦
  let ⟨g, hg, hgab⟩ := hS a b ha hb
  ⟨g, h hg, hgab⟩

theorem IsPointUnique.anti (h : S ⊆ T) (hT : IsPointUnique T N) : IsPointUnique S N :=
  fun g hg k hk ↦ hT g (h hg) k (h hk)

theorem IsPointUnique.succ (h : IsPointUnique S N) : IsPointUnique S (N + 1) :=
  fun g hg k hk a ha hgk ↦
    h g hg k hk (a ∘ Fin.castSucc) (ha.comp Fin.strictMono_castSucc) fun _ ↦ hgk _

theorem IsPointUnique.of_le (h : IsPointUnique S M) (hMN : M ≤ N) : IsPointUnique S N :=
  Nat.le_induction h (fun _ _ ih ↦ ih.succ) N hMN

private theorem strictMono_snoc {a : Fin M → A} (ha : StrictMono a) {x : A} (hx : ∀ i, a i < x) :
    StrictMono (Fin.snoc (α := fun _ ↦ A) a x) := by
  intro i j hij
  induction i using Fin.lastCases with
  | last => exact absurd hij (Fin.le_last j).not_gt
  | cast i =>
    induction j using Fin.lastCases with
    | last => simpa using hx i
    | cast j => simpa using ha (Fin.castSucc_lt_castSucc_iff.1 hij)

private theorem exists_forall_lt [Nonempty A] [NoMaxOrder A] (a : Fin M → A) : ∃ x, ∀ i, a i < x :=
  let ⟨c, hc⟩ := (finite_range a).bddAbove
  let ⟨x, hx⟩ := exists_gt c
  ⟨x, fun i ↦ (hc (mem_range_self i)).trans_lt hx⟩

theorem IsPointHomogeneous.pred [Nonempty A] [NoMaxOrder A] (h : IsPointHomogeneous S (M + 1)) :
    IsPointHomogeneous S M := by
  intro a b ha hb
  obtain ⟨x, hx⟩ := exists_forall_lt a
  obtain ⟨y, hy⟩ := exists_forall_lt b
  obtain ⟨g, hg, hgab⟩ := h _ _ (strictMono_snoc ha hx) (strictMono_snoc hb hy)
  exact ⟨g, hg, fun i ↦ by simpa using hgab i.castSucc⟩

theorem IsPointHomogeneous.of_le [Nonempty A] [NoMaxOrder A] (h : IsPointHomogeneous S N)
    (hMN : M ≤ N) : IsPointHomogeneous S M := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hMN
  induction k with
  | zero => exact h
  | succ k ih => exact ih h.pred (Nat.le_add_right _ _)

/-- The largest degree of homogeneity of a set of order automorphisms. -/
noncomputable def homogeneity (S : Set (A ≃o A)) : ℕ∞ :=
  ⨆ (M : ℕ) (_ : IsPointHomogeneous S M), (M : ℕ∞)

/-- The least degree of uniqueness of a set of order automorphisms. -/
noncomputable def uniqueness (S : Set (A ≃o A)) : ℕ∞ :=
  ⨅ (N : ℕ) (_ : IsPointUnique S N), (N : ℕ∞)

theorem homogeneity_eq [Nonempty A] [NoMaxOrder A] (h : IsPointHomogeneous S M)
    (h' : ¬ IsPointHomogeneous S (M + 1)) : homogeneity S = M :=
  le_antisymm (iSup₂_le fun _ hm ↦ Nat.cast_le.2 (not_lt.1 fun hlt ↦ h' (hm.of_le hlt)))
    (le_iSup₂ (f := fun (M : ℕ) (_ : IsPointHomogeneous S M) ↦ (M : ℕ∞)) M h)

theorem uniqueness_eq (h : IsPointUnique S (N + 1)) (h' : ¬ IsPointUnique S N) :
    uniqueness S = (N + 1 : ℕ) :=
  le_antisymm (iInf₂_le (f := fun (N : ℕ) (_ : IsPointUnique S N) ↦ (N : ℕ∞)) (N + 1) h)
    (le_iInf₂ fun _ hn ↦ Nat.cast_le.2 (not_lt.1 fun hlt ↦ h' (hn.of_le (Nat.lt_succ_iff.1 hlt))))

theorem uniqueness_eq_top (h : ∀ N, ¬ IsPointUnique S N) : uniqueness S = ⊤ :=
  iInf₂_eq_top.2 fun N hN ↦ absurd hN (h N)

/-! ### Ratio and difference scales -/

section Group

variable {G : Type*} [Group G] [LinearOrder G] [MulLeftMono G]

/-- An ordered group acting on itself by translation is `1`-point homogeneous. -/
@[to_additive isPointHomogeneous_one_range_addLeft /-- An ordered additive group acting on itself
by translation is `1`-point homogeneous. -/]
theorem isPointHomogeneous_one_range_mulLeft :
    IsPointHomogeneous (range (OrderIso.mulLeft : G → G ≃o G)) 1 := fun a b _ _ ↦
  ⟨_, ⟨b 0 * (a 0)⁻¹, rfl⟩, fun i ↦ by rw [Subsingleton.elim i 0]; simp⟩

/-- An ordered group acting on itself by translation is `1`-point unique. -/
@[to_additive isPointUnique_one_range_addLeft /-- An ordered additive group acting on itself by
translation is `1`-point unique. -/]
theorem isPointUnique_one_range_mulLeft :
    IsPointUnique (range (OrderIso.mulLeft : G → G ≃o G)) 1 := by
  rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩ a _ h
  have := h 0
  simp only [OrderIso.mulLeft_apply, mul_left_inj] at this
  rw [this]

end Group

section Field

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Interval scales -/

/-- The map `x ↦ a * x + b` with `0 < a`, as an order automorphism. -/
private def affineIso (a : K) (ha : 0 < a) (b : K) : K ≃o K where
  toFun x := a * x + b
  invFun y := (y - b) / a
  left_inv x := by simp [ha.ne']
  right_inv y := by simp [ha.ne', mul_div_cancel₀]
  map_rel_iff' {x y} := by simp [mul_le_mul_iff_of_pos_left ha]

theorem isPointHomogeneous_two_positiveAffine :
    IsPointHomogeneous (positiveAffine : Set (K ≃o K)) 2 := by
  intro p q hp hq
  have hp' : 0 < p 1 - p 0 := sub_pos.2 (hp (by decide))
  have hq' : 0 < q 1 - q 0 := sub_pos.2 (hq (by decide))
  refine ⟨affineIso ((q 1 - q 0) / (p 1 - p 0)) (div_pos hq' hp')
    (q 0 - (q 1 - q 0) / (p 1 - p 0) * p 0), ⟨_, div_pos hq' hp', _, fun _ ↦ rfl⟩, ?_⟩
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · show (q 1 - q 0) / (p 1 - p 0) * p 0 + (q 0 - (q 1 - q 0) / (p 1 - p 0) * p 0) = q 0
    ring
  · show (q 1 - q 0) / (p 1 - p 0) * p 1 + (q 0 - (q 1 - q 0) / (p 1 - p 0) * p 0) = q 1
    field_simp
    ring

theorem isPointUnique_two_positiveAffine : IsPointUnique (positiveAffine : Set (K ≃o K)) 2 := by
  rintro g ⟨a, -, b, hg⟩ h ⟨c, -, d, hh⟩ p hp hgh
  have hp' : 0 < p 1 - p 0 := sub_pos.2 (hp (by decide))
  have e₀ := hgh 0
  have e₁ := hgh 1
  rw [hg, hh] at e₀ e₁
  have hac : a = c := by
    have : (a - c) * (p 1 - p 0) = 0 := by linear_combination e₁ - e₀
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hp'.ne')
  subst hac
  have hbd : b = d := by linear_combination e₀
  exact DFunLike.ext _ _ fun x ↦ by rw [hg, hh, hbd]

theorem not_isPointHomogeneous_three_positiveAffine :
    ¬ IsPointHomogeneous (positiveAffine : Set (K ≃o K)) 3 := by
  intro h
  obtain ⟨g, ⟨a, -, b, hg⟩, hgab⟩ := h (fun i ↦ ((i.1 : ℕ) : K)) (fun i ↦ ((i.1 ^ 2 : ℕ) : K))
    (fun i j hij ↦ Nat.cast_lt.2 hij)
    (fun i j hij ↦ Nat.cast_lt.2 (Nat.pow_lt_pow_left hij two_ne_zero))
  have e₀ := hgab 0
  have e₁ := hgab 1
  have e₂ := hgab 2
  simp only [hg] at e₀ e₁ e₂
  norm_num [Fin.val_one, Fin.val_two] at e₀ e₁ e₂
  linarith

theorem not_isPointUnique_one_positiveAffine :
    ¬ IsPointUnique (positiveAffine : Set (K ≃o K)) 1 := by
  intro h
  have := h (affineIso 1 one_pos 0) ⟨1, one_pos, 0, fun _ ↦ rfl⟩
    (affineIso 2 two_pos 0) ⟨2, two_pos, 0, fun _ ↦ rfl⟩ (fun _ ↦ 0) (Subsingleton.strictMono _)
    (fun _ ↦ by simp [affineIso])
  have := congrArg (fun g : K ≃o K ↦ g 1) this
  simp [affineIso] at this

/-- The positive affine maps carry any two points to any two, in order, and no three. -/
theorem homogeneity_positiveAffine : homogeneity (positiveAffine : Set (K ≃o K)) = 2 :=
  homogeneity_eq isPointHomogeneous_two_positiveAffine not_isPointHomogeneous_three_positiveAffine

/-- A positive affine map is fixed by its values at two points, and not by its value at one. -/
theorem uniqueness_positiveAffine : uniqueness (positiveAffine : Set (K ≃o K)) = 2 :=
  uniqueness_eq isPointUnique_two_positiveAffine not_isPointUnique_one_positiveAffine

/-! ### Ordinal scales -/

/-- The order automorphism fixing everything up to `p` and stretching by `r` above it. -/
private def bendIso (p r : K) (hr : 0 < r) : K ≃o K where
  toFun x := if x ≤ p then x else p + r * (x - p)
  invFun y := if y ≤ p then y else p + (y - p) / r
  left_inv x := by
    by_cases h : x ≤ p
    · simp [h]
    · have : ¬ p + r * (x - p) ≤ p := by nlinarith [mul_pos hr (sub_pos.2 (not_le.1 h))]
      simp [h, this, hr.ne']
  right_inv y := by
    by_cases h : y ≤ p
    · simp [h]
    · have : ¬ p + (y - p) / r ≤ p := by
        have := div_pos (sub_pos.2 (not_le.1 h)) hr
        linarith
      simp [h, this, hr.ne', mul_div_cancel₀]
  map_rel_iff' {x y} := by
    change (if x ≤ p then x else p + r * (x - p)) ≤ (if y ≤ p then y else p + r * (y - p)) ↔ x ≤ y
    split_ifs with hx hy hy
    · rfl
    · have := mul_pos hr (sub_pos.2 (not_le.1 hy))
      exact ⟨fun _ ↦ hx.trans (not_le.1 hy).le, fun _ ↦ by linarith⟩
    · have := mul_pos hr (sub_pos.2 (not_le.1 hx))
      exact ⟨fun h ↦ by linarith, fun h ↦ absurd (h.trans hy) hx⟩
    · rw [add_le_add_iff_left, mul_le_mul_iff_of_pos_left hr, sub_le_sub_iff_right]

private theorem bendIso_apply (p r : K) (hr : 0 < r) (x : K) :
    bendIso p r hr x = if x ≤ p then x else p + r * (x - p) :=
  rfl

/-- The order automorphisms of an ordered field carry any increasing tuple to any other. -/
theorem isPointHomogeneous_univ (M : ℕ) : IsPointHomogeneous (univ : Set (K ≃o K)) M := by
  induction M with
  | zero => exact fun _ _ _ _ ↦ ⟨OrderIso.refl K, mem_univ _, fun i ↦ i.elim0⟩
  | succ M ih =>
    intro a b ha hb
    obtain ⟨g, -, hg⟩ := ih (a ∘ Fin.castSucc) (b ∘ Fin.castSucc)
      (ha.comp Fin.strictMono_castSucc) (hb.comp Fin.strictMono_castSucc)
    replace hg : ∀ i : Fin M, g (a i.castSucc) = b i.castSucc := hg
    rcases M with _ | M
    · refine ⟨affineIso 1 one_pos (b 0 - a 0), mem_univ _, fun i ↦ ?_⟩
      obtain rfl : i = 0 := Fin.eq_zero i
      show 1 * a 0 + (b 0 - a 0) = b 0
      ring
    · have hpq : b (Fin.last M).castSucc < g (a (Fin.last (M + 1))) := by
        rw [← hg (Fin.last M)]
        exact g.strictMono (ha (Fin.castSucc_lt_last _))
      have hpq' : b (Fin.last M).castSucc < b (Fin.last (M + 1)) := hb (Fin.castSucc_lt_last _)
      refine ⟨g.trans (bendIso (b (Fin.last M).castSucc) _
        (div_pos (sub_pos.2 hpq') (sub_pos.2 hpq))), mem_univ _, fun i ↦ ?_⟩
      induction i using Fin.lastCases with
      | last =>
        have hpq'' := hpq.not_ge
        rw [OrderIso.trans_apply, bendIso_apply]
        split_ifs
        rw [div_mul_cancel₀ _ (sub_pos.2 hpq).ne']
        ring
      | cast i =>
        have hi : g (a i.castSucc) = b i.castSucc := hg i
        have hle : b i.castSucc ≤ b (Fin.last M).castSucc :=
          hb.monotone (Fin.castSucc_le_castSucc_iff.2 (Fin.le_last i))
        rw [OrderIso.trans_apply, hi, bendIso_apply]
        split_ifs
        rfl

/-- No finite number of points determines an order automorphism of an ordered field. -/
theorem not_isPointUnique_univ (N : ℕ) : ¬ IsPointUnique (univ : Set (K ≃o K)) N := by
  intro h
  have := h (OrderIso.refl K) (mem_univ _) (bendIso N 2 two_pos) (mem_univ _)
    (fun i ↦ ((i.1 : ℕ) : K)) (fun i j hij ↦ Nat.cast_lt.2 hij) fun i ↦ by
      have hle : ((i.1 : ℕ) : K) ≤ N := Nat.cast_le.2 i.2.le
      rw [bendIso_apply]
      split_ifs
      rfl
  have := congrArg (fun g : K ≃o K ↦ g (N + 1)) this
  norm_num [bendIso_apply] at this

theorem homogeneity_univ : homogeneity (univ : Set (K ≃o K)) = ⊤ :=
  ENat.eq_top_iff_forall_ge.2 fun n ↦
    le_iSup₂ (f := fun (M : ℕ) (_ : IsPointHomogeneous (univ : Set (K ≃o K)) M) ↦ (M : ℕ∞)) n
      (isPointHomogeneous_univ n)

theorem uniqueness_univ : uniqueness (univ : Set (K ≃o K)) = ⊤ :=
  uniqueness_eq_top not_isPointUnique_univ

end Field
