module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Algebra.Order.GroupWithZero.OrderIso
public import Mathlib.Algebra.Order.Positive.Field
public import Mathlib.Data.Fin.VecNotation
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
increasing `M`-tuple to any other, and `N`-point unique when two members agreeing at `N` points are
equal. The largest such `M` and the least such `N` are what measurement theory calls the scale type
of a totally ordered structure, read from its automorphisms. A nontrivial ordered group acting on
itself by translation has [homogeneity](##MeasurementTheory.homogeneity_range_mulLeft) and
[uniqueness](##MeasurementTheory.uniqueness_range_mulLeft) `1`. That is the difference scale,
and it is the ratio scale on positive degrees, where [the similarities are the translations of the
multiplicative group](##MeasurementTheory.range_mulLeft_eq_setOf_similarity). On a whole ordered
field the similarities fix zero, and have [homogeneity
`0`](##MeasurementTheory.homogeneity_similarity) and [uniqueness
`2`](##MeasurementTheory.uniqueness_similarity). The positive affine maps of an ordered field have
[homogeneity](##MeasurementTheory.homogeneity_positiveAffine) and
[uniqueness](##MeasurementTheory.uniqueness_positiveAffine) `2`, the interval scale. All its order
automorphisms are [homogeneous at every length](##MeasurementTheory.isPointHomogeneous_univ) and
[unique at none](##MeasurementTheory.not_isPointUnique_univ), the ordinal scale.

## Implementation notes

Homogeneity and uniqueness are properties of a set of order automorphisms of a linear order, so
each kind of structure names its automorphisms and no type of relational structures is needed. On
an order with fewer than `M` elements every set is vacuously `M`-point homogeneous, so that on a
finite order `homogeneity` is `⊤`.

## References

* [luce-krantz-suppes-tversky-1990]
* [stevens-1946]
-/

@[expose] public section

open Set

namespace MeasurementTheory

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

section CommGroup

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [Nontrivial G]

@[to_additive]
theorem not_isPointHomogeneous_two_range_mulLeft :
    ¬ IsPointHomogeneous (range (OrderIso.mulLeft : G → G ≃o G)) 2 := by
  intro h
  obtain ⟨c, hc⟩ := exists_one_lt' (α := G)
  have hcc : c < c * c := by simpa using hc
  obtain ⟨_, ⟨r, rfl⟩, hr⟩ := h ![1, c] ![1, c * c]
    (Fin.strictMono_iff_lt_succ.2 fun i ↦ by rw [Fin.fin_one_eq_zero i]; simpa using hc)
    (Fin.strictMono_iff_lt_succ.2 fun i ↦ by
      rw [Fin.fin_one_eq_zero i]; simpa using hc.trans hcc)
  have h₀ : r = 1 := by simpa using hr 0
  have h₁ : r * c = c * c := by simpa using hr 1
  rw [h₀, one_mul] at h₁
  exact hcc.ne h₁

@[to_additive]
theorem not_isPointUnique_zero_range_mulLeft :
    ¬ IsPointUnique (range (OrderIso.mulLeft : G → G ≃o G)) 0 := by
  intro h
  obtain ⟨c, hc⟩ := exists_one_lt' (α := G)
  have := h _ ⟨1, rfl⟩ _ ⟨c, rfl⟩ Fin.elim0 (fun i ↦ i.elim0) fun i ↦ i.elim0
  have := congrArg (fun g : G ≃o G ↦ g 1) this
  simp only [OrderIso.mulLeft_apply, mul_one] at this
  exact hc.ne this

/-- A nontrivial ordered group acting on itself by translation carries any point to any other and
no two to any two. -/
@[to_additive /-- A nontrivial ordered additive group acting on itself
by translation carries any point to any other and no two to any two. -/]
theorem homogeneity_range_mulLeft :
    homogeneity (range (OrderIso.mulLeft : G → G ≃o G)) = 1 := by
  simpa using homogeneity_eq isPointHomogeneous_one_range_mulLeft
    (not_isPointHomogeneous_two_range_mulLeft (G := G))

/-- A translation of a nontrivial ordered group is fixed by its value at one point. -/
@[to_additive /-- A translation of a nontrivial ordered additive group is
fixed by its value at one point. -/]
theorem uniqueness_range_mulLeft :
    uniqueness (range (OrderIso.mulLeft : G → G ≃o G)) = 1 := by
  simpa using uniqueness_eq isPointUnique_one_range_mulLeft
    (not_isPointUnique_zero_range_mulLeft (G := G))

end CommGroup

section Field

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Interval scales -/

/-- The map `x ↦ a * x + b` with `0 < a`, as an order automorphism. -/
private def affineIso (a : K) (ha : 0 < a) (b : K) : K ≃o K :=
  (OrderIso.mulLeft₀ a ha).trans (OrderIso.addRight b)

private theorem affineIso_apply (a : K) (ha : 0 < a) (b x : K) :
    affineIso a ha b x = a * x + b := by
  simp [affineIso]

theorem isPointHomogeneous_two_positiveAffine :
    IsPointHomogeneous (positiveAffine : Set (K ≃o K)) 2 := by
  intro p q hp hq
  have hp' : 0 < p 1 - p 0 := sub_pos.2 (hp (by decide))
  have hq' : 0 < q 1 - q 0 := sub_pos.2 (hq (by decide))
  refine ⟨affineIso ((q 1 - q 0) / (p 1 - p 0)) (div_pos hq' hp')
    (q 0 - (q 1 - q 0) / (p 1 - p 0) * p 0),
    ⟨_, div_pos hq' hp', _, affineIso_apply _ _ _⟩, ?_⟩
  rw [Fin.forall_fin_two, affineIso_apply, affineIso_apply]
  refine ⟨by ring, ?_⟩
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

theorem not_isPointUnique_one_similarity : ¬ IsPointUnique (similarity : Set (K ≃o K)) 1 := by
  intro h
  have := h (affineIso 1 one_pos 0) ⟨1, one_pos, fun _ ↦ by simp [affineIso_apply]⟩
    (affineIso 2 two_pos 0) ⟨2, two_pos, fun _ ↦ by simp [affineIso_apply]⟩ (fun _ ↦ 0)
    (Subsingleton.strictMono _) (fun _ ↦ by simp [affineIso_apply])
  have := congrArg (fun g : K ≃o K ↦ g 1) this
  simp [affineIso_apply] at this

theorem not_isPointUnique_one_positiveAffine :
    ¬ IsPointUnique (positiveAffine : Set (K ≃o K)) 1 :=
  fun h ↦ not_isPointUnique_one_similarity (h.anti similarity_subset_positiveAffine)

/-- The positive affine maps carry any two points to any two, in order, and no three. -/
theorem homogeneity_positiveAffine : homogeneity (positiveAffine : Set (K ≃o K)) = 2 :=
  homogeneity_eq isPointHomogeneous_two_positiveAffine not_isPointHomogeneous_three_positiveAffine

/-- A positive affine map is fixed by its values at two points, and not by its value at one. -/
theorem uniqueness_positiveAffine : uniqueness (positiveAffine : Set (K ≃o K)) = 2 :=
  uniqueness_eq isPointUnique_two_positiveAffine not_isPointUnique_one_positiveAffine

/-! ### Similarities -/

theorem not_isPointHomogeneous_one_similarity :
    ¬ IsPointHomogeneous (similarity : Set (K ≃o K)) 1 := by
  intro h
  obtain ⟨g, ⟨a, -, hg⟩, hg'⟩ := h (fun _ ↦ 0) (fun _ ↦ 1) (Subsingleton.strictMono _)
    (Subsingleton.strictMono _)
  have := hg' 0
  rw [hg, mul_zero] at this
  exact zero_ne_one this

/-- On a whole ordered field the similarities fix zero, so they carry no point to every other. -/
theorem homogeneity_similarity : homogeneity (similarity : Set (K ≃o K)) = 0 := by
  have h₀ : IsPointHomogeneous (similarity : Set (K ≃o K)) 0 := fun _ _ _ _ ↦
    ⟨OrderIso.refl K, ⟨1, one_pos, fun t ↦ (one_mul t).symm⟩, fun i ↦ i.elim0⟩
  simpa using homogeneity_eq h₀ not_isPointHomogeneous_one_similarity

/-- A similarity of an ordered field is fixed by its values at two points, and not by its value at
one, since all agree at zero. -/
theorem uniqueness_similarity : uniqueness (similarity : Set (K ≃o K)) = 2 :=
  uniqueness_eq (isPointUnique_two_positiveAffine.anti similarity_subset_positiveAffine)
    not_isPointUnique_one_similarity

/-- On the positive degrees the similarities are the translations of the multiplicative group, so
that the ratio scale is the scale of an ordered group acting on itself. -/
theorem range_mulLeft_eq_setOf_similarity :
    range (OrderIso.mulLeft : {x : K // 0 < x} → {x : K // 0 < x} ≃o {x : K // 0 < x}) =
      {g | ∃ a : K, 0 < a ∧ ∀ t : {x : K // 0 < x}, (g t : K) = a * t} := by
  ext g
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, r.2, fun t ↦ by simp⟩
  · rintro ⟨a, ha, hg⟩
    exact ⟨⟨a, ha⟩, DFunLike.ext _ _ fun t ↦ Subtype.ext (by simp [hg])⟩

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
      rw [affineIso_apply]
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

end MeasurementTheory
