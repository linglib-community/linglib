module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Linarith

/-!
# Farkas' lemma over a linearly ordered field

`[UPSTREAM]` A finite system of linear inequalities `A *ᵥ x ≤ b` over a linearly ordered field
either has a solution or admits a certificate of infeasibility, a nonnegative combination `y` of
its rows with `y ᵥ* A = 0` and `y ⬝ᵥ b < 0`. Gordan's alternative follows: either a nonnegative
combination of the rows of `M` is positive in every column, or a probability vector `x` has
`M *ᵥ x ≤ 0`.

## Main statements

* `Matrix.farkas`: Farkas' lemma for `A *ᵥ x ≤ b`.
* `Matrix.gordan`: Gordan's alternative.

## Implementation notes

The proof is Fourier–Motzkin elimination. Eliminating the last variable multiplies the system on
the left by the nonnegative matrix `fmMatrix A`, whose rows keep each row of `A` with a zero last
coefficient and combine each row with a positive last coefficient with each row with a negative
one, so that the last column of `fmMatrix A * A` vanishes. A solution of the eliminated system
extends to the original one by placing the last variable between the bounds that the original
rows impose, and a certificate `y` for the eliminated system gives the certificate
`y ᵥ* fmMatrix A` for the original. Gordan's alternative states the simplex conditions
explicitly, since the file defining `stdSimplex` imports topology.
-/

@[expose] public section

namespace Matrix

open Finset

variable {K : Type*} [Field K] [LinearOrder K]

section FourierMotzkin

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- `fmMatrix A` eliminates the last variable of `A`. Row `inl i` keeps row `i` when its last
coefficient vanishes, and row `inr (p, q)` combines a row `p` with positive last coefficient and
a row `q` with negative last coefficient so that the last coefficient cancels. -/
private def fmMatrix (A : Matrix ι (Fin (n + 1)) K) : Matrix (ι ⊕ ι × ι) ι K :=
  of fun r k ↦ match r with
    | .inl i => if A i (Fin.last n) = 0 ∧ k = i then 1 else 0
    | .inr (p, q) => if 0 < A p (Fin.last n) ∧ A q (Fin.last n) < 0 then
        (if k = p then -A q (Fin.last n) else 0) + (if k = q then A p (Fin.last n) else 0)
      else 0

private lemma fmMatrix_mulVec_inl (A : Matrix ι (Fin (n + 1)) K) (v : ι → K) (i : ι) :
    (fmMatrix A *ᵥ v) (.inl i) = if A i (Fin.last n) = 0 then v i else 0 := by
  simp only [mulVec, dotProduct, fmMatrix, of_apply]
  split_ifs with h <;> simp [h]

private lemma fmMatrix_mulVec_inr (A : Matrix ι (Fin (n + 1)) K) (v : ι → K) (p q : ι) :
    (fmMatrix A *ᵥ v) (.inr (p, q)) = if 0 < A p (Fin.last n) ∧ A q (Fin.last n) < 0 then
      -A q (Fin.last n) * v p + A p (Fin.last n) * v q else 0 := by
  simp only [mulVec, dotProduct, fmMatrix, of_apply]
  split_ifs with h <;> simp [add_mul, sum_add_distrib]

private lemma fmMatrix_mul_last (A : Matrix ι (Fin (n + 1)) K) (r : ι ⊕ ι × ι) :
    (fmMatrix A * A) r (Fin.last n) = 0 := by
  have h : (fmMatrix A * A) r (Fin.last n) = (fmMatrix A *ᵥ fun k ↦ A k (Fin.last n)) r := rfl
  rw [h]
  rcases r with i | ⟨p, q⟩
  · rw [fmMatrix_mulVec_inl]; split_ifs with h' <;> simp [h']
  · rw [fmMatrix_mulVec_inr]; split_ifs <;> ring

/-- `fmLhs A` is the eliminated system on the first `n` variables. -/
private def fmLhs (A : Matrix ι (Fin (n + 1)) K) : Matrix (ι ⊕ ι × ι) (Fin n) K :=
  (fmMatrix A * A).submatrix id Fin.castSucc

private lemma fmLhs_mulVec (A : Matrix ι (Fin (n + 1)) K) (x : Fin n → K) :
    fmLhs A *ᵥ x = fmMatrix A *ᵥ (A.submatrix id Fin.castSucc *ᵥ x) := by
  rw [mulVec_mulVec]; rfl

private lemma exists_between_finset {α : Type*} {s t : Finset α} (f g : α → K)
    (h : ∀ a ∈ s, ∀ b ∈ t, f a ≤ g b) : ∃ x, (∀ a ∈ s, f a ≤ x) ∧ ∀ b ∈ t, x ≤ g b := by
  by_cases hs : s.Nonempty
  · exact ⟨s.sup' hs f, fun a ha ↦ le_sup' f ha,
      fun b hb ↦ sup'_le hs f fun a ha ↦ h a ha b hb⟩
  by_cases ht : t.Nonempty
  · exact ⟨t.inf' ht g, fun a ha ↦ (hs ⟨a, ha⟩).elim, fun b hb ↦ inf'_le g hb⟩
  · exact ⟨0, fun a ha ↦ (hs ⟨a, ha⟩).elim, fun b hb ↦ (ht ⟨b, hb⟩).elim⟩

variable [IsStrictOrderedRing K]

omit [Fintype ι] in
private lemma fmMatrix_nonneg (A : Matrix ι (Fin (n + 1)) K) (r : ι ⊕ ι × ι) (k : ι) :
    0 ≤ fmMatrix A r k := by
  rcases r with i | ⟨p, q⟩ <;> simp only [fmMatrix, of_apply]
  · split_ifs <;> norm_num
  by_cases h : 0 < A p (Fin.last n) ∧ A q (Fin.last n) < 0
  · simp only [h, and_self, ite_true]
    exact add_nonneg (by split_ifs <;> linarith [h.2]) (by split_ifs <;> linarith [h.1])
  · simp [h]

private lemma exists_mulVec_le_of_fmLhs {A : Matrix ι (Fin (n + 1)) K} {b : ι → K}
    {x : Fin n → K} (hx : fmLhs A *ᵥ x ≤ fmMatrix A *ᵥ b) : ∃ x, A *ᵥ x ≤ b := by
  set r : ι → K := A.submatrix id Fin.castSucc *ᵥ x with hr
  have hrow : ∀ t i, (A *ᵥ Fin.snoc x t) i = r i + A i (Fin.last n) * t := fun t i ↦ by
    simp [hr, mulVec, dotProduct, Fin.sum_univ_castSucc]
  rw [fmLhs_mulVec] at hx
  -- the bounds `(b i - r i) / A i (Fin.last n)` are compatible
  obtain ⟨t, hlo, hup⟩ := exists_between_finset
    (s := {q | A q (Fin.last n) < 0}) (t := {p | 0 < A p (Fin.last n)})
    (fun i ↦ (b i - r i) / A i (Fin.last n)) (fun i ↦ (b i - r i) / A i (Fin.last n))
    fun q hq p hp ↦ by
      simp only [mem_filter, mem_univ, true_and] at hq hp
      have h := hx (.inr (p, q))
      simp only [fmMatrix_mulVec_inr, hp, hq, and_self, ite_true] at h
      rw [← neg_div_neg_eq, div_le_div_iff₀ (neg_pos.2 hq) hp]
      linarith
  refine ⟨Fin.snoc x t, fun i ↦ ?_⟩
  rw [hrow]
  rcases lt_trichotomy (A i (Fin.last n)) 0 with hi | hi | hi
  · have := hlo i (by simpa using hi)
    rw [div_le_iff_of_neg hi] at this
    linarith
  · have h := hx (.inl i)
    simp only [fmMatrix_mulVec_inl, hi, ite_true] at h
    rw [hi, zero_mul, add_zero]
    exact h
  · have := hup i (by simpa using hi)
    rw [le_div_iff₀ hi] at this
    linarith

private lemma exists_cert_of_fmLhs {A : Matrix ι (Fin (n + 1)) K} {b : ι → K}
    {y : ι ⊕ ι × ι → K} (hy : 0 ≤ y) (hyA : y ᵥ* fmLhs A = 0)
    (hyb : y ⬝ᵥ (fmMatrix A *ᵥ b) < 0) :
    ∃ y : ι → K, 0 ≤ y ∧ y ᵥ* A = 0 ∧ y ⬝ᵥ b < 0 := by
  refine ⟨y ᵥ* fmMatrix A, fun k ↦ sum_nonneg fun r _ ↦ mul_nonneg (hy r)
    (fmMatrix_nonneg A r k), ?_, by rwa [← dotProduct_mulVec]⟩
  rw [vecMul_vecMul]
  funext j
  refine Fin.lastCases ?_ (fun j ↦ ?_) j
  · simp [vecMul, dotProduct, fmMatrix_mul_last]
  · exact congrFun hyA j

private theorem farkas_fin : ∀ {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι (Fin n) K) (b : ι → K),
    (∃ x, A *ᵥ x ≤ b) ∨ ∃ y, 0 ≤ y ∧ y ᵥ* A = 0 ∧ y ⬝ᵥ b < 0
  | 0, ι, _, _, A, b => by
    by_cases h : 0 ≤ b
    · exact .inl ⟨0, by rwa [mulVec_zero]⟩
    obtain ⟨i, hi⟩ : ∃ i, b i < 0 := by simpa [Pi.le_def] using h
    exact .inr ⟨Pi.single i 1, Pi.single_nonneg.2 zero_le_one, funext fun j ↦ j.elim0,
      by simpa using hi⟩
  | n + 1, ι, _, _, A, b =>
    (farkas_fin (fmLhs A) (fmMatrix A *ᵥ b)).imp (fun ⟨_, hx⟩ ↦ exists_mulVec_le_of_fmLhs hx)
      fun ⟨_, hy, hyA, hyb⟩ ↦ exists_cert_of_fmLhs hy hyA hyb

end FourierMotzkin

variable [IsStrictOrderedRing K] {ι σ : Type*} [Fintype ι] [Fintype σ]

/-- **Farkas' lemma.** A finite system of linear inequalities `A *ᵥ x ≤ b` over a linearly
ordered field has a solution, or a nonnegative combination `y` of its rows has `y ᵥ* A = 0` and
`y ⬝ᵥ b < 0`. -/
theorem farkas (A : Matrix ι σ K) (b : ι → K) :
    (∃ x, A *ᵥ x ≤ b) ∨ ∃ y, 0 ≤ y ∧ y ᵥ* A = 0 ∧ y ⬝ᵥ b < 0 := by
  classical
  let e := Fintype.equivFin σ
  refine (farkas_fin (A.submatrix id e.symm) b).imp (fun ⟨x, hx⟩ ↦ ⟨x ∘ e, ?_⟩)
    fun ⟨y, hy, hyA, hyb⟩ ↦ ⟨y, hy, funext fun s ↦ ?_, hyb⟩
  · simpa [submatrix_mulVec_equiv] using hx
  · simpa [vecMul, dotProduct] using congrFun hyA (e s)

/-- **Gordan's alternative.** Either a nonnegative combination of the rows of `M` is positive in
every column, or a probability vector `x` has `M *ᵥ x ≤ 0`. -/
theorem gordan (M : Matrix ι σ K) :
    (∃ y, 0 ≤ y ∧ ∀ j, 0 < (y ᵥ* M) j) ∨ ∃ x, 0 ≤ x ∧ ∑ j, x j = 1 ∧ M *ᵥ x ≤ 0 := by
  classical
  -- the system `∑ x ≥ 1`, `x ≥ 0`, `M *ᵥ x ≤ 0`
  let A : Matrix (Option (σ ⊕ ι)) σ K := of fun r j ↦ match r with
    | none => -1
    | some (.inl k) => if j = k then -1 else 0
    | some (.inr i) => M i j
  let b : Option (σ ⊕ ι) → K := fun r ↦ match r with
    | none => -1
    | some _ => 0
  rcases farkas A b with ⟨x, hx⟩ | ⟨y, hy, hyA, hyb⟩
  · have h1 : 1 ≤ ∑ j, x j := by
      have := hx none
      simp only [A, b, mulVec, dotProduct, of_apply, neg_one_mul, sum_neg_distrib] at this
      linarith
    have hnn : ∀ k, 0 ≤ x k := fun k ↦ by
      have := hx (some (.inl k))
      simp [A, b, mulVec, dotProduct] at this
      linarith
    have hs : 0 < ∑ j, x j := by linarith
    refine .inr ⟨fun j ↦ x j / ∑ j, x j, fun j ↦ div_nonneg (hnn j) hs.le, ?_, fun i ↦ ?_⟩
    · rw [← sum_div, div_self hs.ne']
    · have := hx (some (.inr i))
      simp only [A, b, mulVec, dotProduct, of_apply] at this
      simp only [mulVec, dotProduct, Pi.zero_apply, mul_div_assoc', ← sum_div]
      exact div_nonpos_of_nonpos_of_nonneg this hs.le
  · have hnone : 0 < y none := by
      simp [b, dotProduct, Fintype.sum_option] at hyb
      linarith
    refine .inl ⟨fun i ↦ y (some (.inr i)), fun i ↦ hy _, fun j ↦ ?_⟩
    have h := congrFun hyA j
    simp [A, vecMul, dotProduct, Fintype.sum_option, Fintype.sum_sum_type] at h
    simp only [vecMul, dotProduct]
    linarith [show 0 ≤ y (some (.inl j)) from hy _]

end Matrix
