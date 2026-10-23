module

public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Phonology.HarmonicGrammar.Harmony
public import Linglib.Phonology.OptimalityTheory.Ranking
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.Algebra.Order.AddGroupWithTop

/-!
# Riggle (2009): Violation semirings in Optimality Theory

This file formalizes the paper's algebraic characterization of constraint violation. A
violation profile is a multiset over the constraint set, merge is multiset union, and
harmonic inequality under a ranking is the lexicographic order of the ranking's reading of
the profiles, `HarmonicLT`. The minimum under harmonic inequality and merge make the
violation semiring `V`, a tropical semiring over profiles with an infinitely bad profile as
the additive identity, whose commutative semiring structure is inherited from mathlib's
`MinTropical`. The semiring is idempotent and monotone, `le_mul`: merging can only make a
profile worse, which is the principle behind shortest-path optimization that every piece of
an optimal mapping is itself optimal, `Optimal.left_of_add`. Merge commutes with every
ranking's reading, `smul_add`, so the merged violations of a constraint set are one object
for all rankings and a ranking enters only through the minimum. A Harmonic Grammar
weighting is a homomorphism of the merge monoids into the tropical semiring of costs,
`tropWeight`.

## Implementation notes

Profiles are `ViolationProfile n`, whose lexicographic order is harmonic inequality under
the identity ranking; a ranking reads a profile through the action of
`OptimalityTheory.Ranking`, as the tableau substrate does. The weighted same-length
transducers of the paper's sections 3 and 4, their intersection, and the complexity bound
of the H-Opt algorithm are not formalized.

## References

* [J. Riggle, *Violation Semirings in Optimality Theory* (2009)][riggle-2009b]
* [E. W. Dijkstra, *A note on two problems in connexion with graphs* (1959)][dijkstra-1959]
* [A. Prince, P. Smolensky, *Optimality Theory: constraint interaction in generative
  grammar* (1993)][prince-smolensky-1993]
* [P. Smolensky, G. Legendre, *The harmonic mind: from neural computation to
  Optimality-Theoretic grammar* (2006)][smolensky-legendre-2006]
-/

@[expose] public section

namespace Riggle2009b

open OptimalityTheory HarmonicGrammar MinTropical Pointwise

variable {n : ℕ}

/-! ### Harmonic inequality and merge -/

/-- Harmonic inequality (Definition 1) under a ranking: the ranking's reading of `A` is
lexicographically below that of `B`, so `A` has fewer violations of the highest-ranked
constraint on which the two differ. -/
def HarmonicLT (r : Ranking (Fin n) n) (A B : ViolationProfile n) : Prop := r • A < r • B

theorem smul_add (r : Ranking (Fin n) n) (A B : ViolationProfile n) :
    r • (A + B) = r • A + r • B := rfl

theorem HarmonicLT.add_right {r : Ranking (Fin n) n} {A B : ViolationProfile n}
    (h : HarmonicLT r A B) (C : ViolationProfile n) : HarmonicLT r (A + C) (B + C) := by
  unfold HarmonicLT at *
  rw [smul_add, smul_add]
  exact add_lt_add_left h _

/-- A profile is optimal in a set under a ranking when it is minimal in the set for the
ranking's reading of profiles: no member is more harmonic. -/
abbrev Optimal (r : Ranking (Fin n) n) (S : Set (ViolationProfile n))
    (A : ViolationProfile n) : Prop :=
  MinimalFor (· ∈ S) (r • ·) A

theorem Optimal.left_of_add {r : Ranking (Fin n) n} {S T : Set (ViolationProfile n)}
    {A B : ViolationProfile n} (h : Optimal r (S + T) (A + B)) (hA : A ∈ S) (hB : B ∈ T) :
    Optimal r S A :=
  minimalFor_iff_forall_lt.2 ⟨hA, fun _ hlt hC ↦
    MinimalFor.not_lt h (Set.add_mem_add hC hB) (HarmonicLT.add_right hlt B)⟩

theorem Optimal.right_of_add {r : Ranking (Fin n) n} {S T : Set (ViolationProfile n)}
    {A B : ViolationProfile n} (h : Optimal r (S + T) (A + B)) (hA : A ∈ S) (hB : B ∈ T) :
    Optimal r T B := by
  rw [add_comm S, add_comm A] at h
  exact h.left_of_add hB hA

/-! ### The violation semiring -/

/-- The violation semiring (Example 2): profiles under the identity ranking together with
the infinitely bad profile `⊤`; tropical addition is the minimum under harmonic inequality,
tropical multiplication is merge, and the commutative semiring structure is mathlib's. -/
abbrev V (n : ℕ) := MinTropical (WithTop (ViolationProfile n))

theorem le_mul (a b : V n) : a ≤ a * b := by
  rw [← untrop_le_iff, untrop_mul]
  refine le_add_of_nonneg_right ?_
  induction untrop b using WithTop.recTopCoe with
  | top => exact le_top
  | coe x => exact WithTop.coe_le_coe.mpr bot_le

theorem add_mul_self (a b : V n) : a + a * b = a := add_eq_left (le_mul a b)

/-! ### Harmonic Grammar -/

/-- A weighting read as a homomorphism from the merge monoid of profiles to the additive
reals: the weighted violation sum. -/
def weightMap (w : Fin n → ℝ) : ViolationProfile n →+ ℝ where
  toFun v := w ⬝ᵥ (Nat.cast ∘ ofLex v)
  map_zero' := by
    show ∑ i, w i * ((0 : ℕ) : ℝ) = 0
    simp
  map_add' a b := by
    simp only [dotProduct, Function.comp_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by
      show w i * ((a i + b i : ℕ) : ℝ) = w i * (a i : ℝ) + w i * (b i : ℝ)
      push_cast
      exact mul_add _ _ _

/-- The weighting maps the violation semiring to the tropical semiring of costs (section 2),
preserving tropical multiplication and the identities; whether it also preserves the minimum
is the question of Harmonic Grammar's agreement with Optimality Theory, which the paper
does not raise. -/
def tropWeight (w : Fin n → ℝ) : V n →* MinTropical (WithTop ℝ) where
  toFun a := trop ((untrop a).map (weightMap w))
  map_one' := by simp
  map_mul' a b := by simp [untrop_mul, WithTop.map_add]

theorem tropWeight_zero (w : Fin n → ℝ) : tropWeight w 0 = 0 := by
  simp [tropWeight]

end Riggle2009b
