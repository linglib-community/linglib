/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Set.Semiring
public import Mathlib.Order.Concept
public import Linglib.Core.Algebra.Order.SupMonoid
public import Linglib.Core.Order.BoundedComplete

/-!
# Fine (2012): Counterfactuals without Possible Worlds

States are ordered by parthood, and the fusion of some states exists just in case they are
compatible: the order is bounded complete, with a null state `⊥`. With a failed fusion adjoined
the states form a commutative monoid with zero, `Fused S`, and a statement is verified by a set
of states, an element of `SetSemiring (Fused S)`: a conjunction `A * B` by the fusions of a
verifier of each conjunct, a disjunction `A + B + A * B` by the verifiers of either disjunct or
of their conjunction, `⊤` by the null state alone and `⊥` by nothing.

For a transition relation `outcome w t u`, saying that `u` is a possible outcome of imposing
the state `t` on the world `w`, the counterfactual `would outcome A C` is true at `w` when every
outcome at `w` of every exact verifier of `A` contains a verifier of `C`. It is the upper polar
of the verifiers of `A` along that relation. From the form of this clause alone the
counterfactual satisfies Inclusive Disjunction (`inclusive_disjunction`), Conjunction
(`conjunction`), Exact Strengthening, Inexact Weakening and Triviality; when outcomes contain
the state imposed it satisfies Identity, and when a state within a world has an outcome within
it, Modus Ponens (`modus_ponens`).

The paper begins from a derivation: for rocks each of which would topple the next and leave the
previous one standing, the rules Entailment, Substitution, Transitivity, Disjunction and
Conjunction yield that if some rock fell then none would (`rocks`). A conditional between
propositions, sets of worlds, satisfies Substitution of logical equivalents by its type, so the
derivation is a theorem about every such conditional; the conditional between sets of states
does not.

## Implementation notes

Bounded completeness is assumed for pairs of states; the paper assumes it for sets of states,
and infinitary conjunction of statements, which needs that, is not formalized. Statements are
unilateral, a set of verifiers, so negation, which the paper treats by falsifiers, is not
represented. Inexact Weakening is stated for a consequent each of whose verifiers contains a
verifier of the new consequent.

## References

* [fine-2012]
* [fine-2017a]
* [lewis-1973b]
-/

@[expose] public section

namespace Fine2012

open scoped IsBoundedComplete Pointwise

/-! ### The truth clause and its rules -/

section Clause

variable {S W : Type*} [PartialOrder S] [OrderBot S] [IsBoundedComplete S]

/-- States with a failed fusion adjoined, under fusion. -/
abbrev Fused (S : Type*) := SupMonoid (WithTop S)

/-- A state, among the fused states. -/
def st (t : S) : Fused S := SupMonoid.of (t : WithTop S)

theorem st_mul_st_eq_iff {a b c : S} : st a * st b = st c ↔ IsLUB {a, b} c :=
  IsBoundedComplete.coe_sup_coe_eq_coe_iff

/-- The state `u` inexactly verifies `C`: it contains an exact verifier. -/
def Inexact (C : SetSemiring (Fused S)) (u : S) : Prop := ∃ c, st c ∈ C.toSet ∧ c ≤ u

/-- `A > C` is true at `w` when `u` inexactly verifies `C` whenever `t` exactly verifies `A` and
`u` is a possible outcome of `t` at `w`. -/
def would (outcome : W → S → S → Prop) (A C : SetSemiring (Fused S)) : Set W :=
  upperPolar (fun a w ↦ ∀ t, a = st t → ∀ u, outcome w t u → Inexact C u) A.toSet

variable {outcome : W → S → S → Prop} {A A' B C C' : SetSemiring (Fused S)}

omit [OrderBot S] [IsBoundedComplete S] in
theorem would_add : would outcome (A + B) C = would outcome A C ∩ would outcome B C :=
  upperPolar_union ..

/-- Inclusive Disjunction, with its converse. -/
theorem inclusive_disjunction :
    would outcome (A + B + A * B) C =
      would outcome A C ∩ would outcome B C ∩ would outcome (A * B) C := by
  rw [would_add, would_add]

/-- Conjunction: fusing a verifier of each consequent inside the outcome uses BC. -/
theorem conjunction : would outcome A B ∩ would outcome A C ⊆ would outcome A (B * C) := by
  rintro w ⟨hB, hC⟩ a ha t rfl u hu
  obtain ⟨b, hb, hbu⟩ := hB ha t rfl u hu
  obtain ⟨c, hc, hcu⟩ := hC ha t rfl u hu
  obtain ⟨d, hd⟩ := IsBoundedComplete.exists_isLUB_of_bddAbove b c (Compat.of_le hbu hcu)
  exact ⟨d, ⟨_, hb, _, hc, st_mul_st_eq_iff.mpr hd⟩,
    hd.2 (mem_upperBounds_pair.mpr ⟨hbu, hcu⟩)⟩

omit [OrderBot S] [IsBoundedComplete S] in
-- Exact Strengthening
theorem exact_strengthening (h : A' ≤ A) : would outcome A C ⊆ would outcome A' C :=
  upperPolar_anti _ h

omit [OrderBot S] [IsBoundedComplete S] in
-- Inexact Weakening
theorem inexact_weakening (h : ∀ c, st c ∈ C.toSet → Inexact C' c) :
    would outcome A C ⊆ would outcome A C' := by
  intro w hw a ha t ht u hu
  obtain ⟨c, hc, hcu⟩ := hw ha t ht u hu
  obtain ⟨c', hc', hc'c⟩ := h c hc
  exact ⟨c', hc', hc'c.trans hcu⟩

-- Triviality
theorem triviality_top : would outcome A 1 = Set.univ :=
  Set.eq_univ_of_forall fun _ _ _ _ _ _ _ ↦ ⟨⊥, rfl, bot_le⟩

omit [OrderBot S] [IsBoundedComplete S] in
-- Triviality
theorem triviality_bot : would outcome 0 C = Set.univ :=
  upperPolar_empty _

omit [OrderBot S] [IsBoundedComplete S] in
-- Identity, from Inclusion
theorem identity (h : ∀ w t u, outcome w t u → t ≤ u) : would outcome A A = Set.univ :=
  Set.eq_univ_of_forall fun w _ ha t ht u hu ↦ ⟨t, ht ▸ ha, h w t u hu⟩

omit [OrderBot S] [IsBoundedComplete S] in
/-- Modus Ponens, from Actuality: a state within a world has an outcome within it. Here the
worlds are states. -/
theorem modus_ponens {outcome : S → S → S → Prop}
    (h : ∀ w t, t ≤ w → ∃ u ≤ w, outcome w t u) {w : S} (hw : w ∈ would outcome A B)
    (hA : Inexact A w) : Inexact B w := by
  obtain ⟨t, ht, htw⟩ := hA
  obtain ⟨u, huw, hu⟩ := h w t htw
  obtain ⟨b, hb, hbu⟩ := hw ht t rfl u hu
  exact ⟨b, hb, hbu.trans huw⟩

end Clause

/-! ### The rocks -/

/-- For a conditional between propositions that satisfies Entailment, Transitivity, Disjunction
and infinitary Conjunction, Positive Effect and Negative Effect make it a counterfactual
consequence of some rock's falling that no rock falls. -/
theorem rocks {W : Type*} (imp : Set W → Set W → Prop) (R : ℕ → Set W)
    (ent : ∀ {A C : Set W}, A ⊆ C → imp A C)
    (trans : ∀ {A B C : Set W}, imp A B → imp (A ∩ B) C → imp A C)
    (disj : ∀ {A B C : Set W}, imp A C → imp B C → imp (A ∪ B) C)
    (conj : ∀ {A : Set W} {C : ℕ → Set W}, (∀ n, imp A (C n)) → imp A (⋂ n, C n))
    (pos : ∀ n, imp (R n) (R (n + 1))) (neg : ∀ n, imp (R (n + 1)) (R n)ᶜ) :
    imp (⋃ n, R n) (⋃ n, R n)ᶜ := by
  have trans' {A B C : Set W} (hBA : B ⊆ A) (h₁ : imp A B) (h₂ : imp B C) : imp A C :=
    trans h₁ (by rwa [Set.inter_eq_right.mpr hBA])
  have weak {A C C' : Set W} (h : imp A C) (hC : C ⊆ C') : imp A C' :=
    trans h (ent (Set.inter_subset_right.trans hC))
  have conj₂ {A B C : Set W} (h₁ : imp A B) (h₂ : imp A C) : imp A (B ∩ C) := by
    refine weak (conj (C := fun n ↦ if n = 0 then B else C) fun n ↦ ?_) fun x hx ↦ ?_
    · split_ifs
      exacts [h₁, h₂]
    · rw [Set.mem_iInter] at hx
      exact ⟨by simpa using hx 0, by simpa using hx 1⟩
  -- the rocks from the `k`-th on
  let T : ℕ → Set W := fun k ↦ ⋃ n, R (k + n)
  have hT (k : ℕ) : T k ⊆ T 0 := Set.iUnion_subset fun n x hx ↦
    Set.mem_iUnion.mpr ⟨k + n, by rwa [Nat.zero_add]⟩
  have step₁ (k : ℕ) : imp (R k ∪ ((R k)ᶜ ∩ R (k + 1))) (R k)ᶜ :=
    trans' (B := R (k + 1))
      (fun x hx ↦ by by_cases h : x ∈ R k; exacts [.inl h, .inr ⟨h, hx⟩])
      (disj (pos k) (ent Set.inter_subset_right)) (neg k)
  have step₂ (k : ℕ) : imp (T k) (R k)ᶜ := by
    have h := disj (step₁ k) (ent (A := T k ∩ (R k)ᶜ) Set.inter_subset_right)
    have e : R k ∪ ((R k)ᶜ ∩ R (k + 1)) ∪ (T k ∩ (R k)ᶜ) = T k := by
      ext x
      constructor
      · rintro ((hx | ⟨-, hx⟩) | ⟨hx, -⟩)
        · exact Set.mem_iUnion.mpr ⟨0, hx⟩
        · exact Set.mem_iUnion.mpr ⟨1, hx⟩
        · exact hx
      · intro hx
        by_cases h : x ∈ R k
        exacts [.inl (.inl h), .inr ⟨hx, h⟩]
    rwa [e] at h
  have key (k : ℕ) : imp (T 0) (T k) ∧ imp (T 0) (R k)ᶜ := by
    induction k with
    | zero => exact ⟨ent subset_rfl, step₂ 0⟩
    | succ k ih =>
      have h₁ : imp (T k) (T (k + 1)) := by
        refine weak (conj₂ (step₂ k) (ent subset_rfl)) ?_
        rintro x ⟨hxk, hx⟩
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
        cases n with
        | zero => exact (hxk hn).elim
        | succ m => exact Set.mem_iUnion.mpr ⟨m, by rwa [Nat.add_right_comm]⟩
      have h₂ : imp (T 0) (T (k + 1)) := trans' (hT k) ih.1 h₁
      exact ⟨h₂, trans' (hT (k + 1)) h₂ (step₂ (k + 1))⟩
  have h := conj fun k ↦ (key k).2
  have e₀ : T 0 = ⋃ n, R n := by
    change (⋃ n, R (0 + n)) = _
    simp only [Nat.zero_add]
  rwa [e₀, ← Set.compl_iUnion] at h

end Fine2012
