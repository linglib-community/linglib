/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Basic.Rel
public import Mathlib.Order.UpperLower.Closure
public import Linglib.Core.Data.Set.Sups

/-!
# Fine (2012): Counterfactuals without Possible Worlds

States are ordered by parthood, and the fusion of some states exists just in case they are
compatible: the order is bounded complete, with a null state `⊥`. A statement is exactly verified
by a set of states: a conjunction by the fusions `A.lubs B` of a verifier of each conjunct, a
disjunction by the verifiers `A ∪ B ∪ A.lubs B` of either disjunct or of their conjunction,
`⊤` by the null state alone, and `⊥` by nothing. It is inexactly verified by the states
containing an exact verifier, the upper set `upperClosure A`. By BC a state inexactly verifies a
conjunction exactly when it inexactly verifies both conjuncts (`Set.upperClosure_lubs`).

For a transition relation `outcome w`, relating a state `t` to the possible outcomes `u` of
imposing it on the world `w`, the counterfactual `would outcome A C` is true at `w` when every
outcome at `w` of every exact verifier of `A` inexactly verifies `C`: the image of `A` under
`outcome w` is contained in `C`. From the form of this clause alone the counterfactual
satisfies Inclusive Disjunction (`inclusive_disjunction`), Conjunction
(`conjunction`), Exact Strengthening, Inexact Weakening and Triviality; when outcomes contain
the state imposed it satisfies Identity, and when a state within a world has an outcome within
it, Modus Ponens (`modus_ponens`).

The paper begins from a derivation: for rocks each of which would topple the next and leave the
previous one standing, the rules Entailment, Substitution, Transitivity, Disjunction and
Conjunction yield that if some rock fell then none would (`rocks`). A conditional between
propositions, sets of worlds, satisfies Substitution of logical equivalents by its type, so the
derivation is a theorem about every such conditional. Disjunction is used only for exclusive
disjuncts.

## Implementation notes

Bounded completeness is assumed for pairs of states; the paper assumes it for sets of states,
and infinitary conjunction of statements, which needs that, is not formalized. Statements are
unilateral, a set of verifiers, so negation, which the paper treats by falsifiers, is not
represented. The consequent of `would` is an inexact content, an upper set of states.

## References

* [fine-2012]
-/

@[expose] public section

namespace Fine2012


/-! ### The truth clause and its rules -/

section Clause

variable {S W : Type*} [PartialOrder S]

/-- `A > C` is true at `w` when the possible outcomes at `w` of the exact verifiers of `A`
inexactly verify `C`. -/
def would (outcome : W → SetRel S S) (A : Set S) (C : UpperSet S) : Set W :=
  {w | (outcome w).image A ⊆ C}

variable {outcome : W → SetRel S S} {A A' B D E : Set S} {C C' : UpperSet S} {w : W}

theorem mem_would : w ∈ would outcome A C ↔ (outcome w).image A ⊆ C := Iff.rfl

theorem would_union : would outcome (A ∪ B) C = would outcome A C ∩ would outcome B C :=
  Set.ext fun _ ↦ by
    simp only [mem_would, SetRel.image_union, Set.union_subset_iff, Set.mem_inter_iff]

/-- Inclusive Disjunction. -/
theorem inclusive_disjunction :
    would outcome A C ∩ would outcome B C ∩ would outcome (A.lubs B) C ⊆
      would outcome (A ∪ B ∪ A.lubs B) C := by
  rw [would_union, would_union]

theorem would_sup : would outcome A (C ⊔ C') = would outcome A C ∩ would outcome A C' :=
  Set.ext fun _ ↦ by
    simp only [mem_would, UpperSet.coe_sup, Set.subset_inter_iff, Set.mem_inter_iff]

/-- Conjunction: by BC the outcome contains the fusion of the verifiers it contains. -/
theorem conjunction [IsBoundedComplete S] :
    would outcome A (upperClosure D) ∩ would outcome A (upperClosure E) ⊆
      would outcome A (upperClosure (D.lubs E)) := by
  rw [Set.upperClosure_lubs, would_sup]

-- Exact Strengthening
theorem exact_strengthening (h : A' ⊆ A) : would outcome A C ⊆ would outcome A' C :=
  fun _ hw ↦ (SetRel.image_subset_image h).trans hw

-- Inexact Weakening
theorem inexact_weakening (h : (C : Set S) ⊆ C') : would outcome A C ⊆ would outcome A C' :=
  fun _ hw ↦ hw.trans h

-- Triviality
theorem triviality_top [OrderBot S] : would outcome A (upperClosure {⊥}) = Set.univ :=
  Set.eq_univ_of_forall fun _ _ _ ↦ ⟨⊥, rfl, bot_le⟩

-- Triviality
theorem triviality_bot : would outcome ∅ C = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ by
    rw [mem_would, SetRel.image_empty_right]
    exact Set.empty_subset _

-- Identity, from Inclusion
theorem identity (h : ∀ w t u, (t, u) ∈ outcome w → t ≤ u) :
    would outcome A (upperClosure A) = Set.univ :=
  Set.eq_univ_of_forall fun w u ⟨t, ht, htu⟩ ↦ ⟨t, ht, h w t u htu⟩

/-- Modus Ponens, from Actuality: a state within a world has an outcome within it. Here the
worlds are states. -/
theorem modus_ponens {outcome : S → SetRel S S}
    (h : ∀ w t, t ≤ w → ∃ u ≤ w, (t, u) ∈ outcome w) {w : S} (hw : w ∈ would outcome A C)
    (hA : w ∈ upperClosure A) : w ∈ C := by
  obtain ⟨t, ht, htw⟩ := hA
  obtain ⟨u, huw, hu⟩ := h w t htw
  exact C.upper huw (hw ⟨t, ht, hu⟩)

end Clause

/-! ### The rocks -/

/-- For a conditional between propositions that satisfies Entailment, Transitivity, Disjunction
for exclusive disjuncts and infinitary Conjunction, Positive Effect and Negative Effect make it
a counterfactual consequence of some rock's falling that no rock falls. -/
theorem rocks {W : Type*} (imp : Set W → Set W → Prop) (R : ℕ → Set W)
    (ent : ∀ {A C : Set W}, A ⊆ C → imp A C)
    (trans : ∀ {A B C : Set W}, imp A B → imp (A ∩ B) C → imp A C)
    (disj : ∀ {A B C : Set W},
      Disjoint A B → imp A C → imp B C → imp (A ∪ B) C)
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
      (disj (Set.disjoint_left.mpr fun _ hx h ↦ h.1 hx) (pos k) (ent Set.inter_subset_right))
      (neg k)
  have step₂ (k : ℕ) : imp (T k) (R k)ᶜ := by
    have hd : Disjoint (R k ∪ ((R k)ᶜ ∩ R (k + 1))) (T k ∩ (R k)ᶜ ∩ (R (k + 1))ᶜ) :=
      Set.disjoint_left.mpr fun _ hx h ↦ hx.elim (fun h' ↦ h.1.2 h') fun h' ↦ h.2 h'.2
    have h := disj hd (step₁ k) (ent fun _ hx ↦ hx.1.2)
    have e : R k ∪ ((R k)ᶜ ∩ R (k + 1)) ∪ (T k ∩ (R k)ᶜ ∩ (R (k + 1))ᶜ) = T k := by
      ext x
      constructor
      · rintro ((hx | ⟨-, hx⟩) | ⟨⟨hx, -⟩, -⟩)
        · exact Set.mem_iUnion.mpr ⟨0, hx⟩
        · exact Set.mem_iUnion.mpr ⟨1, hx⟩
        · exact hx
      · intro hx
        by_cases h : x ∈ R k
        · exact .inl (.inl h)
        · by_cases h' : x ∈ R (k + 1)
          exacts [.inl (.inr ⟨h, h'⟩), .inr ⟨⟨hx, h⟩, h'⟩]
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
