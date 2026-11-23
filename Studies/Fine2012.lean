/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Conditionals.Counterfactual.Transition

/-!
# Fine (2012): Counterfactuals without Possible Worlds

The paper begins from a derivation: for rocks each of which would topple the next and leave the
previous one standing, the rules Entailment, Substitution, Transitivity, Disjunction and
Conjunction yield that if some rock fell then none would (`rocks`). A conditional between
propositions, sets of worlds, satisfies Substitution of logical equivalents by its type, so the
derivation is a theorem about every such conditional. Disjunction is used only for exclusive
disjuncts.

The paper's own semantics gives up Substitution. States are ordered by parthood, and the fusion
of some states exists just in case they are compatible: the order is bounded complete, with a
null state `⊥`. A statement is exactly verified by a set of states: a conjunction by the fusions
`A.lubs B` of a verifier of each conjunct, a disjunction by the verifiers `A ∪ B ∪ A.lubs B` of
either disjunct or of their conjunction, `⊤` by the null state alone, and `⊥` by nothing. For a
transition relation, the counterfactual is `Conditional.transitionImp`, and the paper's rules
for it are theorems about that clause: Inclusive Disjunction
(`Conditional.transitionImp_union_union_lubs`), Conjunction
(`Conditional.transitionImp_upperClosure_lubs`), Exact Strengthening
(`Conditional.transitionImp_anti`), Inexact Weakening (`Conditional.transitionImp_mono`),
Triviality (`Conditional.transitionImp_upperClosure_bot`, `Conditional.transitionImp_empty`),
Identity from Inclusion (`Conditional.transitionImp_upperClosure_self`), Modus Ponens from
Actuality (`Conditional.state_mem_of_mem_transitionImp`) and Transitivity from Incorporation
(`Conditional.transitionImp_trans`).

## Implementation notes

Bounded completeness is assumed for pairs of states; the paper assumes it for sets of states,
and infinitary conjunction of statements, which needs that, is not formalized. Statements are
unilateral, a set of verifiers, so negation, which the paper treats by falsifiers, is not
represented. Inclusive Disjunction and Conjunction are stated as equalities, of which the
paper's rules are one direction. Transitivity takes Inclusion as a hypothesis, under which the
fusion formed in its proof exists.

## References

* [fine-2012]
-/

@[expose] public section

namespace Fine2012


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
