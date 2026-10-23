module

public import Linglib.Data.Experiments.Chemla2009a
public import Linglib.Semantics.Presupposition.QuantifiedLocalContext

/-!
# Chemla (2009): presuppositions of quantified sentences

Chemla's first experiment finds the universal inference from a trigger in the nuclear scope of
*each* and *no* endorsed far more often than from the scope of the numerical quantifiers
(`Data/Experiments/Chemla2009a`). One amendment the paper considers keeps the universal
presupposition that the transparency theory predicts for every quantifier, and explains why it is
not accommodated after the numerical quantifiers by how hard it is to derive (§4.1.2). Appendix F
makes the measure precise. Under *no*, a single instance of transparency's condition, at the
negation of the presupposition, entails the universal presupposition. Under *less than 3*, the
appendix states, no Boolean combination of the restrictor and the presupposition does, and it
leaves open a proof that no single instance does.

A quantifier derives its universal presupposition in one step when such an instance entails it in
every model (`OneStep`). This holds exactly when the quantifier tells one end of each row of its
tree of numbers from every other point of the row (`oneStep_iff`): the end where no individual of
the restrictor is in the scope, as *no* and *some* do, or the end where all of them are, as *each*
and *not every* do. So among the quantifiers of Experiment 1 the universal presupposition is one
step away under exactly *each* and *no*, the two whose universal inference is robust
(`oneStep_tree_iff`).

## Implementation notes

* A Boolean combination of the restrictor and the presupposition is a set of pairs whose membership
  is a function of membership in the two; the appendix speaks of conjunctions and disjunctions of
  the two and their negations.

## References

* [chemla-2009a]
* [schlenker-2007]
-/

@[expose] public section

namespace Chemla2009a

open Quantifier Presupposition Set

/-- The quantifier of a determiner of Experiment 1, on the tree of numbers. -/
def Determiner.tree : Determiner → NumberTree
  | .each => NumberTree.all
  | .no => NumberTree.no
  | .lessThan3 => NumberTree.cardinal {b | b < 3}
  | .moreThan3 => NumberTree.cardinal {b | 3 < b}
  | .exactly3 => NumberTree.cardinal {3}

/-- Appendix F: transparency derives the universal presupposition of a trigger in the nuclear
scope of `q` in one step when, for some Boolean combination of the restrictor and the
presupposition, the instance of its condition at that combination entails in every model that every
individual of the restrictor satisfies the presupposition. -/
def OneStep (q : NumberTree) : Prop :=
  ∃ φ : Prop → Prop → Prop, ∀ (W E : Type) [Finite E] (A : W → E → Prop) (P : Set (W × E)) (w : W),
    (w ∈ scopeTruth q A (P ⊓ {x | φ (A x.1 x.2) (x ∈ P)}) ↔
      w ∈ scopeTruth q A {x | φ (A x.1 x.2) (x ∈ P)}) → ∀ e, A w e → (w, e) ∈ P

section OneStep

variable {q : NumberTree}

private theorem ncard_eq_add {E : Type} [Finite E] (A B : E → Prop) :
    {e | A e}.ncard = {e | A e ∧ B e}.ncard + {e | A e ∧ ¬ B e}.ncard :=
  (ncard_inter_add_ncard_sdiff_eq_ncard {e | A e} {e | B e}).symm

private theorem forall_mem_of_ncard_eq_zero {W E : Type} [Finite E] {A : W → E → Prop}
    {P : Set (W × E)} {w : W} (h : {e | A w e ∧ (w, e) ∉ P}.ncard = 0) :
    ∀ e, A w e → (w, e) ∈ P := fun e he ↦ by
  rw [ncard_eq_zero] at h
  by_contra hP
  exact (eq_empty_iff_forall_notMem.1 h) e ⟨he, hP⟩

private theorem model_iff {a b : ℕ} (D : Set (Unit × (Fin a ⊕ Fin b))) (d : Set (Fin a ⊕ Fin b))
    (hD : ∀ x, x ∈ D ↔ x.2 ∈ d) :
    () ∈ scopeTruth q (fun _ _ ↦ True) D ↔ q dᶜ.ncard d.ncard := by
  obtain rfl : D = {x | x.2 ∈ d} := ext hD
  simp only [scopeTruth, NumberTree.toGQ_apply, true_and, mem_ofPred_eq, ofPred_mem_eq]
  rfl

private theorem ncard_range_inl (a b : ℕ) :
    (range (Sum.inl : Fin a → Fin a ⊕ Fin b)).ncard = a := by
  simp [ncard_range_of_injective Sum.inl_injective]

private theorem ncard_range_inr (a b : ℕ) :
    (range (Sum.inr : Fin b → Fin a ⊕ Fin b)).ncard = b := by
  simp [ncard_range_of_injective Sum.inr_injective]

/-- Appendix F: transparency derives the universal presupposition in one step exactly when `q`
tells the end of each row where no individual is in the scope from every other point of the row,
or the end where every individual is. -/
theorem oneStep_iff :
    OneStep q ↔ (∀ a b, 0 < b → (q a b ↔ ¬ q (a + b) 0)) ∨
      (∀ a b, 0 < a → (q a b ↔ ¬ q 0 (a + b))) := by
  constructor
  · rintro ⟨φ, hφ⟩
    -- With `a` individuals that satisfy the presupposition and `b > 0` that do not, an instance at
    -- a combination holding of the individuals in `d` fails, since the presupposition does.
    have hfail (a b : ℕ) (hb : 0 < b) (d : Set (Fin a ⊕ Fin b))
        (hd : ∀ e, e ∈ d ↔ φ True (e ∈ range Sum.inl)) :
        ¬ (q (range Sum.inl ∩ d)ᶜ.ncard (range Sum.inl ∩ d).ncard ↔ q dᶜ.ncard d.ncard) := by
      intro h
      have := hφ Unit (Fin a ⊕ Fin b) (fun _ _ ↦ True) {x | x.2 ∈ range Sum.inl} ()
        ((model_iff _ _ fun x ↦ by simp [hd]).trans (h.trans (model_iff _ _ fun x ↦ by
          simp [hd]).symm)) (.inr ⟨0, hb⟩) trivial
      simp at this
    by_cases hf : φ True False
    · by_cases ht : φ True True
      · refine .inr fun a b ha ↦ (not_iff.1 fun h ↦ hfail b a ha univ (fun e ↦ ?_) ?_).symm
        · cases e <;> simp [ht, hf]
        · simpa [ncard_range_inl, ncard_range_inr, add_comm] using h.symm
      · refine .inl fun a b hb ↦
          (not_iff.1 fun h ↦ hfail a b hb (range Sum.inr) (fun e ↦ ?_) ?_).symm
        · cases e <;> simp [ht, hf]
        · simpa [range_inl_inter_range_inr, ncard_range_inl, ncard_range_inr] using h
    · exact (hfail 0 1 one_pos ∅ (fun e ↦ by cases e <;> simp [hf]) (by rw [inter_empty])).elim
  · rintro (h | h)
    · refine ⟨fun _ p ↦ ¬ p, fun W E _ A P w hw ↦ forall_mem_of_ncard_eq_zero ?_⟩
      by_contra hk
      have hw : q {e | A w e}.ncard 0 ↔ q {e | A w e ∧ (w, e) ∈ P}.ncard
          {e | A w e ∧ (w, e) ∉ P}.ncard := by
        simpa [scopeTruth, NumberTree.toGQ_apply] using hw
      rw [ncard_eq_add (A w) fun e ↦ (w, e) ∈ P] at hw
      exact iff_not_self (hw.trans (h _ _ (Nat.pos_of_ne_zero hk)))
    · refine ⟨fun _ _ ↦ True, fun W E _ A P w hw ↦ forall_mem_of_ncard_eq_zero ?_⟩
      by_contra hk
      have hw : q {e | A w e ∧ (w, e) ∉ P}.ncard {e | A w e ∧ (w, e) ∈ P}.ncard ↔
          q 0 {e | A w e}.ncard := by
        simpa [scopeTruth, NumberTree.toGQ_apply] using hw
      rw [ncard_eq_add (A w) fun e ↦ (w, e) ∉ P] at hw
      simp only [not_not] at hw
      exact iff_not_self (hw.symm.trans (h _ _ (Nat.pos_of_ne_zero hk)))

end OneStep

/-- Appendix F: among the quantifiers of Experiment 1, transparency derives the universal
presupposition in one step from exactly those pooled with *each* and *no*. -/
theorem oneStep_tree_iff (d : Determiner) :
    OneStep d.tree ↔ (experiment1Groups d).group = .eachOrNo := by
  rw [oneStep_iff]
  cases d
  · exact iff_of_true (.inr fun a b ha ↦ by simp [Determiner.tree, NumberTree.all, ha.ne']) rfl
  · exact iff_of_true (.inl fun a b hb ↦ by simp [Determiner.tree, NumberTree.no, hb.ne']) rfl
  all_goals
    refine iff_of_false ?_ (by decide)
    rintro (h | h)
    · simpa [Determiner.tree, NumberTree.cardinal] using h 0 1 one_pos
    · simpa [Determiner.tree, NumberTree.cardinal] using h 1 9 one_pos

end Chemla2009a
