module

public import Linglib.Semantics.Conditionals.Basic
public import Mathlib.Tactic.FinCases

/-!
# Lewis (1981): Ordering semantics and premise semantics for counterfactuals

This file formalizes Lewis's equivalence of two ways of letting factual background
settle the truth of a counterfactual. An ordering frame assigns to each world a set of worlds,
its field, and an ordering of them by how little they differ from it, and a counterfactual is
true when its consequent holds at the closest antecedent-worlds (truth condition OF, the
library's `orderingImp`). A premise frame assigns to each world a set of premises, and a
counterfactual is true when every nonempty maximal set of premises consistent with the
antecedent implies the consequent together with it (truth condition PF, Kratzer's premise
semantics up to the word *nonempty*). A premise frame induces an ordering frame
on the worlds where some premise holds, one world closer than another when it satisfies every
premise the other satisfies, and the two frames evaluate every counterfactual alike
(`premiseImp_eq_orderingImp`, §4). Every ordering frame is induced in this way, by the premises
that say a world is at least as close as some world of the field (`orderingImp_eq_premiseImp`),
so the correspondence exhausts both classes of frames.

Section 6 replaces OF by a truth condition that needs neither the Limit Assumption nor
comparability: every antecedent-world of the field has one at least as close, all of whose
antecedent-worlds at least as close are consequent-worlds. This is the variably strict
conditional of the theory layer (`Conditional.variablyStrictImp`), the necessity of ordering
semantics over the antecedent-worlds of the field. It entails OF
(`Conditional.variablyStrictImp_subset_orderingImp`), is OF under the Limit Assumption
(`Conditional.mem_variablyStrictImp_iff_mem_orderingImp`), and under comparability is the truth
condition of *Counterfactuals* (`Conditional.mem_variablyStrictImp_iff_of_total`).

## Main definitions

* `Lewis1981.premiseImp`: truth condition PF of a premise frame.
* `Lewis1981.premiseOrder`: the ordering a premise frame induces.
* `Lewis1981.ofOrdering`: the premise frame an ordering frame induces.

## Implementation notes

* Lewis's orderings are strict partial orders of their fields; the library's are preorders on all
  worlds, the field entering as the accessibility argument of `orderingImp`. Preorders allow
  ties, which a strict ordering cannot tell from incomparabilities, and the proofs do not need
  antisymmetry.
* Neither Centering nor finiteness is assumed: §7 notes that the equivalence results do not
  depend on Centering, and §6 that they carry over to the infinite case.
* Section 5's reconciliation of partial with total orderings, truth on an ordering being truth on
  every refinement to a total one, is `Conditional.mem_closestImp_iff_forall_compatible` for the
  refinements [stalnaker-1981] calls completions.

## TODO

* Section 6's neutral truth condition for premise frames and its equivalence with
  `Conditional.variablyStrictImp`.
* Section 6's example of a counterfactual true under the neutral condition on a frame and false
  on one of its refinements.

## References

* [D. Lewis, *Ordering Semantics and Premise Semantics for Counterfactuals* (1981)][lewis-1981]
* [A. Kratzer, *Partition and Revision: The Semantics of Counterfactuals*
  (1981)][kratzer-1981-partition]
* [A. Kratzer, *Conditional Necessity and Possibility* (1979)][kratzer-1979]
* [D. Lewis, *Counterfactuals* (1973)][lewis-1973b]
* [R. C. Stalnaker, *A Defense of Conditional Excluded Middle* (1981)][stalnaker-1981]
-/

@[expose] public section

namespace Lewis1981

open Conditional

variable {W : Type*}

/-! ### Premise frames (§3) -/

section Premise

variable (H : W → Set (Set W)) (A C : Set W)

/-- An `A`-consistent premise set for `i`: a set of premises for `i` consistent with `A`. -/
def IsConsistentPremiseSet (i : W) (J : Set (Set W)) : Prop := J ⊆ H i ∧ (A ∩ ⋂₀ J).Nonempty

/-- Truth condition PF holds when every nonempty maximal `A`-consistent premise set for `i`
implies `C` together with `A`. -/
def premiseImp : Set W :=
  {i | ∀ J, Maximal (IsConsistentPremiseSet H A i) J → J.Nonempty → A ∩ ⋂₀ J ⊆ C}

/-- In the ordering a premise frame induces at `i`, `j` is at least as close as `k` when every
premise for `i` that holds at `k` holds at `j`. -/
abbrev premiseOrder (i : W) : Preorder W := Preorder.ofCriteria (· ∈ ·) (H i)

end Premise

/-! ### Equivalence of frames (§4) -/

variable {H : W → Set (Set W)} {A C : Set W}

/-- A premise frame and the ordering frame it induces, on the worlds where some premise holds,
evaluate every counterfactual alike. For an antecedent-world `j`, the premises that hold at `j`
form a nonempty maximal consistent premise set exactly when `j` is a closest antecedent-world. -/
theorem premiseImp_eq_orderingImp :
    premiseImp H A C = orderingImp (fun i ↦ ⋃₀ H i) (premiseOrder H) A C := by
  ext i
  simp only [premiseImp, Set.mem_ofPred_eq, mem_orderingImp]
  let F : W → Set (Set W) := fun j ↦ {p ∈ H i | j ∈ p}
  have hcons : ∀ {j}, j ∈ A → IsConsistentPremiseSet H A i (F j) :=
    fun hj ↦ ⟨Set.sep_subset _ _, _, hj, fun _ hp ↦ hp.2⟩
  constructor
  · rintro h j ⟨⟨⟨p, hp, hjp⟩, hjA⟩, hmin⟩
    refine h (F j) ⟨hcons hjA, fun K hK hFK ↦ ?_⟩ ⟨p, hp, hjp⟩ ⟨hjA, fun _ hq ↦ hq.2⟩
    obtain ⟨k, hkA, hkK⟩ := hK.2
    have hKk : K ⊆ F k := fun q hq ↦ ⟨hK.1 hq, hkK q hq⟩
    have hjk := hmin ⟨⟨p, hp, (hKk (hFK ⟨hp, hjp⟩)).2⟩, hkA⟩
      fun q hq hjq ↦ (hKk (hFK ⟨hq, hjq⟩)).2
    exact fun q hq ↦ ⟨hK.1 hq, hjk q (hK.1 hq) (hkK q hq)⟩
  · rintro h J hJ ⟨p, hp⟩ j ⟨hjA, hjJ⟩
    have hJF : J ⊆ F j := fun q hq ↦ ⟨hJ.1.1 hq, hjJ q hq⟩
    refine h ⟨⟨⟨p, hJ.1.1 hp, hjJ p hp⟩, hjA⟩, fun k hk hkj ↦ ?_⟩
    have hkJ : F k ⊆ J :=
      hJ.2 (hcons hk.2) (hJF.trans fun q hq ↦ ⟨hq.1, hkj q hq.1 hq.2⟩)
    exact fun q hq hkq ↦ hjJ q (hkJ ⟨hq, hkq⟩)

/-- In the premise frame an ordering frame induces, the premises for `i` say that a world of the
field is at least as close as some given world of it. -/
def ofOrdering (S : W → Set W) (ord : W → Preorder W) (i : W) : Set (Set W) :=
  (fun k ↦ {j ∈ S i | (ord i).le j k}) '' S i

/-- Every ordering frame is induced by a premise frame, so the correspondence of §4 exhausts both
classes of frames. -/
theorem orderingImp_eq_premiseImp (S : W → Set W) (ord : W → Preorder W) :
    orderingImp S ord A C = premiseImp (ofOrdering S ord) A C := by
  rw [premiseImp_eq_orderingImp]
  ext i
  have hS : ⋃₀ ofOrdering S ord i = S i := Set.ext fun j ↦
    ⟨fun ⟨_, ⟨_, _, hk⟩, hj⟩ ↦ (hk ▸ hj).1, fun hj ↦ ⟨_, ⟨j, hj, rfl⟩, hj, (ord i).le_refl j⟩⟩
  have hle : ∀ j ∈ S i ∩ A, ∀ k ∈ S i ∩ A,
      (ord i).le j k ↔ (premiseOrder (ofOrdering S ord) i).le j k := by
    rintro j ⟨hj, -⟩ k ⟨hk, -⟩
    refine ⟨fun hjk ↦ ?_, fun h ↦ (h _ ⟨k, hk, rfl⟩ ⟨hk, (ord i).le_refl k⟩).2⟩
    rintro _ ⟨m, -, rfl⟩ ⟨-, hkm⟩
    exact ⟨hj, (ord i).le_trans _ _ _ hjk hkm⟩
  simp only [mem_orderingImp, hS, Preorder.minimals_congr hle]

/-! ### Surplus information (§4)

Two premise frames can induce the same strict ordering, and so evaluate every counterfactual
alike, while differing on whether two worlds are tied or incomparable. Of three worlds `0`, `1`,
`2`, premises `{0}` and `{0, 1, 2}` for `0` tie `1` and `2`, and premises `{0, 1}` and `{0, 2}`
make them incomparable. -/

/-- Premises `{0}` and `{0, 1, 2}`. -/
def tied : Fin 3 → Set (Set (Fin 3)) := fun _ ↦ {{0}, {0, 1, 2}}

/-- Premises `{0, 1}` and `{0, 2}`. -/
def split : Fin 3 → Set (Set (Fin 3)) := fun _ ↦ {{0, 1}, {0, 2}}

theorem premiseOrder_tied_ne_split : premiseOrder tied 0 ≠ premiseOrder split 0 := by
  intro h
  have h12 : (premiseOrder tied 0).le 1 2 := by simp [tied, Preorder.ofCriteria_le_iff]
  rw [h] at h12
  simp [split, Preorder.ofCriteria_le_iff] at h12

theorem premiseImp_tied_iff_split (A C : Set (Fin 3)) :
    0 ∈ premiseImp tied A C ↔ 0 ∈ premiseImp split A C := by
  have hS : ⋃₀ tied 0 = ⋃₀ split 0 := by
    ext x; fin_cases x <;> simp [tied, split]
  have hlt : ∀ a b, (premiseOrder tied 0).lt a b ↔ (premiseOrder split 0).lt a b := by
    intro a b
    rw [(premiseOrder tied 0).lt_iff_le_not_ge, (premiseOrder split 0).lt_iff_le_not_ge]
    simp only [Preorder.ofCriteria_le_iff, tied, split, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq]
    revert a b; decide
  simp only [premiseImp_eq_orderingImp, mem_orderingImp, hS,
    Preorder.minimals_eq_of_lt_iff (p := premiseOrder tied 0) (q := premiseOrder split 0) hlt]

end Lewis1981
