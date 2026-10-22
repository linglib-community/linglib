module

public import Linglib.Logic.RankingFunction
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Linglib.Semantics.Questions.Partition.Basic

/-!
# Spohn (1988): Ordinal Conditional Functions: A Dynamic Theory of Epistemic States

This file formalizes the theory of ordinal conditional functions of [spohn-1988] with
natural-number grades, the paper's Note 16, on the ranking functions of
`Logic/RankingFunction.lean`. Conditionalization on a proposition at a firmness is reversible:
conditionalizing again on the proposition at the firmness with which it was believed restores
the ranking, whether the first change conditionalized on the proposition or on its negation
(`conditionα_conditionα`, `conditionα_compl_conditionα`); and two conditionalizations commute
when the three cells they distinguish other than the joint negation have rank zero
(`conditionα_comm`). Generalized conditionalization by a ranking on the atoms of a subfield,
the deterministic counterpart of Jeffrey conditionalization, has conditionalization on a
proposition as its two-atom case (`condition_firmness`) and is reversed by conditionalizing on
the coarsening of the original ranking to the subfield (`condition_condition_coarsen`).

Independence of two subfields, the rank of an intersection of atoms being the sum of the ranks,
extends from atoms to all members of the fields (`Independent.rank_inter`), and it is
equivalent to conditional ranks being unconditional ranks and to the ranks of one field being
invariant under generalized conditionalization on the other (`independent_iff_condRank`,
`independent_iff_condition`). Conditional independence given a subfield satisfies the
contraction law of the paper's Theorem 11 and its mirror image (`CondIndependentOn.inf`,
`CondIndependentOn.inf'`).

## Implementation notes

Complete subfields of the propositions over a set of worlds are partitions, `Setoid W`: the
atoms are the cells, the members are the propositions the partition decides, and the field two
subfields generate is their meet in the lattice of setoids. Over natural numbers every two
firmnesses commute and independence is symmetric, so the paper's two directions of
independence coincide. Simple conditional functions and well-ordered partitions with their
representation theorem, the independence of sequences of subfields, Theorem 13, whose
conclusion conditions on the intersection of two subfields, and the nonstandard-probability
homomorphism of Section 7 are not formalized.

## References

* [spohn-1988]
* [goldszmidt-pearl-1996]
-/

@[expose] public section

namespace Spohn1988

open RankingFunction Setoid

variable {W : Type*} (κ : RankingFunction W)

/-! ### Reversibility and commutativity of conditionalization -/

section Conditionalization

variable {A B : Set W} (hA : A.Nonempty) (hB : B.Nonempty)

theorem toNat_rank_eq_zero (h : rank κ A = 0) : (rank κ A).toNat = 0 := by
  rw [h]; rfl

/-- After conditionalizing on `A` at any firmness, conditionalizing on `A` at the firmness with
which `A` was believed restores the ranking (Theorem 3, first half). -/
theorem conditionα_conditionα (h0 : rank κ A = 0) (α : ℕ) :
    (κ.conditionα A hA α).conditionα A hA (rank κ Aᶜ).toNat = κ := by
  ext w
  by_cases hw : w ∈ A
  · rw [conditionα_of_mem _ _ _ hw, aPart, conditionα_of_mem _ _ _ hw, aPart,
      toNat_rank_eq_zero _ h0, toNat_rank_eq_zero _ (κ.rank_conditionα hA α)]
    rfl
  · rcases Set.eq_empty_or_nonempty Aᶜ with hA' | hA'
    · have hw' : w ∈ Aᶜ := hw
      rw [hA'] at hw'
      exact hw'.elim
    have := toNat_rank_le κ (A := Aᶜ) hw
    rw [conditionα_of_notMem _ _ _ hw, aPart, conditionα_of_notMem _ _ _ hw, aPart,
      κ.rank_conditionα_compl hA hA', ENat.toNat_natCast]
    omega

/-- After conditionalizing on the negation of `A` at any firmness, conditionalizing on `A` at
the firmness with which `A` was believed restores the ranking (Theorem 3, second half). -/
theorem conditionα_compl_conditionα (hA' : Aᶜ.Nonempty) (h0 : rank κ A = 0) (α : ℕ) :
    (κ.conditionα Aᶜ hA' α).conditionα A hA (rank κ Aᶜ).toNat = κ := by
  have hAc : rank (κ.conditionα Aᶜ hA' α) A = α := by
    have := κ.rank_conditionα_compl hA' (by rwa [compl_compl]) α
    rwa [compl_compl] at this
  ext w
  by_cases hw : w ∈ A
  · have hw' : w ∉ Aᶜ := fun h ↦ h hw
    rw [conditionα_of_mem _ _ _ hw, aPart, conditionα_of_notMem _ _ _ hw', aPart, compl_compl,
      toNat_rank_eq_zero _ h0, hAc, ENat.toNat_natCast]
    omega
  · have hw' : w ∈ Aᶜ := hw
    have := toNat_rank_le κ (A := Aᶜ) hw'
    rw [conditionα_of_notMem _ _ _ hw, aPart, conditionα_of_mem _ _ _ hw', aPart,
      toNat_rank_eq_zero _ (κ.rank_conditionα hA' α)]
    omega

/-- Conditionalizations on `A` and on `B` commute when the cells `A ∩ B`, `A ∩ Bᶜ` and
`Aᶜ ∩ B` all have rank zero (Theorem 4). -/
theorem conditionα_comm (hAB : rank κ (A ∩ B) = 0) (hAB' : rank κ (A ∩ Bᶜ) = 0)
    (hA'B : rank κ (Aᶜ ∩ B) = 0) (α β : ℕ) :
    (κ.conditionα A hA α).conditionα B hB β = (κ.conditionα B hB β).conditionα A hA α := by
  classical
  have zero_of_le : ∀ {S T : Set W}, S ⊆ T → rank κ S = 0 → rank κ T = 0 := fun h hS ↦
    le_antisymm (hS ▸ rank_anti κ h) bot_le
  have hA0 := zero_of_le Set.inter_subset_left hAB
  have hB0 := zero_of_le Set.inter_subset_right hAB
  have hA'0 := zero_of_le Set.inter_subset_left hA'B
  have hB'0 := zero_of_le Set.inter_subset_right hAB'
  obtain ⟨u, ⟨huA, huB⟩, hu⟩ := (rank_eq_zero_iff κ).1 hAB
  obtain ⟨u', ⟨hu'A, hu'B⟩, hu'⟩ := (rank_eq_zero_iff κ).1 hAB'
  obtain ⟨u'', ⟨hu''A, hu''B⟩, hu''⟩ := (rank_eq_zero_iff κ).1 hA'B
  have h1 : ∀ w, κ.conditionα A hA α w = if w ∈ A then κ w else α + κ w :=
    fun w ↦ by
      by_cases hw : w ∈ A
      · rw [conditionα_of_mem _ _ _ hw, aPart, toNat_rank_eq_zero _ hA0, ite_eq_left hw]; rfl
      · rw [conditionα_of_notMem _ _ _ hw, aPart, toNat_rank_eq_zero _ hA'0,
          ite_eq_right hw]
        rfl
  have h2 : ∀ w, κ.conditionα B hB β w = if w ∈ B then κ w else β + κ w :=
    fun w ↦ by
      by_cases hw : w ∈ B
      · rw [conditionα_of_mem _ _ _ hw, aPart, toNat_rank_eq_zero _ hB0, ite_eq_left hw]; rfl
      · rw [conditionα_of_notMem _ _ _ hw, aPart, toNat_rank_eq_zero _ hB'0,
          ite_eq_right hw]
        rfl
  have h1B : rank (κ.conditionα A hA α) B = 0 :=
    (rank_eq_zero_iff _).2 ⟨u, huB, by rw [h1, ite_eq_left huA, hu]⟩
  have h1B' : rank (κ.conditionα A hA α) Bᶜ = 0 :=
    (rank_eq_zero_iff _).2 ⟨u', hu'B, by rw [h1, ite_eq_left hu'A, hu']⟩
  have h2A : rank (κ.conditionα B hB β) A = 0 :=
    (rank_eq_zero_iff _).2 ⟨u, huA, by rw [h2, ite_eq_left huB, hu]⟩
  have h2A' : rank (κ.conditionα B hB β) Aᶜ = 0 :=
    (rank_eq_zero_iff _).2 ⟨u'', hu''A, by rw [h2, ite_eq_left hu''B, hu'']⟩
  have L : ∀ w, (κ.conditionα A hA α).conditionα B hB β w =
      (if w ∈ B then 0 else β) + (if w ∈ A then 0 else α) + κ w := fun w ↦ by
    by_cases hwB : w ∈ B
    · rw [conditionα_of_mem _ _ _ hwB, aPart, h1 w, toNat_rank_eq_zero _ h1B, ite_eq_left hwB]
      split_ifs <;> omega
    · rw [conditionα_of_notMem _ _ _ hwB, aPart, h1 w, toNat_rank_eq_zero _ h1B',
        ite_eq_right hwB]
      split_ifs <;> omega
  have R : ∀ w, (κ.conditionα B hB β).conditionα A hA α w =
      (if w ∈ A then 0 else α) + (if w ∈ B then 0 else β) + κ w := fun w ↦ by
    by_cases hwA : w ∈ A
    · rw [conditionα_of_mem _ _ _ hwA, aPart, h2 w, toNat_rank_eq_zero _ h2A, ite_eq_left hwA]
      split_ifs <;> omega
    · rw [conditionα_of_notMem _ _ _ hwA, aPart, h2 w, toNat_rank_eq_zero _ h2A',
        ite_eq_right hwA]
      split_ifs <;> omega
  ext w
  rw [L, R]
  split_ifs <;> omega

end Conditionalization

/-! ### Generalized conditionalization -/

section Generalized

variable (𝔅 : Setoid W)

/-- The conditionalization of `κ` by a ranking `l` on the atoms of a subfield (Definition 7)
ranks each world by the rank of its atom under `l` plus its rank within the atom. -/
noncomputable def condition (l : RankingFunction (Quotient 𝔅)) : RankingFunction W where
  toFun w := l (Quotient.mk 𝔅 w) + aPart κ (𝔅.cell w) w
  exists_eq_zero' := by
    obtain ⟨b, hb⟩ := l.exists_eq_zero
    induction b using Quotient.inductionOn with
    | h w₀ =>
      obtain ⟨w, hw, h0⟩ := exists_aPart_eq_zero κ (𝔅.cell_nonempty w₀)
      refine ⟨w, ?_⟩
      have hrel : 𝔅 w w₀ := 𝔅.mem_cell.1 hw
      simp only [Quotient.sound hrel, hb, cell_eq_of_rel hrel, h0]

theorem condition_rank (l : RankingFunction (Quotient 𝔅)) (w : W) :
    condition κ 𝔅 l w = l (Quotient.mk 𝔅 w) + aPart κ (𝔅.cell w) w :=
  rfl

/-- Within an atom, the conditionalized ranking starts at the atom's rank under `l`. -/
theorem rank_condition_cell (l : RankingFunction (Quotient 𝔅)) (w : W) :
    rank (condition κ 𝔅 l) (𝔅.cell w) = l (Quotient.mk 𝔅 w) := by
  obtain ⟨v, hv, h0⟩ := exists_aPart_eq_zero κ (𝔅.cell_nonempty w)
  have hrel : 𝔅 v w := 𝔅.mem_cell.1 hv
  refine le_antisymm ((rank_le (condition κ 𝔅 l) hv).trans ?_) ?_
  · rw [condition_rank, cell_eq_of_rel hrel, h0, Quotient.sound hrel, add_zero]
  · refine (le_rank_iff _).2 fun u hu ↦ ?_
    rw [condition_rank, Quotient.sound (𝔅.mem_cell.1 hu)]
    exact_mod_cast Nat.le_add_right _ _

open Classical in
/-- The two-atom ranking that believes `A` with firmness `α`. -/
noncomputable def firmness (A : Set W) (hA : A.Nonempty) (α : ℕ) :
    RankingFunction (Quotient (polar A)) where
  toFun := Quotient.lift (fun w ↦ if w ∈ A then 0 else α) fun w v h ↦ by
    simp only [polar_iff.1 h]
  exists_eq_zero' := ⟨Quotient.mk _ hA.some, by simp [hA.some_mem]⟩

/-- Conditionalization on `A` at firmness `α` is generalized conditionalization by the two-atom
ranking believing `A` with firmness `α` (Theorem 5). -/
theorem condition_firmness (A : Set W) (hA : A.Nonempty) (α : ℕ) :
    condition κ (polar A) (firmness A hA α) = κ.conditionα A hA α := by
  ext w
  by_cases hw : w ∈ A
  · rw [condition_rank, conditionα_of_mem _ _ _ hw, polar_cell_of_mem hw]
    simp [firmness, hw]
  · rw [condition_rank, conditionα_of_notMem _ _ _ hw, polar_cell_of_notMem hw]
    simp [firmness, hw]

/-- The coarsening of `κ` to a subfield ranks each atom by its rank under `κ`. -/
noncomputable def coarsen : RankingFunction (Quotient 𝔅) where
  toFun := Quotient.lift (fun w ↦ (rank κ (𝔅.cell w)).toNat) fun w v h ↦ by
    rw [cell_eq_of_rel h]
  exists_eq_zero' := by
    obtain ⟨w, hw⟩ := κ.exists_eq_zero
    exact ⟨Quotient.mk _ w, by
      simpa using toNat_rank_eq_zero κ ((rank_eq_zero_iff κ).2 ⟨w, 𝔅.mem_cell_self w, hw⟩)⟩

/-- Generalized conditionalization is reversed by conditionalizing on the coarsening of the
original ranking to the subfield (Theorem 6). -/
theorem condition_condition_coarsen (l : RankingFunction (Quotient 𝔅)) :
    condition (condition κ 𝔅 l) 𝔅 (coarsen κ 𝔅) = κ := by
  ext w
  have := toNat_rank_le κ (𝔅.mem_cell_self w)
  rw [condition_rank, aPart, rank_condition_cell, ENat.toNat_natCast, condition_rank, aPart]
  show (rank κ (𝔅.cell w)).toNat + _ = _
  omega

end Generalized

/-! ### Independence -/

section Independence

variable (𝔅 ℭ : Setoid W)

/-- `ℭ` is independent of `𝔅` with respect to `κ` (Definition 8) when every atom of `𝔅` meets
every atom of `ℭ` and the rank of their intersection is the sum of their ranks. -/
def Independent : Prop :=
  ∀ w v, (𝔅.cell w ∩ ℭ.cell v).Nonempty ∧
    rank κ (𝔅.cell w ∩ ℭ.cell v) = rank κ (𝔅.cell w) + rank κ (ℭ.cell v)

variable {κ 𝔅 ℭ}

theorem Independent.symm (h : Independent κ 𝔅 ℭ) : Independent κ ℭ 𝔅 := fun w v ↦ by
  obtain ⟨hne, heq⟩ := h v w
  exact ⟨by rwa [Set.inter_comm], by rw [Set.inter_comm, heq, add_comm]⟩

/-- Independence extends from atoms to all satisfiable members of the fields (Theorem 7). -/
theorem Independent.rank_inter (h : Independent κ 𝔅 ℭ) {B C : Set W} (hB : 𝔅.Decides B)
    (hC : ℭ.Decides C) (hB' : B.Nonempty) (hC' : C.Nonempty) :
    rank κ (B ∩ C) = rank κ B + rank κ C := by
  refine le_antisymm ?_ ?_
  · obtain ⟨b, hb, eb⟩ := exists_apply_eq_rank κ hB'
    obtain ⟨c, hc, ec⟩ := exists_apply_eq_rank κ hC'
    calc rank κ (B ∩ C) ≤ rank κ (𝔅.cell b ∩ ℭ.cell c) :=
          rank_anti κ (Set.inter_subset_inter (hB.cell_subset hb) (hC.cell_subset hc))
      _ = rank κ (𝔅.cell b) + rank κ (ℭ.cell c) := (h b c).2
      _ ≤ κ b + κ c :=
          add_le_add (rank_le κ (𝔅.mem_cell_self b)) (rank_le κ (ℭ.mem_cell_self c))
      _ = rank κ B + rank κ C := by rw [eb, ec]
  · rcases Set.eq_empty_or_nonempty (B ∩ C) with hBC | hBC
    · rw [hBC, rank_empty]; exact le_top
    obtain ⟨w, ⟨hwB, hwC⟩, e⟩ := exists_apply_eq_rank κ hBC
    calc rank κ B + rank κ C ≤ rank κ (𝔅.cell w) + rank κ (ℭ.cell w) :=
          add_le_add (rank_anti κ (hB.cell_subset hwB)) (rank_anti κ (hC.cell_subset hwC))
      _ = rank κ (𝔅.cell w ∩ ℭ.cell w) := ((h w w).2).symm
      _ ≤ κ w := rank_le κ ⟨𝔅.mem_cell_self w, ℭ.mem_cell_self w⟩
      _ = rank κ (B ∩ C) := e

variable (κ)

/-- On a satisfiable intersection, the conditional rank is a difference of natural numbers. -/
theorem condRank_eq {A B : Set W} (h : (A ∩ B).Nonempty) :
    κ[B | A] = ((rank κ (A ∩ B)).toNat - (rank κ A).toNat : ℕ) := by
  have hA := rank_ne_top κ (h.mono Set.inter_subset_left)
  rw [condRank_of_ne_top _ hA, ENat.natCast_sub, ENat.natCast_toNat (rank_ne_top κ h),
    ENat.natCast_toNat hA]

/-- On satisfiable intersections, `κ(X | A) = κ(Y | A) + κ(Z | A)` says that
`κ(A ∩ X) + κ(A) = κ(A ∩ Y) + κ(A ∩ Z)`. -/
theorem condRank_add_iff {A X Y Z : Set W} (hX : (A ∩ X).Nonempty) (hY : (A ∩ Y).Nonempty)
    (hZ : (A ∩ Z).Nonempty) :
    κ[X | A] = κ[Y | A] + κ[Z | A] ↔
      (rank κ (A ∩ X)).toNat + (rank κ A).toNat =
        (rank κ (A ∩ Y)).toNat + (rank κ (A ∩ Z)).toNat := by
  have hA : ∀ {S : Set W}, (A ∩ S).Nonempty →
      (rank κ A).toNat ≤ (rank κ (A ∩ S)).toNat := fun hS ↦
    ENat.toNat_le_toNat (rank_anti κ Set.inter_subset_left) (rank_ne_top κ hS)
  have h1 := hA hX
  have h2 := hA hY
  have h3 := hA hZ
  rw [condRank_eq κ hX, condRank_eq κ hY, condRank_eq κ hZ, ← Nat.cast_add, Nat.cast_inj]
  omega

variable {κ}

/-- Independence holds exactly when, for satisfiable members `B` of `𝔅` and `C` of `ℭ`, the
rank of `C` given `B` is the rank of `C` (Theorem 8, (a) and (b)). -/
theorem independent_iff_condRank :
    Independent κ 𝔅 ℭ ↔ ∀ B C, 𝔅.Decides B → ℭ.Decides C → B.Nonempty → C.Nonempty →
      κ[C | B] = rank κ C := by
  constructor
  · intro h B C hB hC hB' hC'
    rw [condRank_of_ne_top _ (rank_ne_top κ hB'), h.rank_inter hB hC hB' hC',
      (ENat.addLECancellable_of_ne_top (rank_ne_top κ hB')).add_tsub_cancel_left]
  · intro h w v
    have heq : rank κ (𝔅.cell w ∩ ℭ.cell v) = rank κ (𝔅.cell w) + rank κ (ℭ.cell v) := by
      rw [← condRank_add_rank κ, h _ _ (𝔅.decides_cell w) (ℭ.decides_cell v)
        (𝔅.cell_nonempty w) (ℭ.cell_nonempty v), add_comm]
    refine ⟨Set.nonempty_iff_ne_empty.2 fun he ↦ ?_, heq⟩
    rw [he, rank_empty] at heq
    exact WithTop.add_ne_top.2 ⟨rank_ne_top κ (𝔅.cell_nonempty w),
      rank_ne_top κ (ℭ.cell_nonempty v)⟩ heq.symm

/-- Independence holds exactly when generalized conditionalization on any ranking of the atoms
of `𝔅` leaves the ranks of the satisfiable members of `ℭ` unchanged (Theorem 8, (a) and
(c)). -/
theorem independent_iff_condition :
    Independent κ 𝔅 ℭ ↔ ∀ (l : RankingFunction (Quotient 𝔅)) (C : Set W), ℭ.Decides C →
      C.Nonempty → rank (condition κ 𝔅 l) C = rank κ C := by
  constructor
  · intro h l C hC hC'
    refine le_antisymm ?_ ((le_rank_iff _).2 fun v hvC ↦ ?_)
    · obtain ⟨c, hc, ec⟩ := exists_apply_eq_rank κ hC'
      obtain ⟨b, hb⟩ := l.exists_eq_zero
      induction b using Quotient.inductionOn with
      | h b₀ =>
        obtain ⟨hne, heq⟩ := h b₀ c
        obtain ⟨v, ⟨hvb, hvc⟩, ev⟩ := exists_apply_eq_rank κ hne
        obtain ⟨n₀, hn₀⟩ := ENat.ne_top_iff_exists.1 (rank_ne_top κ (𝔅.cell_nonempty b₀))
        obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (rank_ne_top κ (ℭ.cell_nonempty c))
        have hv : κ v = n₀ + m := by
          rw [heq, ← hn₀, ← hm, ← Nat.cast_add] at ev
          exact_mod_cast ev
        have hmc : m ≤ κ c := by
          have := rank_le κ (ℭ.mem_cell_self c)
          rw [← hm] at this
          exact_mod_cast this
        have hrel : 𝔅 v b₀ := 𝔅.mem_cell.1 hvb
        refine (rank_le (condition κ 𝔅 l) (hC.cell_subset hc hvc)).trans ?_
        rw [condition_rank, Quotient.sound hrel, hb, zero_add, aPart, cell_eq_of_rel hrel, ← hn₀,
          ENat.toNat_natCast, ← ec, Nat.cast_le]
        omega
    · obtain ⟨hne, heq⟩ := h v v
      obtain ⟨n₀, hn₀⟩ := ENat.ne_top_iff_exists.1 (rank_ne_top κ (𝔅.cell_nonempty v))
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (rank_ne_top κ (ℭ.cell_nonempty v))
      have h1 : n₀ + m ≤ κ v := by
        have := rank_le κ (show v ∈ 𝔅.cell v ∩ ℭ.cell v from
          ⟨𝔅.mem_cell_self v, ℭ.mem_cell_self v⟩)
        rw [heq, ← hn₀, ← hm, ← Nat.cast_add] at this
        exact_mod_cast this
      have h2 : rank κ C ≤ m := hm ▸ rank_anti κ (hC.cell_subset hvC)
      refine h2.trans ?_
      rw [condition_rank, aPart, ← hn₀, ENat.toNat_natCast, Nat.cast_le]
      omega
  · intro h w v
    classical
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (rank_ne_top κ (ℭ.cell_nonempty v))
    obtain ⟨n₀, hn₀⟩ := ENat.ne_top_iff_exists.1 (rank_ne_top κ (𝔅.cell_nonempty w))
    let l : RankingFunction (Quotient 𝔅) :=
      { toFun := Quotient.lift (fun x ↦ if 𝔅 x w then 0 else n + 1) fun x y hxy ↦ by
          simp only [show 𝔅 x w ↔ 𝔅 y w from
            ⟨fun h ↦ 𝔅.trans (𝔅.symm hxy) h, fun h ↦ 𝔅.trans hxy h⟩]
        exists_eq_zero' := ⟨Quotient.mk _ w, by simp⟩ }
    have hl : ∀ x, l (Quotient.mk 𝔅 x) = if 𝔅 x w then 0 else n + 1 := fun x ↦ rfl
    have hC := h l (ℭ.cell v) (ℭ.decides_cell v) (ℭ.cell_nonempty v)
    rw [← hn] at hC
    have hgt : ∀ x ∈ ℭ.cell v, ¬ 𝔅 x w → n + 1 ≤ condition κ 𝔅 l x := fun x _ hx ↦ by
      rw [condition_rank, hl, ite_eq_right hx]
      exact Nat.le_add_right _ _
    have hne : (𝔅.cell w ∩ ℭ.cell v).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      have : (n + 1 : ℕ∞) ≤ rank (condition κ 𝔅 l) (ℭ.cell v) :=
        (le_rank_iff _).2 fun x hx ↦ by
          exact_mod_cast hgt x hx fun hxw ↦ Set.eq_empty_iff_forall_notMem.1 hempty x ⟨hxw, hx⟩
      rw [hC] at this
      exact absurd (by exact_mod_cast this : n + 1 ≤ n) (by omega)
    refine ⟨hne, ?_⟩
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (rank_ne_top κ hne)
    rw [← hk, ← hn₀, ← hn, ← Nat.cast_add, Nat.cast_inj]
    have hk₀ : n₀ ≤ k := by
      have := rank_anti κ (Set.inter_subset_left (s := 𝔅.cell w) (t := ℭ.cell v))
      rw [← hn₀, ← hk] at this
      exact_mod_cast this
    -- the minimum over the atom of ℭ is attained at a world of the atom of 𝔅
    obtain ⟨x, ⟨hxb, hxc⟩, ex⟩ := exists_apply_eq_rank κ hne
    have hx : κ x = k := by rw [← hk] at ex; exact_mod_cast ex
    have hrelx : 𝔅 x w := 𝔅.mem_cell.1 hxb
    have hle : n ≤ k - n₀ := by
      have := rank_le (condition κ 𝔅 l) hxc
      rw [hC, condition_rank, hl, ite_eq_left hrelx, zero_add, aPart, cell_eq_of_rel hrelx, ← hn₀,
        ENat.toNat_natCast, hx] at this
      exact_mod_cast this
    obtain ⟨y, hyc, ey⟩ := exists_apply_eq_rank (condition κ 𝔅 l) (ℭ.cell_nonempty v)
    rw [hC] at ey
    have hy : condition κ 𝔅 l y = n := by exact_mod_cast ey
    by_cases hyw : 𝔅 y w
    · have hky : k ≤ κ y := by
        have := rank_le κ (show y ∈ 𝔅.cell w ∩ ℭ.cell v from ⟨hyw, hyc⟩)
        rw [← hk] at this
        exact_mod_cast this
      rw [condition_rank, hl, ite_eq_left hyw, zero_add, aPart, cell_eq_of_rel hyw, ← hn₀,
        ENat.toNat_natCast] at hy
      omega
    · have := hgt y hyc hyw
      omega

end Independence

/-! ### Conditional independence -/

section CondIndependence

variable (𝔅 ℭ : Setoid W) (A : Set W)

/-- `ℭ` is independent of `𝔅` given `A` with respect to `κ` (Definition 10) when
`κ(B ∩ C | A) = κ(B | A) + κ(C | A)` for atoms `B` of `𝔅` and `C` of `ℭ` meeting `A`. -/
def CondIndependent : Prop :=
  ∀ w v, (A ∩ 𝔅.cell w ∩ ℭ.cell v).Nonempty →
    κ[𝔅.cell w ∩ ℭ.cell v | A] = κ[𝔅.cell w | A] + κ[ℭ.cell v | A]

/-- `ℭ` is independent of `𝔅` given the subfield `𝔇` when it is so given each atom of `𝔇`. -/
def CondIndependentOn (𝔇 : Setoid W) : Prop := ∀ d, CondIndependent κ 𝔅 ℭ (𝔇.cell d)

variable {κ 𝔅 ℭ A}

theorem CondIndependent.symm (h : CondIndependent κ 𝔅 ℭ A) : CondIndependent κ ℭ 𝔅 A :=
  fun w v hne ↦ by
    rw [Set.inter_right_comm] at hne
    rw [Set.inter_comm, h v w hne, add_comm]

theorem CondIndependentOn.symm {𝔇 : Setoid W} (h : CondIndependentOn κ 𝔅 ℭ 𝔇) :
    CondIndependentOn κ ℭ 𝔅 𝔇 :=
  fun d ↦ (h d).symm

/-- If `ℭ` is independent of `𝔅` given `𝔇 + 𝔈` and `𝔇` is independent of `𝔅` given `𝔈`, then
`ℭ + 𝔇` is independent of `𝔅` given `𝔈` (Theorem 11). -/
theorem CondIndependentOn.inf {𝔇 𝔈 : Setoid W} (h₁ : CondIndependentOn κ 𝔅 ℭ (𝔇 ⊓ 𝔈))
    (h₂ : CondIndependentOn κ 𝔅 𝔇 𝔈) : CondIndependentOn κ 𝔅 (ℭ ⊓ 𝔇) 𝔈 := by
  intro e w v hne
  rw [cell_inf] at hne ⊢
  obtain ⟨x, ⟨hxE, hxB⟩, hxC, hxD⟩ := hne
  have hE : 𝔈.cell x = 𝔈.cell e := cell_eq_of_rel (𝔈.mem_cell.1 hxE)
  have hD : 𝔇.cell x = 𝔇.cell v := cell_eq_of_rel (𝔇.mem_cell.1 hxD)
  have H1 := h₁ x w v
  have H2 := h₂ e w x
  rw [cell_inf, hD, hE] at H1
  rw [hD] at H2
  specialize H1 ⟨x, ⟨⟨hxD, hxE⟩, hxB⟩, hxC⟩
  specialize H2 ⟨x, ⟨hxE, hxB⟩, hxD⟩
  have e1 : 𝔇.cell v ∩ 𝔈.cell e ∩ (𝔅.cell w ∩ ℭ.cell v) =
      𝔈.cell e ∩ (𝔅.cell w ∩ (ℭ.cell v ∩ 𝔇.cell v)) := by
    ext; simp only [Set.mem_inter_iff]; tauto
  have e2 : 𝔇.cell v ∩ 𝔈.cell e ∩ 𝔅.cell w = 𝔈.cell e ∩ (𝔅.cell w ∩ 𝔇.cell v) := by
    ext; simp only [Set.mem_inter_iff]; tauto
  have e3 : 𝔇.cell v ∩ 𝔈.cell e ∩ ℭ.cell v = 𝔈.cell e ∩ (ℭ.cell v ∩ 𝔇.cell v) := by
    ext; simp only [Set.mem_inter_iff]; tauto
  have e4 : 𝔇.cell v ∩ 𝔈.cell e = 𝔈.cell e ∩ 𝔇.cell v := Set.inter_comm _ _
  have hX1 : (𝔇.cell v ∩ 𝔈.cell e ∩ (𝔅.cell w ∩ ℭ.cell v)).Nonempty :=
    ⟨x, ⟨hxD, hxE⟩, hxB, hxC⟩
  have hY1 : (𝔇.cell v ∩ 𝔈.cell e ∩ 𝔅.cell w).Nonempty := ⟨x, ⟨hxD, hxE⟩, hxB⟩
  have hZ1 : (𝔇.cell v ∩ 𝔈.cell e ∩ ℭ.cell v).Nonempty := ⟨x, ⟨hxD, hxE⟩, hxC⟩
  have hX2 : (𝔈.cell e ∩ (𝔅.cell w ∩ 𝔇.cell v)).Nonempty := ⟨x, hxE, hxB, hxD⟩
  have hY2 : (𝔈.cell e ∩ 𝔅.cell w).Nonempty := ⟨x, hxE, hxB⟩
  have hZ2 : (𝔈.cell e ∩ 𝔇.cell v).Nonempty := ⟨x, hxE, hxD⟩
  have hX3 : (𝔈.cell e ∩ (𝔅.cell w ∩ (ℭ.cell v ∩ 𝔇.cell v))).Nonempty :=
    ⟨x, hxE, hxB, hxC, hxD⟩
  have hZ3 : (𝔈.cell e ∩ (ℭ.cell v ∩ 𝔇.cell v)).Nonempty := ⟨x, hxE, hxC, hxD⟩
  rw [condRank_add_iff κ hX1 hY1 hZ1, e1, e2, e3, e4] at H1
  rw [condRank_add_iff κ hX2 hY2 hZ2] at H2
  rw [condRank_add_iff κ hX3 hY2 hZ3]
  omega

/-- If `𝔅` is independent of `ℭ` given `𝔇 + 𝔈` and of `𝔇` given `𝔈`, then it is independent
of `ℭ + 𝔇` given `𝔈` (Theorem 12). -/
theorem CondIndependentOn.inf' {𝔇 𝔈 : Setoid W} (h₁ : CondIndependentOn κ ℭ 𝔅 (𝔇 ⊓ 𝔈))
    (h₂ : CondIndependentOn κ 𝔇 𝔅 𝔈) : CondIndependentOn κ (ℭ ⊓ 𝔇) 𝔅 𝔈 :=
  (CondIndependentOn.inf h₁.symm h₂.symm).symm

end CondIndependence

end Spohn1988
