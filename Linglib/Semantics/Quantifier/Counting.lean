module

public import Linglib.Semantics.Quantifier.Basic
public import Linglib.Semantics.Quantifier.NumberTree
public import Linglib.Core.Data.Set.Card
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.Linarith

/-!
# Counting generalized quantifiers

The counting quantifiers *most*, *few*, *half*, *both*, *neither*, *at least n*, *at most n*,
*exactly n*, *all but n* and *between n and k* hold of `A` and `B` according to `|A \ B|` and
`|A ∩ B|` alone, so each is the quantifier of a set of points on van Benthem's tree of numbers.
Defined that way they are conservative and permutation invariant by construction, and their
monotonicity, smoothness and proportionality are read off the tree. Sizes are `Set.ncard`,
which asks for no decidability and is `0` on an infinite set, so on an infinite restrictor the
counting quantifiers take junk values; the theorems that state what they mean assume a finite
universe or finite arguments. The numerals are cardinal quantifiers of intervals of numbers. On
a finite type with decidable arguments each quantifier is decidable through the `Finset` count
of each size, so a concrete case closes by `decide`. A quantifier restricted to a finite set `s`
of individuals is the quantifier with restrictor `s ∩ A`.

## Main definitions

* `Quantifier.NumberTree.most`, `Quantifier.NumberTree.atLeast`, …: the trees of the counting
  quantifiers, with `Quantifier.NumberTree.threshold` for a proportion of the restrictor.
* `Quantifier.Det.most`, `Quantifier.Det.atLeast`, …: their quantifiers.
* `Quantifier.Det.Proportional`: dependence on the ratio of `|A ∩ B|` to `|A \ B|`.

## Main results

* `Quantifier.Det.smooth_most`, `Quantifier.Det.proportional_most`: *most* is smooth and
  proportional.
* `Quantifier.NumberTree.thresholdGt_one_two`: *more than half* is *most*.
* `Quantifier.Det.not_intersective_most`, `Quantifier.Det.not_monotone_half`: *most* is not
  intersective, and *half* is monotone in its scope in neither direction.

## References

* [barwise-cooper-1981]
* [keenan-stavi-1986]
* [peters-westerstahl-2006]
* [van-benthem-1984]
-/

@[expose] public section

namespace Quantifier

namespace NumberTree

/-! ### The trees of the counting quantifiers -/

/-- *Most* holds when more of `A` lies inside `B` than outside it. -/
protected def most : NumberTree := fun a b ↦ a < b

/-- *Few* holds when less of `A` lies inside `B` than outside it. -/
protected def few : NumberTree := fun a b ↦ b < a

/-- *Half* holds when as much of `A` lies inside `B` as outside it. -/
protected def half : NumberTree := fun a b ↦ a = b

/-- *Both* holds when `A` has two members, both in `B`. -/
protected def both : NumberTree := fun a b ↦ a = 0 ∧ b = 2

/-- *Neither* holds when `A` has two members, neither in `B`. -/
protected def neither : NumberTree := fun a b ↦ a = 2 ∧ b = 0

/-- *At least `n`* holds when at least `n` members of `A` lie in `B`. -/
protected def atLeast (n : ℕ) : NumberTree := cardinal (Set.Ici n)

/-- *At most `n`* holds when at most `n` members of `A` lie in `B`. -/
protected def atMost (n : ℕ) : NumberTree := cardinal (Set.Iic n)

/-- *Exactly `n`* holds when exactly `n` members of `A` lie in `B`. -/
protected def exactly (n : ℕ) : NumberTree := cardinal {n}

/-- *More than `n`* holds when more than `n` members of `A` lie in `B`. -/
protected def moreThan (n : ℕ) : NumberTree := cardinal (Set.Ioi n)

/-- *Fewer than `n`* holds when fewer than `n` members of `A` lie in `B`. -/
protected def fewerThan (n : ℕ) : NumberTree := cardinal (Set.Iio n)

/-- *All but `n`* holds when exactly `n` members of `A` lie outside `B`. -/
protected def allBut (n : ℕ) : NumberTree := fun a _ ↦ a = n

/-- *Between `n` and `k`* holds when between `n` and `k` members of `A` lie in `B`. -/
protected def between (n k : ℕ) : NumberTree := cardinal (Set.Icc n k)

/-- The threshold `n / d` holds when at least that proportion of `A` lies in `B`. -/
def threshold (n d : ℕ) : NumberTree := ofSizes fun x p ↦ n * p ≤ d * x

/-- The strict threshold `n / d` holds when more than that proportion of `A` lies in `B`. -/
def thresholdGt (n d : ℕ) : NumberTree := ofSizes fun x p ↦ n * p < d * x

instance : DecidableRel NumberTree.most := fun a b ↦ Nat.decLt a b
instance : DecidableRel NumberTree.few := fun a b ↦ Nat.decLt b a
instance : DecidableRel NumberTree.half := fun a b ↦ Nat.decEq a b
instance : DecidableRel NumberTree.both := fun a b ↦ inferInstanceAs (Decidable (a = 0 ∧ b = 2))
instance : DecidableRel NumberTree.neither := fun a b ↦ inferInstanceAs (Decidable (a = 2 ∧ b = 0))
instance (n : ℕ) : DecidableRel (NumberTree.atLeast n) :=
  inferInstanceAs (DecidableRel (cardinal (Set.Ici n)))
instance (n : ℕ) : DecidableRel (NumberTree.atMost n) :=
  inferInstanceAs (DecidableRel (cardinal (Set.Iic n)))
instance (n : ℕ) : DecidableRel (NumberTree.exactly n) :=
  inferInstanceAs (DecidableRel (cardinal {n}))
instance (n : ℕ) : DecidableRel (NumberTree.moreThan n) :=
  inferInstanceAs (DecidableRel (cardinal (Set.Ioi n)))
instance (n : ℕ) : DecidableRel (NumberTree.fewerThan n) :=
  inferInstanceAs (DecidableRel (cardinal (Set.Iio n)))
instance (n : ℕ) : DecidableRel (NumberTree.allBut n) := fun a _ ↦ Nat.decEq a n
instance (n k : ℕ) : DecidableRel (NumberTree.between n k) :=
  inferInstanceAs (DecidableRel (cardinal (Set.Icc n k)))
instance (n d : ℕ) : DecidableRel (threshold n d) := fun a b ↦
  inferInstanceAs (Decidable (n * (a + b) ≤ d * b))
instance (n d : ℕ) : DecidableRel (thresholdGt n d) := fun a b ↦
  inferInstanceAs (Decidable (n * (a + b) < d * b))

theorem innerNeg_most : NumberTree.most.innerNeg = NumberTree.few := rfl

theorem innerNeg_both : NumberTree.both.innerNeg = NumberTree.neither := by
  funext a b; exact propext and_comm

theorem compl_atLeast_succ (n : ℕ) : (NumberTree.atLeast (n + 1))ᶜ = NumberTree.atMost n := by
  funext a b; exact propext (show ¬ n + 1 ≤ b ↔ b ≤ n by omega)

theorem atLeast_inf_atMost (n : ℕ) :
    NumberTree.atLeast n ⊓ NumberTree.atMost n = NumberTree.exactly n := by
  funext a b; exact propext (show n ≤ b ∧ b ≤ n ↔ b = n by omega)

/-- *More than half* is *most*. -/
theorem thresholdGt_one_two : thresholdGt 1 2 = NumberTree.most := by
  funext a b; exact propext (show 1 * (a + b) < 2 * b ↔ a < b by omega)

theorem scopeMonotone_most : NumberTree.most.ScopeMonotone := fun _ _ h ↦ by
  grind [NumberTree.most]

theorem scopeAntitone_few : NumberTree.few.ScopeAntitone := scopeMonotone_most.innerNeg

theorem scopeMonotone_atLeast (n : ℕ) : (NumberTree.atLeast n).ScopeMonotone :=
  scopeMonotone_cardinal_iff.2 (.Ici n)

theorem scopeAntitone_atMost (n : ℕ) : (NumberTree.atMost n).ScopeAntitone :=
  scopeAntitone_cardinal_iff.2 (.Iic n)

theorem scopeMonotone_threshold (n d : ℕ) : (threshold n d).ScopeMonotone := fun _ _ h ↦ by
  simp only [threshold, ofSizes] at *; nlinarith

/-! ### Proportionality -/

/-- A tree is proportional when on nonempty rows it depends only on the ratio of `b` to `a`. -/
def Proportional (q : NumberTree) : Prop :=
  ∀ a b a' b', 0 < a + b → 0 < a' + b' → b * a' = b' * a → (q a b ↔ q a' b')

theorem Proportional.innerNeg {q : NumberTree} (h : q.Proportional) : q.innerNeg.Proportional :=
  fun a b a' b' h₁ h₂ hx ↦ h b a b' a' (by omega) (by omega) (by linarith)

theorem proportional_most : NumberTree.most.Proportional := fun a b a' b' _ _ _ ↦ by
  unfold NumberTree.most; constructor <;> intro <;> nlinarith

theorem proportional_few : NumberTree.few.Proportional := proportional_most.innerNeg

theorem proportional_half : NumberTree.half.Proportional := fun a b a' b' _ _ _ ↦ by
  unfold NumberTree.half; constructor <;> rintro rfl <;> nlinarith

end NumberTree

namespace Det

variable {α : Type*}

/-! ### The counting quantifiers -/

/-- *Most* `A` are `B` when more of the `A` are `B` than are not. -/
def most : Det α := NumberTree.most.toDet

/-- *Few* `A` are `B` when fewer of the `A` are `B` than are not, the inner negation of
*most*. -/
def few : Det α := NumberTree.few.toDet

/-- *Half* the `A` are `B` when as many of the `A` are `B` as are not. -/
def half : Det α := NumberTree.half.toDet

/-- *Both* is *every* on a restrictor of two, Keenan and Stavi's *each of the two*. -/
def both : Det α := NumberTree.both.toDet

/-- *Neither* is *no* on a restrictor of two, Keenan and Stavi's *not one of the two*. -/
def neither : Det α := NumberTree.neither.toDet

/-- *At least `n`* `A` are `B` when `n ≤ |A ∩ B|`. -/
def atLeast (n : ℕ) : Det α := (NumberTree.atLeast n).toDet

/-- *At most `n`* `A` are `B` when `|A ∩ B| ≤ n`. -/
def atMost (n : ℕ) : Det α := (NumberTree.atMost n).toDet

/-- *Exactly `n`* `A` are `B` when `|A ∩ B| = n`. -/
def exactly (n : ℕ) : Det α := (NumberTree.exactly n).toDet

/-- *All but `n`* `A` are `B` when `|A \ B| = n`. -/
def allBut (n : ℕ) : Det α := (NumberTree.allBut n).toDet

/-- *Between `n` and `k`* `A` are `B` when `n ≤ |A ∩ B| ≤ k`. -/
def between (n k : ℕ) : Det α := (NumberTree.between n k).toDet

section Decidable

variable [Fintype α] (A B : Set α) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] (n k : ℕ)

instance : Decidable (most A B) := NumberTree.toDet.decidable ..
instance : Decidable (few A B) := NumberTree.toDet.decidable ..
instance : Decidable (half A B) := NumberTree.toDet.decidable ..
instance : Decidable (both A B) := NumberTree.toDet.decidable ..
instance : Decidable (neither A B) := NumberTree.toDet.decidable ..
instance : Decidable (atLeast n A B) := NumberTree.toDet.decidable ..
instance : Decidable (atMost n A B) := NumberTree.toDet.decidable ..
instance : Decidable (exactly n A B) := NumberTree.toDet.decidable ..
instance : Decidable (allBut n A B) := NumberTree.toDet.decidable ..
instance : Decidable (between n k A B) := NumberTree.toDet.decidable ..

end Decidable

variable {A B : Set α} {n : ℕ}

theorem most_apply : most A B ↔ (A \ B).ncard < (A ∩ B).ncard := Iff.rfl

theorem few_apply : few A B ↔ (A ∩ B).ncard < (A \ B).ncard := Iff.rfl

theorem half_apply : half A B ↔ (A \ B).ncard = (A ∩ B).ncard := Iff.rfl

theorem atLeast_apply : atLeast n A B ↔ n ≤ (A ∩ B).ncard := Iff.rfl

theorem atMost_apply : atMost n A B ↔ (A ∩ B).ncard ≤ n := Iff.rfl

theorem exactly_apply : exactly n A B ↔ (A ∩ B).ncard = n := Iff.rfl

theorem allBut_apply : allBut n A B ↔ (A \ B).ncard = n := Iff.rfl

theorem conservative_most : (most : Det α).Conservative := NumberTree.conservative_toDet _

theorem conservative_atLeast (n : ℕ) : (atLeast n : Det α).Conservative :=
  NumberTree.conservative_toDet _

theorem conservative_exactly (n : ℕ) : (exactly n : Det α).Conservative :=
  NumberTree.conservative_toDet _

theorem intersective_exactly (n : ℕ) : (exactly n : Det α).Intersective :=
  fun _ _ _ _ h ↦ by rw [exactly_apply, exactly_apply, h]

instance symm_exactly (n : ℕ) : Std.Symm (exactly n : Det α) := (intersective_exactly n).symm

/-! ### Identities -/

theorem atMost_eq_compl_atLeast_succ (n : ℕ) : (atMost n : Det α) = (atLeast (n + 1))ᶜ := by
  rw [atMost, atLeast, ← NumberTree.toDet_compl, NumberTree.compl_atLeast_succ]

theorem exactly_eq_atLeast_inf_atMost (n : ℕ) : (exactly n : Det α) = atLeast n ⊓ atMost n := by
  rw [exactly, atLeast, atMost, ← NumberTree.toDet_inf, NumberTree.atLeast_inf_atMost]

theorem every_eq_toDet_all [Finite α] : (every : Det α) = NumberTree.all.toDet :=
  funext₂ fun _ _ ↦ propext NumberTree.toDet_all_iff.symm

theorem some_eq_toDet_some [Finite α] : (Det.some : Det α) = NumberTree.some.toDet :=
  funext₂ fun _ _ ↦ propext NumberTree.toDet_some_iff.symm

theorem no_eq_toDet_no [Finite α] : (no : Det α) = NumberTree.no.toDet :=
  funext₂ fun _ _ ↦ propext (no_iff_not_some.trans NumberTree.toDet_no_iff.symm)

theorem some_eq_atLeast_one [Finite α] : (Det.some : Det α) = atLeast 1 := by
  rw [some_eq_toDet_some, atLeast]
  congr 1
  funext a b
  exact propext Nat.one_le_iff_ne_zero.symm

theorem no_eq_atMost_zero [Finite α] : (no : Det α) = atMost 0 := by
  rw [← compl_some, some_eq_atLeast_one, atMost_eq_compl_atLeast_succ]

theorem allBut_zero_eq_every [Finite α] : (allBut 0 : Det α) = every := by
  rw [every_eq_toDet_all]; rfl

/-! ### Monotonicity -/

theorem scopeMonotone_most [Finite α] : (most : Det α).ScopeMonotone :=
  NumberTree.scopeMonotone_most.toDet

/-- *Most* lies below its dual: if most `A` are `B`, then it is not the case that most `A` are not
`B`. -/
theorem most_le_dual (A : Set α) : most A ≤ (most A).dual := fun B h h' ↦ by
  have h' : (A \ Bᶜ).ncard < (A ∩ Bᶜ).ncard := h'
  rw [Set.diff_compl, ← Set.diff_eq] at h'
  exact lt_asymm (most_apply.1 h) h'

theorem scopeAntitone_few [Finite α] : (few : Det α).ScopeAntitone :=
  NumberTree.scopeAntitone_few.toDet

theorem scopeMonotone_atLeast [Finite α] (n : ℕ) : (atLeast n : Det α).ScopeMonotone :=
  (NumberTree.scopeMonotone_atLeast n).toDet

theorem scopeAntitone_atMost [Finite α] (n : ℕ) : (atMost n : Det α).ScopeAntitone :=
  (NumberTree.scopeAntitone_atMost n).toDet

theorem monotone_atLeast [Finite α] (n : ℕ) (A : Set α) : Monotone (atLeast n A) :=
  scopeMonotone_atLeast n A

theorem antitone_atMost [Finite α] (n : ℕ) (A : Set α) : Antitone (atMost n A) :=
  scopeAntitone_atMost n A

theorem not_scopeAntitone_most [Finite α] [Nonempty α] : ¬ (most : Det α).ScopeAntitone :=
  fun h ↦ by
    have := h Set.univ (Set.empty_subset Set.univ)
    simp [most_apply, Set.ncard_univ, Nat.card_pos] at this

theorem restrictorMonotone_atLeast [Finite α] (n : ℕ) : (atLeast n : Det α).RestrictorMonotone :=
  fun B _ _ h hq ↦ (atLeast_apply.1 hq).trans (Set.ncard_le_ncard (Set.inter_subset_inter_left B h))

theorem restrictorAntitone_atMost [Finite α] (n : ℕ) : (atMost n : Det α).RestrictorAntitone := by
  rw [atMost_eq_compl_atLeast_succ]; exact (restrictorMonotone_atLeast _).compl

/-! ### Smoothness -/

theorem downNE_most [Finite α] : (most : Det α).DownNEMon := by
  intro A B A' h₁ h₂ hq
  rw [most_apply] at *
  rw [Set.Subset.antisymm (Set.inter_subset_inter_left B h₁) fun x hx ↦ ⟨h₂ hx, hx.2⟩]
  exact (Set.ncard_le_ncard (Set.sdiff_subset_sdiff_left h₁)).trans_lt hq

theorem upSE_most [Finite α] : (most : Det α).UpSEMon := by
  intro A B A' h₁ h₂ hq
  rw [most_apply] at *
  rw [Set.Subset.antisymm (a := A' \ B) (b := A \ B) (fun x hx ↦ ⟨h₂ hx, hx.2⟩)
    (Set.sdiff_subset_sdiff_left h₁)]
  exact hq.trans_le (Set.ncard_le_ncard (Set.inter_subset_inter_left B h₁))

theorem smooth_most [Finite α] : (most : Det α).Smooth := ⟨downNE_most, upSE_most⟩

theorem smooth_atLeast [Finite α] (n : ℕ) : (atLeast n : Det α).Smooth := by
  refine ⟨fun A B A' h₁ h₂ hq ↦ ?_, (restrictorMonotone_atLeast n).upSE⟩
  rwa [atLeast_apply,
    Set.Subset.antisymm (Set.inter_subset_inter_left B h₁) fun x hx ↦ ⟨h₂ hx, hx.2⟩]

theorem coSmooth_atMost [Finite α] (n : ℕ) : (atMost n : Det α).CoSmooth := by
  rw [atMost_eq_compl_atLeast_succ]; exact smooth_iff_coSmooth_compl.mp (smooth_atLeast _)

/-! ### Proportionality -/

/-- A determiner denotation is proportional when on nonempty restrictors its truth depends only
on the ratio of `|A ∩ B|` to `|A \ B|`. -/
def Proportional (d : Det α) : Prop :=
  ∀ A B A' B' : Set α, 0 < (A \ B).ncard + (A ∩ B).ncard → 0 < (A' \ B').ncard + (A' ∩ B').ncard →
    (A ∩ B).ncard * (A' \ B').ncard = (A' ∩ B').ncard * (A \ B).ncard → (d A B ↔ d A' B')

theorem _root_.Quantifier.NumberTree.Proportional.toDet {q : NumberTree} (h : q.Proportional) :
    (q.toDet : Det α).Proportional := fun _ _ _ _ ↦ h _ _ _ _

theorem proportional_most : (most : Det α).Proportional := NumberTree.proportional_most.toDet

theorem proportional_few : (few : Det α).Proportional := NumberTree.proportional_few.toDet

theorem proportional_half : (half : Det α).Proportional := NumberTree.proportional_half.toDet

/-! ### Counterexamples on small universes

The proportional quantifiers fail `Intersective`, [keenan-stavi-1986]'s condition for felicity
in *there*-sentences, since their truth depends on `|A \ B|` and not just on `|A ∩ B|`; *few*
already fails it on one individual, *most* and *half* on two. This is not the weakness of
[barwise-cooper-1981], which means being neither positive nor negative strong: their Table II
lists *few* as weak and does not classify *half*, and they allow a weak *many* or *few* to fail
the intersection condition. -/

/-- *Most* is not intersective. -/
theorem not_intersective_most : ¬ (most : Det (Fin 2)).Intersective := fun h ↦ by
  have := h.iff_inter_univ (A := Set.univ) (B := {x | x = 0})
  revert this; decide

theorem not_intersective_few : ¬ (few : Det (Fin 1)).Intersective := fun h ↦ by
  have := h.iff_inter_univ (A := Set.univ) (B := ∅)
  revert this; decide

theorem not_intersective_half : ¬ (half : Det (Fin 2)).Intersective := fun h ↦ by
  have := h.iff_inter_univ (A := Set.univ) (B := {x | x = 0})
  revert this; decide

theorem not_restrictorMonotone_most : ¬ (most : Det (Fin 3)).RestrictorMonotone := fun h ↦ by
  have hle : {x : Fin 3 | x = 0} ⊆ {x | x ≠ 1} := fun x hx ↦ by subst hx; decide
  have : most {x : Fin 3 | x = 0} {x | x = 0} → most {x : Fin 3 | x ≠ 1} {x | x = 0} :=
    h _ hle
  revert this; decide

theorem not_restrictorAntitone_most : ¬ (most : Det (Fin 3)).RestrictorAntitone := fun h ↦ by
  have : most Set.univ {x : Fin 3 | x ≠ 2} → most {x : Fin 3 | x = 2} {x | x ≠ 2} :=
    h _ (Set.subset_univ _)
  revert this; decide

theorem not_symm_most : ¬ Std.Symm (most : Det (Fin 3)) := fun h ↦ by
  have := h.symm {x | x = 0} {x | x = 0 ∨ x = 1}
  revert this; decide

theorem not_scopeMonotone_half : ¬ (half : Det (Fin 3)).ScopeMonotone := fun h ↦ by
  have hle : {x : Fin 3 | x = 0} ⊆ {x | x = 0 ∨ x = 1} := fun _ ↦ Or.inl
  have : half {x : Fin 3 | x = 0 ∨ x = 1} {x | x = 0} →
      half {x : Fin 3 | x = 0 ∨ x = 1} {x | x = 0 ∨ x = 1} := h _ hle
  revert this; decide

theorem not_scopeAntitone_half : ¬ (half : Det (Fin 3)).ScopeAntitone := fun h ↦ by
  have : half {x : Fin 3 | x = 0 ∨ x = 1} {x | x = 0} →
      half {x : Fin 3 | x = 0 ∨ x = 1} ∅ := h _ (Set.empty_subset _)
  revert this; decide

/-- *Half* is neither monotone nor antitone in its scope. -/
theorem not_monotone_half :
    ¬ (half : Det (Fin 3)).ScopeMonotone ∧ ¬ (half : Det (Fin 3)).ScopeAntitone :=
  ⟨not_scopeMonotone_half, not_scopeAntitone_half⟩

theorem not_monotone_exactly [Fintype α] {n : ℕ} (h : n < Fintype.card α) :
    ¬ Monotone (exactly n (Set.univ : Set α)) := fun hq ↦ by
  obtain ⟨t, -, rfl⟩ := Finset.exists_subset_card_eq (s := .univ) (n := n) (by simpa using h.le)
  have := hq (a := ↑t) (Set.subset_univ _) (by simp [exactly_apply, Set.ncard_coe_finset])
  simp [exactly_apply, Set.ncard_univ, Nat.card_eq_fintype_card] at this
  omega

theorem not_antitone_exactly [Fintype α] {n : ℕ} (hn : n ≠ 0) (h : n ≤ Fintype.card α) :
    ¬ Antitone (exactly n (Set.univ : Set α)) := fun hq ↦ by
  obtain ⟨t, -, rfl⟩ := Finset.exists_subset_card_eq (s := .univ) (n := n) (by simpa using h)
  have := hq (a := ∅) (b := ↑t) (Set.empty_subset _) (by simp [exactly_apply, Set.ncard_coe_finset])
  simp [exactly_apply] at this
  omega

/-- *Exactly n* satisfies Barwise and Cooper's universals, as the conjunction of *at least n* and
*at most n*. -/
theorem satisfiesUniversals_exactly [Finite α] (n : ℕ) :
    (exactly n : Det α).SatisfiesUniversals :=
  ⟨conservative_exactly n, fun A ↦ ⟨atLeast n A, atMost n A, .inl (monotone_atLeast n A),
    .inr (antitone_atMost n A), by rw [exactly_eq_atLeast_inf_atMost]; rfl⟩⟩

/-- *All but n* satisfies Barwise and Cooper's universals, as the conjunction of *all but at most n*
and *at least n are not*. -/
theorem satisfiesUniversals_allBut [Finite α] (n : ℕ) : (allBut n : Det α).SatisfiesUniversals :=
  ⟨NumberTree.conservative_toDet _, fun A ↦ ⟨fun B ↦ (A \ B).ncard ≤ n, fun B ↦ n ≤ (A \ B).ncard,
    .inl fun _ _ h hB ↦ (Set.ncard_le_ncard (Set.sdiff_subset_sdiff_right h)).trans hB,
    .inr fun _ _ h hB ↦ hB.trans (Set.ncard_le_ncard (Set.sdiff_subset_sdiff_right h)),
    funext fun _ ↦ propext le_antisymm_iff⟩⟩

theorem both_fin2 : both (α := Fin 2) Set.univ Set.univ := by decide

theorem not_both_fin3 : ¬ both (α := Fin 3) Set.univ Set.univ := by decide

theorem most_singleton_iff (j : α) (B : Set α) : most {j} B ↔ j ∈ B := by
  by_cases h : j ∈ B
  · rw [most_apply, Set.sdiff_eq_empty.2 (Set.singleton_subset_iff.2 h),
      Set.singleton_inter_of_mem h]
    simpa using h
  · rw [most_apply, Set.singleton_inter_of_notMem h]
    simpa using h

end Det

end Quantifier
