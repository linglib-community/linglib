module

public import Linglib.Semantics.Quantification.Basic
public import Linglib.Semantics.Quantification.NumberTree
public import Linglib.Core.Data.Set.Card
public import Mathlib.Tactic.Linarith

/-!
# Counting generalized quantifiers

The counting quantifiers *most*, *few*, *half*, *both*, *neither*, *at least n*, *at most n*,
*exactly n*, *all but n* and *between n and k* hold of `A` and `B` according to `|A \ B|` and
`|A ∩ B|` alone, so each is the quantifier of a set of points on van Benthem's tree of numbers.
Defined that way they are conservative and permutation invariant by construction, and their
monotonicity, smoothness and proportionality are read off the tree. Sizes are `Set.ncard`,
which asks for no decidability. On a finite type with decidable arguments each quantifier is
decidable through the `Finset` count of each size, so a concrete case closes by `decide`. A
quantifier restricted to a finite set `s` of individuals is the quantifier with restrictor
`x ∈ s ∧ A x`.

## Main definitions

* `Quantifier.NumberTree.most`, `Quantifier.NumberTree.atLeast`, …: the trees of the counting
  quantifiers, with `Quantifier.NumberTree.threshold` for a proportion of the restrictor.
* `Quantifier.GQ.most`, `Quantifier.GQ.atLeast`, …: their quantifiers.
* `Quantifier.GQ.Proportional`: dependence on the ratio of `|A ∩ B|` to `|A \ B|`.

## Main results

* `Quantifier.GQ.smooth_most`, `Quantifier.GQ.proportional_most`: *most* is smooth and
  proportional.
* `Quantifier.NumberTree.thresholdGt_one_two`: *more than half* is *most*.
* `Quantifier.GQ.not_existential_most`, `Quantifier.GQ.not_monotone_half`: *most* is not
  existential, and *half* is monotone in its scope in neither direction.

## References

* [barwise-cooper-1981]
* [keenan-stavi-1986]
* [peters-westerstahl-2006]
* [van-benthem-1984]
* [van-de-pol-etal-2023]
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
protected def atLeast (n : ℕ) : NumberTree := fun _ b ↦ n ≤ b

/-- *At most `n`* holds when at most `n` members of `A` lie in `B`. -/
protected def atMost (n : ℕ) : NumberTree := fun _ b ↦ b ≤ n

/-- *Exactly `n`* holds when exactly `n` members of `A` lie in `B`. -/
protected def exactly (n : ℕ) : NumberTree := fun _ b ↦ b = n

/-- *All but `n`* holds when exactly `n` members of `A` lie outside `B`. -/
protected def allBut (n : ℕ) : NumberTree := fun a _ ↦ a = n

/-- *Between `n` and `k`* holds when between `n` and `k` members of `A` lie in `B`. -/
protected def between (n k : ℕ) : NumberTree := fun _ b ↦ n ≤ b ∧ b ≤ k

/-- The threshold `n / d` holds when at least that proportion of `A` lies in `B`. -/
def threshold (n d : ℕ) : NumberTree := ofSizes fun x p ↦ n * p ≤ d * x

/-- The strict threshold `n / d` holds when more than that proportion of `A` lies in `B`. -/
def thresholdGt (n d : ℕ) : NumberTree := ofSizes fun x p ↦ n * p < d * x

instance : DecidableRel NumberTree.most := fun a b ↦ Nat.decLt a b
instance : DecidableRel NumberTree.few := fun a b ↦ Nat.decLt b a
instance : DecidableRel NumberTree.half := fun a b ↦ Nat.decEq a b
instance : DecidableRel NumberTree.both := fun a b ↦ inferInstanceAs (Decidable (a = 0 ∧ b = 2))
instance : DecidableRel NumberTree.neither := fun a b ↦ inferInstanceAs (Decidable (a = 2 ∧ b = 0))
instance (n : ℕ) : DecidableRel (NumberTree.atLeast n) := fun _ b ↦ Nat.decLe n b
instance (n : ℕ) : DecidableRel (NumberTree.atMost n) := fun _ b ↦ Nat.decLe b n
instance (n : ℕ) : DecidableRel (NumberTree.exactly n) := fun _ b ↦ Nat.decEq b n
instance (n : ℕ) : DecidableRel (NumberTree.allBut n) := fun a _ ↦ Nat.decEq a n
instance (n k : ℕ) : DecidableRel (NumberTree.between n k) := fun _ b ↦
  inferInstanceAs (Decidable (n ≤ b ∧ b ≤ k))
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

theorem scopeMonotone_atLeast (n : ℕ) : (NumberTree.atLeast n).ScopeMonotone := fun _ _ h ↦ by
  grind [NumberTree.atLeast]

theorem scopeAntitone_atMost (n : ℕ) : (NumberTree.atMost n).ScopeAntitone := fun _ _ h ↦ by
  grind [NumberTree.atMost]

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

namespace GQ

variable {α : Type*}

/-! ### The counting quantifiers -/

/-- *Most* `A` are `B` when more of the `A` are `B` than are not. -/
def most : GQ α := NumberTree.most.toGQ

/-- *Few* `A` are `B` when fewer of the `A` are `B` than are not, the inner negation of
*most*. -/
def few : GQ α := NumberTree.few.toGQ

/-- *Half* the `A` are `B` when as many of the `A` are `B` as are not. -/
def half : GQ α := NumberTree.half.toGQ

/-- *Both* is *every* on a restrictor of two, Keenan and Stavi's *each of the two*. -/
def both : GQ α := NumberTree.both.toGQ

/-- *Neither* is *no* on a restrictor of two, Keenan and Stavi's *not one of the two*. -/
def neither : GQ α := NumberTree.neither.toGQ

/-- *At least `n`* `A` are `B` when `n ≤ |A ∩ B|`. -/
def atLeast (n : ℕ) : GQ α := (NumberTree.atLeast n).toGQ

/-- *At most `n`* `A` are `B` when `|A ∩ B| ≤ n`. -/
def atMost (n : ℕ) : GQ α := (NumberTree.atMost n).toGQ

/-- *Exactly `n`* `A` are `B` when `|A ∩ B| = n`. -/
def exactly (n : ℕ) : GQ α := (NumberTree.exactly n).toGQ

/-- *All but `n`* `A` are `B` when `|A \ B| = n`. -/
def allBut (n : ℕ) : GQ α := (NumberTree.allBut n).toGQ

/-- *Between `n` and `k`* `A` are `B` when `n ≤ |A ∩ B| ≤ k`. -/
def between (n k : ℕ) : GQ α := (NumberTree.between n k).toGQ

section Decidable

variable [Fintype α] (A B : α → Prop) [DecidablePred A] [DecidablePred B] (n k : ℕ)

instance : Decidable (most A B) := NumberTree.toGQ.decidable ..
instance : Decidable (few A B) := NumberTree.toGQ.decidable ..
instance : Decidable (half A B) := NumberTree.toGQ.decidable ..
instance : Decidable (both A B) := NumberTree.toGQ.decidable ..
instance : Decidable (neither A B) := NumberTree.toGQ.decidable ..
instance : Decidable (atLeast n A B) := NumberTree.toGQ.decidable ..
instance : Decidable (atMost n A B) := NumberTree.toGQ.decidable ..
instance : Decidable (exactly n A B) := NumberTree.toGQ.decidable ..
instance : Decidable (allBut n A B) := NumberTree.toGQ.decidable ..
instance : Decidable (between n k A B) := NumberTree.toGQ.decidable ..

end Decidable

variable {A B : α → Prop} {n : ℕ}

theorem most_apply : most A B ↔ {x | A x ∧ ¬ B x}.ncard < {x | A x ∧ B x}.ncard := Iff.rfl

theorem few_apply : few A B ↔ {x | A x ∧ B x}.ncard < {x | A x ∧ ¬ B x}.ncard := Iff.rfl

theorem half_apply : half A B ↔ {x | A x ∧ ¬ B x}.ncard = {x | A x ∧ B x}.ncard := Iff.rfl

theorem atLeast_apply : atLeast n A B ↔ n ≤ {x | A x ∧ B x}.ncard := Iff.rfl

theorem atMost_apply : atMost n A B ↔ {x | A x ∧ B x}.ncard ≤ n := Iff.rfl

theorem exactly_apply : exactly n A B ↔ {x | A x ∧ B x}.ncard = n := Iff.rfl

theorem conservative_most : Conservative (most : GQ α) := NumberTree.conservative_toGQ _

theorem conservative_atLeast (n : ℕ) : Conservative (atLeast n : GQ α) :=
  NumberTree.conservative_toGQ _

theorem conservative_exactly (n : ℕ) : Conservative (exactly n : GQ α) :=
  NumberTree.conservative_toGQ _

/-! ### Identities -/

theorem atMost_eq_compl_atLeast_succ (n : ℕ) : (atMost n : GQ α) = (atLeast (n + 1))ᶜ := by
  rw [atMost, atLeast, ← NumberTree.toGQ_compl, NumberTree.compl_atLeast_succ]

theorem exactly_eq_atLeast_inf_atMost (n : ℕ) : (exactly n : GQ α) = atLeast n ⊓ atMost n := by
  rw [exactly, atLeast, atMost, ← NumberTree.toGQ_inf, NumberTree.atLeast_inf_atMost]

theorem every_eq_toGQ_all [Finite α] : (every : GQ α) = NumberTree.all.toGQ := by
  funext A B
  simp only [every, NumberTree.toGQ, NumberTree.all, Set.ncard_eq_zero (Set.toFinite _),
    Set.eq_empty_iff_forall_notMem, Set.mem_ofPred_eq, not_and, not_not]

theorem no_eq_toGQ_no [Finite α] : (no : GQ α) = NumberTree.no.toGQ := by
  funext A B
  simp only [no, NumberTree.toGQ, NumberTree.no, Set.ncard_eq_zero (Set.toFinite _),
    Set.eq_empty_iff_forall_notMem, Set.mem_ofPred_eq, not_and]

theorem some_eq_atLeast_one [Finite α] : (GQ.some : GQ α) = atLeast 1 := by
  funext A B
  simp only [GQ.some, atLeast, NumberTree.toGQ, NumberTree.atLeast, Nat.one_le_iff_ne_zero,
    ne_eq, Set.ncard_eq_zero (Set.toFinite _), ← Set.nonempty_iff_ne_empty]
  rfl

theorem no_eq_atMost_zero [Finite α] : (no : GQ α) = atMost 0 := by
  rw [← compl_some, some_eq_atLeast_one, atMost_eq_compl_atLeast_succ]

theorem allBut_zero_eq_every [Finite α] : (allBut 0 : GQ α) = every := by
  rw [every_eq_toGQ_all]; rfl

/-! ### Monotonicity -/

theorem scopeMonotone_most [Finite α] : ScopeMonotone (most : GQ α) :=
  NumberTree.scopeMonotone_most.toGQ

theorem scopeAntitone_few [Finite α] : ScopeAntitone (few : GQ α) :=
  NumberTree.scopeAntitone_few.toGQ

theorem scopeMonotone_atLeast [Finite α] (n : ℕ) : ScopeMonotone (atLeast n : GQ α) :=
  (NumberTree.scopeMonotone_atLeast n).toGQ

theorem scopeAntitone_atMost [Finite α] (n : ℕ) : ScopeAntitone (atMost n : GQ α) :=
  (NumberTree.scopeAntitone_atMost n).toGQ

theorem monotone_atLeast [Finite α] (n : ℕ) (A : α → Prop) : Monotone (atLeast n A) :=
  scopeMonotone_atLeast n A

theorem antitone_atMost [Finite α] (n : ℕ) (A : α → Prop) : Antitone (atMost n A) :=
  scopeAntitone_atMost n A

theorem not_scopeAntitone_most [Finite α] [Nonempty α] : ¬ ScopeAntitone (most : GQ α) :=
  fun h ↦ by
    have := h (fun _ ↦ True) (bot_le (a := fun _ ↦ True))
    simp [most_apply, Set.ncard_univ, Nat.card_pos] at this

theorem restrictorMonotone_atLeast [Finite α] (n : ℕ) : RestrictorMonotone (atLeast n : GQ α) :=
  fun S R R' h hq ↦ (show n ≤ {x | R x ∧ S x}.ncard from hq).trans
    (Set.ncard_le_ncard (t := {x | R' x ∧ S x}) fun x hx ↦ ⟨h x hx.1, hx.2⟩)

theorem restrictorAntitone_atMost [Finite α] (n : ℕ) : RestrictorAntitone (atMost n : GQ α) := by
  rw [atMost_eq_compl_atLeast_succ]; exact (restrictorMonotone_atLeast _).compl

/-! ### Smoothness -/

theorem downNE_most [Finite α] : DownNEMon (most : GQ α) := by
  intro R S R' hR' hRS hq
  rw [most_apply] at *
  rw [show {x | R' x ∧ S x} = {x | R x ∧ S x} by ext; grind]
  exact (Set.ncard_le_ncard (t := {x | R x ∧ ¬ S x}) fun x hx ↦ ⟨hR' x hx.1, hx.2⟩).trans_lt hq

theorem upSE_most [Finite α] : UpSEMon (most : GQ α) := by
  intro R S R' hR hR'S hq
  rw [most_apply] at *
  rw [show {x | R' x ∧ ¬ S x} = {x | R x ∧ ¬ S x} by ext; grind]
  exact hq.trans_le (Set.ncard_le_ncard (t := {x | R' x ∧ S x}) fun x hx ↦ ⟨hR x hx.1, hx.2⟩)

theorem smooth_most [Finite α] : Smooth (most : GQ α) := ⟨downNE_most, upSE_most⟩

theorem smooth_atLeast [Finite α] (n : ℕ) : Smooth (atLeast n : GQ α) := by
  refine ⟨fun R S R' hR' hRS hq ↦ ?_, (restrictorMonotone_atLeast n).upSE⟩
  rwa [atLeast_apply, show {x | R' x ∧ S x} = {x | R x ∧ S x} by ext; grind]

theorem coSmooth_atMost [Finite α] (n : ℕ) : CoSmooth (atMost n : GQ α) := by
  rw [atMost_eq_compl_atLeast_succ]; exact (smooth_iff_coSmooth_compl _).mp (smooth_atLeast _)

/-! ### Proportionality -/

/-- A quantifier is proportional when on nonempty restrictors its truth depends only on the
ratio of `|A ∩ B|` to `|A \ B|`. -/
def Proportional (q : GQ α) : Prop :=
  ∀ A B A' B' : α → Prop,
    0 < {x | A x ∧ ¬ B x}.ncard + {x | A x ∧ B x}.ncard →
    0 < {x | A' x ∧ ¬ B' x}.ncard + {x | A' x ∧ B' x}.ncard →
    {x | A x ∧ B x}.ncard * {x | A' x ∧ ¬ B' x}.ncard =
      {x | A' x ∧ B' x}.ncard * {x | A x ∧ ¬ B x}.ncard →
    (q A B ↔ q A' B')

/-- The quantifier of a proportional tree is proportional. -/
theorem _root_.Quantifier.NumberTree.Proportional.toGQ {q : NumberTree} (h : q.Proportional) :
    Proportional (q.toGQ : GQ α) := fun _ _ _ _ ↦ h _ _ _ _

theorem proportional_most : Proportional (most : GQ α) := NumberTree.proportional_most.toGQ

theorem proportional_few : Proportional (few : GQ α) := NumberTree.proportional_few.toGQ

theorem proportional_half : Proportional (half : GQ α) := NumberTree.proportional_half.toGQ

/-! ### Counterexamples on small universes

The proportional quantifiers fail `Existential`, the condition for felicity in
there-sentences, although Barwise and Cooper's Table II labels *few* and *half* weak: their
truth depends on `|A \ B|`, not just on `|A ∩ B|`. *Few* already fails it on one individual,
*most* and *half* on two. -/

/-- *Most* fails `Existential`, by `A = ⊤` and `B = {0}` on two individuals. -/
theorem not_existential_most : ¬ Existential (most : GQ (Fin 2)) := fun h ↦ by
  have := h (fun _ ↦ True) (· = 0)
  revert this; decide

theorem not_existential_few : ¬ Existential (few : GQ (Fin 1)) := fun h ↦ by
  have := h (fun _ ↦ True) fun _ ↦ False
  revert this; decide

theorem not_existential_half : ¬ Existential (half : GQ (Fin 2)) := fun h ↦ by
  have := h (fun _ ↦ True) (· = 0)
  revert this; decide

theorem not_restrictorMonotone_most : ¬ RestrictorMonotone (most : GQ (Fin 3)) := fun h ↦ by
  have hle : (· = (0 : Fin 3)) ≤ (· ≠ 1) := fun x hx ↦ by subst hx; decide
  have : most (· = (0 : Fin 3)) (· = 0) → most (· ≠ 1) (· = (0 : Fin 3)) := h _ hle
  revert this; decide

theorem not_symm_most : ¬ Std.Symm (most : GQ (Fin 3)) := fun h ↦ by
  have := h.symm (· = 0) (fun x ↦ x = 0 ∨ x = 1)
  revert this; decide

theorem not_scopeMonotone_half : ¬ ScopeMonotone (half : GQ (Fin 3)) := fun h ↦ by
  have hle : (· = (0 : Fin 3)) ≤ fun x ↦ x = 0 ∨ x = 1 := fun _ ↦ Or.inl
  have : half (fun x : Fin 3 ↦ x = 0 ∨ x = 1) (· = 0) →
      half (fun x : Fin 3 ↦ x = 0 ∨ x = 1) fun x ↦ x = 0 ∨ x = 1 := h _ hle
  revert this; decide

theorem not_scopeAntitone_half : ¬ ScopeAntitone (half : GQ (Fin 3)) := fun h ↦ by
  have hle : (fun _ ↦ False) ≤ (· = (0 : Fin 3)) := fun _ ↦ False.elim
  have : half (fun x : Fin 3 ↦ x = 0 ∨ x = 1) (· = 0) →
      half (fun x : Fin 3 ↦ x = 0 ∨ x = 1) fun _ ↦ False := h _ hle
  revert this; decide

/-- *Half* is non-monotone in its scope, neither monotone nor antitone
([van-de-pol-etal-2023]). -/
theorem not_monotone_half :
    ¬ ScopeMonotone (half : GQ (Fin 3)) ∧ ¬ ScopeAntitone (half : GQ (Fin 3)) :=
  ⟨not_scopeMonotone_half, not_scopeAntitone_half⟩

theorem not_monotone_exactly [Fintype α] {n : ℕ} (h : n < Fintype.card α) :
    ¬ Monotone (exactly n fun _ : α ↦ True) := fun hq ↦ by
  obtain ⟨t, -, rfl⟩ := Finset.exists_subset_card_eq (s := .univ) (n := n) (by simpa using h.le)
  have := hq (a := (· ∈ t)) le_top (by simp [exactly_apply, ← Set.ncard_coe_finset])
  simp [exactly_apply, Set.ncard_univ, Nat.card_eq_fintype_card] at this
  omega

theorem not_antitone_exactly [Fintype α] {n : ℕ} (hn : n ≠ 0) (h : n ≤ Fintype.card α) :
    ¬ Antitone (exactly n fun _ : α ↦ True) := fun hq ↦ by
  obtain ⟨t, -, rfl⟩ := Finset.exists_subset_card_eq (s := .univ) (n := n) (by simpa using h)
  have := hq (a := ⊥) (b := (· ∈ t)) bot_le (by simp [exactly_apply, ← Set.ncard_coe_finset])
  simp [exactly_apply] at this
  omega

theorem both_fin2 : both (α := Fin 2) (fun _ ↦ True) fun _ ↦ True := by decide

theorem not_both_fin3 : ¬ both (α := Fin 3) (fun _ ↦ True) fun _ ↦ True := by decide

theorem most_singleton_iff (j : α) (B : α → Prop) : most (· = j) B ↔ B j := by
  by_cases h : B j
  · rw [most_apply, show {x | x = j ∧ ¬ B x} = ∅ by ext; grind,
      show {x | x = j ∧ B x} = {j} by ext; grind]
    simpa using h
  · rw [most_apply, show {x | x = j ∧ B x} = ∅ by ext; grind]
    simpa using h

/-! ### The families of the canonical denotations

Each canonical denotation given on every finite domain, the readings a lexicon entry draws
on. -/

universe u

namespace Family

/-- `Family.every` is `every` on every finite domain. -/
def every : Family.{u} := fun _ _ ↦ GQ.every
/-- `Family.some` is `GQ.some` on every finite domain. -/
def some : Family.{u} := fun _ _ ↦ GQ.some
/-- `Family.no` is `no` on every finite domain. -/
def no : Family.{u} := fun _ _ ↦ GQ.no
/-- `Family.most` is `most` on every finite domain. -/
def most : Family.{u} := fun _ _ ↦ GQ.most
/-- `Family.few` is `few` on every finite domain. -/
def few : Family.{u} := fun _ _ ↦ GQ.few
/-- `Family.half` is `half` on every finite domain. -/
def half : Family.{u} := fun _ _ ↦ GQ.half
/-- `Family.both` is `both` on every finite domain. -/
def both : Family.{u} := fun _ _ ↦ GQ.both
/-- `Family.neither` is `neither` on every finite domain. -/
def neither : Family.{u} := fun _ _ ↦ GQ.neither
/-- `Family.atLeast n` is `atLeast n` on every finite domain. -/
def atLeast (n : ℕ) : Family.{u} := fun _ _ ↦ GQ.atLeast n
/-- `Family.exactly n` is `exactly n` on every finite domain. -/
def exactly (n : ℕ) : Family.{u} := fun _ _ ↦ GQ.exactly n

theorem some_ne_every : some.{u} ≠ every.{u} := fun h ↦ by
  have := congrArg (fun d : Family.{u} ↦ d PUnit (fun _ ↦ False) fun _ ↦ False) h
  simp [some, every, GQ.some, GQ.every] at this

theorem some_ne_no : some.{u} ≠ no.{u} := fun h ↦ by
  have := congrArg (fun d : Family.{u} ↦ d PUnit (fun _ ↦ True) fun _ ↦ True) h
  simp [some, no, GQ.some, GQ.no] at this

theorem no_ne_every : no.{u} ≠ every.{u} := fun h ↦ by
  have := congrArg (fun d : Family.{u} ↦ d PUnit (fun _ ↦ True) fun _ ↦ True) h
  simp [no, every, GQ.no, GQ.every] at this

theorem most_ne_every : most.{u} ≠ every.{u} := fun h ↦ by
  have := congrArg (fun d : Family.{u} ↦ d PUnit (fun _ ↦ False) fun _ ↦ False) h
  simp [most, every, GQ.every, most_apply] at this

theorem few_ne_every : few.{u} ≠ every.{u} := fun h ↦ by
  have := congrArg (fun d : Family.{u} ↦ d PUnit (fun _ ↦ False) fun _ ↦ False) h
  simp [few, every, GQ.every, few_apply] at this

@[simp]
theorem compl_some : some.{u}ᶜ = no.{u} := by
  funext _ _; exact GQ.compl_some

@[simp]
theorem compl_no : no.{u}ᶜ = some.{u} := by
  rw [← compl_some, compl_compl]

end Family

end GQ

end Quantifier
