module

public import Linglib.Semantics.Quantification.Defs
public import Linglib.Core.Data.Fintype.EquivFin
public import Linglib.Core.Data.Set.Card
public import Linglib.Core.Logic.Function.DependsOn
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Ring
public import Mathlib.Basic.Finite.Sum

/-!
# The tree of numbers

This file defines quantifiers on van Benthem's tree of numbers. A conservative quantifier that is
invariant under permutations of the universe holds of finite sets `A` and `B` according to the
two numbers `a = |A \ B|` and `b = |A ∩ B|` alone, so it is a set of points `(a, b)`. The points
with `a + b = n` form the `n`-th row of the tree, the ways of splitting an `n`-element `A`.

On this representation inner negation, which negates the scope, swaps the two coordinates, and
outer negation is the complement. The four corners of the square of opposition are *all*,
*some*, *no* and *not all*, and the two negations carry each corner to its neighbours.

Van Benthem's postulates of variety, continuity, absence of deadlock and uniformity are each
invariant under both negations. That symmetry carries the verification of the postulates, and the
proof that the corners are the only quantifiers satisfying them, from *all* to the other three.

The trees are exactly the determiner denotations given on every finite universe that are
conservative and constant, [as Boolean algebras](##Quantifier.NumberTree.familyOrderIso), so each
theorem about trees is one about such denotations; van Benthem's theorem that no nonempty
quantifier is asymmetric [is the first](##Quantifier.Det.Family.not_apply_of_asymm). On a single
universe that theorem fails.

## Main definitions

* `Quantifier.NumberTree`: a quantifier as a relation between `|A \ B|` and `|A ∩ B|`.
* `Quantifier.NumberTree.innerNeg`: inner negation, the swap of the two coordinates.
* `Quantifier.NumberTree.all`, `Quantifier.NumberTree.some`, `Quantifier.NumberTree.no`,
  `Quantifier.NumberTree.notAll`: the corners of the square of opposition.
* `Quantifier.NumberTree.cardinal`: the quantifiers that depend on `|A ∩ B|` alone.
* `Quantifier.NumberTree.row`: the points of a row at which a quantifier holds.
* `Quantifier.NumberTree.ScopeMonotone`, `Quantifier.NumberTree.ScopeAntitone`: monotonicity in
  the scope, a step along a row of the tree.
* `Quantifier.NumberTree.Asymmetric`, `Quantifier.NumberTree.StronglyConnected`,
  `Quantifier.NumberTree.Euclidean`: relational conditions on a quantifier, read off the tree.
* `Quantifier.NumberTree.Variety`, `Quantifier.NumberTree.Cont`, `Quantifier.NumberTree.Plus`,
  `Quantifier.NumberTree.Uniform`: the postulates VAR, CONT, PLUS and UNIF.
* `Quantifier.NumberTree.ofSizes`: the tree of a relation between `|A ∩ B|` and `|A|`.
* `Quantifier.NumberTree.ofDet`, `Quantifier.NumberTree.toDet`: the tree of a determiner
  denotation on a finite universe, and the determiner denotation of a tree, counting with
  `Set.ncard`.
* `Quantifier.NumberTree.ofFamily`, `Quantifier.NumberTree.toFamily`: the same on every finite
  universe at once.
* `Quantifier.NumberTree.ConstantOnRow`, `Quantifier.NumberTree.ConstantBelow`: a quantifier that
  does not depend on its scope for a restrictor of a given size, or on either argument on a
  universe of a given size.

## Main results

* `Quantifier.NumberTree.Asymmetric.eq_bot`, `Quantifier.NumberTree.StronglyConnected.eq_top`,
  `Quantifier.NumberTree.Euclidean.eq_top`: the only asymmetric quantifier is the empty one, the
  only strongly connected one is the universal one, and a nonempty Euclidean quantifier is
  universal.
* `Quantifier.NumberTree.variety_cont_plus_uniform_iff`: the quantifiers satisfying the four
  postulates are exactly the four corners of the square of opposition.
* `Quantifier.NumberTree.ofDet_iff`: a conservative, permutation-invariant determiner denotation
  holds of `A` and `B` exactly when its tree holds of `|A \ B|` and `|A ∩ B|`.
* `Quantifier.NumberTree.familyOrderIso`: the conservative constant global determiner
  denotations are the trees, as Boolean algebras.
* `Quantifier.Det.Family.not_apply_of_asymm`: such a denotation that is asymmetric on every
  universe is empty.
* `Quantifier.NumberTree.conservative_toDet`, `Quantifier.NumberTree.quantityInvariant_toDet`: the
  quantifier of a tree is conservative and permutation invariant.
* `Quantifier.NumberTree.ScopeMonotone.toDet`, `Quantifier.NumberTree.ScopeAntitone.toDet`: the
  quantifier of a scope-monotone tree is scope monotone, and likewise antitone.
* `Quantifier.NumberTree.dependsOn_toDet_compl_singleton_iff`: the quantifier of a tree depends on
  whether an individual is in its scope iff the individual is in its restrictor and the tree is not
  constant on the restrictor's row.
* `Quantifier.NumberTree.card_powerset_points`: there are `2 ^ ((n + 1) * (n + 2) / 2)` sets of
  points in rows `0` to `n`.

## Implementation notes

`Variety` asks only that the quantifier hold somewhere and fail somewhere. Van Benthem's VAR is
stronger in both of its versions, so results assuming `Variety` apply under VAR. The paper asks
for a presence and an absence among the points `(0, 0)`, `(1, 0)` and `(0, 1)`, and the book's
chapter on quantifiers, which restates the tree and the postulates, asks for both in every row
below the top.

Continuity, absence of deadlock and uniformity each treat presence and absence of the quantifier
alike. Each is stated as a condition on presence (`RowConvex`, `NoDeadlock`, `Homogeneous`) that
is imposed on the quantifier and on its complement.

## TODO

* Prove that on a universe of `n` individuals `ofDet` is a bijection from the conservative,
  quantity-invariant quantifiers onto the sets of points in rows `0` to `n`, which with
  `card_powerset_points` gives van Benthem's count, the one `KeenanStavi1986.card_logical`
  proves in the coordinates `(|A|, |A ∩ B|)`.

## References

* [peters-westerstahl-2006]
* [van-benthem-1984]
* [van-benthem-1986]
-/

@[expose] public section

namespace Quantifier

/-- A quantifier on the tree of numbers is a relation between `a = |A \ B|` and `b = |A ∩ B|`. -/
abbrev NumberTree := ℕ → ℕ → Prop

namespace NumberTree

variable {q : NumberTree} {a b : ℕ}

theorem compl_apply : qᶜ a b ↔ ¬ q a b := Iff.rfl

/-! ### Negations and the square of opposition -/

/-- Inner negation negates the scope, which swaps `A \ B` with `A ∩ B`. -/
def innerNeg (q : NumberTree) : NumberTree := fun a b ↦ q b a

@[simp] theorem innerNeg_apply : q.innerNeg a b ↔ q b a := Iff.rfl

@[simp] theorem innerNeg_innerNeg (q : NumberTree) : q.innerNeg.innerNeg = q := rfl

theorem innerNeg_compl (q : NumberTree) : qᶜ.innerNeg = q.innerNegᶜ := rfl

instance [DecidableRel q] : DecidableRel q.innerNeg := fun a b ↦ inferInstanceAs (Decidable (q b a))

instance [DecidableRel q] : DecidableRel qᶜ := fun a b ↦ inferInstanceAs (Decidable ¬ q a b)

/-- The quantifier *all* holds when nothing in `A` lies outside `B`. -/
protected def all : NumberTree := fun a _ ↦ a = 0

/-- The quantifier *some* holds when something in `A` lies in `B`. -/
protected def some : NumberTree := fun _ b ↦ b ≠ 0

/-- The quantifier *no* holds when nothing in `A` lies in `B`. -/
protected def no : NumberTree := fun _ b ↦ b = 0

/-- The quantifier *not all* holds when something in `A` lies outside `B`. -/
protected def notAll : NumberTree := fun a _ ↦ a ≠ 0

instance : DecidableRel NumberTree.all := fun a _ ↦ inferInstanceAs (Decidable (a = 0))
instance : DecidableRel NumberTree.some := fun _ b ↦ inferInstanceAs (Decidable (b ≠ 0))
instance : DecidableRel NumberTree.no := fun _ b ↦ inferInstanceAs (Decidable (b = 0))
instance : DecidableRel NumberTree.notAll := fun a _ ↦ inferInstanceAs (Decidable (a ≠ 0))

theorem innerNeg_all : NumberTree.all.innerNeg = NumberTree.no := rfl

theorem innerNeg_some : NumberTree.some.innerNeg = NumberTree.notAll := rfl

theorem compl_all : NumberTree.allᶜ = NumberTree.notAll := rfl

theorem compl_no : NumberTree.noᶜ = NumberTree.some := rfl

/-- A cardinal quantifier holds according to `|A ∩ B|` alone, as the numerals do. -/
def cardinal (s : Set ℕ) : NumberTree := fun _ b ↦ b ∈ s

@[simp] theorem cardinal_apply {s : Set ℕ} : cardinal s a b ↔ b ∈ s := Iff.rfl

instance {s : Set ℕ} [DecidablePred (· ∈ s)] : DecidableRel (cardinal s) :=
  fun _ b ↦ inferInstanceAs (Decidable (b ∈ s))

theorem cardinal_singleton_zero : cardinal {0} = NumberTree.no := rfl

/-- The tree of a relation `c` between `|A ∩ B|` and `|A|` holds at `(a, b)` when `c` relates `b`
to `a + b`, the form in which proportions of the restrictor are stated. -/
def ofSizes (c : ℕ → ℕ → Prop) : NumberTree := fun a b ↦ c b (a + b)

@[simp] theorem ofSizes_apply {c : ℕ → ℕ → Prop} : ofSizes c a b ↔ c b (a + b) := Iff.rfl

instance {c : ℕ → ℕ → Prop} [DecidableRel c] : DecidableRel (ofSizes c) :=
  fun a b ↦ inferInstanceAs (Decidable (c b (a + b)))

/-! ### Rows

Row `n` of the tree lists the ways of splitting `n` members of `A` between `B` and its complement.
A point of the row is given by the number of members inside `B`. -/

/-- The points of row `n` at which a quantifier holds, each given by `|A ∩ B|`. -/
def row (q : NumberTree) [DecidableRel q] (n : ℕ) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun b ↦ q (n - b) b

@[simp] theorem mem_row [DecidableRel q] {n : ℕ} {b : Fin (n + 1)} :
    b ∈ q.row n ↔ q (n - b) b := by
  simp [row]

/-! ### Scope monotonicity

Enlarging the scope `B` by an element of `A` moves one individual from `A \ B` to `A ∩ B`, a step
to the right along a row of the tree. -/

/-- A quantifier is scope monotone when a step right along a row preserves truth. -/
def ScopeMonotone (q : NumberTree) : Prop := ∀ a b, q (a + 1) b → q a (b + 1)

/-- A quantifier is scope antitone when a step left along a row preserves truth. -/
def ScopeAntitone (q : NumberTree) : Prop := ∀ a b, q a (b + 1) → q (a + 1) b

theorem ScopeMonotone.compl (h : q.ScopeMonotone) : qᶜ.ScopeAntitone :=
  fun a b h₁ h₂ ↦ h₁ (h a b h₂)

theorem ScopeAntitone.compl (h : q.ScopeAntitone) : qᶜ.ScopeMonotone :=
  fun a b h₁ h₂ ↦ h₁ (h a b h₂)

theorem ScopeMonotone.innerNeg (h : q.ScopeMonotone) : q.innerNeg.ScopeAntitone :=
  fun a b ↦ h b a

theorem ScopeAntitone.innerNeg (h : q.ScopeAntitone) : q.innerNeg.ScopeMonotone :=
  fun a b ↦ h b a

theorem ScopeMonotone.shift (h : q.ScopeMonotone) (k : ℕ) {a b : ℕ} (hq : q (a + k) b) :
    q a (b + k) := by
  induction k generalizing b with
  | zero => exact hq
  | succ k ih =>
    have := ih (h _ _ (by rwa [← Nat.add_assoc] at hq))
    rwa [Nat.add_assoc, Nat.add_comm 1 k] at this

theorem scopeMonotone_ofSizes {c : ℕ → ℕ → Prop} (hc : ∀ p, Monotone (c · p)) :
    (ofSizes c).ScopeMonotone := fun a b h ↦ by
  rw [ofSizes_apply, show a + (b + 1) = a + 1 + b by omega]
  exact hc _ b.le_succ h

theorem scopeAntitone_ofSizes {c : ℕ → ℕ → Prop} (hc : ∀ p, Antitone (c · p)) :
    (ofSizes c).ScopeAntitone := fun a b h ↦ by
  rw [ofSizes_apply, show a + 1 + b = a + (b + 1) by omega]
  exact hc _ b.le_succ h

theorem scopeMonotone_all : NumberTree.all.ScopeMonotone :=
  fun _ _ h ↦ absurd h (Nat.succ_ne_zero _)

theorem scopeAntitone_no : NumberTree.no.ScopeAntitone := scopeMonotone_all.innerNeg

theorem scopeMonotone_some : NumberTree.some.ScopeMonotone := scopeAntitone_no.compl

theorem scopeAntitone_notAll : NumberTree.notAll.ScopeAntitone := scopeMonotone_all.compl

/-! ### Relational conditions

A condition on the relation `Q A B` between sets becomes a condition on the tree once the sets
are replaced by the sizes of the cells of their Venn diagram. -/

/-- A quantifier is asymmetric when `Q A B` excludes `Q B A`. The two share `|A ∩ B|`, and
`|A \ B|` and `|B \ A|` are arbitrary. -/
def Asymmetric (q : NumberTree) : Prop := ∀ a b c, q a c → ¬ q b c

/-- A quantifier is strongly connected when `Q A B` or `Q B A` holds of any two sets. -/
def StronglyConnected (q : NumberTree) : Prop := ∀ a b c, q a c ∨ q b c

/-- A quantifier is irreflexive when `Q A A` never holds. -/
def Irreflexive (q : NumberTree) : Prop := ∀ n, ¬ q 0 n

/-- A quantifier is Euclidean when `Q X Y` and `Q X Z` give `Q Y Z`. Among the cells of the Venn
diagram of `X`, `Y` and `Z`, `p` counts `X ∩ Y ∩ Z`, `x` the rest of `X ∩ Y`, `y` the rest of
`X ∩ Z`, `s` the rest of `X`, `t` the rest of `Y ∩ Z`, and `u` the rest of `Y`. -/
def Euclidean (q : NumberTree) : Prop :=
  ∀ p x y s t u, q (y + s) (p + x) → q (x + s) (p + y) → q (x + u) (p + t)

/-- The only asymmetric quantifier is the empty one. -/
theorem Asymmetric.eq_bot (h : q.Asymmetric) : q = ⊥ :=
  funext₂ fun a c ↦ eq_false fun hq ↦ h a a c hq hq

/-- The only strongly connected quantifier is the universal one. -/
theorem StronglyConnected.eq_top (h : q.StronglyConnected) : q = ⊤ :=
  funext₂ fun a c ↦ eq_true ((h a a c).elim id id)

/-- An irreflexive quantifier for which `Q A B` and `Q B A` give `Q A A`, as transitivity
requires, is asymmetric. So there is no strict partial order among the nonempty quantifiers. -/
theorem Irreflexive.asymmetric (hI : q.Irreflexive)
    (hT : ∀ a b c, q a c → q b c → q 0 (a + c)) : q.Asymmetric :=
  fun a b c h₁ h₂ ↦ hI _ (hT a b c h₁ h₂)

/-- A nonempty Euclidean quantifier is universal. -/
theorem Euclidean.eq_top (h : q.Euclidean) (hq : ∃ a b, q a b) : q = ⊤ := by
  obtain ⟨d, c, hdc⟩ := hq
  have h₁ : ∀ t u, q u (c + t) := fun t u ↦ by
    simpa using h c 0 0 d t u (by simpa using hdc) (by simpa using hdc)
  have h₂ : ∀ t u, q (c + u) t := fun t u ↦ by
    have hl : q (2 * c) c := by simpa using h₁ 0 (2 * c)
    have hr : q c (2 * c) := by simpa [two_mul] using h₁ c c
    simpa using h 0 c (2 * c) 0 t u (by simpa using hl) (by simpa using hr)
  refine funext₂ fun a b ↦ eq_true ?_
  simpa using h 0 0 c 0 b a (by simpa using h₂ 0 0) (by simpa using h₁ 0 0)

/-! ### The postulates -/

/-- A quantifier has variety when it holds somewhere and fails somewhere. -/
def Variety (q : NumberTree) : Prop := (∃ a b, q a b) ∧ ∃ a b, ¬ q a b

/-- A quantifier is row-convex when it meets each row of the tree in an uninterrupted stretch. -/
def RowConvex (q : NumberTree) : Prop :=
  ∀ ⦃a₁ b₁ a b a₂ b₂ : ℕ⦄, a₁ + b₁ = a + b → a₂ + b₂ = a + b → a₁ ≤ a → a ≤ a₂ →
    q a₁ b₁ → q a₂ b₂ → q a b

/-- The postulate CONT asks that both the presence and the absence of the quantifier be
uninterrupted along each row. -/
def Cont (q : NumberTree) : Prop := q.RowConvex ∧ qᶜ.RowConvex

/-- A quantifier has no deadlock when adding an individual to `A` can always keep it true. -/
def NoDeadlock (q : NumberTree) : Prop := ∀ ⦃a b : ℕ⦄, q a b → q (a + 1) b ∨ q a (b + 1)

/-- The postulate PLUS asks that neither the truth nor the falsity of the quantifier reach a
deadlock. -/
def Plus (q : NumberTree) : Prop := q.NoDeadlock ∧ qᶜ.NoDeadlock

/-- A quantifier is homogeneous when adding an individual to `A` has the same two outcomes
wherever the quantifier holds. -/
def Homogeneous (q : NumberTree) : Prop :=
  ∀ ⦃a₁ b₁ a₂ b₂ : ℕ⦄, q a₁ b₁ → q a₂ b₂ →
    (q (a₁ + 1) b₁ ↔ q (a₂ + 1) b₂) ∧ (q a₁ (b₁ + 1) ↔ q a₂ (b₂ + 1))

/-- The postulate UNIF asks that adding an individual have the same outcomes wherever the
quantifier holds, and the same outcomes wherever it fails. -/
def Uniform (q : NumberTree) : Prop := q.Homogeneous ∧ qᶜ.Homogeneous

theorem Variety.compl (h : q.Variety) : qᶜ.Variety :=
  ⟨h.2, h.1.imp fun _ ↦ Exists.imp fun _ ↦ not_not_intro⟩

theorem Cont.compl (h : q.Cont) : qᶜ.Cont := ⟨h.2, by rw [compl_compl]; exact h.1⟩

theorem Plus.compl (h : q.Plus) : qᶜ.Plus := ⟨h.2, by rw [compl_compl]; exact h.1⟩

theorem Uniform.compl (h : q.Uniform) : qᶜ.Uniform := ⟨h.2, by rw [compl_compl]; exact h.1⟩

theorem Variety.innerNeg (h : q.Variety) : q.innerNeg.Variety :=
  ⟨let ⟨a, b, hq⟩ := h.1; ⟨b, a, hq⟩, let ⟨a, b, hq⟩ := h.2; ⟨b, a, hq⟩⟩

theorem RowConvex.innerNeg (h : q.RowConvex) : q.innerNeg.RowConvex :=
  fun _ _ _ _ _ _ h₁ h₂ _ _ p₁ p₂ ↦ h (by omega) (by omega) (by omega) (by omega) p₂ p₁

theorem NoDeadlock.innerNeg (h : q.NoDeadlock) : q.innerNeg.NoDeadlock :=
  fun _ _ hq ↦ (h hq).symm

theorem Homogeneous.innerNeg (h : q.Homogeneous) : q.innerNeg.Homogeneous :=
  fun _ _ _ _ h₁ h₂ ↦ (h h₁ h₂).symm

theorem Cont.innerNeg (h : q.Cont) : q.innerNeg.Cont := ⟨h.1.innerNeg, h.2.innerNeg⟩

theorem Plus.innerNeg (h : q.Plus) : q.innerNeg.Plus := ⟨h.1.innerNeg, h.2.innerNeg⟩

theorem Uniform.innerNeg (h : q.Uniform) : q.innerNeg.Uniform := ⟨h.1.innerNeg, h.2.innerNeg⟩

/-! ### The square of opposition

The four corners are the only quantifiers with variety that satisfy CONT, PLUS and UNIF. -/

theorem variety_all : NumberTree.all.Variety := ⟨⟨0, 0, rfl⟩, 1, 0, one_ne_zero⟩

theorem cont_all : NumberTree.all.Cont := by
  refine ⟨fun _ _ _ _ _ _ _ _ _ _ h₁ h₂ ↦ ?_, fun _ _ _ _ _ _ _ _ _ _ h₁ _ ↦ ?_⟩ <;>
    simp only [NumberTree.all, compl_apply] at * <;> omega

theorem plus_all : NumberTree.all.Plus :=
  ⟨fun _ _ h ↦ .inr h, fun _ _ _ ↦ .inl (Nat.succ_ne_zero _)⟩

theorem uniform_all : NumberTree.all.Uniform := by
  refine ⟨fun _ _ _ _ h₁ h₂ ↦ ?_, fun _ _ _ _ h₁ h₂ ↦ ?_⟩ <;>
    simp only [NumberTree.all, compl_apply] at * <;> omega

/-- A quantifier that holds at `(0, 0)` and whose row `1` reads absence, presence is *all*. -/
private theorem eq_all (hC : q.RowConvex) (hU : q.Uniform) (h00 : q 0 0) (h10 : ¬ q 1 0)
    (h01 : q 0 1) : q = NumberTree.all := by
  have hT : ∀ {a b}, q a b → ¬ q (a + 1) b ∧ q a (b + 1) := fun h ↦
    let ⟨hl, hr⟩ := hU.1 h h00; ⟨fun h' ↦ h10 (hl.mp h'), hr.mpr h01⟩
  have hcol : ∀ b, q 0 b := fun b ↦ by
    induction b with
    | zero => exact h00
    | succ b ih => exact (hT ih).2
  have h20 : ¬ q 2 0 := fun h ↦
    (hT (hcol 1)).1 (hC (a₁ := 0) (b₁ := 2) (a := 1) (b := 1) (b₂ := 0) rfl rfl zero_le_one
      one_le_two (hcol 2) h)
  have hF : ∀ {a b}, ¬ q a b → ¬ q (a + 1) b ∧ ¬ q a (b + 1) := fun h ↦
    let ⟨hl, hr⟩ := hU.2 h h10; ⟨hl.mpr h20, hr.mpr (hT (hcol 1)).1⟩
  have hrow : ∀ a b, ¬ q (a + 1) b := fun a ↦ by
    induction a with
    | zero => exact fun b ↦ (hT (hcol b)).1
    | succ a ih => exact fun b ↦ (hF (ih b)).1
  funext a b
  cases a with
  | zero => exact propext ⟨fun _ ↦ rfl, fun _ ↦ hcol b⟩
  | succ a => exact propext ⟨fun h ↦ (hrow a b h).elim, fun h ↦ (Nat.succ_ne_zero a h).elim⟩

/-- A quantifier satisfying the postulates that holds at `(0, 0)` is *all* or *no*. -/
private theorem eq_all_or_eq_no (hV : q.Variety) (hC : q.Cont) (hP : q.Plus) (hU : q.Uniform)
    (h00 : q 0 0) : q = NumberTree.all ∨ q = NumberTree.no := by
  by_cases h10 : q 1 0 <;> by_cases h01 : q 0 1
  · have hT : ∀ {a b}, q a b → q (a + 1) b ∧ q a (b + 1) := fun h ↦
      let ⟨hl, hr⟩ := hU.1 h h00; ⟨hl.mpr h10, hr.mpr h01⟩
    have hcol : ∀ b, q 0 b := fun b ↦ by
      induction b with
      | zero => exact h00
      | succ b ih => exact (hT ih).2
    have hall : ∀ a b, q a b := fun a ↦ by
      induction a with
      | zero => exact hcol
      | succ a ih => exact fun b ↦ (hT (ih b)).1
    obtain ⟨a, b, hq⟩ := hV.2
    exact (hq (hall a b)).elim
  · right
    have := eq_all (q := q.innerNeg) hC.1.innerNeg hU.innerNeg h00 h01 h10
    rw [← innerNeg_innerNeg q, this, innerNeg_all]
  · exact .inl (eq_all hC.1 hU h00 h10 h01)
  · exact ((hP.1 h00).elim h10 h01).elim

/-- The quantifiers with variety that satisfy CONT, PLUS and UNIF are exactly *all*, *some*,
*no* and *not all*. -/
theorem variety_cont_plus_uniform_iff :
    q.Variety ∧ q.Cont ∧ q.Plus ∧ q.Uniform ↔
      q = NumberTree.all ∨ q = NumberTree.some ∨ q = NumberTree.no ∨ q = NumberTree.notAll := by
  constructor
  · rintro ⟨hV, hC, hP, hU⟩
    by_cases h00 : q 0 0
    · exact (eq_all_or_eq_no hV hC hP hU h00).imp_right fun h ↦ .inr (.inl h)
    · rcases eq_all_or_eq_no hV.compl hC.compl hP.compl hU.compl h00 with h | h
      · exact .inr (.inr (.inr (by rw [← compl_compl q, h, compl_all])))
      · exact .inr (.inl (by rw [← compl_compl q, h, compl_no]))
  · have hno : NumberTree.no.Variety ∧ NumberTree.no.Cont ∧ NumberTree.no.Plus ∧
        NumberTree.no.Uniform :=
      ⟨variety_all.innerNeg, cont_all.innerNeg, plus_all.innerNeg, uniform_all.innerNeg⟩
    rintro (rfl | rfl | rfl | rfl)
    · exact ⟨variety_all, cont_all, plus_all, uniform_all⟩
    · exact ⟨hno.1.compl, hno.2.1.compl, hno.2.2.1.compl, hno.2.2.2.compl⟩
    · exact hno
    · exact ⟨variety_all.compl, cont_all.compl, plus_all.compl, uniform_all.compl⟩

/-- *At least two* is not uniform, since it is false at `(0, 0)` and true at `(0, 1)`. -/
theorem not_uniform_two_le : ¬ Uniform fun _ b ↦ 2 ≤ b := fun h ↦ by
  have := (h.2 (a₁ := 0) (b₁ := 0) (a₂ := 0) (b₂ := 1) (by simp [compl_apply])
    (by simp [compl_apply])).2
  simp [compl_apply] at this

/-! ### Additivity -/

/-- A quantifier is additive when its points are closed under coordinatewise addition. -/
def Additive (q : NumberTree) : Prop :=
  ∀ ⦃a b a' b' : ℕ⦄, q a b → q a' b' → q (a + a') (b + b')

theorem Additive.innerNeg (h : q.Additive) : q.innerNeg.Additive := fun _ _ _ _ h₁ h₂ ↦ h h₁ h₂

theorem additive_all : NumberTree.all.Additive := fun _ _ _ _ h₁ h₂ ↦ by
  simp only [NumberTree.all] at *; omega

theorem additive_notAll : NumberTree.notAll.Additive := fun _ _ _ _ h₁ _ ↦ by
  simp only [NumberTree.notAll] at *; omega

theorem additive_no : NumberTree.no.Additive := additive_all.innerNeg

theorem additive_some : NumberTree.some.Additive := additive_notAll.innerNeg

/-! ### The tree of a determiner denotation

A determiner denotation counts its arguments with `Set.ncard`, which asks for no decidability;
the counts are meaningful when the sets are finite. -/

section OfDet

open Det

variable {α : Type*} {d : Det α} {A B A' B' : Set α}

/-- A determiner denotation has quantity when `d A B` depends only on the sizes of the four cells
of the Venn diagram, `A ∩ B`, `A \ B`, `B \ A` and `(A ∪ B)ᶜ`. -/
def _root_.Quantifier.Det.Quantity (d : Det α) : Prop :=
  ∀ A B A' B' : Set α, (A ∩ B).ncard = (A' ∩ B').ncard → (A \ B).ncard = (A' \ B').ncard →
    (B \ A).ncard = (B' \ A').ncard → (A ∪ B)ᶜ.ncard = (A' ∪ B')ᶜ.ncard → (d A B ↔ d A' B')

open Classical in
private theorem nat_card_fiber (A B : Set α) (p q : Bool) :
    Nat.card {x // (decide (x ∈ A), decide (x ∈ B)) = (p, q)} =
      ((bif p then A else Aᶜ) ∩ (bif q then B else Bᶜ)).ncard := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ by cases p <;> cases q <;> simp)

theorem _root_.Quantifier.Det.QuantityInvariant.quantity [Finite α] (h : d.QuantityInvariant) :
    d.Quantity := by
  classical
  intro A B A' B' hTT hTF hFT hFF
  have hFT' : (Aᶜ ∩ B).ncard = (A'ᶜ ∩ B').ncard := by
    rwa [Set.inter_comm, Set.inter_comm A'ᶜ]
  rw [Set.compl_union, Set.compl_union] at hFF
  obtain ⟨e, he⟩ := Equiv.exists_comp_eq_of_card_fiber_eq
    (f := fun x ↦ (decide (x ∈ A'), decide (x ∈ B')))
    (g := fun x ↦ (decide (x ∈ A), decide (x ∈ B)))
    fun ⟨p, q⟩ ↦ by
      rw [nat_card_fiber, nat_card_fiber]
      cases p <;> cases q
      exacts [hFF, hFT', hTF, hTT]
  have hA : e ⁻¹' A' = A := Set.ext fun x ↦ decide_eq_decide.1 (congrArg Prod.fst (congrFun he x))
  have hB : e ⁻¹' B' = B := Set.ext fun x ↦ decide_eq_decide.1 (congrArg Prod.snd (congrFun he x))
  rw [← h e A' B', hA, hB]

private theorem ncard_preimage_perm (σ : Equiv.Perm α) (s : Set α) : (σ ⁻¹' s).ncard = s.ncard :=
  Set.ncard_preimage_of_injective_subset_range σ.injective (by simp)

theorem _root_.Quantifier.Det.Quantity.quantityInvariant (h : d.Quantity) :
    d.QuantityInvariant :=
  fun σ A B ↦ h _ _ A B (ncard_preimage_perm σ (A ∩ B)) (ncard_preimage_perm σ (A \ B))
    (ncard_preimage_perm σ (B \ A)) (ncard_preimage_perm σ (A ∪ B)ᶜ)

/-- A conservative, permutation-invariant determiner denotation on a finite universe depends only
on `|A \ B|` and `|A ∩ B|`. -/
theorem _root_.Quantifier.Det.iff_of_ncard_eq [Finite α] (hC : d.Conservative)
    (hQ : d.QuantityInvariant) (hd : (A \ B).ncard = (A' \ B').ncard)
    (hi : (A ∩ B).ncard = (A' ∩ B').ncard) : d A B ↔ d A' B' := by
  have hA := Set.ncard_inter_add_ncard_sdiff_eq_ncard A B
  have hA' := Set.ncard_inter_add_ncard_sdiff_eq_ncard A' B'
  have hc := Set.ncard_add_ncard_compl A
  have hc' := Set.ncard_add_ncard_compl A'
  rw [hC A B, hC A' B']
  refine hQ.quantity _ _ _ _ ?_ ?_ ?_ ?_
  · rwa [Set.inter_eq_right.2 Set.inter_subset_left, Set.inter_eq_right.2 Set.inter_subset_left]
  · rwa [Set.sdiff_self_inter, Set.sdiff_self_inter]
  · rw [Set.sdiff_eq_empty.2 Set.inter_subset_left, Set.sdiff_eq_empty.2 Set.inter_subset_left]
  · rw [Set.union_eq_left.2 Set.inter_subset_left, Set.union_eq_left.2 Set.inter_subset_left]
    omega

/-- A conservative permutation-invariant determiner denotation that is asymmetric fails of `A`
and `B` when `A \ B` and `B \ A` have the same size, since swapping them carries `(A, B)` to
`(B, A)`. -/
theorem _root_.Quantifier.Det.not_apply_of_asymm [Finite α] (hC : d.Conservative)
    (hQ : d.QuantityInvariant) [Std.Asymm d] (h : (A \ B).ncard = (B \ A).ncard) : ¬ d A B :=
  fun hd ↦ Std.Asymm.asymm A B hd ((Det.iff_of_ncard_eq hC hQ h (by rw [Set.inter_comm])).1 hd)

/-- The tree of a determiner denotation holds of `(a, b)` when the denotation holds of some `A`
and `B` with `|A \ B| = a` and `|A ∩ B| = b`. -/
def ofDet (d : Det α) : NumberTree := fun a b ↦
  ∃ A B : Set α, (A \ B).ncard = a ∧ (A ∩ B).ncard = b ∧ d A B

/-- A conservative, permutation-invariant determiner denotation on a finite universe holds of `A`
and `B` exactly when its tree holds of `|A \ B|` and `|A ∩ B|`. -/
theorem ofDet_iff [Finite α] (hC : d.Conservative) (hQ : d.QuantityInvariant) (A B : Set α) :
    ofDet d (A \ B).ncard (A ∩ B).ncard ↔ d A B :=
  ⟨fun ⟨_, _, hd, hi, h⟩ ↦ (Det.iff_of_ncard_eq hC hQ hd hi).mp h, fun h ↦ ⟨A, B, rfl, rfl, h⟩⟩

/-- The determiner denotation of a tree holds of `A` and `B` when the tree holds of `|A \ B|` and
`|A ∩ B|`. -/
def toDet (q : NumberTree) : Det α := fun A B ↦ q (A \ B).ncard (A ∩ B).ncard

theorem toDet_apply (q : NumberTree) (A B : Set α) :
    q.toDet A B ↔ q (A \ B).ncard (A ∩ B).ncard := Iff.rfl

@[simp] theorem toDet_inf (q r : NumberTree) : (q ⊓ r).toDet = (q.toDet ⊓ r.toDet : Det α) := rfl

@[simp] theorem toDet_compl (q : NumberTree) : qᶜ.toDet = (q.toDetᶜ : Det α) := rfl

@[simp] theorem toDet_innerNeg (q : NumberTree) :
    q.innerNeg.toDet = (q.toDet : Det α).innerNeg := by
  funext A B; simp only [toDet, innerNeg_apply, Det.innerNeg, Set.sdiff_compl]; rfl

/-- On a finite universe the determiner denotation of a decidable tree is decidable at decidable
arguments. -/
instance toDet.decidable [Fintype α] (q : NumberTree) [DecidableRel q] (A B : Set α)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] : Decidable (q.toDet A B) :=
  decidable_of_iff (q (A \ B).toFinset.card (A ∩ B).toFinset.card) <| by
    rw [toDet_apply, Set.ncard_eq_toFinset_card' (A \ B), Set.ncard_eq_toFinset_card' (A ∩ B)]

/-- The determiner denotation of a tree is conservative, since `A \ B` and `A ∩ B` see only
`A ∩ B`. -/
theorem conservative_toDet (q : NumberTree) : (q.toDet : Det α).Conservative := fun A B ↦ by
  rw [toDet_apply, toDet_apply, Set.sdiff_self_inter, Set.inter_eq_right.2 Set.inter_subset_left]

theorem quantity_toDet (q : NumberTree) : (q.toDet : Det α).Quantity :=
  fun _ _ _ _ hi hd _ _ ↦ by rw [toDet_apply, toDet_apply, hi, hd]

/-- The determiner denotation of a tree is permutation invariant. -/
theorem quantityInvariant_toDet (q : NumberTree) : (q.toDet : Det α).QuantityInvariant :=
  (quantity_toDet q).quantityInvariant

/-- The determiner denotation of a tree is unchanged by pulling back along an injection whose
range contains the restrictor. -/
theorem toDet_preimage {β : Type*} {f : α → β} (hf : f.Injective) {A : Set β} (B : Set β)
    (hA : A ⊆ Set.range f) (q : NumberTree) : q.toDet (f ⁻¹' A) (f ⁻¹' B) ↔ q.toDet A B := by
  rw [toDet_apply, toDet_apply, ← Set.preimage_sdiff, ← Set.preimage_inter,
    Set.ncard_preimage_of_injective_subset_range hf (Set.sdiff_subset.trans hA),
    Set.ncard_preimage_of_injective_subset_range hf (Set.inter_subset_left.trans hA)]

/-- The determiner denotation of a scope-monotone tree is scope monotone, since enlarging `B`
within `A` moves `|(A \ B) ∩ B'|` individuals from `A \ B` to `A ∩ B`. -/
theorem ScopeMonotone.toDet [Finite α] {q : NumberTree} (h : q.ScopeMonotone) :
    (q.toDet : Det α).ScopeMonotone := by
  intro A B B' hB hq
  rw [toDet_apply] at hq ⊢
  have h₁ := Set.ncard_inter_add_ncard_sdiff_eq_ncard (A \ B) B'
  have h₂ := Set.ncard_inter_add_ncard_sdiff_eq_ncard (A ∩ B') B
  have e₁ : A ∩ B' ∩ B = A ∩ B := by ext x; have := @hB x; grind
  have e₂ : (A \ B) \ B' = A \ B' := by ext x; have := @hB x; grind
  have e₃ : (A ∩ B') \ B = (A \ B) ∩ B' := by ext; grind
  rw [e₂] at h₁
  rw [e₁, e₃] at h₂
  rw [← h₂]
  rw [← h₁, Nat.add_comm] at hq
  exact h.shift _ hq

/-- The determiner denotation of a scope-antitone tree is scope antitone. -/
theorem ScopeAntitone.toDet [Finite α] {q : NumberTree} (h : q.ScopeAntitone) :
    (q.toDet : Det α).ScopeAntitone :=
  fun A _ _ hB hq ↦ Classical.byContradiction fun hn ↦ h.compl.toDet A hB hn hq

end OfDet

/-! ### The tree of a global determiner denotation

A global determiner denotation that is conservative and constant, extensional and closed under
isomorphism, holds of `A` and `B` according to `|A \ B|` and `|A ∩ B|` alone, on every universe
at once, which is Peters and Westerståhl's representation of such quantifiers by binary relations between
numbers. Such denotations are exactly the trees, so every theorem about trees is a theorem
about them. -/

section Family

universe u

open Det

variable {Q : Det.Family.{u}}

/-- Constancy is extension together with isomorphism closure. -/
theorem _root_.Quantifier.Det.Family.constant_iff : Q.Constant ↔ Q.Ext ∧ Q.Isom := by
  refine ⟨fun h ↦ ⟨fun β _ M A B hA hB ↦ ?_, fun α β _ _ e A B ↦ ?_⟩, fun ⟨hE, hI⟩ ↦ ?_⟩
  · exact h (Function.Embedding.subtype (· ∈ M)) A B (by simpa using hA) (by simpa using hB)
  · exact h e.toEmbedding A B (by simp) (by simp)
  · intro α β _ _ f A B hA hB
    exact (hI (Equiv.ofInjective f f.injective) _ _).trans (hE _ A B hA hB)

theorem _root_.Quantifier.Det.Family.Constant.ext (h : Q.Constant) : Q.Ext :=
  (Det.Family.constant_iff.1 h).1

theorem _root_.Quantifier.Det.Family.Constant.isom (h : Q.Constant) : Q.Isom :=
  (Det.Family.constant_iff.1 h).2

private theorem ncard_image_sdiff {α β : Type*} {f : α → β} (hf : f.Injective) (A B : Set α) :
    (f '' A \ f '' B).ncard = (A \ B).ncard := by
  rw [← Set.image_sdiff hf, Set.ncard_image_of_injective _ hf]

private theorem ncard_image_inter {α β : Type*} {f : α → β} (hf : f.Injective) (A B : Set α) :
    (f '' A ∩ f '' B).ncard = (A ∩ B).ncard := by
  rw [← Set.image_inter hf, Set.ncard_image_of_injective _ hf]

/-- A conservative constant global determiner denotation holds of `A` and `B` on one universe
exactly when it holds of `A'` and `B'` on another with the same `|A \ B|` and `|A ∩ B|`. Both
universes embed in their sum, where permutation invariance applies. -/
theorem _root_.Quantifier.Det.Family.iff_of_ncard_eq (hC : Q.Conservative) (hK : Q.Constant)
    {α β : Type u} [Finite α] [Finite β] {A B : Set α} {A' B' : Set β}
    (hd : (A \ B).ncard = (A' \ B').ncard) (hi : (A ∩ B).ncard = (A' ∩ B').ncard) :
    Q α A B ↔ Q β A' B' := by
  have h₁ := hK (Function.Embedding.inl (α := α) (β := β)) _ _
    (Set.image_subset_range _ A) (Set.image_subset_range _ B)
  have h₂ := hK (Function.Embedding.inr (α := α) (β := β)) _ _
    (Set.image_subset_range _ A') (Set.image_subset_range _ B')
  simp only [Set.preimage_image_eq _ (Function.Embedding.injective _)] at h₁ h₂
  refine h₁.trans ((Det.iff_of_ncard_eq (hC _) (hK.isom.quantityInvariant _) ?_ ?_).trans
    h₂.symm)
  · rw [ncard_image_sdiff (Function.Embedding.injective _),
      ncard_image_sdiff (Function.Embedding.injective _), hd]
  · rw [ncard_image_inter (Function.Embedding.injective _),
      ncard_image_inter (Function.Embedding.injective _), hi]

/-- The tree of a global determiner denotation holds of `(a, b)` when the denotation holds of some
`A` and `B` on some universe with `|A \ B| = a` and `|A ∩ B| = b`. -/
def ofFamily (Q : Det.Family.{u}) : NumberTree := fun a b ↦
  ∃ (α : Type u) (_ : Finite α) (A B : Set α), (A \ B).ncard = a ∧ (A ∩ B).ncard = b ∧ Q α A B

/-- A conservative constant global determiner denotation holds of `A` and `B` exactly when its
tree holds of `|A \ B|` and `|A ∩ B|`. -/
theorem ofFamily_iff (hC : Q.Conservative) (hK : Q.Constant) (α : Type u) [Finite α]
    (A B : Set α) : ofFamily Q (A \ B).ncard (A ∩ B).ncard ↔ Q α A B :=
  ⟨fun ⟨_, _, _, _, hd, hi, h⟩ ↦ (Det.Family.iff_of_ncard_eq hC hK hd hi).1 h,
    fun h ↦ ⟨α, inferInstance, A, B, rfl, rfl, h⟩⟩

/-- The global determiner denotation of a tree is its determiner denotation on every universe. -/
def toFamily (q : NumberTree) : Det.Family.{u} := fun _ _ ↦ q.toDet

theorem conservative_toFamily (q : NumberTree) : (q.toFamily : Det.Family.{u}).Conservative :=
  fun _ _ ↦ conservative_toDet q

/-- The global determiner denotation of a tree is constant; only the restrictor need lie inside
the range of the embedding. -/
theorem constant_toFamily (q : NumberTree) : (q.toFamily : Det.Family.{u}).Constant :=
  fun _ _ _ _ f _ B hA _ ↦ toDet_preimage f.injective B hA q

/-- Some universe realizes any three sizes as `|X \ Y|`, `|X ∩ Y|` and `|Y \ X|`. -/
theorem exists_ncard_eq (a b c : ℕ) : ∃ (γ : Type u) (_ : Finite γ) (X Y : Set γ),
    (X \ Y).ncard = a ∧ (X ∩ Y).ncard = b ∧ (Y \ X).ncard = c := by
  let e₁ : Fin a → ULift.{u} (Fin a ⊕ Fin b ⊕ Fin c) := fun i ↦ ⟨.inl i⟩
  let e₂ : Fin b → ULift.{u} (Fin a ⊕ Fin b ⊕ Fin c) := fun i ↦ ⟨.inr (.inl i)⟩
  let e₃ : Fin c → ULift.{u} (Fin a ⊕ Fin b ⊕ Fin c) := fun i ↦ ⟨.inr (.inr i)⟩
  have card {n : ℕ} {e : Fin n → ULift.{u} (Fin a ⊕ Fin b ⊕ Fin c)} (he : e.Injective) :
      (Set.range e).ncard = n := by
    rw [Set.ncard_range_of_injective he, Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨_, inferInstance, Set.range e₁ ∪ Set.range e₂, Set.range e₂ ∪ Set.range e₃, ?_, ?_, ?_⟩
  · convert card (e := e₁) fun i j h ↦ by simpa [e₁] using h using 2
    ext ⟨x | x | x⟩ <;> simp [e₁, e₂, e₃]
  · convert card (e := e₂) fun i j h ↦ by simpa [e₂] using h using 2
    ext ⟨x | x | x⟩ <;> simp [e₁, e₂, e₃]
  · convert card (e := e₃) fun i j h ↦ by simpa [e₃] using h using 2
    ext ⟨x | x | x⟩ <;> simp [e₁, e₂, e₃]

theorem ofFamily_toFamily (q : NumberTree) : ofFamily (q.toFamily : Det.Family.{u}) = q := by
  funext a b
  refine propext ⟨fun ⟨_, _, _, _, ha, hb, h⟩ ↦ ha ▸ hb ▸ h, fun h ↦ ?_⟩
  obtain ⟨γ, _, X, Y, ha, hb, -⟩ := exists_ncard_eq.{u} a b 0
  exact ⟨γ, inferInstance, X, Y, ha, hb, by rwa [toFamily, toDet_apply, ha, hb]⟩

theorem toFamily_ofFamily (hC : Q.Conservative) (hK : Q.Constant) :
    (ofFamily Q).toFamily = Q := by
  funext α _ A B
  exact propext (ofFamily_iff hC hK α A B)

theorem toFamily_le_toFamily_iff {q r : NumberTree} :
    (q.toFamily : Det.Family.{u}) ≤ r.toFamily ↔ q ≤ r := by
  refine ⟨fun h a b hq ↦ ?_, fun h _ _ _ _ ↦ h _ _⟩
  obtain ⟨γ, _, X, Y, ha, hb, -⟩ := exists_ncard_eq.{u} a b 0
  have : r.toDet X Y := h γ ⟨inferInstance⟩ X Y (show q.toDet X Y by rwa [toDet_apply, ha, hb])
  rwa [toDet_apply, ha, hb] at this

/-- The conservative constant global determiner denotations are the trees of numbers, as
Boolean algebras: the tree of a meet, join or complement is the meet, join or complement of
the trees. -/
noncomputable def familyOrderIso :
    {Q : Det.Family.{u} // Q.Conservative ∧ Q.Constant} ≃o NumberTree where
  toFun Q := ofFamily Q.1
  invFun q := ⟨q.toFamily, conservative_toFamily q, constant_toFamily q⟩
  left_inv Q := Subtype.ext (toFamily_ofFamily Q.2.1 Q.2.2)
  right_inv := ofFamily_toFamily
  map_rel_iff' {Q Q'} := by
    change ofFamily Q.1 ≤ ofFamily Q'.1 ↔ Q.1 ≤ Q'.1
    conv_rhs => rw [← toFamily_ofFamily Q.2.1 Q.2.2, ← toFamily_ofFamily Q'.2.1 Q'.2.2]
    exact toFamily_le_toFamily_iff.symm

/-- The tree of a global determiner denotation that is asymmetric on every universe is
asymmetric. -/
theorem asymmetric_ofFamily (hC : Q.Conservative) (hK : Q.Constant)
    (h : ∀ (α : Type u) [Finite α], Std.Asymm (Q α)) : (ofFamily Q).Asymmetric := by
  intro a c b hac hbc
  obtain ⟨γ, _, X, Y, ha, hb, hc⟩ := exists_ncard_eq.{u} a b c
  have hXY := (ofFamily_iff hC hK γ X Y).1 (by rwa [ha, hb])
  have hYX := (ofFamily_iff hC hK γ Y X).1 (by rwa [hc, Set.inter_comm, hb])
  exact Std.Asymm.asymm X Y hXY hYX

/-- No conservative constant global determiner denotation is asymmetric on every universe unless
it is empty ([van-benthem-1984], Theorem 3.2.1). On a single universe
an asymmetric conservative permutation-invariant denotation can be nonempty. -/
theorem _root_.Quantifier.Det.Family.not_apply_of_asymm (hC : Q.Conservative)
    (hK : Q.Constant) (h : ∀ (α : Type u) [Finite α], Std.Asymm (Q α)) (α : Type u) [Finite α]
    (A B : Set α) : ¬ Q α A B := by
  rw [← ofFamily_iff hC hK, (asymmetric_ofFamily hC hK h).eq_bot]
  exact id

end Family

/-! ### Counting quantifiers -/

/-- The points of rows `0` to `n` of the tree, each given with its row. -/
def points (n : ℕ) : Finset (Σ _ : ℕ, ℕ × ℕ) := (Finset.range (n + 1)).sigma Finset.antidiagonal

theorem card_points (n : ℕ) : (points n).card = (n + 1) * (n + 2) / 2 := by
  have h : ∀ n, (∑ k ∈ Finset.range (n + 1), (k + 1)) * 2 = (n + 1) * (n + 2) := fun n ↦ by
    induction n with
    | zero => rfl
    | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; ring
  rw [points, Finset.card_sigma, Finset.sum_congr rfl fun k _ ↦ Finset.Nat.card_antidiagonal k,
    ← h n, Nat.mul_div_cancel _ two_pos]

/-- There are `2 ^ ((n + 1) * (n + 2) / 2)` sets of points in rows `0` to `n`. That these sets
are the conservative, permutation-invariant quantifiers on `n` individuals, van Benthem's count,
is not proved here; `KeenanStavi1986.card_logical` counts those quantifiers directly, in the
coordinates `(|A|, |A ∩ B|)`. -/
theorem card_powerset_points (n : ℕ) :
    (points n).powerset.card = 2 ^ ((n + 1) * (n + 2) / 2) := by
  rw [Finset.card_powerset, card_points]

/-! ### Constant rows and the individuals a quantifier depends on -/

/-- A quantifier is constant on the `n`-th row when whether it holds of an `n`-element restrictor
does not depend on the scope. -/
def ConstantOnRow (q : NumberTree) (n : ℕ) : Prop :=
  ∀ a b a' b', a + b = n → a' + b' = n → (q a b ↔ q a' b')

/-- A quantifier is constant on rows `0` to `n` when, on a universe of `n` individuals, it does
not depend on its arguments at all. -/
def ConstantBelow (q : NumberTree) (n : ℕ) : Prop :=
  ∀ a b a' b', a + b ≤ n → a' + b' ≤ n → (q a b ↔ q a' b')

theorem not_constantOnRow_iff {n : ℕ} :
    ¬ q.ConstantOnRow n ↔ ∃ a b, a + b + 1 = n ∧ ¬ (q (a + 1) b ↔ q a (b + 1)) := by
  refine ⟨fun h ↦ by_contra fun hn ↦ h ?_,
    fun ⟨a, b, hab, h⟩ hc ↦ h (hc _ _ _ _ (by omega) (by omega))⟩
  simp only [not_exists, not_and, not_not] at hn
  have key : ∀ b ≤ n, (q (n - b) b ↔ q n 0) := fun b hb ↦ by
    induction b with
    | zero => rfl
    | succ b ih =>
      have := hn (n - (b + 1)) b (by omega)
      rw [show n - (b + 1) + 1 = n - b by omega] at this
      exact this.symm.trans (ih (by omega))
  intro a b a' b' h h'
  rw [show a = n - b by omega, show a' = n - b' by omega, key b (by omega), key b' (by omega)]

theorem not_constantBelow_iff {n : ℕ} :
    ¬ q.ConstantBelow n ↔
      ∃ a b, a + b + 1 ≤ n ∧ (¬ (q (a + 1) b ↔ q a b) ∨ ¬ (q a (b + 1) ↔ q a b)) := by
  refine ⟨fun h ↦ by_contra fun hn ↦ h ?_, fun ⟨a, b, hab, h⟩ hc ↦ h.elim
    (· (hc _ _ _ _ (by omega) (by omega))) (· (hc _ _ _ _ (by omega) (by omega)))⟩
  simp only [not_exists, not_and, not_or, not_not] at hn
  have h0 : ∀ b ≤ n, (q 0 b ↔ q 0 0) := fun b hb ↦ by
    induction b with
    | zero => rfl
    | succ b ih => exact (hn 0 b (by omega)).2.trans (ih (by omega))
  have ha : ∀ a b, a + b ≤ n → (q a b ↔ q 0 b) := fun a b h ↦ by
    induction a with
    | zero => rfl
    | succ a ih => exact (hn a b (by omega)).1.trans (ih (by omega))
  intro a b a' b' h h'
  rw [ha a b h, ha a' b' h', h0 b (by omega), h0 b' (by omega)]

section Dependence

variable {α : Type*} [Finite α]

private theorem toDet_iff_of_ncard {A B : Set α} {n b : ℕ} (hA : A.ncard = n)
    (hAB : (A ∩ B).ncard = b) : q.toDet A B ↔ q (n - b) b := by
  have := Set.ncard_inter_add_ncard_sdiff_eq_ncard A B
  rw [toDet_apply, hAB, show (A \ B).ncard = n - b by omega]

theorem toDet_some_iff {A B : Set α} : NumberTree.some.toDet A B ↔ (A ∩ B).Nonempty := by
  rw [toDet_apply, NumberTree.some, ne_eq, Set.ncard_eq_zero, ← ne_eq,
    ← Set.nonempty_iff_ne_empty]

theorem toDet_no_iff {A B : Set α} : NumberTree.no.toDet A B ↔ ¬ (A ∩ B).Nonempty := by
  rw [← toDet_some_iff, ← compl_no, toDet_compl]; exact not_not.symm

theorem toDet_all_iff {A B : Set α} : NumberTree.all.toDet A B ↔ A ⊆ B := by
  rw [toDet_apply, NumberTree.all, Set.ncard_eq_zero, Set.sdiff_eq_empty]

/-- The determiner denotation of a tree depends on whether an individual is in its scope only if
the individual is in its restrictor and the tree is not constant on the restrictor's row. -/
theorem dependsOn_toDet_compl_singleton_iff (A : Set α) (e : α) :
    DependsOn (q.toDet A) {e}ᶜ ↔ (e ∈ A → q.ConstantOnRow A.ncard) := by
  refine ⟨fun hdep hA ↦ by_contra fun hc ↦ ?_, fun h D D' hD ↦ propext ?_⟩
  · obtain ⟨a, b, hab, hq⟩ := not_constantOnRow_iff.1 hc
    obtain ⟨S, hS, hSb⟩ := Set.exists_subset_card_eq (s := A \ {e}) (n := b)
      (by have := Set.ncard_sdiff_singleton_add_one hA; omega)
    have heS : e ∉ S := fun h ↦ (hS h).2 rfl
    have h₁ : (A ∩ S).ncard = b := by
      rw [Set.inter_eq_right.2 fun _ h ↦ (hS h).1, hSb]
    have h₂ : (A ∩ insert e S).ncard = b + 1 := by
      rw [Set.inter_eq_right.2 (Set.insert_subset hA fun _ h ↦ (hS h).1),
        Set.ncard_insert_of_notMem heS, hSb]
    have hagree : ∀ i ∈ ({e}ᶜ : Set α), (i ∈ S) = (i ∈ insert e S) :=
      fun i hi ↦ propext (or_iff_right hi).symm
    have e₁ : q.toDet A S ↔ q (a + 1) b := by
      rw [toDet_iff_of_ncard rfl h₁, ← hab, show a + b + 1 - b = a + 1 by omega]
    have e₂ : q.toDet A (insert e S) ↔ q a (b + 1) := by
      rw [toDet_iff_of_ncard rfl h₂, ← hab, show a + b + 1 - (b + 1) = a by omega]
    exact hq (e₁.symm.trans ((Iff.of_eq (hdep hagree)).trans e₂))
  · by_cases hA : e ∈ A
    · rw [toDet_apply, toDet_apply]
      have := Set.ncard_inter_add_ncard_sdiff_eq_ncard A D
      have := Set.ncard_inter_add_ncard_sdiff_eq_ncard A D'
      exact h hA _ _ _ _ (by omega) (by omega)
    · have hs : ∀ P : Prop → Prop, {x | x ∈ A ∧ P (D x)} = {x | x ∈ A ∧ P (D' x)} := fun P ↦
        Set.ext fun x ↦ by
          by_cases hx : x = e
          · subst hx; simp [hA]
          · simp only [Set.mem_ofPred_eq, hD x hx]
      rw [toDet_apply, toDet_apply]
      exact Iff.of_eq (congrArg₂ q (congrArg Set.ncard (hs Not)) (congrArg Set.ncard (hs id)))

theorem exists_not_dependsOn_toDet_restrictor_iff (e : α) :
    (∃ B, ¬ DependsOn (fun A ↦ q.toDet A B) {e}ᶜ) ↔ ¬ q.ConstantBelow (Nat.card α) := by
  refine ⟨fun ⟨B, hB⟩ hc ↦ hB fun A A' _ ↦ propext ?_, fun hc ↦ ?_⟩
  · show q.toDet A B ↔ q.toDet A' B
    rw [toDet_apply, toDet_apply]
    have := Set.ncard_inter_add_ncard_sdiff_eq_ncard A B
    have := Set.ncard_inter_add_ncard_sdiff_eq_ncard A' B
    have := Set.ncard_le_card A
    have := Set.ncard_le_card A'
    exact hc _ _ _ _ (by omega) (by omega)
  obtain ⟨a, b, hab, hq⟩ := not_constantBelow_iff.1 hc
  obtain ⟨T, hT, hTn⟩ := Set.exists_subset_card_eq (s := Set.univ \ {e}) (n := a + b)
    (by have := Set.ncard_sdiff_singleton_add_one (Set.mem_univ e)
        rw [Set.ncard_univ] at this; omega)
  obtain ⟨S, hST, hSb⟩ := Set.exists_subset_card_eq (s := T) (n := b) (by omega)
  have heT : e ∉ T := fun h ↦ (hT h).2 rfl
  have heS : e ∉ S := fun h ↦ heT (hST h)
  have hA' : (insert e T).ncard = a + b + 1 := by rw [Set.ncard_insert_of_notMem heT, hTn]
  have hagree : ∀ i ∈ ({e}ᶜ : Set α), (i ∈ T) = (i ∈ insert e T) :=
    fun i hi ↦ propext (or_iff_right hi).symm
  rcases hq with hq | hq
  · refine ⟨S, fun hdep ↦ hq ?_⟩
    have h₁ : (T ∩ S).ncard = b := by rw [Set.inter_eq_right.2 hST, hSb]
    have h₂ : (insert e T ∩ S).ncard = b := by
      rw [Set.inter_eq_right.2 (hST.trans (Set.subset_insert e T)), hSb]
    have e₁ : q.toDet T S ↔ q a b := by
      rw [toDet_iff_of_ncard hTn h₁, show a + b - b = a by omega]
    have e₂ : q.toDet (insert e T) S ↔ q (a + 1) b := by
      rw [toDet_iff_of_ncard hA' h₂, show a + b + 1 - b = a + 1 by omega]
    exact e₂.symm.trans ((Iff.of_eq (hdep hagree)).symm.trans e₁)
  · refine ⟨insert e S, fun hdep ↦ hq ?_⟩
    have h₁ : (T ∩ insert e S).ncard = b := by
      rw [Set.inter_insert_of_notMem heT, Set.inter_eq_right.2 hST, hSb]
    have h₂ : (insert e T ∩ insert e S).ncard = b + 1 := by
      rw [Set.inter_eq_right.2 (Set.insert_subset_insert hST), Set.ncard_insert_of_notMem heS, hSb]
    have e₁ : q.toDet T (insert e S) ↔ q a b := by
      rw [toDet_iff_of_ncard hTn h₁, show a + b - b = a by omega]
    have e₂ : q.toDet (insert e T) (insert e S) ↔ q a (b + 1) := by
      rw [toDet_iff_of_ncard hA' h₂, show a + b + 1 - (b + 1) = a by omega]
    exact e₂.symm.trans ((Iff.of_eq (hdep hagree)).symm.trans e₁)

end Dependence

end NumberTree

end Quantifier
