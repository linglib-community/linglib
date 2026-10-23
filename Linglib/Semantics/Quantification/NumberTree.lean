module

public import Linglib.Semantics.Quantification.Defs
public import Linglib.Core.Data.Fintype.EquivFin
public import Linglib.Core.Data.Set.Card
public import Linglib.Core.Logic.Function.DependsOn
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Ring

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
* `Quantifier.NumberTree.ofGQ`, `Quantifier.NumberTree.toGQ`: the tree of a generalized
  quantifier over a finite universe, and the quantifier of a tree, counting with `Set.ncard`.
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
* `Quantifier.NumberTree.ofGQ_iff`: a conservative, permutation-invariant generalized quantifier
  holds of `A` and `B` exactly when its tree holds of `|A \ B|` and `|A ∩ B|`.
* `Quantifier.NumberTree.conservative_toGQ`, `Quantifier.NumberTree.quantityInvariant_toGQ`: the
  quantifier of a tree is conservative and permutation invariant.
* `Quantifier.NumberTree.ScopeMonotone.toGQ`, `Quantifier.NumberTree.ScopeAntitone.toGQ`: the
  quantifier of a scope-monotone tree is scope monotone, and likewise antitone.
* `Quantifier.NumberTree.dependsOn_toGQ_compl_singleton_iff`: the quantifier of a tree depends on
  whether an individual is in its scope iff the individual is in its restrictor and the tree is not
  constant on the restrictor's row.
* `Quantifier.NumberTree.card_powerset_points`: there are `2 ^ ((n + 1) * (n + 2) / 2)` sets of
  points in rows `0` to `n`, the number of conservative, permutation-invariant quantifiers on a
  universe of `n` individuals.

## Implementation notes

`Variety` asks only that the quantifier hold somewhere and fail somewhere. Van Benthem's VAR is
stronger in both of its versions, so results assuming `Variety` apply under VAR. The paper asks
for a presence and an absence among the points `(0, 0)`, `(1, 0)` and `(0, 1)`, and the book's
chapter on quantifiers, which restates the tree and the postulates, asks for both in every row
below the top.

Continuity, absence of deadlock and uniformity each treat presence and absence of the quantifier
alike. Each is stated as a condition on presence (`RowConvex`, `NoDeadlock`, `Homogeneous`) that
is imposed on the quantifier and on its complement.

## References

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

/-- The quantifier *at least two* is not uniform. Adding an individual to `A ∩ B` leaves it false
at `(0, 0)` and makes it true at `(0, 1)`. -/
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

/-! ### The tree of a generalized quantifier

A generalized quantifier counts its arguments with `Set.ncard`, which asks for no decidability;
the counts are meaningful when the sets are finite. -/

section OfGQ

open GQ

variable {α : Type*} {Q : GQ α} {A B A' B' : α → Prop}

/-- A quantifier has quantity when `Q(A, B)` depends only on the four cardinalities `|A ∩ B|`,
`|A \ B|`, `|B \ A|` and `|M \ (A ∪ B)|`. -/
def _root_.Quantifier.GQ.Quantity (q : GQ α) : Prop :=
  ∀ R₁ S₁ R₂ S₂ : α → Prop,
    {x | R₁ x ∧ S₁ x}.ncard = {x | R₂ x ∧ S₂ x}.ncard →
    {x | R₁ x ∧ ¬ S₁ x}.ncard = {x | R₂ x ∧ ¬ S₂ x}.ncard →
    {x | ¬ R₁ x ∧ S₁ x}.ncard = {x | ¬ R₂ x ∧ S₂ x}.ncard →
    {x | ¬ R₁ x ∧ ¬ S₁ x}.ncard = {x | ¬ R₂ x ∧ ¬ S₂ x}.ncard → (q R₁ S₁ ↔ q R₂ S₂)

open Classical in
private theorem nat_card_fiber (R S : α → Prop) (p q : Bool) :
    Nat.card {x // (decide (R x), decide (S x)) = (p, q)} =
      {x | (R x ↔ p) ∧ (S x ↔ q)}.ncard := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ by cases p <;> cases q <;> simp)

theorem _root_.Quantifier.GQ.QuantityInvariant.quantity [Finite α] (hQ : QuantityInvariant Q) :
    Q.Quantity := by
  classical
  intro R₁ S₁ R₂ S₂ hTT hTF hFT hFF
  obtain ⟨e, he⟩ := Equiv.exists_comp_eq_of_card_fiber_eq
    (f := fun x ↦ (decide (R₁ x), decide (S₁ x))) (g := fun x ↦ (decide (R₂ x), decide (S₂ x)))
    fun ⟨p, q⟩ ↦ by
      rw [nat_card_fiber, nat_card_fiber]
      cases p <;> cases q <;> simp only [Bool.false_eq_true, iff_false, iff_true] <;> symm <;>
        assumption
  exact hQ R₁ S₁ R₂ S₂ e e.bijective
    (fun x ↦ decide_eq_decide.1 (congrArg Prod.fst (congrFun he x)))
    fun x ↦ decide_eq_decide.1 (congrArg Prod.snd (congrFun he x))

theorem _root_.Quantifier.GQ.Quantity.quantityInvariant (hQ : Q.Quantity) :
    QuantityInvariant Q := by
  intro A B A' B' f hf hA hB
  have key (P P' : α → Prop) (h : ∀ x, P (f x) ↔ P' x) : {x | P x}.ncard = {x | P' x}.ncard := by
    rw [← Set.ncard_preimage_of_injective_subset_range hf.1 (by simp [hf.2.range_eq])]
    exact congrArg Set.ncard (Set.ext h)
  exact hQ A B A' B' (key _ _ fun x ↦ by rw [hA, hB]) (key _ _ fun x ↦ by rw [hA, hB])
    (key _ _ fun x ↦ by rw [hA, hB]) (key _ _ fun x ↦ by rw [hA, hB])

theorem _root_.Quantifier.GQ.iff_of_ncard_eq [Finite α] (hC : Conservative Q)
    (hQ : QuantityInvariant Q) (hd : {x | A x ∧ ¬ B x}.ncard = {x | A' x ∧ ¬ B' x}.ncard)
    (hi : {x | A x ∧ B x}.ncard = {x | A' x ∧ B' x}.ncard) : Q A B ↔ Q A' B' := by
  have hA : {x | A x ∧ B x}.ncard + {x | A x ∧ ¬ B x}.ncard = {x | A x}.ncard :=
    Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _
  have hA' : {x | A' x ∧ B' x}.ncard + {x | A' x ∧ ¬ B' x}.ncard = {x | A' x}.ncard :=
    Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _
  have hn := Set.ncard_add_ncard_compl {x | A x}
  have hn' := Set.ncard_add_ncard_compl {x | A' x}
  have hN : {x | ¬ A x}.ncard = {x | ¬ A' x}.ncard := by
    change {x | A x}ᶜ.ncard = {x | A' x}ᶜ.ncard
    omega
  rw [hC A B, hC A' B']
  refine hQ.quantity _ _ _ _ ?_ ?_ ?_ ?_
  · convert hi using 2 <;> ext <;> simp only [Set.mem_ofPred_eq] <;> tauto
  · convert hd using 2 <;> ext <;> simp only [Set.mem_ofPred_eq] <;> tauto
  · congr 1; ext; simp only [Set.mem_ofPred_eq]; tauto
  · convert hN using 2 <;> ext <;> simp only [Set.mem_ofPred_eq] <;> tauto

/-- The tree of a generalized quantifier holds of `(a, b)` when the quantifier holds of some
`A` and `B` with `|A \ B| = a` and `|A ∩ B| = b`. -/
def ofGQ (Q : GQ α) : NumberTree := fun a b ↦
  ∃ A B : α → Prop, {x | A x ∧ ¬ B x}.ncard = a ∧ {x | A x ∧ B x}.ncard = b ∧ Q A B

/-- A conservative, permutation-invariant quantifier on a finite universe holds of `A` and `B`
exactly when its tree holds of `|A \ B|` and `|A ∩ B|`. -/
theorem ofGQ_iff [Finite α] (hC : Conservative Q) (hQ : QuantityInvariant Q) (A B : α → Prop) :
    ofGQ Q {x | A x ∧ ¬ B x}.ncard {x | A x ∧ B x}.ncard ↔ Q A B :=
  ⟨fun ⟨_, _, hd, hi, h⟩ ↦ (GQ.iff_of_ncard_eq hC hQ hd hi).mp h, fun h ↦ ⟨A, B, rfl, rfl, h⟩⟩

/-- The quantifier of a tree holds of `A` and `B` when the tree holds of `|A \ B|` and
`|A ∩ B|`. -/
def toGQ (q : NumberTree) : GQ α := fun A B ↦ q {x | A x ∧ ¬ B x}.ncard {x | A x ∧ B x}.ncard

theorem toGQ_apply (q : NumberTree) (A B : α → Prop) :
    q.toGQ A B ↔ q {x | A x ∧ ¬ B x}.ncard {x | A x ∧ B x}.ncard := Iff.rfl

@[simp] theorem toGQ_inf (q r : NumberTree) : (q ⊓ r).toGQ = (q.toGQ ⊓ r.toGQ : GQ α) := rfl

@[simp] theorem toGQ_compl (q : NumberTree) : qᶜ.toGQ = (q.toGQᶜ : GQ α) := rfl

@[simp] theorem toGQ_innerNeg (q : NumberTree) : q.innerNeg.toGQ = (q.toGQ : GQ α).innerNeg := by
  funext A B; simp only [toGQ, innerNeg_apply, GQ.innerNeg, not_not]

/-- On a finite universe the quantifier of a decidable tree is decidable at decidable
arguments. -/
instance toGQ.decidable [Fintype α] (q : NumberTree) [DecidableRel q] (A B : α → Prop)
    [DecidablePred A] [DecidablePred B] : Decidable (q.toGQ A B) :=
  decidable_of_iff (q (Finset.univ.filter fun x ↦ A x ∧ ¬ B x).card
    (Finset.univ.filter fun x ↦ A x ∧ B x).card) <| by
      rw [toGQ_apply, Set.ncard_setOf_eq_card_filter, Set.ncard_setOf_eq_card_filter]

/-- The quantifier of a tree is conservative, since `A \ B` and `A ∩ B` see only `B ∩ A`. -/
theorem conservative_toGQ (q : NumberTree) : Conservative (q.toGQ : GQ α) := fun A B ↦ by
  unfold toGQ
  congr! 3 <;> ext <;> tauto

theorem quantity_toGQ (q : NumberTree) : (q.toGQ : GQ α).Quantity :=
  fun _ _ _ _ hi hd _ _ ↦ by rw [toGQ_apply, toGQ_apply, hi, hd]

/-- The quantifier of a tree is permutation invariant. -/
theorem quantityInvariant_toGQ (q : NumberTree) : QuantityInvariant (q.toGQ : GQ α) :=
  (quantity_toGQ q).quantityInvariant

/-- The quantifier of a scope-monotone tree is scope monotone, since enlarging `B` within `A` moves
`|A \ B ∩ B'|` individuals from `A \ B` to `A ∩ B`. -/
theorem ScopeMonotone.toGQ [Finite α] {q : NumberTree} (h : q.ScopeMonotone) :
    GQ.ScopeMonotone (q.toGQ : GQ α) := by
  intro A B B' hB hq
  unfold NumberTree.toGQ at hq ⊢
  have h₁ := Set.ncard_inter_add_ncard_sdiff_eq_ncard {x | A x ∧ ¬ B x} {x | B' x}
  have h₂ := Set.ncard_inter_add_ncard_sdiff_eq_ncard {x | A x ∧ B' x} {x | B x}
  replace hB : ∀ x, B x → B' x := hB
  have e₁ : {x | A x ∧ B' x} ∩ {x | B x} = {x | A x ∧ B x} := by ext x; have := hB x; grind
  have e₂ : {x | A x ∧ ¬ B x} \ {x | B' x} = {x | A x ∧ ¬ B' x} := by
    ext x; have := hB x; grind
  have e₃ : {x | A x ∧ B' x} \ {x | B x} = {x | A x ∧ ¬ B x} ∩ {x | B' x} := by ext; grind
  rw [e₂] at h₁
  rw [e₁, e₃] at h₂
  rw [← h₂]
  rw [← h₁, Nat.add_comm] at hq
  exact h.shift _ hq

/-- The quantifier of a scope-antitone tree is scope antitone. -/
theorem ScopeAntitone.toGQ [Finite α] {q : NumberTree} (h : q.ScopeAntitone) :
    GQ.ScopeAntitone (q.toGQ : GQ α) :=
  fun A _ _ hB hq ↦ Classical.byContradiction fun hn ↦ h.compl.toGQ A hB hn hq

end OfGQ

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

/-- The conservative, permutation-invariant quantifiers on a universe of `n` individuals are the
sets of points in rows `0` to `n` of the tree. -/
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

private theorem ncard_and_not_add_ncard_and (A B : α → Prop) :
    {x | A x ∧ ¬ B x}.ncard + {x | A x ∧ B x}.ncard = {x | A x}.ncard := by
  rw [add_comm]; exact Set.ncard_inter_add_ncard_sdiff_eq_ncard {x | A x} {x | B x}

private theorem toGQ_iff_of_ncard {A B : α → Prop} {n b : ℕ} (hA : {x | A x}.ncard = n)
    (hAB : {x | A x ∧ B x}.ncard = b) : q.toGQ A B ↔ q (n - b) b := by
  have := ncard_and_not_add_ncard_and A B
  rw [toGQ_apply, hAB, show {x | A x ∧ ¬ B x}.ncard = n - b by omega]

private theorem ncard_or_eq {T : Set α} {e : α} (he : e ∉ T) :
    {x | x ∈ T ∨ x = e}.ncard = T.ncard + 1 := by
  rw [show {x | x ∈ T ∨ x = e} = insert e T from Set.ext fun _ ↦ or_comm,
    Set.ncard_insert_of_notMem he]

theorem toGQ_some_iff {A B : α → Prop} : NumberTree.some.toGQ A B ↔ ∃ x, A x ∧ B x := by
  rw [toGQ_apply, NumberTree.some, ne_eq, Set.ncard_eq_zero, ← ne_eq, ← Set.nonempty_iff_ne_empty]
  rfl

theorem toGQ_no_iff {A B : α → Prop} : NumberTree.no.toGQ A B ↔ ¬ ∃ x, A x ∧ B x := by
  rw [← toGQ_some_iff, ← compl_no, toGQ_compl]; exact not_not.symm

theorem toGQ_all_iff {A B : α → Prop} : NumberTree.all.toGQ A B ↔ ∀ x, A x → B x := by
  rw [toGQ_apply, NumberTree.all, Set.ncard_eq_zero, Set.eq_empty_iff_forall_notMem]
  simp

/-- The quantifier of a tree depends on whether an individual is in its scope only if the
individual is in its restrictor and the tree is not constant on the restrictor's row. -/
theorem dependsOn_toGQ_compl_singleton_iff (A : α → Prop) (e : α) :
    DependsOn (q.toGQ A) {e}ᶜ ↔ (A e → q.ConstantOnRow {x | A x}.ncard) := by
  refine ⟨fun hdep hA ↦ by_contra fun hc ↦ ?_, fun h D D' hD ↦ propext ?_⟩
  · obtain ⟨a, b, hab, hq⟩ := not_constantOnRow_iff.1 hc
    have hmem : e ∈ {x | A x} := hA
    obtain ⟨S, hS, hSb⟩ := Set.exists_subset_card_eq (s := {x | A x} \ {e}) (n := b)
      (by have := Set.ncard_sdiff_singleton_add_one hmem; omega)
    have heS : e ∉ S := fun h ↦ (hS h).2 rfl
    have h₁ : {x | A x ∧ x ∈ S}.ncard = b := by
      rw [show {x | A x ∧ x ∈ S} = S from Set.ext fun _ ↦ ⟨And.right, fun h ↦ ⟨(hS h).1, h⟩⟩, hSb]
    have h₂ : {x | A x ∧ (x ∈ S ∨ x = e)}.ncard = b + 1 := by
      rw [show {x | A x ∧ (x ∈ S ∨ x = e)} = {x | x ∈ S ∨ x = e} from Set.ext fun x ↦
        ⟨And.right, fun h ↦ ⟨h.elim (fun h ↦ (hS h).1) (· ▸ hA), h⟩⟩, ncard_or_eq heS, hSb]
    have hagree : ∀ i ∈ ({e}ᶜ : Set α), (i ∈ S) = (i ∈ S ∨ i = e) :=
      fun i hi ↦ propext (or_iff_left hi).symm
    have e₁ : q.toGQ A (· ∈ S) ↔ q (a + 1) b := by
      rw [toGQ_iff_of_ncard rfl h₁, ← hab, show a + b + 1 - b = a + 1 by omega]
    have e₂ : q.toGQ A (fun x ↦ x ∈ S ∨ x = e) ↔ q a (b + 1) := by
      rw [toGQ_iff_of_ncard rfl h₂, ← hab, show a + b + 1 - (b + 1) = a by omega]
    exact hq (e₁.symm.trans ((Iff.of_eq (hdep hagree)).trans e₂))
  · by_cases hA : A e
    · rw [toGQ_apply, toGQ_apply]
      exact h hA _ _ _ _ (ncard_and_not_add_ncard_and A D) (ncard_and_not_add_ncard_and A D')
    · have hs : ∀ P : Prop → Prop, {x | A x ∧ P (D x)} = {x | A x ∧ P (D' x)} := fun P ↦
        Set.ext fun x ↦ by
          by_cases hx : x = e
          · subst hx; simp [hA]
          · simp only [Set.mem_ofPred_eq, hD x hx]
      rw [toGQ_apply, toGQ_apply]
      exact Iff.of_eq (congrArg₂ q (congrArg Set.ncard (hs Not)) (congrArg Set.ncard (hs id)))

theorem exists_not_dependsOn_toGQ_restrictor_iff (e : α) :
    (∃ B, ¬ DependsOn (fun A ↦ q.toGQ A B) {e}ᶜ) ↔ ¬ q.ConstantBelow (Nat.card α) := by
  refine ⟨fun ⟨B, hB⟩ hc ↦ hB fun A A' _ ↦ propext ?_, fun hc ↦ ?_⟩
  · show q.toGQ A B ↔ q.toGQ A' B
    rw [toGQ_apply, toGQ_apply]
    have := ncard_and_not_add_ncard_and A B
    have := ncard_and_not_add_ncard_and A' B
    have := Set.ncard_le_card {x | A x}
    have := Set.ncard_le_card {x | A' x}
    exact hc _ _ _ _ (by omega) (by omega)
  obtain ⟨a, b, hab, hq⟩ := not_constantBelow_iff.1 hc
  have hmem : e ∈ (Set.univ : Set α) := Set.mem_univ e
  obtain ⟨T, hT, hTn⟩ := Set.exists_subset_card_eq (s := Set.univ \ {e}) (n := a + b)
    (by have := Set.ncard_sdiff_singleton_add_one hmem; rw [Set.ncard_univ] at this; omega)
  obtain ⟨S, hST, hSb⟩ := Set.exists_subset_card_eq (s := T) (n := b) (by omega)
  have heT : e ∉ T := fun h ↦ (hT h).2 rfl
  have heS : e ∉ S := fun h ↦ heT (hST h)
  have hA : {x | x ∈ T}.ncard = a + b := hTn
  have hA' : {x | x ∈ T ∨ x = e}.ncard = a + b + 1 := by rw [ncard_or_eq heT, hTn]
  have hagree : ∀ i ∈ ({e}ᶜ : Set α), (i ∈ T) = (i ∈ T ∨ i = e) :=
    fun i hi ↦ propext (or_iff_left hi).symm
  rcases hq with hq | hq
  · refine ⟨(· ∈ S), fun hdep ↦ hq ?_⟩
    have h₁ : {x | x ∈ T ∧ x ∈ S}.ncard = b := by
      rw [show {x | x ∈ T ∧ x ∈ S} = S from Set.ext fun _ ↦ ⟨And.right, fun h ↦ ⟨hST h, h⟩⟩, hSb]
    have h₂ : {x | (x ∈ T ∨ x = e) ∧ x ∈ S}.ncard = b := by
      rw [show {x | (x ∈ T ∨ x = e) ∧ x ∈ S} = S from
        Set.ext fun _ ↦ ⟨And.right, fun h ↦ ⟨.inl (hST h), h⟩⟩, hSb]
    have e₁ : q.toGQ (· ∈ T) (· ∈ S) ↔ q a b := by
      rw [toGQ_iff_of_ncard hA h₁, show a + b - b = a by omega]
    have e₂ : q.toGQ (fun x ↦ x ∈ T ∨ x = e) (· ∈ S) ↔ q (a + 1) b := by
      rw [toGQ_iff_of_ncard hA' h₂, show a + b + 1 - b = a + 1 by omega]
    exact e₂.symm.trans ((Iff.of_eq (hdep hagree)).symm.trans e₁)
  · refine ⟨fun x ↦ x ∈ S ∨ x = e, fun hdep ↦ hq ?_⟩
    have h₁ : {x | x ∈ T ∧ (x ∈ S ∨ x = e)}.ncard = b := by
      rw [show {x | x ∈ T ∧ (x ∈ S ∨ x = e)} = S from Set.ext fun x ↦
        ⟨fun h ↦ h.2.resolve_right fun hx ↦ heT (hx ▸ h.1), fun h ↦ ⟨hST h, .inl h⟩⟩, hSb]
    have h₂ : {x | (x ∈ T ∨ x = e) ∧ (x ∈ S ∨ x = e)}.ncard = b + 1 := by
      rw [show {x | (x ∈ T ∨ x = e) ∧ (x ∈ S ∨ x = e)} = {x | x ∈ S ∨ x = e} from
        Set.ext fun x ↦ ⟨And.right, fun h ↦ ⟨h.imp_left (hST ·), h⟩⟩, ncard_or_eq heS, hSb]
    have e₁ : q.toGQ (· ∈ T) (fun x ↦ x ∈ S ∨ x = e) ↔ q a b := by
      rw [toGQ_iff_of_ncard hA h₁, show a + b - b = a by omega]
    have e₂ : q.toGQ (fun x ↦ x ∈ T ∨ x = e) (fun x ↦ x ∈ S ∨ x = e) ↔ q a (b + 1) := by
      rw [toGQ_iff_of_ncard hA' h₂, show a + b + 1 - (b + 1) = a by omega]
    exact e₂.symm.trans ((Iff.of_eq (hdep hagree)).symm.trans e₁)

end Dependence

end NumberTree

end Quantifier
