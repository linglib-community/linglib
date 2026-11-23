/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.SuccPred.Tree
public import Linglib.Phonology.Autosegmental.Edit
public import Linglib.Phonology.Autosegmental.Realization
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Representations along a tree of tiers

The tiers of a representation often form a tree, with the timing slots at the root and each
other tier hanging from one tier above it: a melody over its slots, the planes of a multiplanar
representation around their slots, the class nodes and features of a feature geometry under the
root node. For a tree of tiers `T : ParentTree ι`, the tokens a token is linked to on the tiers
hanging from its own are its `children`, and slot `k` dominates the tokens it reaches by
descending lines, `X.Dominates T k j q`. The representation reads the label `b` on tier `j` at
slot `k`, `X.Reads T k j b`, when that slot dominates a token of the tier with that label.

A realization `(w.map g₀).prod` whose primitives have one slot each is read symbol by symbol:
reading it at slot `k` is reading the primitive of the `k`th symbol at its slot
(`reads_prod_map`). Spreading a tier from the `m`th symbol onto the `n`th is a change of lines,
`spreadTier`: the token of the `n`th symbol on the tier above is delinked from its own token and
linked to that of the `m`th. When the primitives have at most one token on the two tiers, the
result has no crossing lines exactly when no symbol strictly between the two has a line between
those tiers (`noCrossing_spreadTier_iff`): a symbol with a token there blocks, and one without
is transparent.

## TODO

* The proofs of `reads_prod_map` and `noCrossing_spreadTier_iff`, which are checked on small
  trees of tiers.
* `AR.SurfacesWith` on two tiers and `AR.hostedOn` on planes are `Reads` on trees of depth one,
  and the line edits of `Multiplanar.lean` are `addLine` and `eraseLine` on a star.
* The graph of a tree of tiers is acyclic, so by `AR.noCrossing_iff_hasIntervalOrder_of_isAcyclic`
  a representation whose lines run along it obeys the No-Crossing Constraint exactly when it has
  an interval order.
-/

@[expose] public section

namespace Autosegmental.AR

variable {ι : Type*} {τ : ι → Type*} [Fintype ι] [DecidableEq ι] (T : ParentTree ι)

section Dominates

variable (X : AR τ)

/-- The tokens a token is linked to on the tiers hanging from its own. -/
def children (v : ι × ℕ) : Finset (ι × ℕ) :=
  Finset.univ.biUnion fun j ↦
    if T.parent j = v.1 ∧ j ≠ T.root then
      ((X.lines v.1 j).filter (·.1 = v.2)).image fun x ↦ (j, x.2)
    else ∅

/-- The tokens a token reaches through at most `d` descending lines. -/
def descendants : ℕ → ι × ℕ → Finset (ι × ℕ)
  | 0, v => {v}
  | d + 1, v => insert v ((X.children T v).biUnion (descendants d))

/-- Slot `k` dominates position `q` of tier `j`: descending lines lead from the slot to it. -/
def Dominates (k : ℕ) (j : ι) (q : ℕ) : Prop :=
  (j, q) ∈ X.descendants T (Fintype.card ι) (T.root, k)

instance (k : ℕ) (j : ι) (q : ℕ) : Decidable (X.Dominates T k j q) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- `X` reads the label `b` on tier `j` at slot `k`: the slot dominates a token of the tier with
that label. -/
def Reads (k : ℕ) (j : ι) (b : τ j) : Prop :=
  ∃ q ∈ Finset.range (X.word j).length, X.Dominates T k j q ∧ (X.word j)[q]? = some b

instance [∀ j, DecidableEq (τ j)] (k : ℕ) (j : ι) (b : τ j) : Decidable (X.Reads T k j b) :=
  inferInstanceAs (Decidable (∃ q ∈ Finset.range _, _))

end Dominates

section Realization

variable {S : Type*} (g₀ : S → AR τ) {w : List S} {j : ι} {m n k : ℕ}

/-- Spreading tier `j` from the `m`th symbol of a realization onto the `n`th: the token of the
`n`th symbol on the tier above `j` is delinked from its own token on `j` and linked to that of
the `m`th symbol. -/
def spreadTier (w : List S) (j : ι) (m n : ℕ) : AR τ :=
  ((w.map g₀).prod.eraseLine (T.parent j) j (tierOffset g₀ (T.parent j) w n)
      (tierOffset g₀ j w n)).addLine
    (T.parent j) j (tierOffset g₀ (T.parent j) w n) (tierOffset g₀ j w m)

/-- Reading a realization at slot `k` is reading the primitive of its `k`th symbol. -/
theorem reads_prod_map (h : ∀ s, ((g₀ s).word T.root).length = 1) {b : τ j} :
    (w.map g₀).prod.Reads T k j b ↔ ∃ hk : k < w.length, (g₀ w[k]).Reads T 0 j b := by
  -- TODO: by `link_prod_map` every line lies inside one symbol's primitive, and the root
  -- token of the `k`th symbol is at `k`; by induction on the depth, the descendants of
  -- `(T.root, k)` are those of `(T.root, 0)` in the primitive, moved by the tier offsets.
  sorry

/-- Spreading a tier crosses no line exactly when no symbol strictly between the two has a line
between that tier and the one above it. -/
theorem noCrossing_spreadTier_iff (hj : j ≠ T.root)
    (hp : ∀ s, ((g₀ s).word (T.parent j)).length ≤ 1) (hc : ∀ s, ((g₀ s).word j).length ≤ 1)
    (hm : m < w.length) (hn : n < w.length) (hmj : (g₀ w[m]).word j ≠ [])
    (hnp : (g₀ w[n]).word (T.parent j) ≠ []) (hw : (w.map g₀).prod.NoCrossing) :
    (spreadTier T g₀ w j m n).NoCrossing ↔
      ∀ k (hk : k < w.length), k ∈ Set.uIoo m n → ¬ (g₀ w[k]).Link (T.parent j) j 0 0 := by
  -- TODO: only the lines between `T.parent j` and `j` change. A symbol `k` with a line there
  -- has its two tokens strictly between those of `m` and `n` on both tiers when `k` is, by
  -- monotonicity of `tierOffset`, and the new line from the token of `n` to the token of `m`
  -- crosses it; a symbol without one contributes no line between the two tiers.
  sorry

end Realization

end Autosegmental.AR
