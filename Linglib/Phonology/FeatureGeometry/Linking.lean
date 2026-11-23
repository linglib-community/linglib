module

public import Linglib.Phonology.FeatureGeometry
public import Linglib.Phonology.Autosegmental.Realization
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Feature geometry as an autosegmental representation

A word of segments in a feature geometry is an autosegmental representation whose tiers are the
class nodes and the features. For a specification `s`, the representation `ofSpec node s` has one
token on the tier of the root, one on the tier of each node `s` bears, and one on the tier of
each placed feature `s` specifies, labelled with its value; each token has a line to the token of
the tier its own tier hangs from, `parentTier`. `ofWord node w` concatenates these, so its lines
join only a tier and its parent (`parentTier_of_link_ofWord`) and none of them cross
(`noCrossing_ofWord`).

A representation is read back slot by slot. `Reads node X k f b` holds when the `k`th root token
dominates, through lines that descend the tree, a token of the feature `f` with value `b`, and
reading a realized word gives its segments (`reads_ofWord_iff`).

Spreading is a change of lines. `linkNode node w a m n` spreads the node `a` from segment `m` onto
segment `n`: the token of segment `n` above `a` is delinked from its own `a` token and linked to
that of segment `m`, which the two segments then share. The result reads as the word with
`spread node a` applied at `n` (`reads_linkNode_iff`), and it has no crossing lines exactly when
no segment strictly between `m` and `n` bears `a` (`noCrossing_linkNode_iff`): a segment that
bears the node blocks the spreading and one that lacks it is transparent.

## Implementation notes

Every segment has a root token, whether or not it specifies a placed feature, so the position of
a root token is the position of its segment. Unplaced features have no tier. Tokens are found by
counting: the token of segment `k` on a tier stands at the number of earlier segments with a
token there, `Autosegmental.AR.tierOffset`.

## TODO

* The proofs of `reads_ofWord_iff`, `reads_linkNode_iff` and `noCrossing_linkNode_iff`, which
  are checked on small geometries.
* Spreading a single feature, whose tier hangs from the tier of its node.
* The tiers form a tree under `parentTier`, so by
  `Autosegmental.AR.noCrossing_iff_hasIntervalOrder_of_isAcyclic` a representation whose lines
  run along it obeys the No-Crossing Constraint exactly when it has an interval order.
* Contour segments, with two tokens of one feature under one node token, and geminates, which
  need a tier of timing slots below the root.

## References

* [G. N. Clements, *The Geometry of Phonological Features* (1985)][clements-1985]
* [E. C. Sagey, *The Representation of Features and Relations in Non-Linear Phonology*
  (1986)][sagey-1986]
-/

@[expose] public section

open Autosegmental

namespace Phonology.FeatureGeometry

universe u

variable {N F : Type*} {β : Type u}

/-- The tiers of a geometry are its class nodes and its features; a node token carries no label
and a feature token carries its value. -/
abbrev Tiers (N F : Type*) (β : Type u) : N ⊕ F → Type u :=
  Sum.elim (fun _ ↦ PUnit) (fun _ ↦ β)

variable [PartialOrder N] [OrderBot N] [PredOrder N] [DecidableLE N] [DecidableEq N]
  [Fintype F] [DecidableEq F] (node : F → Option N)

/-- The tier a tier hangs from: a class node from its parent, a feature from its node. -/
def parentTier : N ⊕ F → Option (N ⊕ F)
  | .inl a => if a = ⊥ then none else some (.inl (Order.pred a))
  | .inr f => (node f).map .inl

/-- The tokens of a specification on each tier: one on the root tier and on the tier of each
node it bears, and its value on the tier of each placed feature it specifies. -/
def tierWord (s : F → Option β) : ∀ t, List (Tiers N F β t)
  | .inl a => if a = ⊥ ∨ Bears node s a then [PUnit.unit] else []
  | .inr f => if (node f).isSome then (s f).toList else []

omit [PredOrder N] [DecidableEq F] in
theorem length_tierWord_le_one (s : F → Option β) (t : N ⊕ F) :
    (tierWord node s t).length ≤ 1 := by
  rcases t with a | f
  · simp only [tierWord]
    split_ifs <;> simp
  · simp only [tierWord]
    split_ifs
    · cases s f <;> simp
    · simp

/-- The representation of one specification: its tokens, each linked to the token of the tier
its own tier hangs from. -/
def ofSpec (s : F → Option β) : AR (Tiers N F β) :=
  AR.fromRel (tierWord node s) fun t' t _ _ ↦ parentTier node t = some t'

/-- The representation of a word of specifications, those of its segments in order. -/
def ofWord (w : List (F → Option β)) : AR (Tiers N F β) := (w.map (ofSpec node)).prod

theorem noCrossing_ofSpec (s : F → Option β) : (ofSpec node s).NoCrossing :=
  fun t' _ ↦ AR.isNonCrossing_lines_iff.2 fun p _ p' _ _ h₂ hlt ↦ by
    have h : p' < (tierWord node s t').length := h₂.lt_left
    have := length_tierWord_le_one node s t'
    omega

/-- The lines of a realized word do not cross. -/
theorem noCrossing_ofWord (w : List (F → Option β)) : (ofWord node w).NoCrossing :=
  AR.NoCrossing.prod fun X hX ↦ by
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hX
    exact noCrossing_ofSpec node s

variable {node} in
/-- The lines of a realized word join a tier and the tier it hangs from. -/
theorem parentTier_of_link_ofWord {w : List (F → Option β)} {t' t : N ⊕ F} {p q : ℕ}
    (h : (ofWord node w).Link t' t p q) :
    parentTier node t = some t' ∨ parentTier node t' = some t := by
  obtain ⟨k, hk, -, -, h⟩ := (AR.link_prod_map (ofSpec node) t' t w p q).1 h
  exact (AR.link_fromRel.1 h).2.2.2

/-- The position on a tier of the token of the `k`th segment of a word. -/
def token (w : List (F → Option β)) (t : N ⊕ F) (k : ℕ) : ℕ :=
  AR.tierOffset (ofSpec node) t w k

/-- Spreading the node `a` from segment `m` onto segment `n` by a change of lines: the token of
segment `n` above `a` is delinked from its own `a` token and linked to that of segment `m`. -/
def linkNode (w : List (F → Option β)) (a : N) (m n : ℕ) : AR (Tiers N F β) :=
  ((ofWord node w).eraseLine (.inl (Order.pred a)) (.inl a)
      (token node w (.inl (Order.pred a)) n) (token node w (.inl a) n)).addLine
    (.inl (Order.pred a)) (.inl a) (token node w (.inl (Order.pred a)) n) (token node w (.inl a) m)

/-! ### Reading a representation back -/

section Reads

variable [Fintype N]

/-- The tokens a token is linked to on the tiers hanging from its own. -/
def children (X : AR (Tiers N F β)) (v : (N ⊕ F) × ℕ) : Finset ((N ⊕ F) × ℕ) :=
  Finset.univ.biUnion fun t ↦
    if parentTier node t = some v.1 then
      ((X.lines v.1 t).filter (·.1 = v.2)).image fun x ↦ (t, x.2)
    else ∅

/-- The tokens a token dominates through at most `d` descending lines. -/
def descendants (X : AR (Tiers N F β)) : ℕ → (N ⊕ F) × ℕ → Finset ((N ⊕ F) × ℕ)
  | 0, v => {v}
  | d + 1, v => insert v ((children node X v).biUnion (descendants X d))

/-- The `k`th slot of `X` reads `b` for the feature `f`: its root token dominates a token of `f`
with value `b`. -/
def Reads (X : AR (Tiers N F β)) (k : ℕ) (f : F) (b : β) : Prop :=
  ∃ q ∈ Finset.range (X.word (.inr f)).length,
    (Sum.inr f, q) ∈ descendants node X (Fintype.card N + 1) (.inl ⊥, k) ∧
      (X.word (.inr f))[q]? = some b

instance [DecidableEq β] (X : AR (Tiers N F β)) (k : ℕ) (f : F) (b : β) :
    Decidable (Reads node X k f b) := by
  unfold Reads
  infer_instance

variable {node} {w : List (F → Option β)} {a : N} {m n k : ℕ} {f : F} {b : β}

/-- Reading a realized word back gives its segments. -/
theorem reads_ofWord_iff :
    Reads node (ofWord node w) k f b ↔
      ∃ h : k < w.length, (node f).isSome ∧ w[k] f = some b := by
  -- TODO: by `AR.link_prod_map` every line lies inside one segment's primitive, so the tokens
  -- the `k`th root token dominates are those of segment `k`; induct on the depth of `node f`.
  sorry

/-- Spreading by a change of lines reads as spreading by a change of values. -/
theorem reads_linkNode_iff (hm : m < w.length) (hn : n < w.length) (ha : a ≠ ⊥)
    (hma : Bears node w[m] a) (hna : Order.pred a = ⊥ ∨ Bears node w[n] (Order.pred a)) :
    Reads node (linkNode node w a m n) k f b ↔
      Reads node (ofWord node (w.set n (spread node a w[m] w[n]))) k f b := by
  -- TODO: the lines of `linkNode` differ from those of `ofWord` only between the tiers of
  -- `Order.pred a` and `a` at segment `n`, where the token above `a` now has the `a` token of
  -- segment `m` as its only child; below it the tokens are those of segment `m`.
  sorry

/-- Spreading a node has no crossing lines exactly when no segment strictly between the two
bears the node. -/
theorem noCrossing_linkNode_iff (hm : m < w.length) (hn : n < w.length) (ha : a ≠ ⊥)
    (hma : Bears node w[m] a) (hna : Order.pred a = ⊥ ∨ Bears node w[n] (Order.pred a)) :
    (linkNode node w a m n).NoCrossing ↔
      ∀ k (hk : k < w.length), k ∈ Set.uIoo m n → ¬ Bears node w[k] a := by
  -- TODO: only the lines between the tiers of `Order.pred a` and `a` change. A segment `k`
  -- bearing `a` has a line there between its own tokens, which lie strictly between those of
  -- `m` and `n` on both tiers when `k` does, by monotonicity of `AR.tierOffset`; the new line
  -- runs from the token of `n` to the token of `m` and crosses it.
  sorry

end Reads

end Phonology.FeatureGeometry
