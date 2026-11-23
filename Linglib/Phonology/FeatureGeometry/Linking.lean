module

public import Linglib.Phonology.FeatureGeometry
public import Linglib.Phonology.Autosegmental.TierTree
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum

/-!
# Feature geometry as an autosegmental representation

A word of segments in a feature geometry is an autosegmental representation along a tree of
tiers, `tiers node`: the timing slots at the root, the tier of the root node under them, each
class node under its parent and each feature under its node. For a specification `s`, the
representation `ofSpec node s` has a slot, a token of the root node, a token on the tier of each
node `s` bears and a token on the tier of each placed feature `s` specifies, labelled with its
value; each token has a line to the token of the tier its own hangs from. `ofWord node w`
concatenates these, and its lines do not cross (`noCrossing_ofWord`). Reading it back gives its
segments (`reads_ofWord_iff`).

Spreading is a change of lines. `linkNode node w a m n` spreads the node `a` from segment `m` onto
segment `n`, and `linkFeature node w f m n` a single feature, by `Autosegmental.AR.spreadTier`:
the token of segment `n` above is delinked from its own token and linked to that of segment
`m`, which the two segments then share. The result reads as the word with `spread node a`
applied at `n` (`reads_linkNode_iff`), or with the one feature copied
(`reads_linkFeature_iff`). Spreading a node crosses no line exactly when no segment strictly
between the two has the node (`noCrossing_linkNode_iff`). Spreading the root node shares a whole
segment between two slots, and every segment between blocks it.

## Implementation notes

Every segment has a slot and a root node, whether or not it specifies a placed feature. An
unplaced feature has an empty tier, hanging from the slots. The position of the token of
segment `k` on a tier is the number of earlier segments with a token there,
`Autosegmental.AR.tierOffset`.

## TODO

* The proofs of `reads_ofSpec_iff`, `reads_linkNode_iff`, `reads_linkFeature_iff` and
  `noCrossing_linkNode_iff`, which are checked on small geometries; the last is
  `Autosegmental.AR.noCrossing_spreadTier_iff` at the tier of the node.
* Contour segments, with two tokens of one feature under one node token, and geminates, with one
  root node under two slots, as representations that no word of specifications realizes.

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

/-- The tiers of a geometry are the timing slots, the class nodes and the features; a slot and a
node token carry no label, and a feature token carries its value. -/
abbrev Tiers (N F : Type*) (β : Type u) : Option (N ⊕ F) → Type u
  | some (.inr _) => β
  | _ => PUnit

instance [DecidableEq β] : ∀ t, DecidableEq (Tiers N F β t)
  | none => inferInstanceAs (DecidableEq PUnit)
  | some (.inl _) => inferInstanceAs (DecidableEq PUnit)
  | some (.inr _) => inferInstanceAs (DecidableEq β)

variable [PartialOrder N] [OrderBot N] [PredOrder N] [DecidableEq N] (node : F → Option N)

/-- The tier a tier hangs from: the root node from the slots, another class node from its
parent, a feature from its node; the slots are their own. -/
def tierParent : Option (N ⊕ F) → Option (N ⊕ F)
  | none => none
  | some (.inl a) => if a = ⊥ then none else some (.inl (Order.pred a))
  | some (.inr f) => (node f).map .inl

theorem iterate_tierParent_node (n : ℕ) (a : N) (h : Order.pred^[n] a = ⊥) :
    (tierParent node)^[n + 1] (some (.inl a)) = none := by
  induction n generalizing a with
  | zero =>
    have ha : a = ⊥ := h
    simp [tierParent, ha]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    by_cases ha : a = ⊥
    · subst ha
      simp only [tierParent, ite_true]
      exact Function.iterate_fixed rfl _
    · simp only [tierParent, ha, ite_false]
      exact ih _ (by rwa [Function.iterate_succ_apply] at h)

/-- The tree of tiers of a geometry, with the timing slots at its root. -/
def tiers [IsPredArchimedean N] : ParentTree (Option (N ⊕ F)) where
  parent := tierParent node
  root := none
  parent_root := rfl
  exists_iterate_eq_root t := by
    rcases t with _ | a | f
    · exact ⟨0, rfl⟩
    · obtain ⟨n, hn⟩ := (bot_le (a := a)).exists_pred_iterate
      exact ⟨n + 1, iterate_tierParent_node node n a hn⟩
    · rcases h : node f with _ | a
      · exact ⟨1, by simp [tierParent, h]⟩
      · obtain ⟨n, hn⟩ := (bot_le (a := a)).exists_pred_iterate
        refine ⟨n + 2, ?_⟩
        rw [Function.iterate_succ_apply]
        simp only [tierParent, h, Option.map_some]
        exact iterate_tierParent_node node n a hn

variable [DecidableLE N] [Fintype F] [DecidableEq F]

/-- The tokens of a specification on each tier: a slot, a root node, a token for each node it
bears, and its value for each placed feature it specifies. -/
def tierWord (s : F → Option β) : ∀ t, List (Tiers N F β t)
  | none => [PUnit.unit]
  | some (.inl a) => if a = ⊥ ∨ Bears node s a then [PUnit.unit] else []
  | some (.inr f) => if (node f).isSome then (s f).toList else []

omit [PredOrder N] [DecidableEq F] in
theorem length_tierWord_le_one (s : F → Option β) (t : Option (N ⊕ F)) :
    (tierWord node s t).length ≤ 1 := by
  rcases t with _ | a | f
  · simp [tierWord]
  · simp only [tierWord]
    split_ifs <;> simp
  · simp only [tierWord]
    split_ifs
    · cases s f <;> simp
    · simp

/-- The representation of one specification: its tokens, each linked to the token of the tier
its own hangs from. -/
def ofSpec (s : F → Option β) : AR (Tiers N F β) :=
  AR.fromRel (tierWord node s) fun t' t _ _ ↦ tierParent node t = t' ∧ t ≠ none

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

variable [IsPredArchimedean N]

/-- Spreading the node `a` from segment `m` onto segment `n` by a change of lines. -/
def linkNode (w : List (F → Option β)) (a : N) (m n : ℕ) : AR (Tiers N F β) :=
  AR.spreadTier (tiers node) (ofSpec node) w (some (.inl a)) m n

/-- Spreading the feature `f` from segment `m` onto segment `n` by a change of lines. -/
def linkFeature (w : List (F → Option β)) (f : F) (m n : ℕ) : AR (Tiers N F β) :=
  AR.spreadTier (tiers node) (ofSpec node) w (some (.inr f)) m n

variable [Fintype N] {node} {w : List (F → Option β)} {s : F → Option β} {a : N} {m n k : ℕ}
  {f g : F} {b : β}

theorem reads_ofSpec_iff :
    (ofSpec node s).Reads (tiers node) 0 (some (.inr f)) b ↔ (node f).isSome ∧ s f = some b := by
  -- TODO: a specified placed feature has a token, and so has each node from its own up to the
  -- root, by `Bears.of_le`; the lines between them descend from the slot. Induct on the
  -- number of steps from the node of `f` to the root.
  sorry

/-- Reading a realized word back gives its segments. -/
theorem reads_ofWord_iff :
    (ofWord node w).Reads (tiers node) k (some (.inr f)) b ↔
      ∃ h : k < w.length, (node f).isSome ∧ w[k] f = some b :=
  (AR.reads_prod_map (tiers node) (ofSpec node) fun _ ↦ rfl).trans
    (exists_congr fun _ ↦ reads_ofSpec_iff)

/-- Spreading a node by a change of lines reads as spreading it by a change of values. -/
theorem reads_linkNode_iff (hm : m < w.length) (hn : n < w.length)
    (hma : a = ⊥ ∨ Bears node w[m] a)
    (hna : a = ⊥ ∨ Order.pred a = ⊥ ∨ Bears node w[n] (Order.pred a)) :
    (linkNode node w a m n).Reads (tiers node) k (some (.inr f)) b ↔
      (ofWord node (w.set n (spread node a w[m] w[n]))).Reads (tiers node) k
        (some (.inr f)) b := by
  -- TODO: the lines of `linkNode` differ from those of `ofWord` only between the tier of `a`
  -- and the tier above it at segment `n`, whose token there now has the `a` token of segment
  -- `m` as its only child on that tier; below it the tokens are those of segment `m`.
  sorry

/-- Spreading a feature by a change of lines reads as copying its value. -/
theorem reads_linkFeature_iff (hm : m < w.length) (hn : n < w.length)
    (hmg : (w[m] g).isSome) (hng : ∀ c ∈ node g, c = ⊥ ∨ Bears node w[n] c) :
    (linkFeature node w g m n).Reads (tiers node) k (some (.inr f)) b ↔
      (ofWord node (w.set n (Function.update w[n] g (w[m] g)))).Reads (tiers node) k
        (some (.inr f)) b := by
  -- TODO: as `reads_linkNode_iff`, at the tier of the feature.
  sorry

/-- Spreading a node crosses no line exactly when no segment strictly between the two has the
node. -/
theorem noCrossing_linkNode_iff (hm : m < w.length) (hn : n < w.length)
    (hma : a = ⊥ ∨ Bears node w[m] a)
    (hna : a = ⊥ ∨ Order.pred a = ⊥ ∨ Bears node w[n] (Order.pred a)) :
    (linkNode node w a m n).NoCrossing ↔
      ∀ k (hk : k < w.length), k ∈ Set.uIoo m n → ¬ (a = ⊥ ∨ Bears node w[k] a) := by
  -- TODO: `AR.noCrossing_spreadTier_iff` at the tier of `a`, whose primitives have a line to
  -- the tier above exactly when the segment has the node.
  sorry

end Phonology.FeatureGeometry
