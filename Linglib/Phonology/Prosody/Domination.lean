/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Prosody.Foot
public import Linglib.Phonology.OptimalityTheory.Correspondence.Basic
public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Core.Data.RoseTree.Positions
public import Mathlib.Order.Antichain
public import Mathlib.Order.Cover
public import Mathlib.Order.Grade

/-!
# Constraints on prosodic domination

[selkirk-1996] decomposes the Strict Layer Hypothesis into four constraints on which prosodic
category may dominate which. Layeredness forbids a node from dominating a higher level and
Headedness requires every node above the syllable to dominate the next level down; Exhaustivity
forbids a node of a level from immediately dominating a node more than one level down, and
Nonrecursivity forbids it from dominating its own level. Each is a violation count on the
prosodic tree. The three stated of a node and its daughters count such pairs; Headedness, like
the Parse-into-`ℓ` of [ito-mester-2003], is an alignment of the positions of the tree under
dominance, each node of one family needing a partner in another below or above it.

Layeredness, counted on mothers and daughters, [holds of everything a node
dominates](##Prosody.layeredness_eq_zero_iff), and in a layered tree Nonrecursivity on mothers
and daughters is [the absence of recursion at any depth](##Prosody.noLevelRecursion_iff). A
tree [is strictly layered](##Prosody.isStrictlyLayered_iff) exactly when it violates none of
the four, and a tree satisfying Headedness
[has a node at every level below its root](##Prosody.exists_isSubtree_level_eq).

The constraints are facts about one map, from the nodes of a structure ordered by dominance to
the categories. Layeredness says that [the map is
antitone](##Prosody.layeredness_eq_zero_iff_antitone), and the Strict Layer Hypothesis that [it
grades the nodes](##Prosody.isStrictlyLayered_iff_covBy): a daughter is one category below its
mother and a node without daughters is of the lowest. Nothing in that reading asks the nodes to
form a tree.

## Implementation notes

The constraints are stated for trees over any linearly ordered categories and any marks, the
lowest category in the role of the syllable, so they apply to a tree with or without prominence
and to hierarchies with other categories than those of `Level`. Exhaustivity and Nonrecursivity
take the level of the dominating node as an argument, as [selkirk-1996] ranks them level by
level; `noRec` is the unindexed No-Recursion of
[ito-mester-2009]. Headedness reads "dominates" at any depth, so that a prosodic word whose
only foot lies inside a prosodic word it dominates satisfies it.

## References

* [selkirk-1996]
* [ito-mester-2003]
* [ito-mester-2009]
-/

@[expose] public section

namespace Prosody

open OptimalityTheory RoseTree

namespace Level

/-- A level is covered by the level one rank up. -/
theorem covBy_iff {a b : Level} : a ⋖ b ↔ a.toNat + 1 = b.toNat := by
  refine ⟨fun ⟨hlt, h⟩ ↦ ?_, fun h ↦ ⟨show a.toNat < b.toNat by omega, fun c hac hcb ↦ ?_⟩⟩
  · cases a <;> cases b <;> first
      | rfl
      | exact absurd hlt (by decide)
      | exact (h (c := ft) (by decide) (by decide)).elim
      | exact (h (c := om) (by decide) (by decide)).elim
      | exact (h (c := ph) (by decide) (by decide)).elim
  · have h₁ : a.toNat < c.toNat := hac
    have h₂ : c.toNat < b.toNat := hcb
    omega

instance : DecidableRel (α := Level) (· ⋖ ·) := fun _ _ ↦ decidable_of_iff _ covBy_iff.symm

theorem ft_covBy_om : ft ⋖ om := by decide

theorem om_covBy_ph : om ⋖ ph := by decide

theorem ph_covBy_iota : ph ⋖ iota := by decide

end Level

variable {L M : Type*} [LinearOrder L] {r : L → L → Prop} [DecidableRel r]
  {t s : RoseTree (Constituent L M)} {ℓ : L}

/-! ### Counting mothers and daughters -/

/-- The number of pairs of a node of a tree and a daughter of it whose levels stand in the
relation `r`. -/
def countDaughters (r : L → L → Prop) [DecidableRel r] : Constraint (RoseTree (Constituent L M)) :=
  fun t ↦ (t.localTrees.map fun e ↦ e.2.countP fun k ↦ r e.1.level k.level).sum

omit [LinearOrder L] in
theorem countDaughters_eq_zero_iff : countDaughters r t = 0 ↔
    ∀ s, IsSubtree s t → ∀ c ∈ s.children, ¬r s.value.level c.value.level := by
  have h : countDaughters r t = 0 ↔ t.Licensed fun a ks ↦ ∀ k ∈ ks, ¬r a.level k.level := by
    rw [countDaughters, List.sum_eq_zero_iff, licensed_iff_forall_mem_localTrees,
      List.forall_mem_map]
    exact forall₂_congr fun e _ ↦ by simp [List.countP_eq_zero]
  simp [h, Licensed]

/-! ### Layeredness and Nonrecursivity -/

/-- **Layeredness** ([selkirk-1996]): one violation for each node immediately dominating a node
of a higher level. -/
def layeredness : Constraint (RoseTree (Constituent L M)) := countDaughters (· < ·)

/-- **Nonrecursivity** with respect to the level `ℓ` ([selkirk-1996]): one violation for each
`ℓ`-node that an `ℓ`-node immediately dominates. -/
def nonrecursivity (ℓ : L) : Constraint (RoseTree (Constituent L M)) :=
  countDaughters fun a k ↦ a = ℓ ∧ k = ℓ

/-- **No-Recursion** ([ito-mester-2009]) counts the pairs of a node and a daughter sharing a
level, an element parsed into the same category twice. -/
def noRec : Constraint (RoseTree (Constituent L M)) := countDaughters (· = ·)

/-- A node dominates only nodes of its own level or below, at any depth, when no node
immediately dominates a higher level. -/
theorem layeredness_eq_zero_iff : layeredness t = 0 ↔
    ∀ s, IsSubtree s t → ∀ r, IsSubtree r s → r.value.level ≤ s.value.level := by
  rw [layeredness, countDaughters_eq_zero_iff]
  refine ⟨fun h s hs r hr ↦ ?_, fun h s hs c hc ↦ (h s hs c (.of_mem_children hc)).not_gt⟩
  induction hr with
  | refl => exact le_rfl
  | tail _ hbc ih =>
    exact (ih ((IsSubtree.of_mem_children hbc).trans hs)).trans (not_lt.1 (h _ hs _ hbc))

theorem nonrecursivity_eq_zero_iff : nonrecursivity ℓ t = 0 ↔ ∀ s, IsSubtree s t →
    s.value.level = ℓ → ∀ c ∈ s.children, c.value.level ≠ ℓ := by
  rw [nonrecursivity, countDaughters_eq_zero_iff]
  exact forall₂_congr fun s _ ↦ ⟨fun h hs c hc hcℓ ↦ h c hc ⟨hs, hcℓ⟩,
    fun h c hc ⟨hs, hcℓ⟩ ↦ h hs c hc hcℓ⟩

/-- No-Recursion is satisfied exactly when Nonrecursivity is at every level. -/
theorem noRec_eq_zero_iff : noRec t = 0 ↔ ∀ ℓ, nonrecursivity ℓ t = 0 := by
  simp only [noRec, countDaughters_eq_zero_iff, nonrecursivity_eq_zero_iff]
  exact ⟨fun h ℓ s hs hsℓ c hc hcℓ ↦ h s hs c hc (hsℓ.trans hcℓ.symm),
    fun h s hs c hc e ↦ h _ s hs rfl c hc e.symm⟩

/-! ### Maximal and minimal projections

The **projections** of a level `ℓ` ([ito-mester-2009]) are its extremal nodes under dominance.
The **maximal** ℓ-projections are the ℓ-nodes no ℓ-node dominates, and the **minimal** ones are
the ℓ-nodes dominating no ℓ-node. Since the root is the least position, these are the `Minimal`
and `Maximal` members of the ℓ-positions. That no ℓ-node dominates another at any depth says that
the ℓ-positions form an antichain, and it collapses the two. `nonrecursivity ℓ` counts only a
daughter, so `ω(f(ω))`, which recurses through an intervening foot, satisfies it while its
maximal and minimal ω-projections differ; that tree violates Layeredness, and
[in a layered tree the two agree](##Prosody.noLevelRecursion_iff). The intonational utterance υ
is the maximal ι-projection. -/

/-- The category of the node at a position of `t`. -/
def levelAt {t : RoseTree (Constituent L M)} (p : t.Positions) : L := p.subtree.value.level

/-- The positions of `t` at the level `ℓ`. -/
abbrev levelPositions (ℓ : L) (t : RoseTree (Constituent L M)) : Set GornAddress :=
  RoseTree.positionsWhere (fun s ↦ s.value.level = ℓ) t

/-- The maximal `ℓ`-projections of `t`, its topmost `ℓ`-nodes. -/
abbrev maximalProjections (ℓ : L) (t : RoseTree (Constituent L M)) : Set GornAddress :=
  {p | Minimal (· ∈ levelPositions ℓ t) p}

/-- The minimal `ℓ`-projections of `t`, its bottommost `ℓ`-nodes. -/
abbrev minimalProjections (ℓ : L) (t : RoseTree (Constituent L M)) : Set GornAddress :=
  {p | Maximal (· ∈ levelPositions ℓ t) p}

/-- No `ℓ`-node of `t` dominates another, at any depth. -/
abbrev NoLevelRecursion (ℓ : L) (t : RoseTree (Constituent L M)) : Prop :=
  IsAntichain (· ≤ ·) (levelPositions ℓ t)

instance (ℓ : L) (t : RoseTree (Constituent L M)) : Decidable (NoLevelRecursion ℓ t) :=
  decidable_of_iff (∀ p ∈ t.vertices, ∀ q ∈ t.vertices, (⟨p⟩ : GornAddress) ∈ levelPositions ℓ t →
      (⟨q⟩ : GornAddress) ∈ levelPositions ℓ t → p <+: q → p = q)
    ⟨fun h _ hp _ hq hne hle ↦ hne <| congrArg GornAddress.mk <| h _
        (RoseTree.mem_vertices.2 (Option.isSome_iff_exists.2 ⟨_, hp.choose_spec.1⟩)) _
        (RoseTree.mem_vertices.2 (Option.isSome_iff_exists.2 ⟨_, hq.choose_spec.1⟩)) hp hq hle,
      fun h _ _ _ _ hp hq hle ↦ congrArg GornAddress.toList (h.eq hp hq hle)⟩

omit [LinearOrder L] in
/-- **The absence of recursion collapses the projections**: where no `ℓ`-node dominates another,
every `ℓ`-node is at once topmost and bottommost. -/
theorem maximalProjections_eq_minimalProjections (h : NoLevelRecursion ℓ t) :
    maximalProjections ℓ t = minimalProjections ℓ t := by
  ext p
  exact h.minimal_mem_iff.trans h.maximal_mem_iff.symm

omit [LinearOrder L] in
/-- Where no `ℓ`-node dominates another, at most one `ℓ`-node dominates a given position: the
positions dominating it form a chain, which meets an antichain in at most one member. A tree
without recursion therefore stacks no more nodes over a terminal than there are levels. -/
theorem NoLevelRecursion.subsingleton_inter_Iic (h : NoLevelRecursion ℓ t) (q : GornAddress) :
    (levelPositions ℓ t ∩ Set.Iic q).Subsingleton :=
  subsingleton_of_isChain_of_isAntichain
    (fun _ hp _ hr _ ↦ List.prefix_or_prefix_of_prefix hp.2 hr.2) (h.subset Set.inter_subset_left)

/-- A tree in which no `ℓ`-node dominates another satisfies Nonrecursivity at `ℓ`. -/
theorem NoLevelRecursion.nonrecursivity_eq_zero (h : NoLevelRecursion ℓ t) :
    nonrecursivity ℓ t = 0 := by
  refine nonrecursivity_eq_zero_iff.2 fun s hs hsℓ c hc hcℓ ↦ ?_
  obtain ⟨p, hp⟩ := isSubtree_iff_exists_getElem?.1 hs
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hc
  have hq : t[p ++ [i]]? = some c := by simp [getElem?_append, hp, hi]
  have e := h.eq (a := ⟨p⟩) (b := ⟨p ++ [i]⟩) ⟨s, hp, hsℓ⟩ ⟨c, hq, hcℓ⟩ (List.prefix_append p [i])
  simpa using congrArg GornAddress.toList e

/-- **Nonrecursivity is local under Layeredness**: in a layered tree, no `ℓ`-node dominates
another at any depth exactly when none immediately dominates another, since every node between
two `ℓ`-nodes is itself of level `ℓ`. -/
theorem noLevelRecursion_iff (h : layeredness t = 0) :
    NoLevelRecursion ℓ t ↔ nonrecursivity ℓ t = 0 := by
  refine ⟨NoLevelRecursion.nonrecursivity_eq_zero,
    fun hn p ⟨s, hs, hsℓ⟩ q ⟨u, hu, huℓ⟩ hne hle ↦ ?_⟩
  obtain ⟨l, hl⟩ := hle
  rcases l with _ | ⟨i, l⟩
  · exact hne (GornAddress.ext (by simpa using hl))
  have hs : t[p.toList]? = some s := hs
  rw [Option.mem_def, ← hl, getElem?_append, hs, Option.bind_some,
    getElem?_cons_eq_some_iff] at hu
  obtain ⟨c, hc, hcu⟩ := hu
  have hst := isSubtree_iff_exists_getElem?.2 ⟨_, hs⟩
  have hcs : c ∈ s.children := List.mem_of_getElem? hc
  have hle := layeredness_eq_zero_iff.1 h
  exact nonrecursivity_eq_zero_iff.1 hn s hst hsℓ c hcs <| le_antisymm
    (hsℓ ▸ hle s hst c (.of_mem_children hcs))
    (huℓ ▸ hle c ((IsSubtree.of_mem_children hcs).trans hst) u
      (isSubtree_iff_exists_getElem?.2 ⟨_, hcu⟩))

/-- In a layered tree, No-Recursion is satisfied exactly when no node dominates another of its
level at any depth. -/
theorem noRec_eq_zero_iff_noLevelRecursion (h : layeredness t = 0) :
    noRec t = 0 ↔ ∀ ℓ, NoLevelRecursion ℓ t := by
  simp only [noRec_eq_zero_iff, noLevelRecursion_iff h]

/-! ### Exhaustivity -/

section Exhaustivity

variable [DecidableRel (α := L) (· ⋖ ·)]

/-- **Exhaustivity** with respect to the level `ℓ` ([selkirk-1996]): one violation for each node
more than one level down that an `ℓ`-node immediately dominates. -/
def exhaustivity (ℓ : L) : Constraint (RoseTree (Constituent L M)) :=
  countDaughters fun a k ↦ a = ℓ ∧ k < a ∧ ¬k ⋖ a

theorem exhaustivity_eq_zero_iff : exhaustivity ℓ t = 0 ↔ ∀ s, IsSubtree s t →
    s.value.level = ℓ → ∀ c ∈ s.children, c.value.level < ℓ → c.value.level ⋖ ℓ := by
  rw [exhaustivity, countDaughters_eq_zero_iff]
  refine forall₂_congr fun s _ ↦ ⟨fun h hs c hc hlt ↦ ?_, fun h c hc ⟨hs, hlt, hn⟩ ↦ ?_⟩
  · exact hs ▸ not_not.1 fun hn ↦ h c hc ⟨hs, hs ▸ hlt, hn⟩
  · exact hn (hs ▸ h hs c hc (hs ▸ hlt))

/-! ### Headedness and the Strict Layer Hypothesis -/

variable [OrderBot L]

/-- **Headedness** ([selkirk-1996]): one violation for each node above the lowest level that
dominates no node of the next level down. -/
def headedness : Constraint (RoseTree (Constituent L M)) :=
  fun t ↦ (Correspondence.ofRel (fun (a b : GornAddress × RoseTree (Constituent L M)) ↦
    a.1 ≤ b.1 ∧ b.2.value.level ⋖ a.2.value.level)
      (t.positionedSubtrees.filter fun x ↦ x.2.value.level ≠ ⊥).get
      t.positionedSubtrees.get).maxViol

theorem headedness_eq_zero_iff : headedness t = 0 ↔ ∀ s, IsSubtree s t →
    s.value.level ≠ ⊥ → ∃ r, IsSubtree r s ∧ r.value.level ⋖ s.value.level := by
  rw [headedness, Correspondence.maxViol_ofRel_get_eq_zero_iff]
  constructor
  · intro h s hs hne
    obtain ⟨p, hp⟩ := isSubtree_iff_exists_getElem?.1 hs
    obtain ⟨⟨q, r⟩, hq, hle, hcov⟩ := h (⟨p⟩, s)
      (List.mem_filter.2 ⟨mem_positionedSubtrees.2 hp, by simpa using hne⟩)
    exact ⟨r, (isSubtree_iff_exists_le_getElem? (p := ⟨p⟩) hp).2
      ⟨q, hle, mem_positionedSubtrees.1 hq⟩, hcov⟩
  · rintro h ⟨p, s⟩ hps
    obtain ⟨hmem, hne⟩ := List.mem_filter.1 hps
    have hp := mem_positionedSubtrees.1 hmem
    obtain ⟨r, hr, hcov⟩ := h s (isSubtree_iff_exists_getElem?.2 ⟨_, hp⟩) (by simpa using hne)
    obtain ⟨q, hle, hq⟩ := (isSubtree_iff_exists_le_getElem? hp).1 hr
    exact ⟨(q, r), mem_positionedSubtrees.2 hq, hle, hcov⟩

omit [DecidableRel (α := L) (· ⋖ ·)] in
/-- **Parse-into-`ℓ`** ([ito-mester-2003]): one violation for each terminal, a node of the lowest
level without daughters, that no `ℓ`-node dominates. -/
def parseInto (ℓ : L) : Constraint (RoseTree (Constituent L M)) :=
  fun t ↦ (Correspondence.ofRel (fun (a b : GornAddress × RoseTree (Constituent L M)) ↦ b.1 ≤ a.1)
    (t.positionedSubtrees.filter fun x ↦ x.2.value.level = ⊥ ∧ x.2.children = []).get
    (t.positionedSubtrees.filter fun x ↦ x.2.value.level = ℓ).get).maxViol

omit [DecidableRel (α := L) (· ⋖ ·)] in
theorem parseInto_eq_zero_iff : parseInto ℓ t = 0 ↔ ∀ (q : GornAddress) (s : _),
    t[q.toList]? = some s → s.value.level = ⊥ → s.children = [] →
      ∃ p ∈ levelPositions ℓ t, p ≤ q := by
  rw [parseInto, Correspondence.maxViol_ofRel_get_eq_zero_iff]
  constructor
  · intro h q s hq hb hc
    obtain ⟨⟨p, u⟩, hpu, hle⟩ := h (q, s)
      (List.mem_filter.2 ⟨mem_positionedSubtrees.2 hq, by simp [hb, hc]⟩)
    obtain ⟨hmem, hu⟩ := List.mem_filter.1 hpu
    exact ⟨p, ⟨u, mem_positionedSubtrees.1 hmem, by simpa using hu⟩, hle⟩
  · rintro h ⟨q, s⟩ hqs
    obtain ⟨hmem, hs⟩ := List.mem_filter.1 hqs
    have hs' : s.value.level = ⊥ ∧ s.children = [] := by simpa using hs
    obtain ⟨p, ⟨u, hu, huℓ⟩, hle⟩ := h q s (mem_positionedSubtrees.1 hmem) hs'.1 hs'.2
    exact ⟨(p, u), List.mem_filter.2 ⟨mem_positionedSubtrees.2 hu, by simpa using huℓ⟩, hle⟩

/-- **Headedness fills the hierarchy**: a tree satisfying Headedness has a node at every level
from its root down, so that an utterance of a single syllable is a syllable, a foot, a word and
a phrase at once ([selkirk-1996]). -/
theorem exists_isSubtree_level_eq [WellFoundedLT L] (h : headedness t = 0)
    (hℓ : ℓ ≤ t.value.level) : ∃ s, IsSubtree s t ∧ s.value.level = ℓ := by
  suffices H : ∀ a (s : RoseTree (Constituent L M)), s.value.level = a → IsSubtree s t → ℓ ≤ a →
      ∃ u, IsSubtree u s ∧ u.value.level = ℓ from H _ t rfl (.refl t) hℓ
  intro a
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    intro s ha hs hle
    subst ha
    rcases hle.eq_or_lt with e | hlt
    · exact ⟨s, .refl s, e.symm⟩
    obtain ⟨u, hu, hcov⟩ := headedness_eq_zero_iff.1 h s hs (bot_le.trans_lt hlt).ne'
    obtain ⟨v, hv, e⟩ := ih _ hcov.lt u rfl (hu.trans hs) (not_lt.1 fun h' ↦ hcov.2 h' hlt)
    exact ⟨v, hv.trans hu, e⟩

/-- A tree is **strictly layered** when every node above the lowest level has daughters and
every daughter is of the next level down, the Strict Layer Hypothesis that [selkirk-1996]
decomposes. -/
def IsStrictlyLayered (t : RoseTree (Constituent L M)) : Prop :=
  t.Licensed fun a ks ↦ (a.level ≠ ⊥ → ks ≠ []) ∧ ∀ k ∈ ks, k.level ⋖ a.level

instance (t : RoseTree (Constituent L M)) : Decidable (IsStrictlyLayered t) :=
  inferInstanceAs (Decidable (t.Licensed _))

omit [DecidableRel (α := L) (· ⋖ ·)] in
theorem isStrictlyLayered_iff_forall : IsStrictlyLayered t ↔ ∀ s, IsSubtree s t →
    (s.value.level ≠ ⊥ → s.children ≠ []) ∧ ∀ c ∈ s.children, c.value.level ⋖ s.value.level := by
  simp [IsStrictlyLayered, Licensed]

/-- **The Strict Layer Hypothesis is the four constraints together** ([selkirk-1996]): a tree is
strictly layered exactly when it violates none of Layeredness, Headedness, Exhaustivity and
Nonrecursivity. -/
theorem isStrictlyLayered_iff : IsStrictlyLayered t ↔ layeredness t = 0 ∧ headedness t = 0 ∧
    ∀ ℓ, exhaustivity ℓ t = 0 ∧ nonrecursivity ℓ t = 0 := by
  rw [isStrictlyLayered_iff_forall]
  refine ⟨fun H ↦ ⟨?_, ?_, fun ℓ ↦ ⟨?_, ?_⟩⟩, fun ⟨hl, hh, he⟩ s hs ↦ ⟨fun hne hnil ↦ ?_, ?_⟩⟩
  · exact countDaughters_eq_zero_iff.2 fun s hs c hc ↦ ((H s hs).2 c hc).le.not_gt
  · refine headedness_eq_zero_iff.2 fun s hs hne ↦ ?_
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ ((H s hs).1 hne)
    exact ⟨c, .of_mem_children hc, (H s hs).2 c hc⟩
  · exact exhaustivity_eq_zero_iff.2 fun s hs hsℓ c hc _ ↦ hsℓ ▸ (H s hs).2 c hc
  · exact nonrecursivity_eq_zero_iff.2 fun s hs hsℓ c hc ↦ (hsℓ ▸ (H s hs).2 c hc).ne
  · obtain ⟨u, hu, hcov⟩ := headedness_eq_zero_iff.1 hh s hs hne
    obtain ⟨a, cs⟩ := s
    obtain rfl : cs = [] := hnil
    obtain rfl | ⟨c, hc, -⟩ := isSubtree_node_iff.1 hu
    · exact hcov.lt.ne rfl
    · simp at hc
  · intro c hc
    exact exhaustivity_eq_zero_iff.1 (he _).1 s hs rfl c hc <| lt_of_le_of_ne
      (layeredness_eq_zero_iff.1 hl s hs c (.of_mem_children hc))
      (nonrecursivity_eq_zero_iff.1 (he _).2 s hs rfl c hc)

/-! ### The hierarchy grades dominance

The positions of a tree are ordered by dominance, the root least, and `levelAt` sends each to
its category. Selkirk's constraints are order-theoretic properties of this map. -/

omit [DecidableRel (α := L) (· ⋖ ·)] [OrderBot L] in
/-- **Layeredness says the category map is antitone**: a position dominated by another is of
its category or below. -/
theorem layeredness_eq_zero_iff_antitone : layeredness t = 0 ↔ Antitone (levelAt (t := t)) := by
  rw [layeredness_eq_zero_iff]
  refine ⟨fun h p q hpq ↦ h _ p.isSubtree_subtree_self _
    (Positions.isSubtree_subtree.2 ⟨q, hpq, rfl⟩), fun h s hs r hr ↦ ?_⟩
  obtain ⟨p, rfl⟩ := Positions.exists_subtree_eq hs
  obtain ⟨q, hpq, rfl⟩ := Positions.isSubtree_subtree.1 hr
  exact h hpq

omit [DecidableRel (α := L) (· ⋖ ·)] in
/-- **The Strict Layer Hypothesis says the hierarchy grades dominance**: a tree is strictly
layered exactly when each daughter is one category below its mother and each position without
daughters is of the lowest category. -/
theorem isStrictlyLayered_iff_covBy : IsStrictlyLayered t ↔
    (∀ ⦃p q : t.Positions⦄, p ⋖ q → levelAt q ⋖ levelAt p) ∧
      ∀ ⦃p : t.Positions⦄, IsMax p → levelAt p = ⊥ := by
  rw [isStrictlyLayered_iff_forall]
  constructor
  · refine fun H ↦ ⟨fun p q hpq ↦ (H _ p.isSubtree_subtree_self).2 _
      (Positions.mem_children_subtree.2 ⟨q, hpq, rfl⟩), fun p hp ↦ ?_⟩
    by_contra hne
    exact (H _ p.isSubtree_subtree_self).1 hne (Positions.isMax_iff.1 hp)
  · rintro ⟨hcov, hmax⟩ s hs
    obtain ⟨p, rfl⟩ := Positions.exists_subtree_eq hs
    refine ⟨fun hne hnil ↦ hne (hmax (Positions.isMax_iff.2 hnil)), fun c hc ↦ ?_⟩
    obtain ⟨q, hpq, rfl⟩ := Positions.mem_children_subtree.1 hc
    exact hcov hpq

/-- In a strictly layered tree a dominated position is of a strictly lower category. -/
theorem IsStrictlyLayered.strictAnti_levelAt (h : IsStrictlyLayered t) :
    StrictAnti (levelAt (t := t)) := fun _ _ hpq ↦
  ((isStrictlyLayered_iff_covBy.1 h).1
      (Order.pred_covBy_of_not_isMin (not_isMin_of_lt hpq))).lt.trans_le
    (layeredness_eq_zero_iff_antitone.1 (isStrictlyLayered_iff.1 h).1 (Order.le_pred_of_lt hpq))

/-- The positions of a strictly layered tree are graded by the hierarchy, the root highest and
the positions without daughters lowest. -/
abbrev IsStrictlyLayered.gradeMaxOrder (h : IsStrictlyLayered t) :
    GradeMaxOrder Lᵒᵈ t.Positions where
  grade p := OrderDual.toDual (levelAt p)
  grade_strictMono _ _ hpq := OrderDual.toDual_lt_toDual.2 (h.strictAnti_levelAt hpq)
  covBy_grade _ _ hpq := ((isStrictlyLayered_iff_covBy.1 h).1 hpq).toDual
  isMax_grade _ hp := (isStrictlyLayered_iff_covBy.1 h).2 hp ▸ isMin_bot.toDual

end Exhaustivity

/-! ### Well-formed constituents -/

section IsConstituent

variable {M : Type*} {t c : RoseTree (Constituent Level M)} {ℓ : Level}

/-- A well-formed constituent satisfies Layeredness. -/
theorem IsConstituent.layeredness_eq_zero (h : IsConstituent ℓ t) : layeredness t = 0 := by
  rw [layeredness, countDaughters_eq_zero_iff]
  exact fun s hs c hc ↦ not_lt.2 <| (h.2 s hs).le _
    (List.mem_map.2 ⟨c.value, List.mem_map_of_mem hc, rfl⟩)

theorem IsConstituent.of_mem_children (h : IsConstituent ℓ t) (hc : c ∈ t.children) :
    IsConstituent c.value.level c :=
  ⟨rfl, h.2.of_isSubtree (.of_mem_children hc)⟩

/-- The daughters of a constituent that satisfies Exhaustivity and Nonrecursivity at its own
level are of the next level down. -/
theorem IsConstituent.level_covBy_of_mem_children (h : IsConstituent ℓ t)
    (he : exhaustivity ℓ t = 0) (hn : nonrecursivity ℓ t = 0) (hc : c ∈ t.children) :
    c.value.level ⋖ ℓ :=
  exhaustivity_eq_zero_iff.1 he t (.refl t) h.1 c hc <| lt_of_le_of_ne
    (h.1 ▸ layeredness_eq_zero_iff.1 h.layeredness_eq_zero t (.refl t) c (.of_mem_children hc))
    (nonrecursivity_eq_zero_iff.1 hn t (.refl t) h.1 c hc)

end IsConstituent

end Prosody
