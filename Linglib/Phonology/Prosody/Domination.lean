/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Prosody.Foot
public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Core.Data.RoseTree.Positions
public import Mathlib.Order.Antichain
public import Mathlib.Order.Cover

/-!
# Constraints on prosodic domination

[selkirk-1996] decomposes the Strict Layer Hypothesis into four constraints on which prosodic
category may dominate which. Layeredness forbids a node from dominating a higher level and
Headedness requires every node above the syllable to dominate the next level down; Exhaustivity
forbids a node of a level from immediately dominating a node more than one level down, and
Nonrecursivity forbids it from dominating its own level. Each is a violation count on the
prosodic tree. Layeredness, counted on mothers and daughters, [holds of everything a node
dominates](##Prosody.layeredness_eq_zero_iff), and in a layered tree Nonrecursivity on mothers
and daughters is [the absence of recursion at any depth](##Prosody.noLevelRecursion_iff). A
tree [is strictly layered](##Prosody.isStrictlyLayered_iff) exactly when it violates none of
the four, and a tree satisfying Headedness
[has a node at every level below its root](##Prosody.exists_isSubtree_level_eq).

## Implementation notes

Exhaustivity and Nonrecursivity take the level of the dominating node as an argument, as
[selkirk-1996] ranks them level by level; `noRec` is the unindexed No-Recursion of
[ito-mester-2009]. Headedness reads "dominates" at any depth, so that a prosodic word whose
only foot lies inside a prosodic word it dominates satisfies it.

## References

* [selkirk-1996]
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

theorem syl_le (a : Level) : syl ≤ a := by cases a <;> decide

theorem ft_covBy_om : ft ⋖ om := by decide

theorem om_covBy_ph : om ⋖ ph := by decide

theorem ph_covBy_iota : ph ⋖ iota := by decide

end Level

variable {r : Level → Level → Prop} [DecidableRel r] {t s : Tree} {ℓ : Level}

/-! ### Counting mothers and daughters -/

/-- The number of pairs of a node of a tree and a daughter of it whose levels stand in the
relation `r`. -/
def countDaughters (r : Level → Level → Prop) [DecidableRel r] : Constraint Tree := fun t ↦
  (t.localTrees.map fun e ↦ e.2.countP fun k ↦ r e.1.level k.level).sum

theorem countDaughters_eq_zero_iff : countDaughters r t = 0 ↔
    ∀ s, IsSubtree s t → ∀ c ∈ s.children, ¬r s.value.level c.value.level := by
  have h : countDaughters r t = 0 ↔ t.Licensed fun a ks ↦ ∀ k ∈ ks, ¬r a.level k.level := by
    rw [countDaughters, List.sum_eq_zero_iff, licensed_iff_forall_mem_localTrees,
      List.forall_mem_map]
    exact forall₂_congr fun e _ ↦ by simp [List.countP_eq_zero]
  simp [h, Licensed]

/-! ### The four constraints -/

/-- **Layeredness** ([selkirk-1996]): one violation for each node immediately dominating a node
of a higher level. -/
def layeredness : Constraint Tree := countDaughters (· < ·)

/-- **Headedness** ([selkirk-1996]): one violation for each node above the syllable that
dominates no node of the next level down. -/
def headedness : Constraint Tree := fun t ↦ t.subtrees.countP fun s ↦
  s.value.level ≠ .syl ∧ ∀ r ∈ s.subtrees, ¬r.value.level ⋖ s.value.level

/-- **Exhaustivity** with respect to the level `ℓ` ([selkirk-1996]): one violation for each node
more than one level down that an `ℓ`-node immediately dominates. -/
def exhaustivity (ℓ : Level) : Constraint Tree :=
  countDaughters fun a k ↦ a = ℓ ∧ k < a ∧ ¬k ⋖ a

/-- **Nonrecursivity** with respect to the level `ℓ` ([selkirk-1996]): one violation for each
`ℓ`-node that an `ℓ`-node immediately dominates. -/
def nonrecursivity (ℓ : Level) : Constraint Tree := countDaughters fun a k ↦ a = ℓ ∧ k = ℓ

/-- **No-Recursion** ([ito-mester-2009]) counts the pairs of a node and a daughter sharing a
level, an element parsed into the same category twice. -/
def noRec : Constraint Tree := countDaughters (· = ·)

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

theorem headedness_eq_zero_iff : headedness t = 0 ↔ ∀ s, IsSubtree s t →
    s.value.level ≠ .syl → ∃ r, IsSubtree r s ∧ r.value.level ⋖ s.value.level := by
  simp [headedness, mem_subtrees]

theorem exhaustivity_eq_zero_iff : exhaustivity ℓ t = 0 ↔ ∀ s, IsSubtree s t →
    s.value.level = ℓ → ∀ c ∈ s.children, c.value.level < ℓ → c.value.level ⋖ ℓ := by
  rw [exhaustivity, countDaughters_eq_zero_iff]
  refine forall₂_congr fun s _ ↦ ⟨fun h hs c hc hlt ↦ ?_, fun h c hc ⟨hs, hlt, hn⟩ ↦ ?_⟩
  · exact hs ▸ not_not.1 fun hn ↦ h c hc ⟨hs, hs ▸ hlt, hn⟩
  · exact hn (hs ▸ h hs c hc (hs ▸ hlt))

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

/-- A well-formed constituent satisfies Layeredness. -/
theorem IsConstituent.layeredness_eq_zero (h : IsConstituent ℓ t) : layeredness t = 0 := by
  rw [layeredness, countDaughters_eq_zero_iff]
  intro s hs c hc
  have hR := h.2 s hs
  have hk : c.value ∈ s.children.map value := List.mem_map_of_mem hc
  refine not_lt.2 ?_
  generalize s.value = a at hR
  cases a with
  | syl => simp [Constituent.Licenses] at hR; simp [hR] at hk
  | ft => rw [hR.2 _ hk]; exact Level.syl_le _
  | om => exact hR _ hk
  | ph => exact hR _ hk
  | iota => exact hR _ hk

theorem IsConstituent.of_mem_children {c : Tree} (h : IsConstituent ℓ t) (hc : c ∈ t.children) :
    IsConstituent c.value.level c :=
  ⟨rfl, h.2.of_isSubtree (.of_mem_children hc)⟩

/-- The daughters of a constituent that satisfies Exhaustivity and Nonrecursivity at its own
level are of the next level down. -/
theorem IsConstituent.level_covBy_of_mem_children {c : Tree} (h : IsConstituent ℓ t)
    (he : exhaustivity ℓ t = 0) (hn : nonrecursivity ℓ t = 0) (hc : c ∈ t.children) :
    c.value.level ⋖ ℓ :=
  exhaustivity_eq_zero_iff.1 he t (.refl t) h.1 c hc <| lt_of_le_of_ne
    (h.1 ▸ layeredness_eq_zero_iff.1 h.layeredness_eq_zero t (.refl t) c (.of_mem_children hc))
    (nonrecursivity_eq_zero_iff.1 hn t (.refl t) h.1 c hc)

/-- **Headedness fills the hierarchy**: a tree satisfying Headedness has a node at every level
from its root down, so that an utterance of a single syllable is a syllable, a foot, a word and
a phrase at once ([selkirk-1996]). -/
theorem exists_isSubtree_level_eq (h : headedness t = 0) (hℓ : ℓ ≤ t.value.level) :
    ∃ s, IsSubtree s t ∧ s.value.level = ℓ := by
  suffices H : ∀ n (s : Tree), s.value.level.toNat = n → IsSubtree s t → ℓ ≤ s.value.level →
      ∃ u, IsSubtree u s ∧ u.value.level = ℓ by
    exact H _ t rfl (.refl t) hℓ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hn hs hle
    rcases hle.eq_or_lt with e | hlt
    · exact ⟨s, .refl s, e.symm⟩
    have hne : s.value.level ≠ .syl := fun e ↦ (Level.syl_le ℓ).not_gt (e ▸ hlt)
    obtain ⟨u, hu, hcov⟩ := headedness_eq_zero_iff.1 h s hs hne
    obtain ⟨v, hv, e⟩ := ih _ (hn ▸ hcov.lt) u rfl (hu.trans hs)
      (not_lt.1 fun h' ↦ hcov.2 h' hlt)
    exact ⟨v, hv.trans hu, e⟩

/-! ### The Strict Layer Hypothesis -/

/-- A tree is **strictly layered** when every node above the syllable has daughters and every
daughter is of the next level down, the Strict Layer Hypothesis that [selkirk-1996] decomposes. -/
def IsStrictlyLayered (t : Tree) : Prop :=
  t.Licensed fun a ks ↦ (a.level ≠ .syl → ks ≠ []) ∧ ∀ k ∈ ks, k.level ⋖ a.level

instance (t : Tree) : Decidable (IsStrictlyLayered t) :=
  inferInstanceAs (Decidable (t.Licensed _))

theorem isStrictlyLayered_iff_forall : IsStrictlyLayered t ↔ ∀ s, IsSubtree s t →
    (s.value.level ≠ .syl → s.children ≠ []) ∧ ∀ c ∈ s.children, c.value.level ⋖ s.value.level := by
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

/-- The positions of `t` at the level `ℓ`. -/
abbrev levelPositions (ℓ : Level) (t : Tree) : Set GornAddress :=
  RoseTree.positionsWhere (fun s ↦ s.value.level = ℓ) t

/-- The maximal `ℓ`-projections of `t`, its topmost `ℓ`-nodes. -/
abbrev maximalProjections (ℓ : Level) (t : Tree) : Set GornAddress :=
  {p | Minimal (· ∈ levelPositions ℓ t) p}

/-- The minimal `ℓ`-projections of `t`, its bottommost `ℓ`-nodes. -/
abbrev minimalProjections (ℓ : Level) (t : Tree) : Set GornAddress :=
  {p | Maximal (· ∈ levelPositions ℓ t) p}

/-- No `ℓ`-node of `t` dominates another, at any depth. -/
abbrev NoLevelRecursion (ℓ : Level) (t : Tree) : Prop :=
  IsAntichain (· ≤ ·) (levelPositions ℓ t)

instance (ℓ : Level) (t : Tree) : Decidable (NoLevelRecursion ℓ t) :=
  decidable_of_iff (∀ p ∈ t.vertices, ∀ q ∈ t.vertices, (⟨p⟩ : GornAddress) ∈ levelPositions ℓ t →
      (⟨q⟩ : GornAddress) ∈ levelPositions ℓ t → p <+: q → p = q)
    ⟨fun h _ hp _ hq hne hle ↦ hne <| congrArg GornAddress.mk <| h _
        (RoseTree.mem_vertices.2 (Option.isSome_iff_exists.2 ⟨_, hp.choose_spec.1⟩)) _
        (RoseTree.mem_vertices.2 (Option.isSome_iff_exists.2 ⟨_, hq.choose_spec.1⟩)) hp hq hle,
      fun h _ _ _ _ hp hq hle ↦ congrArg GornAddress.toList (h.eq hp hq hle)⟩

/-- **The absence of recursion collapses the projections**: where no `ℓ`-node dominates another,
every `ℓ`-node is at once topmost and bottommost. -/
theorem maximalProjections_eq_minimalProjections (h : NoLevelRecursion ℓ t) :
    maximalProjections ℓ t = minimalProjections ℓ t := by
  ext p
  exact h.minimal_mem_iff.trans h.maximal_mem_iff.symm

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

end Prosody
