/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.Positions
public import Mathlib.Order.Atoms
public import Linglib.Syntax.Command.Closeness
public import Linglib.Syntax.Command.RoseTree
public import Linglib.Syntax.Projection.GornAddress
public import Linglib.Syntax.Minimalist.SyntacticObject.Term

/-!
# Positions of planar syntactic objects

The positions of a planar syntactic object, the paths to its vertices, form a rooted tree
(`RoseTree.Positions`). Each carries a term, the object at that address: the
terms at the covers of a position are the terms its term immediately contains, and the terms at
the positions below it are the terms its term contains, so c-command by a term occurring once is
c-command from its position. Which daughter heads a position is not part of the object but of a
head function (`SyntacticObject/Projection.lean`).

## Main definitions

* `PlanarSyntacticObject.planarTermAt`, `PlanarSyntacticObject.termAt`: the planar object and the
  term at a position.
* `PlanarSyntacticObject.above`: the branching positions
  of a planar object, and the generators above a position, its closeness key.

## Main statements

* `PlanarSyntacticObject.terms_eq_map_termAt`: the terms are the terms at the positions.
* `PlanarSyntacticObject.immediatelyContains_termAt`,
  `PlanarSyntacticObject.containsOrEq_termAt`: terms contain one another as their positions
  dominate one another.
* `PlanarSyntacticObject.exists_cCommands_termAt_of_cCommands`,
  `PlanarSyntacticObject.cCommands_termAt_of_cCommands`: c-command between terms is witnessed by
  c-command between occurrences, and conversely when sister terms are distinct: Collins and
  Stabler's theorem relating c-command between objects to c-command between occurrences.
* `PlanarSyntacticObject.isBranching_of_not_isMax`: a position that is not a leaf branches.
* `PlanarSyntacticObject.above_branching_lt_iff`: closeness under the branching positions is
  asymmetric c-command.

## References

* [collins-stabler-2016]
-/

@[expose] public section

namespace Minimalist

open RoseTree SyntacticObject PhraseStructure

variable {α : Type}

/-! ### Terms at positions -/

namespace PlanarSyntacticObject

open RoseTree SyntacticObject

variable {t : PlanarSyntacticObject α} {p : t.toRoseTree.Positions}
    {y : SyntacticObject α}

theorem isSome_subAt? (p : t.toRoseTree.Positions) : (t.subAt? p.val.toList).isSome := by
  have h := p.getElem?_eq
  rw [getElem?_toRoseTree] at h
  cases hs : t.subAt? p.val.toList with
  | none => rw [hs] at h; cases h
  | some x => rfl

variable (t) in
/-- The planar object at a position, with the order of daughters it has in `t`. -/
def planarTermAt (p : t.toRoseTree.Positions) : PlanarSyntacticObject α :=
  (t.subAt? p.val.toList).get (isSome_subAt? p)

/-- The subtree at a position is the tree of the planar object there. -/
@[simp] theorem toRoseTree_planarTermAt : (t.planarTermAt p).toRoseTree = p.subtree := by
  have h := p.getElem?_eq
  rw [getElem?_toRoseTree, ← Option.some_get (isSome_subAt? p), Option.map_some] at h
  exact Option.some.inj h

variable (t) in
/-- The term of `t` at a position. -/
def termAt (p : t.toRoseTree.Positions) : SyntacticObject α :=
  (t.planarTermAt p).toSyntacticObject

@[simp] theorem toSyntacticObject_planarTermAt :
    (t.planarTermAt p).toSyntacticObject = t.termAt p := rfl

@[simp] theorem toUnorderedTree_termAt : (t.termAt p).toUnorderedTree =
    UnorderedTree.mk p.subtree := by
  rw [termAt, toUnorderedTree_toSyntacticObject, toRoseTree_planarTermAt]

@[simp] theorem termAt_bot : t.termAt ⊥ = t.toSyntacticObject :=
  SyntacticObject.toUnorderedTree_injective
    (by rw [toUnorderedTree_termAt, toUnorderedTree_toSyntacticObject]; rfl)

theorem length_children_subtree (hp : ¬ IsMax p) : p.subtree.children.length = 2 := by
  rw [Positions.isMax_iff] at hp
  have h := length_children_toRoseTree (t.planarTermAt p)
  rw [toRoseTree_planarTermAt] at h
  exact h.resolve_left (by simpa using hp)

/-- A position that is not a leaf branches. -/
theorem isBranching_of_not_isMax (hp : ¬ IsMax p) : IsBranching p :=
  (isBranching_iff_mem_branching p).2 ⟨_, p.getElem?_eq, (length_children_subtree hp).ge⟩

/-- The term at a position immediately contains the terms at its covers. -/
theorem immediatelyContains_termAt :
    ImmediatelyContains (t.termAt p) y ↔ ∃ q, p ⋖ q ∧ t.termAt q = y := by
  rw [immediatelyContains_iff_mem_children, toUnorderedTree_termAt, UnorderedTree.children_mk,
    Multiset.mem_coe, List.mem_map]
  constructor
  · rintro ⟨c, hc, hcy⟩
    obtain ⟨q, hpq, rfl⟩ := Positions.mem_children_subtree.1 hc
    exact ⟨q, hpq, SyntacticObject.toUnorderedTree_injective (toUnorderedTree_termAt.trans hcy)⟩
  · rintro ⟨q, hpq, rfl⟩
    exact ⟨q.subtree, Positions.mem_children_subtree.2 ⟨q, hpq, rfl⟩, toUnorderedTree_termAt.symm⟩

/-- The term at a position contains or equals the terms at the positions below it. -/
theorem containsOrEq_termAt : ContainsOrEq (t.termAt p) y ↔ ∃ q, p ≤ q ∧ t.termAt q = y := by
  rw [← mem_terms, ← Multiset.mem_map_of_injective SyntacticObject.toUnorderedTree_injective,
      map_toUnorderedTree_terms,
    toUnorderedTree_termAt, UnorderedTree.subtrees_mk]
  simp only [unorderedSubtrees_eq_map, Multiset.mem_coe, List.mem_map, mem_subtrees,
    Positions.isSubtree_subtree]
  constructor
  · rintro ⟨s, ⟨q, hpq, rfl⟩, hsy⟩
    exact ⟨q, hpq, SyntacticObject.toUnorderedTree_injective (toUnorderedTree_termAt.trans hsy)⟩
  · rintro ⟨q, hpq, rfl⟩
    exact ⟨q.subtree, ⟨q, hpq, rfl⟩, toUnorderedTree_termAt.symm⟩

theorem mem_terms_iff : y ∈ t.toSyntacticObject.terms ↔ ∃ q, t.termAt q = y := by
  rw [mem_terms, ← termAt_bot, containsOrEq_termAt]
  simp

variable (t) in
/-- The terms of a planar object are the terms at its positions, one per position. -/
theorem terms_eq_map_termAt :
    t.toSyntacticObject.terms = (Finset.univ : Finset t.toRoseTree.Positions).val.map t.termAt := by
  apply Multiset.map_injective SyntacticObject.toUnorderedTree_injective
  rw [map_toUnorderedTree_terms, Multiset.map_map,
    show SyntacticObject.toUnorderedTree ∘ t.termAt = UnorderedTree.mk ∘ Positions.subtree from
      funext fun _ ↦ toUnorderedTree_termAt, toUnorderedTree_toSyntacticObject]
  rw [← Multiset.map_map, Positions.map_subtree_univ, UnorderedTree.subtrees_mk,
    unorderedSubtrees_eq_map, Multiset.map_coe]

variable (t) in
theorem count_terms [DecidableEq α]
    (u : SyntacticObject α) :
    t.toSyntacticObject.terms.count u = (Finset.univ.filter (t.termAt · = u)).card := by
  rw [terms_eq_map_termAt, Multiset.count_map, Finset.card_def, Finset.filter_val]
  simp only [eq_comm]


variable {a : t.toRoseTree.Positions} {x : SyntacticObject α}

theorem parent_mem_branching (ha : a ≠ ⊥) : a.val.parent ∈ t.toRoseTree.branching := by
  have hc : a.subtree ∈ (Order.pred a).subtree.children :=
    Positions.mem_children_subtree.2
      ⟨a, Order.pred_covBy_of_not_isMin (by simpa [isMin_iff_eq_bot] using ha), rfl⟩
  have hso := length_children_toRoseTree (t.planarTermAt (Order.pred a))
  rw [toRoseTree_planarTermAt] at hso
  refine mem_positionsWhere.2 ⟨_, (Order.pred a).getElem?_eq, ?_⟩
  generalize (Order.pred a).subtree = s at hc hso
  obtain ⟨v, cs⟩ := s
  rcases hso with h0 | h2 <;>
    grind [arity, List.length_eq_zero_iff, children_node]

/-- C-command between terms is witnessed by c-command between occurrences of them, with no
condition on how often they occur. -/
theorem exists_cCommands_termAt_of_cCommands (h : t.toSyntacticObject.CCommands x y) :
    ∃ p q : t.toRoseTree.Positions, t.toRoseTree.CCommands p q ∧ t.termAt p = x ∧ t.termAt q = y :=
        by
  obtain ⟨z, -, ⟨w, hw, hwx, hwz, hne⟩, hzy⟩ := h
  obtain ⟨m, rfl⟩ := mem_terms_iff.1 hw
  obtain ⟨c, hmc, rfl⟩ := immediatelyContains_termAt.1 hwx
  obtain ⟨d, hmd, rfl⟩ := immediatelyContains_termAt.1 hwz
  obtain ⟨q, hdq, rfl⟩ := containsOrEq_termAt.1 hzy
  have hc : c ≠ ⊥ := ne_bot_of_gt hmc.lt
  have hm : m.val = c.val.parent := by rw [← Positions.pred_val, Order.pred_eq_of_covBy hmc]
  refine ⟨c, q, (cCommands_iff_parent_lt (fun h ↦ hc (Subtype.ext h)) (parent_mem_branching hc)).2
    ⟨hm ▸ Subtype.coe_lt_coe.2 (hmd.lt.trans_le hdq), fun hcq ↦ hne ?_⟩, rfl, rfl⟩
  rw [Subtype.ext (IsForestOrder.eq_of_covBy_of_le (Positions.covBy_iff.1 hmc)
    (Positions.covBy_iff.1 hmd) hcq (Subtype.coe_le_coe.2 hdq))]

/-- C-command between occurrences is c-command between their terms when the commander's term differs
from its sisters' ([collins-stabler-2016]'s Theorem 3). -/
theorem cCommands_termAt_of_cCommands {p q : t.toRoseTree.Positions}
    (hs : ∀ d, Order.pred p ⋖ d → d ≠ p → t.termAt d ≠ t.termAt p)
    (h : t.toRoseTree.CCommands p q) : t.toSyntacticObject.CCommands (t.termAt p) (t.termAt q) := by
  have hp : p ≠ ⊥ := fun h' ↦ h.2.1 (h' ▸ bot_le)
  obtain ⟨hpq, hnpq⟩ :=
    (cCommands_iff_parent_lt (fun h' ↦ hp (Subtype.ext h')) (parent_mem_branching hp)).1 h
  obtain ⟨d, hpd, hdq⟩ := exists_covBy_le_of_lt (show Order.pred p < q from hpq)
  have hdp : d ≠ p := by rintro rfl; exact hnpq hdq
  exact ⟨t.termAt d, mem_terms_iff.2 ⟨d, rfl⟩, ⟨_, mem_terms_iff.2 ⟨Order.pred p, rfl⟩,
    immediatelyContains_termAt.2
      ⟨p, Order.pred_covBy_of_not_isMin (by simpa [isMin_iff_eq_bot] using hp), rfl⟩,
    immediatelyContains_termAt.2 ⟨d, hpd, rfl⟩, (hs d hpd hdp).symm⟩,
    containsOrEq_termAt.2 ⟨q, hdq, rfl⟩⟩

theorem cCommands_termAt_iff (hu : ∀ q, t.termAt q = t.termAt a → q = a) :
    t.toSyntacticObject.CCommands (t.termAt a) x ↔
      ∃ q : t.toRoseTree.Positions, t.toRoseTree.CCommands a q ∧ t.termAt q = x := by
  refine ⟨fun h ↦ ?_, fun ⟨q, hq, hqx⟩ ↦ hqx ▸ cCommands_termAt_of_cCommands
    (fun d _ hd he ↦ hd (hu d he)) hq⟩
  obtain ⟨p, q, hpq, hpa, rfl⟩ := exists_cCommands_termAt_of_cCommands h
  exact ⟨q, hu p hpa ▸ hpq, rfl⟩

theorem eq_termAt_pred_of_immediatelyContains (hu : ∀ q, t.termAt q = t.termAt a → q = a)
    {m : SyntacticObject α} (hm : m ∈ t.toSyntacticObject.terms)
    (h : ImmediatelyContains m (t.termAt a)) : m = t.termAt (Order.pred a) := by
  obtain ⟨m, rfl⟩ := mem_terms_iff.1 hm
  obtain ⟨c, hmc, hca⟩ := immediatelyContains_termAt.1 h
  obtain rfl := hu c hca
  rw [Order.pred_eq_of_covBy hmc]

/-! ### Daughters -/

variable {c d e q q' : t.toRoseTree.Positions}

theorem eq_or_eq_of_covBy (hc : a ⋖ c) (hd : a ⋖ d) (hcd : c ≠ d) (he : a ⋖ e) : e = c ∨ e = d := by
  have hlen := length_children_subtree (not_isMax_of_lt hc.lt)
  have hlt : ∀ (r : t.toRoseTree.Positions) (m : ℕ), r.val = a.val * .of m → m < 2 := by
    intro r m hm
    have hr := r.2
    rw [hm] at hr
    obtain ⟨s, hs, hms⟩ := mem_validPaths_append_singleton_iff.1 hr
    rw [a.getElem?_eq, Option.some.injEq] at hs
    exact hlen ▸ hs ▸ hms
  obtain ⟨i, hi⟩ := GornAddress.covBy_iff.1 (Positions.covBy_iff.1 hc)
  obtain ⟨j, hj⟩ := GornAddress.covBy_iff.1 (Positions.covBy_iff.1 hd)
  obtain ⟨k, hk⟩ := GornAddress.covBy_iff.1 (Positions.covBy_iff.1 he)
  have := hlt c i hi
  have := hlt d j hj
  have := hlt e k hk
  have hij : i ≠ j := fun h ↦ hcd (Subtype.ext (by rw [hi, hj, h]))
  rcases (by omega : k = i ∨ k = j) with rfl | rfl
  · exact .inl (Subtype.ext (hk.trans hi.symm))
  · exact .inr (Subtype.ext (hk.trans hj.symm))

theorem immediatelyContains_termAt_iff_of_covBy (hc : a ⋖ c) (hd : a ⋖ d) (hcd : c ≠ d) :
    ImmediatelyContains (t.termAt a) x ↔ x = t.termAt c ∨ x = t.termAt d := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.elim (· ▸ immediatelyContains_termAt.2 ⟨c, hc, rfl⟩)
    (· ▸ immediatelyContains_termAt.2 ⟨d, hd, rfl⟩)⟩
  obtain ⟨e, he, rfl⟩ := immediatelyContains_termAt.1 h
  exact (eq_or_eq_of_covBy hc hd hcd he).imp (congrArg _) (congrArg _)

theorem cCommands_of_covBy (hc : a ⋖ c) (hq : a < q) (hcq : ¬ c ≤ q) : t.toRoseTree.CCommands c q :=
    by
  have hpar : c.val.parent = a.val := by rw [← Positions.pred_val, Order.pred_eq_of_covBy hc]
  exact (commands_iff_lt_of_covBy (Positions.covBy_iff.1 hc)
    (hpar ▸ parent_mem_branching (ne_bot_of_gt hc.lt))).2 ⟨hq, hcq⟩

theorem not_cCommands_of_covBy (hc : a ⋖ c) (hd : a ⋖ d) (hcd : c ≠ d) (hcq : c < q)
    (hdq' : d ≤ q') : ¬ t.toRoseTree.CCommands q q' :=
  not_commands_of_covBy_of_lt (Positions.covBy_iff.1 hd)
    ((isBranching_iff_mem_branching c).1 (isBranching_of_not_isMax (not_isMax_of_lt hcq)))
    (Subtype.coe_lt_coe.2 hc.lt)
    (fun h ↦ hcd (IsForestOrder.eq_of_covBy_of_le hc hd le_rfl (Subtype.coe_le_coe.1 h)))
    (Subtype.coe_lt_coe.2 hcq) (Subtype.coe_le_coe.2 hdq')

theorem termAt_eq_or_eq_of_covBy {y : SyntacticObject α}
    (hn : t.termAt a = x * y) (he : a ⋖ e) : t.termAt e = x ∨ t.termAt e = y :=
  immediatelyContains_mul.1 (hn ▸ immediatelyContains_termAt.2 ⟨e, he, rfl⟩)

theorem exists_covBy_termAt_eq_left {y : SyntacticObject α}
    (hn : t.termAt a = x * y) :
    ∃ c, a ⋖ c ∧ t.termAt c = x :=
  immediatelyContains_termAt.1 (hn ▸ immediatelyContains_mul.2 (.inl rfl))

theorem exists_covBy_termAt_eq_right {y : SyntacticObject α}
    (hn : t.termAt a = x * y) :
    ∃ d, a ⋖ d ∧ t.termAt d = y :=
  immediatelyContains_termAt.1 (hn ▸ immediatelyContains_mul.2 (.inr rfl))

/-! ### Heads -/

variable {L ι : Type} {t : PlanarSyntacticObject (SyntacticObject.Leaf L ι)}
  {a q : t.toRoseTree.Positions}

variable (t) in
/-- The term at a position is a lexical item, a head. -/
def IsHeadAt (q : t.toRoseTree.Positions) : Prop := (t.termAt q).token?.isSome

instance : DecidablePred t.IsHeadAt := fun _ ↦ inferInstanceAs (Decidable (_ = _))

theorem isHeadAt_iff : t.IsHeadAt q ↔ ∃ tok : L, t.termAt q = SyntacticObject.leaf tok := by
  unfold IsHeadAt
  rw [Option.isSome_iff_exists]
  exact exists_congr fun _ ↦ token?_eq_some_iff

theorem IsHeadAt.isMax (h : t.IsHeadAt q) : IsMax q := by
  obtain ⟨tok, htok⟩ := isHeadAt_iff.1 h
  refine fun r hqr ↦ hqr.lt_or_eq.elim (fun hlt ↦ ?_) (·.ge)
  obtain ⟨e, he, -⟩ := exists_covBy_le_of_lt hlt
  exact (immediatelyContains_leaf tok _ (htok ▸ immediatelyContains_termAt.2 ⟨e, he, rfl⟩)).elim

theorem IsHeadAt.exists_covBy_le (h : t.IsHeadAt q) (ha : ¬ IsMax a) (haq : a ≤ q) :
    ∃ e, a ⋖ e ∧ e ≤ q :=
  exists_covBy_le_of_lt (lt_of_le_of_ne haq fun he ↦ ha (he ▸ h.isMax))

end PlanarSyntacticObject

/-! ### Closeness at positions -/

namespace PlanarSyntacticObject

variable (t : PlanarSyntacticObject α)

/-- The generators in `P` properly dominating a position, the key under which a probe searching the
object compares goals (`PhraseStructure.ancestors`). -/
def above (P : Set GornAddress) [DecidablePred (· ∈ P)] (q : t.toRoseTree.Positions) :
    Finset GornAddress :=
  (Finset.Iio q.val).filter (· ∈ P)

theorem coe_above (P : Set GornAddress) [DecidablePred (· ∈ P)] (q : t.toRoseTree.Positions) :
    (t.above P q : Set GornAddress) = ancestors P q.val := by
  ext x
  simp [above, ancestors, and_comm]

variable {t} {q g : t.toRoseTree.Positions}

/-- Between positions neither of which dominates the other, closeness under the branching
positions is asymmetric c-command. -/
theorem above_branching_lt_iff (h : IncompRel (· ≤ ·) q g) :
    t.above t.toRoseTree.branching q < t.above t.toRoseTree.branching g ↔
      t.toRoseTree.CCommands q g ∧ ¬ t.toRoseTree.CCommands g q := by
  rw [← Finset.coe_ssubset, coe_above, coe_above]
  exact ancestors_ssubset_ancestors_iff_commands h

theorem above_branching_lt_of_cCommands (hqg : t.toRoseTree.CCommands q g)
    (hgq : ¬ t.toRoseTree.CCommands g q) :
    t.above t.toRoseTree.branching q < t.above t.toRoseTree.branching g :=
  (above_branching_lt_iff hqg.2).2 ⟨hqg, hgq⟩

end PlanarSyntacticObject

/-! ### Complements -/

section Complement

variable (t : PlanarSyntacticObject α)

variable {t} in
-- A position other than the root is one of the two daughters of its parent.
private theorem exists_eq_parent_mul_of {h : GornAddress} (hh : h ∈ t.toRoseTree.validPaths)
    (h0 : h ≠ ⊥) : ∃ s i, t.toRoseTree[h.parent]? = some s ∧ s.arity = 2 ∧ i < 2 ∧
      h = h.parent * .of i := by
  set hp : t.toRoseTree.Positions := ⟨h, hh⟩
  have hp0 : hp ≠ ⊥ := fun he ↦ h0 (congrArg Subtype.val he)
  have hm : Order.pred hp ⋖ hp :=
    Order.pred_covBy_of_not_isMin (by simpa [isMin_iff_eq_bot] using hp0)
  have hlen := PlanarSyntacticObject.length_children_subtree (not_isMax_of_lt hm.lt)
  obtain ⟨i, hi⟩ := GornAddress.covBy_iff.1 (Positions.covBy_iff.1 hm)
  have hlt : i < 2 := by
    have hv := hp.2
    rw [hi] at hv
    obtain ⟨s, hs, his⟩ := mem_validPaths_append_singleton_iff.1 hv
    rw [(Order.pred hp).getElem?_eq, Option.some.injEq] at hs
    exact hlen ▸ hs ▸ his
  exact ⟨_, i, (Order.pred hp).getElem?_eq, hlen, hlt, hi⟩

end Complement

end Minimalist
