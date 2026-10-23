/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.Positions
public import Mathlib.Order.Atoms
public import Linglib.Syntax.Command
public import Linglib.Syntax.Projection
public import Linglib.Syntax.Minimalist.SyntacticObject.Term

/-!
# Positions of linearized syntactic objects

The positions of a linearized syntactic object, the paths to its vertices, form a rooted tree
(`RoseTree.Positions`). Each carries a term, the subtree there read as a syntactic object: the
terms at the covers of a position are the terms its term immediately contains, and the terms at
the positions below it are the terms its term contains, so c-command by a term occurring once is
c-command from its position. Which daughter heads a position is not part of the object but of a
head function (`SyntacticObject/Projection.lean`).

## Main definitions

* `LinearizedSyntacticObject.termAt`: the term at a position.
* `LinearizedSyntacticObject.branching`, `LinearizedSyntacticObject.above`: the branching positions
  of a linearized object, and the generators above a position, its closeness key.
* `Minimalist.complement`: the sister of a head.

## Main statements

* `LinearizedSyntacticObject.immediatelyContains_termAt`,
  `LinearizedSyntacticObject.containsOrEq_termAt`: terms contain one another as their positions
  dominate one another.
* `LinearizedSyntacticObject.exists_cCommands_termAt_of_cCommands`,
  `LinearizedSyntacticObject.cCommands_termAt_of_cCommands`: c-command between terms is witnessed by
  c-command between occurrences, and conversely when sister terms are distinct: Collins and
  Stabler's theorem relating c-command between objects to c-command between occurrences.
* `LinearizedSyntacticObject.isBranching_of_not_isMax`: a position that is not a leaf branches.
* `LinearizedSyntacticObject.above_branching_lt_iff`: closeness under the branching positions is
  asymmetric c-command.
* `Minimalist.mem_cCommandDomain_iff_complement_le`: a head c-commands exactly the positions below
  its complement.

## References

* [collins-stabler-2016]
-/

@[expose] public section

namespace Minimalist

open RoseTree SyntacticObject Core.Order PhraseStructure

/-! ### Terms at positions -/

namespace LinearizedSyntacticObject

open RoseTree SyntacticObject

variable {t : LinearizedSyntacticObject} {p : t.val.Positions} {y : SyntacticObject}

theorem isSyntacticObject_subtree (p : t.val.Positions) :
    IsSyntacticObject (UnorderedTree.mk p.subtree) :=
  isSyntacticObject_of_mem_subtrees t.toSyntacticObject _
    (mem_unorderedSubtrees.2 ⟨_, _, p.subtreeAt_eq, rfl⟩)

variable (t) in
/-- The term of `t` at a position. -/
def termAt (p : t.val.Positions) : SyntacticObject := ⟨_, isSyntacticObject_subtree p⟩

@[simp] theorem termAt_bot : t.termAt ⊥ = t.toSyntacticObject := rfl

variable (t) in
/-- The term of `t` at a position, with the order of daughters it has in `t`. -/
def linearizedTermAt (p : t.val.Positions) : LinearizedSyntacticObject :=
  ⟨_, isSyntacticObject_subtree p⟩

@[simp] theorem toSyntacticObject_linearizedTermAt :
    (t.linearizedTermAt p).toSyntacticObject = t.termAt p := rfl

theorem length_children_subtree (hp : ¬ IsMax p) : p.subtree.children.length = 2 := by
  have hs := isSyntacticObject_subtree p
  rw [Positions.isMax_iff] at hp
  rcases hsub : p.subtree with ⟨v, cs⟩
  rw [hsub] at hp hs
  exact (SyntacticObject.length_eq_zero_or_two hs).resolve_left (by simpa using hp)

/-- A position that is not a leaf branches. -/
theorem isBranching_of_not_isMax (hp : ¬ IsMax p) : IsBranching p := by
  have h2 := length_children_subtree hp
  have hv : ∀ i < 2, (⟨p.val.toList ++ [i]⟩ : TreePath) ∈ t.val.validPaths := fun i hi ↦
    mem_validPaths_append_singleton_iff.2 ⟨_, p.subtreeAt_eq, h2 ▸ hi⟩
  refine ⟨⟨_, hv 0 (by omega)⟩, Positions.covBy_iff.2 (TreePath.covBy_iff.2 ⟨0, rfl⟩),
    ⟨_, hv 1 (by omega)⟩, Positions.covBy_iff.2 (TreePath.covBy_iff.2 ⟨1, rfl⟩), fun h ↦ ?_⟩
  simpa using congrArg (fun q : t.val.Positions ↦ q.val.toList.getLast?) h

/-- The term at a position immediately contains the terms at its covers. -/
theorem immediatelyContains_termAt :
    ImmediatelyContains (t.termAt p) y ↔ ∃ q, p ⋖ q ∧ t.termAt q = y := by
  show y.val ∈ (UnorderedTree.mk p.subtree).children ↔ _
  rw [UnorderedTree.children_mk, Multiset.mem_coe, List.mem_map]
  constructor
  · rintro ⟨c, hc, hcy⟩
    obtain ⟨q, hpq, rfl⟩ := Positions.mem_children_subtree.1 hc
    exact ⟨q, hpq, Subtype.ext hcy⟩
  · rintro ⟨q, hpq, rfl⟩
    exact ⟨q.subtree, Positions.mem_children_subtree.2 ⟨q, hpq, rfl⟩, rfl⟩

/-- The term at a position contains or equals the terms at the positions below it. -/
theorem containsOrEq_termAt : ContainsOrEq (t.termAt p) y ↔ ∃ q, p ≤ q ∧ t.termAt q = y := by
  rw [← mem_terms, ← Multiset.mem_map_of_injective Subtype.val_injective, map_val_terms]
  show y.val ∈ unorderedSubtrees p.subtree ↔ _
  simp only [unorderedSubtrees_eq_map, Multiset.mem_coe, List.mem_map, mem_subtrees,
    Positions.isSubtree_subtree]
  constructor
  · rintro ⟨s, ⟨q, hpq, rfl⟩, hsy⟩
    exact ⟨q, hpq, Subtype.ext hsy⟩
  · rintro ⟨q, hpq, rfl⟩
    exact ⟨q.subtree, ⟨q, hpq, rfl⟩, rfl⟩

theorem mem_terms_iff : y ∈ t.toSyntacticObject.terms ↔ ∃ q, t.termAt q = y := by
  rw [mem_terms, ← termAt_bot, containsOrEq_termAt]
  simp



variable {a : t.val.Positions} {x : SyntacticObject}

theorem isBranchingAt_parent (ha : a ≠ ⊥) : IsBranchingAt t.val a.val.parent := by
  have hc : a.subtree ∈ (Order.pred a).subtree.children :=
    Positions.mem_children_subtree.2
      ⟨a, Order.pred_covBy_of_not_isMin (by simpa [isMin_iff_eq_bot] using ha), rfl⟩
  have hso := isSyntacticObject_subtree (Order.pred a)
  refine mem_positionsWhere.2 ⟨_, (Order.pred a).subtreeAt_eq, ?_⟩
  generalize (Order.pred a).subtree = s at hc hso
  obtain ⟨v, cs⟩ := s
  rcases length_eq_zero_or_two hso with h0 | h2 <;>
    grind [arity, List.length_eq_zero_iff, children_node]

/-- C-command between terms is witnessed by c-command between occurrences of them, with no
condition on how often they occur. -/
theorem exists_cCommands_termAt_of_cCommands (h : t.toSyntacticObject.CCommands x y) :
    ∃ p q : t.val.Positions, t.val.CCommands p q ∧ t.termAt p = x ∧ t.termAt q = y := by
  obtain ⟨z, -, ⟨w, hw, hwx, hwz, hne⟩, hzy⟩ := h
  obtain ⟨m, rfl⟩ := mem_terms_iff.1 hw
  obtain ⟨c, hmc, rfl⟩ := immediatelyContains_termAt.1 hwx
  obtain ⟨d, hmd, rfl⟩ := immediatelyContains_termAt.1 hwz
  obtain ⟨q, hdq, rfl⟩ := containsOrEq_termAt.1 hzy
  have hc : c ≠ ⊥ := ne_bot_of_gt hmc.lt
  have hm : m.val = c.val.parent := by rw [← Positions.pred_val, Order.pred_eq_of_covBy hmc]
  refine ⟨c, q, (cCommands_iff_parent_lt (fun h ↦ hc (Subtype.ext h)) (isBranchingAt_parent hc)).2
    ⟨hm ▸ Subtype.coe_lt_coe.2 (hmd.lt.trans_le hdq), fun hcq ↦ hne ?_⟩, rfl, rfl⟩
  rw [Subtype.ext (IsLeftLinear.eq_of_covBy_of_le (Positions.covBy_iff.1 hmc)
    (Positions.covBy_iff.1 hmd) hcq (Subtype.coe_le_coe.2 hdq))]

/-- C-command between occurrences is c-command between their terms when the commander's term
differs from those of its sisters, [collins-stabler-2016]'s Theorem 3; their Merge applies only to
distinct objects, which secures the condition. -/
theorem cCommands_termAt_of_cCommands {p q : t.val.Positions}
    (hs : ∀ d, Order.pred p ⋖ d → d ≠ p → t.termAt d ≠ t.termAt p)
    (h : t.val.CCommands p q) : t.toSyntacticObject.CCommands (t.termAt p) (t.termAt q) := by
  have hp : p ≠ ⊥ := fun h' ↦ h.2.1 (h' ▸ bot_le)
  obtain ⟨hpq, hnpq⟩ :=
    (cCommands_iff_parent_lt (fun h' ↦ hp (Subtype.ext h')) (isBranchingAt_parent hp)).1 h
  obtain ⟨d, hpd, hdq⟩ := exists_covBy_le_of_lt (show Order.pred p < q from hpq)
  have hdp : d ≠ p := by rintro rfl; exact hnpq hdq
  exact ⟨t.termAt d, mem_terms_iff.2 ⟨d, rfl⟩, ⟨_, mem_terms_iff.2 ⟨Order.pred p, rfl⟩,
    immediatelyContains_termAt.2
      ⟨p, Order.pred_covBy_of_not_isMin (by simpa [isMin_iff_eq_bot] using hp), rfl⟩,
    immediatelyContains_termAt.2 ⟨d, hpd, rfl⟩, (hs d hpd hdp).symm⟩,
    containsOrEq_termAt.2 ⟨q, hdq, rfl⟩⟩

theorem cCommands_termAt_iff (hu : ∀ q, t.termAt q = t.termAt a → q = a) :
    t.toSyntacticObject.CCommands (t.termAt a) x ↔
      ∃ q : t.val.Positions, t.val.CCommands a q ∧ t.termAt q = x := by
  refine ⟨fun h ↦ ?_, fun ⟨q, hq, hqx⟩ ↦ hqx ▸ cCommands_termAt_of_cCommands
    (fun d _ hd he ↦ hd (hu d he)) hq⟩
  obtain ⟨p, q, hpq, hpa, rfl⟩ := exists_cCommands_termAt_of_cCommands h
  exact ⟨q, hu p hpa ▸ hpq, rfl⟩

theorem eq_termAt_pred_of_immediatelyContains (hu : ∀ q, t.termAt q = t.termAt a → q = a)
    {m : SyntacticObject} (hm : m ∈ t.toSyntacticObject.terms)
    (h : ImmediatelyContains m (t.termAt a)) : m = t.termAt (Order.pred a) := by
  obtain ⟨m, rfl⟩ := mem_terms_iff.1 hm
  obtain ⟨c, hmc, hca⟩ := immediatelyContains_termAt.1 h
  obtain rfl := hu c hca
  rw [Order.pred_eq_of_covBy hmc]

/-! ### Daughters -/

variable {c d e q q' : t.val.Positions}

theorem eq_or_eq_of_covBy (hc : a ⋖ c) (hd : a ⋖ d) (hcd : c ≠ d) (he : a ⋖ e) : e = c ∨ e = d := by
  have hlen := length_children_subtree (not_isMax_of_lt hc.lt)
  have hlt : ∀ (r : t.val.Positions) (m : ℕ), r.val.toList = a.val.toList ++ [m] → m < 2 := by
    intro r m hm
    have hr := r.2
    rw [show r.val = ⟨a.val.toList ++ [m]⟩ from TreePath.ext hm] at hr
    obtain ⟨s, hs, hms⟩ := mem_validPaths_append_singleton_iff.1 hr
    rw [a.subtreeAt_eq, Option.some.injEq] at hs
    exact hlen ▸ hs ▸ hms
  obtain ⟨i, hi⟩ := TreePath.covBy_iff.1 (Positions.covBy_iff.1 hc)
  obtain ⟨j, hj⟩ := TreePath.covBy_iff.1 (Positions.covBy_iff.1 hd)
  obtain ⟨k, hk⟩ := TreePath.covBy_iff.1 (Positions.covBy_iff.1 he)
  have := hlt c i hi
  have := hlt d j hj
  have := hlt e k hk
  have hij : i ≠ j := fun h ↦ hcd (Subtype.ext (TreePath.ext (by rw [hi, hj, h])))
  rcases (by omega : k = i ∨ k = j) with rfl | rfl
  · exact .inl (Subtype.ext (TreePath.ext (hk.trans hi.symm)))
  · exact .inr (Subtype.ext (TreePath.ext (hk.trans hj.symm)))

theorem immediatelyContains_termAt_iff_of_covBy (hc : a ⋖ c) (hd : a ⋖ d) (hcd : c ≠ d) :
    ImmediatelyContains (t.termAt a) x ↔ x = t.termAt c ∨ x = t.termAt d := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.elim (· ▸ immediatelyContains_termAt.2 ⟨c, hc, rfl⟩)
    (· ▸ immediatelyContains_termAt.2 ⟨d, hd, rfl⟩)⟩
  obtain ⟨e, he, rfl⟩ := immediatelyContains_termAt.1 h
  exact (eq_or_eq_of_covBy hc hd hcd he).imp (congrArg _) (congrArg _)

theorem cCommands_of_covBy (hc : a ⋖ c) (hq : a < q) (hcq : ¬ c ≤ q) : t.val.CCommands c q := by
  have hpar : c.val.parent = a.val := by rw [← Positions.pred_val, Order.pred_eq_of_covBy hc]
  exact (cCommands_iff_of_covBy (Positions.covBy_iff.1 hc)
    (hpar ▸ isBranchingAt_parent (ne_bot_of_gt hc.lt))).2 ⟨hq, hcq⟩

theorem not_cCommands_of_covBy (hc : a ⋖ c) (hd : a ⋖ d) (hcd : c ≠ d) (hcq : c < q)
    (hdq' : d ≤ q') : ¬ t.val.CCommands q q' := by
  intro h
  have hq0 : q ≠ ⊥ := ne_bot_of_gt hcq
  rw [cCommands_iff_parent_lt (fun h0 ↦ hq0 (Subtype.ext h0)) (isBranchingAt_parent hq0)] at h
  have hcq' : c.val ≤ q'.val := (Subtype.coe_le_coe.2 (Order.le_pred_of_lt hcq)).trans
    ((Positions.pred_val q).symm ▸ h.1.le)
  exact hcd (Subtype.ext (IsLeftLinear.eq_of_covBy_of_le (Positions.covBy_iff.1 hc)
    (Positions.covBy_iff.1 hd) hcq' (Subtype.coe_le_coe.2 hdq')))

theorem termAt_eq_or_eq_of_covBy {y : SyntacticObject} (hn : t.termAt a = SyntacticObject.merge x y)
    (he : a ⋖ e) : t.termAt e = x ∨ t.termAt e = y :=
  (immediatelyContains_merge _ _ _).1 (hn ▸ immediatelyContains_termAt.2 ⟨e, he, rfl⟩)

theorem exists_covBy_termAt_eq_left {y : SyntacticObject}
    (hn : t.termAt a = SyntacticObject.merge x y) :
    ∃ c, a ⋖ c ∧ t.termAt c = x :=
  immediatelyContains_termAt.1 (hn ▸ (immediatelyContains_merge _ _ _).2 (.inl rfl))

theorem exists_covBy_termAt_eq_right {y : SyntacticObject}
    (hn : t.termAt a = SyntacticObject.merge x y) :
    ∃ d, a ⋖ d ∧ t.termAt d = y :=
  immediatelyContains_termAt.1 (hn ▸ (immediatelyContains_merge _ _ _).2 (.inr rfl))

/-! ### Heads -/

variable (t) in
/-- The term at a position is a lexical item, a head. -/
def IsHeadAt (q : t.val.Positions) : Prop := (t.termAt q).token?.isSome

instance : DecidablePred t.IsHeadAt := fun _ ↦ inferInstanceAs (Decidable (_ = _))

theorem isHeadAt_iff : t.IsHeadAt q ↔ ∃ tok : LexicalItem.Token, t.termAt q = ↑tok := by
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

end LinearizedSyntacticObject

/-! ### Closeness at positions -/

namespace LinearizedSyntacticObject

variable (t : LinearizedSyntacticObject)

/-- The generators in `P` properly dominating a position, the key under which a probe searching the
object compares goals (`PhraseStructure.ancestors`). -/
def above (P : Set TreePath) [DecidablePred (· ∈ P)] (q : t.val.Positions) : Finset TreePath :=
  (Finset.Iio q.val).filter (· ∈ P)

theorem coe_above (P : Set TreePath) [DecidablePred (· ∈ P)] (q : t.val.Positions) :
    (t.above P q : Set TreePath) = ancestors P q.val := by
  ext x
  simp [above, ancestors, and_comm]

/-- The branching positions of a linearized object, the generators of c-command. -/
def branching : Set TreePath := {x | t.val.IsBranchingAt x}

instance : DecidablePred (· ∈ t.branching) :=
  fun x ↦ inferInstanceAs (Decidable (t.val.IsBranchingAt x))

variable {t} {q g : t.val.Positions}

/-- Between positions neither of which dominates the other, closeness under the branching
positions is asymmetric c-command. -/
theorem above_branching_lt_iff (hqg : ¬ q ≤ g) (hgq : ¬ g ≤ q) :
    t.above t.branching q < t.above t.branching g ↔
      t.val.CCommands q g ∧ ¬ t.val.CCommands g q := by
  rw [← Finset.coe_ssubset, coe_above, coe_above]
  exact ancestors_ssubset_ancestors_iff_cCommands hqg hgq

theorem above_branching_lt_of_cCommands (hqg : t.val.CCommands q g)
    (hgq : ¬ t.val.CCommands g q) : t.above t.branching q < t.above t.branching g :=
  (above_branching_lt_iff hqg.2.1 hqg.2.2).2 ⟨hqg, hgq⟩

end LinearizedSyntacticObject

/-! ### Complements -/

section Complement

variable (t : LinearizedSyntacticObject)

/-- The complement of the head at `p` is its sister. -/
def complement (p : TreePath) : TreePath := ⟨p.toList.dropLast ++ [1 - p.toList.getLastD 0]⟩

theorem parent_covBy_complement (p : TreePath) : p.parent ⋖ complement p :=
  TreePath.covBy_iff.2 ⟨_, rfl⟩

@[simp] theorem parent_complement (p : TreePath) : (complement p).parent = p.parent :=
  TreePath.ext (by simp [complement])

variable {t} in
theorem complement_complement {h : TreePath} (hh : h ∈ t.val.validPaths) (h0 : h ≠ ⊥) :
    complement (complement h) = h := by
  set hp : t.val.Positions := ⟨h, hh⟩
  have hp0 : hp ≠ ⊥ := fun he ↦ h0 (congrArg Subtype.val he)
  have hm : Order.pred hp ⋖ hp :=
    Order.pred_covBy_of_not_isMin (by simpa [isMin_iff_eq_bot] using hp0)
  have hlen := LinearizedSyntacticObject.length_children_subtree (not_isMax_of_lt hm.lt)
  obtain ⟨i, hi⟩ := TreePath.covBy_iff.1 (Positions.covBy_iff.1 hm)
  have hlt : i < 2 := by
    have hv := hp.2
    rw [show hp.val = ⟨(Order.pred hp).val.toList ++ [i]⟩ from TreePath.ext hi] at hv
    obtain ⟨s, hs, his⟩ := mem_validPaths_append_singleton_iff.1 hv
    rw [(Order.pred hp).subtreeAt_eq, Option.some.injEq] at hs
    exact hlen ▸ hs ▸ his
  have hhv : h.toList = (Order.pred hp).val.toList ++ [i] := hi
  apply TreePath.ext
  simp only [complement, hhv, List.dropLast_concat, List.getLastD_concat]
  congr 2
  omega

variable {t} in
/-- In a syntactic object, a head other than the root c-commands exactly the positions below its
complement. -/
theorem mem_cCommandDomain_iff_complement_le {h q : TreePath} (hh : h ∈ t.val.validPaths)
    (h0 : h ≠ ⊥) (hq : q ∈ t.val.validPaths) :
    q ∈ t.val.cCommandDomain h ↔ complement h ≤ q := by
  set hp : t.val.Positions := ⟨h, hh⟩
  have hp0 : hp ≠ ⊥ := fun he ↦ h0 (congrArg Subtype.val he)
  have hm : Order.pred hp ⋖ hp :=
    Order.pred_covBy_of_not_isMin (by simpa [isMin_iff_eq_bot] using hp0)
  have hmv : (Order.pred hp).val = h.parent := Positions.pred_val hp
  have hlen := LinearizedSyntacticObject.length_children_subtree (not_isMax_of_lt hm.lt)
  have hcv : complement h ∈ t.val.validPaths := by
    refine mem_validPaths_append_singleton_iff.2 ⟨(Order.pred hp).subtree, ?_, ?_⟩
    · rw [← TreePath.parent_toList, ← hmv]
      exact (Order.pred hp).subtreeAt_eq
    · rw [hlen]
      omega
  set hc : t.val.Positions := ⟨complement h, hcv⟩
  have hmc : Order.pred hp ⋖ hc :=
    Positions.covBy_iff.2 (hmv ▸ parent_covBy_complement h)
  have hhc : hp ≠ hc := fun he ↦ by
    have := congrArg (fun r : t.val.Positions ↦ r.val.toList.getLastD 0) he
    simp only [hp, hc, complement, List.getLastD_concat] at this
    omega
  rw [RoseTree.mem_cCommandDomain, cCommands_iff_parent_lt h0
    (LinearizedSyntacticObject.isBranchingAt_parent (t := t) hp0)]
  set qp : t.val.Positions := ⟨q, hq⟩
  constructor
  · rintro ⟨hlt, hnl⟩
    obtain ⟨e, hme, heq⟩ := exists_covBy_le_of_lt
      (show Order.pred hp < qp from Subtype.coe_lt_coe.1 (hmv ▸ hlt))
    rcases LinearizedSyntacticObject.eq_or_eq_of_covBy hm hmc hhc hme with rfl | rfl
    · exact absurd heq hnl
    · exact heq
  · intro hcq
    refine ⟨(parent_covBy_complement h).lt.trans_le hcq, fun hhq ↦ hhc (Subtype.ext ?_)⟩
    exact IsLeftLinear.eq_of_covBy_of_le (Positions.covBy_iff.1 hm) (Positions.covBy_iff.1 hmc)
      hhq hcq

end Complement

end Minimalist
