/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.UnorderedTree.Replace
public import Linglib.Syntax.Minimalist.SyntacticObject.Build
public import Linglib.Syntax.Minimalist.Label.Selection
public import Linglib.Syntax.Minimalist.SyntacticObject.Term

/-!
# Substitution on syntactic objects

`SyntacticObject.subst f s` substitutes `f u` for every outermost term `u` of `s` on which `f` is
defined, simultaneously; it is `UnorderedTree.subst` closed under well-formedness, which holds
because substitution preserves the arity of every vertex. `replace s target replacement` is its
one-target case, and the copy-theory use is `deleteAccessible mover current`, `current` with the
mover's occurrences replaced by the trace of its head (`headTrace`). The linearized objects carry
the same replacement, commuting with forgetting the order (`toSyntacticObject_replace`).

## Main definitions

* `Minimalist.SyntacticObject.subst`, `Minimalist.SyntacticObject.replace`
* `Minimalist.SyntacticObject.headTrace`, `Minimalist.SyntacticObject.deleteAccessible`
* `Minimalist.LinearizedSyntacticObject.find?`, `Minimalist.LinearizedSyntacticObject.replace`
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject

theorem isSyntacticObject_subst (f : SyntacticObject → Option SyntacticObject)
    (s : SyntacticObject) :
    IsSyntacticObject (UnorderedTree.subst (fun u ↦
      if h : IsSyntacticObject u then (f ⟨u, h⟩).map Subtype.val else none) s.val) := by
  have hg {u d : UnorderedTree Vertex} (hd : IsSyntacticObject d) :
      IsSyntacticObject ((if h : IsSyntacticObject u then (f ⟨u, h⟩).map Subtype.val
        else none).getD d) := by
    split_ifs with h
    · cases f ⟨u, h⟩ with
      | none => exact hd
      | some r => exact r.2
    · exact hd
  induction s using ind with
  | leaf tok =>
    rw [leaf_val, UnorderedTree.subst_leaf]
    exact hg (SyntacticObject.leaf tok).2
  | trace => rw [trace_val, UnorderedTree.subst_leaf]; exact hg trace.2
  | traceOf tok => rw [traceOf_val, UnorderedTree.subst_leaf]; exact hg (traceOf tok).2
  | merge l r ihl ihr =>
    rw [merge_val, UnorderedTree.subst_node_pair]
    exact hg ((isSyntacticObject_merge_iff _ _).2 ⟨ihl, ihr⟩)

namespace SyntacticObject

/-- Substitute `f u` for every outermost term `u` of `s` on which `f` is defined, simultaneously. -/
def subst (f : SyntacticObject → Option SyntacticObject) (s : SyntacticObject) : SyntacticObject :=
  ⟨UnorderedTree.subst (fun u ↦
    if h : IsSyntacticObject u then (f ⟨u, h⟩).map Subtype.val else none) s.val,
    isSyntacticObject_subst f s⟩

variable {f g : SyntacticObject → Option SyntacticObject}

private theorem subst_val (f : SyntacticObject → Option SyntacticObject) (s : SyntacticObject) :
    (s.subst f).val = UnorderedTree.subst (fun u ↦
      if h : IsSyntacticObject u then (f ⟨u, h⟩).map Subtype.val else none) s.val := rfl

private theorem subst_fun_val (f : SyntacticObject → Option SyntacticObject) (s : SyntacticObject) :
    (if h : IsSyntacticObject s.val then (f ⟨s.val, h⟩).map Subtype.val else none) =
      (f s).map Subtype.val :=
  dite_eq_left s.2

private theorem val_getD (o : Option SyntacticObject) (d : SyntacticObject) :
    (o.getD d).val = (o.map Subtype.val).getD d.val := by
  cases o <;> rfl

@[simp] theorem subst_merge (f : SyntacticObject → Option SyntacticObject)
    (l r : SyntacticObject) :
    (merge l r).subst f = (f (merge l r)).getD (merge (l.subst f) (r.subst f)) := by
  apply Subtype.ext
  have h := UnorderedTree.subst_node_pair (fun u ↦
    if h : IsSyntacticObject u then (f ⟨u, h⟩).map Subtype.val else none) Vertex.bare l.val r.val
  rw [← merge_val] at h
  rw [subst_val, h, val_getD, subst_fun_val]
  rfl

theorem subst_of_val_eq_leaf {s : SyntacticObject} {a : Vertex} (hs : s.val = UnorderedTree.leaf a)
    (f : SyntacticObject → Option SyntacticObject) : s.subst f = (f s).getD s := by
  apply Subtype.ext
  have h := UnorderedTree.subst_leaf (fun u ↦
    if h : IsSyntacticObject u then (f ⟨u, h⟩).map Subtype.val else none) a
  rw [← hs] at h
  rw [subst_val, h, val_getD, subst_fun_val]

theorem subst_congr {s : SyntacticObject} (h : ∀ u ∈ s.terms, f u = g u) :
    s.subst f = s.subst g := by
  apply Subtype.ext
  rw [subst_val, subst_val]
  refine UnorderedTree.subst_congr fun u hu ↦ ?_
  have hu' := isSyntacticObject_of_mem_subtrees s u hu
  rw [dite_eq_left hu', dite_eq_left hu',
    h ⟨u, hu'⟩ ((val_mem_subtrees (S := ⟨u, hu'⟩)).1 hu)]

theorem subst_eq_self {s : SyntacticObject} (h : ∀ u ∈ s.terms, ∀ r, f u = some r → r = u) :
    s.subst f = s := by
  apply Subtype.ext
  rw [subst_val]
  refine UnorderedTree.subst_eq_self fun u hu r hr ↦ ?_
  have hu' := isSyntacticObject_of_mem_subtrees s u hu
  rw [dite_eq_left hu', Option.map_eq_some_iff] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  exact congrArg Subtype.val (h ⟨u, hu'⟩ ((val_mem_subtrees (S := ⟨u, hu'⟩)).1 hu) r' hr')

theorem subst_of_forall_eq_none {s : SyntacticObject} (h : ∀ u ∈ s.terms, f u = none) :
    s.subst f = s :=
  subst_eq_self fun u hu r hr ↦ by simp [h u hu] at hr

/-! ### Replacement -/

/-- Replace every subterm of `s` equal to `target` by `replacement`. -/
def replace (s target replacement : SyntacticObject) : SyntacticObject :=
  s.subst fun u ↦ if u = target then some replacement else none

@[simp] theorem replace_val (s target replacement : SyntacticObject) :
    (replace s target replacement).val
      = UnorderedTree.replace target.val replacement.val s.val := by
  rw [replace, subst_val, UnorderedTree.replace]
  refine UnorderedTree.subst_congr fun u hu ↦ ?_
  have hu' := isSyntacticObject_of_mem_subtrees s u hu
  rw [dite_eq_left hu']
  by_cases hut : u = target.val
  · rw [ite_eq_left (Subtype.ext hut : (⟨u, hu'⟩ : SyntacticObject) = target), ite_eq_left hut]
    rfl
  · rw [ite_eq_right fun h ↦ hut (congrArg Subtype.val h), ite_eq_right hut]
    rfl

@[simp] theorem replace_self (target replacement : SyntacticObject) :
    replace target target replacement = replacement :=
  Subtype.ext (by rw [replace_val, UnorderedTree.replace_self])

@[simp] theorem replace_self_self (target s : SyntacticObject) : s.replace target target = s :=
  Subtype.ext (by rw [replace_val, UnorderedTree.replace_self_self])

theorem replace_of_notMem_terms {s target replacement : SyntacticObject} (h : target ∉ s.terms) :
    s.replace target replacement = s :=
  Subtype.ext <| by
    rw [replace_val, UnorderedTree.replace_of_notMem_subtrees (by rwa [val_mem_subtrees])]

theorem replace_merge_of_ne {l r target replacement : SyntacticObject} (h : merge l r ≠ target) :
    replace (merge l r) target replacement
      = merge (replace l target replacement) (replace r target replacement) := by
  rw [replace, subst_merge, ite_eq_right h]
  rfl

theorem replace_of_val_eq_leaf {s target replacement : SyntacticObject} {a : Vertex}
    (hs : s.val = UnorderedTree.leaf a) (h : s ≠ target) : s.replace target replacement = s := by
  rw [replace, subst_of_val_eq_leaf hs, ite_eq_right h]
  rfl

/-- Moving the daughter `r` out of `[l r]` and leaving a trace yields `[l′ t]`, with `l′` the
    substituted left daughter; a tree is never its own daughter, taken here as a hypothesis. -/
example (l r : SyntacticObject) (h : merge l r ≠ r) :
    replace (merge l r) r trace = merge (replace l r trace) trace := by
  rw [replace_merge_of_ne h, replace_self]

/-! ### Traces -/

/-- A moved object leaves the trace of its head under the encoder `τ`, by default the head by
    selection, or the bare trace when it has none. -/
def headTrace (s : SyntacticObject) (τ : SyntacticObject → Option LexicalItem.Token := selHead) :
    SyntacticObject :=
  (τ s).elim trace traceOf

/-- The trace a moved object leaves is the trace leaf its encoder labels. -/
theorem headTrace_val (s : SyntacticObject) (τ : SyntacticObject → Option LexicalItem.Token) :
    (s.headTrace τ).val = UnorderedTree.leaf (Sum.inr (τ s)) := by
  unfold headTrace; cases τ s <;> rfl

/-- The remainder `T/mover`, the current object with the mover's occurrences replaced by the trace
    of its head under `τ`. -/
def deleteAccessible (mover current : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) : SyntacticObject :=
  current.replace mover (mover.headTrace τ)

@[simp] theorem deleteAccessible_val (mover current : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token) :
    (deleteAccessible mover current τ).val
      = UnorderedTree.replace mover.val (mover.headTrace τ).val current.val :=
  replace_val _ _ _

end SyntacticObject

/-! ### Linearized leaves -/

/-- The linearized form of a leaf object, which has only one; `none` on a merged object. -/
def SyntacticObject.toLinearizedLeaf? (s : SyntacticObject) : Option LinearizedSyntacticObject :=
  match s.val.value with
  | .inl (some tok) => some (.leaf tok)
  | .inl none => none
  | .inr none => some .trace
  | .inr (some tok) => some (.traceOf tok)

theorem SyntacticObject.toSyntacticObject_of_toLinearizedLeaf? {s : SyntacticObject}
    {p : LinearizedSyntacticObject} (h : s.toLinearizedLeaf? = some p) :
    p.toSyntacticObject = s := by
  rcases s.exists_form with ⟨tok, rfl⟩ | rfl | ⟨tok, rfl⟩ | ⟨l, r, rfl⟩ <;>
    simp [toLinearizedLeaf?, merge_val] at h <;> subst h <;> rfl

/-! ### Occurrences in linearized objects -/

namespace LinearizedSyntacticObject

/-- The leftmost, outermost subtree of `p` projecting to `target`. -/
def find? (p : LinearizedSyntacticObject) (target : SyntacticObject) :
    Option LinearizedSyntacticObject :=
  (p.val.subtrees.find? (mk · = target.val)).pmap (p := (mk · = target.val))
    (fun s hs ↦ ⟨s, hs.symm ▸ target.2⟩) fun _ h ↦ by simpa using List.find?_some h

theorem toSyntacticObject_find? {p s : LinearizedSyntacticObject} {target : SyntacticObject}
    (h : p.find? target = some s) : s.toSyntacticObject = target := by
  obtain ⟨t, ht, -, rfl⟩ := Option.pmap_eq_some_iff.1 (by rwa [find?] at h)
  exact Subtype.ext ht

/-- Every subtree of `p` projecting to `target` replaced by `rep`. -/
def replace (p : LinearizedSyntacticObject) (target : SyntacticObject)
    (rep : LinearizedSyntacticObject) : LinearizedSyntacticObject :=
  ⟨replaceIf (mk · = target.val) rep.val p.val, by
    rw [mk_replaceIf]
    exact replace_val p.toSyntacticObject target rep.toSyntacticObject ▸
      (p.toSyntacticObject.replace target rep.toSyntacticObject).2⟩

@[simp] theorem toSyntacticObject_replace (p : LinearizedSyntacticObject) (target : SyntacticObject)
    (rep : LinearizedSyntacticObject) :
    (p.replace target rep).toSyntacticObject
      = p.toSyntacticObject.replace target rep.toSyntacticObject :=
  Subtype.ext (by rw [replace_val]; exact mk_replaceIf _ _ _)

theorem mem_terms_toSyntacticObject {p : LinearizedSyntacticObject} {m : SyntacticObject} :
    m ∈ p.toSyntacticObject.terms ↔ ∃ q ∈ p.val.subtrees, mk q = m.val := by
  rw [← val_mem_subtrees, toSyntacticObject_val, subtrees_mk, unorderedSubtrees_eq_map,
    Multiset.mem_coe, List.mem_map]

theorem isSome_find?_iff {p : LinearizedSyntacticObject} {m : SyntacticObject} :
    (p.find? m).isSome ↔ m ∈ p.toSyntacticObject.terms := by
  rw [mem_terms_toSyntacticObject, find?, Option.isSome_pmap, List.find?_isSome]
  simp

theorem mem_subtrees_of_find? {p s : LinearizedSyntacticObject} {m : SyntacticObject}
    (h : p.find? m = some s) : s.val ∈ p.val.subtrees := by
  obtain ⟨t, -, ht, rfl⟩ := Option.pmap_eq_some_iff.1 (by rwa [find?] at h)
  exact List.mem_of_find?_eq_some ht

theorem replace_of_toSyntacticObject_eq {p r : LinearizedSyntacticObject} {target : SyntacticObject}
    (h : p.toSyntacticObject = target) : p.replace target r = r := by
  obtain ⟨⟨a, cs⟩, hp⟩ := p
  apply Subtype.ext
  simp only [replace, replaceIf_node]
  split_ifs with hc
  · rfl
  · exact absurd (congrArg Subtype.val h) hc

theorem replace_attach {p d r : LinearizedSyntacticObject} {target : SyntacticObject} {e : Edge}
    (h : SyntacticObject.merge d.toSyntacticObject p.toSyntacticObject ≠ target) :
    (p.attach e d).replace target r = (p.replace target r).attach e (d.replace target r) := by
  have h' : (p.attach e d).toSyntacticObject ≠ target := by rwa [toSyntacticObject_attach]
  apply Subtype.ext
  cases e <;> simp only [replace, attach, merge_val, replaceIf_node, List.map_cons,
    List.map_nil] <;> split_ifs with hc <;> first | rfl | exact (h' (Subtype.ext hc)).elim

theorem replace_of_val_eq_leaf {p r : LinearizedSyntacticObject} {target : SyntacticObject}
    {a : Vertex} (hp : p.val = RoseTree.leaf a) (h : p.toSyntacticObject ≠ target) :
    p.replace target r = p := by
  apply Subtype.ext
  simp only [replace, hp, replaceIf_node, List.map_nil]
  split_ifs with hc
  · exact (h (Subtype.ext (by rw [toSyntacticObject_val, hp]; exact hc))).elim
  · rfl

end LinearizedSyntacticObject

/-- The linearized trace a moved object leaves, `SyntacticObject.headTrace` with its order. -/
def SyntacticObject.traceLinearized (s : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) : LinearizedSyntacticObject :=
  (τ s).elim LinearizedSyntacticObject.trace LinearizedSyntacticObject.traceOf

@[simp] theorem SyntacticObject.toSyntacticObject_traceLinearized (s : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token) :
    (s.traceLinearized τ).toSyntacticObject = s.headTrace τ := by
  unfold traceLinearized headTrace; cases τ s <;> rfl

theorem SyntacticObject.traceLinearized_val (s : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token) :
    (s.traceLinearized τ).val = .node (.inr (τ s)) [] := by
  unfold traceLinearized; cases τ s <;> rfl

theorem LinearizedSyntacticObject.yield_replace_add_yield {p s : LinearizedSyntacticObject}
    {m : SyntacticObject} (τ : SyntacticObject → Option LexicalItem.Token)
    (hp : p.toSyntacticObject.yield.Nodup) (hs : p.find? m = some s) :
    (p.replace m (m.traceLinearized τ)).toSyntacticObject.yield + s.toSyntacticObject.yield =
      p.toSyntacticObject.yield := by
  obtain ⟨s', -, hs', rfl⟩ := Option.pmap_eq_some_iff.1 (by rwa [find?] at hs)
  refine filterMap_leaves_replaceIf_add _ _ (L := m.yield) (fun u hu ↦ ?_) ?_ hp
    (mem_outerMatches_of_find? hs')
  · rw [← UnorderedTree.leaves_mk, hu]
    rfl
  · rw [SyntacticObject.traceLinearized_val]
    rfl

theorem SyntacticObject.not_sisters_of_toLinearizedLeaf? {s x z : SyntacticObject}
    {p : LinearizedSyntacticObject} (hs : s.toLinearizedLeaf? = some p) : ¬ Sisters s x z := by
  rintro ⟨w, hw, hwx, -, -⟩
  rcases s.exists_form with ⟨tok, rfl⟩ | rfl | ⟨tok, rfl⟩ | ⟨l, r, rfl⟩
  · rw [terms_leaf, Multiset.mem_singleton] at hw
    subst hw
    simp [ImmediatelyContains, leaf_val] at hwx
  · rw [terms_trace, Multiset.mem_singleton] at hw
    subst hw
    simp [ImmediatelyContains, trace_val] at hwx
  · rw [terms_traceOf, Multiset.mem_singleton] at hw
    subst hw
    simp [ImmediatelyContains, traceOf_val] at hwx
  · simp [toLinearizedLeaf?, merge_val] at hs

end Minimalist
