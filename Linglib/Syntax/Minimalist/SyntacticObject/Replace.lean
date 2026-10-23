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

`SyntacticObject.replace s target replacement` substitutes every subterm of `s` equal to
`target` by `replacement`; it is `UnorderedTree.replace` closed under well-formedness, which holds
because substitution preserves the arity of every vertex. The copy-theory use is
`s.replace mover trace`, leaving a trace where a mover was. This is a structural operation:
the Merge-algebraic Internal Merge is the coproduct composition of `Merge/Internal.lean`, with
traces as cut remainders and chains held at the workspace level, and `replace` supports the
transformational view that study files are written in. It is noncomputable; concrete cases
reduce by `replace_self`, `replace_merge_of_ne`, and the leaf lemmas.

## Main definitions

* `Minimalist.SyntacticObject.replace`
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject

theorem isSyntacticObject_replace (target replacement s : SyntacticObject) :
    IsSyntacticObject (UnorderedTree.replace target.val replacement.val s.val) := by
  induction s using ind with
  | leaf tok =>
    rw [show (SyntacticObject.leaf tok).val = UnorderedTree.leaf (Vertex.lex tok) from rfl,
      UnorderedTree.replace_leaf]
    split
    · exact replacement.2
    · exact (SyntacticObject.leaf tok).2
  | trace =>
    rw [show trace.val = UnorderedTree.leaf (Sum.inr none) from rfl, UnorderedTree.replace_leaf]
    split
    · exact replacement.2
    · exact trace.2
  | traceOf tok =>
    rw [show (traceOf tok).val = UnorderedTree.leaf (Sum.inr (some tok)) from rfl,
      UnorderedTree.replace_leaf]
    split
    · exact replacement.2
    · exact (traceOf tok).2
  | merge l r ihl ihr =>
    rw [merge_val, UnorderedTree.replace_node_pair]
    split
    · exact replacement.2
    · exact (isSyntacticObject_merge_iff _ _).2 ⟨ihl, ihr⟩

namespace SyntacticObject

/-- Replace every subterm of `s` equal to `target` by `replacement`. -/
noncomputable def replace (s target replacement : SyntacticObject) : SyntacticObject :=
  ⟨UnorderedTree.replace target.val replacement.val s.val,
    isSyntacticObject_replace target replacement s⟩

@[simp] theorem replace_val (s target replacement : SyntacticObject) :
    (replace s target replacement).val
      = UnorderedTree.replace target.val replacement.val s.val := rfl

@[simp] theorem replace_self (target replacement : SyntacticObject) :
    replace target target replacement = replacement :=
  Subtype.ext (by rw [replace_val, UnorderedTree.replace_self])

theorem replace_merge_of_ne {l r target replacement : SyntacticObject} (h : merge l r ≠ target) :
    replace (merge l r) target replacement
      = merge (replace l target replacement) (replace r target replacement) := by
  apply Subtype.ext
  rw [replace_val, merge_val, UnorderedTree.replace_node_pair, ite_eq_right, merge_val, replace_val,
    replace_val]
  rw [← merge_val]
  exact fun heq => h (Subtype.ext heq)

theorem replace_of_val_eq_leaf {s target replacement : SyntacticObject} {a : Vertex}
    (hs : s.val = UnorderedTree.leaf a) (h : s ≠ target) : s.replace target replacement = s := by
  apply Subtype.ext
  rw [replace_val, hs, UnorderedTree.replace_leaf]
  split_ifs with hc
  · exact (h (Subtype.ext (hs.trans hc))).elim
  · rfl

/-- Moving the daughter `r` out of `[l r]` and leaving a trace yields `[l′ t]`, with `l′` the
    substituted left daughter; a tree is never its own daughter, taken here as a hypothesis. -/
example (l r : SyntacticObject) (h : merge l r ≠ r) :
    replace (merge l r) r trace = merge (replace l r trace) trace := by
  rw [replace_merge_of_ne h, replace_self]

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
    exact isSyntacticObject_replace target rep.toSyntacticObject p.toSyntacticObject⟩

@[simp] theorem toSyntacticObject_replace (p : LinearizedSyntacticObject) (target : SyntacticObject)
    (rep : LinearizedSyntacticObject) :
    (p.replace target rep).toSyntacticObject
      = p.toSyntacticObject.replace target rep.toSyntacticObject :=
  Subtype.ext (mk_replaceIf _ _ _)

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
