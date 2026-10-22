/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.UnorderedTree.Replace
public import Linglib.Syntax.Minimalist.SyntacticObject.Build
public import Linglib.Syntax.Minimalist.SyntacticObject.Selection
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

/-- Substitution preserves well-formedness. -/
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

/-- At a node other than the target, substitution recurses into both daughters. -/
theorem replace_merge_of_ne {l r target replacement : SyntacticObject} (h : merge l r ≠ target) :
    replace (merge l r) target replacement
      = merge (replace l target replacement) (replace r target replacement) := by
  apply Subtype.ext
  rw [replace_val, merge_val, UnorderedTree.replace_node_pair, ite_eq_right, merge_val, replace_val,
    replace_val]
  rw [← merge_val]
  exact fun heq => h (Subtype.ext heq)

/-- A leaf other than the target is kept. -/
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

/-! ### Planar leaves -/

/-- The planar form of a leaf object, which has only one; `none` on a merged object. -/
def SyntacticObject.toPlanarLeaf? (s : SyntacticObject) : Option PlanarSyntacticObject :=
  match s.val.value with
  | .inl (some tok) => some (.leaf tok)
  | .inl none => none
  | .inr none => some .trace
  | .inr (some tok) => some (.traceOf tok)

/-- A planar leaf forgets to the object it came from. -/
theorem SyntacticObject.toSyntacticObject_of_toPlanarLeaf? {s : SyntacticObject}
    {p : PlanarSyntacticObject} (h : s.toPlanarLeaf? = some p) : p.toSyntacticObject = s := by
  rcases s.exists_form with ⟨tok, rfl⟩ | rfl | ⟨tok, rfl⟩ | ⟨l, r, rfl⟩ <;>
    simp [toPlanarLeaf?, merge_val] at h <;> subst h <;> rfl

/-! ### Occurrences in planar objects -/

namespace PlanarSyntacticObject

/-- The leftmost, outermost subtree of `p` projecting to `target`. -/
def find? (p : PlanarSyntacticObject) (target : SyntacticObject) : Option PlanarSyntacticObject :=
  (p.val.subtrees.find? (mk · = target.val)).pmap (p := (mk · = target.val))
    (fun s hs ↦ ⟨s, hs.symm ▸ target.2⟩) fun _ h ↦ by simpa using List.find?_some h

theorem toSyntacticObject_find? {p s : PlanarSyntacticObject} {target : SyntacticObject}
    (h : p.find? target = some s) : s.toSyntacticObject = target := by
  obtain ⟨t, ht, -, rfl⟩ := Option.pmap_eq_some_iff.1 (by rwa [find?] at h)
  exact Subtype.ext ht

/-- Every subtree of `p` projecting to `target` replaced by `rep`. -/
def replace (p : PlanarSyntacticObject) (target : SyntacticObject)
    (rep : PlanarSyntacticObject) : PlanarSyntacticObject :=
  ⟨replaceIf (mk · = target.val) rep.val p.val, by
    rw [mk_replaceIf]
    exact isSyntacticObject_replace target rep.toSyntacticObject p.toSyntacticObject⟩

/-- Replacement forgets to substitution in the syntactic object. -/
@[simp] theorem toSyntacticObject_replace (p : PlanarSyntacticObject) (target : SyntacticObject)
    (rep : PlanarSyntacticObject) :
    (p.replace target rep).toSyntacticObject
      = p.toSyntacticObject.replace target rep.toSyntacticObject :=
  Subtype.ext (mk_replaceIf _ _ _)

/-- The terms of a planar object's object are the projections of its planar subtrees. -/
theorem mem_terms_toSyntacticObject {p : PlanarSyntacticObject} {m : SyntacticObject} :
    m ∈ p.toSyntacticObject.terms ↔ ∃ q ∈ p.val.subtrees, mk q = m.val := by
  rw [← val_mem_subtrees, toSyntacticObject_val, subtrees_mk, unorderedSubtrees_eq_map,
    Multiset.mem_coe, List.mem_map]

/-- An occurrence is found exactly when the target is a term. -/
theorem isSome_find?_iff {p : PlanarSyntacticObject} {m : SyntacticObject} :
    (p.find? m).isSome ↔ m ∈ p.toSyntacticObject.terms := by
  rw [mem_terms_toSyntacticObject, find?, Option.isSome_pmap, List.find?_isSome]
  simp

/-- The occurrence found is a planar subtree. -/
theorem mem_subtrees_of_find? {p s : PlanarSyntacticObject} {m : SyntacticObject}
    (h : p.find? m = some s) : s.val ∈ p.val.subtrees := by
  obtain ⟨t, -, ht, rfl⟩ := Option.pmap_eq_some_iff.1 (by rwa [find?] at h)
  exact List.mem_of_find?_eq_some ht

/-- Replacing at the root yields the replacement. -/
theorem replace_of_toSyntacticObject_eq {p r : PlanarSyntacticObject} {target : SyntacticObject}
    (h : p.toSyntacticObject = target) : p.replace target r = r := by
  obtain ⟨⟨a, cs⟩, hp⟩ := p
  apply Subtype.ext
  simp only [replace, replaceIf_node]
  split_ifs with hc
  · rfl
  · exact absurd (congrArg Subtype.val h) hc

/-- Away from the root, replacement recurses into the daughters. -/
theorem replace_attach {p d r : PlanarSyntacticObject} {target : SyntacticObject} {e : Edge}
    (h : SyntacticObject.merge d.toSyntacticObject p.toSyntacticObject ≠ target) :
    (p.attach e d).replace target r = (p.replace target r).attach e (d.replace target r) := by
  have h' : (p.attach e d).toSyntacticObject ≠ target := by rwa [toSyntacticObject_attach]
  apply Subtype.ext
  cases e <;> simp only [replace, attach, merge_val, replaceIf_node, List.map_cons,
    List.map_nil] <;> split_ifs with hc <;> first | rfl | exact (h' (Subtype.ext hc)).elim

/-- A leaf other than the target is kept. -/
theorem replace_of_val_eq_leaf {p r : PlanarSyntacticObject} {target : SyntacticObject}
    {a : Vertex} (hp : p.val = RoseTree.leaf a) (h : p.toSyntacticObject ≠ target) :
    p.replace target r = p := by
  apply Subtype.ext
  simp only [replace, hp, replaceIf_node, List.map_nil]
  split_ifs with hc
  · exact (h (Subtype.ext (by rw [toSyntacticObject_val, hp]; exact hc))).elim
  · rfl

end PlanarSyntacticObject

/-- The planar trace a moved object leaves, `SyntacticObject.headTrace` with its order. -/
def SyntacticObject.tracePlanar (s : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) : PlanarSyntacticObject :=
  (τ s).elim PlanarSyntacticObject.trace PlanarSyntacticObject.traceOf

/-- The planar trace of `s` is the trace leaf of its label. -/
theorem SyntacticObject.tracePlanar_val (s : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token) :
    (s.tracePlanar τ).val = .node (.inr (τ s)) [] := by
  unfold tracePlanar; cases τ s <;> rfl

/-- Raising the occurrence of `m` that `find?` locates, with its occurrences replaced by its trace,
keeps the pronounced tokens when none is pronounced twice. -/
theorem PlanarSyntacticObject.yield_replace_add_yield {p s : PlanarSyntacticObject}
    {m : SyntacticObject} (τ : SyntacticObject → Option LexicalItem.Token)
    (hp : p.toSyntacticObject.yield.Nodup) (hs : p.find? m = some s) :
    (p.replace m (m.tracePlanar τ)).toSyntacticObject.yield + s.toSyntacticObject.yield =
      p.toSyntacticObject.yield := by
  obtain ⟨s', -, hs', rfl⟩ := Option.pmap_eq_some_iff.1 (by rwa [find?] at hs)
  refine filterMap_leaves_replaceIf_add _ _ (L := m.yield) (fun u hu ↦ ?_) ?_ hp
    (mem_outerMatches_of_find? hs')
  · rw [← UnorderedTree.leaves_mk, hu]
    rfl
  · rw [SyntacticObject.tracePlanar_val]
    rfl

/-- A lexical leaf or trace has no sisters inside it. -/
theorem SyntacticObject.not_sisters_of_toPlanarLeaf? {s x z : SyntacticObject}
    {p : PlanarSyntacticObject} (hs : s.toPlanarLeaf? = some p) : ¬ Sisters s x z := by
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
  · simp [toPlanarLeaf?, merge_val] at hs

end Minimalist
