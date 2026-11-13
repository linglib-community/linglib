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
mover's occurrences replaced by the trace of its head (`headTrace`). The planar objects carry
the same replacement, commuting with forgetting the order (`toSyntacticObject_replace`).

## Main definitions

* `Minimalist.SyntacticObject.subst`, `Minimalist.SyntacticObject.replace`
* `Minimalist.SyntacticObject.headTrace`, `Minimalist.SyntacticObject.deleteAccessible`
* `Minimalist.PlanarSyntacticObject.find?`, `Minimalist.PlanarSyntacticObject.replace`
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject

namespace PlanarSyntacticObject

/-- Substitution on the syntactic object a planar object presents. -/
def substAux (f : SyntacticObject → Option SyntacticObject) :
    PlanarSyntacticObject → SyntacticObject
  | .of x => (f (FreeCommMagma.of x)).getD (FreeCommMagma.of x)
  | .mul l r => (f (toSyntacticObject l * toSyntacticObject r)).getD
      (substAux f l * substAux f r)

theorem substAux_eq_of_commCon (f : SyntacticObject → Option SyntacticObject)
    {p q : PlanarSyntacticObject} (h : Magma.commCon (FreeMagma (Leaf LexicalItem.Token)) p q) :
    substAux f p = substAux f q := by
  induction h with
  | of x y h =>
    obtain ⟨a, b, rfl, rfl⟩ := h
    show (f (_ * _)).getD (_ * _) = (f (_ * _)).getD (_ * _)
    rw [mul_comm (toSyntacticObject a), mul_comm (substAux f a)]
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | @mul w x y z h₁ h₂ ih₁ ih₂ =>
    show (f (toSyntacticObject w * toSyntacticObject y)).getD (substAux f w * substAux f y) =
      (f (toSyntacticObject x * toSyntacticObject z)).getD (substAux f x * substAux f z)
    rw [ih₁, ih₂, show toSyntacticObject w = toSyntacticObject x from
        FreeMagma.toFreeCommMagma_eq_toFreeCommMagma.2 h₁,
      show toSyntacticObject y = toSyntacticObject z from
        FreeMagma.toFreeCommMagma_eq_toFreeCommMagma.2 h₂]

end PlanarSyntacticObject

namespace SyntacticObject

/-- Substitute `f u` for every outermost term `u` of `s` on which `f` is defined, simultaneously. -/
def subst (f : SyntacticObject → Option SyntacticObject) (s : SyntacticObject) : SyntacticObject :=
  Quotient.liftOn s (PlanarSyntacticObject.substAux f)
    fun _ _ h ↦ PlanarSyntacticObject.substAux_eq_of_commCon f h

variable {f g : SyntacticObject → Option SyntacticObject}

@[simp] theorem subst_merge (f : SyntacticObject → Option SyntacticObject)
    (l r : SyntacticObject) :
    (merge l r).subst f = (f (merge l r)).getD (merge (l.subst f) (r.subst f)) := by
  obtain ⟨l, rfl⟩ := PlanarSyntacticObject.toSyntacticObject_surjective l
  obtain ⟨r, rfl⟩ := PlanarSyntacticObject.toSyntacticObject_surjective r
  rfl

theorem subst_of_toUnorderedTree_eq_leaf {s : SyntacticObject} {a : Vertex} (hs : s.toUnorderedTree
    = UnorderedTree.leaf a)
    (f : SyntacticObject → Option SyntacticObject) : s.subst f = (f s).getD s := by
  rcases exists_form s with ⟨b, rfl⟩ | rfl | ⟨b, rfl⟩ | ⟨l, r, rfl⟩
  · rfl
  · rfl
  · rfl
  · have := congrArg UnorderedTree.children hs
    simp [UnorderedTree.leaf] at this

private theorem subst_fun_val (f : SyntacticObject → Option SyntacticObject) (s : SyntacticObject) :
    (if h : IsSyntacticObject s.toUnorderedTree then (f (ofUnorderedTree s.toUnorderedTree h)).map
        toUnorderedTree else none) =
      (f s).map toUnorderedTree := by
  simp [s.isSyntacticObject_toUnorderedTree]

private theorem toUnorderedTree_getD (o : Option SyntacticObject) (d : SyntacticObject) :
    (o.getD d).toUnorderedTree = (o.map toUnorderedTree).getD d.toUnorderedTree := by
  cases o <;> rfl

private theorem toUnorderedTree_subst (f : SyntacticObject → Option SyntacticObject) (s :
    SyntacticObject) :
    (s.subst f).toUnorderedTree = UnorderedTree.subst (fun u ↦
      if h : IsSyntacticObject u then (f (ofUnorderedTree u
          h)).map toUnorderedTree else none) s.toUnorderedTree := by
  induction s using ind with
  | leaf tok =>
    rw [subst_of_toUnorderedTree_eq_leaf (toUnorderedTree_leaf tok), toUnorderedTree_getD, ←
        subst_fun_val, toUnorderedTree_leaf,
      UnorderedTree.subst_leaf]
  | trace =>
    rw [subst_of_toUnorderedTree_eq_leaf toUnorderedTree_trace, toUnorderedTree_getD, ←
        subst_fun_val, toUnorderedTree_trace,
      UnorderedTree.subst_leaf]
  | traceOf tok =>
    rw [subst_of_toUnorderedTree_eq_leaf (toUnorderedTree_traceOf tok), toUnorderedTree_getD, ←
        subst_fun_val, toUnorderedTree_traceOf,
      UnorderedTree.subst_leaf]
  | merge l r ihl ihr =>
    rw [subst_merge, toUnorderedTree_getD, ← subst_fun_val, toUnorderedTree_merge,
        toUnorderedTree_merge, ihl, ihr,
      UnorderedTree.subst_node_pair]

theorem subst_congr {s : SyntacticObject} (h : ∀ u ∈ s.terms, f u = g u) :
    s.subst f = s.subst g := by
  apply toUnorderedTree_injective
  rw [toUnorderedTree_subst, toUnorderedTree_subst]
  refine UnorderedTree.subst_congr fun u hu ↦ ?_
  have hu' := isSyntacticObject_of_mem_subtrees s u hu
  rw [dite_eq_left hu', dite_eq_left hu',
    h (ofUnorderedTree u hu') ((toUnorderedTree_mem_subtrees (S := ofUnorderedTree u hu')).1 (by rwa
        [toUnorderedTree_ofUnorderedTree]))]

theorem subst_eq_self {s : SyntacticObject} (h : ∀ u ∈ s.terms, ∀ r, f u = some r → r = u) :
    s.subst f = s := by
  apply toUnorderedTree_injective
  rw [toUnorderedTree_subst]
  refine UnorderedTree.subst_eq_self fun u hu r hr ↦ ?_
  have hu' := isSyntacticObject_of_mem_subtrees s u hu
  rw [dite_eq_left hu', Option.map_eq_some_iff] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  exact (congrArg toUnorderedTree (h (ofUnorderedTree u hu') ((toUnorderedTree_mem_subtrees (S :=
      ofUnorderedTree u hu')).1
    (by rwa
        [toUnorderedTree_ofUnorderedTree])) r' hr')).trans (toUnorderedTree_ofUnorderedTree u hu')

theorem subst_of_forall_eq_none {s : SyntacticObject} (h : ∀ u ∈ s.terms, f u = none) :
    s.subst f = s :=
  subst_eq_self fun u hu r hr ↦ by simp [h u hu] at hr

/-! ### Replacement -/

/-- Replace every subterm of `s` equal to `target` by `replacement`. -/
def replace (s target replacement : SyntacticObject) : SyntacticObject :=
  s.subst fun u ↦ if u = target then some replacement else none

@[simp] theorem toUnorderedTree_replace (s target replacement : SyntacticObject) :
    (replace s target replacement).toUnorderedTree
      =
          UnorderedTree.replace target.toUnorderedTree replacement.toUnorderedTree s.toUnorderedTree
              := by
  rw [replace, toUnorderedTree_subst, UnorderedTree.replace]
  refine UnorderedTree.subst_congr fun u hu ↦ ?_
  have hu' := isSyntacticObject_of_mem_subtrees s u hu
  rw [dite_eq_left hu']
  by_cases hut : u = target.toUnorderedTree
  · rw [ite_eq_left (toUnorderedTree_injective ((toUnorderedTree_ofUnorderedTree u hu').trans hut) :
      ofUnorderedTree u hu' = target),
      ite_eq_left hut]
    rfl
  · rw [ite_eq_right fun h ↦ hut ((toUnorderedTree_ofUnorderedTree u hu').symm.trans (congrArg
      toUnorderedTree h)),
      ite_eq_right hut]
    rfl

@[simp] theorem replace_self (target replacement : SyntacticObject) :
    replace target target replacement = replacement :=
  toUnorderedTree_injective (by rw [toUnorderedTree_replace, UnorderedTree.replace_self])

@[simp] theorem replace_self_self (target s : SyntacticObject) : s.replace target target = s :=
  toUnorderedTree_injective (by rw [toUnorderedTree_replace, UnorderedTree.replace_self_self])

theorem replace_of_notMem_terms {s target replacement : SyntacticObject} (h : target ∉ s.terms) :
    s.replace target replacement = s :=
  toUnorderedTree_injective <| by
    rw [toUnorderedTree_replace, UnorderedTree.replace_of_notMem_subtrees (by rwa
        [toUnorderedTree_mem_subtrees])]

theorem replace_merge_of_ne {l r target replacement : SyntacticObject} (h : merge l r ≠ target) :
    replace (merge l r) target replacement
      = merge (replace l target replacement) (replace r target replacement) := by
  rw [replace, subst_merge, ite_eq_right h]
  rfl

theorem replace_of_toUnorderedTree_eq_leaf {s target replacement : SyntacticObject} {a : Vertex}
    (hs : s.toUnorderedTree = UnorderedTree.leaf a) (h : s ≠ target) :
        s.replace target replacement = s := by
  rw [replace, subst_of_toUnorderedTree_eq_leaf hs, ite_eq_right h]
  rfl

/-- Replacing `target` keeps what an object contains apart from `target`: a term that neither
lies inside `target` nor holds it. -/
theorem Contains.replace {s x target replacement : SyntacticObject} (h : Contains s x)
    (hx : x ∉ target.terms) (ht : target ∉ x.terms) :
    Contains (s.replace target replacement) x := by
  induction s using ind with
  | leaf a => simp at h
  | trace => simp at h
  | traceOf a => simp at h
  | merge l r ihl ihr =>
    have hne : merge l r ≠ target := fun e ↦ hx (e ▸ mem_terms.2 h.to_reflTransGen)
    rw [replace_merge_of_ne hne, contains_merge]
    refine (contains_merge.1 h).imp (fun h ↦ ?_) fun h ↦ ?_ <;>
      rcases containsOrEq_iff_eq_or_contains.1 h with rfl | h
    · rw [replace_of_notMem_terms ht]; exact h
    · exact (ihl h).to_reflTransGen
    · rw [replace_of_notMem_terms ht]; exact h
    · exact (ihr h).to_reflTransGen

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
theorem toUnorderedTree_headTrace (s : SyntacticObject) (τ : SyntacticObject → Option
    LexicalItem.Token) :
    (s.headTrace τ).toUnorderedTree = UnorderedTree.leaf (Sum.inr (τ s)) := by
  unfold headTrace; cases τ s <;> rfl

/-- Replacing the occurrences of a term by a silent object removes its tokens and no others, in
an object that pronounces no token twice. -/
theorem yield_replace_add_yield {s m t : SyntacticObject} (hs : s.yield.Nodup)
    (hm : m ∈ s.terms) (ht : t.yield = 0) : (s.replace m t).yield + m.yield = s.yield := by
  induction s using ind with
  | leaf a =>
    obtain rfl : m = leaf a := by simpa using hm
    rw [replace_self, ht, zero_add]
  | trace =>
    obtain rfl : m = trace := by simpa using hm
    rw [replace_self, ht, zero_add]
  | traceOf a =>
    obtain rfl : m = traceOf a := by simpa using hm
    rw [replace_self, ht, zero_add]
  | merge l r ihl ihr =>
    by_cases h : merge l r = m
    · subst h; rw [replace_self, ht, zero_add]
    · rw [yield_merge] at hs
      obtain ⟨hl, hr, hdisj⟩ := Multiset.nodup_add.1 hs
      have hm' : m ∈ l.terms ∨ m ∈ r.terms := by
        rw [terms_merge, Multiset.mem_cons, Multiset.mem_add] at hm
        exact hm.resolve_left fun e ↦ h e.symm
      rw [replace_merge_of_ne h, yield_merge, yield_merge]
      by_cases hml : m ∈ l.terms <;> by_cases hmr : m ∈ r.terms
      · have h0 : m.yield = 0 := Multiset.eq_zero_of_forall_notMem fun a ha ↦
          Multiset.disjoint_left.1 hdisj (Multiset.mem_of_le (yield_le_of_mem_terms hml) ha)
            (Multiset.mem_of_le (yield_le_of_mem_terms hmr) ha)
        have el := ihl hl hml
        have er := ihr hr hmr
        rw [h0, add_zero] at el er ⊢
        rw [el, er]
      · rw [replace_of_notMem_terms hmr, add_right_comm, ihl hl hml]
      · rw [replace_of_notMem_terms hml, add_assoc, ihr hr hmr]
      · exact (hm'.elim hml hmr).elim

theorem yield_headTrace (s : SyntacticObject) (τ : SyntacticObject → Option LexicalItem.Token) :
    (s.headTrace τ).yield = 0 := by
  unfold headTrace; cases τ s <;> rfl

section Map

variable {f : LexicalItem.Token → LexicalItem.Token}

/-- Replacement commutes with an injective relabelling. -/
theorem replace_map (hf : Function.Injective f) (s target replacement : SyntacticObject) :
    (s.replace target replacement).map f =
      (s.map f).replace (target.map f) (replacement.map f) := by
  have hmem (x : SyntacticObject) : target.map f ∈ (x.map f).terms ↔ target ∈ x.terms := by
    rw [terms_map, Multiset.mem_map_of_injective (map_injective hf)]
  have leafCase (x : SyntacticObject) (hx : x.terms = {x}) :
      (x.replace target replacement).map f =
        (x.map f).replace (target.map f) (replacement.map f) := by
    by_cases h : x = target
    · subst h; rw [replace_self, replace_self]
    · have hn : target ∉ x.terms := by rw [hx, Multiset.mem_singleton]; exact fun e ↦ h e.symm
      rw [replace_of_notMem_terms hn, replace_of_notMem_terms ((hmem x).not.2 hn)]
  induction s using ind with
  | leaf a => exact leafCase _ (terms_leaf a)
  | trace => exact leafCase _ terms_trace
  | traceOf a => exact leafCase _ (terms_traceOf a)
  | merge l r ihl ihr =>
    by_cases h : merge l r = target
    · subst h; rw [replace_self, replace_self]
    · rw [replace_merge_of_ne h, map_merge, map_merge,
        replace_merge_of_ne fun e ↦ h (map_injective hf (by rwa [map_merge])), ihl, ihr]

end Map

/-- The remainder `T/mover`, the current object with the mover's occurrences replaced by the trace
    of its head under `τ`. -/
def deleteAccessible (mover current : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) : SyntacticObject :=
  current.replace mover (mover.headTrace τ)

@[simp] theorem toUnorderedTree_deleteAccessible (mover current : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token) :
    (deleteAccessible mover current τ).toUnorderedTree
      = UnorderedTree.replace mover.toUnorderedTree (mover.headTrace
          τ).toUnorderedTree current.toUnorderedTree :=
  toUnorderedTree_replace _ _ _

end SyntacticObject

/-! ### Planar leaves -/

/-- The planar form of a leaf object, which has only one; `none` on a merged object. -/
def SyntacticObject.toPlanarLeaf? (s : SyntacticObject) : Option PlanarSyntacticObject :=
  match s.toUnorderedTree.value with
  | .inl (some tok) => some (.leaf tok)
  | .inl none => none
  | .inr none => some .trace
  | .inr (some tok) => some (.traceOf tok)

theorem SyntacticObject.toSyntacticObject_of_toPlanarLeaf? {s : SyntacticObject}
    {p : PlanarSyntacticObject} (h : s.toPlanarLeaf? = some p) :
    p.toSyntacticObject = s := by
  rcases s.exists_form with ⟨tok, rfl⟩ | rfl | ⟨tok, rfl⟩ | ⟨l, r, rfl⟩ <;>
    simp [toPlanarLeaf?, toUnorderedTree_merge] at h <;> subst h <;> rfl

/-! ### Occurrences in planar objects -/

namespace PlanarSyntacticObject

/-- The leftmost, outermost subtree of `p` projecting to `target`. -/
def find? (p : PlanarSyntacticObject) (target : SyntacticObject) :
    Option PlanarSyntacticObject :=
  (p.toRoseTree.subtrees.find? (mk · = target.toUnorderedTree)).pmap (p := (mk · =
      target.toUnorderedTree))
    (fun s hs ↦ ofRoseTree s (hs.symm ▸ target.isSyntacticObject_toUnorderedTree)) fun _ h ↦ by
      simpa using List.find?_some h

theorem toSyntacticObject_find? {p s : PlanarSyntacticObject} {target : SyntacticObject}
    (h : p.find? target = some s) : s.toSyntacticObject = target := by
  obtain ⟨t, ht, -, rfl⟩ := Option.pmap_eq_some_iff.1 (by rwa [find?] at h)
  exact SyntacticObject.toUnorderedTree_injective
    (by rw [toUnorderedTree_toSyntacticObject, toRoseTree_ofRoseTree]; exact ht)

/-- Every subtree of `p` projecting to `target` replaced by `rep`. -/
def replace (p : PlanarSyntacticObject) (target : SyntacticObject)
    (rep : PlanarSyntacticObject) : PlanarSyntacticObject :=
  ofRoseTree (replaceIf (mk · = target.toUnorderedTree) rep.toRoseTree p.toRoseTree) (by
    rw [mk_replaceIf]
    exact toUnorderedTree_replace p.toSyntacticObject target rep.toSyntacticObject ▸
      (p.toSyntacticObject.replace target rep.toSyntacticObject).isSyntacticObject_toUnorderedTree)

@[simp] theorem toRoseTree_replace (p : PlanarSyntacticObject) (target : SyntacticObject)
    (rep : PlanarSyntacticObject) :
    (p.replace target rep).toRoseTree = replaceIf (mk · =
        target.toUnorderedTree) rep.toRoseTree p.toRoseTree :=
  toRoseTree_ofRoseTree _ _

@[simp] theorem toSyntacticObject_replace (p : PlanarSyntacticObject) (target : SyntacticObject)
    (rep : PlanarSyntacticObject) :
    (p.replace target rep).toSyntacticObject
      = p.toSyntacticObject.replace target rep.toSyntacticObject :=
  SyntacticObject.toUnorderedTree_injective (by
    rw [toUnorderedTree_replace, toUnorderedTree_toSyntacticObject,
        toRoseTree_replace]; exact mk_replaceIf _ _ _)

theorem mem_terms_toSyntacticObject {p : PlanarSyntacticObject} {m : SyntacticObject} :
    m ∈ p.toSyntacticObject.terms ↔ ∃ q ∈ p.toRoseTree.subtrees, mk q = m.toUnorderedTree := by
  rw [← toUnorderedTree_mem_subtrees, toUnorderedTree_toSyntacticObject, subtrees_mk,
      unorderedSubtrees_eq_map,
    Multiset.mem_coe, List.mem_map]

theorem isSome_find?_iff {p : PlanarSyntacticObject} {m : SyntacticObject} :
    (p.find? m).isSome ↔ m ∈ p.toSyntacticObject.terms := by
  rw [mem_terms_toSyntacticObject, find?, Option.isSome_pmap, List.find?_isSome]
  simp

theorem mem_subtrees_of_find? {p s : PlanarSyntacticObject} {m : SyntacticObject}
    (h : p.find? m = some s) : s.toRoseTree ∈ p.toRoseTree.subtrees := by
  obtain ⟨t, -, ht, rfl⟩ := Option.pmap_eq_some_iff.1 (by rwa [find?] at h)
  rw [toRoseTree_ofRoseTree]
  exact List.mem_of_find?_eq_some ht

theorem replace_of_toSyntacticObject_eq {p r : PlanarSyntacticObject} {target : SyntacticObject}
    (h : p.toSyntacticObject = target) : p.replace target r = r := by
  apply toRoseTree_injective
  rw [toRoseTree_replace]
  rcases hp : p.toRoseTree with ⟨a, cs⟩
  rw [replaceIf_node]
  split_ifs with hc
  · rfl
  · exact absurd (hp ▸ congrArg SyntacticObject.toUnorderedTree h) hc

theorem replace_attach {p d r : PlanarSyntacticObject} {target : SyntacticObject} {e : Edge}
    (h : SyntacticObject.merge d.toSyntacticObject p.toSyntacticObject ≠ target) :
    (p.attach e d).replace target r = (p.replace target r).attach e (d.replace target r) := by
  have h' : (p.attach e d).toSyntacticObject ≠ target := by rwa [toSyntacticObject_attach]
  apply toRoseTree_injective
  cases e <;> simp only [toRoseTree_replace, attach, toRoseTree_merge, replaceIf_node,
      List.map_cons,
    List.map_nil] <;> split_ifs with hc <;>
    first | rfl | exact (h' (SyntacticObject.toUnorderedTree_injective hc)).elim

theorem replace_of_toRoseTree_eq_leaf {p r : PlanarSyntacticObject} {target : SyntacticObject}
    {a : Vertex} (hp : p.toRoseTree = RoseTree.leaf a) (h : p.toSyntacticObject ≠ target) :
    p.replace target r = p := by
  apply toRoseTree_injective
  simp only [toRoseTree_replace, hp, replaceIf_node, List.map_nil]
  split_ifs with hc
  · exact (h (SyntacticObject.toUnorderedTree_injective
      (by rw [toUnorderedTree_toSyntacticObject, hp]; exact hc))).elim
  · rfl

end PlanarSyntacticObject

/-- The planar trace a moved object leaves, `SyntacticObject.headTrace` with its order. -/
def SyntacticObject.tracePlanar (s : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) : PlanarSyntacticObject :=
  (τ s).elim PlanarSyntacticObject.trace PlanarSyntacticObject.traceOf

@[simp] theorem SyntacticObject.toSyntacticObject_tracePlanar (s : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token) :
    (s.tracePlanar τ).toSyntacticObject = s.headTrace τ := by
  unfold tracePlanar headTrace; cases τ s <;> rfl

theorem SyntacticObject.toRoseTree_tracePlanar (s : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token) :
    (s.tracePlanar τ).toRoseTree = .node (.inr (τ s)) [] := by
  unfold tracePlanar; cases τ s <;> rfl

theorem PlanarSyntacticObject.yield_replace_add_yield {p s : PlanarSyntacticObject}
    {m : SyntacticObject} (τ : SyntacticObject → Option LexicalItem.Token)
    (hp : p.toSyntacticObject.yield.Nodup) (hs : p.find? m = some s) :
    (p.replace m (m.tracePlanar τ)).toSyntacticObject.yield + s.toSyntacticObject.yield =
      p.toSyntacticObject.yield := by
  obtain ⟨s', hs'', hs', rfl⟩ := Option.pmap_eq_some_iff.1 (by rwa [find?] at hs)
  have e₁ : (p.replace m (m.tracePlanar τ)).toRoseTree
      = replaceIf (fun u ↦ mk u = m.toUnorderedTree) (m.tracePlanar τ).toRoseTree p.toRoseTree :=
          toRoseTree_replace _ _ _
  have e₂ := toRoseTree_ofRoseTree s' (hs''.symm ▸ m.isSyntacticObject_toUnorderedTree)
  show Multiset.filterMap _ (UnorderedTree.mk (p.replace m (m.tracePlanar τ)).toRoseTree).leaves +
    Multiset.filterMap _ (UnorderedTree.mk (ofRoseTree s' _).toRoseTree).leaves = _
  rw [e₁, e₂]
  refine filterMap_leaves_replaceIf_add _ _ (L := m.yield) (fun u hu ↦ ?_) ?_ hp
    (mem_outerMatches_of_find? hs')
  · rw [← UnorderedTree.leaves_mk, hu]
    rfl
  · rw [SyntacticObject.toRoseTree_tracePlanar]
    rfl

theorem SyntacticObject.not_sisters_of_toPlanarLeaf? {s x z : SyntacticObject}
    {p : PlanarSyntacticObject} (hs : s.toPlanarLeaf? = some p) : ¬ Sisters s x z := by
  rintro ⟨w, hw, hwx, -, -⟩
  rcases s.exists_form with ⟨tok, rfl⟩ | rfl | ⟨tok, rfl⟩ | ⟨l, r, rfl⟩
  · rw [terms_leaf, Multiset.mem_singleton] at hw
    subst hw
    simp [ImmediatelyContains, toUnorderedTree_leaf] at hwx
  · rw [terms_trace, Multiset.mem_singleton] at hw
    subst hw
    simp [ImmediatelyContains, toUnorderedTree_trace] at hwx
  · rw [terms_traceOf, Multiset.mem_singleton] at hw
    subst hw
    simp [ImmediatelyContains, toUnorderedTree_traceOf] at hwx
  · simp [toPlanarLeaf?, toUnorderedTree_merge] at hs

/-! ### Relabelling -/

section Map

variable {f : LexicalItem.Token → LexicalItem.Token}
  {τ τ' : SyntacticObject → Option LexicalItem.Token}

theorem SyntacticObject.toPlanarLeaf?_map (f : LexicalItem.Token → LexicalItem.Token)
    (s : SyntacticObject) :
    (s.map f).toPlanarLeaf? = s.toPlanarLeaf?.map (PlanarSyntacticObject.map f) := by
  rcases s.exists_form with ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩ | ⟨l, r, rfl⟩ <;>
    simp [toPlanarLeaf?, toUnorderedTree_merge]

theorem SyntacticObject.headTrace_map (hτ : ∀ s, τ' (s.map f) = (τ s).map f)
    (s : SyntacticObject) : (s.headTrace τ).map f = (s.map f).headTrace τ' := by
  unfold headTrace; rw [hτ]; cases τ s <;> simp

theorem SyntacticObject.tracePlanar_map (hτ : ∀ s, τ' (s.map f) = (τ s).map f)
    (s : SyntacticObject) : (s.tracePlanar τ).map f = (s.map f).tracePlanar τ' := by
  unfold tracePlanar; rw [hτ]; cases τ s <;> simp

namespace PlanarSyntacticObject

theorem map_toRoseTree_find? (p : PlanarSyntacticObject) (t : SyntacticObject) :
    (p.find? t).map toRoseTree = p.toRoseTree.subtrees.find? (mk · = t.toUnorderedTree) := by
  simp only [find?, Option.map_pmap, toRoseTree_ofRoseTree, Option.pmap_eq_map, Option.map_id']

theorem find?_map (hf : Function.Injective f) (p : PlanarSyntacticObject)
    (t : SyntacticObject) : (p.map f).find? (t.map f) = (p.find? t).map (map f) := by
  have hv := UnorderedTree.map_injective (SyntacticObject.Vertex.map_injective hf)
  apply Option.map_injective toRoseTree_injective
  rw [map_toRoseTree_find?, Option.map_map, toRoseTree_map, RoseTree.subtrees_map, List.find?_map,
    SyntacticObject.toUnorderedTree_map]
  have hcomp : toRoseTree ∘ map f = RoseTree.map (SyntacticObject.Vertex.map f) ∘ toRoseTree :=
    funext fun q ↦ toRoseTree_map f q
  rw [hcomp, ← Option.map_map, map_toRoseTree_find?]
  congr 2
  funext q
  simp only [Function.comp_apply, ← UnorderedTree.map_mk, hv.eq_iff]

theorem replace_map (hf : Function.Injective f) (p : PlanarSyntacticObject)
    (t : SyntacticObject) (r : PlanarSyntacticObject) :
    (p.replace t r).map f = (p.map f).replace (t.map f) (r.map f) :=
  toRoseTree_injective <| by
    rw [toRoseTree_map, toRoseTree_replace, toRoseTree_replace, toRoseTree_map, toRoseTree_map]
    exact RoseTree.map_replaceIf _ _ (fun s ↦ by
      rw [SyntacticObject.toUnorderedTree_map, ← UnorderedTree.map_mk,
        (UnorderedTree.map_injective (SyntacticObject.Vertex.map_injective
            hf)).eq_iff]) p.toRoseTree

end PlanarSyntacticObject

end Map

end Minimalist
