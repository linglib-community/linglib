/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Linglib.Core.Data.Multiset.ZeroCons
public import Linglib.Core.Data.UnorderedTree.Basic
public import Linglib.Core.Data.UnorderedTree.Licensed
public import Linglib.Syntax.Minimalist.SyntacticObject.Basic

/-!
# The trees of syntactic objects

A planar syntactic object has an ordered tree and a syntactic object an unordered one, with a
lexical item or a trace at each leaf and no label at the other vertices. An object is [determined
by its tree](##Minimalist.SyntacticObject.toUnorderedTree_injective), and the trees that arise are
[the well-formed ones](##Minimalist.SyntacticObject.unorderedTreeEquiv), in which a leaf has no
daughters and an unlabelled vertex has two, so an object can be [read back off a well-formed
tree](##Minimalist.SyntacticObject.ofUnorderedTree). Positions, the coproducts on forests and marked
copies work on these trees.

## Implementation notes

* The trees are over `Vertex L`, an option of a leaf label on either side: on the left a lexical
  leaf or the unlabelled internal vertex, on the right a trace, the convention of the trace
  coproduct.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree

/-- A vertex carries structure on the left, a leaf of the lexical alphabet `L` or the bare
    internal label, and a trace on the right, index-free or of a label. -/
abbrev SyntacticObject.Vertex (L : Type := LexicalItem.Token) : Type := Option L ⊕ Option L

namespace SyntacticObject

variable {L L' L'' : Type}

/-- The lexical leaf `a`. -/
@[match_pattern] abbrev Vertex.lex (a : L) : Vertex L := .inl (some a)

/-- The bare label of a binary internal node. -/
@[match_pattern] abbrev Vertex.bare : Vertex L := .inl none

/-- The index-free trace. -/
@[match_pattern] abbrev Vertex.trace : Vertex L := .inr none

/-- The trace of the leaf `a`. -/
@[match_pattern] abbrev Vertex.traceOf (a : L) : Vertex L := .inr (some a)

/-- A vertex licenses its children when a lexical leaf or a trace has none and the bare label has
two. -/
def Vertex.Licenses : Vertex L → Multiset (Vertex L) → Prop
  | .inl (some _), ks => ks = 0
  | .inl none, ks => Multiset.card ks = 2
  | .inr _, ks => ks = 0

instance : ∀ (a : Vertex L) (ks : Multiset (Vertex L)), Decidable (Vertex.Licenses a ks)
  | .inl (some _), _ => decidable_of_iff _ Multiset.card_eq_zero
  | .inl none, ks => inferInstanceAs (Decidable (Multiset.card ks = 2))
  | .inr _, _ => decidable_of_iff _ Multiset.card_eq_zero

theorem Vertex.licenses_iff_of_card_eq {a : Vertex L} {ks ls : Multiset (Vertex L)}
    (h : Multiset.card ks = Multiset.card ls) : a.Licenses ks ↔ a.Licenses ls := by
  rcases a with (_ | _) | _ <;>
    simp only [Vertex.Licenses, ← Multiset.card_eq_zero, h]

end SyntacticObject

/-- An unordered tree over `Vertex L` is a syntactic object when every vertex licenses its
    children, so that lexical leaves and traces are leaves and bare vertices are binary. -/
def IsSyntacticObject {L : Type} (t : UnorderedTree (SyntacticObject.Vertex L)) : Prop :=
  t.Licensed SyntacticObject.Vertex.Licenses

instance {L : Type} : DecidablePred (IsSyntacticObject (L := L)) :=
  fun t ↦ inferInstanceAs (Decidable (t.Licensed _))

@[simp] theorem isSyntacticObject_mk {L : Type} (t : RoseTree (SyntacticObject.Vertex L)) :
    IsSyntacticObject (UnorderedTree.mk t) ↔
      t.Licensed fun a ks ↦ SyntacticObject.Vertex.Licenses a (ks : Multiset _) :=
  Iff.rfl

namespace SyntacticObject

variable {L L' L'' : Type}

theorem isSyntacticObject_mk_leaf {a : Vertex L} (ha : a ≠ Vertex.bare) :
    IsSyntacticObject (UnorderedTree.mk (.node a [])) := by
  refine (isSyntacticObject_mk _).mpr (licensed_node_iff.mpr ⟨?_, by simp⟩)
  match a, ha with
  | .inl (some _), _ | .inr _, _ => rfl
  | .inl none, h => exact absurd rfl h

@[simp] theorem isSyntacticObject_mk_merge (l r : RoseTree (Vertex L)) :
    IsSyntacticObject (UnorderedTree.mk (.node Vertex.bare [l, r])) ↔
      IsSyntacticObject (UnorderedTree.mk l) ∧ IsSyntacticObject (UnorderedTree.mk r) := by
  simp [licensed_node_iff, Vertex.Licenses]

theorem length_eq_zero_or_two {a : Vertex L} {cs : List (RoseTree (Vertex L))}
    (h : IsSyntacticObject (UnorderedTree.mk (.node a cs))) : cs.length = 0 ∨ cs.length = 2 := by
  have h := (licensed_node_iff.mp ((isSyntacticObject_mk _).mp h)).1
  match a with
  | .inl (some _) | .inr _ => exact .inl (by simpa [Vertex.Licenses] using congrArg Multiset.card h)
  | .inl none => exact .inr (by simpa [Vertex.Licenses] using h)

theorem eq_bare_of_ne_nil {a : Vertex L} {cs : List (RoseTree (Vertex L))}
    (h : IsSyntacticObject (UnorderedTree.mk (.node a cs))) (hcs : cs ≠ []) : a = Vertex.bare := by
  have h := (licensed_node_iff.mp ((isSyntacticObject_mk _).mp h)).1
  match a with
  | .inl none => rfl
  | .inl (some _) | .inr _ => exact absurd (by simpa [Vertex.Licenses] using h) hcs

end SyntacticObject

theorem IsSyntacticObject.isFullBinary {L : Type} {t : UnorderedTree (SyntacticObject.Vertex L)}
    (h : IsSyntacticObject t) : t.IsFullBinary :=
  UnorderedTree.Licensed.mono (R := SyntacticObject.Vertex.Licenses) (fun
    | .inl (some _), _, h | .inr _, _, h => .inl (congrArg Multiset.card h)
    | .inl none, _, h => .inr h) h

namespace SyntacticObject

namespace Leaf

variable {L L' L'' : Type}

/-- The vertex a leaf labels. -/
def toVertex : Leaf L → Vertex L
  | lex a => Vertex.lex a
  | trace => Vertex.trace
  | traceOf a => Vertex.traceOf a

theorem toVertex_injective : Function.Injective (toVertex (L := L)) := by
  rintro (a | _ | a) (b | _ | b) h <;> simp_all [toVertex]

theorem toVertex_ne_bare (x : Leaf L) : x.toVertex ≠ Vertex.bare := by
  cases x <;> simp [toVertex]

end Leaf

end SyntacticObject

namespace PlanarSyntacticObject

open SyntacticObject (Vertex Leaf isSyntacticObject_mk_leaf isSyntacticObject_mk_merge
  length_eq_zero_or_two eq_bare_of_ne_nil)

variable {L L' L'' : Type}

/-- The ordered tree of a planar object. -/
def toRoseTree : PlanarSyntacticObject L → RoseTree (Vertex L)
  | .of x => .node x.toVertex []
  | .mul l r => .node Vertex.bare [toRoseTree l, toRoseTree r]

@[simp] theorem toRoseTree_leaf (a : L) :
    (leaf a).toRoseTree = .node (Vertex.lex a) [] := rfl
@[simp] theorem toRoseTree_trace :
    (trace : PlanarSyntacticObject L).toRoseTree = .node Vertex.trace [] := rfl
@[simp] theorem toRoseTree_traceOf (a : L) :
    (traceOf a).toRoseTree = .node (Vertex.traceOf a) [] := rfl
@[simp] theorem toRoseTree_merge (l r : PlanarSyntacticObject L) :
    (merge l r).toRoseTree = .node Vertex.bare [l.toRoseTree, r.toRoseTree] := rfl

/-- The tree of a planar object is well formed. -/
theorem isSyntacticObject_toRoseTree (p : PlanarSyntacticObject L) :
    IsSyntacticObject (UnorderedTree.mk p.toRoseTree) := by
  induction p using FreeMagma.recOnMul with
  | ih1 x => exact isSyntacticObject_mk_leaf x.toVertex_ne_bare
  | ih2 l r hl hr => exact (isSyntacticObject_mk_merge _ _).2 ⟨hl, hr⟩

theorem toRoseTree_injective : Function.Injective (toRoseTree : PlanarSyntacticObject L → _) := by
  intro p
  induction p using FreeMagma.recOnMul with
  | ih1 x =>
    intro q h
    cases q with
    | of y => exact congrArg FreeMagma.of (Leaf.toVertex_injective (by simpa [toRoseTree] using h))
    | mul l r => simp [toRoseTree] at h
  | ih2 l r hl hr =>
    intro q h
    cases q with
    | of y => simp [toRoseTree] at h
    | mul l' r' =>
      obtain ⟨h₁, h₂⟩ : toRoseTree l = toRoseTree l' ∧ toRoseTree r = toRoseTree r' := by
          simpa [toRoseTree] using h
      rw [hl h₁, hr h₂]; rfl

end PlanarSyntacticObject

namespace SyntacticObject

variable {L L' L'' : Type}

/-- The unordered tree of a syntactic object. -/
def toUnorderedTree : SyntacticObject L → UnorderedTree (Vertex L) :=
  FreeCommMagma.elim (fun x ↦ UnorderedTree.leaf x.toVertex)
    (fun _ _ l r ↦ UnorderedTree.node Vertex.bare {l, r})
    fun _ _ l r ↦ congrArg _ (Multiset.pair_comm l r)

@[simp] theorem toUnorderedTree_of (x : Leaf L) :
    toUnorderedTree (FreeCommMagma.of x) = UnorderedTree.leaf x.toVertex := rfl

@[simp] theorem toUnorderedTree_leaf (a : L) :
    (leaf a).toUnorderedTree = UnorderedTree.leaf (Vertex.lex a) := rfl

@[simp] theorem toUnorderedTree_trace :
    (trace : SyntacticObject L).toUnorderedTree = UnorderedTree.leaf Vertex.trace := rfl

@[simp] theorem toUnorderedTree_traceOf (a : L) :
    (traceOf a).toUnorderedTree = UnorderedTree.leaf (Vertex.traceOf a) := rfl

@[simp] theorem toUnorderedTree_merge (l r : SyntacticObject L) :
    (merge l r).toUnorderedTree =
      UnorderedTree.node Vertex.bare {l.toUnorderedTree, r.toUnorderedTree} :=
  FreeCommMagma.elim_mul ..

@[simp] theorem _root_.Minimalist.PlanarSyntacticObject.toUnorderedTree_toSyntacticObject
    (p : PlanarSyntacticObject L) :
    p.toSyntacticObject.toUnorderedTree = UnorderedTree.mk p.toRoseTree := by
  induction p using FreeMagma.recOnMul with
  | ih1 x => rfl
  | ih2 l r hl hr =>
    refine (toUnorderedTree_merge (PlanarSyntacticObject.toSyntacticObject l)
      (PlanarSyntacticObject.toSyntacticObject r)).trans ?_
    rw [hl, hr]
    exact UnorderedTree.node_pair_mk ..

/-- The tree of a syntactic object is well formed. -/
theorem isSyntacticObject_toUnorderedTree (s : SyntacticObject L) :
    IsSyntacticObject s.toUnorderedTree := by
  obtain ⟨p, rfl⟩ := PlanarSyntacticObject.toSyntacticObject_surjective s
  exact p.toUnorderedTree_toSyntacticObject ▸ p.isSyntacticObject_toRoseTree

/-- A syntactic object is determined by its tree. -/
theorem toUnorderedTree_injective :
    Function.Injective (toUnorderedTree : SyntacticObject L → _) :=
  FreeCommMagma.injective_of_mul_eq_mul
    (fun _ _ h ↦ Leaf.toVertex_injective (by simpa using congrArg UnorderedTree.value h))
    (fun x _ _ h ↦ x.toVertex_ne_bare (by simpa using congrArg UnorderedTree.value h))
    fun _ _ _ _ h ↦ Multiset.pair_eq_pair_iff.1 (by simpa using congrArg UnorderedTree.children h)

@[simp] theorem toUnorderedTree_inj {s t : SyntacticObject L} :
    s.toUnorderedTree = t.toUnorderedTree ↔ s = t := toUnorderedTree_injective.eq_iff

end SyntacticObject

namespace PlanarSyntacticObject

open SyntacticObject (Vertex Leaf isSyntacticObject_mk_leaf isSyntacticObject_mk_merge
  length_eq_zero_or_two eq_bare_of_ne_nil)

variable {L L' L'' : Type}

/-- One step of reading a planar object off a tree: a lexical or trace vertex without
daughters is a leaf, and a bare vertex over two objects is their Merge. -/
def ofRoseTreeStep : Vertex L → List (Option (PlanarSyntacticObject L)) →
    Option (PlanarSyntacticObject L)
  | .inl (some a), [] => some (leaf a)
  | .inr none, [] => some trace
  | .inr (some a), [] => some (traceOf a)
  | .inl none, [some l, some r] => some (l * r)
  | _, _ => none

/-- The planar object with a given tree, if the tree is well formed. -/
def ofRoseTree? : RoseTree (Vertex L) → Option (PlanarSyntacticObject L) :=
  RoseTree.fold ofRoseTreeStep

theorem ofRoseTree?_node (a : Vertex L) (cs : List (RoseTree (Vertex L))) :
    ofRoseTree? (.node a cs) = ofRoseTreeStep a (cs.map ofRoseTree?) :=
  RoseTree.fold_node _ _ _

@[simp] theorem ofRoseTree?_toRoseTree (p : PlanarSyntacticObject L) :
    ofRoseTree? p.toRoseTree = some p := by
  induction p using FreeMagma.recOnMul with
  | ih1 x => cases x <;> rfl
  | ih2 l r hl hr =>
    show ofRoseTree? (.node Vertex.bare [toRoseTree l, toRoseTree r]) = some (l * r)
    rw [ofRoseTree?_node, List.map_cons, List.map_cons, List.map_nil, hl, hr]
    rfl

/-- A well-formed tree is the tree of a planar object. -/
theorem exists_toRoseTree_eq {t : RoseTree (Vertex L)}
    (h : IsSyntacticObject (UnorderedTree.mk t)) :
    ∃ p : PlanarSyntacticObject L, p.toRoseTree = t := by
  induction t with
  | node lbl cs ih =>
    rcases length_eq_zero_or_two h with hlen | hlen
    · obtain rfl := List.length_eq_zero_iff.mp hlen
      rcases lbl with (_ | a) | (_ | a)
      · exact absurd (RoseTree.licensed_node_iff.mp ((isSyntacticObject_mk _).mp h)).1
          (by simp [Vertex.Licenses])
      · exact ⟨leaf a, rfl⟩
      · exact ⟨trace, rfl⟩
      · exact ⟨traceOf a, rfl⟩
    · obtain ⟨pl, pr, rfl⟩ := List.length_eq_two.mp hlen
      obtain rfl := eq_bare_of_ne_nil h (by simp)
      obtain ⟨hl, hr⟩ := (isSyntacticObject_mk_merge pl pr).mp h
      obtain ⟨l, rfl⟩ := ih pl (by simp) hl
      obtain ⟨r, rfl⟩ := ih pr (by simp) hr
      exact ⟨l * r, rfl⟩

theorem isSome_ofRoseTree? {t : RoseTree (Vertex L)}
    (h : IsSyntacticObject (UnorderedTree.mk t)) : (ofRoseTree? t).isSome := by
  obtain ⟨p, rfl⟩ := exists_toRoseTree_eq h
  rw [ofRoseTree?_toRoseTree, Option.isSome_some]

/-- The planar object with the well-formed tree `t`. -/
def ofRoseTree (t : RoseTree (Vertex L)) (h : IsSyntacticObject (UnorderedTree.mk t)) :
    PlanarSyntacticObject L :=
  (ofRoseTree? t).get (isSome_ofRoseTree? h)

@[simp] theorem toRoseTree_ofRoseTree (t : RoseTree (Vertex L))
    (h : IsSyntacticObject (UnorderedTree.mk t)) : (ofRoseTree t h).toRoseTree = t := by
  obtain ⟨p, rfl⟩ := exists_toRoseTree_eq h
  simp [ofRoseTree]

@[simp] theorem ofRoseTree_toRoseTree (p : PlanarSyntacticObject L) :
    ofRoseTree p.toRoseTree p.isSyntacticObject_toRoseTree = p :=
  toRoseTree_injective (toRoseTree_ofRoseTree _ _)

theorem ofRoseTree_node_bare (u v : RoseTree (Vertex L))
    (h : IsSyntacticObject (UnorderedTree.mk (.node Vertex.bare [u, v]))) :
    ofRoseTree (.node Vertex.bare [u, v]) h =
      merge (ofRoseTree u ((isSyntacticObject_mk_merge u v).1 h).1)
        (ofRoseTree v ((isSyntacticObject_mk_merge u v).1 h).2) :=
  toRoseTree_injective (by simp)

/-- Every planar object is the object of its tree. -/
theorem exists_eq_ofRoseTree (p : PlanarSyntacticObject L) : ∃ t h, p = ofRoseTree t h :=
  ⟨p.toRoseTree, p.isSyntacticObject_toRoseTree, (ofRoseTree_toRoseTree p).symm⟩

end PlanarSyntacticObject

namespace SyntacticObject

variable {L L' L'' : Type}

/-- The syntactic object with the well-formed tree `t`. -/
def ofUnorderedTree (t : UnorderedTree (Vertex L)) (_h : IsSyntacticObject t) : SyntacticObject L :=
  Quotient.liftOn t
    (fun r ↦ if h : IsSyntacticObject (UnorderedTree.mk r) then
      (PlanarSyntacticObject.ofRoseTree r h).toSyntacticObject else trace)
    fun r r' hr ↦ by
      have hmk : UnorderedTree.mk r = UnorderedTree.mk r' := Quotient.sound hr
      by_cases h : IsSyntacticObject (UnorderedTree.mk r)
      · have h' : IsSyntacticObject (UnorderedTree.mk r') := hmk ▸ h
        simp only [h, h', ↓reduceDIte]
        refine toUnorderedTree_injective ?_
        rw [PlanarSyntacticObject.toUnorderedTree_toSyntacticObject,
          PlanarSyntacticObject.toUnorderedTree_toSyntacticObject,
              PlanarSyntacticObject.toRoseTree_ofRoseTree,
          PlanarSyntacticObject.toRoseTree_ofRoseTree, hmk]
      · have h' : ¬ IsSyntacticObject (UnorderedTree.mk r') := hmk ▸ h
        simp only [h, h', ↓reduceDIte]

@[simp] theorem toUnorderedTree_ofUnorderedTree (t : UnorderedTree (Vertex L))
    (h : IsSyntacticObject t) :
    (ofUnorderedTree t h).toUnorderedTree = t := by
  induction t using Quotient.inductionOn with
  | _ r =>
    show (if h : IsSyntacticObject (UnorderedTree.mk r) then
      (PlanarSyntacticObject.ofRoseTree r h).toSyntacticObject else trace).toUnorderedTree =
          UnorderedTree.mk r
    have h' : IsSyntacticObject (UnorderedTree.mk r) := h
    simp only [h', ↓reduceDIte, PlanarSyntacticObject.toUnorderedTree_toSyntacticObject,
      PlanarSyntacticObject.toRoseTree_ofRoseTree]

@[simp] theorem ofUnorderedTree_toUnorderedTree (s : SyntacticObject L) :
    ofUnorderedTree s.toUnorderedTree s.isSyntacticObject_toUnorderedTree = s :=
  toUnorderedTree_injective (toUnorderedTree_ofUnorderedTree _ _)

@[simp] theorem _root_.Minimalist.PlanarSyntacticObject.toSyntacticObject_ofRoseTree
    (t : RoseTree (Vertex L)) (h : IsSyntacticObject (UnorderedTree.mk t)) :
    (PlanarSyntacticObject.ofRoseTree t h).toSyntacticObject =
      ofUnorderedTree (UnorderedTree.mk t) h :=
  toUnorderedTree_injective (by simp)

/-- Syntactic objects are the well-formed unordered trees. -/
def unorderedTreeEquiv :
    SyntacticObject L ≃ {t : UnorderedTree (Vertex L) // IsSyntacticObject t} where
  toFun s := ⟨s.toUnorderedTree, s.isSyntacticObject_toUnorderedTree⟩
  invFun t := ofUnorderedTree t.1 t.2
  left_inv := ofUnorderedTree_toUnorderedTree
  right_inv t := Subtype.ext (toUnorderedTree_ofUnorderedTree t.1 t.2)

/-- The vertex with its label relabelled by `f`. -/
def Vertex.map (f : L → L') : Vertex L → Vertex L' := Sum.map (Option.map f) (Option.map f)

@[simp] theorem Vertex.map_lex (f : L → L') (a : L) :
    (Vertex.lex a).map f = Vertex.lex (f a) := rfl

@[simp] theorem Vertex.map_bare (f : L → L') : (Vertex.bare : Vertex L).map f = Vertex.bare := rfl

@[simp] theorem Vertex.map_trace (f : L → L') :
    (Vertex.trace : Vertex L).map f = Vertex.trace := rfl

@[simp] theorem Vertex.map_traceOf (f : L → L') (a : L) :
    (Vertex.traceOf a).map f = Vertex.traceOf (f a) := rfl

@[simp] theorem Vertex.map_id : Vertex.map (id : L → L) = id := by
  funext v; rcases v with (_ | _) | (_ | _) <;> rfl

theorem Vertex.map_comp (f : L → L') (g : L' → L'') :
    Vertex.map g ∘ Vertex.map f = Vertex.map (g ∘ f) := by
  funext v; rcases v with (_ | _) | (_ | _) <;> rfl

theorem Vertex.map_injective {f : L → L'} (hf : Function.Injective f) :
    Function.Injective (Vertex.map f) :=
  Sum.map_injective.2 ⟨Option.map_injective hf, Option.map_injective hf⟩

theorem Leaf.toVertex_map (f : L → L') (x : Leaf L) :
    (x.map f f).toVertex = Vertex.map f x.toVertex := by
  cases x <;> rfl

end SyntacticObject

namespace PlanarSyntacticObject

open SyntacticObject (Vertex Leaf isSyntacticObject_mk_leaf isSyntacticObject_mk_merge
  length_eq_zero_or_two eq_bare_of_ne_nil)

variable {L L' L'' : Type}

@[simp] theorem toRoseTree_map (f : L → L') (p : PlanarSyntacticObject L) :
    (p.map f).toRoseTree = p.toRoseTree.map (Vertex.map f) := by
  induction p using FreeMagma.recOnMul with
  | ih1 x => simp [map, toRoseTree, Leaf.toVertex_map]
  | ih2 l r hl hr =>
    have hl' : toRoseTree (FreeMagma.map (Leaf.map f f) l) =
        RoseTree.map (Vertex.map f) (toRoseTree l) := hl
    have hr' : toRoseTree (FreeMagma.map (Leaf.map f f) r) =
        RoseTree.map (Vertex.map f) (toRoseTree r) := hr
    simp [map, toRoseTree, hl', hr']

end PlanarSyntacticObject

namespace SyntacticObject

variable {L L' L'' : Type}

@[simp] theorem toUnorderedTree_map (f : L → L') (s : SyntacticObject L) :
    (s.map f).toUnorderedTree = s.toUnorderedTree.map (Vertex.map f) := by
  obtain ⟨p, rfl⟩ := PlanarSyntacticObject.toSyntacticObject_surjective s
  rw [← PlanarSyntacticObject.toSyntacticObject_map,
    PlanarSyntacticObject.toUnorderedTree_toSyntacticObject, PlanarSyntacticObject.toRoseTree_map,
    PlanarSyntacticObject.toUnorderedTree_toSyntacticObject, UnorderedTree.map_mk]

end SyntacticObject

end Minimalist
