/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Linglib.Core.Data.Multiset.ZeroCons
public import Linglib.Core.Data.UnorderedTree.DecEq
public import Linglib.Core.Data.UnorderedTree.Licensed
public import Linglib.Syntax.Minimalist.LexicalItem

/-!
# Syntactic objects

A syntactic object is a binary rooted tree with leaves labelled by the lexical alphabet and no
labels at internal vertices: an element of the free non-associative commutative magma on `SO₀`.
This file builds two carriers for it over one alphabet of vertices, `Vertex L`, an option of a
leaf label on either side. The left summand is structure: a leaf `Vertex.lex a` of the lexical
alphabet `L`, or the bare label `Vertex.bare` on a binary internal node. The right summand is a
trace: the index-free `Vertex.trace`, or the trace `Vertex.traceOf a` of a label, the cancellation
`T/T_v` remembering the head of `T_v`. Traces are exactly the right summand, the convention of the
trace coproduct. `SyntacticObject L` is the well-formed unordered tree over `Vertex L`, the object
Merge builds, and `LinearizedSyntacticObject L` the well-formed ordered tree, the form
linearization produces and PF reads, Marcolli, Chomsky and Berwick's planar embedding.
Well-formedness is a local condition, each vertex licensing its children (`Vertex.Licenses`), so
it descends to the quotient; `LinearizedSyntacticObject.toSyntacticObject` forgets the order and
is a homomorphism for the vocabulary the two carriers share, `leaf`, `trace`, `traceOf` and
`merge`.

## Main definitions

* `Minimalist.SyntacticObject.Vertex`, `Minimalist.IsSyntacticObject`
* `Minimalist.SyntacticObject`, `Minimalist.LinearizedSyntacticObject`: the unordered and the
  ordered carrier, each with `leaf`, `trace`, `traceOf` and `merge`.
* `Minimalist.LinearizedSyntacticObject.toSyntacticObject`: forgetting the order.

## Main results

* `Minimalist.SyntacticObject.ind`, `exists_form`: induction and case analysis over the shapes.
* `Minimalist.LinearizedSyntacticObject.toSyntacticObject_merge`: forgetting the order commutes
  with Merge.

## Implementation notes

The lexical alphabet `L` defaults to `LexicalItem.Token`, so a bare `SyntacticObject` is the
carrier over tokens; the default pins `L` to `Type`.

## References

* [marcolli-chomsky-berwick-2025], §1.1 (Definition 1.1.1, §1.1.3), §1.2 (Definitions 1.2.1,
  1.2.6) and §1.12
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree

/-- A vertex carries structure on the left, a leaf of the lexical alphabet `L` or the bare
    internal label, and a trace on the right, index-free or of a label. -/
abbrev SyntacticObject.Vertex (L : Type := LexicalItem.Token) : Type := Option L ⊕ Option L

namespace SyntacticObject

variable {L : Type}

/-- The lexical leaf `a`. -/
@[match_pattern] abbrev Vertex.lex (a : L) : Vertex L := .inl (some a)

/-- The bare label of a binary internal node. -/
@[match_pattern] abbrev Vertex.bare : Vertex L := .inl none

/-- The index-free trace. -/
@[match_pattern] abbrev Vertex.trace : Vertex L := .inr none

/-- The trace of the leaf `a`. -/
@[match_pattern] abbrev Vertex.traceOf (a : L) : Vertex L := .inr (some a)

/-! ### Well-formedness -/

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

variable {L : Type}

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

/-- The syntactic objects over the lexical alphabet `L` are the well-formed unordered trees over
    `Vertex L`. -/
def SyntacticObject (L : Type := LexicalItem.Token) : Type :=
  { t : UnorderedTree (SyntacticObject.Vertex L) // IsSyntacticObject t }

/-- The linearized syntactic objects are the well-formed ordered trees over `Vertex L`, in any
    order of the daughters: [marcolli-chomsky-berwick-2025] §1.12's planar embeddings. -/
def LinearizedSyntacticObject (L : Type := LexicalItem.Token) : Type :=
  { t : RoseTree (SyntacticObject.Vertex L) // IsSyntacticObject (UnorderedTree.mk t) }

instance {L : Type} [DecidableEq L] : DecidableEq (SyntacticObject L) :=
  Subtype.instDecidableEq

instance {L : Type} [DecidableEq L] : DecidableEq (LinearizedSyntacticObject L) :=
  Subtype.instDecidableEq

/-! ### The shapes -/

namespace SyntacticObject

variable {L : Type}

/-- A lexical leaf. -/
@[coe] def leaf (a : L) : SyntacticObject L :=
  ⟨UnorderedTree.leaf (Vertex.lex a), isSyntacticObject_mk_leaf (by simp)⟩

/-- The index-free trace, the mark an admissible cut leaves in the remaining tree
    ([marcolli-chomsky-berwick-2025], Definition 1.2.6); `traceOf` is the indexed trace. -/
def trace : SyntacticObject L :=
  ⟨UnorderedTree.leaf Vertex.trace, isSyntacticObject_mk_leaf (by simp)⟩

/-- The trace of `a`. -/
def traceOf (a : L) : SyntacticObject L :=
  ⟨UnorderedTree.leaf (Vertex.traceOf a), isSyntacticObject_mk_leaf (by simp)⟩

@[simp] theorem leaf_val (a : L) :
    (leaf a).val = UnorderedTree.leaf (Vertex.lex a) :=
  rfl

@[simp] theorem leaf_inj {a b : L} : leaf a = leaf b ↔ a = b :=
  ⟨fun h ↦ Option.some_injective _
    (Sum.inl_injective (congrArg (fun s : SyntacticObject L ↦ s.val.value) h)), congrArg leaf⟩
@[simp] theorem trace_val : (trace : SyntacticObject L).val = UnorderedTree.leaf Vertex.trace :=
  rfl
@[simp] theorem traceOf_val (a : L) :
    (traceOf a).val = UnorderedTree.leaf (Vertex.traceOf a) := rfl

theorem isSyntacticObject_merge_iff (a b : UnorderedTree (Vertex L)) :
    IsSyntacticObject (UnorderedTree.node Vertex.bare {a, b}) ↔
      IsSyntacticObject a ∧ IsSyntacticObject b := by
  refine Quotient.inductionOn₂ a b fun pa pb ↦ ?_
  show IsSyntacticObject (UnorderedTree.node Vertex.bare {UnorderedTree.mk pa,
    UnorderedTree.mk pb}) ↔
    IsSyntacticObject (UnorderedTree.mk pa) ∧ IsSyntacticObject (UnorderedTree.mk pb)
  rw [show ({UnorderedTree.mk pa, UnorderedTree.mk pb} : Multiset (UnorderedTree (Vertex L)))
        = Multiset.ofList ([pa, pb].map UnorderedTree.mk) from rfl, UnorderedTree.node_mk_tree_list]
  exact isSyntacticObject_mk_merge pa pb

/-- Merge on the carrier, the bare binary node over two syntactic objects, also written `*`.
    Noncomputable, since it goes through the smart constructor `UnorderedTree.node`; concrete
    results are built ordered and forgotten by `LinearizedSyntacticObject.toSyntacticObject`. -/
noncomputable def merge (l r : SyntacticObject L) : SyntacticObject L :=
  ⟨UnorderedTree.node Vertex.bare {l.val, r.val}, (isSyntacticObject_merge_iff _ _).2 ⟨l.2, r.2⟩⟩

@[simp] theorem merge_val (l r : SyntacticObject L) :
    (merge l r).val = UnorderedTree.node Vertex.bare {l.val, r.val} := rfl

theorem merge_comm (l r : SyntacticObject L) : merge l r = merge r l :=
  Subtype.ext (by rw [merge_val, merge_val, Multiset.pair_comm])

theorem merge_eq_merge_iff {l r l' r' : SyntacticObject L} :
    merge l r = merge l' r' ↔ l = l' ∧ r = r' ∨ l = r' ∧ r = l' := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have := congrArg (fun s : SyntacticObject L ↦ s.val.children) h
    simp only [merge_val, UnorderedTree.children_node] at this
    rcases Multiset.pair_eq_pair_iff.1 this with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    exacts [.inl ⟨Subtype.ext h₁, Subtype.ext h₂⟩, .inr ⟨Subtype.ext h₁, Subtype.ext h₂⟩]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    exacts [rfl, merge_comm _ _]

@[simp]
theorem leaf_ne_merge (a : L) (l r : SyntacticObject L) : leaf a ≠ merge l r :=
  fun h ↦ by simpa using congrArg (fun s : SyntacticObject L ↦ s.val.value) h

@[simp]
theorem leaf_ne_trace (a : L) : leaf a ≠ trace :=
  fun h ↦ by simpa using congrArg (fun s : SyntacticObject L ↦ s.val.value) h

@[simp]
theorem leaf_ne_traceOf (a b : L) : leaf a ≠ traceOf b :=
  fun h ↦ by simpa using congrArg (fun s : SyntacticObject L ↦ s.val.value) h

@[simp]
theorem traceOf_ne_merge (a : L) (l r : SyntacticObject L) :
    traceOf a ≠ merge l r :=
  fun h ↦ by simpa using congrArg (fun s : SyntacticObject L ↦ s.val.value) h

@[simp]
theorem traceOf_ne_leaf (a b : L) : traceOf a ≠ leaf b :=
  fun h ↦ by simpa using congrArg (fun s : SyntacticObject L ↦ s.val.value) h

theorem merge_mk (pl pr : RoseTree (Vertex L))
    (hl : IsSyntacticObject (UnorderedTree.mk pl)) (hr : IsSyntacticObject (UnorderedTree.mk pr)) :
    (merge ⟨UnorderedTree.mk pl, hl⟩ ⟨UnorderedTree.mk pr, hr⟩).val
      = UnorderedTree.mk (.node Vertex.bare [pl, pr]) := by
  rw [merge_val,
      show ({UnorderedTree.mk pl, UnorderedTree.mk pr} : Multiset (UnorderedTree (Vertex L)))
        = Multiset.ofList ([pl, pr].map UnorderedTree.mk) from rfl,
      UnorderedTree.node_mk_tree_list]

end SyntacticObject

namespace LinearizedSyntacticObject

open SyntacticObject (Vertex isSyntacticObject_mk_leaf isSyntacticObject_mk_merge)

variable {L : Type}

/-- A lexical leaf. -/
@[coe] def leaf (a : L) : LinearizedSyntacticObject L :=
  ⟨.node (Vertex.lex a) [], isSyntacticObject_mk_leaf (by simp)⟩

/-- The index-free trace. -/
def trace : LinearizedSyntacticObject L :=
  ⟨.node Vertex.trace [], isSyntacticObject_mk_leaf (by simp)⟩

/-- The trace of `a`. -/
def traceOf (a : L) : LinearizedSyntacticObject L :=
  ⟨.node (Vertex.traceOf a) [], isSyntacticObject_mk_leaf (by simp)⟩

/-- Merge, with the daughters in the given order. -/
def merge (l r : LinearizedSyntacticObject L) : LinearizedSyntacticObject L :=
  ⟨.node Vertex.bare [l.val, r.val], (isSyntacticObject_mk_merge _ _).mpr ⟨l.2, r.2⟩⟩

@[simp] theorem leaf_val (a : L) :
    (leaf a).val = .node (Vertex.lex a) [] := rfl
@[simp] theorem trace_val : (trace : LinearizedSyntacticObject L).val = .node Vertex.trace [] :=
  rfl
@[simp] theorem traceOf_val (a : L) :
    (traceOf a).val = .node (Vertex.traceOf a) [] :=
  rfl
@[simp] theorem merge_val (l r : LinearizedSyntacticObject L) :
    (merge l r).val = .node Vertex.bare [l.val, r.val] := rfl

/-- Forgetting the order is the quotient map to the syntactic object. -/
@[coe] def toSyntacticObject (p : LinearizedSyntacticObject L)
  : SyntacticObject L := ⟨UnorderedTree.mk p.val, p.2⟩

@[simp] theorem toSyntacticObject_val (p : LinearizedSyntacticObject L) :
    p.toSyntacticObject.val = UnorderedTree.mk p.val := rfl

@[simp] theorem toSyntacticObject_leaf (a : L) :
    (leaf a).toSyntacticObject = SyntacticObject.leaf a := rfl

@[simp] theorem toSyntacticObject_trace :
    (trace : LinearizedSyntacticObject L).toSyntacticObject = SyntacticObject.trace := rfl

@[simp] theorem toSyntacticObject_traceOf (a : L) :
    (traceOf a).toSyntacticObject = SyntacticObject.traceOf a := rfl

@[simp] theorem toSyntacticObject_merge (l r : LinearizedSyntacticObject L) :
    (merge l r).toSyntacticObject = SyntacticObject.merge l.toSyntacticObject r.toSyntacticObject :=
  Subtype.ext (SyntacticObject.merge_mk l.val r.val l.2 r.2).symm

end LinearizedSyntacticObject

/-! ### Induction and case analysis -/

namespace SyntacticObject

variable {L : Type}

@[elab_as_elim]
theorem ind {motive : SyntacticObject L → Prop}
    (leaf : ∀ a, motive (leaf a))
    (trace : motive trace)
    (traceOf : ∀ a, motive (traceOf a))
    (merge : ∀ l r : SyntacticObject L, motive l → motive r → motive (merge l r))
    (s : SyntacticObject L) : motive s := by
  suffices H : ∀ n (p : RoseTree (Vertex L)) (hp : IsSyntacticObject (UnorderedTree.mk p)),
      p.numNodes = n → motive ⟨UnorderedTree.mk p, hp⟩ by
    obtain ⟨t, ht⟩ := s
    refine Quotient.inductionOn (motive := fun t ↦ ∀ (ht : IsSyntacticObject t), motive ⟨t, ht⟩)
      t (fun p ht ↦ H p.numNodes p ht rfl) ht
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    rintro ⟨lbl, cs⟩ hp hw
    rcases length_eq_zero_or_two hp with hlen | hlen
    · obtain rfl := List.length_eq_zero_iff.mp hlen
      rcases lbl with (_ | a) | (_ | a)
      · exact absurd (licensed_node_iff.mp ((isSyntacticObject_mk _).mp hp)).1
          (by simp [Vertex.Licenses])
      · exact leaf a
      · exact trace
      · exact traceOf a
    · obtain ⟨pl, pr, rfl⟩ := List.length_eq_two.mp hlen
      obtain rfl := eq_bare_of_ne_nil hp (by simp)
      obtain ⟨hl, hr⟩ := (isSyntacticObject_mk_merge pl pr).mp hp
      have hmerge : (⟨UnorderedTree.mk (RoseTree.node Vertex.bare [pl, pr]), hp⟩
          : SyntacticObject L) =
            SyntacticObject.merge ⟨UnorderedTree.mk pl, hl⟩ ⟨UnorderedTree.mk pr, hr⟩ :=
        Subtype.ext (merge_mk pl pr hl hr).symm
      rw [hmerge]
      simp only [RoseTree.numNodes_node, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil] at hw
      exact merge _ _ (IH pl.numNodes (by omega) pl hl rfl) (IH pr.numNodes (by omega) pr hr rfl)

theorem exists_form (s : SyntacticObject L) :
    (∃ a, s = leaf a) ∨ s = trace ∨ (∃ a, s = traceOf a) ∨ (∃ l r, s = merge l r) := by
  induction s using ind with
  | leaf a => exact Or.inl ⟨a, rfl⟩
  | trace => exact Or.inr (Or.inl rfl)
  | traceOf a => exact Or.inr (Or.inr (Or.inl ⟨a, rfl⟩))
  | merge l r _ _ => exact Or.inr (Or.inr (Or.inr ⟨l, r, rfl⟩))

end SyntacticObject

end Minimalist
