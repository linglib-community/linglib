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
labels at internal vertices: an element of the free non-associative commutative magma on `SO₀`. This
file builds two carriers for it over one alphabet of vertices, `Vertex`, an option of a token on
either side. The left summand is structure: a lexical item `Vertex.lex tok` on a leaf, or the
bare label `Vertex.bare` on a binary internal node. The right summand is a trace: the index-free
`Vertex.trace`, or the trace `Vertex.traceOf tok` of a token, the cancellation `T/T_v` remembering
the head of `T_v`. Traces are exactly the right summand, the convention of the trace coproduct.
`SyntacticObject` is the well-formed unordered tree over `Vertex`, the object Merge builds, and
`PlanarSyntacticObject` the well-formed ordered tree, the planar embedding of Marcolli, Chomsky
and Berwick, the form linearization and PF read. Well-formedness is a local condition, each vertex
licensing its children (`Vertex.Licenses`), so it descends to the quotient;
`PlanarSyntacticObject.toSyntacticObject` forgets the order and is a homomorphism for the vocabulary
the two carriers share, `leaf`, `trace`, `traceOf` and `merge`.

## Main definitions

* `Minimalist.SyntacticObject.Vertex`, `Minimalist.IsSyntacticObject`
* `Minimalist.SyntacticObject`, `Minimalist.PlanarSyntacticObject`: the unordered and the ordered
  carrier, each with `leaf`, `trace`, `traceOf` and `merge`.
* `Minimalist.PlanarSyntacticObject.toSyntacticObject`: forgetting the order.

## Main results

* `Minimalist.SyntacticObject.ind`, `exists_form`: induction and case analysis over the shapes.
* `Minimalist.PlanarSyntacticObject.toSyntacticObject_merge`: forgetting the order commutes with
  Merge.

## References

* [marcolli-chomsky-berwick-2025], §1.1 (Definition 1.1.1, §1.1.3), §1.2 (Definitions 1.2.1,
  1.2.6) and §1.12
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree

/-- A vertex carries structure on the left, a lexical token or the bare internal label, and a
    trace on the right, index-free or of a token. -/
abbrev SyntacticObject.Vertex : Type := Option LexicalItem.Token ⊕ Option LexicalItem.Token

namespace SyntacticObject

/-- The lexical item `tok` on a leaf. -/
@[match_pattern] abbrev Vertex.lex (tok : LexicalItem.Token) : Vertex := .inl (some tok)

/-- The bare label of a binary internal node. -/
@[match_pattern] abbrev Vertex.bare : Vertex := .inl none

/-- The index-free trace. -/
@[match_pattern] abbrev Vertex.trace : Vertex := .inr none

/-- The trace of the token `tok`. -/
@[match_pattern] abbrev Vertex.traceOf (tok : LexicalItem.Token) : Vertex := .inr (some tok)

/-! ### Well-formedness -/

/-- A vertex licenses its children when a lexical item or a trace has none and the bare label has
two. -/
def Vertex.Licenses : Vertex → Multiset Vertex → Prop
  | .inl (some _), ks => ks = 0
  | .inl none, ks => Multiset.card ks = 2
  | .inr _, ks => ks = 0

instance : ∀ (a : Vertex) (ks : Multiset Vertex), Decidable (Vertex.Licenses a ks)
  | .inl (some _), ks => inferInstanceAs (Decidable (ks = 0))
  | .inl none, ks => inferInstanceAs (Decidable (Multiset.card ks = 2))
  | .inr _, ks => inferInstanceAs (Decidable (ks = 0))

/-- The licensing of a vertex depends only on how many children it has. -/
theorem Vertex.licenses_iff_of_card_eq {a : Vertex} {ks ls : Multiset Vertex}
    (h : Multiset.card ks = Multiset.card ls) : a.Licenses ks ↔ a.Licenses ls := by
  rcases a with (_ | _) | _ <;>
    simp only [Vertex.Licenses, ← Multiset.card_eq_zero, h]

end SyntacticObject

/-- An unordered tree over `Vertex` is a syntactic object when every vertex licenses its
    children, so that lexical items and traces are leaves and bare vertices are binary. -/
def IsSyntacticObject (t : UnorderedTree SyntacticObject.Vertex) : Prop :=
  t.Licensed SyntacticObject.Vertex.Licenses

instance : DecidablePred IsSyntacticObject := fun t ↦ inferInstanceAs (Decidable (t.Licensed _))

@[simp] theorem isSyntacticObject_mk (t : RoseTree SyntacticObject.Vertex) :
    IsSyntacticObject (UnorderedTree.mk t) ↔
      t.Licensed fun a ks ↦ SyntacticObject.Vertex.Licenses a (ks : Multiset _) :=
  Iff.rfl

namespace SyntacticObject

/-- A leaf carrying a lexical item or a trace is a syntactic object. -/
theorem isSyntacticObject_mk_leaf {a : Vertex} (ha : a ≠ Vertex.bare) :
    IsSyntacticObject (UnorderedTree.mk (.node a [])) := by
  refine (isSyntacticObject_mk _).mpr (licensed_node_iff.mpr ⟨?_, by simp⟩)
  match a, ha with
  | .inl (some _), _ | .inr _, _ => rfl
  | .inl none, h => exact absurd rfl h

/-- A bare binary node is a syntactic object exactly when both daughters are. -/
@[simp] theorem isSyntacticObject_mk_merge (l r : RoseTree Vertex) :
    IsSyntacticObject (UnorderedTree.mk (.node Vertex.bare [l, r])) ↔
      IsSyntacticObject (UnorderedTree.mk l) ∧ IsSyntacticObject (UnorderedTree.mk r) := by
  simp [licensed_node_iff, Vertex.Licenses]

/-- A node of a syntactic object has either no children or exactly two. -/
theorem length_eq_zero_or_two {a : Vertex} {cs : List (RoseTree Vertex)}
    (h : IsSyntacticObject (UnorderedTree.mk (.node a cs))) : cs.length = 0 ∨ cs.length = 2 := by
  have h := (licensed_node_iff.mp ((isSyntacticObject_mk _).mp h)).1
  match a with
  | .inl (some _) | .inr _ => exact .inl (by simpa [Vertex.Licenses] using congrArg Multiset.card h)
  | .inl none => exact .inr (by simpa [Vertex.Licenses] using h)

/-- A node of a syntactic object with children is bare. -/
theorem eq_bare_of_ne_nil {a : Vertex} {cs : List (RoseTree Vertex)}
    (h : IsSyntacticObject (UnorderedTree.mk (.node a cs))) (hcs : cs ≠ []) : a = Vertex.bare := by
  have h := (licensed_node_iff.mp ((isSyntacticObject_mk _).mp h)).1
  match a with
  | .inl none => rfl
  | .inl (some _) | .inr _ => exact absurd (by simpa [Vertex.Licenses] using h) hcs

end SyntacticObject

/-- The vertices of a syntactic object have zero or two children. -/
theorem IsSyntacticObject.isFullBinary {t : UnorderedTree SyntacticObject.Vertex}
    (h : IsSyntacticObject t) : t.IsFullBinary :=
  UnorderedTree.Licensed.mono (R := SyntacticObject.Vertex.Licenses) (fun
    | .inl (some _), _, h | .inr _, _, h => .inl (congrArg Multiset.card h)
    | .inl none, _, h => .inr h) h

/-- The syntactic objects are the well-formed unordered trees over `Vertex`. -/
def SyntacticObject : Type := { t : UnorderedTree SyntacticObject.Vertex // IsSyntacticObject t }

/-- The planar syntactic objects are the well-formed ordered trees over `Vertex`,
    [marcolli-chomsky-berwick-2025] §1.12's planar embeddings. -/
def PlanarSyntacticObject : Type :=
  { t : RoseTree SyntacticObject.Vertex // IsSyntacticObject (UnorderedTree.mk t) }

instance : DecidableEq SyntacticObject := Subtype.instDecidableEq

instance : DecidableEq PlanarSyntacticObject := Subtype.instDecidableEq

/-! ### The shapes -/

namespace SyntacticObject

/-- A lexical leaf. -/
@[coe] def leaf (tok : LexicalItem.Token) : SyntacticObject :=
  ⟨UnorderedTree.leaf (Vertex.lex tok), isSyntacticObject_mk_leaf (by simp)⟩

/-- The index-free trace, the mark an admissible cut leaves in the remaining tree
    ([marcolli-chomsky-berwick-2025], Definition 1.2.6); `traceOf` is the indexed trace. -/
def trace : SyntacticObject :=
  ⟨UnorderedTree.leaf Vertex.trace, isSyntacticObject_mk_leaf (by simp)⟩

/-- The trace of `tok`. -/
def traceOf (tok : LexicalItem.Token) : SyntacticObject :=
  ⟨UnorderedTree.leaf (Vertex.traceOf tok), isSyntacticObject_mk_leaf (by simp)⟩

@[simp] theorem leaf_val (tok : LexicalItem.Token) :
    (leaf tok).val = UnorderedTree.leaf (Vertex.lex tok) :=
  rfl

@[simp] theorem leaf_inj {a b : LexicalItem.Token} : leaf a = leaf b ↔ a = b :=
  ⟨fun h ↦ Option.some_injective _
    (Sum.inl_injective (congrArg (fun s : SyntacticObject ↦ s.val.value) h)), congrArg leaf⟩
@[simp] theorem trace_val : trace.val = UnorderedTree.leaf Vertex.trace := rfl
@[simp] theorem traceOf_val (tok : LexicalItem.Token) :
    (traceOf tok).val = UnorderedTree.leaf (Vertex.traceOf tok) := rfl

/-- A bare binary node is a syntactic object exactly when both daughters are. -/
theorem isSyntacticObject_merge_iff (a b : UnorderedTree Vertex) :
    IsSyntacticObject (UnorderedTree.node Vertex.bare {a, b}) ↔
      IsSyntacticObject a ∧ IsSyntacticObject b := by
  refine Quotient.inductionOn₂ a b fun pa pb ↦ ?_
  show IsSyntacticObject (UnorderedTree.node Vertex.bare {UnorderedTree.mk pa,
    UnorderedTree.mk pb}) ↔
    IsSyntacticObject (UnorderedTree.mk pa) ∧ IsSyntacticObject (UnorderedTree.mk pb)
  rw [show ({UnorderedTree.mk pa, UnorderedTree.mk pb} : Multiset (UnorderedTree Vertex))
        = Multiset.ofList ([pa, pb].map UnorderedTree.mk) from rfl, UnorderedTree.node_mk_tree_list]
  exact isSyntacticObject_mk_merge pa pb

/-- Merge on the carrier, the bare binary node over two syntactic objects, also written `*`.
    Noncomputable, since it goes through the smart constructor `UnorderedTree.node`; concrete
    results are built ordered and forgotten by `PlanarSyntacticObject.toSyntacticObject`. -/
noncomputable def merge (l r : SyntacticObject) : SyntacticObject :=
  ⟨UnorderedTree.node Vertex.bare {l.val, r.val}, (isSyntacticObject_merge_iff _ _).2 ⟨l.2, r.2⟩⟩

@[simp] theorem merge_val (l r : SyntacticObject) :
    (merge l r).val = UnorderedTree.node Vertex.bare {l.val, r.val} := rfl

theorem merge_comm (l r : SyntacticObject) : merge l r = merge r l :=
  Subtype.ext (by rw [merge_val, merge_val, Multiset.pair_comm])

/-- Merge is injective up to the order of its daughters. -/
theorem merge_eq_merge_iff {l r l' r' : SyntacticObject} :
    merge l r = merge l' r' ↔ l = l' ∧ r = r' ∨ l = r' ∧ r = l' := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have := congrArg (fun s : SyntacticObject ↦ s.val.children) h
    simp only [merge_val, UnorderedTree.children_node] at this
    rcases Multiset.pair_eq_pair_iff.1 this with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    exacts [.inl ⟨Subtype.ext h₁, Subtype.ext h₂⟩, .inr ⟨Subtype.ext h₁, Subtype.ext h₂⟩]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    exacts [rfl, merge_comm _ _]

@[simp]
theorem leaf_ne_merge (tok : LexicalItem.Token) (l r : SyntacticObject) : leaf tok ≠ merge l r :=
  fun h ↦ by simpa using congrArg (fun s : SyntacticObject ↦ s.val.value) h

@[simp]
theorem traceOf_ne_merge (tok : LexicalItem.Token) (l r : SyntacticObject) :
    traceOf tok ≠ merge l r :=
  fun h ↦ by simpa using congrArg (fun s : SyntacticObject ↦ s.val.value) h

@[simp]
theorem traceOf_ne_leaf (a b : LexicalItem.Token) : traceOf a ≠ leaf b :=
  fun h ↦ by simpa using congrArg (fun s : SyntacticObject ↦ s.val.value) h

/-- Merge of two ordered-built objects is the ordered binary node, so concrete results reduce. -/
theorem merge_mk (pl pr : RoseTree Vertex)
    (hl : IsSyntacticObject (UnorderedTree.mk pl)) (hr : IsSyntacticObject (UnorderedTree.mk pr)) :
    (merge ⟨UnorderedTree.mk pl, hl⟩ ⟨UnorderedTree.mk pr, hr⟩).val
      = UnorderedTree.mk (.node Vertex.bare [pl, pr]) := by
  rw [merge_val,
      show ({UnorderedTree.mk pl, UnorderedTree.mk pr} : Multiset (UnorderedTree Vertex))
        = Multiset.ofList ([pl, pr].map UnorderedTree.mk) from rfl,
      UnorderedTree.node_mk_tree_list]

end SyntacticObject

namespace PlanarSyntacticObject

open SyntacticObject (Vertex isSyntacticObject_mk_leaf isSyntacticObject_mk_merge)

/-- A lexical leaf. -/
@[coe] def leaf (tok : LexicalItem.Token) : PlanarSyntacticObject :=
  ⟨.node (Vertex.lex tok) [], isSyntacticObject_mk_leaf (by simp)⟩

/-- The index-free trace. -/
def trace : PlanarSyntacticObject := ⟨.node Vertex.trace [], isSyntacticObject_mk_leaf (by simp)⟩

/-- The trace of `tok`. -/
def traceOf (tok : LexicalItem.Token) : PlanarSyntacticObject :=
  ⟨.node (Vertex.traceOf tok) [], isSyntacticObject_mk_leaf (by simp)⟩

/-- Merge, with the daughters in the given order. -/
def merge (l r : PlanarSyntacticObject) : PlanarSyntacticObject :=
  ⟨.node Vertex.bare [l.val, r.val], (isSyntacticObject_mk_merge _ _).mpr ⟨l.2, r.2⟩⟩

@[simp] theorem leaf_val (tok : LexicalItem.Token) :
    (leaf tok).val = .node (Vertex.lex tok) [] := rfl
@[simp] theorem trace_val : trace.val = .node Vertex.trace [] := rfl
@[simp] theorem traceOf_val (tok : LexicalItem.Token) :
    (traceOf tok).val = .node (Vertex.traceOf tok) [] :=
  rfl
@[simp] theorem merge_val (l r : PlanarSyntacticObject) :
    (merge l r).val = .node Vertex.bare [l.val, r.val] := rfl

/-- Forgetting the order is the quotient map to the syntactic object. -/
@[coe] def toSyntacticObject (p : PlanarSyntacticObject)
  : SyntacticObject := ⟨UnorderedTree.mk p.val, p.2⟩

@[simp] theorem toSyntacticObject_val (p : PlanarSyntacticObject) :
    p.toSyntacticObject.val = UnorderedTree.mk p.val := rfl

@[simp] theorem toSyntacticObject_leaf (tok : LexicalItem.Token) :
    (leaf tok).toSyntacticObject = SyntacticObject.leaf tok := rfl

@[simp] theorem toSyntacticObject_trace : trace.toSyntacticObject = SyntacticObject.trace := rfl

@[simp] theorem toSyntacticObject_traceOf (tok : LexicalItem.Token) :
    (traceOf tok).toSyntacticObject = SyntacticObject.traceOf tok := rfl

/-- Forgetting the order commutes with Merge. -/
@[simp] theorem toSyntacticObject_merge (l r : PlanarSyntacticObject) :
    (merge l r).toSyntacticObject = SyntacticObject.merge l.toSyntacticObject r.toSyntacticObject :=
  Subtype.ext (SyntacticObject.merge_mk l.val r.val l.2 r.2).symm

end PlanarSyntacticObject

/-! ### Induction and case analysis -/

namespace SyntacticObject

/-- Induction on syntactic objects, each of which is a lexical leaf, a trace, or the Merge of two
    syntactic objects. -/
@[elab_as_elim]
theorem ind {motive : SyntacticObject → Prop}
    (leaf : ∀ tok, motive (leaf tok))
    (trace : motive trace)
    (traceOf : ∀ tok, motive (traceOf tok))
    (merge : ∀ l r : SyntacticObject, motive l → motive r → motive (merge l r))
    (s : SyntacticObject) : motive s := by
  suffices H : ∀ n (p : RoseTree Vertex) (hp : IsSyntacticObject (UnorderedTree.mk p)),
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
      rcases lbl with (_ | tok) | (_ | tok)
      · exact absurd (licensed_node_iff.mp ((isSyntacticObject_mk _).mp hp)).1
          (by simp [Vertex.Licenses])
      · exact leaf tok
      · exact trace
      · exact traceOf tok
    · obtain ⟨pl, pr, rfl⟩ := List.length_eq_two.mp hlen
      obtain rfl := eq_bare_of_ne_nil hp (by simp)
      obtain ⟨hl, hr⟩ := (isSyntacticObject_mk_merge pl pr).mp hp
      have hmerge : (⟨UnorderedTree.mk (RoseTree.node Vertex.bare [pl, pr]), hp⟩
          : SyntacticObject) =
            SyntacticObject.merge ⟨UnorderedTree.mk pl, hl⟩ ⟨UnorderedTree.mk pr, hr⟩ :=
        Subtype.ext (merge_mk pl pr hl hr).symm
      rw [hmerge]
      simp only [RoseTree.numNodes_node, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil] at hw
      exact merge _ _ (IH pl.numNodes (by omega) pl hl rfl) (IH pr.numNodes (by omega) pr hr rfl)

/-- Every syntactic object is a lexical leaf, a trace, or a Merge. -/
theorem exists_form (s : SyntacticObject) :
    (∃ tok, s = leaf tok) ∨ s = trace ∨ (∃ tok, s = traceOf tok) ∨ (∃ l r, s = merge l r) := by
  induction s using ind with
  | leaf tok => exact Or.inl ⟨tok, rfl⟩
  | trace => exact Or.inr (Or.inl rfl)
  | traceOf tok => exact Or.inr (Or.inr (Or.inl ⟨tok, rfl⟩))
  | merge l r _ _ => exact Or.inr (Or.inr (Or.inr ⟨l, r, rfl⟩))

end SyntacticObject

end Minimalist
