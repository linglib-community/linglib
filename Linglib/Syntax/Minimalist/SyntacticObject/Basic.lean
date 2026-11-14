/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.FreeCommMagma
public import Linglib.Syntax.Minimalist.LexicalItem

/-!
# Syntactic objects

[marcolli-chomsky-berwick-2025] define the syntactic objects as the free nonassociative
commutative magma on the lexical items, with Merge as its product, and the planar syntactic
objects as the free magma on the same items. Here `SyntacticObject L` and
`PlanarSyntacticObject L` are those two magmas on the leaves `SyntacticObject.Leaf L`, and
[forgetting the order of daughters](##Minimalist.PlanarSyntacticObject.toSyntacticObject) is the
projection between them. A map of lexical alphabets relabels the leaves, injectively when it is
injective. The trees of the two kinds of object are in `SyntacticObject/Tree.lean`.

## Implementation notes

* A leaf is a lexical item or a trace, so these are the book's syntactic objects over an alphabet
  enlarged by the traces its coproducts leave. A trace is labelled in a type `ι`, a parameter of
  the leaves and of both magmas. The book's trace is labelled by the whole subtree that was
  removed; the default `ι = L` labels it by the head of that subtree.
* The two types are abbreviations, so the API of `FreeMagma` and `FreeCommMagma` applies to them
  directly: `*` is Merge, and a map out of either is determined by its values on the leaves.
* The lexical alphabet `L` defaults to `LexicalItem.Token`, so a bare `SyntacticObject` is over
  tokens; the default pins `L` to `Type`.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

namespace SyntacticObject

variable {L L' L'' : Type}

/-- A leaf of a syntactic object: a lexical item, the index-free trace, or a trace labelled in
`ι`, by default by an item. -/
inductive Leaf (L : Type) (ι : Type := L) where
  /-- A lexical item. -/
  | lex (a : L)
  /-- The index-free trace. -/
  | trace
  /-- The trace labelled `i`. -/
  | traceOf (i : ι)
  deriving DecidableEq

end SyntacticObject

namespace SyntacticObject

namespace Leaf

variable {L L' L'' ι ι' ι'' : Type}

/-- The leaf with its item relabelled by `f` and its trace label by `g`. -/
def map (f : L → L') (g : ι → ι') : Leaf L ι → Leaf L' ι'
  | lex a => lex (f a)
  | trace => trace
  | traceOf i => traceOf (g i)

@[simp] theorem map_id : map (id : L → L) (id : ι → ι) = id := by funext x; cases x <;> rfl

theorem map_comp (f : L → L') (f' : L' → L'') (g : ι → ι') (g' : ι' → ι'') :
    map f' g' ∘ map f g = map (f' ∘ f) (g' ∘ g) := by
  funext x; cases x <;> rfl

theorem map_injective {f : L → L'} {g : ι → ι'} (hf : Function.Injective f)
    (hg : Function.Injective g) : Function.Injective (map f g) := by
  rintro (a | _ | a) (b | _ | b) h <;> simp_all [map, hf.eq_iff, hg.eq_iff]

/-- A function on leaves from one on lexical items and one on traces. -/
def elim {M : Sort*} (ℓ : L → M) (τ : Option ι → M) : Leaf L ι → M
  | lex a => ℓ a
  | trace => τ none
  | traceOf i => τ (some i)

@[simp] theorem elim_lex {M : Sort*} (ℓ : L → M) (τ : Option ι → M) (a : L) :
    elim ℓ τ (lex a) = ℓ a := rfl

@[simp] theorem elim_trace {M : Sort*} (ℓ : L → M) (τ : Option ι → M) :
    elim ℓ τ trace = τ none := rfl

@[simp] theorem elim_traceOf {M : Sort*} (ℓ : L → M) (τ : Option ι → M) (i : ι) :
    elim ℓ τ (traceOf i) = τ (some i) := rfl

/-- A leaf is a lexical item or a trace, which is index-free or labelled. -/
def sumEquiv : Leaf L ι ≃ L ⊕ Option ι where
  toFun := elim .inl .inr
  invFun := Sum.elim lex fun o ↦ o.elim trace traceOf
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with _ | _ | _ <;> rfl

end Leaf

end SyntacticObject

/-- The planar syntactic objects over `L` with traces labelled in `ι`, the free magma on the
leaves: [marcolli-chomsky-berwick-2025] §1.12's planar syntactic objects. -/
abbrev PlanarSyntacticObject (L : Type := LexicalItem.Token) (ι : Type := L) : Type :=
  FreeMagma (SyntacticObject.Leaf L ι)

/-- The syntactic objects over `L` with traces labelled in `ι`, the free commutative magma on the
leaves. -/
abbrev SyntacticObject (L : Type := LexicalItem.Token) (ι : Type := L) : Type :=
  FreeCommMagma (SyntacticObject.Leaf L ι)

namespace PlanarSyntacticObject

open SyntacticObject (Leaf)

variable {L ι : Type}

/-- A lexical leaf. -/
@[coe] def leaf (a : L) : PlanarSyntacticObject L ι := FreeMagma.of (.lex a)

/-- The index-free trace. -/
def trace : PlanarSyntacticObject L ι := FreeMagma.of .trace

/-- The trace labelled `i`. -/
def labelledTrace (i : ι) : PlanarSyntacticObject L ι := FreeMagma.of (.traceOf i)

/-- The trace of the item `a`, a trace labelled by an item. -/
abbrev traceOf (a : L) : PlanarSyntacticObject L := labelledTrace a

/-- Merge, with the daughters in the given order, also written `*`. -/
abbrev merge (l r : PlanarSyntacticObject L ι) : PlanarSyntacticObject L ι := l * r

/-- Forgetting the order is the quotient map to the syntactic object. -/
@[coe] def toSyntacticObject (p : PlanarSyntacticObject L ι) : SyntacticObject L ι :=
  FreeMagma.toFreeCommMagma p

theorem toSyntacticObject_surjective :
    Function.Surjective (toSyntacticObject : PlanarSyntacticObject L ι → SyntacticObject L ι) :=
  FreeMagma.toFreeCommMagma_surjective

end PlanarSyntacticObject

namespace SyntacticObject

variable {L ι : Type}

/-- A lexical leaf. -/
@[coe] def leaf (a : L) : SyntacticObject L ι := FreeCommMagma.of (.lex a)

/-- The index-free trace, the mark an admissible cut leaves in the remaining tree
    ([marcolli-chomsky-berwick-2025], Definition 1.2.6); `labelledTrace` is the labelled trace. -/
def trace : SyntacticObject L ι := FreeCommMagma.of .trace

/-- The trace labelled `i`. -/
def labelledTrace (i : ι) : SyntacticObject L ι := FreeCommMagma.of (.traceOf i)

/-- The trace of the item `a`, a trace labelled by an item. -/
abbrev traceOf (a : L) : SyntacticObject L := labelledTrace a

/-- Merge on the carrier, the product of the free commutative magma, also written `*`. -/
abbrev merge (l r : SyntacticObject L ι) : SyntacticObject L ι := l * r

@[simp] theorem leaf_inj {a b : L} : (leaf a : SyntacticObject L ι) = leaf b ↔ a = b :=
  ⟨fun h ↦ by injection FreeCommMagma.of_injective h, congrArg leaf⟩

theorem merge_comm (l r : SyntacticObject L ι) : merge l r = merge r l := mul_comm l r

theorem merge_eq_merge_iff {l r l' r' : SyntacticObject L ι} :
    merge l r = merge l' r' ↔ l = l' ∧ r = r' ∨ l = r' ∧ r = l' :=
  FreeCommMagma.mul_eq_mul_iff

@[simp]
theorem leaf_ne_merge (a : L) (l r : SyntacticObject L ι) : leaf a ≠ merge l r :=
  FreeCommMagma.of_ne_mul _ l r

@[simp]
theorem leaf_ne_trace (a : L) : (leaf a : SyntacticObject L ι) ≠ trace :=
  fun h ↦ by injection FreeCommMagma.of_injective h

@[simp]
theorem leaf_ne_labelledTrace (a : L) (i : ι) : (leaf a : SyntacticObject L ι) ≠ labelledTrace i :=
  fun h ↦ by injection FreeCommMagma.of_injective h

@[simp]
theorem labelledTrace_ne_merge (i : ι) (l r : SyntacticObject L ι) :
    labelledTrace i ≠ merge l r :=
  FreeCommMagma.of_ne_mul _ l r

@[simp]
theorem labelledTrace_ne_leaf (i : ι) (b : L) : (labelledTrace i : SyntacticObject L ι) ≠ leaf b :=
  fun h ↦ by injection FreeCommMagma.of_injective h

@[simp] theorem labelledTrace_inj {i j : ι} :
    (labelledTrace i : SyntacticObject L ι) = labelledTrace j ↔ i = j :=
  ⟨fun h ↦ by injection FreeCommMagma.of_injective h, congrArg labelledTrace⟩

@[simp]
theorem trace_ne_labelledTrace (i : ι) : (trace : SyntacticObject L ι) ≠ labelledTrace i :=
  fun h ↦ by injection FreeCommMagma.of_injective h

@[simp]
theorem trace_ne_merge (l r : SyntacticObject L ι) : (trace : SyntacticObject L ι) ≠ merge l r :=
  FreeCommMagma.of_ne_mul _ l r

end SyntacticObject

namespace PlanarSyntacticObject

open SyntacticObject (Leaf)

variable {L ι : Type}

@[simp] theorem toSyntacticObject_leaf (a : L) :
    (leaf a : PlanarSyntacticObject L ι).toSyntacticObject = SyntacticObject.leaf a := rfl

@[simp] theorem toSyntacticObject_trace :
    (trace : PlanarSyntacticObject L ι).toSyntacticObject = SyntacticObject.trace := rfl

@[simp] theorem toSyntacticObject_labelledTrace (i : ι) :
    (labelledTrace i : PlanarSyntacticObject L ι).toSyntacticObject =
      SyntacticObject.labelledTrace i := rfl

/-- Forgetting the order commutes with Merge. -/
@[simp] theorem toSyntacticObject_merge (l r : PlanarSyntacticObject L ι) :
    (merge l r).toSyntacticObject = SyntacticObject.merge l.toSyntacticObject r.toSyntacticObject :=
  map_mul FreeMagma.toFreeCommMagma l r

end PlanarSyntacticObject

namespace SyntacticObject

variable {L ι : Type}

/-- Induction on syntactic objects, each of which is a lexical leaf, a trace, or the Merge of two
    syntactic objects. -/
@[elab_as_elim]
theorem ind {motive : SyntacticObject L ι → Prop}
    (leaf : ∀ a, motive (leaf a)) (trace : motive trace)
    (traceOf : ∀ i, motive (labelledTrace i))
    (merge : ∀ l r, motive l → motive r → motive (merge l r)) (s : SyntacticObject L ι) :
    motive s := by
  induction s using FreeCommMagma.inductionOn with
  | of x => cases x with
    | lex a => exact leaf a
    | trace => exact trace
    | traceOf i => exact traceOf i
  | mul x y hx hy => exact merge x y hx hy

/-- A syntactic object is a lexical leaf, a trace, or a Merge. -/
theorem exists_form (s : SyntacticObject L ι) :
    (∃ a, s = leaf a) ∨ s = trace ∨ (∃ i, s = labelledTrace i) ∨ (∃ l r, s = merge l r) := by
  induction s using ind with
  | leaf a => exact Or.inl ⟨a, rfl⟩
  | trace => exact Or.inr (Or.inl rfl)
  | traceOf i => exact Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))
  | merge l r _ _ => exact Or.inr (Or.inr (Or.inr ⟨l, r, rfl⟩))

end SyntacticObject

namespace PlanarSyntacticObject

open SyntacticObject (Leaf)

variable {L L' L'' : Type}

/-- The planar object with its labels relabelled by `f`. -/
def map (f : L → L') (p : PlanarSyntacticObject L) : PlanarSyntacticObject L' :=
  FreeMagma.map (Leaf.map f f) p

@[simp] theorem map_leaf (f : L → L') (a : L) : (leaf a).map f = leaf (f a) := rfl

@[simp] theorem map_trace (f : L → L') : (trace : PlanarSyntacticObject L).map f = trace := rfl

@[simp] theorem map_traceOf (f : L → L') (a : L) : (traceOf a).map f = traceOf (f a) := rfl

@[simp] theorem map_merge (f : L → L') (l r : PlanarSyntacticObject L) :
    (merge l r).map f = merge (l.map f) (r.map f) := rfl

@[simp] theorem map_id (p : PlanarSyntacticObject L) : p.map id = p := by
  induction p using FreeMagma.recOnMul with
  | ih1 x => cases x <;> rfl
  | ih2 l r hl hr => exact congrArg₂ (· * ·) hl hr

@[simp] theorem map_map (f : L → L') (g : L' → L'') (p : PlanarSyntacticObject L) :
    (p.map f).map g = p.map (g ∘ f) := by
  induction p using FreeMagma.recOnMul with
  | ih1 x => cases x <;> rfl
  | ih2 l r hl hr => exact congrArg₂ (· * ·) hl hr

theorem map_injective {f : L → L'} (hf : Function.Injective f) :
    Function.Injective (map f : PlanarSyntacticObject L → PlanarSyntacticObject L') := by
  intro p
  induction p using FreeMagma.recOnMul with
  | ih1 x =>
    intro q h
    cases q with
    | of y => exact congrArg FreeMagma.of (Leaf.map_injective hf hf (by injection h))
    | mul _ _ => cases h
  | ih2 l r hl hr =>
    intro q h
    cases q with
    | of y => cases h
    | mul l' r' => injection h with h₁ h₂; rw [hl h₁, hr h₂]; rfl

end PlanarSyntacticObject

namespace SyntacticObject

variable {L L' L'' : Type}

/-- The syntactic object with its labels relabelled by `f`, the homomorphism of free commutative
magmas that a map of lexical alphabets induces. -/
def map (f : L → L') (s : SyntacticObject L) : SyntacticObject L' :=
  FreeCommMagma.map (Leaf.map f f) s

@[simp] theorem _root_.Minimalist.PlanarSyntacticObject.toSyntacticObject_map (f : L → L')
    (p : PlanarSyntacticObject L) :
    (p.map f).toSyntacticObject = p.toSyntacticObject.map f := by
  induction p using FreeMagma.recOnMul with
  | ih1 x => rfl
  | ih2 l r hl hr =>
    show FreeMagma.toFreeCommMagma (FreeMagma.map (Leaf.map f f) (l * r))
      = FreeCommMagma.map (Leaf.map f f) (FreeMagma.toFreeCommMagma (l * r))
    rw [map_mul, map_mul, map_mul, map_mul]
    exact congrArg₂ (· * ·) hl hr

@[simp] theorem map_leaf (f : L → L') (a : L) : (leaf a).map f = leaf (f a) := rfl

@[simp] theorem map_trace (f : L → L') : (trace : SyntacticObject L).map f = trace := rfl

@[simp] theorem map_traceOf (f : L → L') (a : L) : (traceOf a).map f = traceOf (f a) := rfl

@[simp] theorem map_merge (f : L → L') (l r : SyntacticObject L) :
    (merge l r).map f = merge (l.map f) (r.map f) :=
  map_mul (FreeCommMagma.map (Leaf.map f f)) l r

@[simp] theorem map_id (s : SyntacticObject L) : s.map id = s := by
  rw [map, Leaf.map_id, FreeCommMagma.map_id]; rfl

@[simp] theorem map_map (f : L → L') (g : L' → L'') (s : SyntacticObject L) :
    (s.map f).map g = s.map (g ∘ f) := by
  rw [map, map, map, ← Leaf.map_comp, FreeCommMagma.map_comp]; rfl

theorem map_injective {f : L → L'} (hf : Function.Injective f) :
    Function.Injective (map f : SyntacticObject L → SyntacticObject L') :=
  FreeCommMagma.map_injective (Leaf.map_injective hf hf)

end SyntacticObject

end Minimalist
