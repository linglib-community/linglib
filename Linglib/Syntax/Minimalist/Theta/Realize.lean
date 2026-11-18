module

public import Linglib.Syntax.Minimalist.Theta.Basic
public import Linglib.Syntax.Minimalist.SyntacticObject.Build

/-!
# Realization of colored trees

The colored trees of theta theory are anchored in the leaf alphabet of syntactic objects, lexical
items and traces, and realize in the magma of syntactic objects with its unit `1`, the formal empty
tree. Realization prunes the colors and evaluates the remaining free-magma element: an anchored
leaf becomes its syntactic object, a vertex becomes Merge, and the empty-tree marker becomes the
unit, so that a movement landing site realizes to its host unchanged.

## Main definitions

* `realize`: the evaluation of a colored tree in `WithOne (SyntacticObject L)`.

## Main statements

* `realize_node_emptyTree_right`: the unit law, under which movement landing sites leave no mark
  on the realized object.
* `realize_ne_one`: a tree with an anchored input realizes to a syntactic object.

## References

* [marcolli-larson-2025]
* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist.Theta

open SyntacticObject

variable {L : Type}

/-- What an input color contributes to the realization: an anchored leaf its syntactic object, a
lexical item or a trace, and the empty-tree marker and bare grids the unit. -/
def Color.object : Color (L ⊕ Option L) → WithOne (SyntacticObject L)
  | .lex a _ => (FreeCommMagma.of (Leaf.sumEquiv.symm a) : SyntacticObject L)
  | _ => 1

@[simp] theorem Color.object_lex (a : L ⊕ Option L) (g : List PolarizedRole) :
    (Color.lex a g).object = (FreeCommMagma.of (Leaf.sumEquiv.symm a) : SyntacticObject L) := rfl

@[simp] theorem Color.object_free (g : List PolarizedRole) :
    (Color.free g : Color (L ⊕ Option L)).object = 1 := rfl

@[simp] theorem Color.object_emptyTree :
    (Color.emptyTree : Color (L ⊕ Option L)).object = 1 := rfl

/-- The syntactic object a colored tree builds, or the unit: the pruned tree evaluated in the
magma of syntactic objects with its unit adjoined. -/
noncomputable def realize (x : Bud.Tree (Color (L ⊕ Option L))) : WithOne (SyntacticObject L) :=
  FreeMagma.lift Color.object x.prune

@[simp] theorem realize_leaf (c : Color (L ⊕ Option L)) : realize (.leaf c) = c.object := rfl

@[simp] theorem realize_node (c : Color (L ⊕ Option L)) (l r : Bud.Tree (Color (L ⊕ Option L))) :
    realize (.node c l r) = realize l * realize r :=
  map_mul ..

/-- The unit law `M(T, 1) = T`: a movement landing site realizes to its host unchanged, the
empty-tree marker existing only for the coloring. -/
theorem realize_node_emptyTree_right {c : Color (L ⊕ Option L)}
    {x : Bud.Tree (Color (L ⊕ Option L))} :
    realize (.node c x (.leaf .emptyTree)) = realize x := by
  simp

/-- A tree with an anchored input realizes to a syntactic object. -/
theorem realize_ne_one {x : Bud.Tree (Color (L ⊕ Option L))}
    (h : ∃ a g, Color.lex a g ∈ x.inputs) : realize x ≠ 1 := by
  induction x with
  | leaf c =>
    obtain ⟨a, g, hmem⟩ := h
    obtain rfl : Color.lex a g = c := by simpa using hmem
    simp
  | node c l r ihl ihr =>
    obtain ⟨a, g, hmem⟩ := h
    rw [realize_node]
    rcases List.mem_append.mp (by simpa using hmem) with hmem | hmem
    · obtain ⟨L, hL⟩ := WithOne.ne_one_iff_exists.1 (ihl ⟨a, g, hmem⟩)
      induction realize r using WithOne.cases_on <;> simp [← hL, ← WithOne.coe_mul]
    · obtain ⟨R, hR⟩ := WithOne.ne_one_iff_exists.1 (ihr ⟨a, g, hmem⟩)
      induction realize l using WithOne.cases_on <;> simp [← hR, ← WithOne.coe_mul]

end Minimalist.Theta
