module

public import Linglib.Syntax.Minimalist.Theta.Basic
public import Linglib.Syntax.Minimalist.SyntacticObject.Basic

/-!
# Realization of colored trees

Pruning the colors of a theta structure gives the syntactic object it builds: lexically anchored
leaves become lexical leaves, binary vertices become bare Merge, and the empty-tree marker is the
unit of the magma, so that a movement landing site realizes to its host unchanged.

## Main definitions

* `realize`: pruning to the `SyntacticObject` carrier, `none` playing the magma unit.

## Main statements

* `realize_node_emptyTree_right`: the unit law, under which movement landing sites leave no mark
  on the realized object.
* `realize_isSome`: a tree with a lexically anchored input realizes.

## References

* [marcolli-larson-2025]
-/

@[expose] public section

namespace Minimalist.Theta

/-- Prune a colored tree to the syntactic object it builds. Lexically anchored leaves become
lexical leaves, vertices become bare Merge, and `none` is the magma unit, contributed by the
empty-tree marker and, degenerately, by bare-grid leaves, which a tree with terminal inputs
lacks. -/
noncomputable def realize : Bud.Tree (Color LexicalItem.Token) → Option SyntacticObject
  | .leaf (.lex tok _) => some (.leaf tok)
  | .leaf _ => none
  | .node _ l r =>
      match realize l, realize r with
      | some L, some R => some (L.merge R)
      | some L, none => some L
      | none, some R => some R
      | none, none => none

@[simp] theorem realize_leaf_lex (tok : LexicalItem.Token) (g : List PolarizedRole) :
    realize (.leaf (.lex tok g)) = some (.leaf tok) := rfl

@[simp] theorem realize_leaf_emptyTree :
    realize (.leaf .emptyTree) = none := rfl

@[simp] theorem realize_leaf_free (g : List PolarizedRole) :
    realize (.leaf (.free g)) = none := rfl

theorem realize_node_some_some {l r : Bud.Tree (Color LexicalItem.Token)}
    {c : Color LexicalItem.Token} {L R : SyntacticObject} (hl : realize l = some L)
    (hr : realize r = some R) :
    realize (.node c l r) = some (L.merge R) := by
  simp [realize, hl, hr]

@[simp] theorem realize_node_emptyTree_right {x : Bud.Tree (Color LexicalItem.Token)}
    {c : Color LexicalItem.Token} :
    realize (.node c x (.leaf .emptyTree)) = realize x := by
  cases h : realize x <;> simp [realize, h]

theorem realize_isSome {x : Bud.Tree (Color LexicalItem.Token)}
    (h : ∃ tok g, Color.lex tok g ∈ x.inputs) : (realize x).isSome := by
  induction x with
  | leaf c =>
    obtain ⟨tok, g, hmem⟩ := h
    obtain rfl : Color.lex tok g = c := by simpa using hmem
    simp
  | node c l r ihl ihr =>
    obtain ⟨tok, g, hmem⟩ := h
    rcases List.mem_append.mp (by simpa using hmem) with hmem | hmem
    · have := ihl ⟨tok, g, hmem⟩
      obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp this
      cases hr : realize r <;> simp [realize, hL, hr]
    · have := ihr ⟨tok, g, hmem⟩
      obtain ⟨R, hR⟩ := Option.isSome_iff_exists.mp this
      cases hl : realize l <;> simp [realize, hl, hR]

end Minimalist.Theta
