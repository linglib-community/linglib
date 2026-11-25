/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Build
public import Linglib.Syntax.Minimalist.LexicalItem

/-!
# Syntactic objects on the tokens of lexical items

The syntactic objects of a derivation are built from the tokens of lexical items. `TokenLeaf`
names those leaves, and this file holds what is said of a leaf through its lexical item.

## Main definitions

* `Minimalist.TokenLeaf`: a token of a lexical item.
* `Minimalist.SyntacticObject.isLeafOf`: a leaf whose item has a given category.
-/

@[expose] public section

namespace Minimalist

/-- The leaves of the syntactic objects of a derivation, the tokens of lexical items. -/
abbrev TokenLeaf : Type := LexicalItem.Token

end Minimalist

namespace Minimalist.SyntacticObject

/-- `s` is a leaf whose item's category is `c`. -/
def isLeafOf (c : Cat) (s : SyntacticObject TokenLeaf) : Prop :=
  s.token?.map (·.item.cat) = some c

instance (c : Cat) : DecidablePred (isLeafOf c) := fun _ ↦ inferInstanceAs (Decidable (_ = _))

@[simp] theorem isLeafOf_leaf (c : Cat) (tok : LexicalItem.Token) :
    isLeafOf c (SyntacticObject.leaf tok) ↔ tok.item.cat = c := by
  simp [isLeafOf]

theorem isLeafOf_map {f : LexicalItem.Token → LexicalItem.Token}
    (hcat : ∀ t, (f t).item.cat = t.item.cat) (c : Cat) (s : SyntacticObject TokenLeaf) :
    isLeafOf c (s.map f) ↔ isLeafOf c s := by
  simp [isLeafOf, token?_map, Option.map_map, Function.comp_def, hcat]

end Minimalist.SyntacticObject
