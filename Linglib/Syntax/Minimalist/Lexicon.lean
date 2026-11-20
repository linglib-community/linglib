/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.LexicalItem
public import Mathlib.Data.List.Nodup

/-!
# Declaring a lexicon

The `lexicon` command declares the lexical tokens a derivation draws on. Each entry names a token
and gives its category, optionally followed by the categories it selects, in brackets, and its
phonological form:

```
lexicon tokens where
  /-- The light verb. -/
  v₀ : .v [.V]
  gave : .V [.D] "gave"
  ozzy : .D "Ozzy"
```

Every entry becomes a `LexicalItem.Token` of that name, indexed by its place in the list, counted
from the number after `from` when one is given. The command also defines the list of the tokens,
under the name after `lexicon`, and proves that they are pairwise distinct, `tokens_nodup`.

## Implementation notes

The index of a token tells apart tokens of one lexical item, such as two silent heads of one
category. Numbering every entry makes all tokens of a lexicon distinct without the indices being
chosen by hand, and the generated `Nodup` theorem checks it.
-/

@[expose] public section

namespace Minimalist

/-- An entry of a `lexicon`: a name, a category, the categories it selects and its phonological
form. -/
syntax lexiconEntry := atomic((docComment)? ident " : ") term:max ("[" term,* "]")? (str)?

/-- `lexicon name where entries` declares each entry as a lexical token, the list `name` of the
tokens, and `name_nodup`, that they are pairwise distinct. -/
syntax (docComment)? "lexicon " ident (" from " num)? " where" (ppLine lexiconEntry)+ : command

macro_rules
  | `($[$doc]? lexicon $name $[from $base]? where $entries*) => do
    let base := (base.map (·.getNat)).getD 0
    let mut cmds := #[]
    let mut ids := #[]
    for entry in entries, i in [0:entries.size] do
      match entry with
      | `(lexiconEntry| $[$d]? $x:ident : $c $[[$sel,*]]? $[$phon]?) =>
        let n := Lean.Syntax.mkNumLit (toString (base + i))
        let sel ← match sel with
          | some s => `([$s,*])
          | none => `([])
        let phon := phon.getD (Lean.Syntax.mkStrLit "")
        cmds := cmds.push (← `($[$d]? def $x : Minimalist.LexicalItem.Token :=
          ⟨Minimalist.LexicalItem.of $c $sel $phon, $n⟩))
        ids := ids.push x
      | _ => Lean.Macro.throwUnsupported
    cmds := cmds.push (← `($[$doc]? def $name : List Minimalist.LexicalItem.Token := [$ids,*]))
    let nodup := Lean.mkIdent (name.getId.appendAfter "_nodup")
    cmds := cmds.push (← `(theorem $nodup : List.Nodup $name := by decide))
    return Lean.mkNullNode cmds

end Minimalist
