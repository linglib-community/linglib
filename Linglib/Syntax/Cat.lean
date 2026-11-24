module

public import Linglib.Data.UD.UPOS

/-!
# Syntactic categories

A syntactic category is a lexical category, named by its Universal Dependencies part of speech, or
the clause `S`, which projects from no head. A category carries no level of projection: a noun
phrase and the noun that heads it both have the category `N`, and whether a node is a minimal, an
intermediate or a maximal projection is read off the tree from its head daughters
(`Syntax/Projection/Tree.lean`). This is the category stripped of bar level that HPSG's head value
records. `PhraseStructure.Cat` is the default category type of `PhraseStructure.Tree`.

## Implementation notes

The complementizer `C` is `SCONJ`, the tag UD gives complementizers, and `Neg` is `PART`, the tag
of English *not* and of other particles.

## References

* [pollard-sag-1994]
* [de-marneffe-zeman-2021]
-/

@[expose] public section

namespace PhraseStructure

/-- A syntactic category is a lexical category or the clause. -/
inductive Cat where
  /-- `lex pos` is the lexical category of part of speech `pos`. -/
  | lex : UD.UPOS → Cat
  /-- `S` is the clause, which projects from no head. -/
  | S
  deriving DecidableEq, Repr

namespace Cat

instance : Inhabited Cat := ⟨S⟩

/-! ### Traditional names

Each name is a `match_pattern`, so it can be used in pattern position. -/

@[match_pattern] abbrev N    : Cat := lex .NOUN
@[match_pattern] abbrev V    : Cat := lex .VERB
@[match_pattern] abbrev Det  : Cat := lex .DET
@[match_pattern] abbrev Adj  : Cat := lex .ADJ
@[match_pattern] abbrev Adv  : Cat := lex .ADV
@[match_pattern] abbrev P    : Cat := lex .ADP
@[match_pattern] abbrev Conj : Cat := lex .CCONJ
@[match_pattern] abbrev Neg  : Cat := lex .PART
@[match_pattern] abbrev C    : Cat := lex .SCONJ
@[match_pattern] abbrev Num  : Cat := lex .NUM
@[match_pattern] abbrev Pron : Cat := lex .PRON
@[match_pattern] abbrev Aux  : Cat := lex .AUX

end Cat

end PhraseStructure
