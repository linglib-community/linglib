module

public import Linglib.Syntax.Category.Adjective.Basic

/-!
# Latin adjectives

The comparison of seven Latin adjectives. A regular adjective forms its comparative with *-ior*
and its superlative with *-issimus* on its stem, *longus*, *longior*, *longissimus*. The
suppletive adjectives show the two other root patterns Bobaljik finds, one root for both grades
in *parvus*, *minor*, *minimus* and three roots in *bonus*, *melior*, *optimus*. Suppletion is
the replacement of one root by another, so *magnus*, *maior*, *maximus*, which keeps its root, is
irregular and not suppletive. The entries record no scalar dimension.

## Implementation notes

An irregular or suppletive grade is entered unanalysed, as one root.

## References

* [bobaljik-2012]
-/

@[expose] public section

namespace Latin.Adjectives

open Morphology

/-! ### Grade -/

/-- The suffix of the comparative. -/
def ior : Morph := .suff "ior"

/-- The suffix of the superlative. -/
def issimus : Morph := .suff "issimus"

/-- The regular comparison of an adjective with the stem `stem`. -/
def regular (stem : String) : Adjective.Comparison :=
  { comparative := [.root stem, ior], superlative := [.root stem, issimus] }

/-! ### Regular adjectives -/

/-- *longus*, *longior*, *longissimus* 'long'. -/
def longus : Adjective := { form := "longus", comparison := regular "long" }

/-- *altus*, *altior*, *altissimus* 'tall, high, deep'. -/
def altus : Adjective := { form := "altus", comparison := regular "alt" }

/-- *fortis*, *fortior*, *fortissimus* 'brave, strong'. -/
def fortis : Adjective := { form := "fortis", comparison := regular "fort" }

/-! ### Irregular and suppletive adjectives -/

/-- *bonus*, *melior*, *optimus* 'good' has three roots, the pattern ABC. -/
def bonus : Adjective :=
  { form := "bonus"
    comparison :=
      { comparative := [.root "melior"], superlative := [.root "optimus"] } }

/-- *malus*, *peior*, *pessimus* 'bad' has one suppletive root, *pēj-* or *pe-*, in both grades
([bobaljik-2012] Table 4.1), the pattern ABB. -/
def malus : Adjective :=
  { form := "malus"
    comparison :=
      { comparative := [.root "peior"], superlative := [.root "pessimus"] } }

/-- *magnus*, *maior*, *maximus* 'great' is irregular and not suppletive, *mag-*, *mai-* and
*max-* being one root; the triple is absent from [bobaljik-2012]'s Table 4.1. -/
def magnus : Adjective :=
  { form := "magnus"
    comparison := { comparative := [.root "maior"], superlative := [.root "maximus"] } }

/-- *parvus*, *minor*, *minimus* 'small' has the suppletive root *min-* in both grades, the
pattern ABB. -/
def parvus : Adjective :=
  { form := "parvus"
    comparison :=
      { comparative := [.root "minor"], superlative := [.root "minimus"] } }

/-! ### Inventory -/

/-- Every entry of the fragment. -/
def allEntries : List Adjective :=
  [longus, altus, fortis, bonus, malus, magnus, parvus]

end Latin.Adjectives
