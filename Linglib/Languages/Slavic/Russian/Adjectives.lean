module

public import Linglib.Syntax.Category.Adjective.Basic

/-!
# Russian adjectives

Each entry records the morphological comparative, unanalysed as one root, and the periphrastic
superlative, the degree word *samyj* 'most' with the positive. Since *samyj* embeds the positive,
a suppletive comparative root does not recur in the superlative, and the root pattern of
*xoroš-ij*, *luč-še*, *samyj xoroš-ij* is ABA. A literary morphological superlative such as
*nai-xud-š-ij* 'worst', which Bobaljik discusses beside the periphrasis (§3.3.3), is not entered.

Forms are in scientific transliteration. A consonant mutation before *-e* (*sux-oj*, *suš-e* and
*prost-oj*, *prošč-e*) is phonological and leaves the root pattern AAA.

## References

* [bobaljik-2012]
-/

@[expose] public section

namespace Russian.Adjectives

open Morphology

/-- The degree word *samyj* 'most' of the periphrastic superlative. -/
def samyj : Morph := .free "samyj"

/-- The adjective `form` with the comparative `comparative`, whose superlative is *samyj* with
the positive. -/
def entry (form script comparative : String) : Adjective :=
  { form, script := some script
    comparison := { comparative := [.root comparative], superlative := [samyj, .root form] } }

/-! ### Regular adjectives -/

/-- *sux-oj – suš-e – samyj sux-oj* 'dry'. -/
def suxoj : Adjective := entry "suxoj" "сухой" "suše"

/-- *prost-oj – prošč-e – samyj prost-oj* 'simple'. -/
def prostoj : Adjective := entry "prostoj" "простой" "prošče"

/-! ### Suppletive adjectives -/

/-- *xoroš-ij – luč-še – samyj xoroš-ij* 'good'. *Samyj luč-š-ij* also occurs, which
[bobaljik-2012] takes to be a vestigial morphological superlative reinforced by *samyj*. -/
def xoroshij : Adjective := entry "xorošij" "хороший" "lučše"

/-- *plox-oj – xuž-e – samyj plox-oj* 'bad', with the comparative root *xud-* mutated before
*-e*. -/
def ploxoj : Adjective := entry "ploxoj" "плохой" "xuže"

/-! ### Inventory -/

/-- Every entry of the fragment. -/
def allEntries : List Adjective := [suxoj, prostoj, xoroshij, ploxoj]

end Russian.Adjectives
