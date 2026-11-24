module

public import Linglib.Syntax.Negation

/-!
# Tunica negation

Tunica negates an active verb with a suffix on its semelfactive form, *-aha* in the negative of the
semelfactive and *-kʔaha* in the negative of the habitual: *lɔ'ta-wi* 'he ran' has the negative
*lɔ'ta-w-ɛhɛ* 'he did not run', and the habitual *lɔ'ta-ku* 'he runs' has the negative
*lɔ'ta-wi-kʔaha* 'he does not run', built on the semelfactive *lɔ'ta-wi*. Miestamo's examples, from
Haas's grammar, are rows of `Data.Examples.Miestamo2005`.

## References

* [miestamo-2005]
* [haas-1940]
-/

@[expose] public section

open Negation

namespace Tunica.Negation

/-- *-aha*, the negative suffix of the semelfactive. -/
def aha : Marker := ⟨[[.suff "aha"]]⟩

/-- *-kʔaha*, the negative suffix of the habitual. -/
def kaha : Marker := ⟨[[.suff "kʔaha"]]⟩

/-- The standard negators. -/
def standard : List Marker := [aha, kaha]

end Tunica.Negation
