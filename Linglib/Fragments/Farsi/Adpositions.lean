module

public import Linglib.Syntax.Category.Adposition.Basic

/-!
# Persian prepositions

The prepositions of Persian as `Adposition` entries: so far the comitative *ba* 'with', which
stands between the two noun phrases of an accompaniment, the verb agreeing with the one before it,
and which differs from the coordinators *væ* and *-o* 'and'. Forms are in Mahootian's
transcription.

## Main definitions

* `Farsi.Adpositions.ba`: the comitative preposition.

## References

* [mahootian-1997]
-/

@[expose] public section

namespace Farsi.Adpositions

/-- *ba* 'with', marking a companion, *mæn ba færzad šam xord-æm* 'I ate dinner with Farzad',
[mahootian-1997] p. 81, (329); it takes the pronominal clitics, *ba-hatun* 'with you', p. 265. -/
def ba : Adposition :=
  { morphs := [.free "ba"], linearization := {.pre}, functions := {.com},
    complements := {some .np} }

end Farsi.Adpositions
