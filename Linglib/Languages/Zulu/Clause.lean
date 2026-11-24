module

public import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Zulu complementizers

Zulu (Bantu S42) introduces finite complement clauses with *ukuthi* 'that', the verb stem *-thi*
'say' inflected like an infinitive and carrying the augment *u-* of nominals, which also heads
subjunctive complements. *sengathi* 'as if', from the same stem with aspect and mood morphology
and no augment, heads the complements of verbs like *bona* 'see' and *fisa* 'wish', and manner
adjuncts.

## References

* [halpert-2012]
-/

@[expose] public section

namespace Zulu

/-- *ukuthi* 'that' is the augment over *kuthi*, and introduces indicative and subjunctive
complements. -/
def ukuthi : Complementizer where
  morphs := [.pref "u", .root "kuthi"]
  types := .only .declarative
  verbForm := some .Fin

/-- *sengathi* 'as if' bears no augment. -/
def sengathi : Complementizer where
  morphs := [.root "sengathi"]
  types := .only .declarative
  verbForm := some .Fin

end Zulu
