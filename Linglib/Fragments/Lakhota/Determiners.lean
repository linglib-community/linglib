module

public import Linglib.Syntax.Category.Determiner.Basic

/-!
# Lakhota determiner inventory

Lakhota (Siouan, ISO `lkt`) has two overt definite articles: the general
*kiŋ*, with both situational and anaphoric uses, and *k'uŋ* 'the
above-mentioned', restricted to previously-mentioned referents and far
rarer ([latrouite-van-valin-2014]; [ingham-2003b] §15.1 has *ki* "for new
or previously mentioned items without distinction" and *k'uŋ* as an
infrequent switch back to an earlier topic — endorsing [curl-1999]'s
topic-marking account — or an emphatic marker of 'enforced reality').
Because *kiŋ* covers anaphora it marks both strengths (`isSyncretic_inventory`);
a weak and a strong article follow only under Schwarz's (2013, §4.2.1) tentative
weak/strong construal of the pair, disputed also by [ingham-2003] (the
element is basically a topic marker) and [ogorman-2011] (accessibility).
Covarying (donkey) uses are unreported for either article. The singular
specific (realis) indefinite article is *waŋ*, opposed to non-specific
*waŋži* ([rood-taylor-1996] Table 3; [latrouite-van-valin-2014] Table 1;
[ingham-2003b] §15.1.4); the non-specific, negative, and plural series
are not typed here.

## References

* [latrouite-van-valin-2014]
* [ingham-2003]
* [ingham-2003b], §14–§15
* [schwarz-2013], §4.2.1
* [rood-taylor-1996]
-/

@[expose] public section

namespace Lakhota.Determiners

/-- The Lakhota determiners are the general definite *kiŋ*, the
    anaphoric-only definite *k'uŋ*, and the specific indefinite *waŋ*. -/
def inventory : Determiner.Inventory :=
  [ .article { form := "kiŋ", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := {.immediateSituation, .largerSituation, .anaphoric} },
    .article { form := "k'uŋ", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := {.anaphoric} },
    .article { form := "waŋ", definiteness := .indefinite, exponent := .dedicatedMorpheme } ]

theorem isSyncretic_inventory : inventory.IsSyncretic := by decide

end Lakhota.Determiners
