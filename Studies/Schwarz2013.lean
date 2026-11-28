module

public import Linglib.Semantics.Reference.Definiteness
public import Linglib.Semantics.Reference.Strength
public import Linglib.Languages.German.Determiners
public import Linglib.Languages.Fering.Determiners
public import Linglib.Languages.Akan.Determiners
public import Linglib.Languages.MauritianCreole.Determiners
public import Linglib.Languages.HaitianCreole.Determiners
public import Linglib.Languages.Lakhota.Determiners
public import Linglib.Languages.Hausa.Determiners

/-!
# Schwarz (2013): Two Kinds of Definites Cross-linguistically

This file formalizes the survey's typology of definite articles. Beyond the German and Fering
baseline of Schwarz's dissertation, where a weak article marks situational uniqueness and a strong
one anaphoricity, the survey finds languages whose only overt definite article is anaphoric, with
weak definites as bare nominals (Akan *nó*, Mauritian Creole *la*), languages with two overt
articles (Lakhota *kiŋ* and *k'uŋ*, Hausa *-n* and *ɗîn*), and Haitian Creole *la*, a single article
covering both use families that fits neither pattern. Each language's pattern, which strengths its
inventory marks and whether one article marks both, is derived from its language file's
`Determiners.inventory`. The parallels extend to bridging: in German, Fering, Akan and the two
creoles an article bridges to a part where it has the situational uses and by a relation, as
from a product to its producer, where it is anaphoric. The Lakhota
classification is tentative in the survey itself, whose footnote 16 concedes Ingham's anaphoric
*kiŋ*; the project language file encodes that anaphoric use, under which *kiŋ* marks both strengths
(`anaphoric_kin_syncretic`).

## Implementation notes

The survey's remark that both German and Fering articles and the creole *la* allow covarying uses
(§5.2) is not a property of the inventories: both articles covary, by the mechanisms of the
substrate's two descriptions.

## References

* [schwarz-2013]
* [schwarz-2009]
* [ingham-2003]
* [wespel-2008]
-/

@[expose] public section

namespace Schwarz2013

/-! ### The German/Fering baseline (§3.1) -/

theorem german_fering_two_articles :
    (German.Determiners.inventory.strengths = Finset.univ ∧
      ¬ German.Determiners.inventory.IsSyncretic) ∧
    (Fering.Determiners.inventory.strengths = Finset.univ ∧
      ¬ Fering.Determiners.inventory.IsSyncretic) := by
  decide

/-! ### Bridging (§3.2, §4.1, §4.3) -/

/-- In German, Fering, Akan, Mauritian Creole and Haitian Creole an article has a use exactly when
it marks the strength the use calls for, so part-whole bridging goes with the situational uses and
relational bridging with the anaphoric use. The survey has no bridging example for Hausa and none
it takes to be clear for the strong article of Lakhota. -/
-- (16), (17), (23), (24), (28), (29), (41), (42)
theorem mem_uses_iff_strength_mem_strengths :
    ∀ ds ∈ [German.Determiners.inventory, Fering.Determiners.inventory,
        Akan.Determiners.inventory, MauritianCreole.Determiners.inventory,
        HaitianCreole.Determiners.inventory],
      ∀ e ∈ ds, ∀ u, u ∈ e.uses ↔ u.strength ∈ e.strengths := by
  decide

/-! ### Languages with exclusively anaphoric articles (§4.1) -/

theorem exclusively_anaphoric :
    Akan.Determiners.inventory.strengths = {.familiarity} ∧
    MauritianCreole.Determiners.inventory.strengths = {.familiarity} := by
  decide

/-! ### Languages with two articles (§4.2) -/

-- §4.2.2
theorem hausa_two_articles :
    Hausa.Determiners.inventory.strengths = Finset.univ ∧
      ¬ Hausa.Determiners.inventory.IsSyncretic := by
  decide

/-- The tentative construal of Lakhota in §4.2.1 takes *kiŋ* as weak only, for globally and
situationally unique referents ((30), (31)) and part-whole bridging (34), and *k'uŋ* as the
anaphoric strong article, 'the above-mentioned'. -/
def lakhotaWeakStrongConstrual : Determiner.Inventory :=
  [ .article { form := "kiŋ", definiteness := {.definite}, exponent := .dedicatedMorpheme,
               uses := {.immediateSituation, .largerSituation, .bridging .partWhole} },
    .article { form := "k'uŋ", definiteness := {.definite}, exponent := .dedicatedMorpheme,
               uses := {.anaphoric} } ]

theorem construal_two_articles :
    lakhotaWeakStrongConstrual.strengths = Finset.univ ∧
      ¬ lakhotaWeakStrongConstrual.IsSyncretic := by
  decide

/-- Granting [ingham-2003]'s anaphoric *kiŋ*, as footnote 16 does, *kiŋ* marks both strengths. -/
theorem anaphoric_kin_syncretic :
    ¬ lakhotaWeakStrongConstrual.IsSyncretic ∧ Lakhota.Determiners.inventory.IsSyncretic := by
  decide

/-! ### Haitian Creole: a different type of contrast (§4.3) -/

-- (39), (42), §4.1, §4.2
theorem haitian_one_article : HaitianCreole.Determiners.inventory.IsSyncretic := by
  decide

end Schwarz2013
