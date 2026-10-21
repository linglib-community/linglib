module

public import Linglib.Semantics.Reference.Definiteness
public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Fragments.German.Determiners
public import Linglib.Fragments.Fering.Determiners
public import Linglib.Fragments.Akan.Determiners
public import Linglib.Fragments.MauritianCreole.Determiners
public import Linglib.Fragments.HaitianCreole.Determiners
public import Linglib.Fragments.Lakhota.Determiners
public import Linglib.Fragments.Hausa.Determiners

/-!
# Schwarz (2013): Two Kinds of Definites Cross-linguistically

This file formalizes the survey's typology of definite articles. Beyond the German and Fering
baseline of Schwarz's dissertation, where a weak article marks situational uniqueness and a strong
one anaphoricity, the survey finds languages whose only overt definite article is anaphoric, with
weak definites as bare nominals (Akan *nó*, Mauritian Creole *la*), languages with two overt
articles (Lakhota *kiŋ* and *k'uŋ*, Hausa *-n* and *ɗîn*), and Haitian Creole *la*, a single article
covering both use families that fits neither pattern. Each language's pattern, which strengths its
inventory marks and whether one article marks both, is derived from its fragment's
`Determiners.inventory`, and the bridging split, part-whole bridging with the weak article and
producer bridging with the strong one, is `DefiniteDescription.Bridging.strength`. The Lakhota
classification is tentative in the survey itself, whose footnote 16 concedes Ingham's anaphoric
*kiŋ*; the project fragment encodes that anaphoric use, under which *kiŋ* marks both strengths
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

/-- German and Fering each split the definite paradigm in two, Fering's A-form against its
D-form and German's contracted against its full preposition-article forms, so both strengths are
marked and by distinct articles. -/
theorem german_fering_two_articles :
    (German.Determiners.inventory.strengths = Finset.univ ∧
      ¬ German.Determiners.inventory.IsSyncretic) ∧
    (Fering.Determiners.inventory.strengths = Finset.univ ∧
      ¬ Fering.Determiners.inventory.IsSyncretic) :=
  ⟨⟨German.Determiners.strengths_inventory, German.Determiners.not_isSyncretic_inventory⟩,
    ⟨Fering.Determiners.strengths_inventory, Fering.Determiners.not_isSyncretic_inventory⟩⟩

/-- In German (16) and Fering (17) alike, part-whole bridging, the fridge and its crisper, takes the
weak article, and producer bridging, the play and its author, the strong one (§3.2). -/
theorem bridging_split :
    DefiniteDescription.Bridging.strength .partWhole = .uniqueness ∧
    DefiniteDescription.Bridging.strength .relational = .familiarity :=
  ⟨rfl, rfl⟩

/-! ### Languages with exclusively anaphoric articles (§4.1) -/

/-- Akan *nó* and Mauritian Creole *la* mark only anaphoric definites, weak definites being bare
nominals. -/
theorem exclusively_anaphoric :
    Akan.Determiners.inventory.strengths = {.familiarity} ∧
    MauritianCreole.Determiners.inventory.strengths = {.familiarity} :=
  ⟨Akan.Determiners.strengths_inventory, MauritianCreole.Determiners.strengths_inventory⟩

/-! ### Languages with two articles (§4.2) -/

/-- Hausa splits its two overt articles (§4.2.2), suffixal *-n* for uniquely identifiable
referents, inferable first mentions included, and *ɗîn* for discourse-old ones, as German and Fering
do. -/
theorem hausa_two_articles :
    Hausa.Determiners.inventory.strengths = Finset.univ ∧
      ¬ Hausa.Determiners.inventory.IsSyncretic :=
  ⟨Hausa.Determiners.strengths_inventory, Hausa.Determiners.not_isSyncretic_inventory⟩

/-- The tentative construal of Lakhota in §4.2.1 takes *kiŋ* as weak only, for globally and
situationally unique referents ((30), (31)), and *k'uŋ* as the anaphoric strong article, 'the
above-mentioned'. -/
def lakhotaWeakStrongConstrual : Determiner.Inventory :=
  [ .article { form := "kiŋ", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := {.immediateSituation, .largerSituation} },
    .article { form := "k'uŋ", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := {.anaphoric} } ]

/-- Under the tentative construal, Lakhota patterns with German and Fering. -/
theorem construal_two_articles :
    lakhotaWeakStrongConstrual.strengths = Finset.univ ∧
      ¬ lakhotaWeakStrongConstrual.IsSyncretic := by
  decide

/-- Granting [ingham-2003]'s anaphoric *kiŋ*, as footnote 16 does and the project fragment does,
makes *kiŋ* mark both strengths, so the weak and strong parallel is indeed less extensive. -/
theorem anaphoric_kin_syncretic :
    ¬ lakhotaWeakStrongConstrual.IsSyncretic ∧ Lakhota.Determiners.inventory.IsSyncretic :=
  ⟨construal_two_articles.2, Lakhota.Determiners.isSyncretic_inventory⟩

/-! ### Haitian Creole: a different type of contrast (§4.3) -/

/-- Haitian Creole *la* covers uniqueness at every level, anaphora and both bridging types
((39) to (42)), a single article marking both strengths, neither the §4.1 nor the §4.2 pattern. -/
theorem haitian_one_article : HaitianCreole.Determiners.inventory.IsSyncretic :=
  HaitianCreole.Determiners.isSyncretic_inventory

end Schwarz2013
