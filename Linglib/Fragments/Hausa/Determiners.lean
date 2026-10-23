module

public import Linglib.Syntax.Category.Determiner.Basic

/-!
# Hausa determiners

Hausa has two definite determiners after the noun. The suffix *-n*, *-r̃* after a feminine
singular in *-a*, carries a floating low tone and marks a referent as uniquely identifiable,
either mentioned before or inferable from the context: *yārò* 'boy', *yārò-n* 'the boy'. The
anaphoric *ɗîn* marks a referent that is always discourse-old and never merely inferable. The
specific indefinite determiner is *wani* (feminine *wata*, plural *wa(ɗan)su*). The universals
are the distributive *kōwànè* (feminine *kōwàcè*) 'every, each', which usually modifies a
singular count noun, and the collective *duk* or *dukà* 'all', which does not inflect and
quantifies singular and plural count nouns and mass nouns alike ([jaggar-2001]). The two-article
classification is tentative: a bare noun can also be definite, as *rānā* 'the sun', and
consonant-final loanwords take *ɗîn* in place of *-n* ([schwarz-2013]).

## Main definitions

* `Hausa.Determiners.inventory`: the determiners, whose two definite articles mark the two
  strengths (`strengths_inventory`).

## References

* [jaggar-2001]
* [moroney-2021]
* [schwarz-2013]
-/

@[expose] public section

namespace Hausa.Determiners

/-- The definite suffix *-n*, for a uniquely identifiable referent. -/
def n : Article :=
  { form := "-n", definiteness := .definite, exponent := .dedicatedMorpheme,
    uses := {.largerSituation} }

/-- The anaphoric *ɗîn*, for a discourse-old referent. -/
def din : Article :=
  { form := "ɗîn", definiteness := .definite, exponent := .dedicatedMorpheme,
    uses := {.anaphoric} }

/-- The specific indefinite *wani*. -/
def wani : Article :=
  { form := "wani", definiteness := .indefinite, exponent := .dedicatedMorpheme }

/-- The distributive universal *kōwànè* 'every, each', masculine. -/
def kowane : Quantifier := { form := "kōwànè", numberRestriction := some .singular }

/-- The distributive universal *kōwàcè* 'every, each', feminine. -/
def kowace : Quantifier := { form := "kōwàcè", numberRestriction := some .singular }

/-- The collective universal *duk* 'all'. -/
def duk : Quantifier := { form := "duk", selectsMass := true }

/-- The determiners. -/
def inventory : Determiner.Inventory :=
  [.article n, .article din, .article wani, .quantifier kowane, .quantifier kowace,
    .quantifier duk]

/-- Both strengths are marked, by distinct articles. -/
theorem strengths_inventory : inventory.strengths = Finset.univ := by decide

theorem not_isSyncretic_inventory : ¬ inventory.IsSyncretic := by decide

end Hausa.Determiners
