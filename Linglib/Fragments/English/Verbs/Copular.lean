module

public import Linglib.Syntax.Category.Adjective.ClauseEmbedding
public import Linglib.Syntax.Category.Verb.Basic

/-!
# English copular predicates

This file defines the English predicates of the form *be* + adjective that embed a clause: the
emotive factive *annoyed (that p)* and the veridical non-factive *right (that p)*, which entails
its complement without presupposing it, both from Degen and Tonhauser's projection experiments,
and *able (to VP)*, which Karttunen lists among the positive verbs that are implicative by
default but admit the weaker presupposition of a necessary condition only, so that its negation
entails the negation of the complement while its affirmative need not entail the complement.
The adjectives are `ClauseEmbeddingAdjective` entries, and the copular verbs are their
realization with *be*.

## Main definitions

* `English.Verbs.Copular.annoyed`, `English.Verbs.Copular.right`, `English.Verbs.Copular.able`:
  the adjectives.
* `English.Verbs.Copular.beAnnoyed`, `English.Verbs.Copular.beRight`,
  `English.Verbs.Copular.beAble`: the copular verbs.

## References

* [degen-tonhauser-2021]
* [degen-tonhauser-2022]
* [karttunen-1971]
* [nadathur-2023]
* [nadathur-2023-implicatives]
-/

@[expose] public section

namespace English.Verbs.Copular

open ArgumentStructure

/-- *annoyed (that p)*, an emotive factive adjective. -/
def annoyed : ClauseEmbeddingAdjective where
  form := "annoyed"
  factivity := some .full

/-- *right (that p)*, a veridical non-factive adjective, which entails its complement without
presupposing it. -/
def right : ClauseEmbeddingAdjective where
  form := "right"

/-- *able (to VP)*, a subject-control adjective among the positive verbs of [karttunen-1971]
that are implicative by default but admit the weaker presupposition of a necessary condition
only: *John wasn't able to come* entails that he did not come, while *John was able to come*
need not entail that he came. It is the counterpart of the one-way Finnish *pystyä*
([nadathur-2023-implicatives]). The entailment of the affirmative on its actualized reading is
the actuality entailment of ability, which [nadathur-2023] derives from aspect rather than from
the lexicon: *able* presupposes an action causally necessary and sufficient for the complement
and asserts only the subject's capacity for it, a stative that perfective aspect coerces into an
instance of the action (Proposal (7.10), §7.2). -/
def able : ClauseEmbeddingAdjective where
  form := "able"
  valency := .ofFrame ArgumentFrame.infinitival (controller := some 0)
  implicative := ⟨⊥, .some .negative⟩

/-- *be annoyed (that p)*. -/
def beAnnoyed : Verb := annoyed.toVerb "be"

/-- *be right (that p)*. -/
def beRight : Verb := right.toVerb "be"

/-- *be able (to VP)*. -/
def beAble : Verb := able.toVerb "be"

end English.Verbs.Copular
