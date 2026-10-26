module

public import Linglib.Syntax.Category.Particle.Basic

/-!
# Mandarin question particles

Mandarin forms a polar question from a declarative by rising intonation or by the sentence-final
particle *ma* 吗, which marks nothing but questions, and its other questions by a question word in
situ or by a disjunction, *háishi* 'or' or the A-not-A form of the predicate. Two other
sentence-final particles also serve in questions. *Ne* 呢 relates a declarative, an A-not-A
question or a question-word question to the hearer's claim or expectation but cannot make a
polar question, so that *ma* and *ne* are in complementary distribution over the interrogative
types. *Ba* 吧 solicits the hearer's agreement, making a statement a question that seeks it and
softening a command, and is not added to a clause already marked as a question. The attitude
adverb *nándào* 难道 'is it conceivable that' forms only matrix polar questions.

## Main declarations

* `Mandarin.QuestionParticles.ma`, `ne`, `ba`, `nandao`: the entries.
* `Mandarin.QuestionParticles.ma_ne_complementary`: *ma* and *ne* in complementary distribution.

## Implementation notes

The A-not-A question fills the alternative cell, since Li and Thompson class it with the *háishi*
question as disjunctive (§18.3), and the rising declarative the polar cell (§18.1). The cells are
theirs: *ma* on p. 547 and in (121)-(124), (150), (152), (221) and (222), *ne* on p. 303 and in
(217)-(219) and (224), *ba* in (126), (225)-(229), (232) and (233). *Ba* is one particle, its use
in commands following from its use with statements (pp. 307-308), and Fang and Hengeveld add its
exclamative cell. Chao's *nǐ dàodǐ yào shénme ba?* (234) is the one question-word question with
*ba* that Li and Thompson accept. Xu reads a question word under *ma* as an indefinite, so that
the string is a polar question (p. 512), and the cells of *nándào* are his (3), (5), (7), (11),
(15), (17) and (34). As a movable adverb *nándào* stands before or after the subject or topic
(Li and Thompson pp. 320, 322), so no position is recorded.

## References

* [li-thompson-1981]
* [fang-hengeveld-2020]
* [xu-2012]
-/

@[expose] public section

namespace Mandarin.QuestionParticles

open Clause

/-- *ma* 吗, the particle that turns a declarative into a polar question. -/
def ma : Particle where
  form := "ma"
  script := some "吗"
  position := some .clauseFinal
  distribution
    | .polar, .matrix => some .optional
    | .declarative, .matrix | .alternative, .matrix | .constituent, .matrix
    | .polar, .subordinated => some .excluded
    | _, _ => none

/-- *ne* 呢, which presents a declarative or a question as a response to the hearer's claim or
expectation. -/
def ne : Particle where
  form := "ne"
  script := some "呢"
  position := some .clauseFinal
  distribution
    | .declarative, .matrix | .alternative, .matrix | .constituent, .matrix => some .optional
    | .polar, .matrix => some .excluded
    | _, _ => none

/-- *ba* 吧, which solicits the hearer's agreement. -/
def ba : Particle where
  form := "ba"
  script := some "吧"
  position := some .clauseFinal
  distribution
    | .declarative, .matrix | .polar, .matrix | .imperative, .matrix
    | .exclamative, .matrix => some .optional
    | .alternative, .matrix | .constituent, .matrix => some .excluded
    | _, _ => none

/-- *nándào* 难道 'is it conceivable that', the attitude adverb of polar questions. -/
def nandao : Particle where
  form := "nándào"
  script := some "难道"
  distribution
    | .polar, .matrix => some .optional
    | .declarative, .matrix | .alternative, .matrix | .constituent, .matrix
    | .declarative, .subordinated | .polar, .subordinated => some .excluded
    | _, _ => none

/-- *Ma* and *ne* are in complementary distribution as sentence-final particles for questions
([li-thompson-1981] p. 306). -/
theorem ma_ne_complementary {t : SentenceType} (ht : t.IsInterrogative) :
    root t ∈ ma.distribution.possible ↔ root t ∉ ne.distribution.possible := by
  rcases ht with rfl | rfl | rfl <;> decide

end Mandarin.QuestionParticles
