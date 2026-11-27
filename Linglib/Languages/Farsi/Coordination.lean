module

public import Linglib.Syntax.Category.Coordinator

/-!
# Persian coordinators

This file records the coordinators of Persian, in Mahootian's transcription: *væ* and the clitic
*-o* 'and', the adversative *væli*, *æmma*, *bælke* and *liken*, the disjunctive *ya*, the
negative *næ*, and the emphatic *ya … ya* and *hæm … hæm*.

## Main definitions

* `Farsi.Coordination.va`, `Farsi.Coordination.o`: the conjunctive coordinators.
* `Farsi.Coordination.vali`, `Farsi.Coordination.amma`, `Farsi.Coordination.balke`,
  `Farsi.Coordination.liken`: the adversative coordinators.
* `Farsi.Coordination.ya`, `Farsi.Coordination.na`: the disjunctive and the negative coordinator.
* `Farsi.Coordination.yaYa`, `Farsi.Coordination.hamHam`: the emphatic constructions.

## TODO

*Næ tænha … bælke … (h)æm* 'not only … but … also' is not recorded: its *(h)æm* attaches to the
predicate of the second clause rather than marking a coordinand.

## References

* [mahootian-1997]
* [stassen-2000]
-/

@[expose] public section

namespace Farsi.Coordination

/-- *væ* 'and', [mahootian-1997] p. 72; the medial connective *va* of [stassen-2000]'s (20b),
*dâneşjuyân va kârgarân* 'students and workers'. -/
def va : Coordinator :=
  { morph := .free "væ", gloss := "and", role := .conjunctive }

/-- *-o* 'and', a clitic on the coordinand before the next, *mina-o behruz* 'Mina and Behruz',
[mahootian-1997] p. 78, more common than *væ* in informal speech, p. 72. Either may stand
between any two coordinands and one must stand before the last, p. 78, *mina-o siamæk-o
dana-o jæhan*, (314). It is postposed to the first noun phrase in [stassen-2000]'s (49),
*mardhâ-o zanhâ-o bacehâ* 'men, women, and children'. -/
def o : Coordinator :=
  { morph := .encl "o", gloss := "and", role := .conjunctive }

/-- *væli* 'but', with *æmma* the most common adversative coordinator, [mahootian-1997] p. 75. -/
def vali : Coordinator :=
  { morph := .free "væli", gloss := "but", role := .adversative }

/-- *æmma* 'but', [mahootian-1997] p. 75. -/
def amma : Coordinator :=
  { morph := .free "æmma", gloss := "but", role := .adversative }

/-- *bælke* 'but', formal or literary, [mahootian-1997] p. 75. -/
def balke : Coordinator :=
  { morph := .free "bælke", gloss := "but", role := .adversative }

/-- *liken* 'but, however', formal or literary, [mahootian-1997] p. 75. -/
def liken : Coordinator :=
  { morph := .free "liken", gloss := "but, however", role := .adversative }

/-- *ya* 'or', one before each further disjunct, [mahootian-1997] pp. 75–76. -/
def ya : Coordinator :=
  { morph := .free "ya", gloss := "or", role := .disjunctive }

/-- *næ* 'no', before each coordinand 'neither … nor', *næ bolænd næ kutah-e* 'He's neither tall
nor short', [mahootian-1997] pp. 76–77 and (325). -/
def na : Coordinator :=
  { morph := .free "næ", gloss := "neither, nor", role := .negative }

/-- *ya … ya* 'either … or', [mahootian-1997] p. 75; the second *ya* may be *ya inke*. -/
def yaYa : Coordinator.Correlative := ⟨[ya.morph], [ya.morph], ya⟩

/-- *hæm … hæm* 'both … and', glossed 'also … also', *hæm mæn hæm iræj* 'both Iraj and I',
[mahootian-1997] p. 78. -/
def hamHam : Coordinator.Correlative := ⟨[.free "hæm"], [.free "hæm"], va⟩

end Farsi.Coordination
