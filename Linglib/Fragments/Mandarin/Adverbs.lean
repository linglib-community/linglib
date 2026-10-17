module

public import Linglib.Semantics.Presupposition.Trigger

/-!
# Mandarin adverbs

The Mandarin adverbs that trigger presuppositions. *Yě*, *yòu*, *zài* and *jiù* are among the
nonmovable adverbs of Li and Thompson's grammar, which occur only after the subject or topic and
before the verb. *Yě* 也 'also' applies to the subject: *tā yě mǎi-le yi-ge huāpíng* 's/he, in
addition to some other people, also bought a vase'. The two adverbs meaning 'again' divide the
time line between them: *yòu* 又 applies to past and present events, as in *tā zuótiān yòu chī
le* 's/he ate again yesterday', and *zài* 再 to events that have not yet happened, as in *tā
míngtiān zài chī* 's/he'll eat again tomorrow' and in commands, and neither occurs in the
other's domain. *Jiù* 就 has several uses, among them 'immediately', 'then' and an emphatic one;
the entry here is its use as 'only', in which it associates with a focus to its right. *Réng* 仍
'still' presents a state as continuing from the past, and *búzài* 不再 'no longer', built from
the negator *bù* and *zài*, is its counterpart for a state that has ended; neither combines with
a telic predicate. *Fǎn'ér* 反而 'instead' asserts its clause against a salient alternative that
is false, where *yě* requires one that is true. The description follows Li and Thompson for
*yě*, *yòu*, *zài* and *jiù*, and Wang for the focus association of *jiù* and for *réng*,
*búzài* and *fǎn'ér*. The presuppositional verbs *zhīdào* 'know', *hòuhuǐ* 'regret' and *kāishǐ*
'start' are entries of `Fragments/Mandarin/Verbs.lean`.

## References

* [li-thompson-1981]
* [wang-2025]
-/

@[expose] public section

namespace Mandarin.Adverbs

open Presupposition

/-- *yě* 也 'also', the additive adverb. -/
def ye : TriggerItem := { form := "yě", script := "也", triggerClass := .additive }

/-- *yòu* 又 'again', of past and present events. -/
def you : TriggerItem := { form := "yòu", script := "又", triggerClass := .iterative }

/-- *zài* 再 'again', of events that have not yet happened. -/
def zai : TriggerItem := { form := "zài", script := "再", triggerClass := .iterative }

/-- *réng* 仍 'still', of a state continuing from the past. -/
def reng : TriggerItem := { form := "réng", script := "仍", triggerClass := .continuative }

/-- *búzài* 不再 'no longer', of a state that held until the reference time. -/
def buzai : TriggerItem := { form := "búzài", script := "不再", triggerClass := .changeOfState }

/-- *jiù* 就 in its use as 'only', associating with a focus to its right. -/
def jiu : TriggerItem := { form := "jiù", script := "就", triggerClass := .exclusive }

/-- *fǎn'ér* 反而 'instead, on the contrary'. -/
def faner : TriggerItem := { form := "fǎn'ér", script := "反而", triggerClass := .contrastive }

/-- The presupposition-triggering adverbs. -/
def all : List TriggerItem := [ye, you, zai, reng, buzai, jiu, faner]

end Mandarin.Adverbs
