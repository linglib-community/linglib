module

public import Linglib.Data.Statistics.Schema

/-!
# DegenTonhauser2021: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/DegenTonhauser2021.json` by
`scripts/gen_statistics.py`. Do not edit by hand: edit the JSON and re-run the generator.

Two experiments testing whether listeners' prior beliefs in the content of a clausal complement
modulate its projection, over twenty clause-embedding predicates and twenty contents, each content
paired with a fact expected to raise or lower its prior probability. Experiment 1 measured the prior
probability of the contents and the certainty that the speaker of a polar question is committed to
them within participants; Experiments 2a and 2b measured the two on separate groups. The by-content
prior means and by-predicate certainty means are plotted, not tabulated.

## Raw data

* <https://github.com/judith-tonhauser/projective-probability>: materials, trial-level data and
  analysis code of both experiments (footnote 3); the means are recomputed from results/9-prior-
  projection/data/cd.csv (Exp. 1), results/1-prior/data/cd.csv (Exp. 2a) and
  results/3-projectivity/data/cd.csv (Exp. 2b), which already apply the paper's participant
  exclusions

## References

* [degen-tonhauser-2021]
-/

@[expose] public section

namespace DegenTonhauser2021

open Data.Statistics

/-- The twenty clause-embedding predicates of Figure 1c. -/
inductive Predicate where
  /-- acknowledge: a verb -/
  | acknowledge
  /-- admit: a verb -/
  | admit
  /-- announce: a verb -/
  | announce
  /-- be annoyed: an adjective with the copula -/
  | beAnnoyed
  /-- be right: an adjective with the copula -/
  | beRight
  /-- confess: a verb -/
  | confess
  /-- confirm: a verb -/
  | confirm
  /-- demonstrate: a verb -/
  | demonstrate
  /-- discover: a verb -/
  | discover
  /-- establish: a verb -/
  | establish
  /-- hear: a verb -/
  | hear
  /-- inform: a verb, its indirect object Sam in every stimulus -/
  | inform
  /-- know: a verb -/
  | know
  /-- pretend: a verb -/
  | pretend
  /-- prove: a verb -/
  | prove
  /-- reveal: a verb -/
  | reveal
  /-- say: a verb -/
  | say
  /-- see: a verb -/
  | see
  /-- suggest: a verb -/
  | suggest
  /-- think: a verb -/
  | think
  deriving DecidableEq, Repr, Fintype

/-- The twenty complement contents, each paired between participants with a fact under which it
was expected to have a lower or a higher prior probability (Supplement A). -/
inductive Content where
  /-- Mary is pregnant: lower fact: Mary is a middle school student; higher fact: Mary is taking
  a prenatal yoga class -/
  | mary
  /-- Josie went on vacation to France: lower fact: Josie doesn't have a passport; higher fact:
  Josie loves France -/
  | josie
  /-- Emma studied on Saturday morning: lower fact: Emma is in first grade; higher fact: Emma is
  in law school -/
  | emma
  /-- Olivia sleeps until noon: lower fact: Olivia has two small children; higher fact: Olivia
  works the third shift -/
  | olivia
  /-- Sophia got a tattoo: lower fact: Sophia is a high end fashion model; higher fact: Sophia is
  a hipster -/
  | sophia
  /-- Mia drank 2 cocktails last night: lower fact: Mia is a nun; higher fact: Mia is a college
  student -/
  | mia
  /-- Isabella ate a steak on Sunday: lower fact: Isabella is a vegetarian; higher fact: Isabella
  is from Argentina -/
  | isabella
  /-- Emily bought a car yesterday: lower fact: Emily never has any money; higher fact: Emily has
  been saving for a year -/
  | emily
  /-- Grace visited her sister: lower fact: Grace hates her sister; higher fact: Grace loves her
  sister -/
  | grace
  /-- Zoe calculated the tip: lower fact: Zoe is 5 years old; higher fact: Zoe is a math major -/
  | zoe
  /-- Danny ate the last cupcake: lower fact: Danny is a diabetic; higher fact: Danny loves cake -/
  | danny
  /-- Frank got a cat: lower fact: Frank is allergic to cats; higher fact: Frank has always
  wanted a pet -/
  | frank
  /-- Jackson ran 10 miles: lower fact: Jackson is obese; higher fact: Jackson is training for a
  marathon -/
  | jackson
  /-- Jayden rented a car: lower fact: Jayden doesn't have a driver's license; higher fact:
  Jayden's car is in the shop -/
  | jayden
  /-- Tony had a drink last night: lower fact: Tony has been sober for 20 years; higher fact:
  Tony really likes to party with his friends -/
  | tony
  /-- Josh learned to ride a bike yesterday: lower fact: Josh is a 75-year old man; higher fact:
  Josh is a 5-year old boy -/
  | josh
  /-- Owen shoveled snow last winter: lower fact: Owen lives in New Orleans; higher fact: Owen
  lives in Chicago -/
  | owen
  /-- Julian dances salsa: lower fact: Julian is German; higher fact: Julian is Cuban -/
  | julian
  /-- Jon walks to work: lower fact: Jon lives 10 miles away from work; higher fact: Jon lives 2
  blocks away from work -/
  | jon
  /-- Charley speaks Spanish: lower fact: Charley lives in Korea; higher fact: Charley lives in
  Mexico -/
  | charley
  deriving DecidableEq, Repr, Fintype

/-- Whether the prior probability and certainty ratings came from the same participants. -/
inductive Design where
  /-- within participant: Experiment 1: each participant rated the priors and, in a separate
  block, the certainties -/
  | withinParticipant
  /-- between participants: Experiments 2a (priors) and 2b (certainties), on separate groups -/
  | betweenParticipants
  deriving DecidableEq, Repr, Fintype

/-- The fact condition of a content. -/
inductive Fact where
  /-- lower probability: the fact under which the content was expected to be less likely -/
  | lowerProbability
  /-- higher probability: the fact under which the content was expected to be more likely -/
  | higherProbability
  deriving DecidableEq, Repr, Fintype

/-- A row of Figure 2 (Exp. 1); Figure A2, Supplement D (Exp. 2a): the mean prior probability
rating of a content, given the fact. -/
structure PriorRow where
  /-- The mean rating. -/
  mean : Decimal
  deriving DecidableEq, Repr

/-- The cells of Figure 2 (Exp. 1); Figure A2, Supplement D (Exp. 2a), by design and fact and
content; from an experiment; recomputed from the authors' released data by
`scripts/check_statistics.py`. -/
def prior : Design → Fact → Content → PriorRow
  | .withinParticipant, .lowerProbability, .mary => ⟨⟨23, 2⟩⟩
  | .withinParticipant, .lowerProbability, .josie => ⟨⟨12, 2⟩⟩
  | .withinParticipant, .lowerProbability, .emma => ⟨⟨32, 2⟩⟩
  | .withinParticipant, .lowerProbability, .olivia => ⟨⟨21, 2⟩⟩
  | .withinParticipant, .lowerProbability, .sophia => ⟨⟨42, 2⟩⟩
  | .withinParticipant, .lowerProbability, .mia => ⟨⟨22, 2⟩⟩
  | .withinParticipant, .lowerProbability, .isabella => ⟨⟨13, 2⟩⟩
  | .withinParticipant, .lowerProbability, .emily => ⟨⟨15, 2⟩⟩
  | .withinParticipant, .lowerProbability, .grace => ⟨⟨25, 2⟩⟩
  | .withinParticipant, .lowerProbability, .zoe => ⟨⟨19, 2⟩⟩
  | .withinParticipant, .lowerProbability, .danny => ⟨⟨28, 2⟩⟩
  | .withinParticipant, .lowerProbability, .frank => ⟨⟨17, 2⟩⟩
  | .withinParticipant, .lowerProbability, .jackson => ⟨⟨19, 2⟩⟩
  | .withinParticipant, .lowerProbability, .jayden => ⟨⟨18, 2⟩⟩
  | .withinParticipant, .lowerProbability, .tony => ⟨⟨22, 2⟩⟩
  | .withinParticipant, .lowerProbability, .josh => ⟨⟨24, 2⟩⟩
  | .withinParticipant, .lowerProbability, .owen => ⟨⟨28, 2⟩⟩
  | .withinParticipant, .lowerProbability, .julian => ⟨⟨40, 2⟩⟩
  | .withinParticipant, .lowerProbability, .jon => ⟨⟨24, 2⟩⟩
  | .withinParticipant, .lowerProbability, .charley => ⟨⟨28, 2⟩⟩
  | .withinParticipant, .higherProbability, .mary => ⟨⟨82, 2⟩⟩
  | .withinParticipant, .higherProbability, .josie => ⟨⟨73, 2⟩⟩
  | .withinParticipant, .higherProbability, .emma => ⟨⟨68, 2⟩⟩
  | .withinParticipant, .higherProbability, .olivia => ⟨⟨66, 2⟩⟩
  | .withinParticipant, .higherProbability, .sophia => ⟨⟨63, 2⟩⟩
  | .withinParticipant, .higherProbability, .mia => ⟨⟨58, 2⟩⟩
  | .withinParticipant, .higherProbability, .isabella => ⟨⟨52, 2⟩⟩
  | .withinParticipant, .higherProbability, .emily => ⟨⟨56, 2⟩⟩
  | .withinParticipant, .higherProbability, .grace => ⟨⟨79, 2⟩⟩
  | .withinParticipant, .higherProbability, .zoe => ⟨⟨75, 2⟩⟩
  | .withinParticipant, .higherProbability, .danny => ⟨⟨70, 2⟩⟩
  | .withinParticipant, .higherProbability, .frank => ⟨⟨68, 2⟩⟩
  | .withinParticipant, .higherProbability, .jackson => ⟨⟨77, 2⟩⟩
  | .withinParticipant, .higherProbability, .jayden => ⟨⟨69, 2⟩⟩
  | .withinParticipant, .higherProbability, .tony => ⟨⟨75, 2⟩⟩
  | .withinParticipant, .higherProbability, .josh => ⟨⟨54, 2⟩⟩
  | .withinParticipant, .higherProbability, .owen => ⟨⟨75, 2⟩⟩
  | .withinParticipant, .higherProbability, .julian => ⟨⟨60, 2⟩⟩
  | .withinParticipant, .higherProbability, .jon => ⟨⟨76, 2⟩⟩
  | .withinParticipant, .higherProbability, .charley => ⟨⟨80, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .mary => ⟨⟨11, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .josie => ⟨⟨8, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .emma => ⟨⟨26, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .olivia => ⟨⟨8, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .sophia => ⟨⟨28, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .mia => ⟨⟨13, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .isabella => ⟨⟨6, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .emily => ⟨⟨13, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .grace => ⟨⟨23, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .zoe => ⟨⟨8, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .danny => ⟨⟨25, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .frank => ⟨⟨10, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .jackson => ⟨⟨11, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .jayden => ⟨⟨10, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .tony => ⟨⟨11, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .josh => ⟨⟨21, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .owen => ⟨⟨16, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .julian => ⟨⟨33, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .jon => ⟨⟨12, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .charley => ⟨⟨28, 2⟩⟩
  | .betweenParticipants, .higherProbability, .mary => ⟨⟨88, 2⟩⟩
  | .betweenParticipants, .higherProbability, .josie => ⟨⟨70, 2⟩⟩
  | .betweenParticipants, .higherProbability, .emma => ⟨⟨76, 2⟩⟩
  | .betweenParticipants, .higherProbability, .olivia => ⟨⟨73, 2⟩⟩
  | .betweenParticipants, .higherProbability, .sophia => ⟨⟨60, 2⟩⟩
  | .betweenParticipants, .higherProbability, .mia => ⟨⟨53, 2⟩⟩
  | .betweenParticipants, .higherProbability, .isabella => ⟨⟨51, 2⟩⟩
  | .betweenParticipants, .higherProbability, .emily => ⟨⟨48, 2⟩⟩
  | .betweenParticipants, .higherProbability, .grace => ⟨⟨84, 2⟩⟩
  | .betweenParticipants, .higherProbability, .zoe => ⟨⟨77, 2⟩⟩
  | .betweenParticipants, .higherProbability, .danny => ⟨⟨69, 2⟩⟩
  | .betweenParticipants, .higherProbability, .frank => ⟨⟨62, 2⟩⟩
  | .betweenParticipants, .higherProbability, .jackson => ⟨⟨84, 2⟩⟩
  | .betweenParticipants, .higherProbability, .jayden => ⟨⟨67, 2⟩⟩
  | .betweenParticipants, .higherProbability, .tony => ⟨⟨72, 2⟩⟩
  | .betweenParticipants, .higherProbability, .josh => ⟨⟨51, 2⟩⟩
  | .betweenParticipants, .higherProbability, .owen => ⟨⟨82, 2⟩⟩
  | .betweenParticipants, .higherProbability, .julian => ⟨⟨59, 2⟩⟩
  | .betweenParticipants, .higherProbability, .jon => ⟨⟨80, 2⟩⟩
  | .betweenParticipants, .higherProbability, .charley => ⟨⟨87, 2⟩⟩

/-- A row of Figure 3 (Exp. 1); Figure 6 (Exp. 2b): the mean certainty rating of a predicate's
complement, the speaker taken to be certain of it, by the fact condition of the content. -/
structure CertaintyRow where
  /-- The mean rating. -/
  mean : Decimal
  deriving DecidableEq, Repr

/-- The cells of Figure 3 (Exp. 1); Figure 6 (Exp. 2b), by design and fact and predicate; from an
experiment; recomputed from the authors' released data by `scripts/check_statistics.py`. -/
def certainty : Design → Fact → Predicate → CertaintyRow
  | .withinParticipant, .lowerProbability, .acknowledge => ⟨⟨49, 2⟩⟩
  | .withinParticipant, .lowerProbability, .admit => ⟨⟨43, 2⟩⟩
  | .withinParticipant, .lowerProbability, .announce => ⟨⟨41, 2⟩⟩
  | .withinParticipant, .lowerProbability, .beAnnoyed => ⟨⟨68, 2⟩⟩
  | .withinParticipant, .lowerProbability, .beRight => ⟨⟨20, 2⟩⟩
  | .withinParticipant, .lowerProbability, .confess => ⟨⟨45, 2⟩⟩
  | .withinParticipant, .lowerProbability, .confirm => ⟨⟨28, 2⟩⟩
  | .withinParticipant, .lowerProbability, .demonstrate => ⟨⟨33, 2⟩⟩
  | .withinParticipant, .lowerProbability, .discover => ⟨⟨55, 2⟩⟩
  | .withinParticipant, .lowerProbability, .establish => ⟨⟨27, 2⟩⟩
  | .withinParticipant, .lowerProbability, .hear => ⟨⟨57, 2⟩⟩
  | .withinParticipant, .lowerProbability, .inform => ⟨⟨57, 2⟩⟩
  | .withinParticipant, .lowerProbability, .know => ⟨⟨68, 2⟩⟩
  | .withinParticipant, .lowerProbability, .pretend => ⟨⟨21, 2⟩⟩
  | .withinParticipant, .lowerProbability, .prove => ⟨⟨25, 2⟩⟩
  | .withinParticipant, .lowerProbability, .reveal => ⟨⟨47, 2⟩⟩
  | .withinParticipant, .lowerProbability, .say => ⟨⟨22, 2⟩⟩
  | .withinParticipant, .lowerProbability, .see => ⟨⟨60, 2⟩⟩
  | .withinParticipant, .lowerProbability, .suggest => ⟨⟨24, 2⟩⟩
  | .withinParticipant, .lowerProbability, .think => ⟨⟨20, 2⟩⟩
  | .withinParticipant, .higherProbability, .acknowledge => ⟨⟨65, 2⟩⟩
  | .withinParticipant, .higherProbability, .admit => ⟨⟨60, 2⟩⟩
  | .withinParticipant, .higherProbability, .announce => ⟨⟨53, 2⟩⟩
  | .withinParticipant, .higherProbability, .beAnnoyed => ⟨⟨80, 2⟩⟩
  | .withinParticipant, .higherProbability, .beRight => ⟨⟨34, 2⟩⟩
  | .withinParticipant, .higherProbability, .confess => ⟨⟨58, 2⟩⟩
  | .withinParticipant, .higherProbability, .confirm => ⟨⟨37, 2⟩⟩
  | .withinParticipant, .higherProbability, .demonstrate => ⟨⟨48, 2⟩⟩
  | .withinParticipant, .higherProbability, .discover => ⟨⟨69, 2⟩⟩
  | .withinParticipant, .higherProbability, .establish => ⟨⟨43, 2⟩⟩
  | .withinParticipant, .higherProbability, .hear => ⟨⟨72, 2⟩⟩
  | .withinParticipant, .higherProbability, .inform => ⟨⟨76, 2⟩⟩
  | .withinParticipant, .higherProbability, .know => ⟨⟨74, 2⟩⟩
  | .withinParticipant, .higherProbability, .pretend => ⟨⟨31, 2⟩⟩
  | .withinParticipant, .higherProbability, .prove => ⟨⟨41, 2⟩⟩
  | .withinParticipant, .higherProbability, .reveal => ⟨⟨62, 2⟩⟩
  | .withinParticipant, .higherProbability, .say => ⟨⟨38, 2⟩⟩
  | .withinParticipant, .higherProbability, .see => ⟨⟨69, 2⟩⟩
  | .withinParticipant, .higherProbability, .suggest => ⟨⟨32, 2⟩⟩
  | .withinParticipant, .higherProbability, .think => ⟨⟨40, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .acknowledge => ⟨⟨41, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .admit => ⟨⟨37, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .announce => ⟨⟨31, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .beAnnoyed => ⟨⟨54, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .beRight => ⟨⟨14, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .confess => ⟨⟨33, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .confirm => ⟨⟨22, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .demonstrate => ⟨⟨28, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .discover => ⟨⟨44, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .establish => ⟨⟨18, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .hear => ⟨⟨43, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .inform => ⟨⟨48, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .know => ⟨⟨57, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .pretend => ⟨⟨11, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .prove => ⟨⟨18, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .reveal => ⟨⟨37, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .say => ⟨⟨17, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .see => ⟨⟨43, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .suggest => ⟨⟨18, 2⟩⟩
  | .betweenParticipants, .lowerProbability, .think => ⟨⟨15, 2⟩⟩
  | .betweenParticipants, .higherProbability, .acknowledge => ⟨⟨56, 2⟩⟩
  | .betweenParticipants, .higherProbability, .admit => ⟨⟨56, 2⟩⟩
  | .betweenParticipants, .higherProbability, .announce => ⟨⟨52, 2⟩⟩
  | .betweenParticipants, .higherProbability, .beAnnoyed => ⟨⟨72, 2⟩⟩
  | .betweenParticipants, .higherProbability, .beRight => ⟨⟨33, 2⟩⟩
  | .betweenParticipants, .higherProbability, .confess => ⟨⟨53, 2⟩⟩
  | .betweenParticipants, .higherProbability, .confirm => ⟨⟨37, 2⟩⟩
  | .betweenParticipants, .higherProbability, .demonstrate => ⟨⟨44, 2⟩⟩
  | .betweenParticipants, .higherProbability, .discover => ⟨⟨60, 2⟩⟩
  | .betweenParticipants, .higherProbability, .establish => ⟨⟨38, 2⟩⟩
  | .betweenParticipants, .higherProbability, .hear => ⟨⟨61, 2⟩⟩
  | .betweenParticipants, .higherProbability, .inform => ⟨⟨67, 2⟩⟩
  | .betweenParticipants, .higherProbability, .know => ⟨⟨66, 2⟩⟩
  | .betweenParticipants, .higherProbability, .pretend => ⟨⟨32, 2⟩⟩
  | .betweenParticipants, .higherProbability, .prove => ⟨⟨34, 2⟩⟩
  | .betweenParticipants, .higherProbability, .reveal => ⟨⟨54, 2⟩⟩
  | .betweenParticipants, .higherProbability, .say => ⟨⟨34, 2⟩⟩
  | .betweenParticipants, .higherProbability, .see => ⟨⟨71, 2⟩⟩
  | .betweenParticipants, .higherProbability, .suggest => ⟨⟨32, 2⟩⟩
  | .betweenParticipants, .higherProbability, .think => ⟨⟨38, 2⟩⟩

/-- A row of Figures 3 and 6: the mean certainty rating of the main-clause controls, whose
content was expected not to project. -/
structure ControlRow where
  /-- The mean rating. -/
  mean : Decimal
  deriving DecidableEq, Repr

/-- The cells of Figures 3 and 6, by design; from an experiment; recomputed from the authors'
released data by `scripts/check_statistics.py`. -/
def controls : Design → ControlRow
  | .withinParticipant => ⟨⟨21, 2⟩⟩
  | .betweenParticipants => ⟨⟨19, 2⟩⟩

end DegenTonhauser2021
