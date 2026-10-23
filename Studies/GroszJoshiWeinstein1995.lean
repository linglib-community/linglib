module

public import Linglib.Discourse.Centering.Transition
public import Linglib.Discourse.Centering.GrammaticalRole
public import Linglib.Core.Data.List.Forall2
public import Linglib.Data.Examples.GroszJoshiWeinstein1995
public import Studies.Sidner1979
import all Mathlib.Data.List.Sort  -- for unfolding `List.insertionSort`

/-!
# Grosz, Joshi, and Weinstein (1995): Centering

This file formalizes the applications of centering in [grosz-joshi-weinstein-1995], "Centering:
a framework for modeling the local coherence of discourse", over the library's centering
substrate: the forward-looking centers of an utterance ranked by grammatical role, its
backward-looking center, the transitions of section 3, and the two rules of section 6. The
paper's discourses are rows of `Data.Examples.GroszJoshiWeinstein1995`; the study analyzes them
at the paper's own annotations and proves its claims about them. Section 2's contrast between
(1) and (2) comes out as continuations against retentions and a Rule 1 violation
(`coherence_contrast`); section 5 argues a single backward-looking center ranked by
grammatical role from the hamster variants (7) to (10), which Rule 1 separates into the
acceptable and the degraded (`rule1_separates_variants`), and from the subject preference of
(11) and (12) and the toy contrast of (13) and (14); section 7 applies the rules to the
violation in (15) and its repair by the shift in (16), the full noun phrase center of (17),
and the transitions annotated on (20); and section 9 compares centering with [sidner-1979] on
Sidner's example (34), where the centering account makes Jeff the center that the pronoun of
(34c) continues (`d34_jeff_cb`). The section says that Sidner's actor focus, Carl after (34b),
makes Carl the leading candidate for that pronoun; Sidner's rule for a pronoun in agent
position gives precedence to a discourse focus established before the actor focus, and on it
the pronoun co-specifies Jeff, as in her own analysis of the discourse
(`d34_sidner_foci`, `d34_sidner_cospecify`).

## Implementation notes

Entities are an inductive for the paper's discourses and `Sidner1979.Entity` for Sidner's, whose
discourse D9 the paper's (34) abbreviates;
a realization is by name or by pronoun, and grammatical roles are subject, object, and other,
ranked in that order, with embedded subjects counting as other. Under the definitions the
backward-looking center of (2) stays John throughout, so the paper's informal flipping of
aboutness surfaces as two retentions, a violation of Rule 1 at (2b), and a pronoun for an
entity outside the forward-looking centers at (2d). Rule 2 is read pointwise over the transition
sequences by the order on `Transition`; its restriction to pairs of utterances is
[brennan-friedman-pollard-1987]'s, as the paper's footnote notes, and its qualification of the
(15) to (16) contrast by [gordon-grosz-gilliom-1993] is recorded on the rows.

## References

* [grosz-joshi-weinstein-1995]
* [sidner-1979]
* [brennan-friedman-pollard-1987]
* [gordon-grosz-gilliom-1993]

## TODO

The center of (19), realized but not directly realized, the value-free and value-loaded
interpretations of (25) to (31), and the referential uses of (32) and (33) in section 8 need a
realization relation richer than the substrate's list of directly realized entities.
-/

@[expose] public section

namespace GroszJoshiWeinstein1995

open Discourse.Centering

/-- The individuals of the paper's discourses. -/
inductive Entity
  | john | store | piano | susan | betsy | hamster | wine | susie | tommy | boat | bear | mike
  | speaker | dog | vet
  deriving DecidableEq

/-- An utterance with its realizations, ranked subject > object > other. -/
abbrev Utt := Utterance Entity GrammaticalRole

variable {E : Type*}

/-- A realization by a name or a description. -/
def name (e : E) (r : GrammaticalRole) : Realization E GrammaticalRole := ⟨e, r, false⟩

/-- A realization by a pronoun. -/
def pron (e : E) (r : GrammaticalRole) : Realization E GrammaticalRole := ⟨e, r, true⟩

/-! ### The coherence contrast, section 2 -/

namespace D1

/-- (1a) John went to his favorite music store to buy a piano. -/
def a : Utt := ⟨[name .john .subject, name .store .object, name .piano .other]⟩

/-- (1b) He had frequented the store for many years. -/
def b : Utt := ⟨[pron .john .subject, name .store .object]⟩

/-- (1c) He was excited that he could finally buy a piano. -/
def c : Utt := ⟨[pron .john .subject, name .piano .object]⟩

/-- (1d) He arrived just as the store was closing for the day. -/
def d : Utt := ⟨[pron .john .subject, name .store .other]⟩

def all : List Utt := [a, b, c, d]

end D1

namespace D2

/-- (2b) It was a store John had frequented for many years. -/
def b : Utt := ⟨[pron .store .subject, name .john .other]⟩

/-- (2d) It was closing just as John arrived. -/
def d : Utt := ⟨[pron .store .subject, name .john .other]⟩

def all : List Utt := [D1.a, b, D1.c, d]

end D2

/-- Discourse (1) centers on John by three continuations, Rule 1 holding at each step. -/
theorem d1_continues : transitions D1.all = [.continuation, .continuation, .continuation] ∧
    PronominalizationConstraint D1.a D1.b ∧ PronominalizationConstraint D1.b D1.c ∧
      PronominalizationConstraint D1.c D1.d := by
  decide

/-- Discourse (2) keeps John as backward-looking center; its pronoun in (2b) violates Rule 1, and
that in (2d) lies outside the forward-looking centers of (2c) (section 7). -/
theorem d2_retains : cbs D2.all = [some .john, some .john, some .john] ∧
    transitions D2.all = [.retaining, .continuation, .retaining] ∧
      ¬ PronominalizationConstraint D1.a D2.b ∧ ¬ ∃ e ∈ D1.c.cf, D2.d.Pronominalizes e := by
  decide

/-- Discourse (1) is a sequence of continuations, which Rule 2 prefers to the transitions of (2)
that it dominates one by one. -/
theorem coherence_contrast : (transitions D2.all).Forall₂ (· ≤ ·) (transitions D1.all) ∧
    transitions D2.all ≠ transitions D1.all := by
  decide

/-! ### Factors governing centering, section 5

The hamster variants (7) to (10) share (a) and (b) and differ in which of Susan and Betsy is
pronominalized and which is the subject of (c). -/

namespace D7

/-- (a) Susan gave Betsy a pet hamster. -/
def a : Utt := ⟨[name .susan .subject, name .betsy .object, name .hamster .other]⟩

/-- (b) She reminded her that such hamsters were quite shy. -/
def b : Utt := ⟨[pron .susan .subject, pron .betsy .object]⟩

/-- (7c) She asked Betsy whether she liked the gift. -/
def c7 : Utt := ⟨[pron .susan .subject, name .betsy .object]⟩

/-- (8c) Betsy told her that she really liked the gift. -/
def c8 : Utt := ⟨[name .betsy .subject, pron .susan .object]⟩

/-- (9c) Susan asked her whether she liked the gift. -/
def c9 : Utt := ⟨[name .susan .subject, pron .betsy .object]⟩

/-- (10c) She told Susan that she really liked the gift. -/
def c10 : Utt := ⟨[pron .betsy .subject, name .susan .object]⟩

end D7

theorem susan_cb : cb D7.b D7.c7 = some .susan ∧ cb D7.b D7.c8 = some .susan ∧
    cb D7.b D7.c9 = some .susan ∧ cb D7.b D7.c10 = some .susan := by
  decide

/-- (7c) continues Susan as center; (8c) merely retains her. -/
theorem c7_continues_c8_retains :
    transition (cb D7.a D7.b) D7.b D7.c7 = .continuation ∧
      transition (cb D7.a D7.b) D7.b D7.c8 = .retaining := by
  decide

/-- Rule 1 separates the variants as the paper's acceptability ordering does: (7) and (8)
pronominalize the center, (9) and (10) pronominalize Betsy while naming Susan. -/
theorem rule1_separates_variants :
    PronominalizationConstraint D7.b D7.c7 ∧ PronominalizationConstraint D7.b D7.c8 ∧
      ¬ PronominalizationConstraint D7.b D7.c9 ∧ ¬ PronominalizationConstraint D7.b D7.c10 := by
  decide

namespace D11

/-- (11c) She just gave Betsy a wonderful bottle of wine. -/
def c : Utt := ⟨[pron .susan .subject, name .betsy .object, name .wine .other]⟩

/-- (11d) She told her it was quite rare. -/
def d : Utt := ⟨[pron .susan .subject, pron .betsy .object, pron .wine .other]⟩

/-- (11e) She knows a lot about wine, read with Susan as the subject. -/
def e11 : Utt := ⟨[pron .susan .subject, name .wine .other]⟩

/-- (12e) Wine collecting gives her expertise that's fun to share, read with Susan as the
object. -/
def e12 : Utt := ⟨[pron .susan .object]⟩

end D11

/-- Subject position ranks Susan first among the forward-looking centers of (d), so the
preferred reading of the pronoun in (e), Susan in either grammatical position, keeps her as
the center: the preference is for the subject, not for parallelism. -/
theorem subject_preference : D11.d.cp = some .susan ∧ cb D11.c D11.d = some .susan ∧
    cb D11.d D11.e11 = some .susan ∧ cb D11.d D11.e12 = some .susan := by
  decide

namespace D13

/-- (13c) Susie prefers the green plastic tugboat to the teddy bear. -/
def c : Utt := ⟨[name .susie .subject, name .boat .object, name .bear .other]⟩

/-- (13d) and (14d), first clause: Tommy likes it better than the bear too. -/
def d : Utt := ⟨[name .tommy .subject, pron .boat .object, name .bear .other]⟩

end D13

/-- The boat is the backward-looking center of (d), continued in (13) and in conflict with
pragmatics in (14). -/
theorem boat_cb : cb D13.c D13.d = some .boat := by decide

/-! ### Applications of the rules, section 7 -/

namespace D15

/-- (15a) He has been acting quite odd, in a segment centered on John. -/
def a : Utt := ⟨[pron .john .subject]⟩

/-- (15b) He called up Mike yesterday. -/
def b : Utt := ⟨[pron .john .subject, name .mike .object]⟩

/-- (15c) John wanted to meet him urgently. -/
def c : Utt := ⟨[name .john .subject, pron .mike .object]⟩

end D15

/-- (15c) violates Rule 1: Mike is pronominalized while the center John is named, though
(15b) satisfied it. -/
theorem d15_violates_rule1 : cb D15.b D15.c = some .john ∧
    PronominalizationConstraint D15.a D15.b ∧ ¬ PronominalizationConstraint D15.b D15.c := by
  decide

namespace D16

/-- (16a) John has been acting quite odd. -/
def a : Utt := ⟨[name .john .subject]⟩

/-- (16c) Mike was studying for his driver's test. -/
def c : Utt := ⟨[name .mike .subject]⟩

/-- (16d) He was annoyed by John's call. -/
def d : Utt := ⟨[pron .mike .subject, name .john .other]⟩

def all : List Utt := [a, D15.b, c, d]

end D16

/-- The intervening (16c) shifts the center to Mike, so the pronoun in (16d) satisfies Rule 1, which
(15c) violated. -/
theorem d16_repairs : cbs D16.all = [some .john, some .mike, some .mike] ∧
    transitions D16.all = [.continuation, .shifting, .continuation] ∧
      PronominalizationConstraint D16.c D16.d := by
  decide

namespace D17

/-- (17b) I took him to the vet the other day. -/
def b : Utt := ⟨[pron .speaker .subject, pron .dog .object, name .vet .other]⟩

/-- (17c) The mangy old beast always hates these visits. -/
def c : Utt := ⟨[name .dog .subject]⟩

end D17

/-- Rule 1 does not preclude a description for the center, as in (17c), where no pronoun is used. -/
theorem full_noun_phrase_cb : cb D17.b D17.c = some .dog ∧
    PronominalizationConstraint D17.b D17.c := by
  decide

namespace D20

/-- (20a) John has been having a lot of trouble arranging his vacation. -/
def a : Utt := ⟨[name .john .subject]⟩

/-- (20b) He cannot find anyone to take over his responsibilities. -/
def b : Utt := ⟨[pron .john .subject]⟩

/-- (20c) He called up Mike yesterday to work out a plan. -/
def c : Utt := ⟨[pron .john .subject, name .mike .object]⟩

/-- (20d) Mike has annoyed him a lot recently. -/
def d : Utt := ⟨[name .mike .subject, pron .john .object]⟩

/-- (20e) He called John at 5 AM on Friday last week. -/
def e : Utt := ⟨[pron .mike .subject, name .john .object]⟩

def all : List Utt := [a, b, c, d, e]

end D20

/-- In (20), John continues in (c), is retained in (d), and the center shifts to Mike in (e), with
Rule 1 holding throughout. -/
theorem d20_transitions :
    transitions D20.all = [.continuation, .continuation, .retaining, .shifting] ∧
      PronominalizationConstraint D20.a D20.b ∧ PronominalizationConstraint D20.b D20.c ∧
        PronominalizationConstraint D20.c D20.d ∧ PronominalizationConstraint D20.d D20.e := by
  decide

/-! ### Comparison with Sidner, section 9

Sidner's example (34), *I haven't seen Jeff for several days. Carl thinks he's studying for his
exams, but I think he went to the Cape with Linda.* -/

namespace D34

/-- Sidner's utterances over her entities. -/
abbrev SUtt := Utterance Sidner1979.Entity GrammaticalRole

/-- (34a) I haven't seen Jeff for several days. -/
def a : SUtt := ⟨[pron .speaker .subject, name .jeff .object]⟩

/-- (34b) Carl thinks he's studying for his exams. -/
def b : SUtt := ⟨[name .carl .subject, pron .jeff .other]⟩

/-- (34c) but I think he went to the Cape with Linda, with the pronoun continuing Jeff. -/
def c : SUtt :=
  ⟨[pron .speaker .subject, pron .jeff .other, name .cape .other, name .linda .other]⟩

/-- The paper's variant of (34c), *He thinks he studies too much*, with two pronouns. -/
def c' : SUtt := ⟨[pron .carl .subject, pron .jeff .other]⟩

end D34

/-- On the centering account Jeff is the center at (34b), and the pronoun of (34c) that
continues him satisfies Rule 1: there is no problem. -/
theorem d34_jeff_cb : cb D34.a D34.b = some .jeff ∧ cb D34.b D34.c = some .jeff ∧
    PronominalizationConstraint D34.b D34.c := by
  decide

theorem d34_two_pronouns : cb D34.b D34.c' = some .carl ∧
    PronominalizationConstraint D34.b D34.c' := by
  decide

/-- After (34b), Sidner's discourse focus is Jeff and her actor focus is Carl, and (34a) and (34b)
open her D9. -/
theorem d34_sidner_foci : Sidner1979.D9.afterB.discourse = some ⟨.jeff, 1⟩ ∧
    Sidner1979.D9.afterB.actor = some ⟨.carl, 2⟩ := by
  decide

/-- On Sidner's agent-position rule, the pronoun of (34c) co-specifies Jeff, the discourse focus of
(34a) and the center on the centering account. -/
theorem d34_sidner_cospecify :
    Sidner1979.D9.afterB.cospecify .agent (· ∈ [.jeff, .carl]) = cb D34.a D34.b := by
  decide

end GroszJoshiWeinstein1995
