module

public import Linglib.Data.Statistics.Schema

/-!
# Bybee1985: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/Bybee1985.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The verbal categories of Bybee's fifty-language sample: the share of languages expressing each
category on the verb, and for aspect, tense, mood and person the languages in which one marker
stands closer to the stem than another. Also the token frequencies of the modern descendants of Old
English Strong Verbs.

## References

* [bybee-1985]
-/

@[expose] public section

namespace Bybee1985

open Data.Statistics

/-- The verbal categories coded in the survey, as the rows of Figures 1 and 2. -/
inductive Category where
  /-- valence: Differences in the number or role of the arguments the verb stem takes. -/
  | valence
  /-- voice: The perspective from which the situation described by the verb stem is viewed. -/
  | voice
  /-- aspect: The way the internal temporal constituency of the situation is viewed. -/
  | aspect
  /-- tense: The placement of the situation in time, relative to the moment of speech or another
  established point. -/
  | tense
  /-- mood: The way the speaker presents the truth of the proposition, evidentials included. -/
  | mood
  /-- number: Concord by number with one or more arguments of the verb. -/
  | number
  /-- person: Concord by person with the subject. -/
  | person
  /-- person (object): Concord by person with the object. -/
  | objectPerson
  /-- gender: Concord with arguments by lexical class. -/
  | gender
  deriving DecidableEq, Repr, Fintype

/-- The Old English Strong Verb classes of the table. -/
inductive StrongClass where
  /-- I: Class I -/
  | one
  /-- II: Class II -/
  | two
  /-- VII: Class VII -/
  | seven
  deriving DecidableEq, Repr, Fintype

/-- The modern descendants of the Class I, II and VII Strong Verbs. -/
inductive Verb where
  /-- drive: *drive*, Class I -/
  | drive
  /-- rise: *rise*, Class I -/
  | rise
  /-- ride: *ride*, Class I -/
  | ride
  /-- write: *write*, Class I -/
  | write
  /-- bite: *bite*, Class I -/
  | bite
  /-- bide: *bide*, Class I -/
  | bide
  /-- reap: *reap*, Class I -/
  | reap
  /-- slit: *slit*, Class I -/
  | slit
  /-- sneak: *sneak*, Class I -/
  | sneak
  /-- choose: *choose*, Class II -/
  | choose
  /-- fly: *fly*, Class II -/
  | fly
  /-- shoot: *shoot*, Class II -/
  | shoot
  /-- lose: *lose*, Class II -/
  | lose
  /-- flee: *flee*, Class II -/
  | flee
  /-- rue: *rue*, Class II -/
  | rue
  /-- seethe: *seethe*, Class II -/
  | seethe
  /-- smoke: *smoke*, Class II -/
  | smoke
  /-- float: *float*, Class II -/
  | float
  /-- shove: *shove*, Class II -/
  | shove
  /-- fall: *fall*, Class VII -/
  | fall
  /-- hold: *hold*, Class VII -/
  | hold
  /-- know: *know*, Class VII -/
  | know
  /-- grow: *grow*, Class VII -/
  | grow
  /-- blow: *blow*, Class VII -/
  | blow
  /-- wax: *wax*, Class VII -/
  | wax
  /-- weep: *weep*, Class VII -/
  | weep
  /-- beat: *beat*, Class VII -/
  | beat
  /-- hew: *hew*, Class VII -/
  | hew
  /-- leap: *leap*, Class VII -/
  | leap
  /-- mow: *mow*, Class VII -/
  | mow
  /-- sow: *sow*, Class VII -/
  | sow
  /-- flow: *flow*, Class VII -/
  | flow
  /-- row: *row*, Class VII -/
  | row
  deriving DecidableEq, Repr, Fintype

/-- The languages of the sample. (p. 24; checked against the page images.) -/
def sampleSize : ℕ := 50

/-- A row of Figures 1 and 2, pp. 30-31: the percentage of the sample's languages expressing a
category on the verb. -/
structure ExpressionShare where
  /-- The percentage with inflectional expression, obligatory and bound (Figure 1). -/
  inflectional : ℕ
  /-- The percentage with inflectional or derivational expression (Figure 2). -/
  morphological : ℕ
  deriving DecidableEq, Repr

/-- The cells of Figures 1 and 2, pp. 30-31, by category; from a sample of languages coded from
their descriptions; checked against the page images. -/
def expression : Category → ExpressionShare
  | .valence => ⟨6, 90⟩
  | .voice => ⟨26, 56⟩
  | .aspect => ⟨52, 74⟩
  | .tense => ⟨48, 50⟩
  | .mood => ⟨68, 68⟩
  | .number => ⟨54, 66⟩
  | .person => ⟨56, 56⟩
  | .objectPerson => ⟨28, 28⟩
  | .gender => ⟨16, 16⟩

/-- A row of §6, pp. 34-35: the languages in which one category's marker stands closer to the
stem than another's. -/
structure OrderCount where
  /-- The category named first. -/
  first : Category
  /-- The category named second. -/
  second : Category
  /-- The languages with the first category's marker closer to the stem. -/
  firstCloser : ℕ
  /-- The languages with the second category's marker closer to the stem. -/
  secondCloser : ℕ
  /-- The languages having both categories, whether or not their order can be told. -/
  both : ℕ
  deriving DecidableEq, Repr

/-- The 6 rows of §6, pp. 34-35, in the paper's order; from a sample of languages coded from
their descriptions; checked against the page images. -/
def order : List OrderCount :=
  [⟨.aspect, .tense, 8, 0, 18⟩,
   ⟨.aspect, .mood, 10, 0, 23⟩,
   ⟨.aspect, .person, 12, 1, 21⟩,  -- the opposite order is Navaho's
   ⟨.tense, .mood, 8, 1, 20⟩,  -- the opposite order is Ojibwa's
   ⟨.tense, .person, 8, 1, 17⟩,  -- the opposite order is Navaho's
   ⟨.mood, .person, 13, 5, 26⟩]

/-- A row of the table of p. 120: the token frequency of a verb descended from an Old English
Strong Verb. -/
structure VerbFrequency where
  /-- Its Old English class. -/
  strongClass : StrongClass
  /-- Whether it has regularized or become Weak. -/
  regularized : Bool
  /-- The token frequency of all its forms. -/
  allForms : ℕ
  /-- The token frequency of its Past Tense form. -/
  past : ℕ
  deriving DecidableEq, Repr

/-- The cells of the table of p. 120, by verb; counted in a corpus; checked against the page
images. -/
def strongVerbs : Verb → VerbFrequency
  | .drive => ⟨.one, false, 203, 58⟩
  | .rise => ⟨.one, false, 199, 60⟩
  | .ride => ⟨.one, false, 126, 40⟩
  | .write => ⟨.one, false, 561, 179⟩
  | .bite => ⟨.one, false, 26, 7⟩
  | .bide => ⟨.one, true, 1, 0⟩
  | .reap => ⟨.one, true, 5, 1⟩
  | .slit => ⟨.one, true, 3, 1⟩  -- past *slit*, with the zero allomorph
  | .sneak => ⟨.one, true, 11, 4⟩
  | .choose => ⟨.two, false, 177, 37⟩
  | .fly => ⟨.two, false, 92, 27⟩
  | .shoot => ⟨.two, false, 117, 18⟩
  | .lose => ⟨.two, false, 274, 49⟩
  | .flee => ⟨.two, false, 40, 22⟩
  | .rue => ⟨.two, true, 0, 0⟩
  | .seethe => ⟨.two, true, 0, 0⟩
  | .smoke => ⟨.two, true, 26, 6⟩
  | .float => ⟨.two, true, 23, 6⟩
  | .shove => ⟨.two, true, 16, 8⟩
  | .fall => ⟨.seven, false, 239, 87⟩
  | .hold => ⟨.seven, false, 509, 125⟩
  | .know => ⟨.seven, false, 1473, 394⟩
  | .grow => ⟨.seven, false, 300, 65⟩
  | .blow => ⟨.seven, false, 52, 12⟩
  | .wax => ⟨.seven, true, 6, 3⟩
  | .weep =>  -- past *wept*, a vowel change acquired later by regular sound change
    ⟨.seven,
     true,
     28,
     7⟩
  | .beat => ⟨.seven, true, 66, 12⟩  -- past *beat*, with the zero allomorph
  | .hew => ⟨.seven, true, 1, 1⟩
  | .leap => ⟨.seven, true, 33, 18⟩
  | .mow => ⟨.seven, true, 1, 1⟩
  | .sow => ⟨.seven, true, 6, 0⟩
  | .flow => ⟨.seven, true, 40, 4⟩
  | .row => ⟨.seven, true, 5, 2⟩

end Bybee1985
