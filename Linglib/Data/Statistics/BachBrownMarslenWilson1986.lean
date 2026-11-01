module

public import Linglib.Data.Statistics.Schema

/-!
# BachBrownMarslenWilson1986: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/BachBrownMarslenWilson1986.json` by
`scripts/gen_statistics.py`. Do not edit by hand: edit the JSON and re-run the generator.

Comprehensibility ratings and comprehension scores for matched Dutch and German sentences whose
clause-final verb clusters hold one to four verbs, Dutch in the crossed order and German in the
nested order, against right-branching Paraphrase sentences expressing the same propositions. A
Level-n Test sentence has an n-verb cluster. Three groups of 30 subjects heard the sentences, rated
each on a 9-point scale from 1 (easy) to 9 (difficult), and after two-thirds of the Level 2 and
Level 3 Test and Paraphrase sentences answered a question asking what one of the noun phrases did,
scored 2 for naming the verb and its object, 1 for one of the two.

## References

* [bach-brown-marslen-wilson-1986]
-/

@[expose] public section

namespace BachBrownMarslenWilson1986

open Data.Statistics

/-- The three groups of subjects. -/
inductive Group where
  /-- Dutch: subjects from the student community in the Nijmegen area, hearing the Dutch
  materials -/
  | dutch
  /-- German/Inf.: subjects from the University of Köln, hearing the version of the German
  materials whose final verbs are infinitives -/
  | germanInf
  /-- German/Part.: subjects from the University of Köln, hearing the version of the German
  materials whose final verbs are past participles, except lassen, which occurs only in the
  infinitive -/
  | germanPart
  deriving DecidableEq, Repr, Fintype

/-- The questioned noun phrases of a Level 3 sentence, from the highest clause to the most deeply
embedded: NPk is the subject of the k-th verb from the top of the cluster. -/
inductive NounPhrase where
  /-- NP1: the subject of the matrix verb -/
  | np1
  /-- NP2: the subject of the verb the matrix verb embeds -/
  | np2
  /-- NP3: the subject of the most deeply embedded verb -/
  | np3
  deriving DecidableEq, Repr, Fintype

/-- Paid subjects in each of the three groups. (Subjects, p. 254; checked against the page
images.) -/
def subjectsPerGroup : ℕ := 30

/-- A row of Table 1, p. 255: the mean comprehensibility ratings of the Test and Paraphrase
sentences, collapsed over items and subjects, on the scale from 1 (easy) to 9 (difficult);
the printed Mean column, the mean of the three groups, is left out. -/
structure Rating where
  /-- The level: the number of verbs in the cluster of the Test sentence. -/
  level : ℕ
  /-- The group. -/
  group : Group
  /-- The mean rating of the Test sentences. -/
  test : Decimal
  /-- The mean rating of the Paraphrase sentences; Level 1 had none. -/
  para : Option Decimal
  deriving DecidableEq, Repr

/-- The 12 rows of Table 1, p. 255, in the paper's order; from an experiment; checked against the
page images. -/
def ratings : List Rating :=
  [⟨1, .dutch, ⟨114, 2⟩, none⟩,
   ⟨1, .germanInf, ⟨109, 2⟩, none⟩,
   ⟨1, .germanPart, ⟨124, 2⟩, none⟩,
   ⟨2, .dutch, ⟨234, 2⟩, some ⟨211, 2⟩⟩,
   ⟨2, .germanInf, ⟨277, 2⟩, some ⟨202, 2⟩⟩,
   ⟨2, .germanPart, ⟨263, 2⟩, some ⟨236, 2⟩⟩,
   ⟨3, .dutch, ⟨542, 2⟩, some ⟨406, 2⟩⟩,
   ⟨3, .germanInf, ⟨616, 2⟩, some ⟨413, 2⟩⟩,
   ⟨3, .germanPart, ⟨581, 2⟩, some ⟨385, 2⟩⟩,
   ⟨4, .dutch, ⟨766, 2⟩, some ⟨594, 2⟩⟩,
   ⟨4, .germanInf, ⟨826, 2⟩, some ⟨589, 2⟩⟩,
   ⟨4, .germanPart, ⟨766, 2⟩, some ⟨562, 2⟩⟩]

/-- A row of Table 2, p. 255: the mean comprehensibility ratings of the Filler sentences, matched
to Levels 1 to 3 in numbers of nouns and verbs but not in structure. -/
structure FillerRating where
  /-- The level the fillers were matched to. -/
  level : ℕ
  /-- The group. -/
  group : Group
  /-- The mean rating. -/
  rating : Decimal
  deriving DecidableEq, Repr

/-- The 9 rows of Table 2, p. 255, in the paper's order; from an experiment; checked against the
page images. -/
def fillerRatings : List FillerRating :=
  [⟨1, .dutch, ⟨142, 2⟩⟩,
   ⟨1, .germanInf, ⟨122, 2⟩⟩,
   ⟨1, .germanPart, ⟨137, 2⟩⟩,
   ⟨2, .dutch, ⟨221, 2⟩⟩,
   ⟨2, .germanInf, ⟨212, 2⟩⟩,
   ⟨2, .germanPart, ⟨229, 2⟩⟩,
   ⟨3, .dutch, ⟨331, 2⟩⟩,
   ⟨3, .germanInf, ⟨321, 2⟩⟩,
   ⟨3, .germanPart, ⟨355, 2⟩⟩]

/-- A row of Table 3, p. 257: the mean number correct in the comprehension test, out of 2; no
questions were asked about Level 1 or Level 4 sentences. -/
structure Comprehension where
  /-- The level: the number of verbs in the cluster of the Test sentence. -/
  level : ℕ
  /-- The group. -/
  group : Group
  /-- The mean score on the Test sentences. -/
  test : Decimal
  /-- The mean score on the Paraphrase sentences. -/
  para : Decimal
  deriving DecidableEq, Repr

/-- The 6 rows of Table 3, p. 257, in the paper's order; from an experiment; checked against the
page images. -/
def comprehension : List Comprehension :=
  [⟨2, .dutch, ⟨168, 2⟩, ⟨182, 2⟩⟩,
   ⟨2, .germanInf, ⟨173, 2⟩, ⟨190, 2⟩⟩,
   ⟨2, .germanPart, ⟨158, 2⟩, ⟨170, 2⟩⟩,
   ⟨3, .dutch, ⟨117, 2⟩, ⟨140, 2⟩⟩,
   ⟨3, .germanInf, ⟨89, 2⟩, ⟨144, 2⟩⟩,
   ⟨3, .germanPart, ⟨79, 2⟩, ⟨124, 2⟩⟩]

/-- A row of Table 4, p. 258: the Level 3 comprehension scores, out of 2, by the noun phrase
questioned. -/
structure ComprehensionByNP where
  /-- The mean score on the Test sentences. -/
  test : Decimal
  /-- The mean score on the Paraphrase sentences. -/
  para : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 4, p. 258, by group and nounPhrase; from an experiment; checked against
the page images. -/
def comprehensionByNP : Group → NounPhrase → ComprehensionByNP
  | .dutch, .np1 => ⟨⟨117, 2⟩, ⟨128, 2⟩⟩
  | .dutch, .np2 => ⟨⟨83, 2⟩, ⟨142, 2⟩⟩
  | .dutch, .np3 => ⟨⟨150, 2⟩, ⟨150, 2⟩⟩
  | .germanInf, .np1 => ⟨⟨88, 2⟩, ⟨120, 2⟩⟩
  | .germanInf, .np2 => ⟨⟨67, 2⟩, ⟨158, 2⟩⟩
  | .germanInf, .np3 => ⟨⟨112, 2⟩, ⟨153, 2⟩⟩
  | .germanPart, .np1 => ⟨⟨102, 2⟩, ⟨133, 2⟩⟩
  | .germanPart, .np2 => ⟨⟨38, 2⟩, ⟨107, 2⟩⟩
  | .germanPart, .np3 => ⟨⟨97, 2⟩, ⟨133, 2⟩⟩

/-- A row of Table 5, p. 258: the Level 3 differences in error rate between Test and Paraphrase
sentences, by the noun phrase questioned. -/
structure ErrorDifference where
  /-- The printed difference. -/
  difference : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 5, p. 258, by group and nounPhrase; from an experiment; checked against
the page images. -/
def errorDifference : Group → NounPhrase → ErrorDifference
  | .dutch, .np1 => ⟨⟨11, 2⟩⟩
  | .dutch, .np2 => ⟨⟨59, 2⟩⟩
  | .dutch, .np3 => ⟨⟨0, 2⟩⟩
  | .germanInf, .np1 => ⟨⟨32, 2⟩⟩
  | .germanInf, .np2 => ⟨⟨91, 2⟩⟩
  | .germanInf, .np3 => ⟨⟨41, 2⟩⟩
  | .germanPart, .np1 => ⟨⟨31, 2⟩⟩
  | .germanPart, .np2 => ⟨⟨67, 2⟩⟩  -- Table 4 gives 1.07 - 0.38 = 0.69
  | .germanPart, .np3 => ⟨⟨36, 2⟩⟩

end BachBrownMarslenWilson1986
