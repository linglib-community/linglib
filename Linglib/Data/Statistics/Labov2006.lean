module

public import Linglib.Data.Statistics.Schema

/-!
# Labov2006: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/Labov2006.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

Labov's printed tables from the second edition of the New York City survey: (r) and stops in
*fourth* in the department store survey, the class stratification of the five phonological variables
by class group and contextual style, the distributions in apparent time of /ʌy/, (r), (æh), (oh),
(th) and (dh) by age and class or ethnic group, and the (ing) index by age, social class and style.

## References

* [labov-2006]
-/

@[expose] public section

namespace Labov2006

open Data.Statistics

/-- The three department stores of the Chapter 3 survey, from the least to the most prestigious. -/
inductive Store where
  /-- S. Klein: the lowest-ranking store, on Union Square -/
  | klein
  /-- Macy's: the middle-ranking store, on Herald Square -/
  | macys
  /-- Saks: Saks Fifth Avenue, the highest-ranking store -/
  | saks
  deriving DecidableEq, Repr, Fintype

/-- The five phonological variables of the Lower East Side survey. -/
inductive Variable where
  /-- (r): the percentage of constricted [r] where /r/ is final or preconsonantal, as in *car*,
  *card* -/
  | r
  /-- (æh): the height of the vowel of *bad*, *ask*, *dance*: ten times the mean code on a scale
  from 1, high, to 6, low -/
  | aeh
  /-- (oh): the height of the vowel of *caught*, *talk*, *off*, coded as (æh) -/
  | oh
  /-- (th): the initial consonant of *thing*: one hundred times the mean code less one, coding
  the fricative 1, the affricate 2 and the stop 3 -/
  | th
  /-- (dh): the initial consonant of *then*, coded as (th) -/
  | dh
  deriving DecidableEq, Repr, Fintype

/-- The contextual styles of Chapter 4, from the least to the most attention paid to speech. -/
inductive Style where
  /-- A: casual speech -/
  | casual
  /-- B: careful speech, the interview style -/
  | careful
  /-- C: reading style -/
  | reading
  /-- D: word lists -/
  | wordList
  /-- D′: minimal pairs -/
  | minimalPair
  deriving DecidableEq, Repr, Fintype

/-- The three groups of the ten-point socioeconomic index in Table 7.8, with 23, 28 and 30
informants. -/
inductive ClassGroup where
  /-- 0–2: the lower class -/
  | lower
  /-- 3–5: the working class -/
  | working
  /-- 6–9: the middle class -/
  | middle
  deriving DecidableEq, Repr, Fintype

/-- The four groups of the socioeconomic index in Tables 9.7 and 9.10. -/
inductive SocioeconomicClass where
  /-- 0–1: the lower class -/
  | lower
  /-- 2–5: the working class -/
  | working
  /-- 6–8: the lower middle class -/
  | lowerMiddle
  /-- 9: the upper middle class -/
  | upperMiddle
  deriving DecidableEq, Repr, Fintype

/-- The social class index of Table 8.2, which crosses education with occupation. -/
inductive SocialClass where
  /-- SC 1: no high school -/
  | sc1
  /-- SC 2: at least some high school, blue-collar occupation -/
  | sc2
  /-- SC 3: at least some high school, white-collar occupation -/
  | sc3
  /-- SC 4: at least some high school, professional occupation -/
  | sc4
  deriving DecidableEq, Repr, Fintype

/-- The two adult age groups of the apparent-time tables. -/
inductive AgeGroup where
  /-- 20–39: speakers aged 20 to 39 -/
  | younger
  /-- 40–: speakers aged 40 and over -/
  | older
  deriving DecidableEq, Repr, Fintype

/-- The three age levels of Table 9.10. -/
inductive AgeLevel where
  /-- 8–19: speakers aged 8 to 19 -/
  | youth
  /-- 20–39: speakers aged 20 to 39 -/
  | younger
  /-- 40–: speakers aged 40 and over -/
  | older
  deriving DecidableEq, Repr, Fintype

/-- The five age levels of Table 9.14. -/
inductive AehAgeLevel where
  /-- 8–19: speakers aged 8 to 19 -/
  | age8to19
  /-- 20–39: speakers aged 20 to 39 -/
  | age20to39
  /-- 40–49: speakers aged 40 to 49 -/
  | age40to49
  /-- 50–59: speakers aged 50 to 59 -/
  | age50to59
  /-- 60–: speakers aged 60 and over -/
  | age60
  deriving DecidableEq, Repr, Fintype

/-- The five age levels of the (oh) table 9.17. -/
inductive OhAgeLevel where
  /-- 8–19: speakers aged 8 to 19 -/
  | age8to19
  /-- 20–35: speakers aged 20 to 35 -/
  | age20to35
  /-- 36–49: speakers aged 36 to 49 -/
  | age36to49
  /-- 50–59: speakers aged 50 to 59 -/
  | age50to59
  /-- 60–: speakers aged 60 and over -/
  | age60
  deriving DecidableEq, Repr, Fintype

/-- A row of Table 3.4, p. 49: the percentage of a store's employees with complete responses who
used constricted (r) in all four positions, in some, and in none, and their number. -/
structure CompleteResponses where
  /-- The percentage using (r-1) in all four positions. -/
  allR1 : ℕ
  /-- The percentage using (r-1) in some positions. -/
  someR1 : ℕ
  /-- The percentage using no (r-1). -/
  noR1 : ℕ
  /-- The number of employees with complete responses. -/
  n : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 3.4, p. 49, by store; from a sociolinguistic survey; checked against the
page images. -/
def completeResponses : Store → CompleteResponses
  | .saks => ⟨24, 46, 30, 33⟩
  | .macys => ⟨22, 37, 41, 48⟩
  | .klein => ⟨6, 12, 82, 34⟩

/-- A row of p. 52: the percentage of a store's employees who used a stop for (th) in *fourth*. -/
structure FourthStops where
  /-- The percentage using a stop, printed with two digits. -/
  percent : ℕ
  deriving DecidableEq, Repr

/-- The cells of p. 52, by store; from a sociolinguistic survey; checked against the page images. -/
def fourthStops : Store → FourthStops
  | .saks => ⟨0⟩
  | .macys => ⟨4⟩
  | .klein => ⟨15⟩

/-- A row of Table 7.8, p. 140: the index of a variable for a class group in each style the
variable was measured in, with the number of informants behind each cell. -/
structure StratificationRow where
  /-- The index in casual speech. -/
  casual : Option Decimal
  /-- The index in careful speech. -/
  careful : Option Decimal
  /-- The index in reading style. -/
  reading : Option Decimal
  /-- The index in word lists. -/
  wordList : Option Decimal
  /-- The index in minimal pairs. -/
  minimalPair : Option Decimal
  /-- The number of informants in casual speech. -/
  nCasual : Option ℕ
  /-- The number of informants in careful speech. -/
  nCareful : Option ℕ
  /-- The number of informants in reading style. -/
  nReading : Option ℕ
  /-- The number of informants in word lists. -/
  nWordList : Option ℕ
  /-- The number of informants in minimal pairs. -/
  nMinimalPair : Option ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 7.8, p. 140, by group and variable; from a sociolinguistic survey; checked
against the page images. -/
def classStratification : ClassGroup → Variable → StratificationRow
  | .lower, .r =>
    ⟨some ⟨25, 1⟩,
     some ⟨105, 1⟩,
     some ⟨145, 1⟩,
     some ⟨235, 1⟩,
     some ⟨495, 1⟩,
     some 18,
     some 22,
     some 14,
     some 17,
     some 17⟩
  | .lower, .aeh =>
    ⟨some ⟨230, 1⟩,
     some ⟨270, 1⟩,
     some ⟨290, 1⟩,
     some ⟨320, 1⟩,
     none,
     some 13,
     some 21,
     some 13,
     some 17,
     none⟩
  | .lower, .oh =>
    ⟨some ⟨230, 1⟩,
     some ⟨240, 1⟩,
     some ⟨240, 1⟩,
     some ⟨210, 1⟩,
     none,
     some 16,
     some 22,
     some 13,
     some 15,
     none⟩
  | .lower, .th =>
    ⟨some ⟨780, 1⟩,
     some ⟨650, 1⟩,
     some ⟨435, 1⟩,
     none,
     none,
     some 18,
     some 22,
     some 13,
     none,
     none⟩
  | .lower, .dh =>
    ⟨some ⟨785, 1⟩,
     some ⟨560, 1⟩,
     some ⟨490, 1⟩,
     none,
     none,
     some 17,
     some 22,
     some 13,
     none,
     none⟩
  | .working, .r =>
    ⟨some ⟨40, 1⟩,
     some ⟨125, 1⟩,
     some ⟨210, 1⟩,
     some ⟨350, 1⟩,
     some ⟨550, 1⟩,
     some 26,
     some 28,
     some 26,
     some 27,
     some 26⟩
  | .working, .aeh =>
    ⟨some ⟨250, 1⟩,
     some ⟨280, 1⟩,
     some ⟨305, 1⟩,
     some ⟨320, 1⟩,
     none,
     some 21,
     some 27,
     some 26,
     some 27,
     none⟩
  | .working, .oh =>
    ⟨some ⟨195, 1⟩,
     some ⟨220, 1⟩,
     some ⟨230, 1⟩,
     some ⟨240, 1⟩,
     none,
     some 23,
     some 28,
     some 26,
     some 27,
     none⟩
  | .working, .th =>
    ⟨some ⟨680, 1⟩,
     some ⟨535, 1⟩,
     some ⟨270, 1⟩,
     none,
     none,
     some 15,
     some 28,
     some 26,
     none,
     none⟩
  | .working, .dh =>
    ⟨some ⟨635, 1⟩,
     some ⟨445, 1⟩,
     some ⟨340, 1⟩,
     none,
     none,
     some 22,
     some 28,
     some 26,
     none,
     none⟩
  | .middle, .r =>
    ⟨some ⟨125, 1⟩,
     some ⟨250, 1⟩,
     some ⟨290, 1⟩,
     some ⟨555, 1⟩,
     some ⟨700, 1⟩,
     some 21,
     some 30,
     some 29,
     some 29,
     some 29⟩
  | .middle, .aeh =>
    ⟨some ⟨270, 1⟩,
     some ⟨300, 1⟩,
     some ⟨340, 1⟩,
     some ⟨350, 1⟩,
     none,
     some 23,
     some 30,
     some 29,
     some 29,
     none⟩
  | .middle, .oh =>
    ⟨some ⟨200, 1⟩,
     some ⟨235, 1⟩,
     some ⟨265, 1⟩,
     some ⟨295, 1⟩,
     none,
     some 27,
     some 30,
     some 29,
     some 27,
     none⟩
  | .middle, .th =>
    ⟨some ⟨255, 1⟩,
     some ⟨165, 1⟩,
     some ⟨100, 1⟩,
     none,
     none,
     some 23,
     some 30,
     some 29,
     none,
     none⟩
  | .middle, .dh =>
    ⟨some ⟨295, 1⟩,
     some ⟨165, 1⟩,
     some ⟨130, 1⟩,
     none,
     none,
     some 27,
     some 30,
     some 29,
     none,
     none⟩

/-- A row of Table 9.7, p. 214: the percentage of speakers of an age group and socioeconomic
class who used any upgliding /ʌy/, as in *bird*, in any style, and their number. -/
structure UpglidingCell where
  /-- The percentage using any /ʌy/. -/
  percent : ℕ
  /-- The number of speakers. -/
  n : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 9.7, p. 214, by ageGroup and socioeconomicClass; from a sociolinguistic
survey; checked against the page images. -/
def upglidingByAgeAndClass : AgeGroup → SocioeconomicClass → UpglidingCell
  | .younger, .lower => ⟨75, 4⟩
  | .younger, .working => ⟨35, 16⟩
  | .younger, .lowerMiddle => ⟨9, 11⟩
  | .younger, .upperMiddle => ⟨0, 7⟩
  | .older, .lower => ⟨85, 13⟩
  | .older, .working => ⟨57, 35⟩
  | .older, .lowerMiddle => ⟨35, 17⟩
  | .older, .upperMiddle => ⟨0, 7⟩

/-- A row of Table 9.10, p. 218: the average (r) index in casual speech of an age level and
socioeconomic group, and the number of speakers. -/
structure RCasualCell where
  /-- The average (r) index. -/
  index : ℕ
  /-- The number of speakers. -/
  n : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 9.10, p. 218, by ageLevel and socioeconomicClass; from a sociolinguistic
survey; checked against the page images. -/
def rCasualByAgeAndClass : AgeLevel → SocioeconomicClass → RCasualCell
  | .youth, .lower => ⟨0, 6⟩
  | .youth, .working => ⟨1, 16⟩
  | .youth, .lowerMiddle => ⟨0, 6⟩
  | .youth, .upperMiddle => ⟨48, 4⟩
  | .younger, .lower => ⟨0, 3⟩
  | .younger, .working => ⟨0, 13⟩
  | .younger, .lowerMiddle => ⟨0, 9⟩
  | .younger, .upperMiddle => ⟨34, 4⟩
  | .older, .lower => ⟨0, 10⟩
  | .older, .working => ⟨6, 25⟩
  | .older, .lowerMiddle => ⟨9, 8⟩
  | .older, .upperMiddle => ⟨9, 7⟩

/-- A row of Table 9.11, p. 218: the percentage of speakers of an age group who used some (r-1)
in casual speech, for socioeconomic groups 0–8 together and for group 9. -/
structure SomeRCasualRow where
  /-- The percentage among socioeconomic classes 0–8. -/
  lowerClasses : ℕ
  /-- The percentage in socioeconomic class 9. -/
  upperMiddle : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 9.11, p. 218, by ageGroup; from a sociolinguistic survey; checked against
the page images. -/
def someRCasualByAge : AgeGroup → SomeRCasualRow
  | .younger => ⟨6, 87⟩
  | .older => ⟨31, 43⟩

/-- A row of Table 9.13, p. 227: the average (æh) index in casual speech of an age group and
social class, and the number of speakers. -/
structure AehCell where
  /-- The average (æh) index. -/
  index : ℕ
  /-- The number of speakers. -/
  n : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 9.13, p. 227, by ageGroup and socialClass; from a sociolinguistic survey;
checked against the page images. -/
def aehByAgeAndClass : AgeGroup → SocialClass → AehCell
  | .younger, .sc1 => ⟨24, 2⟩
  | .younger, .sc2 => ⟨24, 11⟩
  | .younger, .sc3 => ⟨22, 5⟩
  | .younger, .sc4 => ⟨35, 4⟩
  | .older, .sc1 => ⟨27, 17⟩
  | .older, .sc2 => ⟨26, 8⟩
  | .older, .sc3 => ⟨25, 10⟩
  | .older, .sc4 => ⟨31, 6⟩

/-- A row of Table 9.14, p. 227: the (æh) index of the lower class SC 1 at each age level. -/
structure AehLowerClassRow where
  /-- The (æh) index. -/
  index : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 9.14, p. 227, by ageLevel; from a sociolinguistic survey; checked against
the page images. -/
def aehLowerClassByAge : AehAgeLevel → AehLowerClassRow
  | .age8to19 => ⟨20⟩
  | .age20to39 => ⟨24⟩
  | .age40to49 => ⟨26⟩
  | .age50to59 => ⟨28⟩
  | .age60 => ⟨28⟩

/-- A row of Table 9.16, p. 229: the average (oh) index in casual speech of an age group and
social class, and the number of speakers. -/
structure OhCell where
  /-- The average (oh) index. -/
  index : ℕ
  /-- The number of speakers. -/
  n : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 9.16, p. 229, by ageGroup and socialClass; from a sociolinguistic survey;
checked against the page images. -/
def ohByAgeAndClass : AgeGroup → SocialClass → OhCell
  | .younger, .sc1 => ⟨21, 3⟩
  | .younger, .sc2 => ⟨22, 12⟩
  | .younger, .sc3 => ⟨18, 6⟩
  | .younger, .sc4 => ⟨22, 5⟩
  | .older, .sc1 => ⟨23, 17⟩
  | .older, .sc2 => ⟨22, 9⟩
  | .older, .sc3 => ⟨19, 12⟩
  | .older, .sc4 => ⟨22, 6⟩

/-- A row of Table 9.17, p. 229: the average (oh) index at an age level of Jews, Italians and
other speakers in social classes 1–3, and of the upper middle class SC 4; the dash of the
oldest SC 4 cell is blank. -/
structure OhEthnicRow where
  /-- The index of the Jewish speakers of SC 1–3. -/
  jews : ℕ
  /-- The index of the Italian speakers of SC 1–3. -/
  italians : ℕ
  /-- The index of the other speakers of SC 1–3. -/
  others : ℕ
  /-- The index of SC 4. -/
  upperMiddle : Option ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 9.17, p. 229, by ageLevel; from a sociolinguistic survey; checked against
the page images. -/
def ohByAgeAndEthnicity : OhAgeLevel → OhEthnicRow
  | .age8to19 => ⟨17, 18, 22, some 23⟩
  | .age20to35 => ⟨18, 18, 16, some 22⟩  -- the others' cell is printed in parentheses
  | .age36to49 => ⟨17, 20, 18, some 22⟩
  | .age50to59 => ⟨15, 20, 15, some 22⟩
  | .age60 => ⟨25, 30, 25, none⟩

/-- A row of Table 9.18, p. 234: the average (th) and (dh) indexes in casual speech of an age
group and social class, with the number of speakers behind each. -/
structure ThDhCell where
  /-- The average (th) index. -/
  th : ℕ
  /-- The average (dh) index. -/
  dh : ℕ
  /-- The number of speakers for (th). -/
  nTh : ℕ
  /-- The number of speakers for (dh). -/
  nDh : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 9.18, p. 234, by ageGroup and socialClass; from a sociolinguistic survey;
checked against the page images. -/
def thDhByAgeAndClass : AgeGroup → SocialClass → ThDhCell
  | .younger, .sc1 => ⟨111, 109, 3, 3⟩
  | .younger, .sc2 => ⟨46, 59, 12, 12⟩
  | .younger, .sc3 => ⟨34, 41, 6, 6⟩
  | .younger, .sc4 => ⟨6, 10, 5, 6⟩
  | .older, .sc1 => ⟨92, 87, 19, 20⟩
  | .older, .sc2 => ⟨30, 45, 5, 8⟩
  | .older, .sc3 => ⟨23, 18, 7, 10⟩
  | .older, .sc4 => ⟨18, 32, 3, 5⟩

/-- A row of Table 9.19, p. 234: the (th), (dh) and (r) indexes of social classes 1–3 taken
together, by age group. -/
structure PooledRow where
  /-- The (th) index of SC 1–3. -/
  th : ℕ
  /-- The (dh) index of SC 1–3. -/
  dh : ℕ
  /-- The (r) index of SC 1–3. -/
  r : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 9.19, p. 234, by ageGroup; from a sociolinguistic survey; checked against
the page images. -/
def pooledLowerClasses : AgeGroup → PooledRow
  | .younger => ⟨57, 59, 0⟩
  | .older => ⟨69, 61, 5⟩

/-- A row of Table 10.10, p. 258: the average (ing) index, the percentage of /in/, of adult white
New York City informants of an age group and social class in casual and in careful speech,
with the number of speakers behind each. -/
structure IngCell where
  /-- The index in casual speech, Style A. -/
  casual : ℕ
  /-- The index in careful speech, Style B. -/
  careful : ℕ
  /-- The number of speakers in casual speech. -/
  nCasual : ℕ
  /-- The number of speakers in careful speech. -/
  nCareful : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 10.10, p. 258, by ageGroup and socialClass; from a sociolinguistic survey;
checked against the page images. -/
def ingByAgeAndClass : AgeGroup → SocialClass → IngCell
  | .younger, .sc1 => ⟨90, 75, 2, 4⟩
  | .younger, .sc2 => ⟨60, 45, 10, 14⟩
  | .younger, .sc3 => ⟨43, 50, 6, 5⟩
  | .younger, .sc4 => ⟨0, 2, 4, 9⟩
  | .older, .sc1 => ⟨85, 50, 24, 22⟩
  | .older, .sc2 => ⟨48, 27, 8, 12⟩
  | .older, .sc3 => ⟨21, 12, 10, 21⟩
  | .older, .sc4 => ⟨23, 2, 5, 10⟩

end Labov2006
