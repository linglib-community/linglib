module

public import Linglib.Data.Statistics.Schema

/-!
# CoetzeePater2011: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/CoetzeePater2011.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

Coetzee and Pater's printed t/d-deletion data and model results, after the ROA-946 draft of 6
October 2009: deletion rates by morphological status (7) and by following context (10), the deletion
probabilities of five partially ordered grammars (13), the Japanese loanword grammars learned by
stochastic OT and Noisy HG (21), the grammars learned for each dialect and for the constructed
Tejano′ (23), the Goldvarb fits (25), and the lexically indexed Noisy HG grammar (32). The observed
rows of (23) for the seven dialects repeat (10) as proportions and are not stored again. Footnote 7
places the input files of the learning simulations in the archive coetzee-pater-variation.zip on
Pater's UMass page.

## References

* [coetzee-pater-2011]
-/

@[expose] public section

namespace CoetzeePater2011

open Data.Statistics

/-- What follows the word-final t/d. -/
inductive Context where
  /-- Pre-V: a vowel, *west end* -/
  | preV
  /-- Pre-Pause: a pause, *west* -/
  | pause
  /-- Pre-C: a consonant, *west side* -/
  | preC
  deriving DecidableEq, Repr, Fintype

/-- The dialects of English whose deletion rates the paper reports, with the sources footnote 3
gives for (10). -/
inductive Dialect where
  /-- AAVE (Washington, DC): after Fasold 1972 -/
  | aave
  /-- Chicano English: after Santa Ana 1991 -/
  | chicano
  /-- Jamaican English: after Patrick 1992 -/
  | jamaican
  /-- New York City English: after Guy 1980 -/
  | newYorkCity
  /-- Tejano English: after Bayley 1995 -/
  | tejano
  /-- Trinidadian English: after Kang 1994 -/
  | trinidad
  /-- Philadelphia English: after Guy 1980 -/
  | philadelphia
  deriving DecidableEq, Repr, Fintype

/-- The ranking a partially ordered grammar of (13) imposes on the constraints of (11). -/
inductive ImposedRanking where
  /-- None: no ranking imposed -/
  | none
  /-- MAX-PRE-V >> *CT: MAX-PRE-V dominates *CT -/
  | maxPreVOverStarCT
  /-- *CT >> MAX-PRE-V: *CT dominates MAX-PRE-V -/
  | starCTOverMaxPreV
  /-- MAX-FIN >> *CT: MAX-FINAL dominates *CT -/
  | maxFinalOverStarCT
  /-- *CT >> MAX-FIN: *CT dominates MAX-FINAL -/
  | starCTOverMaxFinal
  deriving DecidableEq, Repr, Fintype

/-- The stochastic grammars the paper's learners use. -/
inductive Model where
  /-- St-OT: stochastic OT, learned by the OT-GLA -/
  | stOT
  /-- N-HG: Noisy Harmonic Grammar, learned by the HG-GLA -/
  | nHG
  /-- ME-HG: Maximum Entropy Harmonic Grammar, learned by the HG-GLA -/
  | meHG
  deriving DecidableEq, Repr, Fintype

/-- The Japanese loanwords of (18)–(19). -/
inductive Loan where
  /-- bobu: 'Bob', two voiced obstruents -/
  | bobu
  /-- webbu: 'web', a voiced geminate -/
  | webbu
  /-- guddo: 'good', a voiced geminate and another voiced obstruent -/
  | guddo
  deriving DecidableEq, Repr, Fintype

/-- The varieties fitted by Goldvarb in (25). -/
inductive Variety where
  /-- Tejano: Bayley's Tejano English -/
  | tejano
  /-- Tejano': Tejano with the pre-vocalic and pre-consonantal rates traded -/
  | tejanoPrime
  deriving DecidableEq, Repr, Fintype

/-- The words of the lexically indexed simulation (32). -/
inductive Lexeme where
  /-- feast: the word *feast* -/
  | feast
  /-- most: the word *most* -/
  | most
  deriving DecidableEq, Repr, Fintype

/-- The factor weight of a hypothetical informal register in (27). ((27), p. 24; checked against
the page images.) -/
def informalRegisterFactor : Decimal := ⟨70, 2⟩

/-- The weight of *CT in (32). ((32), p. 29; checked against the page images.) -/
def indexedStarCT : Decimal := ⟨10071, 2⟩

/-- The weight of MAX-PRE-V indexed to *feast* in (32). ((32), p. 29; checked against the page
images.) -/
def indexedMaxPreVFeast : Decimal := ⟨118, 2⟩

/-- The weight of MAX-FINAL indexed to *feast* in (32). ((32), p. 29; checked against the page
images.) -/
def indexedMaxFinalFeast : Decimal := ⟨358, 2⟩

/-- The weight of MAX indexed to *feast* in (32). ((32), p. 29; checked against the page images.) -/
def indexedMaxFeast : Decimal := ⟨10007, 2⟩

/-- The weight of MAX-PRE-V indexed to *most* in (32). ((32), p. 29; checked against the page
images.) -/
def indexedMaxPreVMost : Decimal := ⟨116, 2⟩

/-- The weight of MAX-FINAL indexed to *most* in (32). ((32), p. 29; checked against the page
images.) -/
def indexedMaxFinalMost : Decimal := ⟨327, 2⟩

/-- The weight of MAX indexed to *most* in (32). ((32), p. 29; checked against the page images.) -/
def indexedMaxMost : Decimal := ⟨9922, 2⟩

/-- A row of (7), p. 6: the percentage of t/d deleted by morphological status in a dialect. -/
structure MorphRate where
  /-- The dialect. -/
  dialect : Dialect
  /-- The percentage deleted from a regular past suffix, *missed*. -/
  regularPast : ℕ
  /-- The percentage deleted from a semi-weak past, *kept*. -/
  semiWeakPast : ℕ
  /-- The percentage deleted from a monomorpheme, *mist*. -/
  monomorpheme : ℕ
  deriving DecidableEq, Repr

/-- The 3 rows of (7), p. 6, in the paper's order; from a sociolinguistic survey; checked against
the page images. -/
def morphRates : List MorphRate :=
  [⟨.philadelphia, 17, 34, 38⟩,  -- Guy 1991b
   ⟨.chicano, 26, 41, 58⟩,  -- Santa Ana 1992
   ⟨.tejano, 24, 34, 56⟩]  -- Bayley 1997

/-- A row of (10), p. 9: the percentage of t/d deleted in a dialect before a following context. -/
structure ContextRate where
  /-- The percentage deleted. -/
  percent : ℕ
  deriving DecidableEq, Repr

/-- The cells of (10), p. 9, by dialect and context; from a sociolinguistic survey; checked
against the page images. -/
def contextRates : Dialect → Context → ContextRate
  | .aave, .preV => ⟨29⟩
  | .aave, .pause => ⟨73⟩
  | .aave, .preC => ⟨76⟩
  | .chicano, .preV => ⟨45⟩
  | .chicano, .pause => ⟨37⟩
  | .chicano, .preC => ⟨62⟩
  | .jamaican, .preV => ⟨63⟩
  | .jamaican, .pause => ⟨71⟩
  | .jamaican, .preC => ⟨85⟩
  | .newYorkCity, .preV => ⟨66⟩
  | .newYorkCity, .pause => ⟨83⟩
  | .newYorkCity, .preC => ⟨100⟩
  | .tejano, .preV => ⟨25⟩
  | .tejano, .pause => ⟨46⟩
  | .tejano, .preC => ⟨62⟩
  | .trinidad, .preV => ⟨21⟩
  | .trinidad, .pause => ⟨31⟩
  | .trinidad, .preC => ⟨81⟩
  | .philadelphia, .preV => ⟨38⟩
  | .philadelphia, .pause => ⟨12⟩
  | .philadelphia, .preC => ⟨100⟩

/-- A row of (13), p. 12: the number of a partially ordered grammar's linear extensions that
delete in a context, out of all of them, and the probability of deletion. Counting the linear
extensions of the grammars of rows (b)–(e) does not give the printed counts; the study
records the discrepancy. -/
structure GrammarRate where
  /-- The number of linear extensions that delete. -/
  rankings : ℕ
  /-- The number of linear extensions. -/
  total : ℕ
  /-- The probability of deletion. -/
  probability : Decimal
  deriving DecidableEq, Repr

/-- The cells of (13), p. 12, by imposedRanking and context; fitted or simulated by a model;
checked against the page images. -/
def pocRates : ImposedRanking → Context → GrammarRate
  | .none, .preV => ⟨8, 24, ⟨33, 2⟩⟩
  | .none, .pause => ⟨8, 24, ⟨33, 2⟩⟩
  | .none, .preC => ⟨12, 24, ⟨50, 2⟩⟩
  | .maxPreVOverStarCT, .preV => ⟨0, 12, ⟨0, 0⟩⟩
  | .maxPreVOverStarCT, .pause => ⟨4, 12, ⟨33, 2⟩⟩
  | .maxPreVOverStarCT, .preC => ⟨6, 12, ⟨50, 2⟩⟩
  | .starCTOverMaxPreV, .preV => ⟨6, 12, ⟨50, 2⟩⟩
  | .starCTOverMaxPreV, .pause => ⟨4, 12, ⟨33, 2⟩⟩
  | .starCTOverMaxPreV, .preC => ⟨6, 12, ⟨50, 2⟩⟩
  | .maxFinalOverStarCT, .preV => ⟨4, 12, ⟨33, 2⟩⟩
  | .maxFinalOverStarCT, .pause => ⟨0, 12, ⟨0, 0⟩⟩
  | .maxFinalOverStarCT, .preC => ⟨6, 12, ⟨50, 2⟩⟩
  | .starCTOverMaxFinal, .preV => ⟨4, 12, ⟨33, 2⟩⟩
  | .starCTOverMaxFinal, .pause => ⟨6, 12, ⟨50, 2⟩⟩
  | .starCTOverMaxFinal, .preC => ⟨6, 12, ⟨50, 2⟩⟩

/-- A row of (21), p. 18: the constraint values a learner reached on the loanword data of
(18)–(19). -/
structure LoanwordGrammar where
  /-- The learner's grammar. -/
  model : Model
  /-- The value of OCP-VOICE. -/
  ocpVoice : Decimal
  /-- The value of *VOICED-GEMINATE. -/
  voicedGeminate : Decimal
  /-- The value of IDENT-VOICE. -/
  identVoice : Decimal
  deriving DecidableEq, Repr

/-- The 2 rows of (21), p. 18, in the paper's order; fitted or simulated by a model; checked
against the page images. -/
def loanwordWeights : List LoanwordGrammar :=
  [⟨.stOT, ⟨31139, 1⟩, ⟨31139, 1⟩, ⟨31137, 1⟩⟩,
   ⟨.nHG, ⟨668, 1⟩, ⟨676, 1⟩, ⟨1344, 1⟩⟩]

/-- A row of (21), p. 18: the frequency of devoicing of a loanword in the learning data and in
the grammars learned from it. -/
structure DevoicingRate where
  /-- The frequency of devoicing in the learning data. -/
  learningData : Decimal
  /-- The frequency of devoicing in the learned stochastic OT grammar. -/
  stOT : Decimal
  /-- The frequency of devoicing in the learned Noisy HG grammar. -/
  nHG : Decimal
  deriving DecidableEq, Repr

/-- The cells of (21), p. 18, by loan; fitted or simulated by a model; checked against the page
images. -/
def devoicingRates : Loan → DevoicingRate
  | .bobu => ⟨⟨0, 1⟩, ⟨15, 2⟩, ⟨0, 1⟩⟩
  | .webbu => ⟨⟨0, 1⟩, ⟨15, 2⟩, ⟨0, 1⟩⟩
  | .guddo => ⟨⟨50, 2⟩, ⟨25, 2⟩, ⟨50, 2⟩⟩

/-- A row of (23), p. 20: the constraint values a learner reached on a dialect's rates of (10),
and the probabilities of deletion its grammar encodes. -/
structure LearnedGrammar where
  /-- The value of *CT. -/
  starCT : Decimal
  /-- The value of MAX-PRE-V. -/
  maxPreV : Decimal
  /-- The value of MAX-FINAL. -/
  maxFinal : Decimal
  /-- The value of MAX. -/
  maxC : Decimal
  /-- The encoded probability of deletion before a vowel. -/
  preV : Decimal
  /-- The encoded probability of deletion before a pause. -/
  pause : Decimal
  /-- The encoded probability of deletion before a consonant. -/
  preC : Decimal
  deriving DecidableEq, Repr

/-- The cells of (23), p. 20, by dialect and model; fitted or simulated by a model; checked
against the page images. -/
def learnedGrammars : Dialect → Model → LearnedGrammar
  | .aave, .stOT => ⟨⟨1010, 1⟩, ⟨1023, 1⟩, ⟨968, 1⟩, ⟨990, 1⟩, ⟨29, 2⟩, ⟨73, 2⟩, ⟨76, 2⟩⟩
  | .aave, .nHG => ⟨⟨1010, 1⟩, ⟨58, 1⟩, ⟨-15, 1⟩, ⟨972, 1⟩, ⟨29, 2⟩, ⟨73, 2⟩, ⟨77, 2⟩⟩
  | .aave, .meHG => ⟨⟨1006, 1⟩, ⟨21, 1⟩, ⟨2, 1⟩, ⟨994, 1⟩, ⟨30, 2⟩, ⟨74, 2⟩, ⟨77, 2⟩⟩
  | .chicano, .stOT => ⟨⟨1004, 1⟩, ⟨997, 1⟩, ⟨1006, 1⟩, ⟨996, 1⟩, ⟨45, 2⟩, ⟨37, 2⟩, ⟨62, 2⟩⟩
  | .chicano, .nHG => ⟨⟨1004, 1⟩, ⟨10, 1⟩, ⟨18, 1⟩, ⟨996, 1⟩, ⟨43, 2⟩, ⟨36, 2⟩, ⟨60, 2⟩⟩
  | .chicano, .meHG => ⟨⟨1002, 1⟩, ⟨7, 1⟩, ⟨10, 1⟩, ⟨998, 1⟩, ⟨44, 2⟩, ⟨36, 2⟩, ⟨61, 2⟩⟩
  | .jamaican, .stOT => ⟨⟨1014, 1⟩, ⟨1000, 1⟩, ⟨992, 1⟩, ⟨986, 1⟩, ⟨63, 2⟩, ⟨70, 2⟩, ⟨84, 2⟩⟩
  | .jamaican, .nHG => ⟨⟨1015, 1⟩, ⟨17, 1⟩, ⟨8, 1⟩, ⟨985, 1⟩, ⟨63, 2⟩, ⟨70, 2⟩, ⟨85, 2⟩⟩
  | .jamaican, .meHG => ⟨⟨1009, 1⟩, ⟨12, 1⟩, ⟨8, 1⟩, ⟨991, 1⟩, ⟨64, 2⟩, ⟨73, 2⟩, ⟨85, 2⟩⟩
  | .newYorkCity, .stOT => ⟨⟨1076, 1⟩, ⟨1065, 1⟩, ⟨1049, 1⟩, ⟨924, 1⟩, ⟨66, 2⟩, ⟨84, 2⟩, ⟨100, 2⟩⟩
  | .newYorkCity, .nHG => ⟨⟨1411, 1⟩, ⟨809, 1⟩, ⟨790, 1⟩, ⟨589, 1⟩, ⟨65, 2⟩, ⟨83, 2⟩, ⟨100, 2⟩⟩
  | .newYorkCity, .meHG => ⟨⟨1404, 1⟩, ⟨803, 1⟩, ⟨793, 1⟩, ⟨596, 1⟩, ⟨65, 2⟩, ⟨83, 2⟩, ⟨100, 2⟩⟩
  | .tejano, .stOT => ⟨⟨1004, 1⟩, ⟨1019, 1⟩, ⟨996, 1⟩, ⟨996, 1⟩, ⟨25, 2⟩, ⟨46, 2⟩, ⟨62, 2⟩⟩
  | .tejano, .nHG => ⟨⟨1003, 1⟩, ⟨15, 1⟩, ⟨7, 1⟩, ⟨997, 1⟩, ⟨25, 2⟩, ⟨47, 2⟩, ⟨62, 2⟩⟩
  | .tejano, .meHG => ⟨⟨1004, 1⟩, ⟨32, 1⟩, ⟨7, 1⟩, ⟨996, 1⟩, ⟨27, 2⟩, ⟨46, 2⟩, ⟨63, 2⟩⟩
  | .trinidad, .stOT => ⟨⟨1012, 1⟩, ⟨1034, 1⟩, ⟨1025, 1⟩, ⟨988, 1⟩, ⟨21, 2⟩, ⟨31, 2⟩, ⟨80, 2⟩⟩
  | .trinidad, .nHG => ⟨⟨1012, 1⟩, ⟨52, 1⟩, ⟨41, 1⟩, ⟨988, 1⟩, ⟨21, 2⟩, ⟨31, 2⟩, ⟨80, 2⟩⟩
  | .trinidad, .meHG => ⟨⟨1007, 1⟩, ⟨28, 1⟩, ⟨22, 1⟩, ⟨993, 1⟩, ⟨21, 2⟩, ⟨32, 2⟩, ⟨81, 2⟩⟩
  | .philadelphia, .stOT => ⟨⟨1072, 1⟩, ⟨1082, 1⟩, ⟨1106, 1⟩, ⟨928, 1⟩, ⟨37, 2⟩, ⟨12, 2⟩, ⟨100, 2⟩⟩
  | .philadelphia, .nHG => ⟨⟨1392, 1⟩, ⟨794, 1⟩, ⟨824, 1⟩, ⟨608, 1⟩, ⟨38, 2⟩, ⟨12, 2⟩, ⟨100, 2⟩⟩
  | .philadelphia, .meHG => ⟨⟨1395, 1⟩, ⟨795, 1⟩, ⟨810, 1⟩, ⟨605, 1⟩, ⟨38, 2⟩, ⟨12, 2⟩, ⟨100, 2⟩⟩

/-- A row of (23), p. 20: the constraint values a learner reached on the rates of Tejano′, and
the probabilities of deletion its grammar encodes. -/
structure TejanoPrimeGrammar where
  /-- The value of *CT. -/
  starCT : Decimal
  /-- The value of MAX-PRE-V. -/
  maxPreV : Decimal
  /-- The value of MAX-FINAL. -/
  maxFinal : Decimal
  /-- The value of MAX. -/
  maxC : Decimal
  /-- The encoded probability of deletion before a vowel. -/
  preV : Decimal
  /-- The encoded probability of deletion before a pause. -/
  pause : Decimal
  /-- The encoded probability of deletion before a consonant. -/
  preC : Decimal
  deriving DecidableEq, Repr

/-- The cells of (23), p. 20, by model; fitted or simulated by a model; checked against the page
images. -/
def tejanoPrimeGrammars : Model → TejanoPrimeGrammar
  | .stOT => ⟨⟨998, 1⟩, ⟨-65113, 1⟩, ⟨-5232, 1⟩, ⟨1002, 1⟩, ⟨45, 2⟩, ⟨45, 2⟩, ⟨45, 2⟩⟩
  | .nHG => ⟨⟨998, 1⟩, ⟨-63821, 1⟩, ⟨-7352, 1⟩, ⟨1002, 1⟩, ⟨44, 2⟩, ⟨44, 2⟩, ⟨44, 2⟩⟩
  | .meHG => ⟨⟨994, 1⟩, ⟨-16, 1⟩, ⟨-8, 1⟩, ⟨1006, 1⟩, ⟨61, 2⟩, ⟨42, 2⟩, ⟨24, 2⟩⟩

/-- A row of (23), p. 20: the proportion of deletion in the learning data for Tejano′. -/
structure ObservedRate where
  /-- The proportion deleted. -/
  rate : Decimal
  deriving DecidableEq, Repr

/-- The cells of (23), p. 20, by context; fitted or simulated by a model; checked against the
page images. -/
def tejanoPrimeRates : Context → ObservedRate
  | .preV => ⟨⟨62, 2⟩⟩
  | .pause => ⟨⟨46, 2⟩⟩
  | .preC => ⟨⟨25, 2⟩⟩

/-- A row of (25), p. 23: the input probability Goldvarb X fits to a variety. -/
structure GoldvarbInput where
  /-- The input probability p₀. -/
  p0 : Decimal
  deriving DecidableEq, Repr

/-- The cells of (25), p. 23, by variety; fitted or simulated by a model; checked against the
page images. -/
def goldvarbInputs : Variety → GoldvarbInput
  | .tejano => ⟨⟨44, 2⟩⟩
  | .tejanoPrime => ⟨⟨44, 2⟩⟩

/-- A row of (25), p. 23: the factor weight Goldvarb X fits to a following context in a variety,
with the observed and expected percentages of deletion. -/
structure GoldvarbFactor where
  /-- The factor weight p₁. -/
  factorWeight : Decimal
  /-- The observed percentage deleted. -/
  observed : ℕ
  /-- The expected percentage deleted. -/
  expected : Decimal
  deriving DecidableEq, Repr

/-- The cells of (25), p. 23, by variety and context; fitted or simulated by a model; checked
against the page images. -/
def goldvarbFactors : Variety → Context → GoldvarbFactor
  | .tejano, .preV => ⟨⟨30, 2⟩, 25, ⟨2503, 2⟩⟩
  | .tejano, .pause => ⟨⟨52, 2⟩, 46, ⟨4600, 2⟩⟩
  | .tejano, .preC => ⟨⟨68, 2⟩, 62, ⟨6197, 2⟩⟩
  | .tejanoPrime, .preV => ⟨⟨68, 2⟩, 62, ⟨6197, 2⟩⟩
  | .tejanoPrime, .pause => ⟨⟨52, 2⟩, 46, ⟨4600, 2⟩⟩
  | .tejanoPrime, .preC => ⟨⟨30, 2⟩, 25, ⟨2503, 2⟩⟩

/-- A row of (32), p. 29: the probability of deletion of a word before a following context in the
learning data and in the learned lexically indexed Noisy HG grammar. -/
structure IndexedRate where
  /-- The probability of deletion in the learning data. -/
  learningData : Decimal
  /-- The probability of deletion in the learned grammar. -/
  learned : Decimal
  deriving DecidableEq, Repr

/-- The cells of (32), p. 29, by lexeme and context; fitted or simulated by a model; checked
against the page images. -/
def indexedRates : Lexeme → Context → IndexedRate
  | .feast, .preV => ⟨⟨40, 2⟩, ⟨40, 2⟩⟩
  | .feast, .pause => ⟨⟨20, 2⟩, ⟨20, 2⟩⟩
  | .feast, .preC => ⟨⟨60, 2⟩, ⟨59, 2⟩⟩
  | .most, .preV => ⟨⟨50, 2⟩, ⟨50, 2⟩⟩
  | .most, .pause => ⟨⟨30, 2⟩, ⟨30, 2⟩⟩
  | .most, .preC => ⟨⟨70, 2⟩, ⟨70, 2⟩⟩

end CoetzeePater2011
