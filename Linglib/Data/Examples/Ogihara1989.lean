module

public import Linglib.Data.Examples.Schema

/-!
# `Ogihara1989` — typed example data

Auto-generated from `Linglib/Data/Examples/Ogihara1989.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Ogihara1989.Examples`.
-/

@[expose] public section

namespace Ogihara1989.Examples

def ex_1_46a : Datum :=
  { id := "ogihara1989_1_46a"
    source := ⟨"partee-1973", ""⟩
    reportedIn := some ⟨"ogihara-1989", "ch. 1, (46a)"⟩
    method := some .elicitation
    language := "stan1293"
    primaryText := "I didn't turn off the stove."
    glossedTokens := []
    context := "Uttered when the speaker is driving down the freeway."
    judgment := .acceptable
    alternatives := []
    readings := [("no past time at which I turn off the stove", .unacceptable), ("some past time at which I do not turn off the stove", .unacceptable), ("no subinterval of the contextually salient past interval at which I turn off the stove", .acceptable)]
    paperFeatures := [("use", "deictic")] }

def ex_1_47 : Datum :=
  { id := "ogihara1989_1_47"
    source := ⟨"partee-1973", ""⟩
    reportedIn := some ⟨"ogihara-1989", "ch. 1, (47)"⟩
    method := some .elicitation
    language := "stan1293"
    primaryText := "Sheila had a party last Friday, and Sam got drunk."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("Sam got drunk at the time of Sheila's party", .acceptable)]
    paperFeatures := [("use", "anaphoric")] }

def ex_1_57 : Datum :=
  { id := "ogihara1989_1_57"
    source := ⟨"ogihara-1989", "ch. 1, (57)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "Bill: Did you see Mary? I have to talk to her. John: Yes, I saw her, but I don't know where she is now. Bill: What time did you see her? John: Sometime this morning. I don't remember exactly when."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("John saw Mary at some time within the contextually relevant interval", .acceptable), ("John saw Mary at some past time", .unacceptable)]
    paperFeatures := [("restriction", "contextual")] }

def ex_2_1a : Datum :=
  { id := "ogihara1989_2_1a"
    source := ⟨"ogihara-1989", "ch. 2, (1a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John said that Mary was ill."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("shifted", .acceptable), ("simultaneous", .acceptable)]
    paperFeatures := [] }

def ex_2_2a : Datum :=
  { id := "ogihara1989_2_2a"
    source := ⟨"ogihara-1989", "ch. 2, (2a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-wa Mary-ga byookidat-ta to it-ta."
    glossedTokens := [("John-wa", "John-TOP"), ("Mary-ga", "Mary-NOM"), ("byookidat-ta", "be.ill-PST"), ("to", "COMP"), ("it-ta", "say-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("shifted", .acceptable), ("simultaneous", .unacceptable)]
    paperFeatures := [] }

def ex_2_2b : Datum :=
  { id := "ogihara1989_2_2b"
    source := ⟨"ogihara-1989", "ch. 2, (2b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-wa Mary-ga byookid-a to it-ta."
    glossedTokens := [("John-wa", "John-TOP"), ("Mary-ga", "Mary-NOM"), ("byookid-a", "be.ill-PRES"), ("to", "COMP"), ("it-ta", "say-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable), ("shifted", .unacceptable)]
    paperFeatures := [] }

def ex_2_25a : Datum :=
  { id := "ogihara1989_2_25a"
    source := ⟨"ogihara-1989", "ch. 2, (25a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John said that Mary is in Austin."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .unacceptable)]
    paperFeatures := [] }

def ex_2_25b : Datum :=
  { id := "ogihara1989_2_25b"
    source := ⟨"ogihara-1989", "ch. 2, (25b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John said that Mary was in Austin."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable)]
    paperFeatures := [] }

def ex_2_25c : Datum :=
  { id := "ogihara1989_2_25c"
    source := ⟨"ogihara-1989", "ch. 2, (25c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John will say that Mary is in Austin."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable)]
    paperFeatures := [] }

def ex_2_27 : Datum :=
  { id := "ogihara1989_2_27"
    source := ⟨"ogihara-1989", "ch. 2, (27)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John saw a man who was laughing."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("shifted", .acceptable), ("simultaneous", .acceptable), ("subsequent", .acceptable)]
    paperFeatures := [] }

def ex_2_28 : Datum :=
  { id := "ogihara1989_2_28"
    source := ⟨"ogihara-1989", "ch. 2, (28)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John said that Mary was sick."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("shifted", .acceptable), ("simultaneous", .acceptable), ("subsequent", .unacceptable)]
    paperFeatures := [] }

def ex_2_33a : Datum :=
  { id := "ogihara1989_2_33a"
    source := ⟨"ogihara-1989", "ch. 2, (33a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "Two years ago today, John met a man who would become his great supporter."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("before the speech time", .acceptable)]
    paperFeatures := [] }

def ex_2_33b : Datum :=
  { id := "ogihara1989_2_33b"
    source := ⟨"ogihara-1989", "ch. 2, (33b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "Two years ago today, John met a man who will become his great supporter."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("before the speech time", .unacceptable), ("after the speech time", .acceptable)]
    paperFeatures := [] }

def ex_2_34 : Datum :=
  { id := "ogihara1989_2_34"
    source := ⟨"ogihara-1989", "ch. 2, (34)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "At the airport, John will meet a man who is holding a copy of L&P in his hand."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable)]
    paperFeatures := [] }

def ex_2_37 : Datum :=
  { id := "ogihara1989_2_37"
    source := ⟨"ogihara-1989", "ch. 2, (37)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John said that he would buy a fish that was still alive."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable), ("after the speech time", .acceptable)]
    paperFeatures := [] }

def ex_2_47a : Datum :=
  { id := "ogihara1989_2_47a"
    source := ⟨"ogihara-1989", "ch. 2, (47a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-wa warat-te ir-u otoko ni at-ta."
    glossedTokens := [("John-wa", "John-TOP"), ("warat-te", "laugh-TE"), ("ir-u", "PROG-PRES"), ("otoko", "man"), ("ni", "DAT"), ("at-ta", "see-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable), ("subsequent", .acceptable), ("shifted", .unacceptable)]
    paperFeatures := [] }

def ex_2_47b : Datum :=
  { id := "ogihara1989_2_47b"
    source := ⟨"ogihara-1989", "ch. 2, (47b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-wa warat-te ir-ta otoko ni at-ta."
    glossedTokens := [("John-wa", "John-TOP"), ("warat-te", "laugh-TE"), ("ir-ta", "PROG-PST"), ("otoko", "man"), ("ni", "DAT"), ("at-ta", "see-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("shifted", .acceptable), ("subsequent", .acceptable)]
    paperFeatures := [] }

def ex_2_59 : Datum :=
  { id := "ogihara1989_2_59"
    source := ⟨"ogihara-1989", "ch. 2, (59)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John will have claimed that he was sick."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable)]
    paperFeatures := [] }

def ex_2_60b : Datum :=
  { id := "ogihara1989_2_60b"
    source := ⟨"ogihara-1989", "ch. 2, (60b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John's earlier claim that Mary would win the prize is well-known."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_2_61 : Datum :=
  { id := "ogihara1989_2_61"
    source := ⟨"ogihara-1989", "ch. 2, (61)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "Everybody is amused by John's current claim that Mary would win the prize."
    glossedTokens := []
    context := "On the intended reading, the winning follows the speech time."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_2_70 : Datum :=
  { id := "ogihara1989_2_70"
    source := ⟨"ogihara-1989", "ch. 2, (70)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John met a man who would buy a fish which was still alive."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .unacceptable)]
    paperFeatures := [] }

def ex_2_97 : Datum :=
  { id := "ogihara1989_2_97"
    source := ⟨"ogihara-1989", "ch. 2, (97)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I told Bill that you would say that you only had three magic tricks to do, but it looks as if you have brought enough equipment to do six or seven."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable)]
    paperFeatures := [] }

def ex_2_103 : Datum :=
  { id := "ogihara1989_2_103"
    source := ⟨"ogihara-1989", "ch. 2, (103)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "I told Bill that you will say that you only had three magic tricks to do."
    glossedTokens := []
    context := "On the reading on which your having is simultaneous with your saying."
    judgment := .unacceptable
    alternatives := []
    readings := [("simultaneous", .unacceptable)]
    paperFeatures := [] }

def ex_2_104 : Datum :=
  { id := "ogihara1989_2_104"
    source := ⟨"ogihara-1989", "ch. 2, (104)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John promised to say that he did not know anything about the crime."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable)]
    paperFeatures := [] }

def ex_2_105 : Datum :=
  { id := "ogihara1989_2_105"
    source := ⟨"ogihara-1989", "ch. 2, (105)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John will promise to say that he did not know anything about the crime."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .unacceptable)]
    paperFeatures := [] }

def ex_2_125 : Datum :=
  { id := "ogihara1989_2_125"
    source := ⟨"ogihara-1989", "ch. 2, (125)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John said that Mary would come to Austin."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("after the speech time", .acceptable)]
    paperFeatures := [] }

def ex_2_139a : Datum :=
  { id := "ogihara1989_2_139a"
    source := ⟨"ogihara-1989", "ch. 2, (139a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John thought that Bill will claim that he did not know anything about the crime."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .unacceptable), ("shifted", .acceptable)]
    paperFeatures := [] }

def ex_2_139b : Datum :=
  { id := "ogihara1989_2_139b"
    source := ⟨"ogihara-1989", "ch. 2, (139b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John thought that Bill would claim that he did not know anything about the crime."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable)]
    paperFeatures := [] }

def ex_2_139c : Datum :=
  { id := "ogihara1989_2_139c"
    source := ⟨"ogihara-1989", "ch. 2, (139c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John asked Bill to claim that he did not know anything about the crime."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable)]
    paperFeatures := [] }

def ex_4_17d : Datum :=
  { id := "ogihara1989_4_17d"
    source := ⟨"ogihara-1989", "ch. 4, (17d)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John said that Mary is in the room."
    glossedTokens := []
    context := "At 10 A.M. John and Bill are peeping into a room where Sue is. John, near-sighted, says Mary is in the room. Bill denies it. One minute later Sue is still in the room and Bill reports this to Kent, adding: But that's not true. The one that is in the room is Sue."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "true")] }

def ex_4_24_Case_1 : Datum :=
  { id := "ogihara1989_4_24_Case_1"
    source := ⟨"ogihara-1989", "ch. 4, (24) Case 1"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John said in June that Mary is pregnant."
    glossedTokens := []
    context := "On June 20th John says Mary is pregnant, and she is. On December 20th Bill verifies that she is still pregnant."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_4_24_Case_2 : Datum :=
  { id := "ogihara1989_4_24_Case_2"
    source := ⟨"ogihara-1989", "ch. 4, (24) Case 2"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John said in June that Mary is pregnant."
    glossedTokens := []
    context := "On June 20th John says Mary is pregnant, and she is. On December 20th Bill learns that she has had a miscarriage."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_4_27d : Datum :=
  { id := "ogihara1989_4_27d"
    source := ⟨"ogihara-1989", "ch. 4, (27d)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John said that Mary is in the room."
    glossedTokens := []
    context := "As in (17), except that Sue leaves the room before Kent joins them."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_4_28 : Datum :=
  { id := "ogihara1989_4_28"
    source := ⟨"ogihara-1989", "ch. 4, (28)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John said that Mary is in the room. Yeah, he was right! She is in there now."
    glossedTokens := []
    context := "As in (27), except that Mary comes in just before Sue leaves."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_4_34d : Datum :=
  { id := "ogihara1989_4_34d"
    source := ⟨"ogihara-1989", "ch. 4, (34d)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John said that Mary is in the room."
    glossedTokens := []
    context := "As in (17), except that Bill convinces John that it is Sue. One minute later Sue is still in the room."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_4_35 : Datum :=
  { id := "ogihara1989_4_35"
    source := ⟨"ogihara-1989", "ch. 4, (35)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John told me, before he died, that Mary is pregnant."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_4_43c : Datum :=
  { id := "ogihara1989_4_43c"
    source := ⟨"ogihara-1989", "ch. 4, (43c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "John said yesterday that Mary is standing in the room. But that's Sue, not Mary."
    glossedTokens := []
    context := "As in (27) on the first day. On the following day Sue, who went home for the night, is inside the room again."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_1_46a, ex_1_47, ex_1_57, ex_2_1a, ex_2_2a, ex_2_2b, ex_2_25a, ex_2_25b, ex_2_25c, ex_2_27, ex_2_28, ex_2_33a, ex_2_33b, ex_2_34, ex_2_37, ex_2_47a, ex_2_47b, ex_2_59, ex_2_60b, ex_2_61, ex_2_70, ex_2_97, ex_2_103, ex_2_104, ex_2_105, ex_2_125, ex_2_139a, ex_2_139b, ex_2_139c, ex_4_17d, ex_4_24_Case_1, ex_4_24_Case_2, ex_4_27d, ex_4_28, ex_4_34d, ex_4_35, ex_4_43c]

end Ogihara1989.Examples
