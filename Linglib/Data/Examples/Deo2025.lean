module

public import Linglib.Data.Examples.Schema

/-!
# `Deo2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Deo2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Deo2025.Examples`.
-/

@[expose] public section

namespace Deo2025.Examples

def ex_1 : Datum :=
  { id := "deo2025_1"
    source := ⟨"deo-2025-bara", "(1)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "rəst-e kʰup nisərɖ-e ʣʰa-le ahe-t bərə"
    glossedTokens := [("rəst-e", "road.M-PL.NOM"), ("kʰup", "very"), ("nisərɖ-e", "slippery-M.PL.NOM"), ("ʣʰa-le", "become-PERF.M.PL"), ("ahe-t", "be.PRES-3.PL"), ("bərə", "BARA")]
    glossedWords := [⟨[['r', 'ə', 's', 't'], ['e']], [['r', 'o', 'a', 'd', '.', 'M'], ['P', 'L', '.', 'N', 'O', 'M']]⟩, ⟨[['k', 'ʰ', 'u', 'p']], [['v', 'e', 'r', 'y']]⟩, ⟨[['n', 'i', 's', 'ə', 'r', 'ɖ'], ['e']], [['s', 'l', 'i', 'p', 'p', 'e', 'r', 'y'], ['M', '.', 'P', 'L', '.', 'N', 'O', 'M']]⟩, ⟨[['ʣ', 'ʰ', 'a'], ['l', 'e']], [['b', 'e', 'c', 'o', 'm', 'e'], ['P', 'E', 'R', 'F', '.', 'M', '.', 'P', 'L']]⟩, ⟨[['a', 'h', 'e'], ['t']], [['b', 'e', '.', 'P', 'R', 'E', 'S'], ['3', '.', 'P', 'L']]⟩, ⟨[['b', 'ə', 'r', 'ə']], [['B', 'A', 'R', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Anu is going to Mumbai and says to Bilal: I think it will be faster to drive. Bilal: Are you sure? There have been heavy rains..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "declarative"), ("act", "warning")] }

def ex_2 : Datum :=
  { id := "deo2025_2"
    source := ⟨"deo-2025-bara", "(2)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "tu mumbəi=la udya ʣa bərə"
    glossedTokens := [("tu", "you.NOM"), ("mumbəi=la", "Bombay=DAT"), ("udya", "tomorrow"), ("ʣa", "go.IMP"), ("bərə", "BARA")]
    glossedWords := [⟨[['t', 'u']], [['y', 'o', 'u', '.', 'N', 'O', 'M']]⟩, ⟨[['m', 'u', 'm', 'b', 'ə', 'i'], ['l', 'a']], [['B', 'o', 'm', 'b', 'a', 'y'], ['D', 'A', 'T']]⟩, ⟨[['u', 'd', 'y', 'a']], [['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w']]⟩, ⟨[['ʣ', 'a']], [['g', 'o', '.', 'I', 'M', 'P']]⟩, ⟨[['b', 'ə', 'r', 'ə']], [['B', 'A', 'R', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Same as (1). Bilal: I absolutely don't want you to be driving in this weather..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "command")] }

def ex_3 : Datum :=
  { id := "deo2025_3"
    source := ⟨"deo-2025-bara", "(3)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "tu maʤʰ-i ʦavi kuʈʰe ʈʰev-li-s bərə"
    glossedTokens := [("tu", "you.ERG"), ("maʤʰ-i", "my-F.SG.NOM"), ("ʦavi", "key.F.SG.NOM"), ("kuʈʰe", "where"), ("ʈʰev-li-s", "keep-PERF.F.SG-2.SG"), ("bərə", "BARA")]
    glossedWords := [⟨[['t', 'u']], [['y', 'o', 'u', '.', 'E', 'R', 'G']]⟩, ⟨[['m', 'a', 'ʤ', 'ʰ'], ['i']], [['m', 'y'], ['F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['ʦ', 'a', 'v', 'i']], [['k', 'e', 'y', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['k', 'u', 'ʈ', 'ʰ', 'e']], [['w', 'h', 'e', 'r', 'e']]⟩, ⟨[['ʈ', 'ʰ', 'e', 'v'], ['l', 'i'], ['s']], [['k', 'e', 'e', 'p'], ['P', 'E', 'R', 'F', '.', 'F', '.', 'S', 'G'], ['2', '.', 'S', 'G']]⟩, ⟨[['b', 'ə', 'r', 'ə']], [['B', 'A', 'R', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Anu is annoyed because Bilal has hidden her bike key and she needs to get to work urgently. Anu: This is ridiculous..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "constituent"), ("act", "question")] }

def ex_4 : Datum :=
  { id := "deo2025_4"
    source := ⟨"deo-2025-bara", "(4)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "mi ata ɔfis=la ʣa-te ahe bərə"
    glossedTokens := [("mi", "I.NOM"), ("ata", "now"), ("ɔfis=la", "office=DAT"), ("ʣa-te", "go-IMPF.F.SG"), ("ahe", "be.PRES.1.SG"), ("bərə", "BARA")]
    glossedWords := [⟨[['m', 'i']], [['I', '.', 'N', 'O', 'M']]⟩, ⟨[['a', 't', 'a']], [['n', 'o', 'w']]⟩, ⟨[['ɔ', 'f', 'i', 's'], ['l', 'a']], [['o', 'f', 'f', 'i', 'c', 'e'], ['D', 'A', 'T']]⟩, ⟨[['ʣ', 'a'], ['t', 'e']], [['g', 'o'], ['I', 'M', 'P', 'F', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['a', 'h', 'e']], [['b', 'e', '.', 'P', 'R', 'E', 'S', '.', '1', '.', 'S', 'G']]⟩, ⟨[['b', 'ə', 'r', 'ə']], [['B', 'A', 'R', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Anu needs Bilal to stay at home because the plumber will be coming and someone needs to be in the house to meet him. Anu:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "declarative"), ("act", "informing")] }

def ex_5a : Datum :=
  { id := "deo2025_5a"
    source := ⟨"deo-2025-bara", "(5a)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "aʣ kʰup paus pəɖ-to ahe bərə"
    glossedTokens := [("aʣ", "today"), ("kʰup", "much"), ("paus", "rain.M.SG.NOM"), ("pəɖ-to", "fall-IMPF.M.SG"), ("ahe", "be.PRES.3.SG"), ("bərə", "BARA")]
    glossedWords := [⟨[['a', 'ʣ']], [['t', 'o', 'd', 'a', 'y']]⟩, ⟨[['k', 'ʰ', 'u', 'p']], [['m', 'u', 'c', 'h']]⟩, ⟨[['p', 'a', 'u', 's']], [['r', 'a', 'i', 'n', '.', 'M', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['p', 'ə', 'ɖ'], ['t', 'o']], [['f', 'a', 'l', 'l'], ['I', 'M', 'P', 'F', '.', 'M', '.', 'S', 'G']]⟩, ⟨[['a', 'h', 'e']], [['b', 'e', '.', 'P', 'R', 'E', 'S', '.', '3', '.', 'S', 'G']]⟩, ⟨[['b', 'ə', 'r', 'ə']], [['B', 'A', 'R', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Anu is planning to go to Mumbai today by car. It is raining heavily along the route, impacting road conditions, but the weather will significantly improve tomorrow, making the drive much safer. Bilal says:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "declarative"), ("act", "warning")] }

def ex_5b : Datum :=
  { id := "deo2025_5b"
    source := ⟨"deo-2025-bara", "(5b)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "udya ʦaŋgl-ə unʰ pəɖ-el bərə"
    glossedTokens := [("udya", "tomorrow"), ("ʦaŋgl-ə", "good-N.SG.NOM"), ("unʰ", "sunshine-N.SG.NOM"), ("pəɖ-el", "fall-FUT.3.SG"), ("bərə", "BARA")]
    glossedWords := [⟨[['u', 'd', 'y', 'a']], [['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w']]⟩, ⟨[['ʦ', 'a', 'ŋ', 'g', 'l'], ['ə']], [['g', 'o', 'o', 'd'], ['N', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['u', 'n', 'ʰ']], [['s', 'u', 'n', 's', 'h', 'i', 'n', 'e'], ['N', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['p', 'ə', 'ɖ'], ['e', 'l']], [['f', 'a', 'l', 'l'], ['F', 'U', 'T', '.', '3', '.', 'S', 'G']]⟩, ⟨[['b', 'ə', 'r', 'ə']], [['B', 'A', 'R', 'A']]⟩]
    lgrConformance := some .wordAligned
    context := "Anu is planning to go to Mumbai today by car. It is raining heavily along the route, impacting road conditions, but the weather will significantly improve tomorrow, making the drive much safer. Bilal says:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "declarative"), ("act", "warning"), ("infelicity", "precondition")] }

def ex_6 : Datum :=
  { id := "deo2025_6"
    source := ⟨"deo-2025-bara", "(6)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "he əuʃədʰ tum-ʦ-a tap kəmi kər-el bərə"
    glossedTokens := [("he", "this.N.SG.NOM"), ("əuʃədʰ", "medicine.N.SG.NOM"), ("tum-ʦ-a", "you-GEN-M.SG.NOM"), ("tap", "fever.M.SG.NOM"), ("kəmi", "less"), ("kər-el", "do-FUT.3.SG"), ("bərə", "BARA")]
    glossedWords := [⟨[['h', 'e']], [['t', 'h', 'i', 's', '.', 'N', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['ə', 'u', 'ʃ', 'ə', 'd', 'ʰ']], [['m', 'e', 'd', 'i', 'c', 'i', 'n', 'e', '.', 'N', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['t', 'u', 'm'], ['ʦ'], ['a']], [['y', 'o', 'u'], ['G', 'E', 'N'], ['M', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['t', 'a', 'p']], [['f', 'e', 'v', 'e', 'r', '.', 'M', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['k', 'ə', 'm', 'i']], [['l', 'e', 's', 's']]⟩, ⟨[['k', 'ə', 'r'], ['e', 'l']], [['d', 'o'], ['F', 'U', 'T', '.', '3', '.', 'S', 'G']]⟩, ⟨[['b', 'ə', 'r', 'ə']], [['B', 'A', 'R', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Anu has been sick and goes to the doctor, who diagnoses a viral infection. Doctor: Don't worry, the infection will run its course. Meanwhile..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "declarative"), ("act", "advice")] }

def ex_7ctx1 : Datum :=
  { id := "deo2025_7ctx1"
    source := ⟨"deo-2025-bara", "(7), context 1"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "Niśa tiʧ-ya bəhiɳi=la aɳ-te ahe bərə"
    glossedTokens := [("Niśa", "Niśa.NOM"), ("tiʧ-ya", "her.GEN-OBL"), ("bəhiɳi=la", "sister.OBL=ACC"), ("aɳ-te", "bring-IMPF.F.SG"), ("ahe", "PRES.3.SG"), ("bərə", "BARA")]
    glossedWords := [⟨[['N', 'i', 'ś', 'a']], [['N', 'i', 'ś', 'a', '.', 'N', 'O', 'M']]⟩, ⟨[['t', 'i', 'ʧ'], ['y', 'a']], [['h', 'e', 'r', '.', 'G', 'E', 'N'], ['O', 'B', 'L']]⟩, ⟨[['b', 'ə', 'h', 'i', 'ɳ', 'i'], ['l', 'a']], [['s', 'i', 's', 't', 'e', 'r', '.', 'O', 'B', 'L'], ['A', 'C', 'C']]⟩, ⟨[['a', 'ɳ'], ['t', 'e']], [['b', 'r', 'i', 'n', 'g'], ['I', 'M', 'P', 'F', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['a', 'h', 'e']], [['P', 'R', 'E', 'S', '.', '3', '.', 'S', 'G']]⟩, ⟨[['b', 'ə', 'r', 'ə']], [['B', 'A', 'R', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Anu and Bilal are hosting three friends for dinner and they both have been told that one of them will also bring her sister along. Bilal is setting the table. Bilal: Let's see, how many place settings do we need?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "declarative"), ("act", "reminder"), ("infelicity", "alignment")] }

def ex_7ctx2 : Datum :=
  { id := "deo2025_7ctx2"
    source := ⟨"deo-2025-bara", "(7), context 2"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "Niśa tiʧ-ya bəhiɳi=la aɳ-te ahe bərə"
    glossedTokens := [("Niśa", "Niśa.NOM"), ("tiʧ-ya", "her.GEN-OBL"), ("bəhiɳi=la", "sister.OBL=ACC"), ("aɳ-te", "bring-IMPF.F.SG"), ("ahe", "PRES.3.SG"), ("bərə", "BARA")]
    glossedWords := [⟨[['N', 'i', 'ś', 'a']], [['N', 'i', 'ś', 'a', '.', 'N', 'O', 'M']]⟩, ⟨[['t', 'i', 'ʧ'], ['y', 'a']], [['h', 'e', 'r', '.', 'G', 'E', 'N'], ['O', 'B', 'L']]⟩, ⟨[['b', 'ə', 'h', 'i', 'ɳ', 'i'], ['l', 'a']], [['s', 'i', 's', 't', 'e', 'r', '.', 'O', 'B', 'L'], ['A', 'C', 'C']]⟩, ⟨[['a', 'ɳ'], ['t', 'e']], [['b', 'r', 'i', 'n', 'g'], ['I', 'M', 'P', 'F', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['a', 'h', 'e']], [['P', 'R', 'E', 'S', '.', '3', '.', 'S', 'G']]⟩, ⟨[['b', 'ə', 'r', 'ə']], [['B', 'A', 'R', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Anu and Bilal are hosting three friends for dinner and they both have been told that one of them will also bring her sister along. It's almost time for the guests and Bilal has laid the table with settings for only five people. Anu: We need six place settings..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "declarative"), ("act", "reminder")] }

def ex_8 : Datum :=
  { id := "deo2025_8"
    source := ⟨"deo-2025-bara", "(8)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "tu=la dəmya-ʦa tras ahe bərə"
    glossedTokens := [("tu=la", "you.OBL=DAT"), ("dəmya-ʦa", "asthma.OBL-GEN.M.SG.NOM"), ("tras", "suffering.M.SG.NOM"), ("ahe", "be.PRES.3.SG"), ("bərə", "BARA")]
    glossedWords := [⟨[['t', 'u'], ['l', 'a']], [['y', 'o', 'u', '.', 'O', 'B', 'L'], ['D', 'A', 'T']]⟩, ⟨[['d', 'ə', 'm', 'y', 'a'], ['ʦ', 'a']], [['a', 's', 't', 'h', 'm', 'a', '.', 'O', 'B', 'L'], ['G', 'E', 'N', '.', 'M', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['t', 'r', 'a', 's']], [['s', 'u', 'f', 'f', 'e', 'r', 'i', 'n', 'g', '.', 'M', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['a', 'h', 'e']], [['b', 'e', '.', 'P', 'R', 'E', 'S', '.', '3', '.', 'S', 'G']]⟩, ⟨[['b', 'ə', 'r', 'ə']], [['B', 'A', 'R', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Anu has been offered a new job assignment, which requires her to move to a hilly, high-altitude location with steep roads for a year. She is excited about it and is considering it seriously. Bilal prefers that she not make the move for health reasons. Bilal: This could be really difficult for you health-wise..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "declarative"), ("act", "warning")] }

def ex_9 : Datum :=
  { id := "deo2025_9"
    source := ⟨"deo-2025-bara", "(9)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "ho mi ti=la gʰe-un ye-te bərə"
    glossedTokens := [("ho", "yes"), ("mi", "I.NOM"), ("ti=la", "her.OBL=ACC"), ("gʰe-un", "bring-GER"), ("ye-te", "come-IMPF.F.SG"), ("bərə", "BARA")]
    glossedWords := [⟨[['h', 'o']], [['y', 'e', 's']]⟩, ⟨[['m', 'i']], [['I', '.', 'N', 'O', 'M']]⟩, ⟨[['t', 'i'], ['l', 'a']], [['h', 'e', 'r', '.', 'O', 'B', 'L'], ['A', 'C', 'C']]⟩, ⟨[['g', 'ʰ', 'e'], ['u', 'n']], [['b', 'r', 'i', 'n', 'g'], ['G', 'E', 'R']]⟩, ⟨[['y', 'e'], ['t', 'e']], [['c', 'o', 'm', 'e'], ['I', 'M', 'P', 'F', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['b', 'ə', 'r', 'ə']], [['B', 'A', 'R', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Anu and Bilal take turns picking up their daughter Deepa from after-school. It is Bilal's turn today. Bilal tells Anu that he is really busy that day and asks if Anu can pick Deepa up instead. Anu: I understand..."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "declarative"), ("act", "commissive"), ("infelicity", "source")] }

def ex_10a : Datum :=
  { id := "deo2025_10a"
    source := ⟨"deo-2025-bara", "(10a)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "krupəya tumʰi mə=la həʣar rupye dy-a bərə"
    glossedTokens := [("krupəya", "please"), ("tumʰi", "you.PL.HON"), ("mə=la", "I.OBL=DAT"), ("həʣar", "thousand"), ("rupye", "rupees"), ("dy-a", "give.IMP-PL"), ("bərə", "BARA")]
    glossedWords := [⟨[['k', 'r', 'u', 'p', 'ə', 'y', 'a']], [['p', 'l', 'e', 'a', 's', 'e']]⟩, ⟨[['t', 'u', 'm', 'ʰ', 'i']], [['y', 'o', 'u', '.', 'P', 'L', '.', 'H', 'O', 'N']]⟩, ⟨[['m', 'ə'], ['l', 'a']], [['I', '.', 'O', 'B', 'L'], ['D', 'A', 'T']]⟩, ⟨[['h', 'ə', 'ʣ', 'a', 'r']], [['t', 'h', 'o', 'u', 's', 'a', 'n', 'd']]⟩, ⟨[['r', 'u', 'p', 'y', 'e']], [['r', 'u', 'p', 'e', 'e', 's']]⟩, ⟨[['d', 'y'], ['a']], [['g', 'i', 'v', 'e', '.', 'I', 'M', 'P'], ['P', 'L']]⟩, ⟨[['b', 'ə', 'r', 'ə']], [['B', 'A', 'R', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "request"), ("infelicity", "benefit")] }

def ex_10b : Datum :=
  { id := "deo2025_10b"
    source := ⟨"deo-2025-bara", "(10b)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "koɳi=tari mə=la vihir=it=un baher kaɖʰ-a bərə"
    glossedTokens := [("koɳi=tari", "someone=PRT"), ("mə=la", "I.OBL=ACC"), ("vihir=it=un", "well.OBL=IN=FROM"), ("baher", "out"), ("kaɖʰ-a", "bring.IMP-PL"), ("bərə", "BARA")]
    glossedWords := [⟨[['k', 'o', 'ɳ', 'i'], ['t', 'a', 'r', 'i']], [['s', 'o', 'm', 'e', 'o', 'n', 'e'], ['P', 'R', 'T']]⟩, ⟨[['m', 'ə'], ['l', 'a']], [['I', '.', 'O', 'B', 'L'], ['A', 'C', 'C']]⟩, ⟨[['v', 'i', 'h', 'i', 'r'], ['i', 't'], ['u', 'n']], [['w', 'e', 'l', 'l', '.', 'O', 'B', 'L'], ['I', 'N'], ['F', 'R', 'O', 'M']]⟩, ⟨[['b', 'a', 'h', 'e', 'r']], [['o', 'u', 't']]⟩, ⟨[['k', 'a', 'ɖ', 'ʰ'], ['a']], [['b', 'r', 'i', 'n', 'g', '.', 'I', 'M', 'P'], ['P', 'L']]⟩, ⟨[['b', 'ə', 'r', 'ə']], [['B', 'A', 'R', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "plea"), ("infelicity", "benefit")] }

def ex_11a : Datum :=
  { id := "deo2025_11a"
    source := ⟨"deo-2025-bara", "(11a)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "tu hi rəbəɖi kʰa bərə"
    glossedTokens := [("tu", "you.NOM"), ("hi", "this.F.SG.NOM"), ("rəbəɖi", "rabadi.F.SG.NOM"), ("kʰa", "eat.IMP.SG"), ("bərə", "BARA")]
    glossedWords := [⟨[['t', 'u']], [['y', 'o', 'u', '.', 'N', 'O', 'M']]⟩, ⟨[['h', 'i']], [['t', 'h', 'i', 's', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['r', 'ə', 'b', 'ə', 'ɖ', 'i']], [['r', 'a', 'b', 'a', 'd', 'i', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['k', 'ʰ', 'a']], [['e', 'a', 't', '.', 'I', 'M', 'P', '.', 'S', 'G']]⟩, ⟨[['b', 'ə', 'r', 'ə']], [['B', 'A', 'R', 'A']]⟩]
    lgrConformance := some .wordAligned
    context := "Anu has made a dessert and is offering it to Bilal to taste. She says:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "offer"), ("infelicity", "deference")] }

def ex_11b : Datum :=
  { id := "deo2025_11b"
    source := ⟨"deo-2025-bara", "(11b)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "ho ʣa aɳi məʤa kər-a bərə"
    glossedTokens := [("ho", "sure"), ("ʣa", "go.IMP.PL"), ("aɳi", "and"), ("məʤa", "fun"), ("kər-a", "do.IMP-PL"), ("bərə", "BARA")]
    glossedWords := [⟨[['h', 'o']], [['s', 'u', 'r', 'e']]⟩, ⟨[['ʣ', 'a']], [['g', 'o', '.', 'I', 'M', 'P', '.', 'P', 'L']]⟩, ⟨[['a', 'ɳ', 'i']], [['a', 'n', 'd']]⟩, ⟨[['m', 'ə', 'ʤ', 'a']], [['f', 'u', 'n']]⟩, ⟨[['k', 'ə', 'r'], ['a']], [['d', 'o', '.', 'I', 'M', 'P'], ['P', 'L']]⟩, ⟨[['b', 'ə', 'r', 'ə']], [['B', 'A', 'R', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Deepa and her friends are planning to go to the park and Deepa comes and asks her mother: Mom, can I go play in the park with my friends?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "permission"), ("infelicity", "source")] }

def ex_11c : Datum :=
  { id := "deo2025_11c"
    source := ⟨"deo-2025-bara", "(11c)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "ʈʰik ahe ʣa kʰeɭay-la bərə"
    glossedTokens := [("ʈʰik ahe", "alright"), ("ʣa", "go.IMP"), ("kʰeɭay-la", "play-INF"), ("bərə", "BARA")]
    glossedWords := [⟨[['ʈ', 'ʰ', 'i', 'k', ' ', 'a', 'h', 'e']], [['a', 'l', 'r', 'i', 'g', 'h', 't']]⟩, ⟨[['ʣ', 'a']], [['g', 'o', '.', 'I', 'M', 'P']]⟩, ⟨[['k', 'ʰ', 'e', 'ɭ', 'a', 'y'], ['l', 'a']], [['p', 'l', 'a', 'y'], ['I', 'N', 'F']]⟩, ⟨[['b', 'ə', 'r', 'ə']], [['B', 'A', 'R', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Anu has asked Deepa to finish her homework before going out to play. Deepa is badgering Anu because she wants to go play without finishing her homework. Anu gets exasperated and says:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "concession"), ("infelicity", "source")] }

def ex_11d : Datum :=
  { id := "deo2025_11d"
    source := ⟨"deo-2025-bara", "(11d)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "ʣa kʰəɖɖya=t bərə"
    glossedTokens := [("ʣa", "go.IMP"), ("kʰəɖɖya=t", "ditch.OBL=LOC"), ("bərə", "BARA")]
    glossedWords := [⟨[['ʣ', 'a']], [['g', 'o', '.', 'I', 'M', 'P']]⟩, ⟨[['k', 'ʰ', 'ə', 'ɖ', 'ɖ', 'y', 'a'], ['t']], [['d', 'i', 't', 'c', 'h', '.', 'O', 'B', 'L'], ['L', 'O', 'C']]⟩, ⟨[['b', 'ə', 'r', 'ə']], [['B', 'A', 'R', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    alternatives := [("ʣa məsəɳa=t bərə", .unacceptable)]
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "curse"), ("infelicity", "benefit")] }

def ex_12 : Datum :=
  { id := "deo2025_12"
    source := ⟨"deo-2025-bara", "(12)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "tu ata ləgeʦ ʣopay-la ʣa bərə"
    glossedTokens := [("tu", "you.NOM"), ("ata", "now"), ("ləgeʦ", "immediately"), ("ʣopay-la", "sleep-INF"), ("ʣa", "go.IMP"), ("bərə", "BARA")]
    glossedWords := [⟨[['t', 'u']], [['y', 'o', 'u', '.', 'N', 'O', 'M']]⟩, ⟨[['a', 't', 'a']], [['n', 'o', 'w']]⟩, ⟨[['l', 'ə', 'g', 'e', 'ʦ']], [['i', 'm', 'm', 'e', 'd', 'i', 'a', 't', 'e', 'l', 'y']]⟩, ⟨[['ʣ', 'o', 'p', 'a', 'y'], ['l', 'a']], [['s', 'l', 'e', 'e', 'p'], ['I', 'N', 'F']]⟩, ⟨[['ʣ', 'a']], [['g', 'o', '.', 'I', 'M', 'P']]⟩, ⟨[['b', 'ə', 'r', 'ə']], [['B', 'A', 'R', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Deepa has stayed up way past her bedtime playing a video game. Anu gets annoyed because Deepa has school tomorrow and needs to be up early. She has already told Deepa several times to go to bed. Anu: You are stretching my patience now..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "command")] }

def ex_13 : Datum :=
  { id := "deo2025_13"
    source := ⟨"deo-2025-bara", "(13)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "kəɖʰəi=mədʰye ətta=ʦ tel ʈaku nəko bərə"
    glossedTokens := [("kəɖʰəi=mədʰye", "pan.OBL=in"), ("ətta=ʦ", "now=EMPH"), ("tel", "oil.N.SG.NOM"), ("ʈaku", "pour.INF"), ("nəko", "NEG.IMP"), ("bərə", "BARA")]
    glossedWords := [⟨[['k', 'ə', 'ɖ', 'ʰ', 'ə', 'i'], ['m', 'ə', 'd', 'ʰ', 'y', 'e']], [['p', 'a', 'n', '.', 'O', 'B', 'L'], ['i', 'n']]⟩, ⟨[['ə', 't', 't', 'a'], ['ʦ']], [['n', 'o', 'w'], ['E', 'M', 'P', 'H']]⟩, ⟨[['t', 'e', 'l']], [['o', 'i', 'l', '.', 'N', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['ʈ', 'a', 'k', 'u']], [['p', 'o', 'u', 'r', '.', 'I', 'N', 'F']]⟩, ⟨[['n', 'ə', 'k', 'o']], [['N', 'E', 'G', '.', 'I', 'M', 'P']]⟩, ⟨[['b', 'ə', 'r', 'ə']], [['B', 'A', 'R', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Deepa is making dal for the first time with Anu's help and has let the pan get too hot on the stove. She is about to put in some oil to start sautéing the onions. Anu:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "warning")] }

def ex_14 : Datum :=
  { id := "deo2025_14"
    source := ⟨"deo-2025-bara", "(14)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "ata aʤi=la ek pətrə lihi bərə"
    glossedTokens := [("ata", "now"), ("aʤi=la", "grandma.OBL=DAT"), ("ek", "one.NOM"), ("pətrə", "note.N.SG.NOM"), ("lihi", "write.IMP"), ("bərə", "BARA")]
    glossedWords := [⟨[['a', 't', 'a']], [['n', 'o', 'w']]⟩, ⟨[['a', 'ʤ', 'i'], ['l', 'a']], [['g', 'r', 'a', 'n', 'd', 'm', 'a', '.', 'O', 'B', 'L'], ['D', 'A', 'T']]⟩, ⟨[['e', 'k']], [['o', 'n', 'e', '.', 'N', 'O', 'M']]⟩, ⟨[['p', 'ə', 't', 'r', 'ə']], [['n', 'o', 't', 'e', '.', 'N', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['l', 'i', 'h', 'i']], [['w', 'r', 'i', 't', 'e', '.', 'I', 'M', 'P']]⟩, ⟨[['b', 'ə', 'r', 'ə']], [['B', 'A', 'R', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Deepa got a lovely doll in the mail from Anu's mother and has been playing with it. Anu wants Deepa to thank her grandma before she forgets. Anu: Alright, you have played enough now..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "recommendation")] }

def ex_15ctx1 : Datum :=
  { id := "deo2025_15ctx1"
    source := ⟨"deo-2025-bara", "(15), context 1"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "məg aʣ tu gaɖi gʰe-un ʣa bərə"
    glossedTokens := [("məg", "then"), ("aʣ", "today"), ("tu", "you.NOM"), ("gaɖi", "car.F.SG.NOM"), ("gʰe-un", "take-GER"), ("ʣa", "go.IMP"), ("bərə", "BARA")]
    glossedWords := [⟨[['m', 'ə', 'g']], [['t', 'h', 'e', 'n']]⟩, ⟨[['a', 'ʣ']], [['t', 'o', 'd', 'a', 'y']]⟩, ⟨[['t', 'u']], [['y', 'o', 'u', '.', 'N', 'O', 'M']]⟩, ⟨[['g', 'a', 'ɖ', 'i']], [['c', 'a', 'r', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['g', 'ʰ', 'e'], ['u', 'n']], [['t', 'a', 'k', 'e'], ['G', 'E', 'R']]⟩, ⟨[['ʣ', 'a']], [['g', 'o', '.', 'I', 'M', 'P']]⟩, ⟨[['b', 'ə', 'r', 'ə']], [['B', 'A', 'R', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Bilal needs to be at a work meeting soon and he has missed the bus that he takes to work. Anu is the one who usually takes the car to work but Bilal would love to be able to drive to work today. Bilal tells Anu he missed the bus. Anu: Ok, so we need to figure out a solution..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "recommendation")] }

def ex_15ctx2 : Datum :=
  { id := "deo2025_15ctx2"
    source := ⟨"deo-2025-bara", "(15), context 2"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "məg aʣ tu gaɖi gʰe-un ʣa bərə"
    glossedTokens := [("məg", "then"), ("aʣ", "today"), ("tu", "you.NOM"), ("gaɖi", "car.F.SG.NOM"), ("gʰe-un", "take-GER"), ("ʣa", "go.IMP"), ("bərə", "BARA")]
    glossedWords := [⟨[['m', 'ə', 'g']], [['t', 'h', 'e', 'n']]⟩, ⟨[['a', 'ʣ']], [['t', 'o', 'd', 'a', 'y']]⟩, ⟨[['t', 'u']], [['y', 'o', 'u', '.', 'N', 'O', 'M']]⟩, ⟨[['g', 'a', 'ɖ', 'i']], [['c', 'a', 'r', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['g', 'ʰ', 'e'], ['u', 'n']], [['t', 'a', 'k', 'e'], ['G', 'E', 'R']]⟩, ⟨[['ʣ', 'a']], [['g', 'o', '.', 'I', 'M', 'P']]⟩, ⟨[['b', 'ə', 'r', 'ə']], [['B', 'A', 'R', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Bilal needs to be at a work meeting soon and he has missed the bus that he takes to work. Anu is the one who usually takes the car to work but Bilal would love to be able to drive to work today. Bilal tells Anu he missed the bus and adds: I would really like to drive to work today so I don't miss my meeting. Anu:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "recommendation"), ("infelicity", "source")] }

def ex_16 : Datum :=
  { id := "deo2025_16"
    source := ⟨"deo-2025-bara", "(16)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "ʧʰan tu ti=la gʰe-un ye bərə"
    glossedTokens := [("ʧʰan", "great"), ("tu", "you.NOM"), ("ti=la", "her.OBL=ACC"), ("gʰe-un", "bring-GER"), ("ye", "come.IMP"), ("bərə", "BARA")]
    glossedWords := [⟨[['ʧ', 'ʰ', 'a', 'n']], [['g', 'r', 'e', 'a', 't']]⟩, ⟨[['t', 'u']], [['y', 'o', 'u', '.', 'N', 'O', 'M']]⟩, ⟨[['t', 'i'], ['l', 'a']], [['h', 'e', 'r', '.', 'O', 'B', 'L'], ['A', 'C', 'C']]⟩, ⟨[['g', 'ʰ', 'e'], ['u', 'n']], [['b', 'r', 'i', 'n', 'g'], ['G', 'E', 'R']]⟩, ⟨[['y', 'e']], [['c', 'o', 'm', 'e', '.', 'I', 'M', 'P']]⟩, ⟨[['b', 'ə', 'r', 'ə']], [['B', 'A', 'R', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Anu and Bilal take turns picking up their daughter Deepa from after-school. It is Bilal's turn today. Bilal tells Anu that he is really busy that day and doesn't know whether he will make it to the school in time. Anu: No worries, I am working from home today. I will pick her up! Bilal:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "agreement"), ("infelicity", "source")] }

def ex_19a : Datum :=
  { id := "deo2025_19a"
    source := ⟨"deo-2025-bara", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Anu: Keep the discussion we had at this meeting confidential. Nina: Ok/Yes."
    glossedTokens := []
    context := "Anu and her secretary Nina, after a sensitive meeting with a small subset of Anu's team."
    judgment := .acceptable
    alternatives := [("Ok", .acceptable), ("Yes", .acceptable)]
    readings := []
    paperFeatures := [("construction", "responseParticle")] }

def ex_19b : Datum :=
  { id := "deo2025_19b"
    source := ⟨"deo-2025-bara", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nina: I will circulate the minutes among all the staff by tomorrow. Anu: No, keep the discussion we had at this meeting confidential. Nina: Ok/#Yes."
    glossedTokens := []
    context := "Anu and her secretary Nina, after a sensitive meeting with a small subset of Anu's team."
    judgment := .acceptable
    alternatives := [("Ok", .acceptable), ("Yes", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "responseParticle")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5a, ex_5b, ex_6, ex_7ctx1, ex_7ctx2, ex_8, ex_9, ex_10a, ex_10b, ex_11a, ex_11b, ex_11c, ex_11d, ex_12, ex_13, ex_14, ex_15ctx1, ex_15ctx2, ex_16, ex_19a, ex_19b]

end Deo2025.Examples
