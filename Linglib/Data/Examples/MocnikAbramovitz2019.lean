module

public import Linglib.Data.Examples.Schema

/-!
# `MocnikAbramovitz2019` — typed example data

Auto-generated from `Linglib/Data/Examples/MocnikAbramovitz2019.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace MocnikAbramovitz2019.Examples`.
-/

@[expose] public section

namespace MocnikAbramovitz2019.Examples

def ex2 : Datum :=
  { id := "mocnikabramovitz2019_ex2"
    source := ⟨"mocnik-abramovitz-2019", "(2)"⟩
    reportedIn := none
    language := "kory1246"
    primaryText := "meʎʎo kivəŋ, əno kumuqetəŋ"
    glossedTokens := [("meʎʎo", "Melljo"), ("kivəŋ", "ivək.3SG.PRS"), ("əno", "that"), ("kumuqetəŋ", "rain.3SG.PRS")]
    glossedWords := [⟨['m', 'e', 'ʎ', 'ʎ', 'o'], ['M', 'e', 'l', 'l', 'j', 'o'], [⟨['m', 'e', 'ʎ', 'ʎ', 'o'], ['M', 'e', 'l', 'l', 'j', 'o'], none⟩]⟩, ⟨['k', 'i', 'v', 'ə', 'ŋ'], ['i', 'v', 'ə', 'k', '.', '3', 'S', 'G', '.', 'P', 'R', 'S'], [⟨['k', 'i', 'v', 'ə', 'ŋ'], ['i', 'v', 'ə', 'k', '.', '3', 'S', 'G', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], [⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['k', 'u', 'm', 'u', 'q', 'e', 't', 'ə', 'ŋ'], ['r', 'a', 'i', 'n', '.', '3', 'S', 'G', '.', 'P', 'R', 'S'], [⟨['k', 'u', 'm', 'u', 'q', 'e', 't', 'ə', 'ŋ'], ['r', 'a', 'i', 'n', '.', '3', 'S', 'G', '.', 'P', 'R', 'S'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("meʎʎo kivəŋ, kumuqetəŋ", .acceptable)]
    readings := [("says", .acceptable), ("thinks", .acceptable), ("allows", .acceptable), ("hopes", .acceptable), ("fears", .acceptable), ("knows", .ungrammatical), ("imagines", .ungrammatical), ("wishes", .ungrammatical)]
    paperFeatures := [("section", "1")] }

def ex4 : Datum :=
  { id := "mocnikabramovitz2019_ex4"
    source := ⟨"mocnik-abramovitz-2019", "(4)"⟩
    reportedIn := none
    language := "kory1246"
    primaryText := "qoo. təkivəŋ əno kotavareɲjaŋəŋ jajak. qoo. təkivəŋ əno keluŋ umkək."
    glossedTokens := [("qoo", "dunno"), ("təkivəŋ", "ivək.1SG.PRS"), ("əno", "that"), ("kotavareɲjaŋəŋ", "make.jam.3SG.PRS"), ("jajak", "at.home"), ("qoo", "dunno"), ("təkivəŋ", "ivək.1SG.PRS"), ("əno", "that"), ("keluŋ", "pick.berries.3SG.PRS"), ("umkək", "in.forest")]
    glossedWords := [⟨['q', 'o', 'o'], ['d', 'u', 'n', 'n', 'o'], [⟨['q', 'o', 'o'], ['d', 'u', 'n', 'n', 'o'], none⟩]⟩, ⟨['t', 'ə', 'k', 'i', 'v', 'ə', 'ŋ'], ['i', 'v', 'ə', 'k', '.', '1', 'S', 'G', '.', 'P', 'R', 'S'], [⟨['t', 'ə', 'k', 'i', 'v', 'ə', 'ŋ'], ['i', 'v', 'ə', 'k', '.', '1', 'S', 'G', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], [⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['k', 'o', 't', 'a', 'v', 'a', 'r', 'e', 'ɲ', 'j', 'a', 'ŋ', 'ə', 'ŋ'], ['m', 'a', 'k', 'e', '.', 'j', 'a', 'm', '.', '3', 'S', 'G', '.', 'P', 'R', 'S'], [⟨['k', 'o', 't', 'a', 'v', 'a', 'r', 'e', 'ɲ', 'j', 'a', 'ŋ', 'ə', 'ŋ'], ['m', 'a', 'k', 'e', '.', 'j', 'a', 'm', '.', '3', 'S', 'G', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['j', 'a', 'j', 'a', 'k'], ['a', 't', '.', 'h', 'o', 'm', 'e'], [⟨['j', 'a', 'j', 'a', 'k'], ['a', 't', '.', 'h', 'o', 'm', 'e'], none⟩]⟩, ⟨['q', 'o', 'o'], ['d', 'u', 'n', 'n', 'o'], [⟨['q', 'o', 'o'], ['d', 'u', 'n', 'n', 'o'], none⟩]⟩, ⟨['t', 'ə', 'k', 'i', 'v', 'ə', 'ŋ'], ['i', 'v', 'ə', 'k', '.', '1', 'S', 'G', '.', 'P', 'R', 'S'], [⟨['t', 'ə', 'k', 'i', 'v', 'ə', 'ŋ'], ['i', 'v', 'ə', 'k', '.', '1', 'S', 'G', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], [⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['k', 'e', 'l', 'u', 'ŋ'], ['p', 'i', 'c', 'k', '.', 'b', 'e', 'r', 'r', 'i', 'e', 's', '.', '3', 'S', 'G', '.', 'P', 'R', 'S'], [⟨['k', 'e', 'l', 'u', 'ŋ'], ['p', 'i', 'c', 'k', '.', 'b', 'e', 'r', 'r', 'i', 'e', 's', '.', '3', 'S', 'G', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['u', 'm', 'k', 'ə', 'k'], ['i', 'n', '.', 'f', 'o', 'r', 'e', 's', 't'], [⟨['u', 'm', 'k', 'ə', 'k'], ['i', 'n', '.', 'f', 'o', 'r', 'e', 's', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Hewngyto is walking down the street. Melljo sees him and asks: 'Where is your wife? Is she making jam at home?' He replies with the first sentence. He continues walking. Qechghylqot sees him and asks: 'Where is your wife? Is she picking berries in the forest?' Hewngyto replies with the second."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2")] }

def ex5 : Datum :=
  { id := "mocnikabramovitz2019_ex5"
    source := ⟨"mocnik-abramovitz-2019", "(5)"⟩
    reportedIn := none
    language := "kory1246"
    primaryText := "ʔewŋəto kolmalavəŋ əno kumuqetəŋ, ʔam ʔopta kolmalavəŋ əno ujŋe emuqetke."
    glossedTokens := [("ʔewŋəto", "H."), ("kolmalavəŋ", "believe.3SG.PRS"), ("əno", "that"), ("kumuqetəŋ", "rain.PRS"), ("ʔam", "but"), ("ʔopta", "also"), ("kolmalavəŋ", "believe.3SG.PRS"), ("əno", "that"), ("ujŋe", "NEG"), ("emuqetke", "rain")]
    glossedWords := [⟨['ʔ', 'e', 'w', 'ŋ', 'ə', 't', 'o'], ['H', '.'], [⟨['ʔ', 'e', 'w', 'ŋ', 'ə', 't', 'o'], ['H', '.'], none⟩]⟩, ⟨['k', 'o', 'l', 'm', 'a', 'l', 'a', 'v', 'ə', 'ŋ'], ['b', 'e', 'l', 'i', 'e', 'v', 'e', '.', '3', 'S', 'G', '.', 'P', 'R', 'S'], [⟨['k', 'o', 'l', 'm', 'a', 'l', 'a', 'v', 'ə', 'ŋ'], ['b', 'e', 'l', 'i', 'e', 'v', 'e', '.', '3', 'S', 'G', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], [⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['k', 'u', 'm', 'u', 'q', 'e', 't', 'ə', 'ŋ'], ['r', 'a', 'i', 'n', '.', 'P', 'R', 'S'], [⟨['k', 'u', 'm', 'u', 'q', 'e', 't', 'ə', 'ŋ'], ['r', 'a', 'i', 'n', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['ʔ', 'a', 'm'], ['b', 'u', 't'], [⟨['ʔ', 'a', 'm'], ['b', 'u', 't'], none⟩]⟩, ⟨['ʔ', 'o', 'p', 't', 'a'], ['a', 'l', 's', 'o'], [⟨['ʔ', 'o', 'p', 't', 'a'], ['a', 'l', 's', 'o'], none⟩]⟩, ⟨['k', 'o', 'l', 'm', 'a', 'l', 'a', 'v', 'ə', 'ŋ'], ['b', 'e', 'l', 'i', 'e', 'v', 'e', '.', '3', 'S', 'G', '.', 'P', 'R', 'S'], [⟨['k', 'o', 'l', 'm', 'a', 'l', 'a', 'v', 'ə', 'ŋ'], ['b', 'e', 'l', 'i', 'e', 'v', 'e', '.', '3', 'S', 'G', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], [⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['u', 'j', 'ŋ', 'e'], ['N', 'E', 'G'], [⟨['u', 'j', 'ŋ', 'e'], ['N', 'E', 'G'], none⟩]⟩, ⟨['e', 'm', 'u', 'q', 'e', 't', 'k', 'e'], ['r', 'a', 'i', 'n'], [⟨['e', 'm', 'u', 'q', 'e', 't', 'k', 'e'], ['r', 'a', 'i', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2")] }

def ex6 : Datum :=
  { id := "mocnikabramovitz2019_ex6"
    source := ⟨"mocnik-abramovitz-2019", "(6)"⟩
    reportedIn := none
    language := "kory1246"
    primaryText := "ʔewŋəto kivəŋ əno kumuqetəŋ, ʔam ʔopta kivəŋ əno ujŋe emuqetke."
    glossedTokens := [("ʔewŋəto", "H."), ("kivəŋ", "ivək.3SG.PRS"), ("əno", "that"), ("kumuqetəŋ", "rain.3SG.PRS"), ("ʔam", "but"), ("ʔopta", "also"), ("kivəŋ", "ivək.3SG.PRS"), ("əno", "that"), ("ujŋe", "NEG"), ("emuqetke", "rain")]
    glossedWords := [⟨['ʔ', 'e', 'w', 'ŋ', 'ə', 't', 'o'], ['H', '.'], [⟨['ʔ', 'e', 'w', 'ŋ', 'ə', 't', 'o'], ['H', '.'], none⟩]⟩, ⟨['k', 'i', 'v', 'ə', 'ŋ'], ['i', 'v', 'ə', 'k', '.', '3', 'S', 'G', '.', 'P', 'R', 'S'], [⟨['k', 'i', 'v', 'ə', 'ŋ'], ['i', 'v', 'ə', 'k', '.', '3', 'S', 'G', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], [⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['k', 'u', 'm', 'u', 'q', 'e', 't', 'ə', 'ŋ'], ['r', 'a', 'i', 'n', '.', '3', 'S', 'G', '.', 'P', 'R', 'S'], [⟨['k', 'u', 'm', 'u', 'q', 'e', 't', 'ə', 'ŋ'], ['r', 'a', 'i', 'n', '.', '3', 'S', 'G', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['ʔ', 'a', 'm'], ['b', 'u', 't'], [⟨['ʔ', 'a', 'm'], ['b', 'u', 't'], none⟩]⟩, ⟨['ʔ', 'o', 'p', 't', 'a'], ['a', 'l', 's', 'o'], [⟨['ʔ', 'o', 'p', 't', 'a'], ['a', 'l', 's', 'o'], none⟩]⟩, ⟨['k', 'i', 'v', 'ə', 'ŋ'], ['i', 'v', 'ə', 'k', '.', '3', 'S', 'G', '.', 'P', 'R', 'S'], [⟨['k', 'i', 'v', 'ə', 'ŋ'], ['i', 'v', 'ə', 'k', '.', '3', 'S', 'G', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], [⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['u', 'j', 'ŋ', 'e'], ['N', 'E', 'G'], [⟨['u', 'j', 'ŋ', 'e'], ['N', 'E', 'G'], none⟩]⟩, ⟨['e', 'm', 'u', 'q', 'e', 't', 'k', 'e'], ['r', 'a', 'i', 'n'], [⟨['e', 'm', 'u', 'q', 'e', 't', 'k', 'e'], ['r', 'a', 'i', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2")] }

def ex7 : Datum :=
  { id := "mocnikabramovitz2019_ex7"
    source := ⟨"mocnik-abramovitz-2019", "(7)"⟩
    reportedIn := none
    language := "kory1246"
    primaryText := "əməŋ ʔujemtewilʔu mekiw ewlaj əno jemuqetiki nejetən muqeičʔən"
    glossedTokens := [("əməŋ", "all"), ("ʔujemtewilʔu", "people"), ("mekiw", "who"), ("ewlaj", "ivək.3PL.PRS"), ("əno", "that"), ("jemuqetiki", "rain.FUT.IPFV"), ("nejetən", "bring.3PL>3SG.PST"), ("muqeičʔən", "raincoat")]
    glossedWords := [⟨['ə', 'm', 'ə', 'ŋ'], ['a', 'l', 'l'], [⟨['ə', 'm', 'ə', 'ŋ'], ['a', 'l', 'l'], none⟩]⟩, ⟨['ʔ', 'u', 'j', 'e', 'm', 't', 'e', 'w', 'i', 'l', 'ʔ', 'u'], ['p', 'e', 'o', 'p', 'l', 'e'], [⟨['ʔ', 'u', 'j', 'e', 'm', 't', 'e', 'w', 'i', 'l', 'ʔ', 'u'], ['p', 'e', 'o', 'p', 'l', 'e'], none⟩]⟩, ⟨['m', 'e', 'k', 'i', 'w'], ['w', 'h', 'o'], [⟨['m', 'e', 'k', 'i', 'w'], ['w', 'h', 'o'], none⟩]⟩, ⟨['e', 'w', 'l', 'a', 'j'], ['i', 'v', 'ə', 'k', '.', '3', 'P', 'L', '.', 'P', 'R', 'S'], [⟨['e', 'w', 'l', 'a', 'j'], ['i', 'v', 'ə', 'k', '.', '3', 'P', 'L', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], [⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['j', 'e', 'm', 'u', 'q', 'e', 't', 'i', 'k', 'i'], ['r', 'a', 'i', 'n', '.', 'F', 'U', 'T', '.', 'I', 'P', 'F', 'V'], [⟨['j', 'e', 'm', 'u', 'q', 'e', 't', 'i', 'k', 'i'], ['r', 'a', 'i', 'n', '.', 'F', 'U', 'T', '.', 'I', 'P', 'F', 'V'], none⟩]⟩, ⟨['n', 'e', 'j', 'e', 't', 'ə', 'n'], ['b', 'r', 'i', 'n', 'g', '.', '3', 'P', 'L', '>', '3', 'S', 'G', '.', 'P', 'S', 'T'], [⟨['n', 'e', 'j', 'e', 't', 'ə', 'n'], ['b', 'r', 'i', 'n', 'g', '.', '3', 'P', 'L', '>', '3', 'S', 'G', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['m', 'u', 'q', 'e', 'i', 'č', 'ʔ', 'ə', 'n'], ['r', 'a', 'i', 'n', 'c', 'o', 'a', 't'], [⟨['m', 'u', 'q', 'e', 'i', 'č', 'ʔ', 'ə', 'n'], ['r', 'a', 'i', 'n', 'c', 'o', 'a', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "We're walking down the street and there are many people with raincoats. Melljo says:"
    judgment := .acceptable
    alternatives := []
    readings := [("said", .acceptable), ("allowed", .acceptable)]
    paperFeatures := [("section", "2")] }

def ex8a : Datum :=
  { id := "mocnikabramovitz2019_ex8a"
    source := ⟨"mocnik-abramovitz-2019", "(8a)"⟩
    reportedIn := none
    language := "kory1246"
    primaryText := "təkivəŋ əno əɲɲin qapəl nilɣəqin to təkivəŋ əno ənno luqin"
    glossedTokens := [("təkivəŋ", "ivək.1SG.PRS"), ("əno", "that"), ("əɲɲin", "that"), ("qapəl", "ball"), ("nilɣəqin", "white"), ("to", "and"), ("təkivəŋ", "ivək.1SG.PRS"), ("əno", "that"), ("ənno", "it"), ("luqin", "black")]
    glossedWords := [⟨['t', 'ə', 'k', 'i', 'v', 'ə', 'ŋ'], ['i', 'v', 'ə', 'k', '.', '1', 'S', 'G', '.', 'P', 'R', 'S'], [⟨['t', 'ə', 'k', 'i', 'v', 'ə', 'ŋ'], ['i', 'v', 'ə', 'k', '.', '1', 'S', 'G', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], [⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['ə', 'ɲ', 'ɲ', 'i', 'n'], ['t', 'h', 'a', 't'], [⟨['ə', 'ɲ', 'ɲ', 'i', 'n'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['q', 'a', 'p', 'ə', 'l'], ['b', 'a', 'l', 'l'], [⟨['q', 'a', 'p', 'ə', 'l'], ['b', 'a', 'l', 'l'], none⟩]⟩, ⟨['n', 'i', 'l', 'ɣ', 'ə', 'q', 'i', 'n'], ['w', 'h', 'i', 't', 'e'], [⟨['n', 'i', 'l', 'ɣ', 'ə', 'q', 'i', 'n'], ['w', 'h', 'i', 't', 'e'], none⟩]⟩, ⟨['t', 'o'], ['a', 'n', 'd'], [⟨['t', 'o'], ['a', 'n', 'd'], none⟩]⟩, ⟨['t', 'ə', 'k', 'i', 'v', 'ə', 'ŋ'], ['i', 'v', 'ə', 'k', '.', '1', 'S', 'G', '.', 'P', 'R', 'S'], [⟨['t', 'ə', 'k', 'i', 'v', 'ə', 'ŋ'], ['i', 'v', 'ə', 'k', '.', '1', 'S', 'G', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], [⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['ə', 'n', 'n', 'o'], ['i', 't'], [⟨['ə', 'n', 'n', 'o'], ['i', 't'], none⟩]⟩, ⟨['l', 'u', 'q', 'i', 'n'], ['b', 'l', 'a', 'c', 'k'], [⟨['l', 'u', 'q', 'i', 'n'], ['b', 'l', 'a', 'c', 'k'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Two balls are in a box: one white, one black. I pull out one and do not show it to you."
    judgment := .acceptable
    alternatives := []
    readings := [("necessity", .unacceptable), ("possibility", .acceptable)]
    paperFeatures := [("section", "2")] }

def ex8b : Datum :=
  { id := "mocnikabramovitz2019_ex8b"
    source := ⟨"mocnik-abramovitz-2019", "(8b)"⟩
    reportedIn := none
    language := "kory1246"
    primaryText := "ujŋe iwke təkitəŋ əno əɲɲin qapəl nilɣəqin to ujŋe iwke təkitəŋ əno ənno luqin"
    glossedTokens := [("ujŋe", "NEG"), ("iwke", "ivək"), ("təkitəŋ", "AUX.1SG.PRS"), ("əno", "that"), ("əɲɲin", "that"), ("qapəl", "ball"), ("nilɣəqin", "white"), ("to", "and"), ("ujŋe", "NEG"), ("iwke", "ivək"), ("təkitəŋ", "AUX.1SG.PRS"), ("əno", "that"), ("ənno", "it"), ("luqin", "black")]
    glossedWords := [⟨['u', 'j', 'ŋ', 'e'], ['N', 'E', 'G'], [⟨['u', 'j', 'ŋ', 'e'], ['N', 'E', 'G'], none⟩]⟩, ⟨['i', 'w', 'k', 'e'], ['i', 'v', 'ə', 'k'], [⟨['i', 'w', 'k', 'e'], ['i', 'v', 'ə', 'k'], none⟩]⟩, ⟨['t', 'ə', 'k', 'i', 't', 'ə', 'ŋ'], ['A', 'U', 'X', '.', '1', 'S', 'G', '.', 'P', 'R', 'S'], [⟨['t', 'ə', 'k', 'i', 't', 'ə', 'ŋ'], ['A', 'U', 'X', '.', '1', 'S', 'G', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], [⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['ə', 'ɲ', 'ɲ', 'i', 'n'], ['t', 'h', 'a', 't'], [⟨['ə', 'ɲ', 'ɲ', 'i', 'n'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['q', 'a', 'p', 'ə', 'l'], ['b', 'a', 'l', 'l'], [⟨['q', 'a', 'p', 'ə', 'l'], ['b', 'a', 'l', 'l'], none⟩]⟩, ⟨['n', 'i', 'l', 'ɣ', 'ə', 'q', 'i', 'n'], ['w', 'h', 'i', 't', 'e'], [⟨['n', 'i', 'l', 'ɣ', 'ə', 'q', 'i', 'n'], ['w', 'h', 'i', 't', 'e'], none⟩]⟩, ⟨['t', 'o'], ['a', 'n', 'd'], [⟨['t', 'o'], ['a', 'n', 'd'], none⟩]⟩, ⟨['u', 'j', 'ŋ', 'e'], ['N', 'E', 'G'], [⟨['u', 'j', 'ŋ', 'e'], ['N', 'E', 'G'], none⟩]⟩, ⟨['i', 'w', 'k', 'e'], ['i', 'v', 'ə', 'k'], [⟨['i', 'w', 'k', 'e'], ['i', 'v', 'ə', 'k'], none⟩]⟩, ⟨['t', 'ə', 'k', 'i', 't', 'ə', 'ŋ'], ['A', 'U', 'X', '.', '1', 'S', 'G', '.', 'P', 'R', 'S'], [⟨['t', 'ə', 'k', 'i', 't', 'ə', 'ŋ'], ['A', 'U', 'X', '.', '1', 'S', 'G', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], [⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['ə', 'n', 'n', 'o'], ['i', 't'], [⟨['ə', 'n', 'n', 'o'], ['i', 't'], none⟩]⟩, ⟨['l', 'u', 'q', 'i', 'n'], ['b', 'l', 'a', 'c', 'k'], [⟨['l', 'u', 'q', 'i', 'n'], ['b', 'l', 'a', 'c', 'k'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Two balls are in a box: one white, one black. I pull out one and do not show it to you."
    judgment := .acceptable
    alternatives := []
    readings := [("the thought of (8a)", .acceptable), ("the ball is half white and half black", .unacceptable)]
    paperFeatures := [("section", "2")] }

def ex9a : Datum :=
  { id := "mocnikabramovitz2019_ex9a"
    source := ⟨"mocnik-abramovitz-2019", "(9a)"⟩
    reportedIn := none
    language := "kory1246"
    primaryText := "ɣəmmo təkivəŋ, amu jemuqejuʔəŋ"
    glossedTokens := [("ɣəmmo", "I"), ("təkivəŋ", "ivək.1SG.PRS"), ("amu", "might"), ("jemuqejuʔəŋ", "begin.to.rain.3SG.FUT")]
    glossedWords := [⟨['ɣ', 'ə', 'm', 'm', 'o'], ['I'], [⟨['ɣ', 'ə', 'm', 'm', 'o'], ['I'], none⟩]⟩, ⟨['t', 'ə', 'k', 'i', 'v', 'ə', 'ŋ'], ['i', 'v', 'ə', 'k', '.', '1', 'S', 'G', '.', 'P', 'R', 'S'], [⟨['t', 'ə', 'k', 'i', 'v', 'ə', 'ŋ'], ['i', 'v', 'ə', 'k', '.', '1', 'S', 'G', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['a', 'm', 'u'], ['m', 'i', 'g', 'h', 't'], [⟨['a', 'm', 'u'], ['m', 'i', 'g', 'h', 't'], none⟩]⟩, ⟨['j', 'e', 'm', 'u', 'q', 'e', 'j', 'u', 'ʔ', 'ə', 'ŋ'], ['b', 'e', 'g', 'i', 'n', '.', 't', 'o', '.', 'r', 'a', 'i', 'n', '.', '3', 'S', 'G', '.', 'F', 'U', 'T'], [⟨['j', 'e', 'm', 'u', 'q', 'e', 'j', 'u', 'ʔ', 'ə', 'ŋ'], ['b', 'e', 'g', 'i', 'n', '.', 't', 'o', '.', 'r', 'a', 'i', 'n', '.', '3', 'S', 'G', '.', 'F', 'U', 'T'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2")] }

def ex14a : Datum :=
  { id := "mocnikabramovitz2019_ex14a"
    source := ⟨"mocnik-abramovitz-2019", "(14a)"⟩
    reportedIn := none
    language := "kory1246"
    primaryText := "inenɣəjulevəčʔən ivi əno əninew jejɣučewŋəlʔu metʔaŋ kojajɣočawŋəlaŋ ʔam činin ivi əno əčču qekwaŋ kojajɣočawŋəlaŋ."
    glossedTokens := [("inenɣəjulevəčʔən", "teacher"), ("ivi", "ivək.3SG.PST"), ("əno", "that"), ("əninew", "his"), ("jejɣučewŋəlʔu", "students"), ("metʔaŋ", "well"), ("kojajɣočawŋəlaŋ", "study.3PL.PRS"), ("ʔam", "but"), ("činin", "self"), ("ivi", "ivək.3SG.PST"), ("əno", "that"), ("əčču", "they"), ("qekwaŋ", "badly"), ("kojajɣočawŋəlaŋ", "study.3PL.PRS")]
    glossedWords := [⟨['i', 'n', 'e', 'n', 'ɣ', 'ə', 'j', 'u', 'l', 'e', 'v', 'ə', 'č', 'ʔ', 'ə', 'n'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], [⟨['i', 'n', 'e', 'n', 'ɣ', 'ə', 'j', 'u', 'l', 'e', 'v', 'ə', 'č', 'ʔ', 'ə', 'n'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], none⟩]⟩, ⟨['i', 'v', 'i'], ['i', 'v', 'ə', 'k', '.', '3', 'S', 'G', '.', 'P', 'S', 'T'], [⟨['i', 'v', 'i'], ['i', 'v', 'ə', 'k', '.', '3', 'S', 'G', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], [⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['ə', 'n', 'i', 'n', 'e', 'w'], ['h', 'i', 's'], [⟨['ə', 'n', 'i', 'n', 'e', 'w'], ['h', 'i', 's'], none⟩]⟩, ⟨['j', 'e', 'j', 'ɣ', 'u', 'č', 'e', 'w', 'ŋ', 'ə', 'l', 'ʔ', 'u'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's'], [⟨['j', 'e', 'j', 'ɣ', 'u', 'č', 'e', 'w', 'ŋ', 'ə', 'l', 'ʔ', 'u'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's'], none⟩]⟩, ⟨['m', 'e', 't', 'ʔ', 'a', 'ŋ'], ['w', 'e', 'l', 'l'], [⟨['m', 'e', 't', 'ʔ', 'a', 'ŋ'], ['w', 'e', 'l', 'l'], none⟩]⟩, ⟨['k', 'o', 'j', 'a', 'j', 'ɣ', 'o', 'č', 'a', 'w', 'ŋ', 'ə', 'l', 'a', 'ŋ'], ['s', 't', 'u', 'd', 'y', '.', '3', 'P', 'L', '.', 'P', 'R', 'S'], [⟨['k', 'o', 'j', 'a', 'j', 'ɣ', 'o', 'č', 'a', 'w', 'ŋ', 'ə', 'l', 'a', 'ŋ'], ['s', 't', 'u', 'd', 'y', '.', '3', 'P', 'L', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['ʔ', 'a', 'm'], ['b', 'u', 't'], [⟨['ʔ', 'a', 'm'], ['b', 'u', 't'], none⟩]⟩, ⟨['č', 'i', 'n', 'i', 'n'], ['s', 'e', 'l', 'f'], [⟨['č', 'i', 'n', 'i', 'n'], ['s', 'e', 'l', 'f'], none⟩]⟩, ⟨['i', 'v', 'i'], ['i', 'v', 'ə', 'k', '.', '3', 'S', 'G', '.', 'P', 'S', 'T'], [⟨['i', 'v', 'i'], ['i', 'v', 'ə', 'k', '.', '3', 'S', 'G', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], [⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['ə', 'č', 'č', 'u'], ['t', 'h', 'e', 'y'], [⟨['ə', 'č', 'č', 'u'], ['t', 'h', 'e', 'y'], none⟩]⟩, ⟨['q', 'e', 'k', 'w', 'a', 'ŋ'], ['b', 'a', 'd', 'l', 'y'], [⟨['q', 'e', 'k', 'w', 'a', 'ŋ'], ['b', 'a', 'd', 'l', 'y'], none⟩]⟩, ⟨['k', 'o', 'j', 'a', 'j', 'ɣ', 'o', 'č', 'a', 'w', 'ŋ', 'ə', 'l', 'a', 'ŋ'], ['s', 't', 'u', 'd', 'y', '.', '3', 'P', 'L', '.', 'P', 'R', 'S'], [⟨['k', 'o', 'j', 'a', 'j', 'ɣ', 'o', 'č', 'a', 'w', 'ŋ', 'ə', 'l', 'a', 'ŋ'], ['s', 't', 'u', 'd', 'y', '.', '3', 'P', 'L', '.', 'P', 'R', 'S'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "A teacher is always complaining to his wife about how bad his students are. One day, the principal asks him about his students, and he tells him that they are great."
    judgment := .acceptable
    alternatives := [("inenɣəjulevəčʔən ivi əno əninew jejɣučewŋəlʔu metʔaŋ kojajɣočawŋəlaŋ ʔam ivi əno əčču qekwaŋ kojajɣočawŋəlaŋ.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "3")] }

def ex14b : Datum :=
  { id := "mocnikabramovitz2019_ex14b"
    source := ⟨"mocnik-abramovitz-2019", "(14b)"⟩
    reportedIn := none
    language := "kory1246"
    primaryText := "inenɣəjulevəčʔən ivi əno əninew jejɣučewŋəlʔu qekwaŋ kojajɣočawŋəlaŋ ʔam ʔojaŋ ivi əno əčču metʔaŋ kojajɣočawŋəlaŋ"
    glossedTokens := [("inenɣəjulevəčʔən", "teacher"), ("ivi", "ivək.3SG.PST"), ("əno", "that"), ("əninew", "his"), ("jejɣučewŋəlʔu", "students"), ("qekwaŋ", "badly"), ("kojajɣočawŋəlaŋ", "study.3PL.PRS"), ("ʔam", "but"), ("ʔojaŋ", "openly"), ("ivi", "ivək.3SG.PST"), ("əno", "that"), ("əčču", "they"), ("metʔaŋ", "well"), ("kojajɣočawŋəlaŋ", "study.3PL.PRS")]
    glossedWords := [⟨['i', 'n', 'e', 'n', 'ɣ', 'ə', 'j', 'u', 'l', 'e', 'v', 'ə', 'č', 'ʔ', 'ə', 'n'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], [⟨['i', 'n', 'e', 'n', 'ɣ', 'ə', 'j', 'u', 'l', 'e', 'v', 'ə', 'č', 'ʔ', 'ə', 'n'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], none⟩]⟩, ⟨['i', 'v', 'i'], ['i', 'v', 'ə', 'k', '.', '3', 'S', 'G', '.', 'P', 'S', 'T'], [⟨['i', 'v', 'i'], ['i', 'v', 'ə', 'k', '.', '3', 'S', 'G', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], [⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['ə', 'n', 'i', 'n', 'e', 'w'], ['h', 'i', 's'], [⟨['ə', 'n', 'i', 'n', 'e', 'w'], ['h', 'i', 's'], none⟩]⟩, ⟨['j', 'e', 'j', 'ɣ', 'u', 'č', 'e', 'w', 'ŋ', 'ə', 'l', 'ʔ', 'u'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's'], [⟨['j', 'e', 'j', 'ɣ', 'u', 'č', 'e', 'w', 'ŋ', 'ə', 'l', 'ʔ', 'u'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's'], none⟩]⟩, ⟨['q', 'e', 'k', 'w', 'a', 'ŋ'], ['b', 'a', 'd', 'l', 'y'], [⟨['q', 'e', 'k', 'w', 'a', 'ŋ'], ['b', 'a', 'd', 'l', 'y'], none⟩]⟩, ⟨['k', 'o', 'j', 'a', 'j', 'ɣ', 'o', 'č', 'a', 'w', 'ŋ', 'ə', 'l', 'a', 'ŋ'], ['s', 't', 'u', 'd', 'y', '.', '3', 'P', 'L', '.', 'P', 'R', 'S'], [⟨['k', 'o', 'j', 'a', 'j', 'ɣ', 'o', 'č', 'a', 'w', 'ŋ', 'ə', 'l', 'a', 'ŋ'], ['s', 't', 'u', 'd', 'y', '.', '3', 'P', 'L', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['ʔ', 'a', 'm'], ['b', 'u', 't'], [⟨['ʔ', 'a', 'm'], ['b', 'u', 't'], none⟩]⟩, ⟨['ʔ', 'o', 'j', 'a', 'ŋ'], ['o', 'p', 'e', 'n', 'l', 'y'], [⟨['ʔ', 'o', 'j', 'a', 'ŋ'], ['o', 'p', 'e', 'n', 'l', 'y'], none⟩]⟩, ⟨['i', 'v', 'i'], ['i', 'v', 'ə', 'k', '.', '3', 'S', 'G', '.', 'P', 'S', 'T'], [⟨['i', 'v', 'i'], ['i', 'v', 'ə', 'k', '.', '3', 'S', 'G', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], [⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['ə', 'č', 'č', 'u'], ['t', 'h', 'e', 'y'], [⟨['ə', 'č', 'č', 'u'], ['t', 'h', 'e', 'y'], none⟩]⟩, ⟨['m', 'e', 't', 'ʔ', 'a', 'ŋ'], ['w', 'e', 'l', 'l'], [⟨['m', 'e', 't', 'ʔ', 'a', 'ŋ'], ['w', 'e', 'l', 'l'], none⟩]⟩, ⟨['k', 'o', 'j', 'a', 'j', 'ɣ', 'o', 'č', 'a', 'w', 'ŋ', 'ə', 'l', 'a', 'ŋ'], ['s', 't', 'u', 'd', 'y', '.', '3', 'P', 'L', '.', 'P', 'R', 'S'], [⟨['k', 'o', 'j', 'a', 'j', 'ɣ', 'o', 'č', 'a', 'w', 'ŋ', 'ə', 'l', 'a', 'ŋ'], ['s', 't', 'u', 'd', 'y', '.', '3', 'P', 'L', '.', 'P', 'R', 'S'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "A teacher is always complaining to his wife about how bad his students are. One day, the principal asks him about his students, and he tells him that they are great."
    judgment := .acceptable
    alternatives := [("inenɣəjulevəčʔən ivi əno əninew jejɣučewŋəlʔu qekwaŋ kojajɣočawŋəlaŋ ʔam ivi əno əčču metʔaŋ kojajɣočawŋəlaŋ", .unacceptable)]
    readings := []
    paperFeatures := [("section", "3")] }

def ex20 : Datum :=
  { id := "mocnikabramovitz2019_ex20"
    source := ⟨"mocnik-abramovitz-2019", "(20)"⟩
    reportedIn := none
    language := "kory1246"
    primaryText := "inenɣəjulevət͡ɕʔən ivi əno əninew jejɣut͡ɕewŋəlʔu metʔaŋ kojajɣot͡ɕawŋəlaŋ ʔam əno qekwaŋ kojajɣot͡ɕawŋəlaŋ"
    glossedTokens := [("inenɣəjulevət͡ɕʔən", "teacher"), ("ivi", "ivək.3SG.PST"), ("əno", "that"), ("əninew", "his"), ("jejɣut͡ɕewŋəlʔu", "students"), ("metʔaŋ", "well"), ("kojajɣot͡ɕawŋəlaŋ", "study.3PL.PRS"), ("ʔam", "but"), ("əno", "that"), ("qekwaŋ", "badly"), ("kojajɣot͡ɕawŋəlaŋ", "study.3PL.PRS")]
    glossedWords := [⟨['i', 'n', 'e', 'n', 'ɣ', 'ə', 'j', 'u', 'l', 'e', 'v', 'ə', 't', '͡', 'ɕ', 'ʔ', 'ə', 'n'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], [⟨['i', 'n', 'e', 'n', 'ɣ', 'ə', 'j', 'u', 'l', 'e', 'v', 'ə', 't', '͡', 'ɕ', 'ʔ', 'ə', 'n'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], none⟩]⟩, ⟨['i', 'v', 'i'], ['i', 'v', 'ə', 'k', '.', '3', 'S', 'G', '.', 'P', 'S', 'T'], [⟨['i', 'v', 'i'], ['i', 'v', 'ə', 'k', '.', '3', 'S', 'G', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], [⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['ə', 'n', 'i', 'n', 'e', 'w'], ['h', 'i', 's'], [⟨['ə', 'n', 'i', 'n', 'e', 'w'], ['h', 'i', 's'], none⟩]⟩, ⟨['j', 'e', 'j', 'ɣ', 'u', 't', '͡', 'ɕ', 'e', 'w', 'ŋ', 'ə', 'l', 'ʔ', 'u'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's'], [⟨['j', 'e', 'j', 'ɣ', 'u', 't', '͡', 'ɕ', 'e', 'w', 'ŋ', 'ə', 'l', 'ʔ', 'u'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's'], none⟩]⟩, ⟨['m', 'e', 't', 'ʔ', 'a', 'ŋ'], ['w', 'e', 'l', 'l'], [⟨['m', 'e', 't', 'ʔ', 'a', 'ŋ'], ['w', 'e', 'l', 'l'], none⟩]⟩, ⟨['k', 'o', 'j', 'a', 'j', 'ɣ', 'o', 't', '͡', 'ɕ', 'a', 'w', 'ŋ', 'ə', 'l', 'a', 'ŋ'], ['s', 't', 'u', 'd', 'y', '.', '3', 'P', 'L', '.', 'P', 'R', 'S'], [⟨['k', 'o', 'j', 'a', 'j', 'ɣ', 'o', 't', '͡', 'ɕ', 'a', 'w', 'ŋ', 'ə', 'l', 'a', 'ŋ'], ['s', 't', 'u', 'd', 'y', '.', '3', 'P', 'L', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['ʔ', 'a', 'm'], ['b', 'u', 't'], [⟨['ʔ', 'a', 'm'], ['b', 'u', 't'], none⟩]⟩, ⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], [⟨['ə', 'n', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['q', 'e', 'k', 'w', 'a', 'ŋ'], ['b', 'a', 'd', 'l', 'y'], [⟨['q', 'e', 'k', 'w', 'a', 'ŋ'], ['b', 'a', 'd', 'l', 'y'], none⟩]⟩, ⟨['k', 'o', 'j', 'a', 'j', 'ɣ', 'o', 't', '͡', 'ɕ', 'a', 'w', 'ŋ', 'ə', 'l', 'a', 'ŋ'], ['s', 't', 'u', 'd', 'y', '.', '3', 'P', 'L', '.', 'P', 'R', 'S'], [⟨['k', 'o', 'j', 'a', 'j', 'ɣ', 'o', 't', '͡', 'ɕ', 'a', 'w', 'ŋ', 'ə', 'l', 'a', 'ŋ'], ['s', 't', 'u', 'd', 'y', '.', '3', 'P', 'L', '.', 'P', 'R', 'S'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "A principal enters the classroom of a teacher whose students are doing poorly in class and asks him how the students are doing. The teacher doesn't want to disappoint the principal, so he says 'The students are doing well'."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4")] }

def all : List Datum := [ex2, ex4, ex5, ex6, ex7, ex8a, ex8b, ex9a, ex14a, ex14b, ex20]

end MocnikAbramovitz2019.Examples
