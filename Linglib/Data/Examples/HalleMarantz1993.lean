module

public import Linglib.Data.Examples.Schema

/-!
# `HalleMarantz1993` — typed example data

Auto-generated from `Linglib/Data/Examples/HalleMarantz1993.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HalleMarantz1993.Examples`.
-/

@[expose] public section

namespace HalleMarantz1993.Examples

def beat_past_participle : Datum :=
  { id := "hallemarantz1993_beat_past_participle"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "beaten"
    glossedTokens := [("beat-en", "beat-PST.PTCP")]
    glossedWords := [⟨[['b', 'e', 'a', 't'], ['e', 'n']], [['b', 'e', 'a', 't'], ['P', 'S', 'T', '.', 'P', 'T', 'C', 'P']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Row 'Past participle' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "beat"), ("part", "past_participle"), ("suffix", "-n")] }

def beat_past_finite : Datum :=
  { id := "hallemarantz1993_beat_past_finite"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "beat"
    glossedTokens := [("beat", "beat.PST")]
    glossedWords := [⟨[['b', 'e', 'a', 't']], [['b', 'e', 'a', 't', '.', 'P', 'S', 'T']]⟩]
    lgrConformance := some .wordAligned
    context := "Row 'Past finite' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "beat"), ("part", "past_finite"), ("suffix", "∅")] }

def beat_nonpast_3sg : Datum :=
  { id := "hallemarantz1993_beat_nonpast_3sg"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "beats"
    glossedTokens := [("beat-s", "beat-3SG.PRS")]
    glossedWords := [⟨[['b', 'e', 'a', 't'], ['s']], [['b', 'e', 'a', 't'], ['3', 'S', 'G', '.', 'P', 'R', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Row 'Nonpast finite 3rd sg' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "beat"), ("part", "nonpast_3sg"), ("suffix", "-z")] }

def beat_nonpast_participle : Datum :=
  { id := "hallemarantz1993_beat_nonpast_participle"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "beating"
    glossedTokens := [("beat-ing", "beat-PRS.PTCP")]
    glossedWords := [⟨[['b', 'e', 'a', 't'], ['i', 'n', 'g']], [['b', 'e', 'a', 't'], ['P', 'R', 'S', '.', 'P', 'T', 'C', 'P']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Row 'Nonpast participle' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "beat"), ("part", "nonpast_participle"), ("suffix", "-ing")] }

def beat_nonpast_finite : Datum :=
  { id := "hallemarantz1993_beat_nonpast_finite"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "beat"
    glossedTokens := [("beat", "beat.PRS")]
    glossedWords := [⟨[['b', 'e', 'a', 't']], [['b', 'e', 'a', 't', '.', 'P', 'R', 'S']]⟩]
    lgrConformance := some .wordAligned
    context := "Row 'Nonpast finite' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "beat"), ("part", "nonpast_finite"), ("suffix", "∅")] }

def put_past_participle : Datum :=
  { id := "hallemarantz1993_put_past_participle"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "put"
    glossedTokens := [("put", "put.PST.PTCP")]
    glossedWords := [⟨[['p', 'u', 't']], [['p', 'u', 't', '.', 'P', 'S', 'T', '.', 'P', 'T', 'C', 'P']]⟩]
    lgrConformance := some .wordAligned
    context := "Row 'Past participle' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "put"), ("part", "past_participle"), ("suffix", "∅")] }

def put_past_finite : Datum :=
  { id := "hallemarantz1993_put_past_finite"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "put"
    glossedTokens := [("put", "put.PST")]
    glossedWords := [⟨[['p', 'u', 't']], [['p', 'u', 't', '.', 'P', 'S', 'T']]⟩]
    lgrConformance := some .wordAligned
    context := "Row 'Past finite' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "put"), ("part", "past_finite"), ("suffix", "∅")] }

def put_nonpast_3sg : Datum :=
  { id := "hallemarantz1993_put_nonpast_3sg"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "puts"
    glossedTokens := [("put-s", "put-3SG.PRS")]
    glossedWords := [⟨[['p', 'u', 't'], ['s']], [['p', 'u', 't'], ['3', 'S', 'G', '.', 'P', 'R', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Row 'Nonpast finite 3rd sg' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "put"), ("part", "nonpast_3sg"), ("suffix", "-z")] }

def put_nonpast_participle : Datum :=
  { id := "hallemarantz1993_put_nonpast_participle"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "putting"
    glossedTokens := [("putt-ing", "put-PRS.PTCP")]
    glossedWords := [⟨[['p', 'u', 't', 't'], ['i', 'n', 'g']], [['p', 'u', 't'], ['P', 'R', 'S', '.', 'P', 'T', 'C', 'P']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Row 'Nonpast participle' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "put"), ("part", "nonpast_participle"), ("suffix", "-ing")] }

def put_nonpast_finite : Datum :=
  { id := "hallemarantz1993_put_nonpast_finite"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "put"
    glossedTokens := [("put", "put.PRS")]
    glossedWords := [⟨[['p', 'u', 't']], [['p', 'u', 't', '.', 'P', 'R', 'S']]⟩]
    lgrConformance := some .wordAligned
    context := "Row 'Nonpast finite' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "put"), ("part", "nonpast_finite"), ("suffix", "∅")] }

def dwell_past_participle : Datum :=
  { id := "hallemarantz1993_dwell_past_participle"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "dwelt"
    glossedTokens := [("dwel-t", "dwell-PST.PTCP")]
    glossedWords := [⟨[['d', 'w', 'e', 'l'], ['t']], [['d', 'w', 'e', 'l', 'l'], ['P', 'S', 'T', '.', 'P', 'T', 'C', 'P']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Row 'Past participle' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "dwell"), ("part", "past_participle"), ("suffix", "-t")] }

def dwell_past_finite : Datum :=
  { id := "hallemarantz1993_dwell_past_finite"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "dwelt"
    glossedTokens := [("dwel-t", "dwell-PST")]
    glossedWords := [⟨[['d', 'w', 'e', 'l'], ['t']], [['d', 'w', 'e', 'l', 'l'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Row 'Past finite' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "dwell"), ("part", "past_finite"), ("suffix", "-t")] }

def dwell_nonpast_3sg : Datum :=
  { id := "hallemarantz1993_dwell_nonpast_3sg"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "dwells"
    glossedTokens := [("dwell-s", "dwell-3SG.PRS")]
    glossedWords := [⟨[['d', 'w', 'e', 'l', 'l'], ['s']], [['d', 'w', 'e', 'l', 'l'], ['3', 'S', 'G', '.', 'P', 'R', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Row 'Nonpast finite 3rd sg' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "dwell"), ("part", "nonpast_3sg"), ("suffix", "-z")] }

def dwell_nonpast_participle : Datum :=
  { id := "hallemarantz1993_dwell_nonpast_participle"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "dwelling"
    glossedTokens := [("dwell-ing", "dwell-PRS.PTCP")]
    glossedWords := [⟨[['d', 'w', 'e', 'l', 'l'], ['i', 'n', 'g']], [['d', 'w', 'e', 'l', 'l'], ['P', 'R', 'S', '.', 'P', 'T', 'C', 'P']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Row 'Nonpast participle' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "dwell"), ("part", "nonpast_participle"), ("suffix", "-ing")] }

def dwell_nonpast_finite : Datum :=
  { id := "hallemarantz1993_dwell_nonpast_finite"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "dwell"
    glossedTokens := [("dwell", "dwell.PRS")]
    glossedWords := [⟨[['d', 'w', 'e', 'l', 'l']], [['d', 'w', 'e', 'l', 'l', '.', 'P', 'R', 'S']]⟩]
    lgrConformance := some .wordAligned
    context := "Row 'Nonpast finite' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "dwell"), ("part", "nonpast_finite"), ("suffix", "∅")] }

def play_past_participle : Datum :=
  { id := "hallemarantz1993_play_past_participle"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "played"
    glossedTokens := [("play-ed", "play-PST.PTCP")]
    glossedWords := [⟨[['p', 'l', 'a', 'y'], ['e', 'd']], [['p', 'l', 'a', 'y'], ['P', 'S', 'T', '.', 'P', 'T', 'C', 'P']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Row 'Past participle' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "play"), ("part", "past_participle"), ("suffix", "-d")] }

def play_past_finite : Datum :=
  { id := "hallemarantz1993_play_past_finite"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "played"
    glossedTokens := [("play-ed", "play-PST")]
    glossedWords := [⟨[['p', 'l', 'a', 'y'], ['e', 'd']], [['p', 'l', 'a', 'y'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Row 'Past finite' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "play"), ("part", "past_finite"), ("suffix", "-d")] }

def play_nonpast_3sg : Datum :=
  { id := "hallemarantz1993_play_nonpast_3sg"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "plays"
    glossedTokens := [("play-s", "play-3SG.PRS")]
    glossedWords := [⟨[['p', 'l', 'a', 'y'], ['s']], [['p', 'l', 'a', 'y'], ['3', 'S', 'G', '.', 'P', 'R', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Row 'Nonpast finite 3rd sg' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "play"), ("part", "nonpast_3sg"), ("suffix", "-z")] }

def play_nonpast_participle : Datum :=
  { id := "hallemarantz1993_play_nonpast_participle"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "playing"
    glossedTokens := [("play-ing", "play-PRS.PTCP")]
    glossedWords := [⟨[['p', 'l', 'a', 'y'], ['i', 'n', 'g']], [['p', 'l', 'a', 'y'], ['P', 'R', 'S', '.', 'P', 'T', 'C', 'P']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Row 'Nonpast participle' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "play"), ("part", "nonpast_participle"), ("suffix", "-ing")] }

def play_nonpast_finite : Datum :=
  { id := "hallemarantz1993_play_nonpast_finite"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "play"
    glossedTokens := [("play", "play.PRS")]
    glossedWords := [⟨[['p', 'l', 'a', 'y']], [['p', 'l', 'a', 'y', '.', 'P', 'R', 'S']]⟩]
    lgrConformance := some .wordAligned
    context := "Row 'Nonpast finite' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "play"), ("part", "nonpast_finite"), ("suffix", "∅")] }

def all : List Datum := [beat_past_participle, beat_past_finite, beat_nonpast_3sg, beat_nonpast_participle, beat_nonpast_finite, put_past_participle, put_past_finite, put_nonpast_3sg, put_nonpast_participle, put_nonpast_finite, dwell_past_participle, dwell_past_finite, dwell_nonpast_3sg, dwell_nonpast_participle, dwell_nonpast_finite, play_past_participle, play_past_finite, play_nonpast_3sg, play_nonpast_participle, play_nonpast_finite]

end HalleMarantz1993.Examples
