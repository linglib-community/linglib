module

public import Linglib.Data.Examples.Schema

/-!
# `BejarRezac2009` — typed example data

Auto-generated from `Linglib/Data/Examples/BejarRezac2009.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BejarRezac2009.Examples`.
-/

@[expose] public section

namespace BejarRezac2009.Examples

def br2009_2a : Datum :=
  { id := "br2009_2a"
    source := ⟨"bejar-rezac-2009", "(2a)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "ikusi zintudan"
    glossedTokens := [("ikusi", "seen"), ("z-in-t-u-da-n", "2-X-PL-have-1-PAST")]
    glossedWords := [⟨['i', 'k', 'u', 's', 'i'], ['s', 'e', 'e', 'n'], [⟨['i', 'k', 'u', 's', 'i'], ['s', 'e', 'e', 'n'], none⟩]⟩, ⟨['z', '-', 'i', 'n', '-', 't', '-', 'u', '-', 'd', 'a', '-', 'n'], ['2', '-', 'X', '-', 'P', 'L', '-', 'h', 'a', 'v', 'e', '-', '1', '-', 'P', 'A', 'S', 'T'], [⟨['z'], ['2'], none⟩, ⟨['i', 'n'], ['X'], some '-'⟩, ⟨['t'], ['P', 'L'], some '-'⟩, ⟨['u'], ['h', 'a', 'v', 'e'], some '-'⟩, ⟨['d', 'a'], ['1'], some '-'⟩, ⟨['n'], ['P', 'A', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "1"), ("ia", "2"), ("controller", "2"), ("context", "inverse")] }

def br2009_2b : Datum :=
  { id := "br2009_2b"
    source := ⟨"bejar-rezac-2009", "(2b)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "ikusi ninduen"
    glossedTokens := [("ikusi", "seen"), ("n-ind-u-en", "1-X-have-PAST")]
    glossedWords := [⟨['i', 'k', 'u', 's', 'i'], ['s', 'e', 'e', 'n'], [⟨['i', 'k', 'u', 's', 'i'], ['s', 'e', 'e', 'n'], none⟩]⟩, ⟨['n', '-', 'i', 'n', 'd', '-', 'u', '-', 'e', 'n'], ['1', '-', 'X', '-', 'h', 'a', 'v', 'e', '-', 'P', 'A', 'S', 'T'], [⟨['n'], ['1'], none⟩, ⟨['i', 'n', 'd'], ['X'], some '-'⟩, ⟨['u'], ['h', 'a', 'v', 'e'], some '-'⟩, ⟨['e', 'n'], ['P', 'A', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "3"), ("ia", "1"), ("controller", "1"), ("context", "inverse")] }

def br2009_2c : Datum :=
  { id := "br2009_2c"
    source := ⟨"bejar-rezac-2009", "(2c)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "ikusi ninduzun"
    glossedTokens := [("ikusi", "seen"), ("n-ind-u-zu-n", "1-X-have-2-PAST")]
    glossedWords := [⟨['i', 'k', 'u', 's', 'i'], ['s', 'e', 'e', 'n'], [⟨['i', 'k', 'u', 's', 'i'], ['s', 'e', 'e', 'n'], none⟩]⟩, ⟨['n', '-', 'i', 'n', 'd', '-', 'u', '-', 'z', 'u', '-', 'n'], ['1', '-', 'X', '-', 'h', 'a', 'v', 'e', '-', '2', '-', 'P', 'A', 'S', 'T'], [⟨['n'], ['1'], none⟩, ⟨['i', 'n', 'd'], ['X'], some '-'⟩, ⟨['u'], ['h', 'a', 'v', 'e'], some '-'⟩, ⟨['z', 'u'], ['2'], some '-'⟩, ⟨['n'], ['P', 'A', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "2"), ("ia", "1"), ("controller", "1"), ("context", "inverse")] }

def br2009_2d : Datum :=
  { id := "br2009_2d"
    source := ⟨"bejar-rezac-2009", "(2d)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "ikusi nuen"
    glossedTokens := [("ikusi", "seen"), ("n-u-en", "1-have-PAST")]
    glossedWords := [⟨['i', 'k', 'u', 's', 'i'], ['s', 'e', 'e', 'n'], [⟨['i', 'k', 'u', 's', 'i'], ['s', 'e', 'e', 'n'], none⟩]⟩, ⟨['n', '-', 'u', '-', 'e', 'n'], ['1', '-', 'h', 'a', 'v', 'e', '-', 'P', 'A', 'S', 'T'], [⟨['n'], ['1'], none⟩, ⟨['u'], ['h', 'a', 'v', 'e'], some '-'⟩, ⟨['e', 'n'], ['P', 'A', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "1"), ("ia", "3"), ("controller", "1"), ("context", "direct")] }

def br2009_3 : Datum :=
  { id := "br2009_3"
    source := ⟨"bejar-rezac-2009", "(3)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Nik neure burua ikusten nuen."
    glossedTokens := [("Ni-k", "1-E"), ("neure", "my.own"), ("buru-a", "head-the.A"), ("ikusten", "seeing"), ("n-u-en", "1-have-PAST")]
    glossedWords := [⟨['N', 'i', '-', 'k'], ['1', '-', 'E'], [⟨['N', 'i'], ['1'], none⟩, ⟨['k'], ['E'], some '-'⟩]⟩, ⟨['n', 'e', 'u', 'r', 'e'], ['m', 'y', '.', 'o', 'w', 'n'], [⟨['n', 'e', 'u', 'r', 'e'], ['m', 'y', '.', 'o', 'w', 'n'], none⟩]⟩, ⟨['b', 'u', 'r', 'u', '-', 'a'], ['h', 'e', 'a', 'd', '-', 't', 'h', 'e', '.', 'A'], [⟨['b', 'u', 'r', 'u'], ['h', 'e', 'a', 'd'], none⟩, ⟨['a'], ['t', 'h', 'e', '.', 'A'], some '-'⟩]⟩, ⟨['i', 'k', 'u', 's', 't', 'e', 'n'], ['s', 'e', 'e', 'i', 'n', 'g'], [⟨['i', 'k', 'u', 's', 't', 'e', 'n'], ['s', 'e', 'e', 'i', 'n', 'g'], none⟩]⟩, ⟨['n', '-', 'u', '-', 'e', 'n'], ['1', '-', 'h', 'a', 'v', 'e', '-', 'P', 'A', 'S', 'T'], [⟨['n'], ['1'], none⟩, ⟨['u'], ['h', 'a', 'v', 'e'], some '-'⟩, ⟨['e', 'n'], ['P', 'A', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "1"), ("ia", "3"), ("controller", "1"), ("diagnostic", "case and binding unaffected")] }

def br2009_15 : Datum :=
  { id := "br2009_15"
    source := ⟨"bejar-rezac-2009", "(15)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Zuk etsaiari misilak saldu dizkiozu"
    glossedTokens := [("Zu-k", "you-E"), ("etsaia-ri", "enemy-D"), ("misil-ak", "missile-A.PL"), ("saldu", "sold"), ("d-i-zki-o-zu", "X-have-PL-3.D-2.E")]
    glossedWords := [⟨['Z', 'u', '-', 'k'], ['y', 'o', 'u', '-', 'E'], [⟨['Z', 'u'], ['y', 'o', 'u'], none⟩, ⟨['k'], ['E'], some '-'⟩]⟩, ⟨['e', 't', 's', 'a', 'i', 'a', '-', 'r', 'i'], ['e', 'n', 'e', 'm', 'y', '-', 'D'], [⟨['e', 't', 's', 'a', 'i', 'a'], ['e', 'n', 'e', 'm', 'y'], none⟩, ⟨['r', 'i'], ['D'], some '-'⟩]⟩, ⟨['m', 'i', 's', 'i', 'l', '-', 'a', 'k'], ['m', 'i', 's', 's', 'i', 'l', 'e', '-', 'A', '.', 'P', 'L'], [⟨['m', 'i', 's', 'i', 'l'], ['m', 'i', 's', 's', 'i', 'l', 'e'], none⟩, ⟨['a', 'k'], ['A', '.', 'P', 'L'], some '-'⟩]⟩, ⟨['s', 'a', 'l', 'd', 'u'], ['s', 'o', 'l', 'd'], [⟨['s', 'a', 'l', 'd', 'u'], ['s', 'o', 'l', 'd'], none⟩]⟩, ⟨['d', '-', 'i', '-', 'z', 'k', 'i', '-', 'o', '-', 'z', 'u'], ['X', '-', 'h', 'a', 'v', 'e', '-', 'P', 'L', '-', '3', '.', 'D', '-', '2', '.', 'E'], [⟨['d'], ['X'], none⟩, ⟨['i'], ['h', 'a', 'v', 'e'], some '-'⟩, ⟨['z', 'k', 'i'], ['P', 'L'], some '-'⟩, ⟨['o'], ['3', '.', 'D'], some '-'⟩, ⟨['z', 'u'], ['2', '.', 'E'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("constraint", "Person Case Constraint")] }

def br2009_15_ni : Datum :=
  { id := "br2009_15_ni"
    source := ⟨"bejar-rezac-2009", "(15)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Zu-k etsaia-ri ni saldu n-a-i-o-zu"
    glossedTokens := [("Zu-k", "you-E"), ("etsaia-ri", "enemy-D"), ("ni", "me.A"), ("saldu", "sold"), ("n-a-i-o-zu", "1-X-have-3.D-2.E")]
    glossedWords := [⟨['Z', 'u', '-', 'k'], ['y', 'o', 'u', '-', 'E'], [⟨['Z', 'u'], ['y', 'o', 'u'], none⟩, ⟨['k'], ['E'], some '-'⟩]⟩, ⟨['e', 't', 's', 'a', 'i', 'a', '-', 'r', 'i'], ['e', 'n', 'e', 'm', 'y', '-', 'D'], [⟨['e', 't', 's', 'a', 'i', 'a'], ['e', 'n', 'e', 'm', 'y'], none⟩, ⟨['r', 'i'], ['D'], some '-'⟩]⟩, ⟨['n', 'i'], ['m', 'e', '.', 'A'], [⟨['n', 'i'], ['m', 'e', '.', 'A'], none⟩]⟩, ⟨['s', 'a', 'l', 'd', 'u'], ['s', 'o', 'l', 'd'], [⟨['s', 'a', 'l', 'd', 'u'], ['s', 'o', 'l', 'd'], none⟩]⟩, ⟨['n', '-', 'a', '-', 'i', '-', 'o', '-', 'z', 'u'], ['1', '-', 'X', '-', 'h', 'a', 'v', 'e', '-', '3', '.', 'D', '-', '2', '.', 'E'], [⟨['n'], ['1'], none⟩, ⟨['a'], ['X'], some '-'⟩, ⟨['i'], ['h', 'a', 'v', 'e'], some '-'⟩, ⟨['o'], ['3', '.', 'D'], some '-'⟩, ⟨['z', 'u'], ['2', '.', 'E'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("constraint", "Person Case Constraint")] }

def br2009_t9_3_1 : Datum :=
  { id := "br2009_t9_3_1"
    source := ⟨"bejar-rezac-2009", "Table 9"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "niñdduen"
    glossedTokens := [("n-iñdd-u-en", "1.SG-INV-have-PAST")]
    glossedWords := [⟨['n', '-', 'i', 'ñ', 'd', 'd', '-', 'u', '-', 'e', 'n'], ['1', '.', 'S', 'G', '-', 'I', 'N', 'V', '-', 'h', 'a', 'v', 'e', '-', 'P', 'A', 'S', 'T'], [⟨['n'], ['1', '.', 'S', 'G'], none⟩, ⟨['i', 'ñ', 'd', 'd'], ['I', 'N', 'V'], some '-'⟩, ⟨['u'], ['h', 'a', 'v', 'e'], some '-'⟩, ⟨['e', 'n'], ['P', 'A', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "3"), ("ia", "1"), ("repair", "added probe (INV)")] }

def br2009_t9_1_2 : Datum :=
  { id := "br2009_t9_1_2"
    source := ⟨"bejar-rezac-2009", "Table 9"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "s-iñdd-u-te-n"
    glossedTokens := [("s-iñdd-u-te-n", "2.SG-INV-have-1.SG-PAST")]
    glossedWords := [⟨['s', '-', 'i', 'ñ', 'd', 'd', '-', 'u', '-', 't', 'e', '-', 'n'], ['2', '.', 'S', 'G', '-', 'I', 'N', 'V', '-', 'h', 'a', 'v', 'e', '-', '1', '.', 'S', 'G', '-', 'P', 'A', 'S', 'T'], [⟨['s'], ['2', '.', 'S', 'G'], none⟩, ⟨['i', 'ñ', 'd', 'd'], ['I', 'N', 'V'], some '-'⟩, ⟨['u'], ['h', 'a', 'v', 'e'], some '-'⟩, ⟨['t', 'e'], ['1', '.', 'S', 'G'], some '-'⟩, ⟨['n'], ['P', 'A', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "1"), ("ia", "2"), ("repair", "added probe (INV)")] }

def br2009_t9_1_3 : Datum :=
  { id := "br2009_t9_1_3"
    source := ⟨"bejar-rezac-2009", "Table 9"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "n-eb-en"
    glossedTokens := [("n-eb-en", "1.SG-have-PAST")]
    glossedWords := [⟨['n', '-', 'e', 'b', '-', 'e', 'n'], ['1', '.', 'S', 'G', '-', 'h', 'a', 'v', 'e', '-', 'P', 'A', 'S', 'T'], [⟨['n'], ['1', '.', 'S', 'G'], none⟩, ⟨['e', 'b'], ['h', 'a', 'v', 'e'], some '-'⟩, ⟨['e', 'n'], ['P', 'A', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "1"), ("ia", "3"), ("context", "direct")] }

def br2009_t9_2_1 : Datum :=
  { id := "br2009_t9_2_1"
    source := ⟨"bejar-rezac-2009", "Table 9"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "n-iñdd-u-su-n"
    glossedTokens := [("n-iñdd-u-su-n", "1.SG-INV-have-2.SG-PAST")]
    glossedWords := [⟨['n', '-', 'i', 'ñ', 'd', 'd', '-', 'u', '-', 's', 'u', '-', 'n'], ['1', '.', 'S', 'G', '-', 'I', 'N', 'V', '-', 'h', 'a', 'v', 'e', '-', '2', '.', 'S', 'G', '-', 'P', 'A', 'S', 'T'], [⟨['n'], ['1', '.', 'S', 'G'], none⟩, ⟨['i', 'ñ', 'd', 'd'], ['I', 'N', 'V'], some '-'⟩, ⟨['u'], ['h', 'a', 'v', 'e'], some '-'⟩, ⟨['s', 'u'], ['2', '.', 'S', 'G'], some '-'⟩, ⟨['n'], ['P', 'A', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "2"), ("ia", "1"), ("repair", "added probe (INV)")] }

def br2009_t9_2_1pl : Datum :=
  { id := "br2009_t9_2_1pl"
    source := ⟨"bejar-rezac-2009", "Table 9"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "g-iñdd-u-su-n"
    glossedTokens := [("g-iñdd-u-su-n", "1.PL-INV-have-2.SG-PAST")]
    glossedWords := [⟨['g', '-', 'i', 'ñ', 'd', 'd', '-', 'u', '-', 's', 'u', '-', 'n'], ['1', '.', 'P', 'L', '-', 'I', 'N', 'V', '-', 'h', 'a', 'v', 'e', '-', '2', '.', 'S', 'G', '-', 'P', 'A', 'S', 'T'], [⟨['g'], ['1', '.', 'P', 'L'], none⟩, ⟨['i', 'ñ', 'd', 'd'], ['I', 'N', 'V'], some '-'⟩, ⟨['u'], ['h', 'a', 'v', 'e'], some '-'⟩, ⟨['s', 'u'], ['2', '.', 'S', 'G'], some '-'⟩, ⟨['n'], ['P', 'A', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "2"), ("ia", "1"), ("repair", "added probe (INV)")] }

def br2009_t9_2_3 : Datum :=
  { id := "br2009_t9_2_3"
    source := ⟨"bejar-rezac-2009", "Table 9"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "s-eb-en"
    glossedTokens := [("s-eb-en", "2.SG-have-PAST")]
    glossedWords := [⟨['s', '-', 'e', 'b', '-', 'e', 'n'], ['2', '.', 'S', 'G', '-', 'h', 'a', 'v', 'e', '-', 'P', 'A', 'S', 'T'], [⟨['s'], ['2', '.', 'S', 'G'], none⟩, ⟨['e', 'b'], ['h', 'a', 'v', 'e'], some '-'⟩, ⟨['e', 'n'], ['P', 'A', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "2"), ("ia", "3"), ("context", "direct")] }

def br2009_t9_1pl_2 : Datum :=
  { id := "br2009_t9_1pl_2"
    source := ⟨"bejar-rezac-2009", "Table 9"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "s-iñdd-u-gu-n"
    glossedTokens := [("s-iñdd-u-gu-n", "2.SG-INV-have-1.PL-PAST")]
    glossedWords := [⟨['s', '-', 'i', 'ñ', 'd', 'd', '-', 'u', '-', 'g', 'u', '-', 'n'], ['2', '.', 'S', 'G', '-', 'I', 'N', 'V', '-', 'h', 'a', 'v', 'e', '-', '1', '.', 'P', 'L', '-', 'P', 'A', 'S', 'T'], [⟨['s'], ['2', '.', 'S', 'G'], none⟩, ⟨['i', 'ñ', 'd', 'd'], ['I', 'N', 'V'], some '-'⟩, ⟨['u'], ['h', 'a', 'v', 'e'], some '-'⟩, ⟨['g', 'u'], ['1', '.', 'P', 'L'], some '-'⟩, ⟨['n'], ['P', 'A', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "1"), ("ia", "2"), ("repair", "added probe (INV)")] }

def br2009_t9_1pl_3 : Datum :=
  { id := "br2009_t9_1pl_3"
    source := ⟨"bejar-rezac-2009", "Table 9"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "g-eb-en"
    glossedTokens := [("g-eb-en", "1.PL-have-PAST")]
    glossedWords := [⟨['g', '-', 'e', 'b', '-', 'e', 'n'], ['1', '.', 'P', 'L', '-', 'h', 'a', 'v', 'e', '-', 'P', 'A', 'S', 'T'], [⟨['g'], ['1', '.', 'P', 'L'], none⟩, ⟨['e', 'b'], ['h', 'a', 'v', 'e'], some '-'⟩, ⟨['e', 'n'], ['P', 'A', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "1"), ("ia", "3"), ("context", "direct")] }

def br2009_t9_3_2 : Datum :=
  { id := "br2009_t9_3_2"
    source := ⟨"bejar-rezac-2009", "Table 9"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "s-iñdd-u-en"
    glossedTokens := [("s-iñdd-u-en", "2.SG-INV-have-PAST")]
    glossedWords := [⟨['s', '-', 'i', 'ñ', 'd', 'd', '-', 'u', '-', 'e', 'n'], ['2', '.', 'S', 'G', '-', 'I', 'N', 'V', '-', 'h', 'a', 'v', 'e', '-', 'P', 'A', 'S', 'T'], [⟨['s'], ['2', '.', 'S', 'G'], none⟩, ⟨['i', 'ñ', 'd', 'd'], ['I', 'N', 'V'], some '-'⟩, ⟨['u'], ['h', 'a', 'v', 'e'], some '-'⟩, ⟨['e', 'n'], ['P', 'A', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "3"), ("ia", "2"), ("repair", "added probe (INV)")] }

def br2009_t9_3_1pl : Datum :=
  { id := "br2009_t9_3_1pl"
    source := ⟨"bejar-rezac-2009", "Table 9"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "g-iñdd-u-en"
    glossedTokens := [("g-iñdd-u-en", "1.PL-INV-have-PAST")]
    glossedWords := [⟨['g', '-', 'i', 'ñ', 'd', 'd', '-', 'u', '-', 'e', 'n'], ['1', '.', 'P', 'L', '-', 'I', 'N', 'V', '-', 'h', 'a', 'v', 'e', '-', 'P', 'A', 'S', 'T'], [⟨['g'], ['1', '.', 'P', 'L'], none⟩, ⟨['i', 'ñ', 'd', 'd'], ['I', 'N', 'V'], some '-'⟩, ⟨['u'], ['h', 'a', 'v', 'e'], some '-'⟩, ⟨['e', 'n'], ['P', 'A', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "3"), ("ia", "1"), ("repair", "added probe (INV)")] }

def br2009_t9_3_3 : Datum :=
  { id := "br2009_t9_3_3"
    source := ⟨"bejar-rezac-2009", "Table 9"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "eb-en"
    glossedTokens := [("eb-en", "have-PAST")]
    glossedWords := [⟨['e', 'b', '-', 'e', 'n'], ['h', 'a', 'v', 'e', '-', 'P', 'A', 'S', 'T'], [⟨['e', 'b'], ['h', 'a', 'v', 'e'], none⟩, ⟨['e', 'n'], ['P', 'A', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "3"), ("ia", "3")] }

def br2009_10 : Datum :=
  { id := "br2009_10"
    source := ⟨"bejar-rezac-2009", "(10)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "sijakiona chochote"
    glossedTokens := [("si-ja-ki-ona", "1.SG-NEG-7-see"), ("chochote", "anything")]
    glossedWords := [⟨['s', 'i', '-', 'j', 'a', '-', 'k', 'i', '-', 'o', 'n', 'a'], ['1', '.', 'S', 'G', '-', 'N', 'E', 'G', '-', '7', '-', 's', 'e', 'e'], [⟨['s', 'i'], ['1', '.', 'S', 'G'], none⟩, ⟨['j', 'a'], ['N', 'E', 'G'], some '-'⟩, ⟨['k', 'i'], ['7'], some '-'⟩, ⟨['o', 'n', 'a'], ['s', 'e', 'e'], some '-'⟩]⟩, ⟨['c', 'h', 'o', 'c', 'h', 'o', 't', 'e'], ['a', 'n', 'y', 't', 'h', 'i', 'n', 'g'], [⟨['c', 'h', 'o', 'c', 'h', 'o', 't', 'e'], ['a', 'n', 'y', 't', 'h', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("probe", "flat [u-3]"), ("agreement", "object and subject independent")] }

def br2009_17a : Datum :=
  { id := "br2009_17a"
    source := ⟨"bejar-rezac-2009", "(17a)"⟩
    reportedIn := none
    language := "otta1242"
    primaryText := "g-waabm-in"
    glossedTokens := [("g-waabm-in", "2-see-1.INV")]
    glossedWords := [⟨['g', '-', 'w', 'a', 'a', 'b', 'm', '-', 'i', 'n'], ['2', '-', 's', 'e', 'e', '-', '1', '.', 'I', 'N', 'V'], [⟨['g'], ['2'], none⟩, ⟨['w', 'a', 'a', 'b', 'm'], ['s', 'e', 'e'], some '-'⟩, ⟨['i', 'n'], ['1', '.', 'I', 'N', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "1"), ("ia", "2"), ("controller", "2"), ("context", "inverse")] }

def br2009_17b : Datum :=
  { id := "br2009_17b"
    source := ⟨"bejar-rezac-2009", "(17b)"⟩
    reportedIn := none
    language := "otta1242"
    primaryText := "g-waabm-i"
    glossedTokens := [("g-waabm-i", "2-see-DFLT.1")]
    glossedWords := [⟨['g', '-', 'w', 'a', 'a', 'b', 'm', '-', 'i'], ['2', '-', 's', 'e', 'e', '-', 'D', 'F', 'L', 'T', '.', '1'], [⟨['g'], ['2'], none⟩, ⟨['w', 'a', 'a', 'b', 'm'], ['s', 'e', 'e'], some '-'⟩, ⟨['i'], ['D', 'F', 'L', 'T', '.', '1'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "2"), ("ia", "1"), ("controller", "2"), ("context", "direct")] }

def br2009_17c : Datum :=
  { id := "br2009_17c"
    source := ⟨"bejar-rezac-2009", "(17c)"⟩
    reportedIn := none
    language := "otta1242"
    primaryText := "n-waabm-ig"
    glossedTokens := [("n-waabm-ig", "1-see-3.INV")]
    glossedWords := [⟨['n', '-', 'w', 'a', 'a', 'b', 'm', '-', 'i', 'g'], ['1', '-', 's', 'e', 'e', '-', '3', '.', 'I', 'N', 'V'], [⟨['n'], ['1'], none⟩, ⟨['w', 'a', 'a', 'b', 'm'], ['s', 'e', 'e'], some '-'⟩, ⟨['i', 'g'], ['3', '.', 'I', 'N', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "3"), ("ia", "1"), ("controller", "1"), ("context", "inverse")] }

def br2009_17d : Datum :=
  { id := "br2009_17d"
    source := ⟨"bejar-rezac-2009", "(17d)"⟩
    reportedIn := none
    language := "otta1242"
    primaryText := "g-waabm-ig"
    glossedTokens := [("g-waabm-ig", "2-see-3.INV")]
    glossedWords := [⟨['g', '-', 'w', 'a', 'a', 'b', 'm', '-', 'i', 'g'], ['2', '-', 's', 'e', 'e', '-', '3', '.', 'I', 'N', 'V'], [⟨['g'], ['2'], none⟩, ⟨['w', 'a', 'a', 'b', 'm'], ['s', 'e', 'e'], some '-'⟩, ⟨['i', 'g'], ['3', '.', 'I', 'N', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "3"), ("ia", "2"), ("controller", "2"), ("context", "inverse")] }

def br2009_18a : Datum :=
  { id := "br2009_18a"
    source := ⟨"bejar-rezac-2009", "(18a)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "m-xedav-s"
    glossedTokens := [("m-xedav-s", "1.I-see-X")]
    glossedWords := [⟨['m', '-', 'x', 'e', 'd', 'a', 'v', '-', 's'], ['1', '.', 'I', '-', 's', 'e', 'e', '-', 'X'], [⟨['m'], ['1', '.', 'I'], none⟩, ⟨['x', 'e', 'd', 'a', 'v'], ['s', 'e', 'e'], some '-'⟩, ⟨['s'], ['X'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "3"), ("ia", "1"), ("controller", "1"), ("morphology", "first-cycle m-")] }

def br2009_18b : Datum :=
  { id := "br2009_18b"
    source := ⟨"bejar-rezac-2009", "(18b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "v-xedav"
    glossedTokens := [("v-xedav", "1.II-see")]
    glossedWords := [⟨['v', '-', 'x', 'e', 'd', 'a', 'v'], ['1', '.', 'I', 'I', '-', 's', 'e', 'e'], [⟨['v'], ['1', '.', 'I', 'I'], none⟩, ⟨['x', 'e', 'd', 'a', 'v'], ['s', 'e', 'e'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "1"), ("ia", "3"), ("controller", "1"), ("morphology", "second-cycle v-")] }

def br2009_29a : Datum :=
  { id := "br2009_29a"
    source := ⟨"bejar-rezac-2009", "(29a)"⟩
    reportedIn := none
    language := "kash1277"
    primaryText := "bɨ chusath tsɨ parɨna:va:n"
    glossedTokens := [("bɨ", "I.N"), ("chu-s-ath", "be.M.SG-1.SG.N-2.SG.E/A"), ("tsɨ", "you.N"), ("parɨna:va:n", "teaching")]
    glossedWords := [⟨['b', 'ɨ'], ['I', '.', 'N'], [⟨['b', 'ɨ'], ['I', '.', 'N'], none⟩]⟩, ⟨['c', 'h', 'u', '-', 's', '-', 'a', 't', 'h'], ['b', 'e', '.', 'M', '.', 'S', 'G', '-', '1', '.', 'S', 'G', '.', 'N', '-', '2', '.', 'S', 'G', '.', 'E', '/', 'A'], [⟨['c', 'h', 'u'], ['b', 'e', '.', 'M', '.', 'S', 'G'], none⟩, ⟨['s'], ['1', '.', 'S', 'G', '.', 'N'], some '-'⟩, ⟨['a', 't', 'h'], ['2', '.', 'S', 'G', '.', 'E', '/', 'A'], some '-'⟩]⟩, ⟨['t', 's', 'ɨ'], ['y', 'o', 'u', '.', 'N'], [⟨['t', 's', 'ɨ'], ['y', 'o', 'u', '.', 'N'], none⟩]⟩, ⟨['p', 'a', 'r', 'ɨ', 'n', 'a', ':', 'v', 'a', ':', 'n'], ['t', 'e', 'a', 'c', 'h', 'i', 'n', 'g'], [⟨['p', 'a', 'r', 'ɨ', 'n', 'a', 'v', 'a', 'n'], ['t', 'e', 'a', 'c', 'h', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "1"), ("ia", "2"), ("context", "direct")] }

def br2009_29b : Datum :=
  { id := "br2009_29b"
    source := ⟨"bejar-rezac-2009", "(29b)"⟩
    reportedIn := none
    language := "kash1277"
    primaryText := "tsɨ chukh me parɨna:va:n"
    glossedTokens := [("tsɨ", "you.N"), ("chu-kh", "be.M.SG-2.SG.N"), ("me", "me.D"), ("parɨna:va:n", "teaching")]
    glossedWords := [⟨['t', 's', 'ɨ'], ['y', 'o', 'u', '.', 'N'], [⟨['t', 's', 'ɨ'], ['y', 'o', 'u', '.', 'N'], none⟩]⟩, ⟨['c', 'h', 'u', '-', 'k', 'h'], ['b', 'e', '.', 'M', '.', 'S', 'G', '-', '2', '.', 'S', 'G', '.', 'N'], [⟨['c', 'h', 'u'], ['b', 'e', '.', 'M', '.', 'S', 'G'], none⟩, ⟨['k', 'h'], ['2', '.', 'S', 'G', '.', 'N'], some '-'⟩]⟩, ⟨['m', 'e'], ['m', 'e', '.', 'D'], [⟨['m', 'e'], ['m', 'e', '.', 'D'], none⟩]⟩, ⟨['p', 'a', 'r', 'ɨ', 'n', 'a', ':', 'v', 'a', ':', 'n'], ['t', 'e', 'a', 'c', 'h', 'i', 'n', 'g'], [⟨['p', 'a', 'r', 'ɨ', 'n', 'a', 'v', 'a', 'n'], ['t', 'e', 'a', 'c', 'h', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "2"), ("ia", "1"), ("context", "inverse"), ("repair", "R-Case")] }

def br2009_30a : Datum :=
  { id := "br2009_30a"
    source := ⟨"bejar-rezac-2009", "(30a)"⟩
    reportedIn := none
    language := "kash1277"
    primaryText := "su kari-y tse me hava:lɨ"
    glossedTokens := [("su", "he.N"), ("kari-y", "do.FUT-2.SG.D"), ("tse", "you.D"), ("me", "me.D"), ("hava:lɨ", "handover")]
    glossedWords := [⟨['s', 'u'], ['h', 'e', '.', 'N'], [⟨['s', 'u'], ['h', 'e', '.', 'N'], none⟩]⟩, ⟨['k', 'a', 'r', 'i', '-', 'y'], ['d', 'o', '.', 'F', 'U', 'T', '-', '2', '.', 'S', 'G', '.', 'D'], [⟨['k', 'a', 'r', 'i'], ['d', 'o', '.', 'F', 'U', 'T'], none⟩, ⟨['y'], ['2', '.', 'S', 'G', '.', 'D'], some '-'⟩]⟩, ⟨['t', 's', 'e'], ['y', 'o', 'u', '.', 'D'], [⟨['t', 's', 'e'], ['y', 'o', 'u', '.', 'D'], none⟩]⟩, ⟨['m', 'e'], ['m', 'e', '.', 'D'], [⟨['m', 'e'], ['m', 'e', '.', 'D'], none⟩]⟩, ⟨['h', 'a', 'v', 'a', ':', 'l', 'ɨ'], ['h', 'a', 'n', 'd', 'o', 'v', 'e', 'r'], [⟨['h', 'a', 'v', 'a', 'l', 'ɨ'], ['h', 'a', 'n', 'd', 'o', 'v', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "3"), ("ia", "2"), ("context", "inverse"), ("repair", "R-Case")] }

def br2009_30b : Datum :=
  { id := "br2009_30b"
    source := ⟨"bejar-rezac-2009", "(30b)"⟩
    reportedIn := none
    language := "kash1277"
    primaryText := "tsɨ yikh me hava:lɨ karnɨ təm'sɨndi dəs'"
    glossedTokens := [("tsɨ", "you.N"), ("yi-kh", "come.FUT-2.SG.N"), ("me", "me.D"), ("hava:lɨ", "handover"), ("karnɨ", "do.INF.ABL"), ("təm'sɨndi", "he.GEN"), ("dəs'", "by")]
    glossedWords := [⟨['t', 's', 'ɨ'], ['y', 'o', 'u', '.', 'N'], [⟨['t', 's', 'ɨ'], ['y', 'o', 'u', '.', 'N'], none⟩]⟩, ⟨['y', 'i', '-', 'k', 'h'], ['c', 'o', 'm', 'e', '.', 'F', 'U', 'T', '-', '2', '.', 'S', 'G', '.', 'N'], [⟨['y', 'i'], ['c', 'o', 'm', 'e', '.', 'F', 'U', 'T'], none⟩, ⟨['k', 'h'], ['2', '.', 'S', 'G', '.', 'N'], some '-'⟩]⟩, ⟨['m', 'e'], ['m', 'e', '.', 'D'], [⟨['m', 'e'], ['m', 'e', '.', 'D'], none⟩]⟩, ⟨['h', 'a', 'v', 'a', ':', 'l', 'ɨ'], ['h', 'a', 'n', 'd', 'o', 'v', 'e', 'r'], [⟨['h', 'a', 'v', 'a', 'l', 'ɨ'], ['h', 'a', 'n', 'd', 'o', 'v', 'e', 'r'], none⟩]⟩, ⟨['k', 'a', 'r', 'n', 'ɨ'], ['d', 'o', '.', 'I', 'N', 'F', '.', 'A', 'B', 'L'], [⟨['k', 'a', 'r', 'n', 'ɨ'], ['d', 'o', '.', 'I', 'N', 'F', '.', 'A', 'B', 'L'], none⟩]⟩, ⟨['t', 'ə', 'm', '\'', 's', 'ɨ', 'n', 'd', 'i'], ['h', 'e', '.', 'G', 'E', 'N'], [⟨['t', 'ə', 'm', '\'', 's', 'ɨ', 'n', 'd', 'i'], ['h', 'e', '.', 'G', 'E', 'N'], none⟩]⟩, ⟨['d', 'ə', 's', '\''], ['b', 'y'], [⟨['d', 'ə', 's', '\''], ['b', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "passivization"), ("result", "R-Case disappears")] }

def br2009_31a : Datum :=
  { id := "br2009_31a"
    source := ⟨"bejar-rezac-2009", "(31a)"⟩
    reportedIn := none
    language := "kash1277"
    primaryText := "tsɨ vuch-a-kh me"
    glossedTokens := [("tsɨ", "you.N"), ("vuch-a-kh", "see-2.SG-2.SG.N"), ("me", "me.D")]
    glossedWords := [⟨['t', 's', 'ɨ'], ['y', 'o', 'u', '.', 'N'], [⟨['t', 's', 'ɨ'], ['y', 'o', 'u', '.', 'N'], none⟩]⟩, ⟨['v', 'u', 'c', 'h', '-', 'a', '-', 'k', 'h'], ['s', 'e', 'e', '-', '2', '.', 'S', 'G', '-', '2', '.', 'S', 'G', '.', 'N'], [⟨['v', 'u', 'c', 'h'], ['s', 'e', 'e'], none⟩, ⟨['a'], ['2', '.', 'S', 'G'], some '-'⟩, ⟨['k', 'h'], ['2', '.', 'S', 'G', '.', 'N'], some '-'⟩]⟩, ⟨['m', 'e'], ['m', 'e', '.', 'D'], [⟨['m', 'e'], ['m', 'e', '.', 'D'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ea", "2"), ("ia", "1"), ("context", "inverse"), ("repair", "R-Case")] }

def all : List Datum := [br2009_2a, br2009_2b, br2009_2c, br2009_2d, br2009_3, br2009_15, br2009_15_ni, br2009_t9_3_1, br2009_t9_1_2, br2009_t9_1_3, br2009_t9_2_1, br2009_t9_2_1pl, br2009_t9_2_3, br2009_t9_1pl_2, br2009_t9_1pl_3, br2009_t9_3_2, br2009_t9_3_1pl, br2009_t9_3_3, br2009_10, br2009_17a, br2009_17b, br2009_17c, br2009_17d, br2009_18a, br2009_18b, br2009_29a, br2009_29b, br2009_30a, br2009_30b, br2009_31a]

end BejarRezac2009.Examples
