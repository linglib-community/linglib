module

public import Linglib.Data.Examples.Schema

/-!
# `Bobaljik2000` — typed example data

Auto-generated from `Linglib/Data/Examples/Bobaljik2000.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Bobaljik2000.Examples`.
-/

@[expose] public section

namespace Bobaljik2000.Examples

def ex_9a : Datum :=
  { id := "bobaljik2000_9a"
    source := ⟨"bobaljik-2000", "(9a)"⟩
    reportedIn := none
    language := "itel1242"
    primaryText := "t’-əŋkzu-s-čeʔn"
    glossedTokens := [("t’-əŋkzu-s-čeʔn", "1S:SU-help-PRES-1>3P:OB")]
    glossedWords := [⟨['t', '’', '-', 'ə', 'ŋ', 'k', 'z', 'u', '-', 's', '-', 'č', 'e', 'ʔ', 'n'], ['1', 'S', ':', 'S', 'U', '-', 'h', 'e', 'l', 'p', '-', 'P', 'R', 'E', 'S', '-', '1', '>', '3', 'P', ':', 'O', 'B'], [⟨['t', '’'], ['1', 'S', ':', 'S', 'U'], none⟩, ⟨['ə', 'ŋ', 'k', 'z', 'u'], ['h', 'e', 'l', 'p'], some '-'⟩, ⟨['s'], ['P', 'R', 'E', 'S'], some '-'⟩, ⟨['č', 'e', 'ʔ', 'n'], ['1', '>', '3', 'P', ':', 'O', 'B'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "əŋkzu"), ("rootClass", "I"), ("subj", "1sg"), ("obj", "3pl"), ("m1", "t"), ("m2", "əŋkzu"), ("m3", "s"), ("m4", "čeʔn")] }

def ex_9b : Datum :=
  { id := "bobaljik2000_9b"
    source := ⟨"bobaljik-2000", "(9b)"⟩
    reportedIn := none
    language := "itel1242"
    primaryText := "t-tɸ-s-ki-čeʔn"
    glossedTokens := [("t-tɸ-s-ki-čeʔn", "1S:SU-bring-PRES-II-1>3P:OB")]
    glossedWords := [⟨['t', '-', 't', 'ɸ', '-', 's', '-', 'k', 'i', '-', 'č', 'e', 'ʔ', 'n'], ['1', 'S', ':', 'S', 'U', '-', 'b', 'r', 'i', 'n', 'g', '-', 'P', 'R', 'E', 'S', '-', 'I', 'I', '-', '1', '>', '3', 'P', ':', 'O', 'B'], [⟨['t'], ['1', 'S', ':', 'S', 'U'], none⟩, ⟨['t', 'ɸ'], ['b', 'r', 'i', 'n', 'g'], some '-'⟩, ⟨['s'], ['P', 'R', 'E', 'S'], some '-'⟩, ⟨['k', 'i'], ['I', 'I'], some '-'⟩, ⟨['č', 'e', 'ʔ', 'n'], ['1', '>', '3', 'P', ':', 'O', 'B'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "tɸ"), ("rootClass", "II"), ("subj", "1sg"), ("obj", "3pl"), ("m1", "t"), ("m2", "tɸ"), ("m3", "s"), ("m4", "ki"), ("m5", "čeʔn")] }

def ex_10a : Datum :=
  { id := "bobaljik2000_10a"
    source := ⟨"bobaljik-2000", "(10a)"⟩
    reportedIn := none
    language := "itel1242"
    primaryText := "əlčqu-z-in"
    glossedTokens := [("əlčqu-z-in", "see-PRES-2S>3S:OB")]
    glossedWords := [⟨['ə', 'l', 'č', 'q', 'u', '-', 'z', '-', 'i', 'n'], ['s', 'e', 'e', '-', 'P', 'R', 'E', 'S', '-', '2', 'S', '>', '3', 'S', ':', 'O', 'B'], [⟨['ə', 'l', 'č', 'q', 'u'], ['s', 'e', 'e'], none⟩, ⟨['z'], ['P', 'R', 'E', 'S'], some '-'⟩, ⟨['i', 'n'], ['2', 'S', '>', '3', 'S', ':', 'O', 'B'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "əlčqu"), ("rootClass", "I"), ("subj", "2sg"), ("obj", "3sg"), ("m1", "əlčqu"), ("m2", "s"), ("m3", "in")] }

def ex_10b : Datum :=
  { id := "bobaljik2000_10b"
    source := ⟨"bobaljik-2000", "(10b)"⟩
    reportedIn := none
    language := "itel1242"
    primaryText := "tɸ-s-čŋ-in"
    glossedTokens := [("tɸ-s-čŋ-in", "bring-PRES-II-2S>3S:OB")]
    glossedWords := [⟨['t', 'ɸ', '-', 's', '-', 'č', 'ŋ', '-', 'i', 'n'], ['b', 'r', 'i', 'n', 'g', '-', 'P', 'R', 'E', 'S', '-', 'I', 'I', '-', '2', 'S', '>', '3', 'S', ':', 'O', 'B'], [⟨['t', 'ɸ'], ['b', 'r', 'i', 'n', 'g'], none⟩, ⟨['s'], ['P', 'R', 'E', 'S'], some '-'⟩, ⟨['č', 'ŋ'], ['I', 'I'], some '-'⟩, ⟨['i', 'n'], ['2', 'S', '>', '3', 'S', ':', 'O', 'B'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "tɸ"), ("rootClass", "II"), ("subj", "2sg"), ("obj", "3sg"), ("m1", "tɸ"), ("m2", "s"), ("m3", "čŋ"), ("m4", "in")] }

def ex_19b : Datum :=
  { id := "bobaljik2000_19b"
    source := ⟨"bobaljik-2000", "(19b)"⟩
    reportedIn := none
    language := "chuk1273"
    primaryText := "ənan ɣət ne-ɬʔu-ɣət"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "ɬʔu"), ("subj", "3sg"), ("obj", "2sg"), ("m1", "ne"), ("m2", "ɬʔu"), ("m3", "ɣət")] }

def ex_19c : Datum :=
  { id := "bobaljik2000_19c"
    source := ⟨"bobaljik-2000", "(19c)"⟩
    reportedIn := none
    language := "chuk1273"
    primaryText := "ənan ətɬjon ɬʔu-nin"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "ɬʔu"), ("subj", "3sg"), ("obj", "3sg"), ("m1", "ɬʔu"), ("m2", "nin")] }

def ex_19d : Datum :=
  { id := "bobaljik2000_19d"
    source := ⟨"bobaljik-2000", "(19d)"⟩
    reportedIn := none
    language := "chuk1273"
    primaryText := "ənan muri ne-ɬʔu-mək"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "ɬʔu"), ("subj", "3sg"), ("obj", "1pl"), ("m1", "ne"), ("m2", "ɬʔu"), ("m3", "mək")] }

def ex_19e : Datum :=
  { id := "bobaljik2000_19e"
    source := ⟨"bobaljik-2000", "(19e)"⟩
    reportedIn := none
    language := "chuk1273"
    primaryText := "ənan turi ne-ɬʔu-tək"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "ɬʔu"), ("subj", "3sg"), ("obj", "2pl"), ("m1", "ne"), ("m2", "ɬʔu"), ("m3", "tək")] }

def ex_19f : Datum :=
  { id := "bobaljik2000_19f"
    source := ⟨"bobaljik-2000", "(19f)"⟩
    reportedIn := none
    language := "chuk1273"
    primaryText := "ənan ətri ɬʔu-ninet"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "ɬʔu"), ("subj", "3sg"), ("obj", "3pl"), ("m1", "ɬʔu"), ("m2", "ninet")] }

def ex_19g : Datum :=
  { id := "bobaljik2000_19g"
    source := ⟨"bobaljik-2000", "(19g)"⟩
    reportedIn := none
    language := "chuk1273"
    primaryText := "ərɣənan ɣəm ne-ɬʔu-ɣəm"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "ɬʔu"), ("subj", "3pl"), ("obj", "1sg"), ("m1", "ne"), ("m2", "ɬʔu"), ("m3", "ɣəm")] }

def ex_19h : Datum :=
  { id := "bobaljik2000_19h"
    source := ⟨"bobaljik-2000", "(19h)"⟩
    reportedIn := none
    language := "chuk1273"
    primaryText := "ərɣənan ɣət ne-ɬʔu-ɣət"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "ɬʔu"), ("subj", "3pl"), ("obj", "2sg"), ("m1", "ne"), ("m2", "ɬʔu"), ("m3", "ɣət")] }

def ex_19i : Datum :=
  { id := "bobaljik2000_19i"
    source := ⟨"bobaljik-2000", "(19i)"⟩
    reportedIn := none
    language := "chuk1273"
    primaryText := "ərɣənan ətɬjon ne-ɬʔu-ɣʔen"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "ɬʔu"), ("subj", "3pl"), ("obj", "3sg"), ("m1", "ne"), ("m2", "ɬʔu"), ("m3", "ɣʔen")] }

def ex_19j : Datum :=
  { id := "bobaljik2000_19j"
    source := ⟨"bobaljik-2000", "(19j)"⟩
    reportedIn := none
    language := "chuk1273"
    primaryText := "ərɣənan muri ne-ɬʔu-mək"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "ɬʔu"), ("subj", "3pl"), ("obj", "1pl"), ("m1", "ne"), ("m2", "ɬʔu"), ("m3", "mək")] }

def ex_19k : Datum :=
  { id := "bobaljik2000_19k"
    source := ⟨"bobaljik-2000", "(19k)"⟩
    reportedIn := none
    language := "chuk1273"
    primaryText := "ərɣənan turi ne-ɬʔu-tək"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "ɬʔu"), ("subj", "3pl"), ("obj", "2pl"), ("m1", "ne"), ("m2", "ɬʔu"), ("m3", "tək")] }

def ex_19l : Datum :=
  { id := "bobaljik2000_19l"
    source := ⟨"bobaljik-2000", "(19l)"⟩
    reportedIn := none
    language := "chuk1273"
    primaryText := "ərɣənan ətri ne-ɬʔu-net"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "ɬʔu"), ("subj", "3pl"), ("obj", "3pl"), ("m1", "ne"), ("m2", "ɬʔu"), ("m3", "net")] }

def ex_27 : Datum :=
  { id := "bobaljik2000_27"
    source := ⟨"bobaljik-2000", "(27)"⟩
    reportedIn := none
    language := "chuk1273"
    primaryText := "ənan ɣənəkə ənqen ne-jəl-ɣət"
    glossedTokens := [("ənan", "3SG:ERG"), ("ɣənəkə", "2SG:DAT"), ("ənqen", "sth.(ABS)"), ("ne-jəl-ɣət", "3:SU-give-2S:OB")]
    glossedWords := [⟨['ə', 'n', 'a', 'n'], ['3', 'S', 'G', ':', 'E', 'R', 'G'], [⟨['ə', 'n', 'a', 'n'], ['3', 'S', 'G', ':', 'E', 'R', 'G'], none⟩]⟩, ⟨['ɣ', 'ə', 'n', 'ə', 'k', 'ə'], ['2', 'S', 'G', ':', 'D', 'A', 'T'], [⟨['ɣ', 'ə', 'n', 'ə', 'k', 'ə'], ['2', 'S', 'G', ':', 'D', 'A', 'T'], none⟩]⟩, ⟨['ə', 'n', 'q', 'e', 'n'], ['s', 't', 'h', '.', '(', 'A', 'B', 'S', ')'], [⟨['ə', 'n', 'q', 'e', 'n'], ['s', 't', 'h', '.', '(', 'A', 'B', 'S', ')'], none⟩]⟩, ⟨['n', 'e', '-', 'j', 'ə', 'l', '-', 'ɣ', 'ə', 't'], ['3', ':', 'S', 'U', '-', 'g', 'i', 'v', 'e', '-', '2', 'S', ':', 'O', 'B'], [⟨['n', 'e'], ['3', ':', 'S', 'U'], none⟩, ⟨['j', 'ə', 'l'], ['g', 'i', 'v', 'e'], some '-'⟩, ⟨['ɣ', 'ə', 't'], ['2', 'S', ':', 'O', 'B'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "jəl"), ("subj", "3sg"), ("obj", "3sg"), ("io", "2sg"), ("m1", "ne"), ("m2", "jəl"), ("m3", "ɣət")] }

def all : List Datum := [ex_9a, ex_9b, ex_10a, ex_10b, ex_19b, ex_19c, ex_19d, ex_19e, ex_19f, ex_19g, ex_19h, ex_19i, ex_19j, ex_19k, ex_19l, ex_27]

end Bobaljik2000.Examples
