module

public import Linglib.Data.Examples.Schema

/-!
# `Belth2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Belth2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Belth2026.Examples`.
-/

@[expose] public section

namespace Belth2026.Examples

def ex_53a : Datum :=
  { id := "belth2026_53a"
    source := ⟨"belth-2026", "(53a)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "nav-alis"
    glossedTokens := [("nav-alis", "naval")]
    glossedWords := [⟨['n', 'a', 'v', '-', 'a', 'l', 'i', 's'], ['n', 'a', 'v', 'a', 'l'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("suffix", "-alis"), ("analysis", "default l: tier-preceding consonant not lateral")] }

def ex_53b1 : Datum :=
  { id := "belth2026_53b1"
    source := ⟨"belth-2026", "(53b)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "popul-aris"
    glossedTokens := [("popul-aris", "popular")]
    glossedWords := [⟨['p', 'o', 'p', 'u', 'l', '-', 'a', 'r', 'i', 's'], ['p', 'o', 'p', 'u', 'l', 'a', 'r'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("suffix", "-aris"), ("analysis", "dissimilation from tier-adjacent stem l")] }

def ex_53b2 : Datum :=
  { id := "belth2026_53b2"
    source := ⟨"belth-2026", "(53b)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "lun-aris"
    glossedTokens := [("lun-aris", "lunar")]
    glossedWords := [⟨['l', 'u', 'n', '-', 'a', 'r', 'i', 's'], ['l', 'u', 'n', 'a', 'r'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("suffix", "-aris"), ("analysis", "dissimilation across the coronal n")] }

def ex_53c : Datum :=
  { id := "belth2026_53c"
    source := ⟨"belth-2026", "(53c)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "flor-alis"
    glossedTokens := [("flor-alis", "floral")]
    glossedWords := [⟨['f', 'l', 'o', 'r', '-', 'a', 'l', 'i', 's'], ['f', 'l', 'o', 'r', 'a', 'l'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("suffix", "-alis"), ("analysis", "blocked by intervening r")] }

def ex_53d1 : Datum :=
  { id := "belth2026_53d1"
    source := ⟨"belth-2026", "(53d)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "pluvi-alis"
    glossedTokens := [("pluvi-alis", "rainy")]
    glossedWords := [⟨['p', 'l', 'u', 'v', 'i', '-', 'a', 'l', 'i', 's'], ['r', 'a', 'i', 'n', 'y'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("suffix", "-alis"), ("analysis", "blocked by an intervening non-coronal consonant")] }

def ex_53d2 : Datum :=
  { id := "belth2026_53d2"
    source := ⟨"belth-2026", "(53d)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "leg-alis"
    glossedTokens := [("leg-alis", "legal")]
    glossedWords := [⟨['l', 'e', 'g', '-', 'a', 'l', 'i', 's'], ['l', 'e', 'g', 'a', 'l'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("suffix", "-alis"), ("analysis", "blocked by intervening g")] }

def ex_46 : Datum :=
  { id := "belth2026_46"
    source := ⟨"belth-2026", "(46)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "dɑl-lɑr-ɯn / jer-ler-in / ip-ler-in"
    glossedTokens := [("dɑl-lɑr-ɯn", "branch-PL-GEN"), ("jer-ler-in", "place-PL-GEN"), ("ip-ler-in", "rope-PL-GEN")]
    glossedWords := [⟨['d', 'ɑ', 'l', '-', 'l', 'ɑ', 'r', '-', 'ɯ', 'n'], ['b', 'r', 'a', 'n', 'c', 'h', '-', 'P', 'L', '-', 'G', 'E', 'N'], [⟨['d', 'ɑ', 'l'], ['b', 'r', 'a', 'n', 'c', 'h'], none⟩, ⟨['l', 'ɑ', 'r'], ['P', 'L'], some '-'⟩, ⟨['ɯ', 'n'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['j', 'e', 'r', '-', 'l', 'e', 'r', '-', 'i', 'n'], ['p', 'l', 'a', 'c', 'e', '-', 'P', 'L', '-', 'G', 'E', 'N'], [⟨['j', 'e', 'r'], ['p', 'l', 'a', 'c', 'e'], none⟩, ⟨['l', 'e', 'r'], ['P', 'L'], some '-'⟩, ⟨['i', 'n'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['i', 'p', '-', 'l', 'e', 'r', '-', 'i', 'n'], ['r', 'o', 'p', 'e', '-', 'P', 'L', '-', 'G', 'E', 'N'], [⟨['i', 'p'], ['r', 'o', 'p', 'e'], none⟩, ⟨['l', 'e', 'r'], ['P', 'L'], some '-'⟩, ⟨['i', 'n'], ['G', 'E', 'N'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("process", "backness harmony"), ("tier", "vowels")] }

def ex_47 : Datum :=
  { id := "belth2026_47"
    source := ⟨"belth-2026", "(47a)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "ip-in / jyz-yn / kɯz-ɯn / buz-un"
    glossedTokens := [("ip-in", "rope-GEN"), ("jyz-yn", "face-GEN"), ("kɯz-ɯn", "girl-GEN"), ("buz-un", "ice-GEN")]
    glossedWords := [⟨['i', 'p', '-', 'i', 'n'], ['r', 'o', 'p', 'e', '-', 'G', 'E', 'N'], [⟨['i', 'p'], ['r', 'o', 'p', 'e'], none⟩, ⟨['i', 'n'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['j', 'y', 'z', '-', 'y', 'n'], ['f', 'a', 'c', 'e', '-', 'G', 'E', 'N'], [⟨['j', 'y', 'z'], ['f', 'a', 'c', 'e'], none⟩, ⟨['y', 'n'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['k', 'ɯ', 'z', '-', 'ɯ', 'n'], ['g', 'i', 'r', 'l', '-', 'G', 'E', 'N'], [⟨['k', 'ɯ', 'z'], ['g', 'i', 'r', 'l'], none⟩, ⟨['ɯ', 'n'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['b', 'u', 'z', '-', 'u', 'n'], ['i', 'c', 'e', '-', 'G', 'E', 'N'], [⟨['b', 'u', 'z'], ['i', 'c', 'e'], none⟩, ⟨['u', 'n'], ['G', 'E', 'N'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("process", "secondary rounding harmony"), ("target", "high vowels only")] }

def ex_51 : Datum :=
  { id := "belth2026_51"
    source := ⟨"belth-2026", "(51)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "pøytæ-næ / poutɑ-nɑ / koti-nɑ / velje-næ"
    glossedTokens := [("pøytæ-næ", "table-ESS"), ("poutɑ-nɑ", "fine.weather-ESS"), ("koti-nɑ", "home-ESS"), ("velje-næ", "road-ESS")]
    glossedWords := [⟨['p', 'ø', 'y', 't', 'æ', '-', 'n', 'æ'], ['t', 'a', 'b', 'l', 'e', '-', 'E', 'S', 'S'], [⟨['p', 'ø', 'y', 't', 'æ'], ['t', 'a', 'b', 'l', 'e'], none⟩, ⟨['n', 'æ'], ['E', 'S', 'S'], some '-'⟩]⟩, ⟨['p', 'o', 'u', 't', 'ɑ', '-', 'n', 'ɑ'], ['f', 'i', 'n', 'e', '.', 'w', 'e', 'a', 't', 'h', 'e', 'r', '-', 'E', 'S', 'S'], [⟨['p', 'o', 'u', 't', 'ɑ'], ['f', 'i', 'n', 'e', '.', 'w', 'e', 'a', 't', 'h', 'e', 'r'], none⟩, ⟨['n', 'ɑ'], ['E', 'S', 'S'], some '-'⟩]⟩, ⟨['k', 'o', 't', 'i', '-', 'n', 'ɑ'], ['h', 'o', 'm', 'e', '-', 'E', 'S', 'S'], [⟨['k', 'o', 't', 'i'], ['h', 'o', 'm', 'e'], none⟩, ⟨['n', 'ɑ'], ['E', 'S', 'S'], some '-'⟩]⟩, ⟨['v', 'e', 'l', 'j', 'e', '-', 'n', 'æ'], ['r', 'o', 'a', 'd', '-', 'E', 'S', 'S'], [⟨['v', 'e', 'l', 'j', 'e'], ['r', 'o', 'a', 'd'], none⟩, ⟨['n', 'æ'], ['E', 'S', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("process", "backness harmony"), ("neutral vowels", "i, e off the tier"), ("default", "front when only neutral vowels precede")] }

def all : List Datum := [ex_53a, ex_53b1, ex_53b2, ex_53c, ex_53d1, ex_53d2, ex_46, ex_47, ex_51]

end Belth2026.Examples
