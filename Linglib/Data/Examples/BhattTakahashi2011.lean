module

public import Linglib.Data.Examples.Schema

/-!
# `BhattTakahashi2011` — typed example data

Auto-generated from `Linglib/Data/Examples/BhattTakahashi2011.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BhattTakahashi2011.Examples`.
-/

@[expose] public section

namespace BhattTakahashi2011.Examples

def ex11a : Datum :=
  { id := "bhatttakahashi2011_ex11a"
    source := ⟨"bhatt-takahashi-2011", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More people introduced him_i to Mary than to John_i's mother."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "binding"), ("pron_c_commands_associate", "yes")] }

def ex11b : Datum :=
  { id := "bhatttakahashi2011_ex11b"
    source := ⟨"bhatt-takahashi-2011", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary introduced him_i to more people than John_i's mother."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "binding"), ("pron_c_commands_associate", "no")] }

def ex12a : Datum :=
  { id := "bhatttakahashi2011_ex12a"
    source := ⟨"bhatt-takahashi-2011", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More people talked to him_i about Sally than about Peter_i's sister."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "binding"), ("pron_c_commands_associate", "yes")] }

def ex12b : Datum :=
  { id := "bhatttakahashi2011_ex12b"
    source := ⟨"bhatt-takahashi-2011", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More people talked to Sally about him_i than to Peter_i's sister."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "binding"), ("pron_c_commands_associate", "no")] }

def ex13a : Datum :=
  { id := "bhatttakahashi2011_ex13a"
    source := ⟨"bhatt-takahashi-2011", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More people expect him_i to overtake Sally than Peter_i's sister."
    glossedTokens := []
    context := "Peter, Peter's sister, and Sally are taking part in a race; people are betting on their prospects."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "binding"), ("pron_c_commands_associate", "yes")] }

def ex13b : Datum :=
  { id := "bhatttakahashi2011_ex13b"
    source := ⟨"bhatt-takahashi-2011", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More people expect Sally to overtake him_i than Peter_i's sister."
    glossedTokens := []
    context := "Peter, Peter's sister, and Sally are taking part in a race; people are betting on their prospects."
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "binding"), ("pron_c_commands_associate", "no")] }

def ex35 : Datum :=
  { id := "bhatttakahashi2011_ex35"
    source := ⟨"bhatt-takahashi-2011", "(35)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "Atif-ne Ravi-kii behen-kii foto-se us-ko Mohan-kii behen-kii foto zyaadaa baar dikhaa-ii."
    glossedTokens := [("Atif-ne", "Atif-ERG"), ("Ravi-kii", "Ravi-GEN"), ("behen-kii", "sister-GEN"), ("foto-se", "picture-than"), ("us-ko", "he-DAT"), ("Mohan-kii", "Mohan-GEN"), ("behen-kii", "sister-GEN"), ("foto", "picture"), ("zyaadaa", "more"), ("baar", "times"), ("dikhaa-ii", "show-PFV.F")]
    glossedWords := [⟨['A', 't', 'i', 'f', '-', 'n', 'e'], ['A', 't', 'i', 'f', '-', 'E', 'R', 'G'], [⟨['A', 't', 'i', 'f'], ['A', 't', 'i', 'f'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['R', 'a', 'v', 'i', '-', 'k', 'i', 'i'], ['R', 'a', 'v', 'i', '-', 'G', 'E', 'N'], [⟨['R', 'a', 'v', 'i'], ['R', 'a', 'v', 'i'], none⟩, ⟨['k', 'i', 'i'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['b', 'e', 'h', 'e', 'n', '-', 'k', 'i', 'i'], ['s', 'i', 's', 't', 'e', 'r', '-', 'G', 'E', 'N'], [⟨['b', 'e', 'h', 'e', 'n'], ['s', 'i', 's', 't', 'e', 'r'], none⟩, ⟨['k', 'i', 'i'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['f', 'o', 't', 'o', '-', 's', 'e'], ['p', 'i', 'c', 't', 'u', 'r', 'e', '-', 't', 'h', 'a', 'n'], [⟨['f', 'o', 't', 'o'], ['p', 'i', 'c', 't', 'u', 'r', 'e'], none⟩, ⟨['s', 'e'], ['t', 'h', 'a', 'n'], some '-'⟩]⟩, ⟨['u', 's', '-', 'k', 'o'], ['h', 'e', '-', 'D', 'A', 'T'], [⟨['u', 's'], ['h', 'e'], none⟩, ⟨['k', 'o'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['M', 'o', 'h', 'a', 'n', '-', 'k', 'i', 'i'], ['M', 'o', 'h', 'a', 'n', '-', 'G', 'E', 'N'], [⟨['M', 'o', 'h', 'a', 'n'], ['M', 'o', 'h', 'a', 'n'], none⟩, ⟨['k', 'i', 'i'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['b', 'e', 'h', 'e', 'n', '-', 'k', 'i', 'i'], ['s', 'i', 's', 't', 'e', 'r', '-', 'G', 'E', 'N'], [⟨['b', 'e', 'h', 'e', 'n'], ['s', 'i', 's', 't', 'e', 'r'], none⟩, ⟨['k', 'i', 'i'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['f', 'o', 't', 'o'], ['p', 'i', 'c', 't', 'u', 'r', 'e'], [⟨['f', 'o', 't', 'o'], ['p', 'i', 'c', 't', 'u', 'r', 'e'], none⟩]⟩, ⟨['z', 'y', 'a', 'a', 'd', 'a', 'a'], ['m', 'o', 'r', 'e'], [⟨['z', 'y', 'a', 'a', 'd', 'a', 'a'], ['m', 'o', 'r', 'e'], none⟩]⟩, ⟨['b', 'a', 'a', 'r'], ['t', 'i', 'm', 'e', 's'], [⟨['b', 'a', 'a', 'r'], ['t', 'i', 'm', 'e', 's'], none⟩]⟩, ⟨['d', 'i', 'k', 'h', 'a', 'a', '-', 'i', 'i'], ['s', 'h', 'o', 'w', '-', 'P', 'F', 'V', '.', 'F'], [⟨['d', 'i', 'k', 'h', 'a', 'a'], ['s', 'h', 'o', 'w'], none⟩, ⟨['i', 'i'], ['P', 'F', 'V', '.', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "binding"), ("pron_c_commands_associate", "yes")] }

def ex43a : Datum :=
  { id := "bhatttakahashi2011_ex43a"
    source := ⟨"bhatt-takahashi-2011", "(43a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Craige assigned every first year student more papers than every second year student."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "scope"), ("qp_base_c_commands_degree_trace", "yes"), ("than_internal_scope", "unavailable")] }

def ex43b : Datum :=
  { id := "bhatttakahashi2011_ex43b"
    source := ⟨"bhatt-takahashi-2011", "(43b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Craige assigned more students every paper by Hellan than every paper by Klein."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "scope"), ("qp_base_c_commands_degree_trace", "no"), ("than_internal_scope", "available")] }

def ex40 : Datum :=
  { id := "bhatttakahashi2011_ex40"
    source := ⟨"bhatt-takahashi-2011", "(40)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "har syntax paper har semantics paper-se zyaadaa logõ-ne paṛh-aa."
    glossedTokens := [("har", "every"), ("syntax", "syntax"), ("paper", "paper"), ("har", "every"), ("semantics", "semantics"), ("paper-se", "paper-than"), ("zyaadaa", "more"), ("logõ-ne", "people-ERG"), ("paṛh-aa", "read-PFV")]
    glossedWords := [⟨['h', 'a', 'r'], ['e', 'v', 'e', 'r', 'y'], [⟨['h', 'a', 'r'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['s', 'y', 'n', 't', 'a', 'x'], ['s', 'y', 'n', 't', 'a', 'x'], [⟨['s', 'y', 'n', 't', 'a', 'x'], ['s', 'y', 'n', 't', 'a', 'x'], none⟩]⟩, ⟨['p', 'a', 'p', 'e', 'r'], ['p', 'a', 'p', 'e', 'r'], [⟨['p', 'a', 'p', 'e', 'r'], ['p', 'a', 'p', 'e', 'r'], none⟩]⟩, ⟨['h', 'a', 'r'], ['e', 'v', 'e', 'r', 'y'], [⟨['h', 'a', 'r'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['s', 'e', 'm', 'a', 'n', 't', 'i', 'c', 's'], ['s', 'e', 'm', 'a', 'n', 't', 'i', 'c', 's'], [⟨['s', 'e', 'm', 'a', 'n', 't', 'i', 'c', 's'], ['s', 'e', 'm', 'a', 'n', 't', 'i', 'c', 's'], none⟩]⟩, ⟨['p', 'a', 'p', 'e', 'r', '-', 's', 'e'], ['p', 'a', 'p', 'e', 'r', '-', 't', 'h', 'a', 'n'], [⟨['p', 'a', 'p', 'e', 'r'], ['p', 'a', 'p', 'e', 'r'], none⟩, ⟨['s', 'e'], ['t', 'h', 'a', 'n'], some '-'⟩]⟩, ⟨['z', 'y', 'a', 'a', 'd', 'a', 'a'], ['m', 'o', 'r', 'e'], [⟨['z', 'y', 'a', 'a', 'd', 'a', 'a'], ['m', 'o', 'r', 'e'], none⟩]⟩, ⟨['l', 'o', 'g', 'õ', '-', 'n', 'e'], ['p', 'e', 'o', 'p', 'l', 'e', '-', 'E', 'R', 'G'], [⟨['l', 'o', 'g', 'õ'], ['p', 'e', 'o', 'p', 'l', 'e'], none⟩, ⟨['n', 'e'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['p', 'a', 'ṛ', 'h', '-', 'a', 'a'], ['r', 'e', 'a', 'd', '-', 'P', 'F', 'V'], [⟨['p', 'a', 'ṛ', 'h'], ['r', 'e', 'a', 'd'], none⟩, ⟨['a', 'a'], ['P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("diagnostic", "scope"), ("qp_base_c_commands_degree_trace", "no"), ("than_internal_scope", "unavailable")] }

def all : List Datum := [ex11a, ex11b, ex12a, ex12b, ex13a, ex13b, ex35, ex43a, ex43b, ex40]

end BhattTakahashi2011.Examples
