module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Baker1985` — typed example data

Auto-generated from `Linglib/Data/Examples/Baker1985.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Baker1985.Examples`.
-/

@[expose] public section

namespace Baker1985.Examples

def chamorro_15a : Datum :=
  { id := "baker1985_chamorro_15a"
    source := ⟨"gibson-1980", "(15a)"⟩
    reportedIn := some ⟨"baker-1985", "(15a)"⟩
    language := "cham1312"
    primaryText := "Man-dikiki'."
    glossedTokens := [("Man-dikiki'", "PL-small")]
    glossedWords := [⟨['M', 'a', 'n', '-', 'd', 'i', 'k', 'i', 'k', 'i', '\''], ['P', 'L', '-', 's', 'm', 'a', 'l', 'l'], [⟨['M', 'a', 'n'], ['P', 'L'], none⟩, ⟨['d', 'i', 'k', 'i', 'k', 'i', '\''], ['s', 'm', 'a', 'l', 'l'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "small"), ("valence", "intransitive"), ("agreesWith", "surface subject"), ("m1", "PL"), ("f1", "man"), ("m2", "small"), ("f2", "dikiki'")] }

def chamorro_15b : Datum :=
  { id := "baker1985_chamorro_15b"
    source := ⟨"gibson-1980", "(15b)"⟩
    reportedIn := some ⟨"baker-1985", "(15b)"⟩
    language := "cham1312"
    primaryText := "Para#u#fan-s-in-aolak i famagu'un gi as tata-n-niha."
    glossedTokens := [("Para#u#fan-s-in-aolak", "IRR-3PL.SBJ-PL-PASS-spank"), ("i", "the"), ("famagu'un", "children"), ("gi as", "OBL"), ("tata-n-niha", "father-their")]
    glossedWords := [⟨['P', 'a', 'r', 'a', '#', 'u', '#', 'f', 'a', 'n', '-', 's', '-', 'i', 'n', '-', 'a', 'o', 'l', 'a', 'k'], ['I', 'R', 'R', '-', '3', 'P', 'L', '.', 'S', 'B', 'J', '-', 'P', 'L', '-', 'P', 'A', 'S', 'S', '-', 's', 'p', 'a', 'n', 'k'], []⟩, ⟨['i'], ['t', 'h', 'e'], [⟨['i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['f', 'a', 'm', 'a', 'g', 'u', '\'', 'u', 'n'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], [⟨['f', 'a', 'm', 'a', 'g', 'u', '\'', 'u', 'n'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], none⟩]⟩, ⟨['g', 'i', ' ', 'a', 's'], ['O', 'B', 'L'], [⟨['g', 'i', ' ', 'a', 's'], ['O', 'B', 'L'], none⟩]⟩, ⟨['t', 'a', 't', 'a', '-', 'n', '-', 'n', 'i', 'h', 'a'], ['f', 'a', 't', 'h', 'e', 'r', '-', 't', 'h', 'e', 'i', 'r'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "spank"), ("valence", "transitive"), ("agreesWith", "surface subject"), ("m1", "IRR"), ("f1", "para"), ("m2", "3PL.SBJ"), ("f2", "u"), ("m3", "PL"), ("f3", "fan"), ("m4", "PASS"), ("f4", "in"), ("m5", "spank"), ("f5", "saolak")] }

def chamorro_15c : Datum :=
  { id := "baker1985_chamorro_15c"
    source := ⟨"gibson-1980", "(15c)"⟩
    reportedIn := some ⟨"baker-1985", "(15c)"⟩
    language := "cham1312"
    primaryText := "Hu#na'-fan-otchu siha."
    glossedTokens := [("Hu#na'-fan-otchu", "1SG.SBJ-CAUS-PL-eat"), ("siha", "them")]
    glossedWords := [⟨['H', 'u', '#', 'n', 'a', '\'', '-', 'f', 'a', 'n', '-', 'o', 't', 'c', 'h', 'u'], ['1', 'S', 'G', '.', 'S', 'B', 'J', '-', 'C', 'A', 'U', 'S', '-', 'P', 'L', '-', 'e', 'a', 't'], []⟩, ⟨['s', 'i', 'h', 'a'], ['t', 'h', 'e', 'm'], [⟨['s', 'i', 'h', 'a'], ['t', 'h', 'e', 'm'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "eat"), ("valence", "intransitive"), ("agreesWith", "semantic subject"), ("m1", "1SG.SBJ"), ("f1", "hu"), ("m2", "CAUS"), ("f2", "na'"), ("m3", "PL"), ("f3", "fan"), ("m4", "eat"), ("f4", "otchu")] }

def chamorro_25 : Datum :=
  { id := "baker1985_chamorro_25"
    source := ⟨"gibson-1980", "(25)"⟩
    reportedIn := some ⟨"baker-1985", "(25)"⟩
    language := "cham1312"
    primaryText := "Hu#na'-fan-s-in-aolak i famagu'un gi as tata-n-niha."
    glossedTokens := [("Hu#na'-fan-s-in-aolak", "1SG.SBJ-CAUS-PL-PASS-spank"), ("i famagu'un", "children"), ("gi as", "OBL"), ("tata-n-niha", "father-their")]
    glossedWords := [⟨['H', 'u', '#', 'n', 'a', '\'', '-', 'f', 'a', 'n', '-', 's', '-', 'i', 'n', '-', 'a', 'o', 'l', 'a', 'k'], ['1', 'S', 'G', '.', 'S', 'B', 'J', '-', 'C', 'A', 'U', 'S', '-', 'P', 'L', '-', 'P', 'A', 'S', 'S', '-', 's', 'p', 'a', 'n', 'k'], [⟨['H', 'u', '#', 'n', 'a', '\''], ['1', 'S', 'G', '.', 'S', 'B', 'J'], none⟩, ⟨['f', 'a', 'n'], ['C', 'A', 'U', 'S'], some '-'⟩, ⟨['s'], ['P', 'L'], some '-'⟩, ⟨['i', 'n'], ['P', 'A', 'S', 'S'], some '-'⟩, ⟨['a', 'o', 'l', 'a', 'k'], ['s', 'p', 'a', 'n', 'k'], some '-'⟩]⟩, ⟨['i', ' ', 'f', 'a', 'm', 'a', 'g', 'u', '\'', 'u', 'n'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], [⟨['i', ' ', 'f', 'a', 'm', 'a', 'g', 'u', '\'', 'u', 'n'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], none⟩]⟩, ⟨['g', 'i', ' ', 'a', 's'], ['O', 'B', 'L'], [⟨['g', 'i', ' ', 'a', 's'], ['O', 'B', 'L'], none⟩]⟩, ⟨['t', 'a', 't', 'a', '-', 'n', '-', 'n', 'i', 'h', 'a'], ['f', 'a', 't', 'h', 'e', 'r', '-', 't', 'h', 'e', 'i', 'r'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "spank"), ("valence", "transitive"), ("agreesWith", "intermediate subject"), ("m1", "1SG.SBJ"), ("f1", "hu"), ("m2", "CAUS"), ("f2", "na'"), ("m3", "PL"), ("f3", "fan"), ("m4", "PASS"), ("f4", "in"), ("m5", "spank"), ("f5", "saolak")] }

def quechua_39a : Datum :=
  { id := "baker1985_quechua_39a"
    source := ⟨"muysken-1981", "(39a)"⟩
    reportedIn := some ⟨"baker-1985", "(39a)"⟩
    language := "quec1387"
    primaryText := "Maqa-naku-ya-chi-n."
    glossedTokens := [("Maqa-naku-ya-chi-n", "beat-RECP-DUR-CAUS-3SBJ")]
    glossedWords := [⟨['M', 'a', 'q', 'a', '-', 'n', 'a', 'k', 'u', '-', 'y', 'a', '-', 'c', 'h', 'i', '-', 'n'], ['b', 'e', 'a', 't', '-', 'R', 'E', 'C', 'P', '-', 'D', 'U', 'R', '-', 'C', 'A', 'U', 'S', '-', '3', 'S', 'B', 'J'], [⟨['M', 'a', 'q', 'a'], ['b', 'e', 'a', 't'], none⟩, ⟨['n', 'a', 'k', 'u'], ['R', 'E', 'C', 'P'], some '-'⟩, ⟨['y', 'a'], ['D', 'U', 'R'], some '-'⟩, ⟨['c', 'h', 'i'], ['C', 'A', 'U', 'S'], some '-'⟩, ⟨['n'], ['3', 'S', 'B', 'J'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "beat"), ("valence", "transitive"), ("links", "agent-patient"), ("m1", "beat"), ("f1", "maqa"), ("m2", "RECP"), ("f2", "naku"), ("m3", "DUR"), ("f3", "ya"), ("m4", "CAUS"), ("f4", "chi"), ("m5", "3SBJ"), ("f5", "n")] }

def quechua_39b : Datum :=
  { id := "baker1985_quechua_39b"
    source := ⟨"muysken-1981", "(39b)"⟩
    reportedIn := some ⟨"baker-1985", "(39b)"⟩
    language := "quec1387"
    primaryText := "Maqa-chi-naku-rka-n."
    glossedTokens := [("Maqa-chi-naku-rka-n", "beat-CAUS-RECP-PL-3SBJ")]
    glossedWords := [⟨['M', 'a', 'q', 'a', '-', 'c', 'h', 'i', '-', 'n', 'a', 'k', 'u', '-', 'r', 'k', 'a', '-', 'n'], ['b', 'e', 'a', 't', '-', 'C', 'A', 'U', 'S', '-', 'R', 'E', 'C', 'P', '-', 'P', 'L', '-', '3', 'S', 'B', 'J'], [⟨['M', 'a', 'q', 'a'], ['b', 'e', 'a', 't'], none⟩, ⟨['c', 'h', 'i'], ['C', 'A', 'U', 'S'], some '-'⟩, ⟨['n', 'a', 'k', 'u'], ['R', 'E', 'C', 'P'], some '-'⟩, ⟨['r', 'k', 'a'], ['P', 'L'], some '-'⟩, ⟨['n'], ['3', 'S', 'B', 'J'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "beat"), ("valence", "transitive"), ("links", "causer-patient"), ("m1", "beat"), ("f1", "maqa"), ("m2", "CAUS"), ("f2", "chi"), ("m3", "RECP"), ("f3", "naku"), ("m4", "PL"), ("f4", "rka"), ("m5", "3SBJ"), ("f5", "n")] }

def bemba_49a : Datum :=
  { id := "baker1985_bemba_49a"
    source := ⟨"givon-1976", "(49a)"⟩
    reportedIn := some ⟨"baker-1985", "(49a)"⟩
    language := "bemb1257"
    primaryText := "Naa-mon-an-ya Mwape na Mutumba."
    glossedTokens := [("Naa-mon-an-ya", "1SG.SBJ.PST-see-RECP-CAUS"), ("Mwape", "Mwape"), ("na", "and"), ("Mutumba", "Mutumba")]
    glossedWords := [⟨['N', 'a', 'a', '-', 'm', 'o', 'n', '-', 'a', 'n', '-', 'y', 'a'], ['1', 'S', 'G', '.', 'S', 'B', 'J', '.', 'P', 'S', 'T', '-', 's', 'e', 'e', '-', 'R', 'E', 'C', 'P', '-', 'C', 'A', 'U', 'S'], [⟨['N', 'a', 'a'], ['1', 'S', 'G', '.', 'S', 'B', 'J', '.', 'P', 'S', 'T'], none⟩, ⟨['m', 'o', 'n'], ['s', 'e', 'e'], some '-'⟩, ⟨['a', 'n'], ['R', 'E', 'C', 'P'], some '-'⟩, ⟨['y', 'a'], ['C', 'A', 'U', 'S'], some '-'⟩]⟩, ⟨['M', 'w', 'a', 'p', 'e'], ['M', 'w', 'a', 'p', 'e'], [⟨['M', 'w', 'a', 'p', 'e'], ['M', 'w', 'a', 'p', 'e'], none⟩]⟩, ⟨['n', 'a'], ['a', 'n', 'd'], [⟨['n', 'a'], ['a', 'n', 'd'], none⟩]⟩, ⟨['M', 'u', 't', 'u', 'm', 'b', 'a'], ['M', 'u', 't', 'u', 'm', 'b', 'a'], [⟨['M', 'u', 't', 'u', 'm', 'b', 'a'], ['M', 'u', 't', 'u', 'm', 'b', 'a'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "see"), ("valence", "transitive"), ("links", "agent-patient"), ("m1", "1SG.SBJ.PST"), ("f1", "naa"), ("m2", "see"), ("f2", "mon"), ("m3", "RECP"), ("f3", "an"), ("m4", "CAUS"), ("f4", "ya")] }

def bemba_49b : Datum :=
  { id := "baker1985_bemba_49b"
    source := ⟨"givon-1976", "(49b)"⟩
    reportedIn := some ⟨"baker-1985", "(49b)"⟩
    language := "bemb1257"
    primaryText := "Mwape na Chilufya baa-mon-eshy-ana Mutumba."
    glossedTokens := [("Mwape", "Mwape"), ("na", "and"), ("Chilufya", "Chilufya"), ("baa-mon-eshy-ana", "3PL.SBJ-see-CAUS-RECP"), ("Mutumba", "Mutumba")]
    glossedWords := [⟨['M', 'w', 'a', 'p', 'e'], ['M', 'w', 'a', 'p', 'e'], [⟨['M', 'w', 'a', 'p', 'e'], ['M', 'w', 'a', 'p', 'e'], none⟩]⟩, ⟨['n', 'a'], ['a', 'n', 'd'], [⟨['n', 'a'], ['a', 'n', 'd'], none⟩]⟩, ⟨['C', 'h', 'i', 'l', 'u', 'f', 'y', 'a'], ['C', 'h', 'i', 'l', 'u', 'f', 'y', 'a'], [⟨['C', 'h', 'i', 'l', 'u', 'f', 'y', 'a'], ['C', 'h', 'i', 'l', 'u', 'f', 'y', 'a'], none⟩]⟩, ⟨['b', 'a', 'a', '-', 'm', 'o', 'n', '-', 'e', 's', 'h', 'y', '-', 'a', 'n', 'a'], ['3', 'P', 'L', '.', 'S', 'B', 'J', '-', 's', 'e', 'e', '-', 'C', 'A', 'U', 'S', '-', 'R', 'E', 'C', 'P'], [⟨['b', 'a', 'a'], ['3', 'P', 'L', '.', 'S', 'B', 'J'], none⟩, ⟨['m', 'o', 'n'], ['s', 'e', 'e'], some '-'⟩, ⟨['e', 's', 'h', 'y'], ['C', 'A', 'U', 'S'], some '-'⟩, ⟨['a', 'n', 'a'], ['R', 'E', 'C', 'P'], some '-'⟩]⟩, ⟨['M', 'u', 't', 'u', 'm', 'b', 'a'], ['M', 'u', 't', 'u', 'm', 'b', 'a'], [⟨['M', 'u', 't', 'u', 'm', 'b', 'a'], ['M', 'u', 't', 'u', 'm', 'b', 'a'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "see"), ("valence", "transitive"), ("links", "causer-agent"), ("m1", "3PL.SBJ"), ("f1", "baa"), ("m2", "see"), ("f2", "mon"), ("m3", "CAUS"), ("f3", "eshy"), ("m4", "RECP"), ("f4", "ana")] }

def huichol_55 : Datum :=
  { id := "baker1985_huichol_55"
    source := ⟨"comrie-1982", "(55)"⟩
    reportedIn := some ⟨"baker-1985", "(55)"⟩
    language := "huic1243"
    primaryText := "Tiiri yi-nauka-ti nawazi me-puutinanai-ri-yeri."
    glossedTokens := [("Tiiri", "children"), ("yi-nauka-ti", "four-SBJ"), ("nawazi", "knife"), ("me-puutinanai-ri-yeri", "3PL.SBJ-buy-BEN-PASS")]
    glossedWords := [⟨['T', 'i', 'i', 'r', 'i'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], [⟨['T', 'i', 'i', 'r', 'i'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], none⟩]⟩, ⟨['y', 'i', '-', 'n', 'a', 'u', 'k', 'a', '-', 't', 'i'], ['f', 'o', 'u', 'r', '-', 'S', 'B', 'J'], []⟩, ⟨['n', 'a', 'w', 'a', 'z', 'i'], ['k', 'n', 'i', 'f', 'e'], [⟨['n', 'a', 'w', 'a', 'z', 'i'], ['k', 'n', 'i', 'f', 'e'], none⟩]⟩, ⟨['m', 'e', '-', 'p', 'u', 'u', 't', 'i', 'n', 'a', 'n', 'a', 'i', '-', 'r', 'i', '-', 'y', 'e', 'r', 'i'], ['3', 'P', 'L', '.', 'S', 'B', 'J', '-', 'b', 'u', 'y', '-', 'B', 'E', 'N', '-', 'P', 'A', 'S', 'S'], [⟨['m', 'e'], ['3', 'P', 'L', '.', 'S', 'B', 'J'], none⟩, ⟨['p', 'u', 'u', 't', 'i', 'n', 'a', 'n', 'a', 'i'], ['b', 'u', 'y'], some '-'⟩, ⟨['r', 'i'], ['B', 'E', 'N'], some '-'⟩, ⟨['y', 'e', 'r', 'i'], ['P', 'A', 'S', 'S'], some '-'⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "buy"), ("valence", "transitive"), ("surfaceSubject", "applied object"), ("m1", "3PL.SBJ"), ("f1", "me"), ("m2", "buy"), ("f2", "puutinanai"), ("m3", "BEN"), ("f3", "ri"), ("m4", "PASS"), ("f4", "yeri")] }

def chimwiini_56c : Datum :=
  { id := "baker1985_chimwiini_56c"
    source := ⟨"kisseberth-abasheikh-1977", "(56c)"⟩
    reportedIn := some ⟨"baker-1985", "(56c)"⟩
    language := "chim1312"
    primaryText := "Mwa:limu ∅-tet-el-el-a chibu:ku na Nu:ru."
    glossedTokens := [("Mwa:limu", "teacher"), ("∅-tet-el-el-a", "SP-bring-APPL-ASP-PASS"), ("chibu:ku", "book"), ("na", "by"), ("Nu:ru", "Nuru")]
    glossedWords := [⟨['M', 'w', 'a', ':', 'l', 'i', 'm', 'u'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], [⟨['M', 'w', 'a', 'l', 'i', 'm', 'u'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], none⟩]⟩, ⟨['∅', '-', 't', 'e', 't', '-', 'e', 'l', '-', 'e', 'l', '-', 'a'], ['S', 'P', '-', 'b', 'r', 'i', 'n', 'g', '-', 'A', 'P', 'P', 'L', '-', 'A', 'S', 'P', '-', 'P', 'A', 'S', 'S'], [⟨['∅'], ['S', 'P'], none⟩, ⟨['t', 'e', 't'], ['b', 'r', 'i', 'n', 'g'], some '-'⟩, ⟨['e', 'l'], ['A', 'P', 'P', 'L'], some '-'⟩, ⟨['e', 'l'], ['A', 'S', 'P'], some '-'⟩, ⟨['a'], ['P', 'A', 'S', 'S'], some '-'⟩]⟩, ⟨['c', 'h', 'i', 'b', 'u', ':', 'k', 'u'], ['b', 'o', 'o', 'k'], [⟨['c', 'h', 'i', 'b', 'u', 'k', 'u'], ['b', 'o', 'o', 'k'], none⟩]⟩, ⟨['n', 'a'], ['b', 'y'], [⟨['n', 'a'], ['b', 'y'], none⟩]⟩, ⟨['N', 'u', ':', 'r', 'u'], ['N', 'u', 'r', 'u'], [⟨['N', 'u', 'r', 'u'], ['N', 'u', 'r', 'u'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "bring"), ("valence", "transitive"), ("surfaceSubject", "applied object"), ("m1", "SP"), ("f1", "∅"), ("m2", "bring"), ("f2", "tet"), ("m3", "APPL"), ("f3", "el"), ("m4", "ASP"), ("f4", "el"), ("m5", "PASS"), ("f5", "a")] }

def chimwiini_56d : Datum :=
  { id := "baker1985_chimwiini_56d"
    source := ⟨"kisseberth-abasheikh-1977", "(56d)"⟩
    reportedIn := some ⟨"baker-1985", "(56d)"⟩
    language := "chim1312"
    primaryText := "Chibu:ku chi-tet-el-el-a mwa:limu na Nu:ru."
    glossedTokens := [("Chibu:ku", "book"), ("chi-tet-el-el-a", "SP-bring-APPL-ASP-PASS"), ("mwa:limu", "teacher"), ("na", "by"), ("Nu:ru", "Nuru")]
    glossedWords := [⟨['C', 'h', 'i', 'b', 'u', ':', 'k', 'u'], ['b', 'o', 'o', 'k'], [⟨['C', 'h', 'i', 'b', 'u', 'k', 'u'], ['b', 'o', 'o', 'k'], none⟩]⟩, ⟨['c', 'h', 'i', '-', 't', 'e', 't', '-', 'e', 'l', '-', 'e', 'l', '-', 'a'], ['S', 'P', '-', 'b', 'r', 'i', 'n', 'g', '-', 'A', 'P', 'P', 'L', '-', 'A', 'S', 'P', '-', 'P', 'A', 'S', 'S'], [⟨['c', 'h', 'i'], ['S', 'P'], none⟩, ⟨['t', 'e', 't'], ['b', 'r', 'i', 'n', 'g'], some '-'⟩, ⟨['e', 'l'], ['A', 'P', 'P', 'L'], some '-'⟩, ⟨['e', 'l'], ['A', 'S', 'P'], some '-'⟩, ⟨['a'], ['P', 'A', 'S', 'S'], some '-'⟩]⟩, ⟨['m', 'w', 'a', ':', 'l', 'i', 'm', 'u'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], [⟨['m', 'w', 'a', 'l', 'i', 'm', 'u'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], none⟩]⟩, ⟨['n', 'a'], ['b', 'y'], [⟨['n', 'a'], ['b', 'y'], none⟩]⟩, ⟨['N', 'u', ':', 'r', 'u'], ['N', 'u', 'r', 'u'], [⟨['N', 'u', 'r', 'u'], ['N', 'u', 'r', 'u'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("root", "bring"), ("valence", "transitive"), ("surfaceSubject", "patient"), ("m1", "SP"), ("f1", "chi"), ("m2", "bring"), ("f2", "tet"), ("m3", "APPL"), ("f3", "el"), ("m4", "ASP"), ("f4", "el"), ("m5", "PASS"), ("f5", "a")] }

def kinyarwanda_57c : Datum :=
  { id := "baker1985_kinyarwanda_57c"
    source := ⟨"kimenyi-1980", "(57c)"⟩
    reportedIn := some ⟨"baker-1985", "(57c)"⟩
    language := "kiny1244"
    primaryText := "Ikaramu i-ra-andik-iish-w-a ibaruwa n'umugabo."
    glossedTokens := [("Ikaramu", "pen"), ("i-ra-andik-iish-w-a", "SP-PRS-write-INSTR-PASS-ASP"), ("ibaruwa", "letter"), ("n'umugabo", "by-man")]
    glossedWords := [⟨['I', 'k', 'a', 'r', 'a', 'm', 'u'], ['p', 'e', 'n'], [⟨['I', 'k', 'a', 'r', 'a', 'm', 'u'], ['p', 'e', 'n'], none⟩]⟩, ⟨['i', '-', 'r', 'a', '-', 'a', 'n', 'd', 'i', 'k', '-', 'i', 'i', 's', 'h', '-', 'w', '-', 'a'], ['S', 'P', '-', 'P', 'R', 'S', '-', 'w', 'r', 'i', 't', 'e', '-', 'I', 'N', 'S', 'T', 'R', '-', 'P', 'A', 'S', 'S', '-', 'A', 'S', 'P'], [⟨['i'], ['S', 'P'], none⟩, ⟨['r', 'a'], ['P', 'R', 'S'], some '-'⟩, ⟨['a', 'n', 'd', 'i', 'k'], ['w', 'r', 'i', 't', 'e'], some '-'⟩, ⟨['i', 'i', 's', 'h'], ['I', 'N', 'S', 'T', 'R'], some '-'⟩, ⟨['w'], ['P', 'A', 'S', 'S'], some '-'⟩, ⟨['a'], ['A', 'S', 'P'], some '-'⟩]⟩, ⟨['i', 'b', 'a', 'r', 'u', 'w', 'a'], ['l', 'e', 't', 't', 'e', 'r'], [⟨['i', 'b', 'a', 'r', 'u', 'w', 'a'], ['l', 'e', 't', 't', 'e', 'r'], none⟩]⟩, ⟨['n', '\'', 'u', 'm', 'u', 'g', 'a', 'b', 'o'], ['b', 'y', '-', 'm', 'a', 'n'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "write"), ("valence", "transitive"), ("surfaceSubject", "applied object"), ("m1", "SP"), ("f1", "i"), ("m2", "PRS"), ("f2", "ra"), ("m3", "write"), ("f3", "andik"), ("m4", "INSTR"), ("f4", "iish"), ("m5", "PASS"), ("f5", "w"), ("m6", "ASP"), ("f6", "a")] }

def kinyarwanda_57d : Datum :=
  { id := "baker1985_kinyarwanda_57d"
    source := ⟨"kimenyi-1980", "(57d)"⟩
    reportedIn := some ⟨"baker-1985", "(57d)"⟩
    language := "kiny1244"
    primaryText := "Ibaruwa i-ra-andik-iish-w-a ikaramu n'umugabo."
    glossedTokens := [("Ibaruwa", "letter"), ("i-ra-andik-iish-w-a", "SP-PRS-write-INSTR-PASS-ASP"), ("ikaramu", "pen"), ("n'umugabo", "by-man")]
    glossedWords := [⟨['I', 'b', 'a', 'r', 'u', 'w', 'a'], ['l', 'e', 't', 't', 'e', 'r'], [⟨['I', 'b', 'a', 'r', 'u', 'w', 'a'], ['l', 'e', 't', 't', 'e', 'r'], none⟩]⟩, ⟨['i', '-', 'r', 'a', '-', 'a', 'n', 'd', 'i', 'k', '-', 'i', 'i', 's', 'h', '-', 'w', '-', 'a'], ['S', 'P', '-', 'P', 'R', 'S', '-', 'w', 'r', 'i', 't', 'e', '-', 'I', 'N', 'S', 'T', 'R', '-', 'P', 'A', 'S', 'S', '-', 'A', 'S', 'P'], [⟨['i'], ['S', 'P'], none⟩, ⟨['r', 'a'], ['P', 'R', 'S'], some '-'⟩, ⟨['a', 'n', 'd', 'i', 'k'], ['w', 'r', 'i', 't', 'e'], some '-'⟩, ⟨['i', 'i', 's', 'h'], ['I', 'N', 'S', 'T', 'R'], some '-'⟩, ⟨['w'], ['P', 'A', 'S', 'S'], some '-'⟩, ⟨['a'], ['A', 'S', 'P'], some '-'⟩]⟩, ⟨['i', 'k', 'a', 'r', 'a', 'm', 'u'], ['p', 'e', 'n'], [⟨['i', 'k', 'a', 'r', 'a', 'm', 'u'], ['p', 'e', 'n'], none⟩]⟩, ⟨['n', '\'', 'u', 'm', 'u', 'g', 'a', 'b', 'o'], ['b', 'y', '-', 'm', 'a', 'n'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "write"), ("valence", "transitive"), ("surfaceSubject", "patient"), ("m1", "SP"), ("f1", "i"), ("m2", "PRS"), ("f2", "ra"), ("m3", "write"), ("f3", "andik"), ("m4", "INSTR"), ("f4", "iish"), ("m5", "PASS"), ("f5", "w"), ("m6", "ASP"), ("f6", "a")] }

def all : List Datum := [chamorro_15a, chamorro_15b, chamorro_15c, chamorro_25, quechua_39a, quechua_39b, bemba_49a, bemba_49b, huichol_55, chimwiini_56c, chimwiini_56d, kinyarwanda_57c, kinyarwanda_57d]

/-- The subject the verb agrees with. -/
inductive AgreementController where
  /-- surface subject: the surface subject -/
  | surface
  /-- semantic subject: the semantic subject -/
  | semantic
  /-- intermediate subject: the subject at an intermediate stage -/
  | intermediate
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `agreesWith`. -/
def agreementController (e : Datum) : Option AgreementController :=
  e.parse? "agreesWith" [("surface subject", .surface), ("semantic subject", .semantic),
    ("intermediate subject", .intermediate)]

/-- The pair of arguments a reciprocal or reflexive links. -/
inductive Links where
  /-- agent-patient: agent and patient -/
  | agentPatient
  /-- causer-patient: causer and patient -/
  | causerPatient
  /-- causer-agent: causer and agent -/
  | causerAgent
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `links`. -/
def links (e : Datum) : Option Links :=
  e.parse? "links" [("agent-patient", .agentPatient), ("causer-patient", .causerPatient),
    ("causer-agent", .causerAgent)]

/-- The argument that is the surface subject of a passive. -/
inductive SurfaceSubject where
  /-- applied object: the applied object -/
  | appliedObject
  /-- patient: the patient -/
  | patient
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `surfaceSubject`. -/
def surfaceSubject (e : Datum) : Option SurfaceSubject :=
  e.parse? "surfaceSubject" [("applied object", .appliedObject), ("patient", .patient)]

end Baker1985.Examples
