module

public import Linglib.Data.Examples.Schema

/-!
# `Bondarenko2022` — typed example data

Auto-generated from `Linglib/Data/Examples/Bondarenko2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Bondarenko2022.Examples`.
-/

@[expose] public section

namespace Bondarenko2022.Examples

def ch2_105 : Datum :=
  { id := "bondarenko2022_ch2_105"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (105)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Ideja čto grjadut reformy javljaetsja vernoj."
    glossedTokens := [("Ideja", "idea"), ("čto", "COMP"), ("grjadut", "are.coming"), ("reformy", "reforms"), ("javljaetsja", "is"), ("vernoj", "true")]
    context := ""
    judgment := .acceptable
    alternatives := [("Situacija čto grjadut reformy javljaetsja vernoj.", .ungrammatical), ("Ideja čto grjadut reformy javljaetsja ošibočnoj.", .acceptable)]
    readings := []
    paperFeatures := [("diagnostic", "truth-predicates"), ("nounSort", "content")] }

def ch2_106 : Datum :=
  { id := "bondarenko2022_ch2_106"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (106)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Swuna-ka mwuncey-lul phwul-ess-ta-nun cwucang-i kecis-i-ta."
    glossedTokens := [("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-ess-ta-nun", "solve-PST-DECL-ADN"), ("cwucang-i", "claim-NOM"), ("kecis-i-ta", "falsehood-COP-DECL")]
    context := ""
    judgment := .acceptable
    alternatives := [("Swuna-ka mwuncey-lul phwul-ess-ta-nun cwucang-i cham-i-ta.", .acceptable)]
    readings := []
    paperFeatures := [("diagnostic", "truth-predicates"), ("nounSort", "content")] }

def ch2_107 : Datum :=
  { id := "bondarenko2022_ch2_107"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (107)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Swuna-ka mwuncey-lul phwul-un sanghwang-i kecis-i-ta."
    glossedTokens := [("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-un", "solve-ADN"), ("sanghwang-i", "situation-NOM"), ("kecis-i-ta", "falsehood-COP-DECL")]
    context := ""
    judgment := .ungrammatical
    alternatives := [("Swuna-ka mwuncey-lul phwul-un sanghwang-i cham-i-ta.", .ungrammatical)]
    readings := []
    paperFeatures := [("diagnostic", "truth-predicates"), ("nounSort", "situation")] }

def ch2_108 : Datum :=
  { id := "bondarenko2022_ch2_108"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (108)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Včera proizošla situacija čto moj zakaz zaderžali."
    glossedTokens := [("Včera", "yesterday"), ("proizošla", "occured"), ("situacija", "situation"), ("čto", "COMP"), ("moj", "my"), ("zakaz", "order"), ("zaderžali", "delayed")]
    context := ""
    judgment := .acceptable
    alternatives := [("Včera proizošla ideja čto moj zakaz zaderžali.", .ungrammatical), ("Včera slučilas’ situacija čto moj zakaz zaderžali.", .acceptable)]
    readings := []
    paperFeatures := [("diagnostic", "occurrence-predicates"), ("nounSort", "situation")] }

def ch2_109 : Datum :=
  { id := "bondarenko2022_ch2_109"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (109)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Swuna-ka mwuncey-lul phwul-ess-ta-nun cwucang-i ilena-ss-ta"
    glossedTokens := [("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-ess-ta-nun", "solve-PST-DECL-ADN"), ("cwucang-i", "claim-NOM"), ("ilena-ss-ta", "occur-PST-DECL")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "occurrence-predicates"), ("nounSort", "content")] }

def ch2_110 : Datum :=
  { id := "bondarenko2022_ch2_110"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (110)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Swuna-ka mwuncey-lul phwul-un sanghwang-i ilena-ss-ta"
    glossedTokens := [("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-un", "solve-ADN"), ("sanghwang-i", "situation-NOM"), ("ilena-ss-ta", "occur-PST-DECL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "occurrence-predicates"), ("nounSort", "situation")] }

def ch2_111 : Datum :=
  { id := "bondarenko2022_ch2_111"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (111)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kore1280"
    primaryText := "Mina-ka Swuna-ka mwuncey-lul phwul-ess-ta-nun cwucang-ul alachay-ss-ta"
    glossedTokens := [("Mina-ka", "Mina-NOM"), ("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-ess-ta-nun", "solve-PST-DECL-ADN"), ("cwucang-ul", "claim-ACC"), ("alachay-ss-ta", "notice-PST-DECL")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "situation-only-predicate-notice"), ("nounSort", "content")] }

def ch2_112 : Datum :=
  { id := "bondarenko2022_ch2_112"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (112)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Mina-ka Swuna-ka mwuncey-lul phwul-un sanghwang-ul alachay-ss-ta"
    glossedTokens := [("Mina-ka", "Mina-NOM"), ("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-un", "solve-ADN"), ("sanghwang-ul", "situation-ACC"), ("alachay-ss-ta", "notice-PST-DECL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "situation-only-predicate-notice"), ("nounSort", "situation")] }

def ch2_120a : Datum :=
  { id := "bondarenko2022_ch2_120a"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (120a)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Lena zametila slux čto èta ženščina priexala na kone."
    glossedTokens := [("Lena", "Lena"), ("zametila", "noticed"), ("slux", "rumor"), ("čto", "COMP"), ("èta", "this"), ("ženščina", "woman"), ("priexala", "arrived"), ("na", "on"), ("kone", "horse")]
    context := ""
    judgment := .acceptable
    alternatives := [("Lena zametila slučaj čto èta ženščina priexala na kone.", .acceptable)]
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("role", "premise-a")] }

def ch2_120b : Datum :=
  { id := "bondarenko2022_ch2_120b"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (120b)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "èta ženščina — koroleva Velikobritanii."
    glossedTokens := [("èta", "this"), ("ženščina", "woman"), ("koroleva", "queen"), ("Velikobritanii", "Great.Britain")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("role", "premise-b")] }

def ch2_120c : Datum :=
  { id := "bondarenko2022_ch2_120c"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (120c)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Lena zametila slux čto koroleva Velikobritanii priexala na kone."
    glossedTokens := [("Lena", "Lena"), ("zametila", "noticed"), ("slux", "rumor"), ("čto", "COMP"), ("koroleva", "queen"), ("Velikobritanii", "Great.Britain"), ("priexala", "arrived"), ("na", "on"), ("kone", "horse")]
    context := ""
    judgment := .acceptable
    alternatives := [("Lena zametila slučaj čto koroleva Velikobritanii priexala na kone.", .acceptable)]
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("role", "conclusion")] }

def ch2_121a : Datum :=
  { id := "bondarenko2022_ch2_121a"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (121a)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Mina-ka Swuna-ka mwuncey-lul phwul-ess-ta-nun cwucang-ul kiekhay-ss-ta."
    glossedTokens := [("Mina-ka", "Mina-NOM"), ("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-ess-ta-nun", "solve-PST-DECL-ADN"), ("cwucang-ul", "claim-ACC"), ("kiekhay-ss-ta", "remember-PST-DECL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("nounSort", "content"), ("role", "premise-a")] }

def ch2_121b : Datum :=
  { id := "bondarenko2022_ch2_121b"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (121b)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Swuna-ka pan-eyse kacang khi-ga khu-ta."
    glossedTokens := [("Swuna-ka", "Swuna-NOM"), ("pan-eyse", "class-LOC"), ("kacang", "most"), ("khi-ga", "height-NOM"), ("khu-ta", "large-DECL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("role", "premise-b")] }

def ch2_121c : Datum :=
  { id := "bondarenko2022_ch2_121c"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (121c)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Mina-ka pan-eyse kacang khi-ga khun sonye-ka mwuncey-lul phwul-ess-ta-nun cwucang-ul kiekhay-ss-ta."
    glossedTokens := [("Mina-ka", "Mina-NOM"), ("pan-eyse", "class-LOC"), ("kacang", "most"), ("khi-ga", "height-NOM"), ("khun", "large"), ("sonye-ka", "girl-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-ess-ta-nun", "solve-PST-DECL-ADN"), ("cwucang-ul", "claim-ACC"), ("kiekhay-ss-ta", "remember-PST-DECL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("nounSort", "content"), ("role", "conclusion"), ("inference", "invalid")] }

def ch2_122a : Datum :=
  { id := "bondarenko2022_ch2_122a"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (122a)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Mina-ka Swuna-ka mwuncey-lul phwul-un sanghwang-ul kiekhay-ss-ta."
    glossedTokens := [("Mina-ka", "Mina-NOM"), ("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-un", "solve-ADN"), ("sanghwang-ul", "situation-ACC"), ("kiekhay-ss-ta", "remember-PST-DECL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("nounSort", "situation"), ("role", "premise-a")] }

def ch2_122b : Datum :=
  { id := "bondarenko2022_ch2_122b"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (122b)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Swuna-ka pan-eyse kacang khi-ga khu-ta."
    glossedTokens := [("Swuna-ka", "Swuna-NOM"), ("pan-eyse", "class-LOC"), ("kacang", "most"), ("khi-ga", "height-NOM"), ("khu-ta", "large-DECL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("role", "premise-b")] }

def ch2_122c : Datum :=
  { id := "bondarenko2022_ch2_122c"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (122c)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Mina-ka pan-eyse kacang khi-ga khun sonye-ka mwuncey-lul phwul-un sanghwang-ul kiekhay-ss-ta."
    glossedTokens := [("Mina-ka", "Mina-NOM"), ("pan-eyse", "class-LOC"), ("kacang", "most"), ("khi-ga", "height-NOM"), ("khun", "large"), ("sonye-ka", "girl-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-un", "solve-ADN"), ("sanghwang-ul", "situation-ACC"), ("kiekhay-ss-ta", "remember-PST-DECL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("nounSort", "situation"), ("role", "conclusion"), ("inference", "valid")] }

def ch4_30 : Datum :=
  { id := "bondarenko2022_ch4_30"
    source := ⟨"bondarenko-2022", "§4.3.1 ex. (30)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Dugar mi:sgɘi zagaha ɘdj-ɘ: gɘ-žɘ han-a:"
    glossedTokens := [("Dugar", "Dugar.NOM"), ("mi:sgɘi", "cat.NOM"), ("zagaha", "fish"), ("ɘdj-ɘ:", "eat-PST"), ("gɘ-žɘ", "say-CVB"), ("han-a:", "think-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "Cont-CP"), ("shape", "bare gɘ-žɘ clause")] }

def ch4_31 : Datum :=
  { id := "bondarenko2022_ch4_31"
    source := ⟨"bondarenko-2022", "§4.3.1 ex. (31)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Dugar mi:sgɘi-n zagaha ɘdj-ɘ:š-i:jɘ-(n’) han-a:"
    glossedTokens := [("Dugar", "Dugar.NOM"), ("mi:sgɘi-n", "cat-GEN"), ("zagaha", "fish"), ("ɘdj-ɘ:š-i:jɘ-(n’)", "eat-PART-ACC-(3)"), ("han-a:", "think-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "Sit-CP"), ("shape", "nominalized participial clause")] }

def ch4_32 : Datum :=
  { id := "bondarenko2022_ch4_32"
    source := ⟨"bondarenko-2022", "§4.3.1 ex. (32)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Dugar mi:sgɘi-n zagaha ɘdj-ɘ: g-ɘ:š-i:jɘ-(n’) han-a:"
    glossedTokens := [("Dugar", "Dugar.NOM"), ("mi:sgɘi-n", "cat-GEN"), ("zagaha", "fish"), ("ɘdj-ɘ:", "eat-PST"), ("g-ɘ:š-i:jɘ-(n’)", "say-PART-ACC-(3)"), ("han-a:", "think-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "Cont-CP"), ("shape", "nominalized gɘ-participial clause")] }

def all : List Datum := [ch2_105, ch2_106, ch2_107, ch2_108, ch2_109, ch2_110, ch2_111, ch2_112, ch2_120a, ch2_120b, ch2_120c, ch2_121a, ch2_121b, ch2_121c, ch2_122a, ch2_122b, ch2_122c, ch4_30, ch4_31, ch4_32]

end Bondarenko2022.Examples
