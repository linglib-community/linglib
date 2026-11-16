module

public import Linglib.Data.Examples.Schema

/-!
# `Sells1987` — typed example data

Auto-generated from `Linglib/Data/Examples/Sells1987.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Sells1987.Examples`.
-/

@[expose] public section

namespace Sells1987.Examples

def ex_11a : Datum :=
  { id := "sells1987_11a"
    source := ⟨"sells-1987", "(11a)"⟩
    reportedIn := none
    language := "ewee1241"
    primaryText := "kofi be yè-dzo"
    glossedTokens := [("kofi", "Kofi"), ("be", "say"), ("yè-dzo", "Log-leave")]
    glossedWords := [⟨[['k', 'o', 'f', 'i']], [['K', 'o', 'f', 'i']]⟩, ⟨[['b', 'e']], [['s', 'a', 'y']]⟩, ⟨[['y', 'è'], ['d', 'z', 'o']], [['L', 'o', 'g'], ['l', 'e', 'a', 'v', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "yè"), ("environment", "logophoric verb")] }

def ex_12 : Datum :=
  { id := "sells1987_12"
    source := ⟨"sells-1987", "(12)"⟩
    reportedIn := none
    language := "ewee1241"
    primaryText := "ana kpɔ dyidzo be yè-dyi vi"
    glossedTokens := [("ana", "Ana"), ("kpɔ", "see"), ("dyidzo", "happiness"), ("be", "Comp"), ("yè-dyi", "Log-bear"), ("vi", "child")]
    glossedWords := [⟨[['a', 'n', 'a']], [['A', 'n', 'a']]⟩, ⟨[['k', 'p', 'ɔ']], [['s', 'e', 'e']]⟩, ⟨[['d', 'y', 'i', 'd', 'z', 'o']], [['h', 'a', 'p', 'p', 'i', 'n', 'e', 's', 's']]⟩, ⟨[['b', 'e']], [['C', 'o', 'm', 'p']]⟩, ⟨[['y', 'è'], ['d', 'y', 'i']], [['L', 'o', 'g'], ['b', 'e', 'a', 'r']]⟩, ⟨[['v', 'i']], [['c', 'h', 'i', 'l', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "yè"), ("environment", "psych-verb")] }

def ex_17 : Datum :=
  { id := "sells1987_17"
    source := ⟨"sells-1987", "(17)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Hann sagði að sig vantaði hæfileika."
    glossedTokens := [("Hann", "he"), ("sagði", "said"), ("að", "that"), ("sig", "self"), ("vantaði", "lacked"), ("hæfileika", "ability")]
    glossedWords := [⟨[['H', 'a', 'n', 'n']], [['h', 'e']]⟩, ⟨[['s', 'a', 'g', 'ð', 'i']], [['s', 'a', 'i', 'd']]⟩, ⟨[['a', 'ð']], [['t', 'h', 'a', 't']]⟩, ⟨[['s', 'i', 'g']], [['s', 'e', 'l', 'f']]⟩, ⟨[['v', 'a', 'n', 't', 'a', 'ð', 'i']], [['l', 'a', 'c', 'k', 'e', 'd']]⟩, ⟨[['h', 'æ', 'f', 'i', 'l', 'e', 'i', 'k', 'a']], [['a', 'b', 'i', 'l', 'i', 't', 'y']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "sig"), ("environment", "logophoric verb")] }

def ex_43 : Datum :=
  { id := "sells1987_43"
    source := ⟨"sells-1987", "(43)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo wa Yosiko ga zibun o aisiteiru to itta."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "zibun"), ("environment", "logophoric verb")] }

def ex_44 : Datum :=
  { id := "sells1987_44"
    source := ⟨"sells-1987", "(44)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Yosiko ga zibun o musisita koto ga Taroo o yuutunisita."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "zibun"), ("environment", "psych-verb")] }

def ex_45 : Datum :=
  { id := "sells1987_45"
    source := ⟨"sells-1987", "(45)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Takasi wa Taroo ni baka no Yosiko ga zibun o oikake-mawasiteiru koto o hanasita."
    glossedTokens := [("Takasi", "Takasi"), ("wa", "Top"), ("Taroo", "Taroo"), ("ni", "Dat"), ("baka", "fool"), ("no", "Gen"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("zibun", "self"), ("o", "Obj"), ("oikake-mawasiteiru", "chase-around-be"), ("koto", "Comp"), ("o", "Obj"), ("hanasita", "told")]
    glossedWords := [⟨[['T', 'a', 'k', 'a', 's', 'i']], [['T', 'a', 'k', 'a', 's', 'i']]⟩, ⟨[['w', 'a']], [['T', 'o', 'p']]⟩, ⟨[['T', 'a', 'r', 'o', 'o']], [['T', 'a', 'r', 'o', 'o']]⟩, ⟨[['n', 'i']], [['D', 'a', 't']]⟩, ⟨[['b', 'a', 'k', 'a']], [['f', 'o', 'o', 'l']]⟩, ⟨[['n', 'o']], [['G', 'e', 'n']]⟩, ⟨[['Y', 'o', 's', 'i', 'k', 'o']], [['Y', 'o', 's', 'i', 'k', 'o']]⟩, ⟨[['g', 'a']], [['S', 'u', 'b', 'j']]⟩, ⟨[['z', 'i', 'b', 'u', 'n']], [['s', 'e', 'l', 'f']]⟩, ⟨[['o']], [['O', 'b', 'j']]⟩, ⟨[['o', 'i', 'k', 'a', 'k', 'e'], ['m', 'a', 'w', 'a', 's', 'i', 't', 'e', 'i', 'r', 'u']], [['c', 'h', 'a', 's', 'e'], ['a', 'r', 'o', 'u', 'n', 'd'], ['b', 'e']]⟩, ⟨[['k', 'o', 't', 'o']], [['C', 'o', 'm', 'p']]⟩, ⟨[['o']], [['O', 'b', 'j']]⟩, ⟨[['h', 'a', 'n', 'a', 's', 'i', 't', 'a']], [['t', 'o', 'l', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .acceptable), ("external speaker", .marginal)]
    paperFeatures := [("pronoun", "zibun"), ("diagnostic", "that fool"), ("environment", "logophoric verb")] }

def ex_46 : Datum :=
  { id := "sells1987_46"
    source := ⟨"sells-1987", "(46)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo wa Takasi kara baka no Yosiko ga zibun o oikake-mawasiteiru to kiita."
    glossedTokens := [("Taroo", "Taroo"), ("wa", "Top"), ("Takasi", "Takasi"), ("kara", "from"), ("baka", "fool"), ("no", "Gen"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("zibun", "self"), ("o", "Obj"), ("oikake-mawasiteiru", "chase-around-be"), ("to", "Comp"), ("kiita", "heard")]
    glossedWords := [⟨[['T', 'a', 'r', 'o', 'o']], [['T', 'a', 'r', 'o', 'o']]⟩, ⟨[['w', 'a']], [['T', 'o', 'p']]⟩, ⟨[['T', 'a', 'k', 'a', 's', 'i']], [['T', 'a', 'k', 'a', 's', 'i']]⟩, ⟨[['k', 'a', 'r', 'a']], [['f', 'r', 'o', 'm']]⟩, ⟨[['b', 'a', 'k', 'a']], [['f', 'o', 'o', 'l']]⟩, ⟨[['n', 'o']], [['G', 'e', 'n']]⟩, ⟨[['Y', 'o', 's', 'i', 'k', 'o']], [['Y', 'o', 's', 'i', 'k', 'o']]⟩, ⟨[['g', 'a']], [['S', 'u', 'b', 'j']]⟩, ⟨[['z', 'i', 'b', 'u', 'n']], [['s', 'e', 'l', 'f']]⟩, ⟨[['o']], [['O', 'b', 'j']]⟩, ⟨[['o', 'i', 'k', 'a', 'k', 'e'], ['m', 'a', 'w', 'a', 's', 'i', 't', 'e', 'i', 'r', 'u']], [['c', 'h', 'a', 's', 'e'], ['a', 'r', 'o', 'u', 'n', 'd'], ['b', 'e']]⟩, ⟨[['t', 'o']], [['C', 'o', 'm', 'p']]⟩, ⟨[['k', 'i', 'i', 't', 'a']], [['h', 'e', 'a', 'r', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .acceptable), ("external speaker", .acceptable)]
    paperFeatures := [("pronoun", "zibun"), ("diagnostic", "that fool"), ("environment", "logophoric verb")] }

def ex_47 : Datum :=
  { id := "sells1987_47"
    source := ⟨"sells-1987", "(47)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Baka no Yosiko ga zibun o oikake-mawasiteiru koto ga Mitiko o zetuboo e oiyatta."
    glossedTokens := [("Baka", "fool"), ("no", "Gen"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("zibun", "self"), ("o", "Obj"), ("oikake-mawasiteiru", "chase-around-be"), ("koto", "Comp"), ("ga", "Subj"), ("Mitiko", "Mitiko"), ("o", "Obj"), ("zetuboo", "desperation"), ("e", "to"), ("oiyatta", "drove")]
    glossedWords := [⟨[['B', 'a', 'k', 'a']], [['f', 'o', 'o', 'l']]⟩, ⟨[['n', 'o']], [['G', 'e', 'n']]⟩, ⟨[['Y', 'o', 's', 'i', 'k', 'o']], [['Y', 'o', 's', 'i', 'k', 'o']]⟩, ⟨[['g', 'a']], [['S', 'u', 'b', 'j']]⟩, ⟨[['z', 'i', 'b', 'u', 'n']], [['s', 'e', 'l', 'f']]⟩, ⟨[['o']], [['O', 'b', 'j']]⟩, ⟨[['o', 'i', 'k', 'a', 'k', 'e'], ['m', 'a', 'w', 'a', 's', 'i', 't', 'e', 'i', 'r', 'u']], [['c', 'h', 'a', 's', 'e'], ['a', 'r', 'o', 'u', 'n', 'd'], ['b', 'e']]⟩, ⟨[['k', 'o', 't', 'o']], [['C', 'o', 'm', 'p']]⟩, ⟨[['g', 'a']], [['S', 'u', 'b', 'j']]⟩, ⟨[['M', 'i', 't', 'i', 'k', 'o']], [['M', 'i', 't', 'i', 'k', 'o']]⟩, ⟨[['o']], [['O', 'b', 'j']]⟩, ⟨[['z', 'e', 't', 'u', 'b', 'o', 'o']], [['d', 'e', 's', 'p', 'e', 'r', 'a', 't', 'i', 'o', 'n']]⟩, ⟨[['e']], [['t', 'o']]⟩, ⟨[['o', 'i', 'y', 'a', 't', 't', 'a']], [['d', 'r', 'o', 'v', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .unacceptable), ("external speaker", .acceptable)]
    paperFeatures := [("pronoun", "zibun"), ("diagnostic", "that fool"), ("environment", "psych-verb")] }

def ex_48 : Datum :=
  { id := "sells1987_48"
    source := ⟨"sells-1987", "(48)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo wa baka no Yosiko ga mizu o zibun no ue ni kobosita node nurete-simatta."
    glossedTokens := [("Taroo", "Taroo"), ("wa", "Top"), ("baka", "fool"), ("no", "Gen"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("mizu", "water"), ("o", "Obj"), ("zibun", "self"), ("no", "Gen"), ("ue", "on"), ("ni", "Loc"), ("kobosita", "spilled"), ("node", "because"), ("nurete-simatta", "wet-got")]
    glossedWords := [⟨[['T', 'a', 'r', 'o', 'o']], [['T', 'a', 'r', 'o', 'o']]⟩, ⟨[['w', 'a']], [['T', 'o', 'p']]⟩, ⟨[['b', 'a', 'k', 'a']], [['f', 'o', 'o', 'l']]⟩, ⟨[['n', 'o']], [['G', 'e', 'n']]⟩, ⟨[['Y', 'o', 's', 'i', 'k', 'o']], [['Y', 'o', 's', 'i', 'k', 'o']]⟩, ⟨[['g', 'a']], [['S', 'u', 'b', 'j']]⟩, ⟨[['m', 'i', 'z', 'u']], [['w', 'a', 't', 'e', 'r']]⟩, ⟨[['o']], [['O', 'b', 'j']]⟩, ⟨[['z', 'i', 'b', 'u', 'n']], [['s', 'e', 'l', 'f']]⟩, ⟨[['n', 'o']], [['G', 'e', 'n']]⟩, ⟨[['u', 'e']], [['o', 'n']]⟩, ⟨[['n', 'i']], [['L', 'o', 'c']]⟩, ⟨[['k', 'o', 'b', 'o', 's', 'i', 't', 'a']], [['s', 'p', 'i', 'l', 'l', 'e', 'd']]⟩, ⟨[['n', 'o', 'd', 'e']], [['b', 'e', 'c', 'a', 'u', 's', 'e']]⟩, ⟨[['n', 'u', 'r', 'e', 't', 'e'], ['s', 'i', 'm', 'a', 't', 't', 'a']], [['w', 'e', 't'], ['g', 'o', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .unacceptable), ("external speaker", .acceptable)]
    paperFeatures := [("pronoun", "zibun"), ("diagnostic", "that fool"), ("environment", "3POV")] }

def ex_49 : Datum :=
  { id := "sells1987_49"
    source := ⟨"sells-1987", "(49)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Takasi wa Yosiko ga hukakainimo ato o tuke-mawasiteiru to itta."
    glossedTokens := [("Takasi", "Takasi"), ("wa", "Top"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("hukakainimo", "mysteriously"), ("ato o tuke-mawasiteiru", "be-following"), ("to", "Comp"), ("itta", "said")]
    glossedWords := [⟨[['T', 'a', 'k', 'a', 's', 'i']], [['T', 'a', 'k', 'a', 's', 'i']]⟩, ⟨[['w', 'a']], [['T', 'o', 'p']]⟩, ⟨[['Y', 'o', 's', 'i', 'k', 'o']], [['Y', 'o', 's', 'i', 'k', 'o']]⟩, ⟨[['g', 'a']], [['S', 'u', 'b', 'j']]⟩, ⟨[['h', 'u', 'k', 'a', 'k', 'a', 'i', 'n', 'i', 'm', 'o']], [['m', 'y', 's', 't', 'e', 'r', 'i', 'o', 'u', 's', 'l', 'y']]⟩, ⟨[['a', 't', 'o', ' ', 'o', ' ', 't', 'u', 'k', 'e'], ['m', 'a', 'w', 'a', 's', 'i', 't', 'e', 'i', 'r', 'u']], [['b', 'e'], ['f', 'o', 'l', 'l', 'o', 'w', 'i', 'n', 'g']]⟩, ⟨[['t', 'o']], [['C', 'o', 'm', 'p']]⟩, ⟨[['i', 't', 't', 'a']], [['s', 'a', 'i', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .acceptable)]
    paperFeatures := [("diagnostic", "mysteriously"), ("environment", "logophoric verb")] }

def ex_50 : Datum :=
  { id := "sells1987_50"
    source := ⟨"sells-1987", "(50)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo wa Takasi kara Yosiko ga hukakainimo ato o tuke-mawasiteiru to kiita."
    glossedTokens := [("Taroo", "Taroo"), ("wa", "Top"), ("Takasi", "Takasi"), ("kara", "from"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("hukakainimo", "mysteriously"), ("ato o tuke-mawasiteiru", "be-following"), ("to", "Comp"), ("kiita", "heard")]
    glossedWords := [⟨[['T', 'a', 'r', 'o', 'o']], [['T', 'a', 'r', 'o', 'o']]⟩, ⟨[['w', 'a']], [['T', 'o', 'p']]⟩, ⟨[['T', 'a', 'k', 'a', 's', 'i']], [['T', 'a', 'k', 'a', 's', 'i']]⟩, ⟨[['k', 'a', 'r', 'a']], [['f', 'r', 'o', 'm']]⟩, ⟨[['Y', 'o', 's', 'i', 'k', 'o']], [['Y', 'o', 's', 'i', 'k', 'o']]⟩, ⟨[['g', 'a']], [['S', 'u', 'b', 'j']]⟩, ⟨[['h', 'u', 'k', 'a', 'k', 'a', 'i', 'n', 'i', 'm', 'o']], [['m', 'y', 's', 't', 'e', 'r', 'i', 'o', 'u', 's', 'l', 'y']]⟩, ⟨[['a', 't', 'o', ' ', 'o', ' ', 't', 'u', 'k', 'e'], ['m', 'a', 'w', 'a', 's', 'i', 't', 'e', 'i', 'r', 'u']], [['b', 'e'], ['f', 'o', 'l', 'l', 'o', 'w', 'i', 'n', 'g']]⟩, ⟨[['t', 'o']], [['C', 'o', 'm', 'p']]⟩, ⟨[['k', 'i', 'i', 't', 'a']], [['h', 'e', 'a', 'r', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .acceptable)]
    paperFeatures := [("diagnostic", "mysteriously"), ("environment", "logophoric verb")] }

def ex_51 : Datum :=
  { id := "sells1987_51"
    source := ⟨"sells-1987", "(51)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Yosiko ga hukakainimo ato o tuke-mawasiteiru koto ga Takasi o iradataseteiru."
    glossedTokens := [("Yosiko", "Yosiko"), ("ga", "Subj"), ("hukakainimo", "mysteriously"), ("ato o tuke-mawasiteiru", "be-following"), ("koto", "Comp"), ("ga", "Subj"), ("Takasi", "Takasi"), ("o", "Obj"), ("iradataseteiru", "bothers")]
    glossedWords := [⟨[['Y', 'o', 's', 'i', 'k', 'o']], [['Y', 'o', 's', 'i', 'k', 'o']]⟩, ⟨[['g', 'a']], [['S', 'u', 'b', 'j']]⟩, ⟨[['h', 'u', 'k', 'a', 'k', 'a', 'i', 'n', 'i', 'm', 'o']], [['m', 'y', 's', 't', 'e', 'r', 'i', 'o', 'u', 's', 'l', 'y']]⟩, ⟨[['a', 't', 'o', ' ', 'o', ' ', 't', 'u', 'k', 'e'], ['m', 'a', 'w', 'a', 's', 'i', 't', 'e', 'i', 'r', 'u']], [['b', 'e'], ['f', 'o', 'l', 'l', 'o', 'w', 'i', 'n', 'g']]⟩, ⟨[['k', 'o', 't', 'o']], [['C', 'o', 'm', 'p']]⟩, ⟨[['g', 'a']], [['S', 'u', 'b', 'j']]⟩, ⟨[['T', 'a', 'k', 'a', 's', 'i']], [['T', 'a', 'k', 'a', 's', 'i']]⟩, ⟨[['o']], [['O', 'b', 'j']]⟩, ⟨[['i', 'r', 'a', 'd', 'a', 't', 'a', 's', 'e', 't', 'e', 'i', 'r', 'u']], [['b', 'o', 't', 'h', 'e', 'r', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .acceptable)]
    paperFeatures := [("diagnostic", "mysteriously"), ("environment", "psych-verb")] }

def ex_52 : Datum :=
  { id := "sells1987_52"
    source := ⟨"sells-1987", "(52)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Yosiko ga hukakainimo ato o tuke-mawasiteiru noni Takasi wa ki ni sitei-nai."
    glossedTokens := [("Yosiko", "Yosiko"), ("ga", "Subj"), ("hukakainimo", "mysteriously"), ("ato o tuke-mawasiteiru", "be-following"), ("noni", "though"), ("Takasi", "Takasi"), ("wa", "Top"), ("ki", "care"), ("ni", "to"), ("sitei-nai", "give-not")]
    glossedWords := [⟨[['Y', 'o', 's', 'i', 'k', 'o']], [['Y', 'o', 's', 'i', 'k', 'o']]⟩, ⟨[['g', 'a']], [['S', 'u', 'b', 'j']]⟩, ⟨[['h', 'u', 'k', 'a', 'k', 'a', 'i', 'n', 'i', 'm', 'o']], [['m', 'y', 's', 't', 'e', 'r', 'i', 'o', 'u', 's', 'l', 'y']]⟩, ⟨[['a', 't', 'o', ' ', 'o', ' ', 't', 'u', 'k', 'e'], ['m', 'a', 'w', 'a', 's', 'i', 't', 'e', 'i', 'r', 'u']], [['b', 'e'], ['f', 'o', 'l', 'l', 'o', 'w', 'i', 'n', 'g']]⟩, ⟨[['n', 'o', 'n', 'i']], [['t', 'h', 'o', 'u', 'g', 'h']]⟩, ⟨[['T', 'a', 'k', 'a', 's', 'i']], [['T', 'a', 'k', 'a', 's', 'i']]⟩, ⟨[['w', 'a']], [['T', 'o', 'p']]⟩, ⟨[['k', 'i']], [['c', 'a', 'r', 'e']]⟩, ⟨[['n', 'i']], [['t', 'o']]⟩, ⟨[['s', 'i', 't', 'e', 'i'], ['n', 'a', 'i']], [['g', 'i', 'v', 'e'], ['n', 'o', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .unacceptable), ("external speaker", .acceptable)]
    paperFeatures := [("diagnostic", "mysteriously"), ("environment", "3POV")] }

def ex_56 : Datum :=
  { id := "sells1987_56"
    source := ⟨"sells-1987", "(56)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Takasi wa Taroo ni itosii Yosiko ga zibun o nikundeiru koto o hanasita."
    glossedTokens := [("Takasi", "Takasi"), ("wa", "Top"), ("Taroo", "Taroo"), ("ni", "Dat"), ("itosii", "beloved"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("zibun", "self"), ("o", "Obj"), ("nikundeiru", "be-hating"), ("koto", "Comp"), ("o", "Obj"), ("hanasita", "told")]
    glossedWords := [⟨[['T', 'a', 'k', 'a', 's', 'i']], [['T', 'a', 'k', 'a', 's', 'i']]⟩, ⟨[['w', 'a']], [['T', 'o', 'p']]⟩, ⟨[['T', 'a', 'r', 'o', 'o']], [['T', 'a', 'r', 'o', 'o']]⟩, ⟨[['n', 'i']], [['D', 'a', 't']]⟩, ⟨[['i', 't', 'o', 's', 'i', 'i']], [['b', 'e', 'l', 'o', 'v', 'e', 'd']]⟩, ⟨[['Y', 'o', 's', 'i', 'k', 'o']], [['Y', 'o', 's', 'i', 'k', 'o']]⟩, ⟨[['g', 'a']], [['S', 'u', 'b', 'j']]⟩, ⟨[['z', 'i', 'b', 'u', 'n']], [['s', 'e', 'l', 'f']]⟩, ⟨[['o']], [['O', 'b', 'j']]⟩, ⟨[['n', 'i', 'k', 'u', 'n', 'd', 'e', 'i', 'r', 'u']], [['b', 'e'], ['h', 'a', 't', 'i', 'n', 'g']]⟩, ⟨[['k', 'o', 't', 'o']], [['C', 'o', 'm', 'p']]⟩, ⟨[['o']], [['O', 'b', 'j']]⟩, ⟨[['h', 'a', 'n', 'a', 's', 'i', 't', 'a']], [['t', 'o', 'l', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .acceptable)]
    paperFeatures := [("pronoun", "zibun"), ("diagnostic", "beloved"), ("environment", "logophoric verb")] }

def ex_57 : Datum :=
  { id := "sells1987_57"
    source := ⟨"sells-1987", "(57)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo wa Takasi kara itosii Yosiko ga zibun o nikundeiru to kiita."
    glossedTokens := [("Taroo", "Taroo"), ("wa", "Top"), ("Takasi", "Takasi"), ("kara", "from"), ("itosii", "beloved"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("zibun", "self"), ("o", "Obj"), ("nikundeiru", "be-hating"), ("to", "Comp"), ("kiita", "heard")]
    glossedWords := [⟨[['T', 'a', 'r', 'o', 'o']], [['T', 'a', 'r', 'o', 'o']]⟩, ⟨[['w', 'a']], [['T', 'o', 'p']]⟩, ⟨[['T', 'a', 'k', 'a', 's', 'i']], [['T', 'a', 'k', 'a', 's', 'i']]⟩, ⟨[['k', 'a', 'r', 'a']], [['f', 'r', 'o', 'm']]⟩, ⟨[['i', 't', 'o', 's', 'i', 'i']], [['b', 'e', 'l', 'o', 'v', 'e', 'd']]⟩, ⟨[['Y', 'o', 's', 'i', 'k', 'o']], [['Y', 'o', 's', 'i', 'k', 'o']]⟩, ⟨[['g', 'a']], [['S', 'u', 'b', 'j']]⟩, ⟨[['z', 'i', 'b', 'u', 'n']], [['s', 'e', 'l', 'f']]⟩, ⟨[['o']], [['O', 'b', 'j']]⟩, ⟨[['n', 'i', 'k', 'u', 'n', 'd', 'e', 'i', 'r', 'u']], [['b', 'e'], ['h', 'a', 't', 'i', 'n', 'g']]⟩, ⟨[['t', 'o']], [['C', 'o', 'm', 'p']]⟩, ⟨[['k', 'i', 'i', 't', 'a']], [['h', 'e', 'a', 'r', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .acceptable)]
    paperFeatures := [("pronoun", "zibun"), ("diagnostic", "beloved"), ("environment", "logophoric verb")] }

def ex_58 : Datum :=
  { id := "sells1987_58"
    source := ⟨"sells-1987", "(58)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Itosii Yosiko ga zibun o nikundeiru koto ga Mitiko o zetuboo e oiyatta."
    glossedTokens := [("Itosii", "beloved"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("zibun", "self"), ("o", "Obj"), ("nikundeiru", "be-hating"), ("koto", "Comp"), ("ga", "Subj"), ("Mitiko", "Mitiko"), ("o", "Obj"), ("zetuboo", "desperation"), ("e", "to"), ("oiyatta", "drove")]
    glossedWords := [⟨[['I', 't', 'o', 's', 'i', 'i']], [['b', 'e', 'l', 'o', 'v', 'e', 'd']]⟩, ⟨[['Y', 'o', 's', 'i', 'k', 'o']], [['Y', 'o', 's', 'i', 'k', 'o']]⟩, ⟨[['g', 'a']], [['S', 'u', 'b', 'j']]⟩, ⟨[['z', 'i', 'b', 'u', 'n']], [['s', 'e', 'l', 'f']]⟩, ⟨[['o']], [['O', 'b', 'j']]⟩, ⟨[['n', 'i', 'k', 'u', 'n', 'd', 'e', 'i', 'r', 'u']], [['b', 'e'], ['h', 'a', 't', 'i', 'n', 'g']]⟩, ⟨[['k', 'o', 't', 'o']], [['C', 'o', 'm', 'p']]⟩, ⟨[['g', 'a']], [['S', 'u', 'b', 'j']]⟩, ⟨[['M', 'i', 't', 'i', 'k', 'o']], [['M', 'i', 't', 'i', 'k', 'o']]⟩, ⟨[['o']], [['O', 'b', 'j']]⟩, ⟨[['z', 'e', 't', 'u', 'b', 'o', 'o']], [['d', 'e', 's', 'p', 'e', 'r', 'a', 't', 'i', 'o', 'n']]⟩, ⟨[['e']], [['t', 'o']]⟩, ⟨[['o', 'i', 'y', 'a', 't', 't', 'a']], [['d', 'r', 'o', 'v', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .acceptable)]
    paperFeatures := [("pronoun", "zibun"), ("diagnostic", "beloved"), ("environment", "psych-verb")] }

def ex_59 : Datum :=
  { id := "sells1987_59"
    source := ⟨"sells-1987", "(59)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Takasi wa itosii Yosiko ga mizu o zibun no ue ni kobosita node nurete-simatta."
    glossedTokens := [("Takasi", "Takasi"), ("wa", "Top"), ("itosii", "beloved"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("mizu", "water"), ("o", "Obj"), ("zibun", "self"), ("no", "Gen"), ("ue", "on"), ("ni", "Loc"), ("kobosita", "spilled"), ("node", "because"), ("nurete-simatta", "wet-got")]
    glossedWords := [⟨[['T', 'a', 'k', 'a', 's', 'i']], [['T', 'a', 'k', 'a', 's', 'i']]⟩, ⟨[['w', 'a']], [['T', 'o', 'p']]⟩, ⟨[['i', 't', 'o', 's', 'i', 'i']], [['b', 'e', 'l', 'o', 'v', 'e', 'd']]⟩, ⟨[['Y', 'o', 's', 'i', 'k', 'o']], [['Y', 'o', 's', 'i', 'k', 'o']]⟩, ⟨[['g', 'a']], [['S', 'u', 'b', 'j']]⟩, ⟨[['m', 'i', 'z', 'u']], [['w', 'a', 't', 'e', 'r']]⟩, ⟨[['o']], [['O', 'b', 'j']]⟩, ⟨[['z', 'i', 'b', 'u', 'n']], [['s', 'e', 'l', 'f']]⟩, ⟨[['n', 'o']], [['G', 'e', 'n']]⟩, ⟨[['u', 'e']], [['o', 'n']]⟩, ⟨[['n', 'i']], [['L', 'o', 'c']]⟩, ⟨[['k', 'o', 'b', 'o', 's', 'i', 't', 'a']], [['s', 'p', 'i', 'l', 'l', 'e', 'd']]⟩, ⟨[['n', 'o', 'd', 'e']], [['b', 'e', 'c', 'a', 'u', 's', 'e']]⟩, ⟨[['n', 'u', 'r', 'e', 't', 'e'], ['s', 'i', 'm', 'a', 't', 't', 'a']], [['w', 'e', 't'], ['g', 'o', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .acceptable)]
    paperFeatures := [("pronoun", "zibun"), ("diagnostic", "beloved"), ("environment", "3POV")] }

def ex_60 : Datum :=
  { id := "sells1987_60"
    source := ⟨"sells-1987", "(60)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Takasi wa Yosiko ga mizu o zibun no ue ni kobosita node nurete-simatta."
    glossedTokens := [("Takasi", "Takasi"), ("wa", "Top"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("mizu", "water"), ("o", "Obj"), ("zibun", "self"), ("no", "Gen"), ("ue", "on"), ("ni", "Loc"), ("kobosita", "spilled"), ("node", "because"), ("nurete-simatta", "wet-got")]
    glossedWords := [⟨[['T', 'a', 'k', 'a', 's', 'i']], [['T', 'a', 'k', 'a', 's', 'i']]⟩, ⟨[['w', 'a']], [['T', 'o', 'p']]⟩, ⟨[['Y', 'o', 's', 'i', 'k', 'o']], [['Y', 'o', 's', 'i', 'k', 'o']]⟩, ⟨[['g', 'a']], [['S', 'u', 'b', 'j']]⟩, ⟨[['m', 'i', 'z', 'u']], [['w', 'a', 't', 'e', 'r']]⟩, ⟨[['o']], [['O', 'b', 'j']]⟩, ⟨[['z', 'i', 'b', 'u', 'n']], [['s', 'e', 'l', 'f']]⟩, ⟨[['n', 'o']], [['G', 'e', 'n']]⟩, ⟨[['u', 'e']], [['o', 'n']]⟩, ⟨[['n', 'i']], [['L', 'o', 'c']]⟩, ⟨[['k', 'o', 'b', 'o', 's', 'i', 't', 'a']], [['s', 'p', 'i', 'l', 'l', 'e', 'd']]⟩, ⟨[['n', 'o', 'd', 'e']], [['b', 'e', 'c', 'a', 'u', 's', 'e']]⟩, ⟨[['n', 'u', 'r', 'e', 't', 'e'], ['s', 'i', 'm', 'a', 't', 't', 'a']], [['w', 'e', 't'], ['g', 'o', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "zibun"), ("environment", "3POV")] }

def ex_61 : Datum :=
  { id := "sells1987_61"
    source := ⟨"sells-1987", "(61)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Takasi wa Yosiko ga mizu o zibun no ue ni kobosita toki nurete-simatta."
    glossedTokens := [("Takasi", "Takasi"), ("wa", "Top"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("mizu", "water"), ("o", "Obj"), ("zibun", "self"), ("no", "Gen"), ("ue", "on"), ("ni", "Loc"), ("kobosita", "spilled"), ("toki", "when"), ("nurete-simatta", "wet-got")]
    glossedWords := [⟨[['T', 'a', 'k', 'a', 's', 'i']], [['T', 'a', 'k', 'a', 's', 'i']]⟩, ⟨[['w', 'a']], [['T', 'o', 'p']]⟩, ⟨[['Y', 'o', 's', 'i', 'k', 'o']], [['Y', 'o', 's', 'i', 'k', 'o']]⟩, ⟨[['g', 'a']], [['S', 'u', 'b', 'j']]⟩, ⟨[['m', 'i', 'z', 'u']], [['w', 'a', 't', 'e', 'r']]⟩, ⟨[['o']], [['O', 'b', 'j']]⟩, ⟨[['z', 'i', 'b', 'u', 'n']], [['s', 'e', 'l', 'f']]⟩, ⟨[['n', 'o']], [['G', 'e', 'n']]⟩, ⟨[['u', 'e']], [['o', 'n']]⟩, ⟨[['n', 'i']], [['L', 'o', 'c']]⟩, ⟨[['k', 'o', 'b', 'o', 's', 'i', 't', 'a']], [['s', 'p', 'i', 'l', 'l', 'e', 'd']]⟩, ⟨[['t', 'o', 'k', 'i']], [['w', 'h', 'e', 'n']]⟩, ⟨[['n', 'u', 'r', 'e', 't', 'e'], ['s', 'i', 'm', 'a', 't', 't', 'a']], [['w', 'e', 't'], ['g', 'o', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "zibun"), ("environment", "external")] }

def ex_71 : Datum :=
  { id := "sells1987_71"
    source := ⟨"sells-1987", "(71)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Oedipus wa Jocasta ga zibun o unda ie de ima wa kodomotati to koohuku-soo-ni kurasite-imasu."
    glossedTokens := [("Oedipus", "Oedipus"), ("wa", "Top"), ("Jocasta", "Jocasta"), ("ga", "Subj"), ("zibun", "self"), ("o", "Obj"), ("unda", "bore"), ("ie", "house"), ("de", "Loc"), ("ima", "now"), ("wa", "Top"), ("kodomotati", "children"), ("to", "with"), ("koohuku-soo-ni", "happily"), ("kurasite-imasu", "living-is")]
    glossedWords := [⟨[['O', 'e', 'd', 'i', 'p', 'u', 's']], [['O', 'e', 'd', 'i', 'p', 'u', 's']]⟩, ⟨[['w', 'a']], [['T', 'o', 'p']]⟩, ⟨[['J', 'o', 'c', 'a', 's', 't', 'a']], [['J', 'o', 'c', 'a', 's', 't', 'a']]⟩, ⟨[['g', 'a']], [['S', 'u', 'b', 'j']]⟩, ⟨[['z', 'i', 'b', 'u', 'n']], [['s', 'e', 'l', 'f']]⟩, ⟨[['o']], [['O', 'b', 'j']]⟩, ⟨[['u', 'n', 'd', 'a']], [['b', 'o', 'r', 'e']]⟩, ⟨[['i', 'e']], [['h', 'o', 'u', 's', 'e']]⟩, ⟨[['d', 'e']], [['L', 'o', 'c']]⟩, ⟨[['i', 'm', 'a']], [['n', 'o', 'w']]⟩, ⟨[['w', 'a']], [['T', 'o', 'p']]⟩, ⟨[['k', 'o', 'd', 'o', 'm', 'o', 't', 'a', 't', 'i']], [['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n']]⟩, ⟨[['t', 'o']], [['w', 'i', 't', 'h']]⟩, ⟨[['k', 'o', 'o', 'h', 'u', 'k', 'u'], ['s', 'o', 'o'], ['n', 'i']], [['h', 'a', 'p', 'p', 'i', 'l', 'y']]⟩, ⟨[['k', 'u', 'r', 'a', 's', 'i', 't', 'e'], ['i', 'm', 'a', 's', 'u']], [['l', 'i', 'v', 'i', 'n', 'g'], ['i', 's']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "zibun"), ("environment", "3POV")] }

def ex_72 : Datum :=
  { id := "sells1987_72"
    source := ⟨"sells-1987", "(72)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Takasi wa Taroo ni Yosiko ga zibun o nikundeiru koto o hanasanakatta."
    glossedTokens := [("Takasi", "Takasi"), ("wa", "Top"), ("Taroo", "Taroo"), ("ni", "Dat"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("zibun", "self"), ("o", "Obj"), ("nikundeiru", "be-hating"), ("koto", "Comp"), ("o", "Obj"), ("hanasanakatta", "told-not")]
    glossedWords := [⟨[['T', 'a', 'k', 'a', 's', 'i']], [['T', 'a', 'k', 'a', 's', 'i']]⟩, ⟨[['w', 'a']], [['T', 'o', 'p']]⟩, ⟨[['T', 'a', 'r', 'o', 'o']], [['T', 'a', 'r', 'o', 'o']]⟩, ⟨[['n', 'i']], [['D', 'a', 't']]⟩, ⟨[['Y', 'o', 's', 'i', 'k', 'o']], [['Y', 'o', 's', 'i', 'k', 'o']]⟩, ⟨[['g', 'a']], [['S', 'u', 'b', 'j']]⟩, ⟨[['z', 'i', 'b', 'u', 'n']], [['s', 'e', 'l', 'f']]⟩, ⟨[['o']], [['O', 'b', 'j']]⟩, ⟨[['n', 'i', 'k', 'u', 'n', 'd', 'e', 'i', 'r', 'u']], [['b', 'e'], ['h', 'a', 't', 'i', 'n', 'g']]⟩, ⟨[['k', 'o', 't', 'o']], [['C', 'o', 'm', 'p']]⟩, ⟨[['o']], [['O', 'b', 'j']]⟩, ⟨[['h', 'a', 'n', 'a', 's', 'a', 'n', 'a', 'k', 'a', 't', 't', 'a']], [['t', 'o', 'l', 'd'], ['n', 'o', 't']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "zibun"), ("environment", "logophoric verb")] }

def ex_73 : Datum :=
  { id := "sells1987_73"
    source := ⟨"sells-1987", "(73)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo wa Takasi kara Yosiko ga zibun o nikundeiru to kikanakatta."
    glossedTokens := [("Taroo", "Taroo"), ("wa", "Top"), ("Takasi", "Takasi"), ("kara", "from"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("zibun", "self"), ("o", "Obj"), ("nikundeiru", "be-hating"), ("to", "Comp"), ("kikanakatta", "heard-not")]
    glossedWords := [⟨[['T', 'a', 'r', 'o', 'o']], [['T', 'a', 'r', 'o', 'o']]⟩, ⟨[['w', 'a']], [['T', 'o', 'p']]⟩, ⟨[['T', 'a', 'k', 'a', 's', 'i']], [['T', 'a', 'k', 'a', 's', 'i']]⟩, ⟨[['k', 'a', 'r', 'a']], [['f', 'r', 'o', 'm']]⟩, ⟨[['Y', 'o', 's', 'i', 'k', 'o']], [['Y', 'o', 's', 'i', 'k', 'o']]⟩, ⟨[['g', 'a']], [['S', 'u', 'b', 'j']]⟩, ⟨[['z', 'i', 'b', 'u', 'n']], [['s', 'e', 'l', 'f']]⟩, ⟨[['o']], [['O', 'b', 'j']]⟩, ⟨[['n', 'i', 'k', 'u', 'n', 'd', 'e', 'i', 'r', 'u']], [['b', 'e'], ['h', 'a', 't', 'i', 'n', 'g']]⟩, ⟨[['t', 'o']], [['C', 'o', 'm', 'p']]⟩, ⟨[['k', 'i', 'k', 'a', 'n', 'a', 'k', 'a', 't', 't', 'a']], [['h', 'e', 'a', 'r', 'd'], ['n', 'o', 't']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "zibun"), ("environment", "logophoric verb")] }

def ex_74 : Datum :=
  { id := "sells1987_74"
    source := ⟨"sells-1987", "(74)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Yosiko ga zibun o nikundeiru koto ga Mitiko o yuutunisite-wa-inai."
    glossedTokens := [("Yosiko", "Yosiko"), ("ga", "Subj"), ("zibun", "self"), ("o", "Obj"), ("nikundeiru", "be-hating"), ("koto", "Comp"), ("ga", "Subj"), ("Mitiko", "Mitiko"), ("o", "Obj"), ("yuutunisite-wa-inai", "bothered-at all-not")]
    glossedWords := [⟨[['Y', 'o', 's', 'i', 'k', 'o']], [['Y', 'o', 's', 'i', 'k', 'o']]⟩, ⟨[['g', 'a']], [['S', 'u', 'b', 'j']]⟩, ⟨[['z', 'i', 'b', 'u', 'n']], [['s', 'e', 'l', 'f']]⟩, ⟨[['o']], [['O', 'b', 'j']]⟩, ⟨[['n', 'i', 'k', 'u', 'n', 'd', 'e', 'i', 'r', 'u']], [['b', 'e'], ['h', 'a', 't', 'i', 'n', 'g']]⟩, ⟨[['k', 'o', 't', 'o']], [['C', 'o', 'm', 'p']]⟩, ⟨[['g', 'a']], [['S', 'u', 'b', 'j']]⟩, ⟨[['M', 'i', 't', 'i', 'k', 'o']], [['M', 'i', 't', 'i', 'k', 'o']]⟩, ⟨[['o']], [['O', 'b', 'j']]⟩, ⟨[['y', 'u', 'u', 't', 'u', 'n', 'i', 's', 'i', 't', 'e'], ['w', 'a'], ['i', 'n', 'a', 'i']], [['b', 'o', 't', 'h', 'e', 'r', 'e', 'd'], ['a', 't', ' ', 'a', 'l', 'l'], ['n', 'o', 't']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "zibun"), ("environment", "psych-verb")] }

def ex_75 : Datum :=
  { id := "sells1987_75"
    source := ⟨"sells-1987", "(75)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Takasi wa Yosiko ga zibun o tazunete-kita node kanasigaranakatta."
    glossedTokens := [("Takasi", "Takasi"), ("wa", "Top"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("zibun", "self"), ("o", "Obj"), ("tazunete-kita", "visit-came"), ("node", "because"), ("kanasigaranakatta", "sad(verb)-not-Past")]
    glossedWords := [⟨[['T', 'a', 'k', 'a', 's', 'i']], [['T', 'a', 'k', 'a', 's', 'i']]⟩, ⟨[['w', 'a']], [['T', 'o', 'p']]⟩, ⟨[['Y', 'o', 's', 'i', 'k', 'o']], [['Y', 'o', 's', 'i', 'k', 'o']]⟩, ⟨[['g', 'a']], [['S', 'u', 'b', 'j']]⟩, ⟨[['z', 'i', 'b', 'u', 'n']], [['s', 'e', 'l', 'f']]⟩, ⟨[['o']], [['O', 'b', 'j']]⟩, ⟨[['t', 'a', 'z', 'u', 'n', 'e', 't', 'e'], ['k', 'i', 't', 'a']], [['v', 'i', 's', 'i', 't'], ['c', 'a', 'm', 'e']]⟩, ⟨[['n', 'o', 'd', 'e']], [['b', 'e', 'c', 'a', 'u', 's', 'e']]⟩, ⟨[['k', 'a', 'n', 'a', 's', 'i', 'g', 'a', 'r', 'a', 'n', 'a', 'k', 'a', 't', 't', 'a']], [['s', 'a', 'd', '(', 'v', 'e', 'r', 'b', ')'], ['n', 'o', 't'], ['P', 'a', 's', 't']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "zibun"), ("environment", "3POV")] }

def ex_76 : Datum :=
  { id := "sells1987_76"
    source := ⟨"sells-1987", "(76)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jón er hér enn þó að María kyssi sig."
    glossedTokens := [("Jón", "Jon"), ("er", "is"), ("hér", "here"), ("enn", "still"), ("þó að", "although"), ("María", "Maria"), ("kyssi", "kisses(subj)"), ("sig", "self")]
    glossedWords := [⟨[['J', 'ó', 'n']], [['J', 'o', 'n']]⟩, ⟨[['e', 'r']], [['i', 's']]⟩, ⟨[['h', 'é', 'r']], [['h', 'e', 'r', 'e']]⟩, ⟨[['e', 'n', 'n']], [['s', 't', 'i', 'l', 'l']]⟩, ⟨[['þ', 'ó', ' ', 'a', 'ð']], [['a', 'l', 't', 'h', 'o', 'u', 'g', 'h']]⟩, ⟨[['M', 'a', 'r', 'í', 'a']], [['M', 'a', 'r', 'i', 'a']]⟩, ⟨[['k', 'y', 's', 's', 'i']], [['k', 'i', 's', 's', 'e', 's', '(', 's', 'u', 'b', 'j', ')']]⟩, ⟨[['s', 'i', 'g']], [['s', 'e', 'l', 'f']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "sig"), ("environment", "external")] }

def ex_77 : Datum :=
  { id := "sells1987_77"
    source := ⟨"sells-1987", "(77)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jón segir að Haraldur sé hér enn þó að María kyssi sig."
    glossedTokens := [("Jón", "Jon"), ("segir", "says"), ("að", "that"), ("Haraldur", "Harold"), ("sé", "is(subj)"), ("hér", "here"), ("enn", "still"), ("þó að", "although"), ("María", "Maria"), ("kyssi", "kisses(subj)"), ("sig", "self")]
    glossedWords := [⟨[['J', 'ó', 'n']], [['J', 'o', 'n']]⟩, ⟨[['s', 'e', 'g', 'i', 'r']], [['s', 'a', 'y', 's']]⟩, ⟨[['a', 'ð']], [['t', 'h', 'a', 't']]⟩, ⟨[['H', 'a', 'r', 'a', 'l', 'd', 'u', 'r']], [['H', 'a', 'r', 'o', 'l', 'd']]⟩, ⟨[['s', 'é']], [['i', 's', '(', 's', 'u', 'b', 'j', ')']]⟩, ⟨[['h', 'é', 'r']], [['h', 'e', 'r', 'e']]⟩, ⟨[['e', 'n', 'n']], [['s', 't', 'i', 'l', 'l']]⟩, ⟨[['þ', 'ó', ' ', 'a', 'ð']], [['a', 'l', 't', 'h', 'o', 'u', 'g', 'h']]⟩, ⟨[['M', 'a', 'r', 'í', 'a']], [['M', 'a', 'r', 'i', 'a']]⟩, ⟨[['k', 'y', 's', 's', 'i']], [['k', 'i', 's', 's', 'e', 's', '(', 's', 'u', 'b', 'j', ')']]⟩, ⟨[['s', 'i', 'g']], [['s', 'e', 'l', 'f']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "sig"), ("environment", "logophoric verb")] }

def all : List Datum := [ex_11a, ex_12, ex_17, ex_43, ex_44, ex_45, ex_46, ex_47, ex_48, ex_49, ex_50, ex_51, ex_52, ex_56, ex_57, ex_58, ex_59, ex_60, ex_61, ex_71, ex_72, ex_73, ex_74, ex_75, ex_76, ex_77]

end Sells1987.Examples
