module

public import Linglib.Data.Examples.Schema

/-!
# `Dayal2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Dayal2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Dayal2025.Examples`.
-/

@[expose] public section

namespace Dayal2025.Examples

def ex3b : Datum :=
  { id := "dayal2025_ex3b"
    source := ⟨"dayal-2025", "(3b)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "ravi ja:nta: hai (ki) anu ja:egi: *(ya: nahĩ:)."
    glossedTokens := [("ravi", "Ravi"), ("ja:nta:", "knows"), ("hai", ""), ("ki", "SUB"), ("anu", "Anu"), ("ja:egi:", "will.go"), ("ya:", "or"), ("nahĩ:", "not")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1"), ("particle", "ya: nahĩ:"), ("embedding", "subordination")] }

def ex5a : Datum :=
  { id := "dayal2025_ex5a"
    source := ⟨"dayal-2025", "(5a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Mary-wa hon-o kai-masi-ta (ka)?"
    glossedTokens := [("Mary-wa", "Mary-TOP"), ("hon-o", "book-ACC"), ("kai-masi-ta", "buy-POL-PST"), ("ka", "Q")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1"), ("particle", "ka"), ("embedding", "matrix")] }

def ex5b : Datum :=
  { id := "dayal2025_ex5b"
    source := ⟨"dayal-2025", "(5b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Tanaka-kun-wa [Mary-ga hon-o kat-ta ka] sit-tei-mas-u."
    glossedTokens := [("Tanaka-kun-wa", "Tanaka-HON-TOP"), ("Mary-ga", "Mary-NOM"), ("hon-o", "book-ACC"), ("kat-ta", "buy-PST"), ("ka", "Q"), ("sit-tei-mas-u", "know-PROG-POL-PRS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.1"), ("particle", "ka"), ("embedding", "subordination")] }

def ex8a : Datum :=
  { id := "dayal2025_ex8a"
    source := ⟨"mccloskey-2006", ""⟩
    reportedIn := some ⟨"dayal-2025", "(8a)"⟩
    language := "stan1293"
    primaryText := "I wondered [was he illiterate↑]."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2"), ("verb", "wonder"), ("embedding", "quasi")] }

def ex8b : Datum :=
  { id := "dayal2025_ex8b"
    source := ⟨"mccloskey-2006", ""⟩
    reportedIn := some ⟨"dayal-2025", "(8b)"⟩
    language := "stan1293"
    primaryText := "I asked him [from what source could the reprisals come↑]."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2"), ("verb", "ask"), ("embedding", "quasi")] }

def ex9a : Datum :=
  { id := "dayal2025_ex9a"
    source := ⟨"mccloskey-2006", ""⟩
    reportedIn := some ⟨"dayal-2025", "(9a)"⟩
    language := "stan1293"
    primaryText := "I knew [was he illiterate↑]."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2"), ("verb", "know"), ("embedding", "quasi")] }

def ex11a : Datum :=
  { id := "dayal2025_ex11a"
    source := ⟨"dayal-2025", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The question is [whether Mary will leave]."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2"), ("embedding", "subordination")] }

def ex11b : Datum :=
  { id := "dayal2025_ex11b"
    source := ⟨"dayal-2025", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The question is, [will Mary leave↑]."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2"), ("embedding", "quasi")] }

def ex11c : Datum :=
  { id := "dayal2025_ex11c"
    source := ⟨"dayal-2025", "(11c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "[Whether Mary will leave] depends on Sue."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2"), ("verb", "depend on"), ("embedding", "subordination")] }

def ex11d : Datum :=
  { id := "dayal2025_ex11d"
    source := ⟨"dayal-2025", "(11d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "[Will Mary leave↑] depends on Sue."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2"), ("verb", "depend on"), ("embedding", "quasi")] }

def ex13a : Datum :=
  { id := "dayal2025_ex13a"
    source := ⟨"dayal-2025", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The question is, [is it raining↑]."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("The question is, [it's raining↑].", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "1.2"), ("embedding", "quasi"), ("syntax", "interrogative")] }

def ex14a : Datum :=
  { id := "dayal2025_ex14a"
    source := ⟨"dayal-2025", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She asked, \"Is it raining↑\""
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2"), ("verb", "ask"), ("embedding", "quotation")] }

def ex14b : Datum :=
  { id := "dayal2025_ex14b"
    source := ⟨"dayal-2025", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She asked, \"It's raining↓\""
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("She said, \"It's raining↓\"", .acceptable)]
    readings := []
    paperFeatures := [("section", "1.2"), ("verb", "ask"), ("complement", "declarativeAssertion")] }

def ex14c : Datum :=
  { id := "dayal2025_ex14c"
    source := ⟨"dayal-2025", "(14c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She asked, \"It's raining↑\""
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.2"), ("verb", "ask"), ("embedding", "quotation"), ("syntax", "declarative")] }

def ex15b : Datum :=
  { id := "dayal2025_ex15b"
    source := ⟨"dayal-2025", "(15b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Tanaka-kun-wa [Mary-ga nani-o kat-ta *(ka)] sit-tei-mas-u."
    glossedTokens := [("Tanaka-kun-wa", "Tanaka-HON-TOP"), ("Mary-ga", "Mary-NOM"), ("nani-o", "what-ACC"), ("kat-ta", "buy-PST"), ("ka", "Q"), ("sit-tei-mas-u", "know-PROG-POL-PRS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.3"), ("particle", "ka"), ("embedding", "subordination")] }

def ex16b : Datum :=
  { id := "dayal2025_ex16b"
    source := ⟨"dayal-2025", "(16b)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "ravi ja:nta: hai ki kya: anu ja:egi:."
    glossedTokens := [("ravi", "Ravi"), ("ja:nta:", "knows"), ("hai", ""), ("ki", "SUB"), ("kya:", "PQP"), ("anu", "Anu"), ("ja:egi:", "will.go")]
    context := ""
    judgment := .ungrammatical
    alternatives := [("ravi ja:nta: hai ki anu ja:egi:.", .acceptable)]
    readings := []
    paperFeatures := [("section", "1.3"), ("particle", "kya:"), ("embedding", "subordination")] }

def ex17a : Datum :=
  { id := "dayal2025_ex17a"
    source := ⟨"bhatt-dayal-2020", "(9a)"⟩
    reportedIn := some ⟨"dayal-2025", "(17a)"⟩
    language := "hind1269"
    primaryText := "Ti:char-ne anu-se pu:cha: ki kya: vo ca:i piyegi:."
    glossedTokens := [("Ti:char-ne", "teacher-ERG"), ("anu-se", "Anu-INS"), ("pu:cha:", "asked"), ("ki", "SUB"), ("kya:", "PQP"), ("vo", "she"), ("ca:i", "tea"), ("piyegi:", "will.drink")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.3"), ("particle", "kya:"), ("embedding", "quasi")] }

def ex17b : Datum :=
  { id := "dayal2025_ex17b"
    source := ⟨"bhatt-dayal-2020", "(14a)"⟩
    reportedIn := some ⟨"dayal-2025", "(17b)"⟩
    language := "hind1269"
    primaryText := "sava:l yeh hai ki kya: nayi: vyavastha: ka:gar sa:bit hogi:."
    glossedTokens := [("sava:l", "question"), ("yeh", "this"), ("hai", "is"), ("ki", "SUB"), ("kya:", "PQP"), ("nayi:", "new"), ("vyavastha:", "arrangement"), ("ka:gar", "effective"), ("sa:bit", "prove"), ("hogi:", "will.be")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.3"), ("particle", "kya:"), ("embedding", "quasi")] }

def ex17c : Datum :=
  { id := "dayal2025_ex17c"
    source := ⟨"bhatt-dayal-2020", "(15b)"⟩
    reportedIn := some ⟨"dayal-2025", "(17c)"⟩
    language := "hind1269"
    primaryText := "kya: vo ja:egi: ya: nahĩ: uske mu:D par nirbhar karta: hai."
    glossedTokens := [("kya:", "PQP"), ("vo", "she"), ("ja:egi:", "will.go"), ("ya:", "or"), ("nahĩ:", "not"), ("uske", "her"), ("mu:D", "mood"), ("par", "on"), ("nirbhar", "depend"), ("karta:", "does"), ("hai", "")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.3"), ("particle", "kya:"), ("embedding", "subordination")] }

def ex18a : Datum :=
  { id := "dayal2025_ex18a"
    source := ⟨"dayal-2025", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Quick, where did you hide the matza?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.3"), ("particle", "quick"), ("embedding", "matrix")] }

def ex19a : Datum :=
  { id := "dayal2025_ex19a"
    source := ⟨"dayal-2025", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary asked Sue quick where she hid the matza."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.3"), ("particle", "quick"), ("embedding", "subordination")] }

def ex18b : Datum :=
  { id := "dayal2025_ex18b"
    source := ⟨"sauerland-yatsushiro-2017", ""⟩
    reportedIn := some ⟨"dayal-2025", "(18b)"⟩
    language := "nucl1643"
    primaryText := "Namae-wa nan da-kke (ka)?"
    glossedTokens := [("Namae-wa", "name-TOP"), ("nan", "what"), ("da-kke", "COP-KKE"), ("ka", "Q")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.3"), ("particle", "kke"), ("embedding", "matrix")] }

def ex19c : Datum :=
  { id := "dayal2025_ex19c"
    source := ⟨"dayal-2025", "(19c)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Boku-wa [(kimi-no) namae-ga nan-da-kke (ka)] siri-tai."
    glossedTokens := [("Boku-wa", "I-TOP"), ("kimi-no", "you-GEN"), ("namae-ga", "name-NOM"), ("nan-da-kke", "what-COP-KKE"), ("ka", "Q"), ("siri-tai", "know-want")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "1.3"), ("particle", "kke"), ("embedding", "subordination")] }

def ex24a_wonder : Datum :=
  { id := "dayal2025_ex24a_wonder"
    source := ⟨"dayal-2025", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary wonders [whether Sue will leave]."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1.1"), ("verb", "wonder"), ("embedding", "subordination")] }

def ex24a_know : Datum :=
  { id := "dayal2025_ex24a_know"
    source := ⟨"dayal-2025", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary knows [whether Sue will leave]."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1.1"), ("verb", "know"), ("embedding", "subordination")] }

def ex24a_believe : Datum :=
  { id := "dayal2025_ex24a_believe"
    source := ⟨"dayal-2025", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary believes [whether Sue will leave]."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1.1"), ("verb", "believe"), ("embedding", "subordination")] }

def ex38b : Datum :=
  { id := "dayal2025_ex38b"
    source := ⟨"dayal-2025", "(38b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everybody knows [did I succeed in buying chocolate for Winifred↑]."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("Everybody wants to know [did I succeed in buying chocolate for Winifred↑].", .acceptable)]
    readings := []
    paperFeatures := [("section", "3.2"), ("verb", "know"), ("embedding", "quasi")] }

def ex39a : Datum :=
  { id := "dayal2025_ex39a"
    source := ⟨"dayal-2025", "(39a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "anu ja:nna: ca:hti: hai [ki (kya:) tum cai piyoge↑]."
    glossedTokens := [("anu", "Anu"), ("ja:nna:", "to.know"), ("ca:hti:", "wants"), ("hai", ""), ("ki", "SUB"), ("kya:", "PQP"), ("tum", "you"), ("cai", "tea"), ("piyoge", "will.drink")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("embedding", "quasi"), ("verbClass", "rogativePerspP")] }

def ex39b : Datum :=
  { id := "dayal2025_ex39b"
    source := ⟨"dayal-2025", "(39b)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "anu ja:nti: hai [ki (kya:) tum cai piyoge(↑)]."
    glossedTokens := [("anu", "Anu"), ("ja:nti:", "knows"), ("hai", ""), ("ki", "SUB"), ("kya:", "PQP"), ("tum", "you"), ("cai", "tea"), ("piyoge", "will.drink")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("embedding", "quasi"), ("verbClass", "responsive")] }

def ex40a : Datum :=
  { id := "dayal2025_ex40a"
    source := ⟨"mccloskey-2006", "p. 112"⟩
    reportedIn := some ⟨"dayal-2025", "(40a)"⟩
    language := "stan1293"
    primaryText := "I remember [was Henry a communist↑]."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("verb", "remember"), ("embedding", "quasi")] }

def ex40b : Datum :=
  { id := "dayal2025_ex40b"
    source := ⟨"mccloskey-2006", "p. 112"⟩
    reportedIn := some ⟨"dayal-2025", "(40b)"⟩
    language := "stan1293"
    primaryText := "I don't remember [was Henry a communist↑]."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("verb", "remember"), ("embedding", "quasi"), ("negated", "true")] }

def ex40c : Datum :=
  { id := "dayal2025_ex40c"
    source := ⟨"mccloskey-2006", "p. 112"⟩
    reportedIn := some ⟨"dayal-2025", "(40c)"⟩
    language := "stan1293"
    primaryText := "Do you remember↑ [was Henry a communist↑]"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("verb", "remember"), ("embedding", "quasi"), ("questioned", "true")] }

def ex41a : Datum :=
  { id := "dayal2025_ex41a"
    source := ⟨"bhatt-dayal-2020", "(10b)"⟩
    reportedIn := some ⟨"dayal-2025", "(41a)"⟩
    method := some .corpus
    language := "hind1269"
    primaryText := "koi: nahĩ: ja:nta: [ki kya: TiTo sTa:lin-se mile the↑]."
    glossedTokens := [("koi:", "someone"), ("nahĩ:", "not"), ("ja:nta:", "knows"), ("ki", "SUB"), ("kya:", "PQP"), ("TiTo", "Tito"), ("sTa:lin-se", "Stalin-with"), ("mile", "met"), ("the", "")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("embedding", "quasi"), ("verbClass", "responsive"), ("negated", "true")] }

def ex41b : Datum :=
  { id := "dayal2025_ex41b"
    source := ⟨"dayal-2025", "(41b)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "kisi:-ko bhi: ma:lum hai↑ [ki (kya:) TiTo sTa:lin-se mile the↑]"
    glossedTokens := [("kisi:-ko", "someone-ACC"), ("bhi:", "at.all"), ("ma:lum", "know"), ("hai", ""), ("ki", "SUB"), ("kya:", "PQP"), ("TiTo", "Tito"), ("sTa:lin-se", "Stalin-with"), ("mile", "met"), ("the", "")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("embedding", "quasi"), ("verbClass", "responsive"), ("questioned", "true")] }

def ex43a : Datum :=
  { id := "dayal2025_ex43a"
    source := ⟨"dayal-2025", "(43a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have forgotten, [did Ann get A's in her 1st year courses↑]."
    glossedTokens := []
    context := "Speaker A is writing evaluation letters and asks a colleague (44a)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("verb", "forget"), ("embedding", "quasi")] }

def ex45a : Datum :=
  { id := "dayal2025_ex45a"
    source := ⟨"dayal-2025", "(45a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary knows [did Sue leave early↑]."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("Mary wants to know [did Sue leave early↑].", .acceptable)]
    readings := []
    paperFeatures := [("section", "3.3"), ("verb", "know"), ("embedding", "quasi")] }

def ex45b_forget : Datum :=
  { id := "dayal2025_ex45b_forget"
    source := ⟨"dayal-2025", "(45b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I forget [did Sue leave early↑]."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("verb", "forget"), ("embedding", "quasi")] }

def ex45b_remember : Datum :=
  { id := "dayal2025_ex45b_remember"
    source := ⟨"dayal-2025", "(45b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I remember [did Sue leave early↑]."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("verb", "remember"), ("embedding", "quasi")] }

def ex46a : Datum :=
  { id := "dayal2025_ex46a"
    source := ⟨"dayal-2025", "(46a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Does Sue remember↑ [was Henry a communist↑]"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("verb", "remember"), ("embedding", "quasi"), ("questioned", "true")] }

def ex46b : Datum :=
  { id := "dayal2025_ex46b"
    source := ⟨"dayal-2025", "(46b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Have you forgotten↑ [was Henry a communist↑]"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("verb", "forget"), ("embedding", "quasi"), ("questioned", "true"), ("invested", "speaker")] }

def ex49a_you : Datum :=
  { id := "dayal2025_ex49a_you"
    source := ⟨"dayal-2025", "(49a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You have forgotten [was Henry a communist↑]."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("I have forgotten [was Henry a communist↑].", .acceptable)]
    readings := []
    paperFeatures := [("section", "3.3"), ("verb", "forget"), ("embedding", "quasi"), ("invested", "speaker")] }

def ex62a : Datum :=
  { id := "dayal2025_ex62a"
    source := ⟨"dayal-2025", "(62a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Do you drink wine?"
    glossedTokens := []
    context := "Neutral: deciding whether to order a bottle to share. Biased: the speaker thought the addressee a teetotaler and sees them looking at the wine list."
    judgment := .acceptable
    alternatives := []
    readings := [("neutral", .acceptable), ("biased", .acceptable)]
    paperFeatures := [("section", "4.3"), ("syntax", "interrogative"), ("embedding", "matrix")] }

def ex62b : Datum :=
  { id := "dayal2025_ex62b"
    source := ⟨"dayal-2025", "(62b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You drink wine?"
    glossedTokens := []
    context := "Neutral: deciding whether to order a bottle to share. Biased: the speaker thought the addressee a teetotaler and sees them looking at the wine list."
    judgment := .acceptable
    alternatives := []
    readings := [("neutral", .unacceptable), ("biased", .acceptable)]
    paperFeatures := [("section", "4.3"), ("syntax", "declarative"), ("embedding", "matrix")] }

def ex63a : Datum :=
  { id := "dayal2025_ex63a"
    source := ⟨"dayal-2025", "(63a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "a:p shara:b pi:te haĩ?"
    glossedTokens := [("a:p", "you"), ("shara:b", "wine"), ("pi:te", "drink"), ("haĩ", "")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("neutral", .acceptable), ("biased", .acceptable)]
    paperFeatures := [("section", "4.3"), ("syntax", "declarative"), ("embedding", "matrix")] }

def ex63b : Datum :=
  { id := "dayal2025_ex63b"
    source := ⟨"dayal-2025", "(63b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Bevi il vino?"
    glossedTokens := [("Bevi", "drink"), ("il", "the"), ("vino", "wine")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("neutral", .acceptable), ("biased", .acceptable)]
    paperFeatures := [("section", "4.3"), ("syntax", "declarative"), ("embedding", "matrix")] }

def ex69a_en : Datum :=
  { id := "dayal2025_ex69a_en"
    source := ⟨"dayal-2025", "(69a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Do you drink wine (or not)?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.4"), ("simplex", "true"), ("embedding", "matrix")] }

def ex69b_en : Datum :=
  { id := "dayal2025_ex69b_en"
    source := ⟨"dayal-2025", "(69b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The question is, [do you drink wine (or not)]?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.4"), ("simplex", "true"), ("embedding", "quasi")] }

def ex69c_en : Datum :=
  { id := "dayal2025_ex69c_en"
    source := ⟨"dayal-2025", "(69c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "[Whether she will drink wine (or not)] depends on whether she has to work tomorrow."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.4"), ("simplex", "true"), ("embedding", "subordination")] }

def ex69a_it : Datum :=
  { id := "dayal2025_ex69a_it"
    source := ⟨"dayal-2025", "(69a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Bevi il vino (o no)?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.4"), ("simplex", "true"), ("embedding", "matrix")] }

def ex69b_it : Datum :=
  { id := "dayal2025_ex69b_it"
    source := ⟨"dayal-2025", "(69b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "La domanda è [se berrai il vino (o no)]?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.4"), ("simplex", "true"), ("embedding", "quasi")] }

def ex69c_it : Datum :=
  { id := "dayal2025_ex69c_it"
    source := ⟨"dayal-2025", "(69c)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "[Se berrà il vino (o no)] dipenderà dal fatto che lavorerà domani."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.4"), ("simplex", "true"), ("embedding", "subordination")] }

def ex70a : Datum :=
  { id := "dayal2025_ex70a"
    source := ⟨"dayal-2025", "(70a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "(kya:) anu ja:egi: (ya: nahĩ:)↑"
    glossedTokens := [("kya:", "PQP"), ("anu", "Anu"), ("ja:egi:", "will.go"), ("ya:", "or"), ("nahĩ:", "not")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.4"), ("simplex", "true"), ("embedding", "matrix")] }

def ex70b : Datum :=
  { id := "dayal2025_ex70b"
    source := ⟨"dayal-2025", "(70b)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "ravi ja:nna: ca:hta: hai [ki (kya:) anu ja:egi: (ya: nahĩ:)↑]"
    glossedTokens := [("ravi", "Ravi"), ("ja:nna:", "to.know"), ("ca:hta:", "wants"), ("hai", ""), ("ki", "SUB"), ("kya:", "PQP"), ("anu", "Anu"), ("ja:egi:", "will.go"), ("ya:", "or"), ("nahĩ:", "not")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.4"), ("simplex", "true"), ("embedding", "quasi")] }

def ex71 : Datum :=
  { id := "dayal2025_ex71"
    source := ⟨"dayal-2025", "(71)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "ravi ja:nta: hai [ki anu ja:egi:]"
    glossedTokens := [("ravi", "Ravi"), ("ja:nta:", "knows"), ("hai", ""), ("ki", "SUB"), ("anu", "Anu"), ("ja:egi:", "will.go")]
    context := ""
    judgment := .ungrammatical
    alternatives := [("ravi ja:nta: hai [ki anu ja:egi: ya: nahĩ:]", .acceptable)]
    readings := []
    paperFeatures := [("section", "4.4"), ("simplex", "true"), ("embedding", "subordination")] }

def ex84a : Datum :=
  { id := "dayal2025_ex84a"
    source := ⟨"dayal-2025", "(84a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mueller was investigating [whether Russia interfered in the 2016 election]."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1"), ("verb", "investigate"), ("embedding", "subordination")] }

def ex84b : Datum :=
  { id := "dayal2025_ex84b"
    source := ⟨"dayal-2025", "(84b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mueller was investigating [did Russia interfere in the 2016 election↑]."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("Mueller wanted to know [did Russia interfere in the 2016 election↑].", .acceptable)]
    readings := []
    paperFeatures := [("section", "6.1"), ("verb", "investigate"), ("embedding", "quasi")] }

def all : List Datum := [ex3b, ex5a, ex5b, ex8a, ex8b, ex9a, ex11a, ex11b, ex11c, ex11d, ex13a, ex14a, ex14b, ex14c, ex15b, ex16b, ex17a, ex17b, ex17c, ex18a, ex19a, ex18b, ex19c, ex24a_wonder, ex24a_know, ex24a_believe, ex38b, ex39a, ex39b, ex40a, ex40b, ex40c, ex41a, ex41b, ex43a, ex45a, ex45b_forget, ex45b_remember, ex46a, ex46b, ex49a_you, ex62a, ex62b, ex63a, ex63b, ex69a_en, ex69b_en, ex69c_en, ex69a_it, ex69b_it, ex69c_it, ex70a, ex70b, ex71, ex84a, ex84b]

end Dayal2025.Examples
