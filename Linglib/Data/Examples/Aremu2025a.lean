module

public import Linglib.Data.Examples.Schema

/-!
# `Aremu2025a` — typed example data

Auto-generated from `Linglib/Data/Examples/Aremu2025a.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Aremu2025a.Examples`.
-/

@[expose] public section

namespace Aremu2025a.Examples

def ex_157b : Datum :=
  { id := "aremu2025a_157b"
    source := ⟨"aremu-2025a", "(157-b)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Adé ra bàtà"
    glossedTokens := [("Adé", "Adé"), ("ra", "buy"), ("bàtà", "shoe")]
    context := "Answer to: Kí ni Adé rà? 'What did Adé buy?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "object")] }

def ex_157b_ni : Datum :=
  { id := "aremu2025a_157b_ni"
    source := ⟨"aremu-2025a", "(157-b)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Adé ra bàtà ni"
    glossedTokens := [("Adé", "Adé"), ("ra", "buy"), ("bàtà", "shoe"), ("ni", "FOC")]
    context := "Answer to: Kí ni Adé rà? 'What did Adé buy?'"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("focus", "object")] }

def ex_157c : Datum :=
  { id := "aremu2025a_157c"
    source := ⟨"aremu-2025a", "(157-c)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Bàtà ni Adé rà"
    glossedTokens := [("Bàtà", "shoe"), ("ni", "FOC"), ("Adé", "Adé"), ("rà", "buy")]
    context := "Answer to: Kí ni Adé rà? 'What did Adé buy?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "object"), ("fronted", "object")] }

def ex_158b : Datum :=
  { id := "aremu2025a_158b"
    source := ⟨"aremu-2025a", "(158-b)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Adé ra bàtà. Ó ra aṣọ pẹ̀lu."
    glossedTokens := [("Adé", "Adé"), ("ra", "buy"), ("bàtà", "shoe"), ("Ó", "3SG"), ("ra", "buy"), ("aṣọ", "cloth"), ("pẹ̀lu", "also")]
    context := "Answer to: Kí ni Adé rà? 'What did Adé buy?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "object"), ("continuation", "additive")] }

def ex_158c : Datum :=
  { id := "aremu2025a_158c"
    source := ⟨"aremu-2025a", "(158-c)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Bàtà ni Adé rà. Ó ra aṣọ pẹ̀lu."
    glossedTokens := [("Bàtà", "shoe"), ("ni", "FOC"), ("Adé", "Adé"), ("rà", "buy"), ("Ó", "3SG"), ("ra", "buy"), ("aṣọ", "cloth"), ("pẹ̀lu", "also")]
    context := "Answer to: Kí ni Adé rà? 'What did Adé buy?'"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "object"), ("fronted", "object"), ("continuation", "additive")] }

def ex_159b : Datum :=
  { id := "aremu2025a_159b"
    source := ⟨"aremu-2025a", "(159-b)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Adé rà bàtà ní àná"
    glossedTokens := [("Adé", "Adé"), ("rà", "buy"), ("bàtà", "shoe"), ("ní", "LOC"), ("àná", "yesterday")]
    context := "Answer to: Igba wo ni Adé rà bàtà? 'When did Adé buy a shoe?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "adjunct")] }

def ex_159c : Datum :=
  { id := "aremu2025a_159c"
    source := ⟨"aremu-2025a", "(159-c)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Àná ni Adé rà bàtà"
    glossedTokens := [("Àná", "yesterday"), ("ni", "FOC"), ("Adé", "Adé"), ("rà", "buy"), ("bàtà", "shoe")]
    context := "Answer to: Igba wo ni Adé rà bàtà? 'When did Adé buy a shoe?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "adjunct"), ("fronted", "adjunct")] }

def ex_160b : Datum :=
  { id := "aremu2025a_160b"
    source := ⟨"aremu-2025a", "(160-b)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Ó fọ́ o"
    glossedTokens := [("Ó", "3SG.NOM"), ("fọ́", "break"), ("o", "3SG.ACC")]
    context := "Answer to: Ki ni Adé ṣe sí fèrèsé? 'What did Adé do to the window?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "verb")] }

def ex_161 : Datum :=
  { id := "aremu2025a_161"
    source := ⟨"aremu-2025a", "(161)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Fífọ́ ni Adé fọ́ fèrèsé"
    glossedTokens := [("Fífọ́", "NMLZ.break"), ("ni", "FOC"), ("Adé", "Adé"), ("fọ́", "break"), ("fèrèsé", "window")]
    context := "Verb focus, the fronted verb nominalized and a copy left in place."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "verb"), ("fronted", "verb")] }

def ex_162b : Datum :=
  { id := "aremu2025a_162b"
    source := ⟨"aremu-2025a", "(162-b)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Adé fọ́ fèrèsé"
    glossedTokens := [("Adé", "Adé"), ("fọ́", "break"), ("fèrèsé", "window")]
    context := "Answer to: Ki ni Adé ṣe? 'What did Adé do?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "vp")] }

def ex_162c : Datum :=
  { id := "aremu2025a_162c"
    source := ⟨"aremu-2025a", "(162-c)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Fífọ́ fèrèsé ni Adé fọ́ fèrèsé"
    glossedTokens := [("Fífọ́", "NMLZ.break"), ("fèrèsé", "window"), ("ni", "FOC"), ("Adé", "Adé"), ("fọ́", "break"), ("fèrèsé", "window")]
    context := "Answer to: Ki ni Adé ṣe? 'What did Adé do?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "vp"), ("fronted", "vp")] }

def ex_163b : Datum :=
  { id := "aremu2025a_163b"
    source := ⟨"aremu-2025a", "(163-b)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Adé ni ó rà bàtà"
    glossedTokens := [("Adé", "Adé"), ("ni", "FOC"), ("ó", "3SG"), ("rà", "buy"), ("bàtà", "shoe")]
    context := "Answer to: Ta ni ó rà bàtà? 'Who bought a shoe?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "subject"), ("fronted", "subject")] }

def ex_163c : Datum :=
  { id := "aremu2025a_163c"
    source := ⟨"aremu-2025a", "(163-c)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Adé rà bàtà"
    glossedTokens := [("Adé", "Adé"), ("rà", "buy"), ("bàtà", "shoe")]
    context := "Answer to: Ta ni ó rà bàtà? 'Who bought a shoe?'"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "subject")] }

def ex_165b : Datum :=
  { id := "aremu2025a_165b"
    source := ⟨"aremu-2025a", "(165-b)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Tolú ni ó jẹ iṣu"
    glossedTokens := [("Tolú", "Tolú"), ("ni", "FOC"), ("ó", "3SG"), ("jẹ", "eat"), ("iṣu", "yam")]
    context := "Answer to: Kí ni ó ṣẹlẹ̀? 'What happened?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "clause"), ("fronted", "subject")] }

def ex_165c : Datum :=
  { id := "aremu2025a_165c"
    source := ⟨"aremu-2025a", "(165-c)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Tolú jẹ iṣu"
    glossedTokens := [("Tolú", "Tolú"), ("jẹ", "eat"), ("iṣu", "yam")]
    context := "Answer to: Kí ni ó ṣẹlẹ̀? 'What happened?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "clause")] }

def ex_166b : Datum :=
  { id := "aremu2025a_166b"
    source := ⟨"aremu-2025a", "(166-b)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Tolú pa eku"
    glossedTokens := [("Tolú", "Tolú"), ("pa", "kill"), ("eku", "rat")]
    context := "Answer to: Kí ni Tolú se? 'What did Tolú do?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "vp")] }

def ex_166c : Datum :=
  { id := "aremu2025a_166c"
    source := ⟨"aremu-2025a", "(166-c)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Eku ni Tolú pa"
    glossedTokens := [("Eku", "rat"), ("ni", "FOC"), ("Tolú", "Tolú"), ("pa", "kill")]
    context := "Answer to: Kí ni Tolú se? 'What did Tolú do?'"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "vp"), ("fronted", "object")] }

def ex_167b : Datum :=
  { id := "aremu2025a_167b"
    source := ⟨"aremu-2025a", "(167-b)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Tolú ni ó subú"
    glossedTokens := [("Tolú", "Tolú"), ("ni", "FOC"), ("ó", "3SG"), ("subú", "fall")]
    context := "Answer to: Kí ni ó ṣẹlẹ̀? 'What happened?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "clause"), ("fronted", "subject")] }

def ex_167c : Datum :=
  { id := "aremu2025a_167c"
    source := ⟨"aremu-2025a", "(167-c)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Tolú ni ó sùn"
    glossedTokens := [("Tolú", "Tolú"), ("ni", "FOC"), ("ó", "3SG"), ("sùn", "sleep")]
    context := "Answer to: Kí ni ó ṣẹlẹ̀? 'What happened?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "clause"), ("fronted", "subject")] }

def ex_168 : Datum :=
  { id := "aremu2025a_168"
    source := ⟨"aremu-2025a", "(168)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Enikan ni ó jí ọkọ̀"
    glossedTokens := [("Enikan", "someone"), ("ni", "FOC"), ("ó", "3SG"), ("jí", "steal"), ("ọkọ̀", "car")]
    context := "Clause focus with an indefinite subject."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "clause"), ("fronted", "subject")] }

def ex_169 : Datum :=
  { id := "aremu2025a_169"
    source := ⟨"aremu-2025a", "(169)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Pípa eku ni Tolú pa eku"
    glossedTokens := [("Pípa", "kill.NMNL"), ("eku", "rat"), ("ni", "FOC"), ("Tolú", "Tolú"), ("pa", "kill"), ("eku", "rat")]
    context := "Verb phrase focus, the verb phrase fronted with its verb nominalized."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "vp"), ("fronted", "vp")] }

def ex_188a : Datum :=
  { id := "aremu2025a_188a"
    source := ⟨"aremu-2025a", "(188-a)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Àwọn ọmọ ni wọ́n ra bàtà"
    glossedTokens := [("Àwọn", "PL"), ("ọmọ", "child"), ("ni", "FOC"), ("wọ́n", "3PL"), ("ra", "buy"), ("bàtà", "shoe")]
    context := "Subject focus."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "subject"), ("fronted", "subject"), ("number", "plural")] }

def ex_188b : Datum :=
  { id := "aremu2025a_188b"
    source := ⟨"aremu-2025a", "(188-b)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Adé ni ó ra bàtà"
    glossedTokens := [("Adé", "Adé"), ("ni", "FOC"), ("ó", "3SG"), ("ra", "buy"), ("bàtà", "shoe")]
    context := "Subject focus."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "subject"), ("fronted", "subject")] }

def all : List Datum := [ex_157b, ex_157b_ni, ex_157c, ex_158b, ex_158c, ex_159b, ex_159c, ex_160b, ex_161, ex_162b, ex_162c, ex_163b, ex_163c, ex_165b, ex_165c, ex_166b, ex_166c, ex_167b, ex_167c, ex_168, ex_169, ex_188a, ex_188b]

end Aremu2025a.Examples
