module

public import Linglib.Data.Examples.Schema

/-!
# `BrananErlewine2024` — typed example data

Auto-generated from `Linglib/Data/Examples/BrananErlewine2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BrananErlewine2024.Examples`.
-/

@[expose] public section

namespace BrananErlewine2024.Examples

def ex12a : Datum :=
  { id := "brananerlewine2024_ex12a"
    source := ⟨"branan-erlewine-2024", "(12a)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "kız-ı sok-an arı"
    glossedTokens := []
    context := "Subject relative with the SR form."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "SR")] }

def ex12b : Datum :=
  { id := "brananerlewine2024_ex12b"
    source := ⟨"branan-erlewine-2024", "(12b)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "arı-nın sok-tuğ-u kız"
    glossedTokens := []
    context := "Object relative across a high subject, with the NSR form."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "NSR")] }

def ex13a : Datum :=
  { id := "brananerlewine2024_ex13a"
    source := ⟨"branan-erlewine-2024", "(13a)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "arı sok-an adam"
    glossedTokens := []
    context := "Object relative with the SR form; the subject is a low indefinite."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "SR")] }

def ex14a : Datum :=
  { id := "brananerlewine2024_ex14a"
    source := ⟨"branan-erlewine-2024", "(14a)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "bomba patlay-an gün"
    glossedTokens := []
    context := "Temporal relative with the SR form; the subject is a low indefinite."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "SR")] }

def ex14b : Datum :=
  { id := "brananerlewine2024_ex14b"
    source := ⟨"branan-erlewine-2024", "(14b)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "kar yağ-an gün-ler"
    glossedTokens := []
    context := "Temporal relative with the SR form; the subject is a low indefinite."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "SR")] }

def ex16a : Datum :=
  { id := "brananerlewine2024_ex16a"
    source := ⟨"branan-erlewine-2024", "(16a)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "oğl-u mekteb-e gid-en adam"
    glossedTokens := []
    context := "Possessor-of-subject relative with the SR form."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "SR")] }

def ex16b : Datum :=
  { id := "brananerlewine2024_ex16b"
    source := ⟨"branan-erlewine-2024", "(16b)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "oğl-u-un mekteb-e git-tiğ-i adam"
    glossedTokens := []
    context := "Possessor-of-subject relative with the NSR form."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("form", "NSR")] }

def ex18 : Datum :=
  { id := "brananerlewine2024_ex18"
    source := ⟨"branan-erlewine-2024", "(18)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "kız-ın-ı arı sok-an adam"
    glossedTokens := []
    context := "Possessor-of-object relative with the SR form; the subject is a low indefinite."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "SR")] }

def ex18_nsr : Datum :=
  { id := "brananerlewine2024_ex18_nsr"
    source := ⟨"branan-erlewine-2024", "(18)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "kız-ın-ı arı sok-tuğ-u adam"
    glossedTokens := []
    context := "Possessor-of-object relative with the NSR form; the subject is a low indefinite."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("form", "NSR")] }

def ex20a : Datum :=
  { id := "brananerlewine2024_ex20a"
    source := ⟨"branan-erlewine-2024", "(20a)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "(birkaç) arı-nın bacağ-ın-ı sok-tuğ-u kız"
    glossedTokens := []
    context := "Possessor-of-object relative across a high subject, with the NSR form."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "NSR")] }

def ex20b : Datum :=
  { id := "brananerlewine2024_ex20b"
    source := ⟨"branan-erlewine-2024", "(20b)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "(birkaç) arı bacağ-ın-ı sok-an kız"
    glossedTokens := []
    context := "Possessor-of-object relative across a high subject, with the SR form."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("form", "SR")] }

def ex21a : Datum :=
  { id := "brananerlewine2024_ex21a"
    source := ⟨"branan-erlewine-2024", "(21a)"⟩
    reportedIn := none
    language := "reja1240"
    primaryText := "tun gi pelisi o m-akep kelem o"
    glossedTokens := []
    context := "Theme relative of an active verb across a full subject."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("voice", "active")] }

def ex21b : Datum :=
  { id := "brananerlewine2024_ex21b"
    source := ⟨"branan-erlewine-2024", "(21b)"⟩
    reportedIn := none
    language := "reja1240"
    primaryText := "tun gi t⟨en⟩akep pelisi kelem o"
    glossedTokens := []
    context := "Theme relative of a passive verb."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("voice", "passive")] }

def ex22 : Datum :=
  { id := "brananerlewine2024_ex22"
    source := ⟨"branan-erlewine-2024", "(22)"⟩
    reportedIn := none
    language := "reja1240"
    primaryText := "Jano gi ko t⟨em⟩okoa?"
    glossedTokens := []
    context := "Active theme wh-question across a pronominal subject."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("voice", "active")] }

def ex23b : Datum :=
  { id := "brananerlewine2024_ex23b"
    source := ⟨"branan-erlewine-2024", "(23b)"⟩
    reportedIn := none
    language := "reja1240"
    primaryText := "pilem gi mulaé ku t⟨em⟩oton kelem o"
    glossedTokens := []
    context := "Active theme relative across an immediately preverbal pronominal agent."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("voice", "active")] }

def ex26a : Datum :=
  { id := "brananerlewine2024_ex26a"
    source := ⟨"branan-erlewine-2024", "(26a)"⟩
    reportedIn := none
    language := "reja1240"
    primaryText := "tun tuey gi n-adea' Alui bawo si teko ceño' o"
    glossedTokens := []
    context := "Long-distance subject relative with the complementizer bawo and a resumptive pronoun; the higher clause is passive."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("voice", "passive")] }

def ex26b : Datum :=
  { id := "brananerlewine2024_ex26b"
    source := ⟨"branan-erlewine-2024", "(26b)"⟩
    reportedIn := none
    language := "reja1240"
    primaryText := "tun tuey gi n-adea' Alui gi teko ceño' o"
    glossedTokens := []
    context := "Long-distance subject relative with the complementizer gi and a gap; the higher clause is passive."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("voice", "passive")] }

def ex28a : Datum :=
  { id := "brananerlewine2024_ex28a"
    source := ⟨"branan-erlewine-2024", "(28a)"⟩
    reportedIn := none
    language := "reja1240"
    primaryText := "tun gi ku m-adea' gi t⟨em⟩anang Pak Lu'ea' kelem o"
    glossedTokens := []
    context := "Long-distance subject relative over an active verb with a pronominal subject."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("voice", "active")] }

def ex28b : Datum :=
  { id := "brananerlewine2024_ex28b"
    source := ⟨"branan-erlewine-2024", "(28b)"⟩
    reportedIn := none
    language := "reja1240"
    primaryText := "filem gi ko m-adea' gi mulaé ko t⟨em⟩oton kelem o"
    glossedTokens := []
    context := "Long-distance theme relative over active verbs with pronominal subjects."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("voice", "active")] }

def ex29a : Datum :=
  { id := "brananerlewine2024_ex29a"
    source := ⟨"branan-erlewine-2024", "(29a)"⟩
    reportedIn := none
    language := "reja1240"
    primaryText := "tun gi nyung ne panjang o"
    glossedTokens := []
    context := "Possessor-of-subject relative with a resumptive pronoun."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex29b : Datum :=
  { id := "brananerlewine2024_ex29b"
    source := ⟨"branan-erlewine-2024", "(29b)"⟩
    reportedIn := none
    language := "reja1240"
    primaryText := "tun gi Alui k⟨em⟩lea' ngenyan ne o"
    glossedTokens := []
    context := "Possessor-of-object relative across a full subject."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("voice", "active")] }

def ex30 : Datum :=
  { id := "brananerlewine2024_ex30"
    source := ⟨"branan-erlewine-2024", "(30)"⟩
    reportedIn := none
    language := "reja1240"
    primaryText := "api bae de Keme m-anjang omor ne"
    glossedTokens := []
    context := "Possessor-of-object relative over a pronominal subject."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("voice", "active")] }

def all : List Datum := [ex12a, ex12b, ex13a, ex14a, ex14b, ex16a, ex16b, ex18, ex18_nsr, ex20a, ex20b, ex21a, ex21b, ex22, ex23b, ex26a, ex26b, ex28a, ex28b, ex29a, ex29b, ex30]

end BrananErlewine2024.Examples
