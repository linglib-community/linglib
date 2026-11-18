module

public import Linglib.Data.Examples.Schema

/-!
# `KadmonLandman1993` — typed example data

Auto-generated from `Linglib/Data/Examples/KadmonLandman1993.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace KadmonLandman1993.Examples`.
-/

@[expose] public section

namespace KadmonLandman1993.Examples

def kl1993_1 : Datum :=
  { id := "kl1993_1"
    source := ⟨"kadmon-landman-1993", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't have any potatoes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("context", "negation"), ("widening", "cooking potatoes to any potatoes")] }

def kl1993_2 : Datum :=
  { id := "kl1993_2"
    source := ⟨"kadmon-landman-1993", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have any potatoes."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("local_signature", "mono")] }

def kl1993_10 : Datum :=
  { id := "kl1993_10"
    source := ⟨"kadmon-landman-1993", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Any owl hunts mice."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("context", "generic"), ("widening", "healthy owls to any owl")] }

def kl1993_27b : Datum :=
  { id := "kl1993_27b"
    source := ⟨"kadmon-landman-1993", "(27b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every man who has any matches is happy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.4"), ("context", "universalRestrictor"), ("widening", "dry matches to any matches")] }

def kl1993_55 : Datum :=
  { id := "kl1993_55"
    source := ⟨"kadmon-landman-1993", "(55)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every boy has any potatoes."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.4"), ("local_signature", "mult")] }

def kl1993_56 : Datum :=
  { id := "kl1993_56"
    source := ⟨"kadmon-landman-1993", "(56)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not the case that every boy has any potatoes."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.6"), ("local_signature", "mult")] }

def kl1993_72 : Datum :=
  { id := "kl1993_72"
    source := ⟨"kadmon-landman-1993", "(72)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'm surprised that he ever said anything."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("context", "adversative")] }

def kl1993_73 : Datum :=
  { id := "kl1993_73"
    source := ⟨"kadmon-landman-1993", "(73)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'm sure that I ever met him."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("local_signature", "mono")] }

def kl1993_76B : Datum :=
  { id := "kl1993_76B"
    source := ⟨"kadmon-landman-1993", "(76B)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Be glad we got ANY tickets!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("local_signature", "mono"), ("settle_for_less", "yes")] }

def kl1993_82 : Datum :=
  { id := "kl1993_82"
    source := ⟨"kadmon-landman-1993", "(82)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'm sorry that anybody hates me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("context", "adversative"), ("widening", "phonologists who hate me to linguists who hate me")] }

def kl1993_88 : Datum :=
  { id := "kl1993_88"
    source := ⟨"kadmon-landman-1993", "(88)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'm glad ANYBODY likes me!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("local_signature", "mono"), ("settle_for_less", "yes")] }

def kl1993_95 : Datum :=
  { id := "kl1993_95"
    source := ⟨"kadmon-landman-1993", "(95)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'm sure we got ANY tickets!"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("local_signature", "mono")] }

def kl1993_105 : Datum :=
  { id := "kl1993_105"
    source := ⟨"kadmon-landman-1993", "(105)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It isn't because Sue said anything bad about me that I'm angry."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.4"), ("local_signature", "all"), ("metalinguistic_denial", "yes")] }

def kl1993_106 : Datum :=
  { id := "kl1993_106"
    source := ⟨"kadmon-landman-1993", "(106)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I didn't help him because I have any sympathy for urban guerillas, although I do sympathize with urban guerillas."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.4"), ("local_signature", "all")] }

def kl1993_109 : Datum :=
  { id := "kl1993_109"
    source := ⟨"kadmon-landman-1993", "(109)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "When he accepted the case, Sir Winfred was already convinced that the accused was not guilty. His deep sympathy for defendants that he believed to be innocent was well known, and the present case was no exception. Yet, in the present case, it wasn't because he had any such sympathy that he had decided to take on the case. It was his professional curiosity that led him this time: he was thoroughly puzzled by the case and when he heard who the prosecutor was, the prospect of renewing their previous animosity in the courtroom was irresistible."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.4"), ("local_signature", "all")] }

def kl1993_122 : Datum :=
  { id := "kl1993_122"
    source := ⟨"kadmon-landman-1993", "(122)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It isn't because of anything she said that I'm angry – although she did say all sorts of annoying things – it's because of the faces she was making."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.4"), ("local_signature", "anti")] }

def kl1993_123 : Datum :=
  { id := "kl1993_123"
    source := ⟨"kadmon-landman-1993", "(123)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "When he accepted the case, Sir Winfred was already convinced that the accused was not guilty. His deep sympathy for defendants that he believed to be innocent was well known, and the present case was no exception. Yet, in the present case, it wasn't because of any such sympathy that he had decided to take on the case. It was his professional curiosity that led him this time: he was thoroughly puzzled by the case and when he heard who the prosecutor was, the prospect of renewing their previous animosity in the courtroom was irresistible."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.4"), ("local_signature", "anti")] }

def kl1993_125 : Datum :=
  { id := "kl1993_125"
    source := ⟨"kadmon-landman-1993", "(125)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not because anybody read her paper that she's happy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.4"), ("local_signature", "all"), ("metalinguistic_denial", "yes")] }

def kl1993_132 : Datum :=
  { id := "kl1993_132"
    source := ⟨"kadmon-landman-1993", "(132)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If it's because anybody read her paper that she is happy, I'll eat my hat."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.4"), ("local_signature", "all")] }

def kl1993_143 : Datum :=
  { id := "kl1993_143"
    source := ⟨"kadmon-landman-1993", "(143)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John subscribes to any newspaper, he gets well informed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.5"), ("context", "conditionalAntecedent"), ("widening", "important newspapers to any newspaper")] }

def kl1993_almost_every : Datum :=
  { id := "kl1993_almost_every"
    source := ⟨"kadmon-landman-1993", "4.1.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "almost every owl"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.1.1"), ("np", "every owl"), ("precision", "precise"), ("universal", "yes"), ("dimensionally_universal", "no")] }

def kl1993_almost_no : Datum :=
  { id := "kl1993_almost_no"
    source := ⟨"kadmon-landman-1993", "4.1.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "almost no owl"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.1.1"), ("np", "no owl"), ("precision", "precise"), ("universal", "yes"), ("dimensionally_universal", "no")] }

def kl1993_almost_some : Datum :=
  { id := "kl1993_almost_some"
    source := ⟨"kadmon-landman-1993", "4.1.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "almost some owl"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.1.1"), ("np", "some owl"), ("precision", "precise"), ("universal", "no"), ("dimensionally_universal", "no")] }

def kl1993_almost_an : Datum :=
  { id := "kl1993_almost_an"
    source := ⟨"kadmon-landman-1993", "4.1.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "almost an owl hunts mice"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.1.1"), ("np", "an owl"), ("precision", "vague"), ("universal", "yes"), ("dimensionally_universal", "no")] }

def kl1993_almost_any : Datum :=
  { id := "kl1993_almost_any"
    source := ⟨"kadmon-landman-1993", "4.3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "almost any owl"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.3"), ("np", "any owl"), ("precision", "vague"), ("universal", "yes"), ("dimensionally_universal", "yes")] }

def all : List Datum := [kl1993_1, kl1993_2, kl1993_10, kl1993_27b, kl1993_55, kl1993_56, kl1993_72, kl1993_73, kl1993_76B, kl1993_82, kl1993_88, kl1993_95, kl1993_105, kl1993_106, kl1993_109, kl1993_122, kl1993_123, kl1993_125, kl1993_132, kl1993_143, kl1993_almost_every, kl1993_almost_no, kl1993_almost_some, kl1993_almost_an, kl1993_almost_any]

end KadmonLandman1993.Examples
