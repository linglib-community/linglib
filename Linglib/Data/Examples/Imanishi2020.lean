module

public import Linglib.Data.Examples.Schema

/-!
# `Imanishi2020` — typed example data

Auto-generated from `Linglib/Data/Examples/Imanishi2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Imanishi2020.Examples`.
-/

@[expose] public section

namespace Imanishi2020.Examples

def s1a : Datum :=
  { id := "imanishi2020_s1a"
    source := ⟨"imanishi-2020", "(1a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "y-in-ajin che [ki-k'ul-ïk ak'wal-a']."
    glossedTokens := [("y-in-ajin", "IPFV-B1SG-PROG"), ("che", "PREP"), ("ki-k'ul-ïk", "A3PL-meet-NMLZ"), ("ak'wal-a'", "child-PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("alignment", "S/A = set B on ajin, O = set A on the nominalized verb")] }

def s1b : Datum :=
  { id := "imanishi2020_s1b"
    source := ⟨"imanishi-2020", "(1b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "y-in-ajin che [atin-ïk]."
    glossedTokens := [("y-in-ajin", "IPFV-B1SG-PROG"), ("che", "PREP"), ("atin-ïk", "bathe-NMLZ")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("alignment", "S = set B on ajin, no set A on the nominalized verb")] }

def s2a : Datum :=
  { id := "imanishi2020_s2a"
    source := ⟨"imanishi-2020", "(2a)"⟩
    reportedIn := none
    language := "chol1282"
    primaryText := "Choñkol-ø [i-jats'-oñ]."
    glossedTokens := [("Choñkol-ø", "PROG-B3SG"), ("i-jats'-oñ", "A3SG-hit-B1SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("source", "Coon 2013a:11"), ("alignment", "A = set A, O = set B inside the nominalized clause")] }

def s2b : Datum :=
  { id := "imanishi2020_s2b"
    source := ⟨"imanishi-2020", "(2b)"⟩
    reportedIn := none
    language := "chol1282"
    primaryText := "Choñkol-ø [i-majl-el]."
    glossedTokens := [("Choñkol-ø", "PROG-B3SG"), ("i-majl-el", "A3SG-go-NMLZ")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("source", "Coon 2013a:11"), ("alignment", "S = set A")] }

def s3a : Datum :=
  { id := "imanishi2020_s3a"
    source := ⟨"imanishi-2020", "(3a)"⟩
    reportedIn := none
    language := "qanj1241"
    primaryText := "lanan-ø [hach w-il-on-i]."
    glossedTokens := [("lanan-ø", "PROG-B3SG"), ("hach", "B2SG"), ("w-il-on-i", "A1SG-see-DM-INTR")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("source", "Mateo Pedro 2009"), ("alignment", "A = set A, O = set B, the suffix -on supplying object Case")] }

def s3b : Datum :=
  { id := "imanishi2020_s3b"
    source := ⟨"imanishi-2020", "(3b)"⟩
    reportedIn := none
    language := "qanj1241"
    primaryText := "lanan-ø [ha-way-i]."
    glossedTokens := [("lanan-ø", "PROG-B3SG"), ("ha-way-i", "A2SG-sleep-INTR")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("source", "Mateo Pedro 2009"), ("alignment", "S = set A")] }

def s62 : Datum :=
  { id := "imanishi2020_s62"
    source := ⟨"imanishi-2020", "(62)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "i katastrofi tis polis apo tus varvarus mesa se tris meres"
    glossedTokens := [("i", "the"), ("katastrofi", "destruction"), ("tis", "the"), ("polis", "city-GEN"), ("apo", "by"), ("tus", "the"), ("varvarus", "barbarians"), ("mesa", "within"), ("se", ""), ("tris", "three"), ("meres", "days")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("source", "Alexiadou 2001:76"), ("nominalization", "process nominal without an external argument")] }

def s64 : Datum :=
  { id := "imanishi2020_s64"
    source := ⟨"imanishi-2020", "(64)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri ru-k'at-ïk ri tinamït [ri x-ø-b'än/x-ø-u-b'än ri a Juan] x-ø-xib'i-n."
    glossedTokens := [("ri", "DET"), ("ru-k'at-ïk", "A3SG-burn-NMLZ"), ("ri", "DET"), ("tinamït", "city"), ("ri", "DET"), ("x-ø-b'än/x-ø-u-b'än", "PFV-B3SG-do/PFV-B3SG-A3SG-do"), ("ri", "DET"), ("a", "CL"), ("Juan", "Juan"), ("x-ø-xib'i-n", "PFV-B3SG-scare-ANTIP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("nominalization", "the external argument appears in a relative clause")] }

def s65 : Datum :=
  { id := "imanishi2020_s65"
    source := ⟨"imanishi-2020", "(65)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri ru-k'at-ïk ri tinamït r-oma ri a Juan x-ø-xib'i-n."
    glossedTokens := [("ri", "DET"), ("ru-k'at-ïk", "A3SG-burn-NMLZ"), ("ri", "DET"), ("tinamït", "city"), ("r-oma", "A3SG-because.of"), ("ri", "DET"), ("a", "CL"), ("Juan", "Juan"), ("x-ø-xib'i-n", "PFV-B3SG-scare-ANTIP")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("nominalization", "the by-phrase counterpart is degraded")] }

def s66 : Datum :=
  { id := "imanishi2020_s66"
    source := ⟨"imanishi-2020", "(66)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "nu-ki-k'ul-ïk/ki-nu-k'ul-ïk ak'wal-a'"
    glossedTokens := [("nu-ki-k'ul-ïk/ki-nu-k'ul-ïk", "A1SG-A3PL-meet-NMLZ/A3PL-A1SG-meet-NMLZ"), ("ak'wal-a'", "child-PL")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("nominalization", "two set A markers impossible in either order")] }

def s67 : Datum :=
  { id := "imanishi2020_s67"
    source := ⟨"imanishi-2020", "(67)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ru-k'at-ïk ri a Juan x-ø-xib'i-n."
    glossedTokens := [("ru-k'at-ïk", "A3SG-burn-NMLZ"), ("ri", "DET"), ("a", "CL"), ("Juan", "Juan"), ("x-ø-xib'i-n", "PFV-B3SG-scare-ANTIP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("nominalization", "a sole argument is the internal argument")] }

def s68a : Datum :=
  { id := "imanishi2020_s68a"
    source := ⟨"imanishi-2020", "(68a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "nu-b'iyïn-ïk"
    glossedTokens := [("nu-b'iyïn-ïk", "A1SG-walk-NMLZ")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("nominalization", "unergative nominalization excludes its external argument")] }

def s68b : Datum :=
  { id := "imanishi2020_s68b"
    source := ⟨"imanishi-2020", "(68b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ru-tzopin-ïk ri xta Maria"
    glossedTokens := [("ru-tzopin-ïk", "A3SG-jump-NMLZ"), ("ri", "DET"), ("xta", "CL"), ("Maria", "Maria")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("nominalization", "unergative nominalization excludes its external argument")] }

def s69 : Datum :=
  { id := "imanishi2020_s69"
    source := ⟨"imanishi-2020", "(69)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri ru-tzaq-ïk ri a Juan ütz."
    glossedTokens := [("ri", "DET"), ("ru-tzaq-ïk", "A3SG-fall-NMLZ"), ("ri", "DET"), ("a", "CL"), ("Juan", "Juan"), ("ütz", "good")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("nominalization", "unaccusative nominalized in subject position; the internal argument takes genitive")] }

def s70 : Datum :=
  { id := "imanishi2020_s70"
    source := ⟨"imanishi-2020", "(70)"⟩
    reportedIn := none
    language := "chol1282"
    primaryText := "Mach uts'aty [a-jats'-oñ]."
    glossedTokens := [("Mach", "NEG"), ("uts'aty", "good"), ("a-jats'-oñ", "A2SG-hit-B1SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("source", "Coon 2013a:141"), ("nominalization", "external and internal argument both inside")] }

def s71 : Datum :=
  { id := "imanishi2020_s71"
    source := ⟨"imanishi-2020", "(71)"⟩
    reportedIn := none
    language := "qanj1241"
    primaryText := "[h-il-on ø] kawal watx'."
    glossedTokens := [("h-il-on", "A2SG-see-DM"), ("ø", "B3SG"), ("kawal", "very"), ("watx'", "good")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("source", "p.c. Pedro Mateo Pedro"), ("nominalization", "external argument inside the nominalized clause")] }

def s76a : Datum :=
  { id := "imanishi2020_s76a"
    source := ⟨"imanishi-2020", "(76a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "x-ø-in-k'ul oxi' ak'wal-a'."
    glossedTokens := [("x-ø-in-k'ul", "PFV-B3SG-A1SG-meet"), ("oxi'", "three"), ("ak'wal-a'", "child-PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("voice", "active root transitive")] }

def s76b : Datum :=
  { id := "imanishi2020_s76b"
    source := ⟨"imanishi-2020", "(76b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "oxi' ak'wal-a' x-e-k'ul r-oma ri Ana."
    glossedTokens := [("oxi'", "three"), ("ak'wal-a'", "child-PL"), ("x-e-k'ul", "PFV-B3PL-meet"), ("r-oma", "A3SG-because.of"), ("ri", "DET"), ("Ana", "Ana")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("voice", "passive root transitive without overt passive morphology")] }

def s78a : Datum :=
  { id := "imanishi2020_s78a"
    source := ⟨"imanishi-2020", "(78a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "röj x-e-qa-tïk k'iy k'otz'i'j pa jardin."
    glossedTokens := [("röj", "we"), ("x-e-qa-tïk", "PFV-B3PL-A1PL-plant"), ("k'iy", "many"), ("k'otz'i'j", "flower"), ("pa", "PREP"), ("jardin", "garden")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("voice", "active, lax vowel")] }

def s78b : Datum :=
  { id := "imanishi2020_s78b"
    source := ⟨"imanishi-2020", "(78b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "k'iy k'otz'i'j x-e-tik pa jardin."
    glossedTokens := [("k'iy", "many"), ("k'otz'i'j", "flower"), ("x-e-tik", "PFV-B3PL-plant.PASS"), ("pa", "PREP"), ("jardin", "garden")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("voice", "passive, tensed vowel")] }

def s80a : Datum :=
  { id := "imanishi2020_s80a"
    source := ⟨"imanishi-2020", "(80a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "röj x-ø-qa-chäp ru-tik-ïk jun k'otz'i'j."
    glossedTokens := [("röj", "we"), ("x-ø-qa-chäp", "PFV-B3SG-A1PL-begin"), ("ru-tik-ïk", "A3SG-plant.PASS-NMLZ"), ("jun", "one"), ("k'otz'i'j", "flower")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("voice", "tensed vowel: the nominalized verb is passivized")] }

def s80b : Datum :=
  { id := "imanishi2020_s80b"
    source := ⟨"imanishi-2020", "(80b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "y-oj-ajin che ru-tik-ïk jun k'otz'i'j."
    glossedTokens := [("y-oj-ajin", "IPFV-B1PL-PROG"), ("che", "PREP"), ("ru-tik-ïk", "A3SG-plant.PASS-NMLZ"), ("jun", "one"), ("k'otz'i'j", "flower")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("voice", "tensed vowel: the nominalized verb is passivized")] }

def s82a : Datum :=
  { id := "imanishi2020_s82a"
    source := ⟨"imanishi-2020", "(82a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "röj x-e-qa-q'ete-j ri ak'wal-a'."
    glossedTokens := [("röj", "we"), ("x-e-qa-q'ete-j", "PFV-B3PL-A1PL-hug-TR"), ("ri", "DET"), ("ak'wal-a'", "child-PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("voice", "active derived transitive")] }

def s82b : Datum :=
  { id := "imanishi2020_s82b"
    source := ⟨"imanishi-2020", "(82b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri ak'wal-a' x-e-q'ete-x."
    glossedTokens := [("ri", "DET"), ("ak'wal-a'", "child-PL"), ("x-e-q'ete-x", "PFV-B3PL-hug-PASS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("voice", "passive suffix -x replaces -j")] }

def s83a : Datum :=
  { id := "imanishi2020_s83a"
    source := ⟨"imanishi-2020", "(83a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "röj x-ø-qa-chäp ki-q'ete-x-ïk ri ak'wal-a'."
    glossedTokens := [("röj", "we"), ("x-ø-qa-chäp", "PFV-B3SG-A1PL-begin"), ("ki-q'ete-x-ïk", "A3PL-hug-PASS-NMLZ"), ("ri", "DET"), ("ak'wal-a'", "child-PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("voice", "passive morpheme under nominalization")] }

def s83b : Datum :=
  { id := "imanishi2020_s83b"
    source := ⟨"imanishi-2020", "(83b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "röj y-oj-ajin che ki-q'ete-x-ïk ri ak'wal-a'."
    glossedTokens := [("röj", "we"), ("y-oj-ajin", "IPFV-B1PL-PROG"), ("che", "PREP"), ("ki-q'ete-x-ïk", "A3PL-hug-PASS-NMLZ"), ("ri", "DET"), ("ak'wal-a'", "child-PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("voice", "passive morpheme under nominalization")] }

def s85 : Datum :=
  { id := "imanishi2020_s85"
    source := ⟨"imanishi-2020", "(85)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri ixöq n-ø-ajin [che ki-k'ul-ïk ak'wal-a']."
    glossedTokens := [("ri", "DET"), ("ixöq", "woman"), ("n-ø-ajin", "IPFV-B3SG-PROG"), ("che", "PREP"), ("ki-k'ul-ïk", "A3PL-meet-NMLZ"), ("ak'wal-a'", "child-PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("derivation", "object genitive from D, subject absolutive from the matrix Infl")] }

def s90 : Datum :=
  { id := "imanishi2020_s90"
    source := ⟨"imanishi-2020", "(90)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "y-in-ajin che jun b'ix."
    glossedTokens := [("y-in-ajin", "IPFV-B1SG-PROG"), ("che", "PREP"), ("jun", "INDF"), ("b'ix", "song")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("theta", "ajin assigns an agentive θ-role to its subject")] }

def s91 : Datum :=
  { id := "imanishi2020_s91"
    source := ⟨"imanishi-2020", "(91)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "y-in-ajin che [atin-ïk]."
    glossedTokens := [("y-in-ajin", "IPFV-B1SG-PROG"), ("che", "PREP"), ("atin-ïk", "bathe-NMLZ")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("derivation", "unergative base: no DP inside, no genitive")] }

def s92 : Datum :=
  { id := "imanishi2020_s92"
    source := ⟨"imanishi-2020", "(92)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri a Juan n-ø-ajin che (ru-)tzaq-ïk."
    glossedTokens := [("ri", "DET"), ("a", "CL"), ("Juan", "Juan"), ("n-ø-ajin", "IPFV-B3SG-PROG"), ("che", "PREP"), ("(ru-)tzaq-ïk", "(A3SG-)fall-NMLZ")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("control", "unaccusative base resists nominalization under ajin")] }

def s93a : Datum :=
  { id := "imanishi2020_s93a"
    source := ⟨"imanishi-2020", "(93a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri a Juan n-ø-ajin n-ø-tzaq."
    glossedTokens := [("ri", "DET"), ("a", "CL"), ("Juan", "Juan"), ("n-ø-ajin", "IPFV-B3SG-PROG"), ("n-ø-tzaq", "IPFV-B3SG-fall")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("control", "the unaccusative appears as a finite verb under ajin")] }

def s93b : Datum :=
  { id := "imanishi2020_s93b"
    source := ⟨"imanishi-2020", "(93b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri a Juan n-ø-tzaq."
    glossedTokens := [("ri", "DET"), ("a", "CL"), ("Juan", "Juan"), ("n-ø-tzaq", "IPFV-B3SG-fall")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("control", "simple imperfective")] }

def s94 : Datum :=
  { id := "imanishi2020_s94"
    source := ⟨"imanishi-2020", "(94)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri wäy y-e-ajin che (ru/ki)-chaq'irse-x-ïk."
    glossedTokens := [("ri", "DET"), ("wäy", "tortilla"), ("y-e-ajin", "IPFV-B3PL-PROG"), ("che", "PREP"), ("(ru/ki)-chaq'irse-x-ïk", "A3SG/A3PL-dry-PASS-NMLZ")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("control", "passive base resists nominalization under ajin")] }

def s95 : Datum :=
  { id := "imanishi2020_s95"
    source := ⟨"imanishi-2020", "(95)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri wäy y-e-chaq'irse-x."
    glossedTokens := [("ri", "DET"), ("wäy", "tortilla"), ("y-e-chaq'irse-x", "IPFV-B3PL-dry-PASS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("control", "simple imperfective passive")] }

def s96a : Datum :=
  { id := "imanishi2020_s96a"
    source := ⟨"imanishi-2020", "(96a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I was engaged in falling."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("source", "Coon 2010a:104"), ("control", "engage in resists an unaccusative gerund")] }

def s96b : Datum :=
  { id := "imanishi2020_s96b"
    source := ⟨"imanishi-2020", "(96b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I was engaged in being attacked."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("source", "Coon 2010a:104"), ("control", "engage in resists a passive gerund")] }

def s97 : Datum :=
  { id := "imanishi2020_s97"
    source := ⟨"imanishi-2020", "(97)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "n-ø-ajin jun nimaq'ij."
    glossedTokens := [("n-ø-ajin", "IPFV-B3SG-PROG"), ("jun", "INDF"), ("nimaq'ij", "celebration/festival")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("source", "Macario et al. 1998"), ("case", "no preposition when a single DP takes absolutive from Infl")] }

def s98a : Datum :=
  { id := "imanishi2020_s98a"
    source := ⟨"imanishi-2020", "(98a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "röj x-ø-qa-chäp [ki-k'ul-ïk rje']."
    glossedTokens := [("röj", "we"), ("x-ø-qa-chäp", "PFV-B3SG-A1PL-begin"), ("ki-k'ul-ïk", "A3PL-meet-NMLZ"), ("rje'", "they")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.3"), ("alignment", "subject inherent ergative from transitive v, object genitive: both set A")] }

def s98b : Datum :=
  { id := "imanishi2020_s98b"
    source := ⟨"imanishi-2020", "(98b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "rat x-ø-a-chäp [atin-ïk]."
    glossedTokens := [("rat", "you"), ("x-ø-a-chäp", "PFV-B3SG-A2SG-begin"), ("atin-ïk", "bathe-NMLZ")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.3"), ("alignment", "subject set A on chäp, no genitive inside")] }

def s100 : Datum :=
  { id := "imanishi2020_s100"
    source := ⟨"imanishi-2020", "(100)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "x-ø-u-chäp [q'et-e-n-ik] r-ichin ri ak'wal."
    glossedTokens := [("x-ø-u-chäp", "PFV-B3SG-A3SG-begin"), ("q'et-e-n-ik", "hug-BV-ANTIP-NMLZ"), ("r-ichin", "A3SG-RN"), ("ri", "DET"), ("ak'wal", "child")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("source", "García Matzar and Rodríguez Guaján 1997:457"), ("strategy", "antipassive: object oblique under the relational noun")] }

def s102 : Datum :=
  { id := "imanishi2020_s102"
    source := ⟨"imanishi-2020", "(102)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "röj y-oj-ajin che [choy-oj che']."
    glossedTokens := [("röj", "we"), ("y-oj-ajin", "IPFV-B1PL-PROG"), ("che", "PREP"), ("choy-oj", "cut-NMLZ"), ("che'", "tree")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.2"), ("strategy", "incorporating -oj nominalization, no set A")] }

def s103 : Datum :=
  { id := "imanishi2020_s103"
    source := ⟨"imanishi-2020", "(103)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "x-ø-qa-chäp (ri) [choy-oj che']."
    glossedTokens := [("x-ø-qa-chäp", "PFV-B3SG-A1PL-begin"), ("(ri)", "DET"), ("choy-oj", "cut-NMLZ"), ("che'", "tree")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.2"), ("strategy", "incorporating -oj nominalization under chäp")] }

def s104 : Datum :=
  { id := "imanishi2020_s104"
    source := ⟨"imanishi-2020", "(104)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "x-ø-qa-chäp ru/ki-choy-oj che'."
    glossedTokens := [("x-ø-qa-chäp", "PFV-B3SG-A1PL-begin"), ("ru/ki-choy-oj", "A3SG/A3PL-cut-NMLZ"), ("che'", "tree")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.2"), ("strategy", "set A impossible on the -oj nominalization")] }

def s107 : Datum :=
  { id := "imanishi2020_s107"
    source := ⟨"imanishi-2020", "(107)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "x-ø-qa-chäp ri choy-oj ri che'."
    glossedTokens := [("x-ø-qa-chäp", "PFV-B3SG-A1PL-begin"), ("ri", "DET"), ("choy-oj", "cut-NMLZ"), ("ri", "DET"), ("che'", "tree")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.2"), ("incorporation", "a determiner-marked object cannot be incorporated")] }

def s109 : Datum :=
  { id := "imanishi2020_s109"
    source := ⟨"imanishi-2020", "(109)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "x-ø-qa-chäp ri choy-oj oxi' che'."
    glossedTokens := [("x-ø-qa-chäp", "PFV-B3SG-A1PL-begin"), ("ri", "DET"), ("choy-oj", "cut-NMLZ"), ("oxi'", "three"), ("che'", "tree")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.2"), ("incorporation", "a numeral-marked object cannot be incorporated")] }

def s112 : Datum :=
  { id := "imanishi2020_s112"
    source := ⟨"imanishi-2020", "(112)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "x-ø-qa-chäp ri choy-oj a-che'."
    glossedTokens := [("x-ø-qa-chäp", "PFV-B3SG-A1PL-begin"), ("ri", "DET"), ("choy-oj", "cut-NMLZ"), ("a-che'", "A2SG-tree")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.2"), ("incorporation", "a possessed object cannot be incorporated")] }

def s113 : Datum :=
  { id := "imanishi2020_s113"
    source := ⟨"imanishi-2020", "(113)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "achike x-ø-a-chäp (ri) choy-oj?"
    glossedTokens := [("achike", "what"), ("x-ø-a-chäp", "PFV-B3SG-A2SG-begin"), ("(ri)", "DET"), ("choy-oj", "cut-NMLZ")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.2"), ("incorporation", "no wh-extraction of the incorporated object")] }

def s114 : Datum :=
  { id := "imanishi2020_s114"
    source := ⟨"imanishi-2020", "(114)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "achike x-ø-a-chäp ru-ch'ey-ïk?"
    glossedTokens := [("achike", "what"), ("x-ø-a-chäp", "PFV-B3SG-A2SG-begin"), ("ru-ch'ey-ïk", "A3SG-hit-NMLZ")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.2"), ("incorporation", "wh-extraction from the -ïk nominalization")] }

def all : List Datum := [s1a, s1b, s2a, s2b, s3a, s3b, s62, s64, s65, s66, s67, s68a, s68b, s69, s70, s71, s76a, s76b, s78a, s78b, s80a, s80b, s82a, s82b, s83a, s83b, s85, s90, s91, s92, s93a, s93b, s94, s95, s96a, s96b, s97, s98a, s98b, s100, s102, s103, s104, s107, s109, s112, s113, s114]

end Imanishi2020.Examples
