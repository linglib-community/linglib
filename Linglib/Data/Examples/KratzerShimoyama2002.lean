module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `KratzerShimoyama2002` — typed example data

Auto-generated from `Linglib/Data/Examples/KratzerShimoyama2002.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace KratzerShimoyama2002.Examples`.
-/

@[expose] public section

namespace KratzerShimoyama2002.Examples

def ex23a : Datum :=
  { id := "kratzershimoyama2002_ex23a"
    source := ⟨"kratzer-shimoyama-2002", "(23a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat sie nicht WEM gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("sie", "she"), ("nicht", "not"), ("WEM", "to.whom"), ("gezeigt", "shown")]
    glossedWords := [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['s', 'i', 'e'], ['s', 'h', 'e'], [⟨['s', 'i', 'e'], ['s', 'h', 'e'], none⟩]⟩, ⟨['n', 'i', 'c', 'h', 't'], ['n', 'o', 't'], [⟨['n', 'i', 'c', 'h', 't'], ['n', 'o', 't'], none⟩]⟩, ⟨['W', 'E', 'M'], ['t', 'o', '.', 'w', 'h', 'o', 'm'], [⟨['W', 'E', 'M'], ['t', 'o', '.', 'w', 'h', 'o', 'm'], none⟩]⟩, ⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], [⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("intervener", "nicht"), ("feature", "Neg"), ("order", "intervener-first")] }

def ex23b : Datum :=
  { id := "kratzershimoyama2002_ex23b"
    source := ⟨"kratzer-shimoyama-2002", "(23b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat sie nie WEM gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("sie", "she"), ("nie", "never"), ("WEM", "to.whom"), ("gezeigt", "shown")]
    glossedWords := [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['s', 'i', 'e'], ['s', 'h', 'e'], [⟨['s', 'i', 'e'], ['s', 'h', 'e'], none⟩]⟩, ⟨['n', 'i', 'e'], ['n', 'e', 'v', 'e', 'r'], [⟨['n', 'i', 'e'], ['n', 'e', 'v', 'e', 'r'], none⟩]⟩, ⟨['W', 'E', 'M'], ['t', 'o', '.', 'w', 'h', 'o', 'm'], [⟨['W', 'E', 'M'], ['t', 'o', '.', 'w', 'h', 'o', 'm'], none⟩]⟩, ⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], [⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("intervener", "nie"), ("feature", "exists"), ("order", "intervener-first")] }

def ex23c : Datum :=
  { id := "kratzershimoyama2002_ex23c"
    source := ⟨"kratzer-shimoyama-2002", "(23c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat niemand WEM gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("niemand", "nobody"), ("WEM", "to.whom"), ("gezeigt", "shown")]
    glossedWords := [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['n', 'i', 'e', 'm', 'a', 'n', 'd'], ['n', 'o', 'b', 'o', 'd', 'y'], [⟨['n', 'i', 'e', 'm', 'a', 'n', 'd'], ['n', 'o', 'b', 'o', 'd', 'y'], none⟩]⟩, ⟨['W', 'E', 'M'], ['t', 'o', '.', 'w', 'h', 'o', 'm'], [⟨['W', 'E', 'M'], ['t', 'o', '.', 'w', 'h', 'o', 'm'], none⟩]⟩, ⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], [⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("intervener", "niemand"), ("feature", "exists"), ("order", "intervener-first")] }

def ex23d : Datum :=
  { id := "kratzershimoyama2002_ex23d"
    source := ⟨"kratzer-shimoyama-2002", "(23d)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat fast jeder WEM gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("fast", "almost"), ("jeder", "everybody"), ("WEM", "to.whom"), ("gezeigt", "shown")]
    glossedWords := [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['f', 'a', 's', 't'], ['a', 'l', 'm', 'o', 's', 't'], [⟨['f', 'a', 's', 't'], ['a', 'l', 'm', 'o', 's', 't'], none⟩]⟩, ⟨['j', 'e', 'd', 'e', 'r'], ['e', 'v', 'e', 'r', 'y', 'b', 'o', 'd', 'y'], [⟨['j', 'e', 'd', 'e', 'r'], ['e', 'v', 'e', 'r', 'y', 'b', 'o', 'd', 'y'], none⟩]⟩, ⟨['W', 'E', 'M'], ['t', 'o', '.', 'w', 'h', 'o', 'm'], [⟨['W', 'E', 'M'], ['t', 'o', '.', 'w', 'h', 'o', 'm'], none⟩]⟩, ⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], [⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("intervener", "fast jeder"), ("feature", "exists"), ("order", "intervener-first")] }

def ex23e : Datum :=
  { id := "kratzershimoyama2002_ex23e"
    source := ⟨"kratzer-shimoyama-2002", "(23e)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat (irgend)jemand WEM gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("(irgend)jemand", "somebody"), ("WEM", "to.whom"), ("gezeigt", "shown")]
    glossedWords := [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['(', 'i', 'r', 'g', 'e', 'n', 'd', ')', 'j', 'e', 'm', 'a', 'n', 'd'], ['s', 'o', 'm', 'e', 'b', 'o', 'd', 'y'], [⟨['i', 'r', 'g', 'e', 'n', 'd', 'j', 'e', 'm', 'a', 'n', 'd'], ['s', 'o', 'm', 'e', 'b', 'o', 'd', 'y'], none⟩]⟩, ⟨['W', 'E', 'M'], ['t', 'o', '.', 'w', 'h', 'o', 'm'], [⟨['W', 'E', 'M'], ['t', 'o', '.', 'w', 'h', 'o', 'm'], none⟩]⟩, ⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], [⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("intervener", "(irgend)jemand"), ("feature", "exists"), ("order", "intervener-first")] }

def ex23f : Datum :=
  { id := "kratzershimoyama2002_ex23f"
    source := ⟨"kratzer-shimoyama-2002", "(23f)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat der Hans WEM gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("der", "the"), ("Hans", "Hans"), ("WEM", "to.whom"), ("gezeigt", "shown")]
    glossedWords := [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['d', 'e', 'r'], ['t', 'h', 'e'], [⟨['d', 'e', 'r'], ['t', 'h', 'e'], none⟩]⟩, ⟨['H', 'a', 'n', 's'], ['H', 'a', 'n', 's'], [⟨['H', 'a', 'n', 's'], ['H', 'a', 'n', 's'], none⟩]⟩, ⟨['W', 'E', 'M'], ['t', 'o', '.', 'w', 'h', 'o', 'm'], [⟨['W', 'E', 'M'], ['t', 'o', '.', 'w', 'h', 'o', 'm'], none⟩]⟩, ⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], [⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("intervener", "der Hans"), ("feature", "none"), ("order", "intervener-first")] }

def ex23g : Datum :=
  { id := "kratzershimoyama2002_ex23g"
    source := ⟨"kratzer-shimoyama-2002", "(23g)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat sie damals WEM gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("sie", "she"), ("damals", "then"), ("WEM", "whom"), ("gezeigt", "shown")]
    glossedWords := [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['s', 'i', 'e'], ['s', 'h', 'e'], [⟨['s', 'i', 'e'], ['s', 'h', 'e'], none⟩]⟩, ⟨['d', 'a', 'm', 'a', 'l', 's'], ['t', 'h', 'e', 'n'], [⟨['d', 'a', 'm', 'a', 'l', 's'], ['t', 'h', 'e', 'n'], none⟩]⟩, ⟨['W', 'E', 'M'], ['w', 'h', 'o', 'm'], [⟨['W', 'E', 'M'], ['w', 'h', 'o', 'm'], none⟩]⟩, ⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], [⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("intervener", "damals"), ("feature", "none"), ("order", "intervener-first")] }

def ex24a : Datum :=
  { id := "kratzershimoyama2002_ex24a"
    source := ⟨"kratzer-shimoyama-2002", "(24a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat sie WEM nicht gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("sie", "she"), ("WEM", "to.whom"), ("nicht", "not"), ("gezeigt", "shown")]
    glossedWords := [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['s', 'i', 'e'], ['s', 'h', 'e'], [⟨['s', 'i', 'e'], ['s', 'h', 'e'], none⟩]⟩, ⟨['W', 'E', 'M'], ['t', 'o', '.', 'w', 'h', 'o', 'm'], [⟨['W', 'E', 'M'], ['t', 'o', '.', 'w', 'h', 'o', 'm'], none⟩]⟩, ⟨['n', 'i', 'c', 'h', 't'], ['n', 'o', 't'], [⟨['n', 'i', 'c', 'h', 't'], ['n', 'o', 't'], none⟩]⟩, ⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], [⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("intervener", "nicht"), ("feature", "Neg"), ("order", "wh-first")] }

def ex24b : Datum :=
  { id := "kratzershimoyama2002_ex24b"
    source := ⟨"kratzer-shimoyama-2002", "(24b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat sie WEM nie gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("sie", "she"), ("WEM", "to.whom"), ("nie", "never"), ("gezeigt", "shown")]
    glossedWords := [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['s', 'i', 'e'], ['s', 'h', 'e'], [⟨['s', 'i', 'e'], ['s', 'h', 'e'], none⟩]⟩, ⟨['W', 'E', 'M'], ['t', 'o', '.', 'w', 'h', 'o', 'm'], [⟨['W', 'E', 'M'], ['t', 'o', '.', 'w', 'h', 'o', 'm'], none⟩]⟩, ⟨['n', 'i', 'e'], ['n', 'e', 'v', 'e', 'r'], [⟨['n', 'i', 'e'], ['n', 'e', 'v', 'e', 'r'], none⟩]⟩, ⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], [⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("intervener", "nie"), ("feature", "exists"), ("order", "wh-first")] }

def ex24c : Datum :=
  { id := "kratzershimoyama2002_ex24c"
    source := ⟨"kratzer-shimoyama-2002", "(24c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat WEM niemand gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("WEM", "to.whom"), ("niemand", "nobody"), ("gezeigt", "shown")]
    glossedWords := [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['W', 'E', 'M'], ['t', 'o', '.', 'w', 'h', 'o', 'm'], [⟨['W', 'E', 'M'], ['t', 'o', '.', 'w', 'h', 'o', 'm'], none⟩]⟩, ⟨['n', 'i', 'e', 'm', 'a', 'n', 'd'], ['n', 'o', 'b', 'o', 'd', 'y'], [⟨['n', 'i', 'e', 'm', 'a', 'n', 'd'], ['n', 'o', 'b', 'o', 'd', 'y'], none⟩]⟩, ⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], [⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("intervener", "niemand"), ("feature", "exists"), ("order", "wh-first")] }

def ex24d : Datum :=
  { id := "kratzershimoyama2002_ex24d"
    source := ⟨"kratzer-shimoyama-2002", "(24d)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat WEM fast jeder gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("WEM", "to.whom"), ("fast", "almost"), ("jeder", "everybody"), ("gezeigt", "shown")]
    glossedWords := [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['W', 'E', 'M'], ['t', 'o', '.', 'w', 'h', 'o', 'm'], [⟨['W', 'E', 'M'], ['t', 'o', '.', 'w', 'h', 'o', 'm'], none⟩]⟩, ⟨['f', 'a', 's', 't'], ['a', 'l', 'm', 'o', 's', 't'], [⟨['f', 'a', 's', 't'], ['a', 'l', 'm', 'o', 's', 't'], none⟩]⟩, ⟨['j', 'e', 'd', 'e', 'r'], ['e', 'v', 'e', 'r', 'y', 'b', 'o', 'd', 'y'], [⟨['j', 'e', 'd', 'e', 'r'], ['e', 'v', 'e', 'r', 'y', 'b', 'o', 'd', 'y'], none⟩]⟩, ⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], [⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("intervener", "fast jeder"), ("feature", "exists"), ("order", "wh-first")] }

def ex24e : Datum :=
  { id := "kratzershimoyama2002_ex24e"
    source := ⟨"kratzer-shimoyama-2002", "(24e)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat WEM (irgend)jemand gezeigt?"
    glossedTokens := [("Was", "what"), ("hat", "has"), ("WEM", "to.whom"), ("(irgend)jemand", "somebody"), ("gezeigt", "shown")]
    glossedWords := [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], [⟨['W', 'a', 's'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['W', 'E', 'M'], ['t', 'o', '.', 'w', 'h', 'o', 'm'], [⟨['W', 'E', 'M'], ['t', 'o', '.', 'w', 'h', 'o', 'm'], none⟩]⟩, ⟨['(', 'i', 'r', 'g', 'e', 'n', 'd', ')', 'j', 'e', 'm', 'a', 'n', 'd'], ['s', 'o', 'm', 'e', 'b', 'o', 'd', 'y'], [⟨['i', 'r', 'g', 'e', 'n', 'd', 'j', 'e', 'm', 'a', 'n', 'd'], ['s', 'o', 'm', 'e', 'b', 'o', 'd', 'y'], none⟩]⟩, ⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], [⟨['g', 'e', 'z', 'e', 'i', 'g', 't'], ['s', 'h', 'o', 'w', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("intervener", "(irgend)jemand"), ("feature", "exists"), ("order", "wh-first")] }

def ex12 : Datum :=
  { id := "kratzershimoyama2002_ex12"
    source := ⟨"kratzer-shimoyama-2002", "(12)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Niemand musste irgendjemand einladen."
    glossedTokens := [("Niemand", "nobody"), ("musste", "had.to"), ("irgendjemand", "irgend-one"), ("einladen", "invite")]
    glossedWords := [⟨['N', 'i', 'e', 'm', 'a', 'n', 'd'], ['n', 'o', 'b', 'o', 'd', 'y'], [⟨['N', 'i', 'e', 'm', 'a', 'n', 'd'], ['n', 'o', 'b', 'o', 'd', 'y'], none⟩]⟩, ⟨['m', 'u', 's', 's', 't', 'e'], ['h', 'a', 'd', '.', 't', 'o'], [⟨['m', 'u', 's', 's', 't', 'e'], ['h', 'a', 'd', '.', 't', 'o'], none⟩]⟩, ⟨['i', 'r', 'g', 'e', 'n', 'd', 'j', 'e', 'm', 'a', 'n', 'd'], ['i', 'r', 'g', 'e', 'n', 'd', '-', 'o', 'n', 'e'], []⟩, ⟨['e', 'i', 'n', 'l', 'a', 'd', 'e', 'n'], ['i', 'n', 'v', 'i', 't', 'e'], [⟨['e', 'i', 'n', 'l', 'a', 'd', 'e', 'n'], ['i', 'n', 'v', 'i', 't', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "nobody"), ("intervener", "niemand"), ("feature", "exists")] }

def ex13 : Datum :=
  { id := "kratzershimoyama2002_ex13"
    source := ⟨"kratzer-shimoyama-2002", "(13)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ich bezweifle, dass sie je irgendjemand einladen durfte."
    glossedTokens := [("Ich", "I"), ("bezweifle", "doubt"), ("dass", "that"), ("sie", "she"), ("je", "ever"), ("irgendjemand", "irgend-one"), ("einladen", "invite"), ("durfte", "could")]
    glossedWords := [⟨['I', 'c', 'h'], ['I'], [⟨['I', 'c', 'h'], ['I'], none⟩]⟩, ⟨['b', 'e', 'z', 'w', 'e', 'i', 'f', 'l', 'e'], ['d', 'o', 'u', 'b', 't'], [⟨['b', 'e', 'z', 'w', 'e', 'i', 'f', 'l', 'e'], ['d', 'o', 'u', 'b', 't'], none⟩]⟩, ⟨['d', 'a', 's', 's'], ['t', 'h', 'a', 't'], [⟨['d', 'a', 's', 's'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['s', 'i', 'e'], ['s', 'h', 'e'], [⟨['s', 'i', 'e'], ['s', 'h', 'e'], none⟩]⟩, ⟨['j', 'e'], ['e', 'v', 'e', 'r'], [⟨['j', 'e'], ['e', 'v', 'e', 'r'], none⟩]⟩, ⟨['i', 'r', 'g', 'e', 'n', 'd', 'j', 'e', 'm', 'a', 'n', 'd'], ['i', 'r', 'g', 'e', 'n', 'd', '-', 'o', 'n', 'e'], []⟩, ⟨['e', 'i', 'n', 'l', 'a', 'd', 'e', 'n'], ['i', 'n', 'v', 'i', 't', 'e'], [⟨['e', 'i', 'n', 'l', 'a', 'd', 'e', 'n'], ['i', 'n', 'v', 'i', 't', 'e'], none⟩]⟩, ⟨['d', 'u', 'r', 'f', 't', 'e'], ['c', 'o', 'u', 'l', 'd'], [⟨['d', 'u', 'r', 'f', 't', 'e'], ['c', 'o', 'u', 'l', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "doubtVerb")] }

def ex16 : Datum :=
  { id := "kratzershimoyama2002_ex16"
    source := ⟨"kratzer-shimoyama-2002", "(16)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Du kannst dir irgendeins von diesen beiden Büchern leihen."
    glossedTokens := [("Du", "you"), ("kannst", "can"), ("dir", "you.DAT"), ("irgendeins", "irgend-one"), ("von", "of"), ("diesen", "those"), ("beiden", "two"), ("Büchern", "books"), ("leihen", "borrow")]
    glossedWords := [⟨['D', 'u'], ['y', 'o', 'u'], [⟨['D', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['k', 'a', 'n', 'n', 's', 't'], ['c', 'a', 'n'], [⟨['k', 'a', 'n', 'n', 's', 't'], ['c', 'a', 'n'], none⟩]⟩, ⟨['d', 'i', 'r'], ['y', 'o', 'u', '.', 'D', 'A', 'T'], [⟨['d', 'i', 'r'], ['y', 'o', 'u', '.', 'D', 'A', 'T'], none⟩]⟩, ⟨['i', 'r', 'g', 'e', 'n', 'd', 'e', 'i', 'n', 's'], ['i', 'r', 'g', 'e', 'n', 'd', '-', 'o', 'n', 'e'], []⟩, ⟨['v', 'o', 'n'], ['o', 'f'], [⟨['v', 'o', 'n'], ['o', 'f'], none⟩]⟩, ⟨['d', 'i', 'e', 's', 'e', 'n'], ['t', 'h', 'o', 's', 'e'], [⟨['d', 'i', 'e', 's', 'e', 'n'], ['t', 'h', 'o', 's', 'e'], none⟩]⟩, ⟨['b', 'e', 'i', 'd', 'e', 'n'], ['t', 'w', 'o'], [⟨['b', 'e', 'i', 'd', 'e', 'n'], ['t', 'w', 'o'], none⟩]⟩, ⟨['B', 'ü', 'c', 'h', 'e', 'r', 'n'], ['b', 'o', 'o', 'k', 's'], [⟨['B', 'ü', 'c', 'h', 'e', 'r', 'n'], ['b', 'o', 'o', 'k', 's'], none⟩]⟩, ⟨['l', 'e', 'i', 'h', 'e', 'n'], ['b', 'o', 'r', 'r', 'o', 'w'], [⟨['l', 'e', 'i', 'h', 'e', 'n'], ['b', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Two books are under discussion, an algebra book and a biology book."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "modalPossibility")] }

def ex17 : Datum :=
  { id := "kratzershimoyama2002_ex17"
    source := ⟨"kratzer-shimoyama-2002", "(17)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Du musst dir irgendeins von diesen beiden Büchern leihen."
    glossedTokens := [("Du", "you"), ("musst", "must"), ("dir", "you.DAT"), ("irgendeins", "irgend-one"), ("von", "of"), ("diesen", "those"), ("beiden", "two"), ("Büchern", "books"), ("leihen", "borrow")]
    glossedWords := [⟨['D', 'u'], ['y', 'o', 'u'], [⟨['D', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['m', 'u', 's', 's', 't'], ['m', 'u', 's', 't'], [⟨['m', 'u', 's', 's', 't'], ['m', 'u', 's', 't'], none⟩]⟩, ⟨['d', 'i', 'r'], ['y', 'o', 'u', '.', 'D', 'A', 'T'], [⟨['d', 'i', 'r'], ['y', 'o', 'u', '.', 'D', 'A', 'T'], none⟩]⟩, ⟨['i', 'r', 'g', 'e', 'n', 'd', 'e', 'i', 'n', 's'], ['i', 'r', 'g', 'e', 'n', 'd', '-', 'o', 'n', 'e'], []⟩, ⟨['v', 'o', 'n'], ['o', 'f'], [⟨['v', 'o', 'n'], ['o', 'f'], none⟩]⟩, ⟨['d', 'i', 'e', 's', 'e', 'n'], ['t', 'h', 'o', 's', 'e'], [⟨['d', 'i', 'e', 's', 'e', 'n'], ['t', 'h', 'o', 's', 'e'], none⟩]⟩, ⟨['b', 'e', 'i', 'd', 'e', 'n'], ['t', 'w', 'o'], [⟨['b', 'e', 'i', 'd', 'e', 'n'], ['t', 'w', 'o'], none⟩]⟩, ⟨['B', 'ü', 'c', 'h', 'e', 'r', 'n'], ['b', 'o', 'o', 'k', 's'], [⟨['B', 'ü', 'c', 'h', 'e', 'r', 'n'], ['b', 'o', 'o', 'k', 's'], none⟩]⟩, ⟨['l', 'e', 'i', 'h', 'e', 'n'], ['b', 'o', 'r', 'r', 'o', 'w'], [⟨['l', 'e', 'i', 'h', 'e', 'n'], ['b', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Two books are under discussion, an algebra book and a biology book."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "modalNecessity")] }

def ex18 : Datum :=
  { id := "kratzershimoyama2002_ex18"
    source := ⟨"kratzer-shimoyama-2002", "(18)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Du kannst dir auf keinen Fall irgendeins von diesen beiden Büchern leihen."
    glossedTokens := [("Du", "you"), ("kannst", "can"), ("dir", "you.DAT"), ("auf", "in"), ("keinen", "no"), ("Fall", "case"), ("irgendeins", "irgend-one"), ("von", "of"), ("diesen", "those"), ("beiden", "two"), ("Büchern", "books"), ("leihen", "borrow")]
    glossedWords := [⟨['D', 'u'], ['y', 'o', 'u'], [⟨['D', 'u'], ['y', 'o', 'u'], none⟩]⟩, ⟨['k', 'a', 'n', 'n', 's', 't'], ['c', 'a', 'n'], [⟨['k', 'a', 'n', 'n', 's', 't'], ['c', 'a', 'n'], none⟩]⟩, ⟨['d', 'i', 'r'], ['y', 'o', 'u', '.', 'D', 'A', 'T'], [⟨['d', 'i', 'r'], ['y', 'o', 'u', '.', 'D', 'A', 'T'], none⟩]⟩, ⟨['a', 'u', 'f'], ['i', 'n'], [⟨['a', 'u', 'f'], ['i', 'n'], none⟩]⟩, ⟨['k', 'e', 'i', 'n', 'e', 'n'], ['n', 'o'], [⟨['k', 'e', 'i', 'n', 'e', 'n'], ['n', 'o'], none⟩]⟩, ⟨['F', 'a', 'l', 'l'], ['c', 'a', 's', 'e'], [⟨['F', 'a', 'l', 'l'], ['c', 'a', 's', 'e'], none⟩]⟩, ⟨['i', 'r', 'g', 'e', 'n', 'd', 'e', 'i', 'n', 's'], ['i', 'r', 'g', 'e', 'n', 'd', '-', 'o', 'n', 'e'], []⟩, ⟨['v', 'o', 'n'], ['o', 'f'], [⟨['v', 'o', 'n'], ['o', 'f'], none⟩]⟩, ⟨['d', 'i', 'e', 's', 'e', 'n'], ['t', 'h', 'o', 's', 'e'], [⟨['d', 'i', 'e', 's', 'e', 'n'], ['t', 'h', 'o', 's', 'e'], none⟩]⟩, ⟨['b', 'e', 'i', 'd', 'e', 'n'], ['t', 'w', 'o'], [⟨['b', 'e', 'i', 'd', 'e', 'n'], ['t', 'w', 'o'], none⟩]⟩, ⟨['B', 'ü', 'c', 'h', 'e', 'r', 'n'], ['b', 'o', 'o', 'k', 's'], [⟨['B', 'ü', 'c', 'h', 'e', 'r', 'n'], ['b', 'o', 'o', 'k', 's'], none⟩]⟩, ⟨['l', 'e', 'i', 'h', 'e', 'n'], ['b', 'o', 'r', 'r', 'o', 'w'], [⟨['l', 'e', 'i', 'h', 'e', 'n'], ['b', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Two books are under discussion, an algebra book and a biology book."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "nobody"), ("intervener", "auf keinen Fall"), ("feature", "exists")] }

def ex21 : Datum :=
  { id := "kratzershimoyama2002_ex21"
    source := ⟨"kratzer-shimoyama-2002", "(21)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ich hab’ nicht irgendwas gelesen."
    glossedTokens := [("Ich", "I"), ("hab’", "have"), ("nicht", "not"), ("irgendwas", "irgend-what"), ("gelesen", "read")]
    glossedWords := [⟨['I', 'c', 'h'], ['I'], [⟨['I', 'c', 'h'], ['I'], none⟩]⟩, ⟨['h', 'a', 'b', '’'], ['h', 'a', 'v', 'e'], [⟨['h', 'a', 'b', '’'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['n', 'i', 'c', 'h', 't'], ['n', 'o', 't'], [⟨['n', 'i', 'c', 'h', 't'], ['n', 'o', 't'], none⟩]⟩, ⟨['i', 'r', 'g', 'e', 'n', 'd', 'w', 'a', 's'], ['i', 'r', 'g', 'e', 'n', 'd', '-', 'w', 'h', 'a', 't'], []⟩, ⟨['g', 'e', 'l', 'e', 's', 'e', 'n'], ['r', 'e', 'a', 'd'], [⟨['g', 'e', 'l', 'e', 's', 'e', 'n'], ['r', 'e', 'a', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("context", "negation"), ("intervener", "nicht"), ("feature", "Neg")] }

def ex22 : Datum :=
  { id := "kratzershimoyama2002_ex22"
    source := ⟨"kratzer-shimoyama-2002", "(22)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Lehrer hat gefragt, ob Hans irgendein Buch gelesen hat."
    glossedTokens := [("Der", "the"), ("Lehrer", "teacher"), ("hat", "has"), ("gefragt", "asked"), ("ob", "whether"), ("Hans", "Hans"), ("irgendein", "irgend-one"), ("Buch", "book"), ("gelesen", "read"), ("hat", "has")]
    glossedWords := [⟨['D', 'e', 'r'], ['t', 'h', 'e'], [⟨['D', 'e', 'r'], ['t', 'h', 'e'], none⟩]⟩, ⟨['L', 'e', 'h', 'r', 'e', 'r'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], [⟨['L', 'e', 'h', 'r', 'e', 'r'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩, ⟨['g', 'e', 'f', 'r', 'a', 'g', 't'], ['a', 's', 'k', 'e', 'd'], [⟨['g', 'e', 'f', 'r', 'a', 'g', 't'], ['a', 's', 'k', 'e', 'd'], none⟩]⟩, ⟨['o', 'b'], ['w', 'h', 'e', 't', 'h', 'e', 'r'], [⟨['o', 'b'], ['w', 'h', 'e', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['H', 'a', 'n', 's'], ['H', 'a', 'n', 's'], [⟨['H', 'a', 'n', 's'], ['H', 'a', 'n', 's'], none⟩]⟩, ⟨['i', 'r', 'g', 'e', 'n', 'd', 'e', 'i', 'n'], ['i', 'r', 'g', 'e', 'n', 'd', '-', 'o', 'n', 'e'], []⟩, ⟨['B', 'u', 'c', 'h'], ['b', 'o', 'o', 'k'], [⟨['B', 'u', 'c', 'h'], ['b', 'o', 'o', 'k'], none⟩]⟩, ⟨['g', 'e', 'l', 'e', 's', 'e', 'n'], ['r', 'e', 'a', 'd'], [⟨['g', 'e', 'l', 'e', 's', 'e', 'n'], ['r', 'e', 'a', 'd'], none⟩]⟩, ⟨['h', 'a', 't'], ['h', 'a', 's'], [⟨['h', 'a', 't'], ['h', 'a', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "question")] }

def all : List Datum := [ex23a, ex23b, ex23c, ex23d, ex23e, ex23f, ex23g, ex24a, ex24b, ex24c, ex24d, ex24e, ex12, ex13, ex16, ex17, ex18, ex21, ex22]

/-- The environment in which *irgendein* occurs. -/
inductive Context where
  /-- question: an embedded question -/
  | question
  /-- doubtVerb: the complement of *bezweifeln* 'doubt' -/
  | doubtVerb
  /-- modalPossibility: under a possibility modal -/
  | modalPossibility
  /-- modalNecessity: under a necessity modal -/
  | modalNecessity
  /-- nobody: under *niemand* 'nobody' -/
  | nobody
  /-- negation: under inflectional negation *nicht* -/
  | negation
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `context`. -/
def context (e : Datum) : Option Context :=
  e.parse? "context" [("question", .question), ("doubtVerb", .doubtVerb), ("modalPossibility", .modalPossibility),
    ("modalNecessity", .modalNecessity), ("nobody", .nobody), ("negation", .negation)]

end KratzerShimoyama2002.Examples
