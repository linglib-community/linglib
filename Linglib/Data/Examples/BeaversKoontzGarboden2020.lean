module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `BeaversKoontzGarboden2020` — typed example data

Auto-generated from `Linglib/Data/Examples/BeaversKoontzGarboden2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BeaversKoontzGarboden2020.Examples`.
-/

@[expose] public section

namespace BeaversKoontzGarboden2020.Examples

def bkg2020_25a : Datum :=
  { id := "bkg2020_25a"
    source := ⟨"beavers-koontz-garboden-2020", "ch. 1 (25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary flattened the rug again, and it had been flat before."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("restitutive: again scopes over the root state", .acceptable)]
    paperFeatures := [("diagnostic", "sublexical again"), ("attachment", "root")] }

def bkg2020_25b : Datum :=
  { id := "bkg2020_25b"
    source := ⟨"beavers-koontz-garboden-2020", "ch. 1 (25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary flattened the rug again, and it had flattened before."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("repetitive over the change: again scopes over v_become", .acceptable)]
    paperFeatures := [("diagnostic", "sublexical again"), ("attachment", "v_become")] }

def bkg2020_25c : Datum :=
  { id := "bkg2020_25c"
    source := ⟨"beavers-koontz-garboden-2020", "ch. 1 (25c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary flattened the rug again, and Mary had flattened it before."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("repetitive over the causation: again scopes over v_cause", .acceptable)]
    paperFeatures := [("diagnostic", "sublexical again"), ("attachment", "v_cause")] }

def bkg2020_ch2_46a : Datum :=
  { id := "bkg2020_ch2_46a"
    source := ⟨"beavers-koontz-garboden-2020", "ch. 2 (46a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John sharpened the knife again."
    glossedTokens := []
    context := "John buys a knife forged already sharp, uses it until it becomes blunt, and sharpens it with a whetting stone."
    judgment := .acceptable
    contrasts := []
    readings := [("restitutive: could be just one sharpening", .acceptable)]
    paperFeatures := [("root class", "property concept"), ("diagnostic", "restitutive again")] }

def bkg2020_ch2_47a : Datum :=
  { id := "bkg2020_ch2_47a"
    source := ⟨"beavers-koontz-garboden-2020", "ch. 2 (47a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sandy returned the shirt again."
    glossedTokens := []
    context := "A boutique store makes their shirts in the back. Sandy buys one, decides she does not want it, and exchanges it."
    judgment := .unacceptable
    contrasts := []
    readings := [("repetitive: necessarily two returnings", .acceptable)]
    paperFeatures := [("root class", "result"), ("diagnostic", "restitutive again")] }

def bkg2020_ch2_47b : Datum :=
  { id := "bkg2020_ch2_47b"
    source := ⟨"beavers-koontz-garboden-2020", "ch. 2 (47b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leah thawed the meat again."
    glossedTokens := []
    context := "Leah kills a rabbit, butchers it, freezes the fresh meat for three days, then puts it out to thaw."
    judgment := .unacceptable
    contrasts := []
    readings := [("repetitive: necessarily two defrostings", .acceptable)]
    paperFeatures := [("root class", "result"), ("diagnostic", "restitutive again")] }

def bkg2020_ch2_48 : Datum :=
  { id := "bkg2020_ch2_48"
    source := ⟨"beavers-koontz-garboden-2020", "ch. 2 (48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John fried the fruit again."
    glossedTokens := []
    context := "John finds a fruit that naturally has brown, fatty edges, trims off the edges, refrigerates it, and later fries it."
    judgment := .unacceptable
    contrasts := []
    readings := [("repetitive: necessarily two fryings", .acceptable)]
    paperFeatures := [("root class", "result"), ("diagnostic", "restitutive again")] }

def bkg2020_ch3_10a : Datum :=
  { id := "bkg2020_ch3_10a"
    source := ⟨"beavers-koontz-garboden-2020", "ch. 3 (10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary gave John a ring, but he never got it."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("root class", "true possession"), ("diagnostic", "result denial")] }

def bkg2020_ch3_11a : Datum :=
  { id := "bkg2020_ch3_11a"
    source := ⟨"beavers-koontz-garboden-2020", "ch. 3 (11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary sent John a letter, but it got lost in the mail and he never got it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root class", "release"), ("diagnostic", "result denial")] }

def bkg2020_ch3_48a : Datum :=
  { id := "bkg2020_ch3_48a"
    source := ⟨"beavers-koontz-garboden-2020", "ch. 3 (48a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary handed John the book, but it never came to be on his person."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("root class", "transfer of possession by motion"), ("diagnostic", "result denial")] }

def bkg2020_ch4_25a : Datum :=
  { id := "bkg2020_ch4_25a"
    source := ⟨"beavers-koontz-garboden-2020", "ch. 4 (25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane just drowned Joe, but nothing is different about him."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb class", "manner of killing"), ("diagnostic", "result denial")] }

def bkg2020_ch4_26c : Datum :=
  { id := "bkg2020_ch4_26c"
    source := ⟨"beavers-koontz-garboden-2020", "ch. 4 (26c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All last night, Shane drowned."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("verb class", "manner of killing"), ("diagnostic", "object deletion")] }

def bkg2020_ch4_32b : Datum :=
  { id := "bkg2020_ch4_32b"
    source := ⟨"beavers-koontz-garboden-2020", "ch. 4 (32b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The governor drowned the prisoner, but didn't move a muscle — rather, during the execution she just sat there, tacitly refusing to order a halt!"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verb class", "manner of killing"), ("diagnostic", "action denial")] }

def all : List Datum := [bkg2020_25a, bkg2020_25b, bkg2020_25c, bkg2020_ch2_46a, bkg2020_ch2_47a, bkg2020_ch2_47b, bkg2020_ch2_48, bkg2020_ch3_10a, bkg2020_ch3_11a, bkg2020_ch3_48a, bkg2020_ch4_25a, bkg2020_ch4_26c, bkg2020_ch4_32b]

/-- The classes of root the book distinguishes. -/
inductive RootClass where
  /-- property concept: a root that describes a state and entails no change -/
  | propertyConcept
  /-- result: a root whose state arises from a change -/
  | result
  /-- true possession: a ditransitive root that entails caused possession, as of *give* -/
  | truePossession
  /-- transfer of possession by motion: a ditransitive root that entails caused possession reached by motion, as of *hand* -/
  | transferByMotion
  /-- release: a ditransitive root that entails that the theme leaves the causer, as of *send* -/
  | release
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `root class`. -/
def rootClass (e : Datum) : Option RootClass :=
  e.parse? "root class" [("property concept", .propertyConcept), ("result", .result),
    ("true possession", .truePossession),
    ("transfer of possession by motion", .transferByMotion), ("release", .release)]

/-- The verb classes of chapter 4. -/
inductive VerbClass where
  /-- manner of killing: a verb of killing that names the manner, as *drown* -/
  | mannerOfKilling
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `verb class`. -/
def verbClass (e : Datum) : Option VerbClass :=
  e.parse? "verb class" [("manner of killing", .mannerOfKilling)]

/-- The diagnostics the examples apply. -/
inductive Diagnostic where
  /-- sublexical again: *again* attached within the causative structure -/
  | sublexicalAgain
  /-- restitutive again: *again* with a reading on which only the state held before -/
  | restitutiveAgain
  /-- result denial: a continuation that denies the result -/
  | resultDenial
  /-- object deletion: the verb without its object -/
  | objectDeletion
  /-- action denial: a continuation that denies that the causer acted -/
  | actionDenial
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `diagnostic`. -/
def diagnostic (e : Datum) : Option Diagnostic :=
  e.parse? "diagnostic" [("sublexical again", .sublexicalAgain), ("restitutive again", .restitutiveAgain),
    ("result denial", .resultDenial), ("object deletion", .objectDeletion),
    ("action denial", .actionDenial)]

/-- The attachment sites of *again* (27). -/
inductive Attachment where
  /-- root: the root, for the restitutive reading -/
  | root
  /-- v_become: `vbecome`, for the repetitive reading over the change -/
  | vBecome
  /-- v_cause: `vcause`, for the repetitive reading over the causation -/
  | vCause
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `attachment`. -/
def attachment (e : Datum) : Option Attachment :=
  e.parse? "attachment" [("root", .root), ("v_become", .vBecome), ("v_cause", .vCause)]

end BeaversKoontzGarboden2020.Examples
