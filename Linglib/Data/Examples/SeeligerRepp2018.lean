module

public import Linglib.Data.Examples.Schema

/-!
# `SeeligerRepp2018` — typed example data

Auto-generated from `Linglib/Data/Examples/SeeligerRepp2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace SeeligerRepp2018.Examples`.
-/

@[expose] public section

namespace SeeligerRepp2018.Examples

def en_pdq : Datum :=
  { id := "seeligerrepp2018_en_pdq"
    source := ⟨"seeliger-repp-2018", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Peter is coming?"
    glossedTokens := []
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees Peter's name on the list."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("type", "PDQ"), ("declarative", "p"), ("evidential", "+positive"), ("epistemic", "-positive")] }

def de_pdq : Datum :=
  { id := "seeligerrepp2018_de_pdq"
    source := ⟨"seeliger-repp-2018", "(5b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Peter kommt?"
    glossedTokens := [("Peter", "Peter"), ("kommt", "comes")]
    glossedWords := [⟨[['P', 'e', 't', 'e', 'r']], [['P', 'e', 't', 'e', 'r']]⟩, ⟨[['k', 'o', 'm', 'm', 't']], [['c', 'o', 'm', 'e', 's']]⟩]
    lgrConformance := some .wordAligned
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees Peter's name on the list."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("type", "PDQ"), ("declarative", "p"), ("evidential", "+positive"), ("epistemic", "-positive")] }

def sv_pdq : Datum :=
  { id := "seeligerrepp2018_sv_pdq"
    source := ⟨"seeliger-repp-2018", "(5c)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Peter kommer?"
    glossedTokens := [("Peter", "Peter"), ("kommer", "comes")]
    glossedWords := [⟨[['P', 'e', 't', 'e', 'r']], [['P', 'e', 't', 'e', 'r']]⟩, ⟨[['k', 'o', 'm', 'm', 'e', 'r']], [['c', 'o', 'm', 'e', 's']]⟩]
    lgrConformance := some .wordAligned
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees Peter's name on the list."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("type", "PDQ"), ("declarative", "p"), ("evidential", "+positive"), ("epistemic", "-positive")] }

def en_ndq : Datum :=
  { id := "seeligerrepp2018_en_ndq"
    source := ⟨"seeliger-repp-2018", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Peter isn't coming?"
    glossedTokens := []
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees that Peter's name on the list is crossed out."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("type", "NDQ"), ("declarative", "not p"), ("evidential", "+negative"), ("epistemic", "-negative")] }

def de_ndq : Datum :=
  { id := "seeligerrepp2018_de_ndq"
    source := ⟨"seeliger-repp-2018", "(6b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Peter kommt nicht?"
    glossedTokens := [("Peter", "Peter"), ("kommt", "comes"), ("nicht", "not")]
    glossedWords := [⟨[['P', 'e', 't', 'e', 'r']], [['P', 'e', 't', 'e', 'r']]⟩, ⟨[['k', 'o', 'm', 'm', 't']], [['c', 'o', 'm', 'e', 's']]⟩, ⟨[['n', 'i', 'c', 'h', 't']], [['n', 'o', 't']]⟩]
    lgrConformance := some .wordAligned
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees that Peter's name on the list is crossed out."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("type", "NDQ"), ("declarative", "not p"), ("evidential", "+negative"), ("epistemic", "-negative")] }

def sv_ndq : Datum :=
  { id := "seeligerrepp2018_sv_ndq"
    source := ⟨"seeliger-repp-2018", "(6c)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Peter kommer inte?"
    glossedTokens := [("Peter", "Peter"), ("kommer", "comes"), ("inte", "not")]
    glossedWords := [⟨[['P', 'e', 't', 'e', 'r']], [['P', 'e', 't', 'e', 'r']]⟩, ⟨[['k', 'o', 'm', 'm', 'e', 'r']], [['c', 'o', 'm', 'e', 's']]⟩, ⟨[['i', 'n', 't', 'e']], [['n', 'o', 't']]⟩]
    lgrConformance := some .wordAligned
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees that Peter's name on the list is crossed out."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("type", "NDQ"), ("declarative", "not p"), ("evidential", "+negative"), ("epistemic", "-negative")] }

def en_nrq : Datum :=
  { id := "seeligerrepp2018_en_nrq"
    source := ⟨"seeliger-repp-2018", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Surely Peter isn't coming?"
    glossedTokens := []
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees Peter's name on the list."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("type", "NRQ"), ("declarative", "not p"), ("evidential", "+positive"), ("epistemic", "+negative")] }

def de_nrq_doch_wohl : Datum :=
  { id := "seeligerrepp2018_de_nrq_doch_wohl"
    source := ⟨"seeliger-repp-2018", "(7b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Peter kommt doch wohl nicht?"
    glossedTokens := [("Peter", "Peter"), ("kommt", "comes"), ("doch", "mp"), ("wohl", "mp"), ("nicht", "not")]
    glossedWords := [⟨[['P', 'e', 't', 'e', 'r']], [['P', 'e', 't', 'e', 'r']]⟩, ⟨[['k', 'o', 'm', 'm', 't']], [['c', 'o', 'm', 'e', 's']]⟩, ⟨[['d', 'o', 'c', 'h']], [['m', 'p']]⟩, ⟨[['w', 'o', 'h', 'l']], [['m', 'p']]⟩, ⟨[['n', 'i', 'c', 'h', 't']], [['n', 'o', 't']]⟩]
    lgrConformance := some .wordAligned
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees Peter's name on the list."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("type", "NRQ"), ("declarative", "not p"), ("evidential", "+positive"), ("epistemic", "+negative")] }

def sv_nrq_fronted_negation : Datum :=
  { id := "seeligerrepp2018_sv_nrq_fronted_negation"
    source := ⟨"seeliger-repp-2018", "(7c)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Inte kommer Peter?"
    glossedTokens := [("Inte", "not"), ("kommer", "comes"), ("Peter", "Peter")]
    glossedWords := [⟨[['I', 'n', 't', 'e']], [['n', 'o', 't']]⟩, ⟨[['k', 'o', 'm', 'm', 'e', 'r']], [['c', 'o', 'm', 'e', 's']]⟩, ⟨[['P', 'e', 't', 'e', 'r']], [['P', 'e', 't', 'e', 'r']]⟩]
    lgrConformance := some .wordAligned
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees Peter's name on the list."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("type", "NRQ"), ("declarative", "not p"), ("evidential", "+positive"), ("epistemic", "+negative"), ("negation", "fronted"), ("väl", "no"), ("men", "no"), ("visst/nog", "no"), ("evidence", "direct")] }

def en_prq : Datum :=
  { id := "seeligerrepp2018_en_prq"
    source := ⟨"seeliger-repp-2018", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Surely Peter is coming?"
    glossedTokens := []
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees that Peter's name on the list is crossed out."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("type", "PRQ"), ("declarative", "p"), ("evidential", "+negative"), ("epistemic", "+positive")] }

def de_prq_doch_wohl : Datum :=
  { id := "seeligerrepp2018_de_prq_doch_wohl"
    source := ⟨"seeliger-repp-2018", "(8b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Peter kommt doch wohl?"
    glossedTokens := [("Peter", "Peter"), ("kommt", "comes"), ("doch", "mp"), ("wohl", "mp")]
    glossedWords := [⟨[['P', 'e', 't', 'e', 'r']], [['P', 'e', 't', 'e', 'r']]⟩, ⟨[['k', 'o', 'm', 'm', 't']], [['c', 'o', 'm', 'e', 's']]⟩, ⟨[['d', 'o', 'c', 'h']], [['m', 'p']]⟩, ⟨[['w', 'o', 'h', 'l']], [['m', 'p']]⟩]
    lgrConformance := some .wordAligned
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees that Peter's name on the list is crossed out."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("type", "PRQ"), ("declarative", "p"), ("evidential", "+negative"), ("epistemic", "+positive")] }

def sv_prq_men_val : Datum :=
  { id := "seeligerrepp2018_sv_prq_men_val"
    source := ⟨"seeliger-repp-2018", "(8c)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Men Peter kommer väl?"
    glossedTokens := [("Men", "but"), ("Peter", "Peter"), ("kommer", "comes"), ("väl", "mp")]
    glossedWords := [⟨[['M', 'e', 'n']], [['b', 'u', 't']]⟩, ⟨[['P', 'e', 't', 'e', 'r']], [['P', 'e', 't', 'e', 'r']]⟩, ⟨[['k', 'o', 'm', 'm', 'e', 'r']], [['c', 'o', 'm', 'e', 's']]⟩, ⟨[['v', 'ä', 'l']], [['m', 'p']]⟩]
    lgrConformance := some .wordAligned
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees that Peter's name on the list is crossed out."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("type", "PRQ"), ("declarative", "p"), ("evidential", "+negative"), ("epistemic", "+positive"), ("negation", "none"), ("väl", "yes"), ("men", "yes"), ("visst/nog", "no"), ("evidence", "direct")] }

def sv_prq_visst : Datum :=
  { id := "seeligerrepp2018_sv_prq_visst"
    source := ⟨"seeliger-repp-2018", "(8c′)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Visst kommer Peter?"
    glossedTokens := [("Visst", "mp"), ("kommer", "comes"), ("Peter", "Peter")]
    glossedWords := [⟨[['V', 'i', 's', 's', 't']], [['m', 'p']]⟩, ⟨[['k', 'o', 'm', 'm', 'e', 'r']], [['c', 'o', 'm', 'e', 's']]⟩, ⟨[['P', 'e', 't', 'e', 'r']], [['P', 'e', 't', 'e', 'r']]⟩]
    lgrConformance := some .wordAligned
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees that Peter's name on the list is crossed out."
    judgment := .acceptable
    alternatives := [("Nog kommer Peter?", .acceptable)]
    readings := []
    paperFeatures := [("section", "3"), ("type", "PRQ"), ("declarative", "p"), ("evidential", "+negative"), ("epistemic", "+positive"), ("negation", "none"), ("väl", "no"), ("men", "no"), ("visst/nog", "yes"), ("evidence", "direct")] }

def sv_23a : Datum :=
  { id := "seeligerrepp2018_sv_23a"
    source := ⟨"seeliger-repp-2018", "(23a)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Noah är till sjöss?"
    glossedTokens := [("Noah", "Noah"), ("är", "is"), ("till", "to"), ("sjöss", "sea")]
    glossedWords := [⟨[['N', 'o', 'a', 'h']], [['N', 'o', 'a', 'h']]⟩, ⟨[['ä', 'r']], [['i', 's']]⟩, ⟨[['t', 'i', 'l', 'l']], [['t', 'o']]⟩, ⟨[['s', 'j', 'ö', 's', 's']], [['s', 'e', 'a']]⟩]
    lgrConformance := some .wordAligned
    context := "Ann: Noah is coming to the party tomorrow."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.3"), ("type", "PRQ"), ("negation", "none"), ("väl", "no"), ("men", "no"), ("visst/nog", "no"), ("evidence", "indirect")] }

def sv_23b : Datum :=
  { id := "seeligerrepp2018_sv_23b"
    source := ⟨"seeliger-repp-2018", "(23b)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Men Noah är väl till sjöss?"
    glossedTokens := [("Men", "but"), ("Noah", "Noah"), ("är", "is"), ("väl", "mp"), ("till", "to"), ("sjöss", "sea")]
    glossedWords := [⟨[['M', 'e', 'n']], [['b', 'u', 't']]⟩, ⟨[['N', 'o', 'a', 'h']], [['N', 'o', 'a', 'h']]⟩, ⟨[['ä', 'r']], [['i', 's']]⟩, ⟨[['v', 'ä', 'l']], [['m', 'p']]⟩, ⟨[['t', 'i', 'l', 'l']], [['t', 'o']]⟩, ⟨[['s', 'j', 'ö', 's', 's']], [['s', 'e', 'a']]⟩]
    lgrConformance := some .wordAligned
    context := "Ann: Noah is coming to the party tomorrow."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.3"), ("type", "PRQ"), ("negation", "none"), ("väl", "yes"), ("men", "yes"), ("visst/nog", "no"), ("evidence", "indirect")] }

def sv_23c : Datum :=
  { id := "seeligerrepp2018_sv_23c"
    source := ⟨"seeliger-repp-2018", "(23c)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Visst är Noah till sjöss?"
    glossedTokens := [("Visst", "mp"), ("är", "is"), ("Noah", "Noah"), ("till", "to"), ("sjöss", "sea")]
    glossedWords := [⟨[['V', 'i', 's', 's', 't']], [['m', 'p']]⟩, ⟨[['ä', 'r']], [['i', 's']]⟩, ⟨[['N', 'o', 'a', 'h']], [['N', 'o', 'a', 'h']]⟩, ⟨[['t', 'i', 'l', 'l']], [['t', 'o']]⟩, ⟨[['s', 'j', 'ö', 's', 's']], [['s', 'e', 'a']]⟩]
    lgrConformance := some .wordAligned
    context := "Ann: Noah is coming to the party tomorrow."
    judgment := .unacceptable
    alternatives := [("Nog är Noah till sjöss?", .unacceptable)]
    readings := []
    paperFeatures := [("section", "5.3"), ("type", "PRQ"), ("negation", "none"), ("väl", "no"), ("men", "no"), ("visst/nog", "yes"), ("evidence", "indirect")] }

def sv_23d : Datum :=
  { id := "seeligerrepp2018_sv_23d"
    source := ⟨"seeliger-repp-2018", "(23d)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Visst är väl Noah till sjöss?"
    glossedTokens := [("Visst", "mp"), ("är", "is"), ("väl", "mp"), ("Noah", "Noah"), ("till", "to"), ("sjöss", "sea")]
    glossedWords := [⟨[['V', 'i', 's', 's', 't']], [['m', 'p']]⟩, ⟨[['ä', 'r']], [['i', 's']]⟩, ⟨[['v', 'ä', 'l']], [['m', 'p']]⟩, ⟨[['N', 'o', 'a', 'h']], [['N', 'o', 'a', 'h']]⟩, ⟨[['t', 'i', 'l', 'l']], [['t', 'o']]⟩, ⟨[['s', 'j', 'ö', 's', 's']], [['s', 'e', 'a']]⟩]
    lgrConformance := some .wordAligned
    context := "Ann: Noah is coming to the party tomorrow."
    judgment := .unacceptable
    alternatives := [("Nog är väl Noah till sjöss?", .unacceptable)]
    readings := []
    paperFeatures := [("section", "5.3"), ("type", "PRQ"), ("negation", "none"), ("väl", "yes"), ("men", "no"), ("visst/nog", "yes"), ("evidence", "indirect")] }

def sv_24a : Datum :=
  { id := "seeligerrepp2018_sv_24a"
    source := ⟨"seeliger-repp-2018", "(24a)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Noah är inte till sjöss?"
    glossedTokens := [("Noah", "Noah"), ("är", "is"), ("inte", "not"), ("till", "to"), ("sjöss", "sea")]
    glossedWords := [⟨[['N', 'o', 'a', 'h']], [['N', 'o', 'a', 'h']]⟩, ⟨[['ä', 'r']], [['i', 's']]⟩, ⟨[['i', 'n', 't', 'e']], [['n', 'o', 't']]⟩, ⟨[['t', 'i', 'l', 'l']], [['t', 'o']]⟩, ⟨[['s', 'j', 'ö', 's', 's']], [['s', 'e', 'a']]⟩]
    lgrConformance := some .wordAligned
    context := "Whenever Noah is on shore leave, he always visits every party. Ann: Noah is not coming to the party tomorrow."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.3"), ("type", "NRQ"), ("negation", "low"), ("väl", "no"), ("men", "no"), ("visst/nog", "no"), ("evidence", "indirect")] }

def sv_24b : Datum :=
  { id := "seeligerrepp2018_sv_24b"
    source := ⟨"seeliger-repp-2018", "(24b)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Noah är väl inte till sjöss?"
    glossedTokens := [("Noah", "Noah"), ("är", "is"), ("väl", "mp"), ("inte", "not"), ("till", "to"), ("sjöss", "sea")]
    glossedWords := [⟨[['N', 'o', 'a', 'h']], [['N', 'o', 'a', 'h']]⟩, ⟨[['ä', 'r']], [['i', 's']]⟩, ⟨[['v', 'ä', 'l']], [['m', 'p']]⟩, ⟨[['i', 'n', 't', 'e']], [['n', 'o', 't']]⟩, ⟨[['t', 'i', 'l', 'l']], [['t', 'o']]⟩, ⟨[['s', 'j', 'ö', 's', 's']], [['s', 'e', 'a']]⟩]
    lgrConformance := some .wordAligned
    context := "Whenever Noah is on shore leave, he always visits every party. Ann: Noah is not coming to the party tomorrow."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.3"), ("type", "NRQ"), ("negation", "low"), ("väl", "yes"), ("men", "no"), ("visst/nog", "no"), ("evidence", "indirect")] }

def sv_24c : Datum :=
  { id := "seeligerrepp2018_sv_24c"
    source := ⟨"seeliger-repp-2018", "(24c)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Inte är Noah till sjöss?"
    glossedTokens := [("Inte", "not"), ("är", "is"), ("Noah", "Noah"), ("till", "to"), ("sjöss", "sea")]
    glossedWords := [⟨[['I', 'n', 't', 'e']], [['n', 'o', 't']]⟩, ⟨[['ä', 'r']], [['i', 's']]⟩, ⟨[['N', 'o', 'a', 'h']], [['N', 'o', 'a', 'h']]⟩, ⟨[['t', 'i', 'l', 'l']], [['t', 'o']]⟩, ⟨[['s', 'j', 'ö', 's', 's']], [['s', 'e', 'a']]⟩]
    lgrConformance := some .wordAligned
    context := "Whenever Noah is on shore leave, he always visits every party. Ann: Noah is not coming to the party tomorrow."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.3"), ("type", "NRQ"), ("negation", "fronted"), ("väl", "no"), ("men", "no"), ("visst/nog", "no"), ("evidence", "indirect")] }

def sv_24d : Datum :=
  { id := "seeligerrepp2018_sv_24d"
    source := ⟨"seeliger-repp-2018", "(24d)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Inte är väl Noah till sjöss?"
    glossedTokens := [("Inte", "not"), ("är", "is"), ("väl", "mp"), ("Noah", "Noah"), ("till", "to"), ("sjöss", "sea")]
    glossedWords := [⟨[['I', 'n', 't', 'e']], [['n', 'o', 't']]⟩, ⟨[['ä', 'r']], [['i', 's']]⟩, ⟨[['v', 'ä', 'l']], [['m', 'p']]⟩, ⟨[['N', 'o', 'a', 'h']], [['N', 'o', 'a', 'h']]⟩, ⟨[['t', 'i', 'l', 'l']], [['t', 'o']]⟩, ⟨[['s', 'j', 'ö', 's', 's']], [['s', 'e', 'a']]⟩]
    lgrConformance := some .wordAligned
    context := "Whenever Noah is on shore leave, he always visits every party. Ann: Noah is not coming to the party tomorrow."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.3"), ("type", "NRQ"), ("negation", "fronted"), ("väl", "yes"), ("men", "no"), ("visst/nog", "no"), ("evidence", "indirect")] }

def all : List Datum := [en_pdq, de_pdq, sv_pdq, en_ndq, de_ndq, sv_ndq, en_nrq, de_nrq_doch_wohl, sv_nrq_fronted_negation, en_prq, de_prq_doch_wohl, sv_prq_men_val, sv_prq_visst, sv_23a, sv_23b, sv_23c, sv_23d, sv_24a, sv_24b, sv_24c, sv_24d]

end SeeligerRepp2018.Examples
