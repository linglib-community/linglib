module

public import Linglib.Data.Examples.Schema

/-!
# `Marantz2013` — typed example data

Auto-generated from `Linglib/Data/Examples/Marantz2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Marantz2013.Examples`.
-/

@[expose] public section

namespace Marantz2013.Examples

def taught : Datum :=
  { id := "marantz2013_taught"
    source := ⟨"marantz-2013", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "taught"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "TEACH"), ("h1", "v"), ("h1exp", ""), ("h2", "voice"), ("h2exp", ""), ("h3", "T"), ("h3exp", "-t"), ("trigger", "3"), ("allomorphy", "attested"), ("allosemy", "blocked")] }

def quantized : Datum :=
  { id := "marantz2013_quantized"
    source := ⟨"marantz-2013", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "quantized"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "QUANTUM"), ("h1", "v"), ("h1exp", "-ize"), ("h2", "T"), ("h2exp", "-d"), ("trigger", "2"), ("allomorphy", "blocked")] }

def worker : Datum :=
  { id := "marantz2013_worker"
    source := ⟨"marantz-2013", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "work-Ø-(ø)-er"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "WORK"), ("h1", "v"), ("h1exp", ""), ("h2", "n"), ("h2exp", "-er"), ("trigger", "2"), ("allomorphy", "blocked")] }

def rotor : Datum :=
  { id := "marantz2013_rotor"
    source := ⟨"marantz-2013", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "rotor"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "ROTATE"), ("h1", "n"), ("h1exp", "-or"), ("trigger", "1"), ("allomorphy", "attested")] }

def rotater : Datum :=
  { id := "marantz2013_rotater"
    source := ⟨"marantz-2013", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "rotater"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "ROTATE"), ("h1", "v"), ("h1exp", ""), ("h2", "n"), ("h2exp", "-er"), ("trigger", "2"), ("allomorphy", "blocked")] }

def curiosity : Datum :=
  { id := "marantz2013_curiosity"
    source := ⟨"marantz-2013", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "curiosity"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "CURIOUS"), ("h1", "n"), ("h1exp", "-ity"), ("trigger", "1"), ("allomorphy", "attested")] }

def gloriousness : Datum :=
  { id := "marantz2013_gloriousness"
    source := ⟨"marantz-2013", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "gloriousness"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "GLORY"), ("h1", "a"), ("h1exp", "-ous"), ("h2", "n"), ("h2exp", "-ness"), ("trigger", "2"), ("allomorphy", "blocked")] }

def house_v : Datum :=
  { id := "marantz2013_house_v"
    source := ⟨"marantz-2013", "§6.3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "hou[z]e"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "HOUSE"), ("h1", "v"), ("h1exp", ""), ("trigger", "1"), ("allomorphy", "attested"), ("allosemy", "attested")] }

def housed_denominal : Datum :=
  { id := "marantz2013_housed_denominal"
    source := ⟨"marantz-2013", "§6.3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He took a bunch of plastic models and housed the room in revenge"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "HOUSE"), ("h1", "n"), ("h1exp", ""), ("h2", "v"), ("h2exp", ""), ("trigger", "2"), ("allomorphy", "blocked"), ("allosemy", "blocked")] }

def global : Datum :=
  { id := "marantz2013_global"
    source := ⟨"marantz-2013", "§6.3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "global"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "GLOBE"), ("h1", "a"), ("h1exp", "-al"), ("trigger", "1"), ("allosemy", "attested")] }

def globalize : Datum :=
  { id := "marantz2013_globalize"
    source := ⟨"marantz-2013", "§6.3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "globalize"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "GLOBE"), ("h1", "a"), ("h1exp", "-al"), ("h2", "v"), ("h2exp", "-ize"), ("trigger", "2"), ("allosemy", "blocked")] }

def novelize : Datum :=
  { id := "marantz2013_novelize"
    source := ⟨"marantz-2013", "§6.3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "novelize"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "NOVEL"), ("h1", "v"), ("h1exp", "-ize"), ("trigger", "1"), ("allosemy", "attested")] }

def novelization : Datum :=
  { id := "marantz2013_novelization"
    source := ⟨"marantz-2013", "§6.3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "novelization"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "NOVEL"), ("h1", "v"), ("h1exp", "-ize"), ("h2", "n"), ("h2exp", "-ation"), ("trigger", "2"), ("allosemy", "blocked")] }

def nationalize : Datum :=
  { id := "marantz2013_nationalize"
    source := ⟨"marantz-2013", "§6.3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "nationalize"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "NATION"), ("h1", "a"), ("h1exp", "-al"), ("h2", "v"), ("h2exp", "-ize"), ("trigger", "2"), ("allosemy", "blocked"), ("idiom", "attested")] }

def jp_koe : Datum :=
  { id := "marantz2013_jp_koe"
    source := ⟨"marantz-2013", "Table 6.1"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "ko-e"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "ko(y)"), ("h1", "v0"), ("h1exp", "-e"), ("h2", "cont"), ("h2exp", ""), ("h3", "n"), ("h3exp", ""), ("trigger", "2"), ("allosemy", "attested")] }

def jp_nagashi : Datum :=
  { id := "marantz2013_jp_nagashi"
    source := ⟨"marantz-2013", "Table 6.1"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "nag-ashi"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "nag"), ("h1", "v0"), ("h1exp", "-as"), ("h2", "cont"), ("h2exp", "-i"), ("h3", "n"), ("h3exp", ""), ("trigger", "2"), ("allosemy", "attested")] }

def jp_dashi : Datum :=
  { id := "marantz2013_jp_dashi"
    source := ⟨"marantz-2013", "Table 6.1"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "d-ashi"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "d"), ("h1", "v0"), ("h1exp", "-as"), ("h2", "cont"), ("h2exp", "-i"), ("h3", "n"), ("h3exp", ""), ("trigger", "2"), ("allosemy", "attested")] }

def jp_sagari : Datum :=
  { id := "marantz2013_jp_sagari"
    source := ⟨"marantz-2013", "Table 6.1"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "(o)sag-ari"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "sag"), ("h1", "v0"), ("h1exp", "-ar"), ("h2", "cont"), ("h2exp", "-i"), ("h3", "n"), ("h3exp", ""), ("trigger", "2"), ("allosemy", "attested")] }

def jp_mage : Datum :=
  { id := "marantz2013_jp_mage"
    source := ⟨"marantz-2013", "Table 6.1"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "mag-e"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "mag"), ("h1", "v0"), ("h1exp", "-e"), ("h2", "cont"), ("h2exp", ""), ("h3", "n"), ("h3exp", ""), ("trigger", "2"), ("allosemy", "attested")] }

def gr_axnistos : Datum :=
  { id := "marantz2013_gr_axnistos"
    source := ⟨"marantz-2013", "(5a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "axn-is-tos"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "axn"), ("h1", "v0"), ("h1exp", "-is"), ("h2", "ptcp"), ("h2exp", "-t"), ("h3", "a"), ("h3exp", ""), ("trigger", "2"), ("allosemy", "attested")] }

def gr_koudounistos : Datum :=
  { id := "marantz2013_gr_koudounistos"
    source := ⟨"marantz-2013", "(5b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "koudoun-is-tos"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "koudoun"), ("h1", "v0"), ("h1exp", "-is"), ("h2", "ptcp"), ("h2exp", "-t"), ("h3", "a"), ("h3exp", ""), ("trigger", "2"), ("allosemy", "attested")] }

def gr_magireftos : Datum :=
  { id := "marantz2013_gr_magireftos"
    source := ⟨"marantz-2013", "(5c)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "magir-ef-tos"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "magir"), ("h1", "v0"), ("h1exp", "-ef"), ("h2", "ptcp"), ("h2exp", "-t"), ("h3", "a"), ("h3exp", ""), ("trigger", "2"), ("allosemy", "attested")] }

def gr_kolitos : Datum :=
  { id := "marantz2013_gr_kolitos"
    source := ⟨"marantz-2013", "(6a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "kol-i-tos"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "kol"), ("h1", "v0"), ("h1exp", "-i"), ("h2", "ptcp"), ("h2exp", "-t"), ("h3", "a"), ("h3exp", ""), ("trigger", "2"), ("allosemy", "attested")] }

def gr_xtiplitos : Datum :=
  { id := "marantz2013_gr_xtiplitos"
    source := ⟨"marantz-2013", "(6b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "xtipl-i-tos"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "xtip"), ("h1", "v0"), ("h1exp", "-i"), ("h2", "ptcp"), ("h2exp", "-t"), ("h3", "a"), ("h3exp", ""), ("trigger", "2"), ("allosemy", "attested")] }

def gr_xoneftos : Datum :=
  { id := "marantz2013_gr_xoneftos"
    source := ⟨"marantz-2013", "(6c)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "xon-ef-tos"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "xon"), ("h1", "v0"), ("h1exp", "-ef"), ("h2", "ptcp"), ("h2exp", "-t"), ("h3", "a"), ("h3exp", ""), ("trigger", "2"), ("allosemy", "attested")] }

def en_quantized_energy : Datum :=
  { id := "marantz2013_en_quantized_energy"
    source := ⟨"marantz-2013", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "quantized energy"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "QUANTUM"), ("h1", "v0"), ("h1exp", "-ize"), ("h2", "ptcp"), ("h2exp", "-ed"), ("h3", "a"), ("h3exp", ""), ("trigger", "2"), ("allosemy", "attested")] }

def en_pulverized_lime : Datum :=
  { id := "marantz2013_en_pulverized_lime"
    source := ⟨"marantz-2013", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "pulverized lime"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "PULVER"), ("h1", "v0"), ("h1exp", "-ize"), ("h2", "ptcp"), ("h2exp", "-ed"), ("h3", "a"), ("h3exp", ""), ("trigger", "2"), ("allosemy", "attested")] }

def en_atomized_individual : Datum :=
  { id := "marantz2013_en_atomized_individual"
    source := ⟨"marantz-2013", "(7c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "atomized individual"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "ATOM"), ("h1", "v0"), ("h1exp", "-ize"), ("h2", "ptcp"), ("h2exp", "-ed"), ("h3", "a"), ("h3exp", ""), ("trigger", "2"), ("allosemy", "attested")] }

def en_globalized_universe : Datum :=
  { id := "marantz2013_en_globalized_universe"
    source := ⟨"marantz-2013", "(7d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "globalized universe"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "GLOBE"), ("h1", "a"), ("h1exp", "-al"), ("h2", "v"), ("h2exp", "-ize"), ("h3", "ptcp"), ("h3exp", "-ed"), ("h4", "a"), ("h4exp", ""), ("trigger", "3"), ("allosemy", "blocked")] }

def en_nationalized_island : Datum :=
  { id := "marantz2013_en_nationalized_island"
    source := ⟨"marantz-2013", "(7e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "nationalized island"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "NATION"), ("h1", "a"), ("h1exp", "-al"), ("h2", "v"), ("h2exp", "-ize"), ("h3", "ptcp"), ("h3exp", "-ed"), ("h4", "a"), ("h4exp", ""), ("trigger", "3"), ("allosemy", "blocked")] }

def en_fictionalized_account : Datum :=
  { id := "marantz2013_en_fictionalized_account"
    source := ⟨"marantz-2013", "(7f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "fictionalized account"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "FICTION"), ("h1", "a"), ("h1exp", "-al"), ("h2", "v"), ("h2exp", "-ize"), ("h3", "ptcp"), ("h3exp", "-ed"), ("h4", "a"), ("h4exp", ""), ("trigger", "3"), ("allosemy", "blocked")] }

def all : List Datum := [taught, quantized, worker, rotor, rotater, curiosity, gloriousness, house_v, housed_denominal, global, globalize, novelize, novelization, nationalize, jp_koe, jp_nagashi, jp_dashi, jp_sagari, jp_mage, gr_axnistos, gr_koudounistos, gr_magireftos, gr_kolitos, gr_xtiplitos, gr_xoneftos, en_quantized_energy, en_pulverized_lime, en_atomized_individual, en_globalized_universe, en_nationalized_island, en_fictionalized_account]

end Marantz2013.Examples
