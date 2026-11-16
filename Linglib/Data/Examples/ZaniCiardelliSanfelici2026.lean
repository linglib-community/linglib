module

public import Linglib.Data.Examples.Schema

/-!
# `ZaniCiardelliSanfelici2026` — typed example data

Auto-generated from `Linglib/Data/Examples/ZaniCiardelliSanfelici2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ZaniCiardelliSanfelici2026.Examples`.
-/

@[expose] public section

namespace ZaniCiardelliSanfelici2026.Examples

def ex_1a : Datum :=
  { id := "zaniciardellisanfelici2026_1a"
    source := ⟨"zani-ciardelli-sanfelici-2026", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If it rains or snows, the hike will be cancelled."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "indicative"), ("reading", "SDA")] }

def ex_1b : Datum :=
  { id := "zaniciardellisanfelici2026_1b"
    source := ⟨"zani-ciardelli-sanfelici-2026", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If it had rained or snowed, the hike would have been cancelled."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "counterfactual"), ("reading", "SDA")] }

def ex_3 : Datum :=
  { id := "zaniciardellisanfelici2026_3"
    source := ⟨"zani-ciardelli-sanfelici-2026", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Spain had fought either with the Axis or with the Allies in World War II, it would have fought with the Axis."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "counterfactual"), ("reading", "AR"), ("type", "specificational")] }

def ex_4 : Datum :=
  { id := "zaniciardellisanfelici2026_4"
    source := ⟨"zani-ciardelli-sanfelici-2026", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If we had had good weather or the sun had grown cold, we would have had a bumper crop."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "counterfactual"), ("reading", "SDA")] }

def ex_6 : Datum :=
  { id := "zaniciardellisanfelici2026_6"
    source := ⟨"zani-ciardelli-sanfelici-2026", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you press the red button or the blue button, the machine will explode. But I don't remember which."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "indicative"), ("reading", "DCR")] }

def ex_7 : Datum :=
  { id := "zaniciardellisanfelici2026_7"
    source := ⟨"zani-ciardelli-sanfelici-2026", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may have cake or ice-cream."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "free choice")] }

def ex_8 : Datum :=
  { id := "zaniciardellisanfelici2026_8"
    source := ⟨"zani-ciardelli-sanfelici-2026", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The circles are red."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "plural definite homogeneity")] }

def target_ind : Datum :=
  { id := "zaniciardellisanfelici2026_target_ind"
    source := ⟨"zani-ciardelli-sanfelici-2026", "§4 target item, Ind."⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Se lo scoiattolo o la tartaruga vincerà la gara, avrà in premio una nocciola."
    glossedTokens := [("Se", "if"), ("lo", "the"), ("scoiattolo", "squirrel"), ("o", "or"), ("la", "the"), ("tartaruga", "tortoise"), ("vincerà", "win.FUT.3SG"), ("la", "the"), ("gara", "race"), ("avrà", "get.FUT.3SG"), ("in", "as"), ("premio", "prize"), ("una", "a"), ("nocciola", "hazelnut")]
    glossedWords := [⟨['S', 'e'], ['i', 'f'], [⟨['S', 'e'], ['i', 'f'], none⟩]⟩, ⟨['l', 'o'], ['t', 'h', 'e'], [⟨['l', 'o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 'c', 'o', 'i', 'a', 't', 't', 'o', 'l', 'o'], ['s', 'q', 'u', 'i', 'r', 'r', 'e', 'l'], [⟨['s', 'c', 'o', 'i', 'a', 't', 't', 'o', 'l', 'o'], ['s', 'q', 'u', 'i', 'r', 'r', 'e', 'l'], none⟩]⟩, ⟨['o'], ['o', 'r'], [⟨['o'], ['o', 'r'], none⟩]⟩, ⟨['l', 'a'], ['t', 'h', 'e'], [⟨['l', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'a', 'r', 't', 'a', 'r', 'u', 'g', 'a'], ['t', 'o', 'r', 't', 'o', 'i', 's', 'e'], [⟨['t', 'a', 'r', 't', 'a', 'r', 'u', 'g', 'a'], ['t', 'o', 'r', 't', 'o', 'i', 's', 'e'], none⟩]⟩, ⟨['v', 'i', 'n', 'c', 'e', 'r', 'à'], ['w', 'i', 'n', '.', 'F', 'U', 'T', '.', '3', 'S', 'G'], [⟨['v', 'i', 'n', 'c', 'e', 'r', 'à'], ['w', 'i', 'n', '.', 'F', 'U', 'T', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['l', 'a'], ['t', 'h', 'e'], [⟨['l', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'a', 'r', 'a'], ['r', 'a', 'c', 'e'], [⟨['g', 'a', 'r', 'a'], ['r', 'a', 'c', 'e'], none⟩]⟩, ⟨['a', 'v', 'r', 'à'], ['g', 'e', 't', '.', 'F', 'U', 'T', '.', '3', 'S', 'G'], [⟨['a', 'v', 'r', 'à'], ['g', 'e', 't', '.', 'F', 'U', 'T', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['i', 'n'], ['a', 's'], [⟨['i', 'n'], ['a', 's'], none⟩]⟩, ⟨['p', 'r', 'e', 'm', 'i', 'o'], ['p', 'r', 'i', 'z', 'e'], [⟨['p', 'r', 'e', 'm', 'i', 'o'], ['p', 'r', 'i', 'z', 'e'], none⟩]⟩, ⟨['u', 'n', 'a'], ['a'], [⟨['u', 'n', 'a'], ['a'], none⟩]⟩, ⟨['n', 'o', 'c', 'c', 'i', 'o', 'l', 'a'], ['h', 'a', 'z', 'e', 'l', 'n', 'u', 't'], [⟨['n', 'o', 'c', 'c', 'i', 'o', 'l', 'a'], ['h', 'a', 'z', 'e', 'l', 'n', 'u', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "indicative"), ("item", "target"), ("schema", "(9a)")] }

def target_ctf : Datum :=
  { id := "zaniciardellisanfelici2026_target_ctf"
    source := ⟨"zani-ciardelli-sanfelici-2026", "§4 target item, Ctf."⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Se lo scoiattolo o la tartaruga avesse vinto la gara, avrebbe avuto in premio una nocciola."
    glossedTokens := [("Se", "if"), ("lo", "the"), ("scoiattolo", "squirrel"), ("o", "or"), ("la", "the"), ("tartaruga", "tortoise"), ("avesse", "have.SBJV.IPFV.3SG"), ("vinto", "win.PTCP.PST"), ("la", "the"), ("gara", "race"), ("avrebbe", "have.COND.3SG"), ("avuto", "get.PTCP.PST"), ("in", "as"), ("premio", "prize"), ("una", "a"), ("nocciola", "hazelnut")]
    glossedWords := [⟨['S', 'e'], ['i', 'f'], [⟨['S', 'e'], ['i', 'f'], none⟩]⟩, ⟨['l', 'o'], ['t', 'h', 'e'], [⟨['l', 'o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 'c', 'o', 'i', 'a', 't', 't', 'o', 'l', 'o'], ['s', 'q', 'u', 'i', 'r', 'r', 'e', 'l'], [⟨['s', 'c', 'o', 'i', 'a', 't', 't', 'o', 'l', 'o'], ['s', 'q', 'u', 'i', 'r', 'r', 'e', 'l'], none⟩]⟩, ⟨['o'], ['o', 'r'], [⟨['o'], ['o', 'r'], none⟩]⟩, ⟨['l', 'a'], ['t', 'h', 'e'], [⟨['l', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'a', 'r', 't', 'a', 'r', 'u', 'g', 'a'], ['t', 'o', 'r', 't', 'o', 'i', 's', 'e'], [⟨['t', 'a', 'r', 't', 'a', 'r', 'u', 'g', 'a'], ['t', 'o', 'r', 't', 'o', 'i', 's', 'e'], none⟩]⟩, ⟨['a', 'v', 'e', 's', 's', 'e'], ['h', 'a', 'v', 'e', '.', 'S', 'B', 'J', 'V', '.', 'I', 'P', 'F', 'V', '.', '3', 'S', 'G'], [⟨['a', 'v', 'e', 's', 's', 'e'], ['h', 'a', 'v', 'e', '.', 'S', 'B', 'J', 'V', '.', 'I', 'P', 'F', 'V', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['v', 'i', 'n', 't', 'o'], ['w', 'i', 'n', '.', 'P', 'T', 'C', 'P', '.', 'P', 'S', 'T'], [⟨['v', 'i', 'n', 't', 'o'], ['w', 'i', 'n', '.', 'P', 'T', 'C', 'P', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['l', 'a'], ['t', 'h', 'e'], [⟨['l', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'a', 'r', 'a'], ['r', 'a', 'c', 'e'], [⟨['g', 'a', 'r', 'a'], ['r', 'a', 'c', 'e'], none⟩]⟩, ⟨['a', 'v', 'r', 'e', 'b', 'b', 'e'], ['h', 'a', 'v', 'e', '.', 'C', 'O', 'N', 'D', '.', '3', 'S', 'G'], [⟨['a', 'v', 'r', 'e', 'b', 'b', 'e'], ['h', 'a', 'v', 'e', '.', 'C', 'O', 'N', 'D', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['a', 'v', 'u', 't', 'o'], ['g', 'e', 't', '.', 'P', 'T', 'C', 'P', '.', 'P', 'S', 'T'], [⟨['a', 'v', 'u', 't', 'o'], ['g', 'e', 't', '.', 'P', 'T', 'C', 'P', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['i', 'n'], ['a', 's'], [⟨['i', 'n'], ['a', 's'], none⟩]⟩, ⟨['p', 'r', 'e', 'm', 'i', 'o'], ['p', 'r', 'i', 'z', 'e'], [⟨['p', 'r', 'e', 'm', 'i', 'o'], ['p', 'r', 'i', 'z', 'e'], none⟩]⟩, ⟨['u', 'n', 'a'], ['a'], [⟨['u', 'n', 'a'], ['a'], none⟩]⟩, ⟨['n', 'o', 'c', 'c', 'i', 'o', 'l', 'a'], ['h', 'a', 'z', 'e', 'l', 'n', 'u', 't'], [⟨['n', 'o', 'c', 'c', 'i', 'o', 'l', 'a'], ['h', 'a', 'z', 'e', 'l', 'n', 'u', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "counterfactual"), ("item", "target"), ("schema", "(9a)")] }

def control_ind : Datum :=
  { id := "zaniciardellisanfelici2026_control_ind"
    source := ⟨"zani-ciardelli-sanfelici-2026", "§4 control item, Ind."⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Se lo scoiattolo vincerà la gara, avrà in premio una nocciola."
    glossedTokens := [("Se", "if"), ("lo", "the"), ("scoiattolo", "squirrel"), ("vincerà", "win.FUT.3SG"), ("la", "the"), ("gara", "race"), ("avrà", "get.FUT.3SG"), ("in", "as"), ("premio", "prize"), ("una", "a"), ("nocciola", "hazelnut")]
    glossedWords := [⟨['S', 'e'], ['i', 'f'], [⟨['S', 'e'], ['i', 'f'], none⟩]⟩, ⟨['l', 'o'], ['t', 'h', 'e'], [⟨['l', 'o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 'c', 'o', 'i', 'a', 't', 't', 'o', 'l', 'o'], ['s', 'q', 'u', 'i', 'r', 'r', 'e', 'l'], [⟨['s', 'c', 'o', 'i', 'a', 't', 't', 'o', 'l', 'o'], ['s', 'q', 'u', 'i', 'r', 'r', 'e', 'l'], none⟩]⟩, ⟨['v', 'i', 'n', 'c', 'e', 'r', 'à'], ['w', 'i', 'n', '.', 'F', 'U', 'T', '.', '3', 'S', 'G'], [⟨['v', 'i', 'n', 'c', 'e', 'r', 'à'], ['w', 'i', 'n', '.', 'F', 'U', 'T', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['l', 'a'], ['t', 'h', 'e'], [⟨['l', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'a', 'r', 'a'], ['r', 'a', 'c', 'e'], [⟨['g', 'a', 'r', 'a'], ['r', 'a', 'c', 'e'], none⟩]⟩, ⟨['a', 'v', 'r', 'à'], ['g', 'e', 't', '.', 'F', 'U', 'T', '.', '3', 'S', 'G'], [⟨['a', 'v', 'r', 'à'], ['g', 'e', 't', '.', 'F', 'U', 'T', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['i', 'n'], ['a', 's'], [⟨['i', 'n'], ['a', 's'], none⟩]⟩, ⟨['p', 'r', 'e', 'm', 'i', 'o'], ['p', 'r', 'i', 'z', 'e'], [⟨['p', 'r', 'e', 'm', 'i', 'o'], ['p', 'r', 'i', 'z', 'e'], none⟩]⟩, ⟨['u', 'n', 'a'], ['a'], [⟨['u', 'n', 'a'], ['a'], none⟩]⟩, ⟨['n', 'o', 'c', 'c', 'i', 'o', 'l', 'a'], ['h', 'a', 'z', 'e', 'l', 'n', 'u', 't'], [⟨['n', 'o', 'c', 'c', 'i', 'o', 'l', 'a'], ['h', 'a', 'z', 'e', 'l', 'n', 'u', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "indicative"), ("item", "control"), ("expected", "true")] }

def control_ctf : Datum :=
  { id := "zaniciardellisanfelici2026_control_ctf"
    source := ⟨"zani-ciardelli-sanfelici-2026", "§4 control item, Ctf."⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Se lo scoiattolo avesse vinto la gara, avrebbe avuto in premio una nocciola."
    glossedTokens := [("Se", "if"), ("lo", "the"), ("scoiattolo", "squirrel"), ("avesse", "have.SBJV.IPFV.3SG"), ("vinto", "win.PTCP.PST"), ("la", "the"), ("gara", "race"), ("avrebbe", "have.COND.3SG"), ("avuto", "get.PTCP.PST"), ("in", "as"), ("premio", "prize"), ("una", "a"), ("nocciola", "hazelnut")]
    glossedWords := [⟨['S', 'e'], ['i', 'f'], [⟨['S', 'e'], ['i', 'f'], none⟩]⟩, ⟨['l', 'o'], ['t', 'h', 'e'], [⟨['l', 'o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 'c', 'o', 'i', 'a', 't', 't', 'o', 'l', 'o'], ['s', 'q', 'u', 'i', 'r', 'r', 'e', 'l'], [⟨['s', 'c', 'o', 'i', 'a', 't', 't', 'o', 'l', 'o'], ['s', 'q', 'u', 'i', 'r', 'r', 'e', 'l'], none⟩]⟩, ⟨['a', 'v', 'e', 's', 's', 'e'], ['h', 'a', 'v', 'e', '.', 'S', 'B', 'J', 'V', '.', 'I', 'P', 'F', 'V', '.', '3', 'S', 'G'], [⟨['a', 'v', 'e', 's', 's', 'e'], ['h', 'a', 'v', 'e', '.', 'S', 'B', 'J', 'V', '.', 'I', 'P', 'F', 'V', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['v', 'i', 'n', 't', 'o'], ['w', 'i', 'n', '.', 'P', 'T', 'C', 'P', '.', 'P', 'S', 'T'], [⟨['v', 'i', 'n', 't', 'o'], ['w', 'i', 'n', '.', 'P', 'T', 'C', 'P', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['l', 'a'], ['t', 'h', 'e'], [⟨['l', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'a', 'r', 'a'], ['r', 'a', 'c', 'e'], [⟨['g', 'a', 'r', 'a'], ['r', 'a', 'c', 'e'], none⟩]⟩, ⟨['a', 'v', 'r', 'e', 'b', 'b', 'e'], ['h', 'a', 'v', 'e', '.', 'C', 'O', 'N', 'D', '.', '3', 'S', 'G'], [⟨['a', 'v', 'r', 'e', 'b', 'b', 'e'], ['h', 'a', 'v', 'e', '.', 'C', 'O', 'N', 'D', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['a', 'v', 'u', 't', 'o'], ['g', 'e', 't', '.', 'P', 'T', 'C', 'P', '.', 'P', 'S', 'T'], [⟨['a', 'v', 'u', 't', 'o'], ['g', 'e', 't', '.', 'P', 'T', 'C', 'P', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['i', 'n'], ['a', 's'], [⟨['i', 'n'], ['a', 's'], none⟩]⟩, ⟨['p', 'r', 'e', 'm', 'i', 'o'], ['p', 'r', 'i', 'z', 'e'], [⟨['p', 'r', 'e', 'm', 'i', 'o'], ['p', 'r', 'i', 'z', 'e'], none⟩]⟩, ⟨['u', 'n', 'a'], ['a'], [⟨['u', 'n', 'a'], ['a'], none⟩]⟩, ⟨['n', 'o', 'c', 'c', 'i', 'o', 'l', 'a'], ['h', 'a', 'z', 'e', 'l', 'n', 'u', 't'], [⟨['n', 'o', 'c', 'c', 'i', 'o', 'l', 'a'], ['h', 'a', 'z', 'e', 'l', 'n', 'u', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "counterfactual"), ("item", "control"), ("expected", "true")] }

def closeness_ind : Datum :=
  { id := "zaniciardellisanfelici2026_closeness_ind"
    source := ⟨"zani-ciardelli-sanfelici-2026", "§4 closeness evaluation item, Ind."⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Se non vincerà la lepre, vincerà lo scoiattolo."
    glossedTokens := [("Se", "if"), ("non", "NEG"), ("vincerà", "win.FUT.3SG"), ("la", "the"), ("lepre", "hare"), ("vincerà", "win.FUT.3SG"), ("lo", "the"), ("scoiattolo", "squirrel")]
    glossedWords := [⟨['S', 'e'], ['i', 'f'], [⟨['S', 'e'], ['i', 'f'], none⟩]⟩, ⟨['n', 'o', 'n'], ['N', 'E', 'G'], [⟨['n', 'o', 'n'], ['N', 'E', 'G'], none⟩]⟩, ⟨['v', 'i', 'n', 'c', 'e', 'r', 'à'], ['w', 'i', 'n', '.', 'F', 'U', 'T', '.', '3', 'S', 'G'], [⟨['v', 'i', 'n', 'c', 'e', 'r', 'à'], ['w', 'i', 'n', '.', 'F', 'U', 'T', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['l', 'a'], ['t', 'h', 'e'], [⟨['l', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['l', 'e', 'p', 'r', 'e'], ['h', 'a', 'r', 'e'], [⟨['l', 'e', 'p', 'r', 'e'], ['h', 'a', 'r', 'e'], none⟩]⟩, ⟨['v', 'i', 'n', 'c', 'e', 'r', 'à'], ['w', 'i', 'n', '.', 'F', 'U', 'T', '.', '3', 'S', 'G'], [⟨['v', 'i', 'n', 'c', 'e', 'r', 'à'], ['w', 'i', 'n', '.', 'F', 'U', 'T', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['l', 'o'], ['t', 'h', 'e'], [⟨['l', 'o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 'c', 'o', 'i', 'a', 't', 't', 'o', 'l', 'o'], ['s', 'q', 'u', 'i', 'r', 'r', 'e', 'l'], [⟨['s', 'c', 'o', 'i', 'a', 't', 't', 'o', 'l', 'o'], ['s', 'q', 'u', 'i', 'r', 'r', 'e', 'l'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "indicative"), ("item", "closeness evaluation")] }

def closeness_ctf : Datum :=
  { id := "zaniciardellisanfelici2026_closeness_ctf"
    source := ⟨"zani-ciardelli-sanfelici-2026", "§4 closeness evaluation item, Ctf."⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Se non avesse vinto la lepre, avrebbe vinto lo scoiattolo."
    glossedTokens := [("Se", "if"), ("non", "NEG"), ("avesse", "have.SBJV.IPFV.3SG"), ("vinto", "win.PTCP.PST"), ("la", "the"), ("lepre", "hare"), ("avrebbe", "have.COND.3SG"), ("vinto", "win.PTCP.PST"), ("lo", "the"), ("scoiattolo", "squirrel")]
    glossedWords := [⟨['S', 'e'], ['i', 'f'], [⟨['S', 'e'], ['i', 'f'], none⟩]⟩, ⟨['n', 'o', 'n'], ['N', 'E', 'G'], [⟨['n', 'o', 'n'], ['N', 'E', 'G'], none⟩]⟩, ⟨['a', 'v', 'e', 's', 's', 'e'], ['h', 'a', 'v', 'e', '.', 'S', 'B', 'J', 'V', '.', 'I', 'P', 'F', 'V', '.', '3', 'S', 'G'], [⟨['a', 'v', 'e', 's', 's', 'e'], ['h', 'a', 'v', 'e', '.', 'S', 'B', 'J', 'V', '.', 'I', 'P', 'F', 'V', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['v', 'i', 'n', 't', 'o'], ['w', 'i', 'n', '.', 'P', 'T', 'C', 'P', '.', 'P', 'S', 'T'], [⟨['v', 'i', 'n', 't', 'o'], ['w', 'i', 'n', '.', 'P', 'T', 'C', 'P', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['l', 'a'], ['t', 'h', 'e'], [⟨['l', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['l', 'e', 'p', 'r', 'e'], ['h', 'a', 'r', 'e'], [⟨['l', 'e', 'p', 'r', 'e'], ['h', 'a', 'r', 'e'], none⟩]⟩, ⟨['a', 'v', 'r', 'e', 'b', 'b', 'e'], ['h', 'a', 'v', 'e', '.', 'C', 'O', 'N', 'D', '.', '3', 'S', 'G'], [⟨['a', 'v', 'r', 'e', 'b', 'b', 'e'], ['h', 'a', 'v', 'e', '.', 'C', 'O', 'N', 'D', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['v', 'i', 'n', 't', 'o'], ['w', 'i', 'n', '.', 'P', 'T', 'C', 'P', '.', 'P', 'S', 'T'], [⟨['v', 'i', 'n', 't', 'o'], ['w', 'i', 'n', '.', 'P', 'T', 'C', 'P', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['l', 'o'], ['t', 'h', 'e'], [⟨['l', 'o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 'c', 'o', 'i', 'a', 't', 't', 'o', 'l', 'o'], ['s', 'q', 'u', 'i', 'r', 'r', 'e', 'l'], [⟨['s', 'c', 'o', 'i', 'a', 't', 't', 'o', 'l', 'o'], ['s', 'q', 'u', 'i', 'r', 'r', 'e', 'l'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "counterfactual"), ("item", "closeness evaluation")] }

def app_1 : Datum :=
  { id := "zaniciardellisanfelici2026_app_1"
    source := ⟨"zani-ciardelli-sanfelici-2026", "§6 (1)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Se il tasto rosso o il tasto blu viene premuto, il computer esplode. Non mi ricordo quale dei due."
    glossedTokens := [("Se", "if"), ("il", "the"), ("tasto", "key"), ("rosso", "red"), ("o", "or"), ("il", "the"), ("tasto", "key"), ("blu", "blue"), ("viene", "come.3SG"), ("premuto", "pressed.PTCP.SG"), ("il", "the"), ("computer", "computer"), ("esplode", "explodes.3SG"), ("Non", "not"), ("mi", "CL.1SG"), ("ricordo", "remember.1SG"), ("quale", "which"), ("dei", "of.the"), ("due", "two")]
    glossedWords := [⟨['S', 'e'], ['i', 'f'], [⟨['S', 'e'], ['i', 'f'], none⟩]⟩, ⟨['i', 'l'], ['t', 'h', 'e'], [⟨['i', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'a', 's', 't', 'o'], ['k', 'e', 'y'], [⟨['t', 'a', 's', 't', 'o'], ['k', 'e', 'y'], none⟩]⟩, ⟨['r', 'o', 's', 's', 'o'], ['r', 'e', 'd'], [⟨['r', 'o', 's', 's', 'o'], ['r', 'e', 'd'], none⟩]⟩, ⟨['o'], ['o', 'r'], [⟨['o'], ['o', 'r'], none⟩]⟩, ⟨['i', 'l'], ['t', 'h', 'e'], [⟨['i', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'a', 's', 't', 'o'], ['k', 'e', 'y'], [⟨['t', 'a', 's', 't', 'o'], ['k', 'e', 'y'], none⟩]⟩, ⟨['b', 'l', 'u'], ['b', 'l', 'u', 'e'], [⟨['b', 'l', 'u'], ['b', 'l', 'u', 'e'], none⟩]⟩, ⟨['v', 'i', 'e', 'n', 'e'], ['c', 'o', 'm', 'e', '.', '3', 'S', 'G'], [⟨['v', 'i', 'e', 'n', 'e'], ['c', 'o', 'm', 'e', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['p', 'r', 'e', 'm', 'u', 't', 'o'], ['p', 'r', 'e', 's', 's', 'e', 'd', '.', 'P', 'T', 'C', 'P', '.', 'S', 'G'], [⟨['p', 'r', 'e', 'm', 'u', 't', 'o'], ['p', 'r', 'e', 's', 's', 'e', 'd', '.', 'P', 'T', 'C', 'P', '.', 'S', 'G'], none⟩]⟩, ⟨['i', 'l'], ['t', 'h', 'e'], [⟨['i', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['c', 'o', 'm', 'p', 'u', 't', 'e', 'r'], ['c', 'o', 'm', 'p', 'u', 't', 'e', 'r'], [⟨['c', 'o', 'm', 'p', 'u', 't', 'e', 'r'], ['c', 'o', 'm', 'p', 'u', 't', 'e', 'r'], none⟩]⟩, ⟨['e', 's', 'p', 'l', 'o', 'd', 'e'], ['e', 'x', 'p', 'l', 'o', 'd', 'e', 's', '.', '3', 'S', 'G'], [⟨['e', 's', 'p', 'l', 'o', 'd', 'e'], ['e', 'x', 'p', 'l', 'o', 'd', 'e', 's', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['N', 'o', 'n'], ['n', 'o', 't'], [⟨['N', 'o', 'n'], ['n', 'o', 't'], none⟩]⟩, ⟨['m', 'i'], ['C', 'L', '.', '1', 'S', 'G'], [⟨['m', 'i'], ['C', 'L', '.', '1', 'S', 'G'], none⟩]⟩, ⟨['r', 'i', 'c', 'o', 'r', 'd', 'o'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r', '.', '1', 'S', 'G'], [⟨['r', 'i', 'c', 'o', 'r', 'd', 'o'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r', '.', '1', 'S', 'G'], none⟩]⟩, ⟨['q', 'u', 'a', 'l', 'e'], ['w', 'h', 'i', 'c', 'h'], [⟨['q', 'u', 'a', 'l', 'e'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['d', 'e', 'i'], ['o', 'f', '.', 't', 'h', 'e'], [⟨['d', 'e', 'i'], ['o', 'f', '.', 't', 'h', 'e'], none⟩]⟩, ⟨['d', 'u', 'e'], ['t', 'w', 'o'], [⟨['d', 'u', 'e'], ['t', 'w', 'o'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agreement", "singular"), ("reading", "DCR")] }

def app_2 : Datum :=
  { id := "zaniciardellisanfelici2026_app_2"
    source := ⟨"zani-ciardelli-sanfelici-2026", "§6 (2)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Se il tasto rosso o il tasto blu vengono premuti, il computer esplode. Non mi ricordo quale dei due."
    glossedTokens := [("Se", "if"), ("il", "the"), ("tasto", "key"), ("rosso", "red"), ("o", "or"), ("il", "the"), ("tasto", "key"), ("blu", "blue"), ("vengono", "come.3PL"), ("premuti", "pressed.PTCP.PL"), ("il", "the"), ("computer", "computer"), ("esplode", "explodes.3SG"), ("Non", "not"), ("mi", "CL.1SG"), ("ricordo", "remember.1SG"), ("quale", "which"), ("dei", "of.the"), ("due", "two")]
    glossedWords := [⟨['S', 'e'], ['i', 'f'], [⟨['S', 'e'], ['i', 'f'], none⟩]⟩, ⟨['i', 'l'], ['t', 'h', 'e'], [⟨['i', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'a', 's', 't', 'o'], ['k', 'e', 'y'], [⟨['t', 'a', 's', 't', 'o'], ['k', 'e', 'y'], none⟩]⟩, ⟨['r', 'o', 's', 's', 'o'], ['r', 'e', 'd'], [⟨['r', 'o', 's', 's', 'o'], ['r', 'e', 'd'], none⟩]⟩, ⟨['o'], ['o', 'r'], [⟨['o'], ['o', 'r'], none⟩]⟩, ⟨['i', 'l'], ['t', 'h', 'e'], [⟨['i', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'a', 's', 't', 'o'], ['k', 'e', 'y'], [⟨['t', 'a', 's', 't', 'o'], ['k', 'e', 'y'], none⟩]⟩, ⟨['b', 'l', 'u'], ['b', 'l', 'u', 'e'], [⟨['b', 'l', 'u'], ['b', 'l', 'u', 'e'], none⟩]⟩, ⟨['v', 'e', 'n', 'g', 'o', 'n', 'o'], ['c', 'o', 'm', 'e', '.', '3', 'P', 'L'], [⟨['v', 'e', 'n', 'g', 'o', 'n', 'o'], ['c', 'o', 'm', 'e', '.', '3', 'P', 'L'], none⟩]⟩, ⟨['p', 'r', 'e', 'm', 'u', 't', 'i'], ['p', 'r', 'e', 's', 's', 'e', 'd', '.', 'P', 'T', 'C', 'P', '.', 'P', 'L'], [⟨['p', 'r', 'e', 'm', 'u', 't', 'i'], ['p', 'r', 'e', 's', 's', 'e', 'd', '.', 'P', 'T', 'C', 'P', '.', 'P', 'L'], none⟩]⟩, ⟨['i', 'l'], ['t', 'h', 'e'], [⟨['i', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['c', 'o', 'm', 'p', 'u', 't', 'e', 'r'], ['c', 'o', 'm', 'p', 'u', 't', 'e', 'r'], [⟨['c', 'o', 'm', 'p', 'u', 't', 'e', 'r'], ['c', 'o', 'm', 'p', 'u', 't', 'e', 'r'], none⟩]⟩, ⟨['e', 's', 'p', 'l', 'o', 'd', 'e'], ['e', 'x', 'p', 'l', 'o', 'd', 'e', 's', '.', '3', 'S', 'G'], [⟨['e', 's', 'p', 'l', 'o', 'd', 'e'], ['e', 'x', 'p', 'l', 'o', 'd', 'e', 's', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['N', 'o', 'n'], ['n', 'o', 't'], [⟨['N', 'o', 'n'], ['n', 'o', 't'], none⟩]⟩, ⟨['m', 'i'], ['C', 'L', '.', '1', 'S', 'G'], [⟨['m', 'i'], ['C', 'L', '.', '1', 'S', 'G'], none⟩]⟩, ⟨['r', 'i', 'c', 'o', 'r', 'd', 'o'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r', '.', '1', 'S', 'G'], [⟨['r', 'i', 'c', 'o', 'r', 'd', 'o'], ['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r', '.', '1', 'S', 'G'], none⟩]⟩, ⟨['q', 'u', 'a', 'l', 'e'], ['w', 'h', 'i', 'c', 'h'], [⟨['q', 'u', 'a', 'l', 'e'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['d', 'e', 'i'], ['o', 'f', '.', 't', 'h', 'e'], [⟨['d', 'e', 'i'], ['o', 'f', '.', 't', 'h', 'e'], none⟩]⟩, ⟨['d', 'u', 'e'], ['t', 'w', 'o'], [⟨['d', 'u', 'e'], ['t', 'w', 'o'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("agreement", "plural"), ("reading", "DCR")] }

def all : List Datum := [ex_1a, ex_1b, ex_3, ex_4, ex_6, ex_7, ex_8, target_ind, target_ctf, control_ind, control_ctf, closeness_ind, closeness_ctf, app_1, app_2]

end ZaniCiardelliSanfelici2026.Examples
