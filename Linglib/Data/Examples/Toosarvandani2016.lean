module

public import Linglib.Data.Examples.Schema

/-!
# `Toosarvandani2016` — typed example data

Auto-generated from `Linglib/Data/Examples/Toosarvandani2016.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Toosarvandani2016.Examples`.
-/

@[expose] public section

namespace Toosarvandani2016.Examples

def ex_39a : Datum :=
  { id := "toosarvandani2016_39a"
    source := ⟨"toosarvandani-2016", "(39a)"⟩
    reportedIn := none
    language := "nort2954"
    primaryText := "Su=tɨɨtsi-’yu naatsi’i nabagia-wɨnnɨ-na, su=ddoogga u=bbuni-katɨ."
    glossedTokens := [("Su=tɨɨtsi-’yu", "NOM=little-NOM"), ("naatsi’i", "boy"), ("nabagia-wɨnnɨ-na", "bathe-PROG-SIM"), ("su=ddoogga", "NOM=dog"), ("u=bbuni-katɨ", "3SG.ACC=see-sit.IPFV")]
    context := "The boy is bathing. The dog is sitting and looking at him in the bathtub."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "sim"), ("aspect", "prog"), ("markedEvent", "bathe"), ("unmarkedAspect", "ipfv"), ("unmarkedEvent", "watch")] }

def ex_39b : Datum :=
  { id := "toosarvandani2016_39b"
    source := ⟨"toosarvandani-2016", "(39b)"⟩
    reportedIn := none
    language := "nort2954"
    primaryText := "Su=tɨɨtsi-’yu naatsi’i nabagia-hu-si, su=ddoogga u=bbuni-katɨ."
    glossedTokens := [("Su=tɨɨtsi-’yu", "NOM=little-NOM"), ("naatsi’i", "boy"), ("nabagia-hu-si", "bathe-PFV-SEQ"), ("su=ddoogga", "NOM=dog"), ("u=bbuni-katɨ", "3SG.ACC=see-sit.IPFV")]
    context := "The boy is bathing. The dog is sitting and looking at him in the bathtub."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "seq"), ("aspect", "pfv"), ("markedEvent", "bathe"), ("unmarkedAspect", "ipfv"), ("unmarkedEvent", "watch")] }

def ex_40b : Datum :=
  { id := "toosarvandani2016_40b"
    source := ⟨"toosarvandani-2016", "(40b)"⟩
    reportedIn := none
    language := "nort2954"
    primaryText := "Su=naatsi’i tɨ=kaadzi madabbui-wɨnnɨ-na, yaisi hubiadu-wɨnnɨ."
    glossedTokens := [("Su=naatsi’i", "NOM=boy"), ("tɨ=kaadzi", "REFL=car"), ("madabbui-wɨnnɨ-na", "fix-PROG-SIM"), ("yaisi", "PTC"), ("hubiadu-wɨnnɨ", "sing-PROG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "sim"), ("aspect", "prog")] }

def ex_40c : Datum :=
  { id := "toosarvandani2016_40c"
    source := ⟨"toosarvandani-2016", "(40c)"⟩
    reportedIn := none
    language := "nort2954"
    primaryText := "Su=nana tɨ=kaadzi madabbui-hu-na, yaisi hubiadu-wɨnnɨ."
    glossedTokens := [("Su=nana", "NOM=man"), ("tɨ=kaadzi", "REFL=car"), ("madabbui-hu-na", "fix-PFV-SIM"), ("yaisi", "PTC"), ("hubiadu-wɨnnɨ", "sing-PROG")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "sim"), ("aspect", "pfv")] }

def ex_47a : Datum :=
  { id := "toosarvandani2016_47a"
    source := ⟨"toosarvandani-2016", "(47a)"⟩
    reportedIn := none
    language := "nort2954"
    primaryText := "Su=naatsi’i tɨbuni-hu-si, tɨ=pa’mogo yaa-hu."
    glossedTokens := [("Su=naatsi’i", "NOM=boy"), ("tɨbuni-hu-si", "wake.up-PFV-SEQ"), ("tɨ=pa’mogo", "REFL=frog"), ("yaa-hu", "miss-PFV")]
    context := "While the boy is asleep, the frog escapes. After the boy wakes up, he notices the frog is gone."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "seq"), ("aspect", "pfv"), ("markedEvent", "wakeUp"), ("unmarkedAspect", "pfv"), ("unmarkedEvent", "miss")] }

def ex_47b : Datum :=
  { id := "toosarvandani2016_47b"
    source := ⟨"toosarvandani-2016", "(47b)"⟩
    reportedIn := none
    language := "nort2954"
    primaryText := "Su=naatsi’i tɨbuni-wɨnnɨ-na, tɨ=pa’mogo yaa-hu."
    glossedTokens := [("Su=naatsi’i", "NOM=boy"), ("tɨbuni-wɨnnɨ-na", "wake.up-PROG-SIM"), ("tɨ=pa’mogo", "REFL=frog"), ("yaa-hu", "miss-PFV")]
    context := "While the boy is asleep, the frog escapes. After the boy wakes up, he notices the frog is gone."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "sim"), ("aspect", "prog"), ("markedEvent", "wakeUp"), ("unmarkedAspect", "pfv"), ("unmarkedEvent", "miss")] }

def ex_66a : Datum :=
  { id := "toosarvandani2016_66a"
    source := ⟨"toosarvandani-2016", "(66a)"⟩
    reportedIn := none
    language := "nort2954"
    primaryText := "Su=pa’mogo wadzi-mia-hu-si, yaisi su=naatsi’i tɨbuni-hu."
    glossedTokens := [("Su=pa’mogo", "NOM=frog"), ("wadzi-mia-hu-si", "hide-go-PFV-SEQ"), ("yaisi", "PTC"), ("su=naatsi’i", "NOM=boy"), ("tɨbuni-hu", "wake.up-PFV")]
    context := "While the boy is asleep, the frog escapes. After the boy wakes up, he notices the frog is gone."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "seq"), ("aspect", "pfv"), ("markedEvent", "escape"), ("unmarkedAspect", "pfv"), ("unmarkedEvent", "wakeUp")] }

def ex_66b : Datum :=
  { id := "toosarvandani2016_66b"
    source := ⟨"toosarvandani-2016", "(66b)"⟩
    reportedIn := none
    language := "nort2954"
    primaryText := "Su=naatsi’i tɨbuni-hu, su=tɨɨtsi-’yu pa’mogo wadzi-mia-hu-si."
    glossedTokens := [("Su=naatsi’i", "NOM=boy"), ("tɨbuni-hu", "wake.up-PFV"), ("su=tɨɨtsi-’yu", "NOM=little-NOM"), ("pa’mogo", "frog"), ("wadzi-mia-hu-si", "hide-go-PFV-SEQ")]
    context := "While the boy is asleep, the frog escapes. After the boy wakes up, he notices the frog is gone."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "seq"), ("aspect", "pfv"), ("markedEvent", "escape"), ("unmarkedAspect", "pfv"), ("unmarkedEvent", "wakeUp")] }

def ex_66c : Datum :=
  { id := "toosarvandani2016_66c"
    source := ⟨"toosarvandani-2016", "(66c)"⟩
    reportedIn := none
    language := "nort2954"
    primaryText := "Su=naatsi’i tɨbuni-hu-si, su=pa’mogo wadzi-mia-hu."
    glossedTokens := [("Su=naatsi’i", "NOM=boy"), ("tɨbuni-hu-si", "wake.up-PFV-SEQ"), ("su=pa’mogo", "NOM=frog"), ("wadzi-mia-hu", "hide-go-PFV")]
    context := "While the boy is asleep, the frog escapes. After the boy wakes up, he notices the frog is gone."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "seq"), ("aspect", "pfv"), ("markedEvent", "wakeUp"), ("unmarkedAspect", "pfv"), ("unmarkedEvent", "escape")] }

def ex_66d : Datum :=
  { id := "toosarvandani2016_66d"
    source := ⟨"toosarvandani-2016", "(66d)"⟩
    reportedIn := none
    language := "nort2954"
    primaryText := "Su=pa’mogo wadzi-mia-hu, su=tɨɨtsi-’yu naatsi’i tɨbuni-hu-si."
    glossedTokens := [("Su=pa’mogo", "NOM=frog"), ("wadzi-mia-hu", "hide-go-PFV"), ("su=tɨɨtsi-’yu", "NOM=little-NOM"), ("naatsi’i", "boy"), ("tɨbuni-hu-si", "wake.up-PFV-SEQ")]
    context := "While the boy is asleep, the frog escapes. After the boy wakes up, he notices the frog is gone."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "seq"), ("aspect", "pfv"), ("markedEvent", "wakeUp"), ("unmarkedAspect", "pfv"), ("unmarkedEvent", "escape")] }

def ex_71a : Datum :=
  { id := "toosarvandani2016_71a"
    source := ⟨"toosarvandani-2016", "(71a)"⟩
    reportedIn := none
    language := "nort2954"
    primaryText := "Su=naatsi’i ti’atia-hu-si, su=tsɨa’a nɨga-hu-si, su=mogo’ni nobi-ggwe iga-hu."
    glossedTokens := [("Su=naatsi’i", "NOM=boy"), ("ti’atia-hu-si", "play-PFV-SEQ"), ("su=tsɨa’a", "NOM=girl"), ("nɨga-hu-si", "dance-PFV-SEQ"), ("su=mogo’ni", "NOM=woman"), ("nobi-ggwe", "house-LOC"), ("iga-hu", "enter-PFV")]
    context := "The boy and girl are at home. Instead of studying, he is playing and she is dancing at the same time. They both stop before their mother comes home."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "seq"), ("aspect", "pfv"), ("markedEvent", "play"), ("markedEvent", "dance"), ("unmarkedAspect", "pfv"), ("unmarkedEvent", "enter")] }

def ex_71b : Datum :=
  { id := "toosarvandani2016_71b"
    source := ⟨"toosarvandani-2016", "(71b)"⟩
    reportedIn := none
    language := "nort2954"
    primaryText := "Su=tsɨa’a nɨga-hu-si, su=naatsi’i ti’atia-hu-si, su=mogo’ni nobi-ggwe iga-hu."
    glossedTokens := [("Su=tsɨa’a", "NOM=girl"), ("nɨga-hu-si", "dance-PFV-SEQ"), ("su=naatsi’i", "NOM=boy"), ("ti’atia-hu-si", "play-PFV-SEQ"), ("su=mogo’ni", "NOM=woman"), ("nobi-ggwe", "house-LOC"), ("iga-hu", "enter-PFV")]
    context := "The boy and girl are at home. Instead of studying, he is playing and she is dancing at the same time. They both stop before their mother comes home."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "seq"), ("aspect", "pfv"), ("markedEvent", "dance"), ("markedEvent", "play"), ("unmarkedAspect", "pfv"), ("unmarkedEvent", "enter")] }

def all : List Datum := [ex_39a, ex_39b, ex_40b, ex_40c, ex_47a, ex_47b, ex_66a, ex_66b, ex_66c, ex_66d, ex_71a, ex_71b]

end Toosarvandani2016.Examples
