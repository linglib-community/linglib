module

public import Linglib.Data.Examples.Schema

/-!
# `ElliottNicolaeSauerland2022` — typed example data

Auto-generated from `Linglib/Data/Examples/ElliottNicolaeSauerland2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ElliottNicolaeSauerland2022.Examples`.
-/

@[expose] public section

namespace ElliottNicolaeSauerland2022.Examples

def ex_2 : Datum :=
  { id := "elliottnicolaesauerland2022_2"
    source := ⟨"elliott-nicolae-sauerland-2022", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which employee left early?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .acceptable), ("plural answer", .unacceptable)]
    paperFeatures := [("type", "SCI")] }

def ex_3 : Datum :=
  { id := "elliottnicolaesauerland2022_3"
    source := ⟨"elliott-nicolae-sauerland-2022", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which employees left early?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .unacceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "PCI")] }

def ex_11 : Datum :=
  { id := "elliottnicolaesauerland2022_11"
    source := ⟨"elliott-nicolae-sauerland-2022", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who is leaving early?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Who are leaving early?", .ungrammatical)]
    readings := [("singular answer", .acceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "BI")] }

def ex_12 : Datum :=
  { id := "elliottnicolaesauerland2022_12"
    source := ⟨"elliott-nicolae-sauerland-2022", "(12)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Pjos andras efige noris?"
    glossedTokens := [("Pjos", "who.SG"), ("andras", "man.SG"), ("efige", "left"), ("noris", "early")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .acceptable), ("plural answer", .unacceptable)]
    paperFeatures := [("type", "SCI")] }

def ex_13 : Datum :=
  { id := "elliottnicolaesauerland2022_13"
    source := ⟨"elliott-nicolae-sauerland-2022", "(13)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Melyik fiú ment el?"
    glossedTokens := [("Melyik", "which"), ("fiú", "boy.SG"), ("ment", "goes"), ("el", "away")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .acceptable), ("plural answer", .unacceptable)]
    paperFeatures := [("type", "SCI")] }

def ex_14 : Datum :=
  { id := "elliottnicolaesauerland2022_14"
    source := ⟨"elliott-nicolae-sauerland-2022", "(14)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Qué chico se fue pronto?"
    glossedTokens := [("Qué", "which"), ("chico", "boy.SG"), ("se", "REFL"), ("fue", "left"), ("pronto", "early")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .acceptable), ("plural answer", .unacceptable)]
    paperFeatures := [("type", "SCI")] }

def ex_15 : Datum :=
  { id := "elliottnicolaesauerland2022_15"
    source := ⟨"elliott-nicolae-sauerland-2022", "(15)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Pji andres efigan noris?"
    glossedTokens := [("Pji", "who.PL"), ("andres", "man.PL"), ("efigan", "left"), ("noris", "early")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .unacceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "PCI")] }

def ex_16 : Datum :=
  { id := "elliottnicolaesauerland2022_16"
    source := ⟨"elliott-nicolae-sauerland-2022", "(16)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Melyik fiúk mentek el?"
    glossedTokens := [("Melyik", "which"), ("fiúk", "boy.PL"), ("mentek", "went"), ("el", "away")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .unacceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "PCI")] }

def ex_17 : Datum :=
  { id := "elliottnicolaesauerland2022_17"
    source := ⟨"elliott-nicolae-sauerland-2022", "(17)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Qué chicos se fueron pronto?"
    glossedTokens := [("Qué", "which"), ("chicos", "boy.PL"), ("se", "REFL"), ("fueron", "left"), ("pronto", "early")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .unacceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "PCI")] }

def ex_18 : Datum :=
  { id := "elliottnicolaesauerland2022_18"
    source := ⟨"elliott-nicolae-sauerland-2022", "(18)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Pjos efige noris?"
    glossedTokens := [("Pjos", "who.SG"), ("efige", "left"), ("noris", "early")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .acceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_19 : Datum :=
  { id := "elliottnicolaesauerland2022_19"
    source := ⟨"elliott-nicolae-sauerland-2022", "(19)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Ki énekel?"
    glossedTokens := [("Ki", "who.SG"), ("énekel", "sings")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .acceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_20 : Datum :=
  { id := "elliottnicolaesauerland2022_20"
    source := ⟨"elliott-nicolae-sauerland-2022", "(20)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quién se fue pronto?"
    glossedTokens := [("Quién", "who.SG"), ("se", "REFL"), ("fue", "left"), ("pronto", "early")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .acceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_21 : Datum :=
  { id := "elliottnicolaesauerland2022_21"
    source := ⟨"elliott-nicolae-sauerland-2022", "(21)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Pji efigan noris?"
    glossedTokens := [("Pji", "who.PL"), ("efigan", "left"), ("noris", "early")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .unacceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "PBI")] }

def ex_22 : Datum :=
  { id := "elliottnicolaesauerland2022_22"
    source := ⟨"elliott-nicolae-sauerland-2022", "(22)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Kik énekelnek?"
    glossedTokens := [("Kik", "who.PL"), ("énekelnek", "sing")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .unacceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "PBI")] }

def ex_23 : Datum :=
  { id := "elliottnicolaesauerland2022_23"
    source := ⟨"elliott-nicolae-sauerland-2022", "(23)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quiénes se fueron pronto?"
    glossedTokens := [("Quiénes", "who.PL"), ("se", "REFL"), ("fueron", "left"), ("pronto", "early")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .unacceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "PBI")] }

def ex_24a : Datum :=
  { id := "elliottnicolaesauerland2022_24a"
    source := ⟨"elliott-nicolae-sauerland-2022", "(24a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "pero no me acuerdo quién"
    glossedTokens := [("pero", "but"), ("no", "not"), ("me", "REFL"), ("acuerdo", "remember"), ("quién", "who.SG")]
    context := "One of my friends called"
    judgment := .acceptable
    alternatives := [("pero no me acuerdo quiénes", .unacceptable)]
    readings := []
    paperFeatures := [("context", "exactlyOne"), ("form", "quien"), ("rival", "quienes")] }

def ex_24b : Datum :=
  { id := "elliottnicolaesauerland2022_24b"
    source := ⟨"elliott-nicolae-sauerland-2022", "(24b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "pero no me acuerdo quién"
    glossedTokens := [("pero", "but"), ("no", "not"), ("me", "REFL"), ("acuerdo", "remember"), ("quién", "who.SG")]
    context := "At least one person called"
    judgment := .acceptable
    alternatives := [("pero no me acuerdo quiénes", .unacceptable)]
    readings := []
    paperFeatures := [("context", "atLeastOne"), ("form", "quien"), ("rival", "quienes")] }

def ex_24c : Datum :=
  { id := "elliottnicolaesauerland2022_24c"
    source := ⟨"elliott-nicolae-sauerland-2022", "(24c)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "pero no me acuerdo quiénes"
    glossedTokens := [("pero", "but"), ("no", "not"), ("me", "REFL"), ("acuerdo", "remember"), ("quiénes", "who.PL")]
    context := "Several friends called"
    judgment := .acceptable
    alternatives := [("pero no me acuerdo quién", .questionable)]
    readings := []
    paperFeatures := [("context", "several"), ("antecedent", "plural"), ("form", "quienes"), ("rival", "quien")] }

def ex_25 : Datum :=
  { id := "elliottnicolaesauerland2022_25"
    source := ⟨"elliott-nicolae-sauerland-2022", "(25)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Juan no sabe qué amigos van a venir a la fiesta"
    glossedTokens := [("Juan", "Juan"), ("no", "not"), ("sabe", "know"), ("qué", "which"), ("amigos", "friends"), ("van", "will"), ("a", "a"), ("venir", "come"), ("a", "to"), ("la", "the"), ("fiesta", "party")]
    context := "Juan is expecting at least one friend to come to the party."
    judgment := .acceptable
    alternatives := [("Juan no sabe quiénes van a venir a la fiesta", .unacceptable)]
    readings := []
    paperFeatures := [("context", "atLeastOne"), ("form", "quePl"), ("rival", "quienes")] }

def ex_57 : Datum :=
  { id := "elliottnicolaesauerland2022_57"
    source := ⟨"maldonado-2020", "n. 16 (i)"⟩
    reportedIn := some ⟨"elliott-nicolae-sauerland-2022", "(57)"⟩
    language := "stan1288"
    primaryText := "¿Quién hay en la fiesta?"
    glossedTokens := [("Quién", "who.SG"), ("hay", "was.at"), ("en", "in"), ("la", "the"), ("fiesta", "party")]
    context := "A context that does not satisfy existence."
    judgment := .acceptable
    alternatives := [("¿Quiénes hay en la fiesta?", .unacceptable)]
    readings := []
    paperFeatures := [("context", "noExistence"), ("form", "quien"), ("rival", "quienes")] }

def ex_59 : Datum :=
  { id := "elliottnicolaesauerland2022_59"
    source := ⟨"elliott-nicolae-sauerland-2022", "(59)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Juan no sabe quiénes van a venir a la fiesta"
    glossedTokens := [("Juan", "Juan"), ("no", "not"), ("sabe", "know"), ("quiénes", "who.PL"), ("van", "will"), ("a", "a"), ("venir", "come"), ("a", "to"), ("la", "the"), ("fiesta", "party")]
    context := "Juan is expecting at least one of his friends to come with him to the party."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "atLeastOne"), ("form", "quienes")] }

def ex_66 : Datum :=
  { id := "elliottnicolaesauerland2022_66"
    source := ⟨"elliott-nicolae-sauerland-2022", "(66)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Juan no sabe qué amigos van a venir"
    glossedTokens := [("Juan", "Juan"), ("no", "not"), ("sabe", "know"), ("qué", "which"), ("amigos", "friend.PL"), ("van", "go"), ("a", "PREP"), ("venir", "come")]
    context := "Juan is expecting at least one friend to come to the party, but two or more might come."
    judgment := .acceptable
    alternatives := [("Juan no sabe qué amigo van a venir", .unacceptable)]
    readings := []
    paperFeatures := [("context", "atLeastOne"), ("form", "quePl"), ("rival", "queSg")] }

def ex_68 : Datum :=
  { id := "elliottnicolaesauerland2022_68"
    source := ⟨"maldonado-2020", "(18a)"⟩
    reportedIn := some ⟨"elliott-nicolae-sauerland-2022", "(68)"⟩
    language := "stan1288"
    primaryText := "¿Quién está ahí?"
    glossedTokens := [("Quién", "who.SG"), ("está", "is"), ("ahí", "there")]
    context := "Mary and John arrive at their apartment, where there is supposed to be no one. They hear two people whispering inside. Mary asks:"
    judgment := .acceptable
    alternatives := [("¿Quiénes está ahí?", .unacceptable)]
    readings := []
    paperFeatures := [("context", "twoWhispering"), ("form", "quien"), ("rival", "quienes")] }

def n19i : Datum :=
  { id := "elliottnicolaesauerland2022_n19i"
    source := ⟨"elliott-nicolae-sauerland-2022", "n. 19 (i)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1288"
    primaryText := "¿Quién entró en la habitación?"
    glossedTokens := [("Quién", "who.SG"), ("entró", "entered.SG"), ("en", "in"), ("la", "the"), ("habitación", "room")]
    context := "The speaker isn't certain if anyone entered the room, but if someone did, it was at least two people."
    judgment := .acceptable
    alternatives := [("¿Quénes entraron en la habitación?", .unacceptable)]
    readings := []
    paperFeatures := [("context", "zeroOrSeveral"), ("form", "quien"), ("rival", "quienes")] }

def ex_76 : Datum :=
  { id := "elliottnicolaesauerland2022_76"
    source := ⟨"elliott-nicolae-sauerland-2022", "(76)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quiénes formaron un grupo?"
    glossedTokens := [("Quiénes", "who.PL"), ("formaron", "formed"), ("un", "a"), ("grupo", "group")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("two-group answer", .acceptable)]
    paperFeatures := [("type", "PBI")] }

def ex_79 : Datum :=
  { id := "elliottnicolaesauerland2022_79"
    source := ⟨"elliott-nicolae-sauerland-2022", "(79)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quién se reunió en el patio?"
    glossedTokens := [("Quién", "who.SG"), ("se", "REFL"), ("reunió", "gathered"), ("en", "in"), ("el", "the"), ("patio", "playground")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "SBI")] }

def ex_80 : Datum :=
  { id := "elliottnicolaesauerland2022_80"
    source := ⟨"elliott-nicolae-sauerland-2022", "(80)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quién formó un grupo?"
    glossedTokens := [("Quién", "who.SG"), ("formó", "formed"), ("un", "a"), ("grupo", "group")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "SBI")] }

def ex_81 : Datum :=
  { id := "elliottnicolaesauerland2022_81"
    source := ⟨"elliott-nicolae-sauerland-2022", "(81)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quién pesa 300kg?"
    glossedTokens := [("Quién", "who.SG"), ("pesa", "weighs"), ("300kg", "300kg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("distributive answer", .acceptable), ("collective answer", .unacceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_82 : Datum :=
  { id := "elliottnicolaesauerland2022_82"
    source := ⟨"elliott-nicolae-sauerland-2022", "(82)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿Quiénes bebieron 40 cervezas juntos?"
    glossedTokens := [("Quiénes", "who.PL"), ("bebieron", "drink.PL"), ("40", "40"), ("cervezas", "beer"), ("juntos", "together")]
    context := ""
    judgment := .acceptable
    alternatives := [("¿Quién bebió 40 cervezas juntos?", .unacceptable)]
    readings := []
    paperFeatures := [("type", "PBI")] }

def all : List Datum := [ex_2, ex_3, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19, ex_20, ex_21, ex_22, ex_23, ex_24a, ex_24b, ex_24c, ex_25, ex_57, ex_59, ex_66, ex_68, n19i, ex_76, ex_79, ex_80, ex_81, ex_82]

end ElliottNicolaeSauerland2022.Examples
