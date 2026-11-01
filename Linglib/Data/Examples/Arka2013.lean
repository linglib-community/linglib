module

public import Linglib.Data.Examples.Schema

/-!
# `Arka2013` — typed example data

Auto-generated from `Linglib/Data/Examples/Arka2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Arka2013.Examples`.
-/

@[expose] public section

namespace Arka2013.Examples

def ex_3 : Datum :=
  { id := "arka2013_3"
    source := ⟨"arka-2013", "(3)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia datang."
    glossedTokens := [("Dia", "3s"), ("datang", "come")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("S/he came.", .acceptable), ("S/he is coming.", .acceptable), ("S/he will come.", .acceptable)]
    paperFeatures := [("tam", "contextual")] }

def ex_4a : Datum :=
  { id := "arka2013_4a"
    source := ⟨"arka-2013", "(4a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia datang (besok)."
    glossedTokens := [("Dia", "3s"), ("datang", "come"), ("besok", "tomorrow")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("frame", "S<E-R"), ("adjunct", "besok")] }

def ex_4b : Datum :=
  { id := "arka2013_4b"
    source := ⟨"arka-2013", "(4b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia datang (kemarin)."
    glossedTokens := [("Dia", "3s"), ("datang", "come"), ("kemarin", "yesterday")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("frame", "E-R<S"), ("adjunct", "kemarin")] }

def ex_4c : Datum :=
  { id := "arka2013_4c"
    source := ⟨"arka-2013", "(4c)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia datang (sekarang)."
    glossedTokens := [("Dia", "3s"), ("datang", "come"), ("sekarang", "now")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("frame", "E-R-S"), ("adjunct", "sekarang")] }

def ex_5a : Datum :=
  { id := "arka2013_5a"
    source := ⟨"arka-2013", "(5a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia sudah pergi (sekarang)."
    glossedTokens := [("Dia", "3s"), ("sudah", "PERF"), ("pergi", "go"), ("sekarang", "now")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aux", "sudah"), ("frame", "E<S,R")] }

def ex_5b : Datum :=
  { id := "arka2013_5b"
    source := ⟨"arka-2013", "(5b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia sudah pergi kemarin."
    glossedTokens := [("Dia", "3s"), ("sudah", "PERF"), ("pergi", "go"), ("kemarin", "yesterday")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aux", "sudah"), ("frame", "E<R<S"), ("adjunct", "kemarin")] }

def ex_6a : Datum :=
  { id := "arka2013_6a"
    source := ⟨"arka-2013", "(6a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Ali (sedang) me-mukul-i kepala=nya sendiri."
    glossedTokens := [("Ali", "A."), ("sedang", "PROG"), ("me-mukul-i", "AV.hit-I"), ("kepala=nya", "head=3sg.poss"), ("sendiri", "self")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aux", "sedang"), ("aspect", "progressive"), ("marking", "applicative -i")] }

def ex_6b : Datum :=
  { id := "arka2013_6b"
    source := ⟨"arka-2013", "(6b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Ali (sedang) me-mukul-mukul kepala=nya sendiri."
    glossedTokens := [("Ali", "Ali"), ("sedang", "PROG"), ("me-mukul-mukul", "AV.hit-RED"), ("kepala=nya", "head=3sg.poss"), ("sendiri", "self")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aux", "sedang"), ("aspect", "progressive"), ("marking", "reduplication")] }

def ex_7 : Datum :=
  { id := "arka2013_7"
    source := ⟨"arka-2013", "(7)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Ali tidak masuk-masuk ke rumah."
    glossedTokens := [("Ali", "Ali"), ("tidak", "NEG"), ("masuk-masuk", "enter-RED"), ("ke", "to"), ("rumah", "house")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marking", "reduplication"), ("meaning", "unrealised expectation")] }

def ex_8 : Datum :=
  { id := "arka2013_8"
    source := ⟨"arka-2013", "(8)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia makan sambil menonton TV."
    glossedTokens := [("Dia", "3s"), ("makan", "eat"), ("sambil", "while"), ("menonton", "AV.watch"), ("TV", "TV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "progressive"), ("tam", "contextual")] }

def ex_10 : Datum :=
  { id := "arka2013_10"
    source := ⟨"arka-2013", "(10)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Mereka (akan) datang."
    glossedTokens := [("Mereka", "3p"), ("akan", "FUT"), ("datang", "come")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aux", "akan"), ("frame", "S<E-R"), ("withAux", "acceptable"), ("clause", "root")] }

def ex_11a : Datum :=
  { id := "arka2013_11a"
    source := ⟨"arka-2013", "(11a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Mereka ingin [datang besok]."
    glossedTokens := [("Mereka", "3p"), ("ingin", "want"), ("datang", "come"), ("besok", "tomorrow")]
    context := ""
    judgment := .acceptable
    alternatives := [("Mereka ingin [akan datang besok].", .ungrammatical)]
    readings := []
    paperFeatures := [("withAux", "ungrammatical"), ("matrix", "ingin")] }

def ex_11c : Datum :=
  { id := "arka2013_11c"
    source := ⟨"arka-2013", "(11c)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Saya tahu [bahwa mereka akan datang]."
    glossedTokens := [("Saya", "1s"), ("tahu", "know"), ("bahwa", "that"), ("mereka", "3p"), ("akan", "FUT"), ("datang", "come")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aux", "akan"), ("withAux", "acceptable"), ("matrix", "tahu"), ("subordinator", "bahwa")] }

def ex_12a : Datum :=
  { id := "arka2013_12a"
    source := ⟨"arka-2013", "(12a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia akan/sudah/sedang makan."
    glossedTokens := [("Dia", "3s"), ("akan/sudah/sedang", "FUT/PERF/PROG"), ("makan", "eat")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("withAux", "acceptable"), ("clause", "root")] }

def ex_12b : Datum :=
  { id := "arka2013_12b"
    source := ⟨"arka-2013", "(12b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Saya menyuruh dia [makan]."
    glossedTokens := [("Saya", "1s"), ("menyuruh", "AV.ask"), ("dia", "3s"), ("makan", "eat")]
    context := ""
    judgment := .acceptable
    alternatives := [("Saya menyuruh dia [akan/sudah/sedang makan].", .ungrammatical)]
    readings := []
    paperFeatures := [("withAux", "ungrammatical"), ("matrix", "menyuruh")] }

def ex_13a : Datum :=
  { id := "arka2013_13a"
    source := ⟨"arka-2013", "(13a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Orang itu mendorong saya [ _ jatuh]."
    glossedTokens := [("Orang", "person"), ("itu", "that"), ("mendorong", "AV.push"), ("saya", "1s"), ("jatuh", "fall")]
    context := ""
    judgment := .acceptable
    alternatives := [("Orang itu mendorong saya [ _ akan/sedang/sudah jatuh].", .ungrammatical)]
    readings := []
    paperFeatures := [("withAux", "ungrammatical"), ("matrix", "mendorong")] }

def ex_14a : Datum :=
  { id := "arka2013_14a"
    source := ⟨"arka-2013", "(14a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia datang (sambil) menangis."
    glossedTokens := [("Dia", "3s"), ("datang", "come"), ("sambil", "while"), ("menangis", "AV.cry")]
    context := ""
    judgment := .acceptable
    alternatives := [("Dia datang [(sambil) sedang menangis].", .ungrammatical)]
    readings := []
    paperFeatures := [("withAux", "ungrammatical"), ("adjunct", "sambil")] }

def ex_15a : Datum :=
  { id := "arka2013_15a"
    source := ⟨"arka-2013", "(15a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Saya belajar [menembak]."
    glossedTokens := [("Saya", "1s"), ("belajar", "study"), ("menembak", "AV.shoot")]
    context := ""
    judgment := .acceptable
    alternatives := [("Saya belajar bisa [menembak].", .ungrammatical)]
    readings := []
    paperFeatures := [("withAux", "ungrammatical"), ("matrix", "belajar")] }

def ex_15c : Datum :=
  { id := "arka2013_15c"
    source := ⟨"arka-2013", "(15c)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Saya belajar agar (bisa) menembak."
    glossedTokens := [("Saya", "1s"), ("belajar", "study"), ("agar", "so.that"), ("bisa", "able"), ("menembak", "AV.shoot")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("withAux", "acceptable"), ("subordinator", "agar")] }

def ex_18a : Datum :=
  { id := "arka2013_18a"
    source := ⟨"arka-2013", "(18a)"⟩
    reportedIn := none
    method := some .corpus
    language := "indo1316"
    primaryText := "...di jalan banyak sapi yang sedang memakan rumput."
    glossedTokens := [("di", "at"), ("jalan", "road"), ("banyak", "plenty"), ("sapi", "cow"), ("yang", "REL"), ("sedang", "PROG"), ("memakan", "AV.eat"), ("rumput", "grass")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aux", "sedang"), ("voice", "AV")] }

def ex_18b : Datum :=
  { id := "arka2013_18b"
    source := ⟨"arka-2013", "(18b)"⟩
    reportedIn := none
    method := some .corpus
    language := "indo1316"
    primaryText := "Dari salah satu swalayan, petugas menemukan makanan jenis roti yang kemasan dan isi=nya telah rusak dan diduga sudah dimakan tikus."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aux", "sudah"), ("voice", "passive")] }

def ex_34a : Datum :=
  { id := "arka2013_34a"
    source := ⟨"arka-2013", "(34a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "'Siapa itu?', tanya=nya."
    glossedTokens := [("Siapa", "who"), ("itu", "that"), ("tanya=nya", "ask=NYA")]
    context := ""
    judgment := .acceptable
    alternatives := [("'Siapa itu?' akan tanyanya (nanti).", .ungrammatical)]
    readings := [("he asked", .acceptable), ("he will ask", .unacceptable)]
    paperFeatures := [("nominalised", "true"), ("axis", "past"), ("predicate", "nominal"), ("withAux", "ungrammatical")] }

def ex_34b : Datum :=
  { id := "arka2013_34b"
    source := ⟨"arka-2013", "(34b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "'Siapa itu?', tanya=nya nanti."
    glossedTokens := [("Siapa", "who"), ("itu", "that"), ("tanya=nya", "ask=NYA"), ("nanti", "later")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("nominalised", "true"), ("axis", "future"), ("adjunct", "nanti")] }

def ex_34d : Datum :=
  { id := "arka2013_34d"
    source := ⟨"arka-2013", "(34d)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "'Siapa itu?', dia akan (ber)tanya (nanti)."
    glossedTokens := [("Siapa", "who"), ("itu", "that"), ("dia", "3"), ("akan", "FUT"), ("(ber)tanya", "BER-ask"), ("nanti", "later")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aux", "akan"), ("withAux", "acceptable"), ("clause", "root")] }

def ex_35a : Datum :=
  { id := "arka2013_35a"
    source := ⟨"arka-2013", "(35a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Kapan beli=nya?"
    glossedTokens := [("Kapan", "when"), ("beli=nya", "buy=NYA")]
    context := ""
    judgment := .acceptable
    alternatives := [("kapan akan beli=nya?", .ungrammatical)]
    readings := [("When did you buy it?", .acceptable), ("When are you going to buy it?", .unacceptable)]
    paperFeatures := [("nominalised", "true"), ("axis", "past"), ("predicate", "nominal"), ("withAux", "ungrammatical")] }

def ex_35c : Datum :=
  { id := "arka2013_35c"
    source := ⟨"arka-2013", "(35c)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Kapan kamu akan beli?"
    glossedTokens := [("Kapan", "when"), ("kamu", "2s"), ("akan", "FUT"), ("beli", "buy")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aux", "akan"), ("withAux", "acceptable"), ("clause", "root")] }

def ex_36a : Datum :=
  { id := "arka2013_36a"
    source := ⟨"arka-2013", "(36a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Kapan lahirnya?"
    glossedTokens := [("Kapan", "when"), ("lahirnya", "birth=3s")]
    context := ""
    judgment := .acceptable
    alternatives := [("Kapan akan lahirnya?", .ungrammatical)]
    readings := [("When was s/he born?", .acceptable), ("When is s/he going to be born?", .unacceptable)]
    paperFeatures := [("nominalised", "true"), ("axis", "past"), ("predicate", "nominal"), ("withAux", "ungrammatical")] }

def ex_36c : Datum :=
  { id := "arka2013_36c"
    source := ⟨"arka-2013", "(36c)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Kapan ia akan lahir?"
    glossedTokens := [("Kapan", "when"), ("ia", "3s"), ("akan", "FUT"), ("lahir", "birth")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aux", "akan"), ("withAux", "acceptable"), ("clause", "root")] }

def ex_37a : Datum :=
  { id := "arka2013_37a"
    source := ⟨"arka-2013", "(37a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "kamu harus datang."
    glossedTokens := [("kamu", "2"), ("harus", "must"), ("datang", "come")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "harus"), ("nominalised", "false"), ("soa", "future"), ("evaluation", "deontic")] }

def ex_37b : Datum :=
  { id := "arka2013_37b"
    source := ⟨"arka-2013", "(37b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "harus=nya kamu datang."
    glossedTokens := [("harus=nya", "must=NYA"), ("kamu", "2"), ("datang", "come")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "harus"), ("nominalised", "true"), ("soa", "past"), ("evaluation", "counterfactual")] }

def ex_38a : Datum :=
  { id := "arka2013_38a"
    source := ⟨"arka-2013", "(38a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Ia bisa menangis"
    glossedTokens := [("Ia", "she"), ("bisa", "can"), ("menangis", "cry")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "bisa"), ("nominalised", "false"), ("soa", "future"), ("evaluation", "epistemic")] }

def ex_38b : Datum :=
  { id := "arka2013_38b"
    source := ⟨"arka-2013", "(38b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "bisa=nya menangis"
    glossedTokens := [("bisa=nya", "can=3s"), ("menangis", "cry")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "bisa"), ("nominalised", "true"), ("soa", "past"), ("evaluation", "past ability")] }

def ex_39a : Datum :=
  { id := "arka2013_39a"
    source := ⟨"arka-2013", "(39a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Ia mau pulang."
    glossedTokens := [("Ia", "3s"), ("mau", "wish"), ("pulang", "go.home")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "mau"), ("nominalised", "false"), ("soa", "future")] }

def ex_39b : Datum :=
  { id := "arka2013_39b"
    source := ⟨"arka-2013", "(39b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "mau=nya pulang."
    glossedTokens := [("mau=nya", "wish=DEF"), ("pulang", "go.home")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "mau"), ("nominalised", "true"), ("soa", "present/past"), ("evaluation", "counterfactual")] }

def ex_40a : Datum :=
  { id := "arka2013_40a"
    source := ⟨"arka-2013", "(40a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "tampak=nya [ada orang datang]"
    glossedTokens := [("tampak=nya", "appear=DEF"), ("ada", "exist"), ("orang", "person"), ("datang", "come")]
    context := ""
    judgment := .acceptable
    alternatives := [("sedang tampak=nya [ada orang datang].", .ungrammatical)]
    readings := []
    paperFeatures := [("nominalised", "true"), ("withAux", "ungrammatical"), ("evidential", "visual"), ("predicate", "nominal")] }

def ex_41 : Datum :=
  { id := "arka2013_41"
    source := ⟨"arka-2013", "(41)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Tampak ada orang datang"
    glossedTokens := [("Tampak", "appear"), ("ada", "exist"), ("orang", "people"), ("datang", "come")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("nominalised", "false")] }

def ex_42a : Datum :=
  { id := "arka2013_42a"
    source := ⟨"arka-2013", "(42a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia sakit."
    glossedTokens := [("Dia", "3s"), ("sakit", "ill")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential", "none")] }

def ex_42b : Datum :=
  { id := "arka2013_42b"
    source := ⟨"arka-2013", "(42b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia sakit kata=nya."
    glossedTokens := [("Dia", "3s"), ("sakit", "ill"), ("kata=nya", "word=DEF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential", "reportative"), ("nominalised", "true")] }

def ex_43a : Datum :=
  { id := "arka2013_43a"
    source := ⟨"arka-2013", "(43a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Kamu pembohong kata=nya"
    glossedTokens := [("Kamu", "2"), ("pembohong", "PEN.lie"), ("kata=nya", "word=DEF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential", "reportative"), ("nominalised", "true")] }

def ex_43b : Datum :=
  { id := "arka2013_43b"
    source := ⟨"arka-2013", "(43b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Kamu pembohong keluh=nya"
    glossedTokens := [("Kamu", "2"), ("pembohong", "PEN.lie"), ("keluh=nya", "word=3POSS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential", "none"), ("nominalised", "true")] }

def ex_44a : Datum :=
  { id := "arka2013_44a"
    source := ⟨"arka-2013", "(44a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia tidur."
    glossedTokens := [("Dia", "3s"), ("tidur", "sleep")]
    context := ""
    judgment := .acceptable
    alternatives := [("Dia adalah tidur.", .ungrammatical)]
    readings := []
    paperFeatures := [("predicate", "verbal"), ("adalah", "ungrammatical")] }

def ex_45a : Datum :=
  { id := "arka2013_45a"
    source := ⟨"arka-2013", "(45a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Ali (adalah) guru itu."
    glossedTokens := [("Ali", "Ali"), ("adalah", "be"), ("guru", "teacher"), ("itu", "the")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "nominal"), ("adalah", "acceptable")] }

def ex_45b : Datum :=
  { id := "arka2013_45b"
    source := ⟨"arka-2013", "(45b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Guru itu (adalah) Ali."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "nominal"), ("adalah", "acceptable")] }

def ex_46a : Datum :=
  { id := "arka2013_46a"
    source := ⟨"arka-2013", "(46a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "[ _ tidur] (adalah) mau=nya"
    glossedTokens := [("tidur", "sleep"), ("adalah", "be"), ("mau=nya", "want=DEF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "nominal"), ("nominalised", "true"), ("adalah", "acceptable")] }

def ex_46b : Datum :=
  { id := "arka2013_46b"
    source := ⟨"arka-2013", "(46b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Mau=nya (adalah) [ _ tidur]"
    glossedTokens := [("Mau=nya", "want=DEF"), ("adalah", "be"), ("tidur", "sleep")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "nominal"), ("nominalised", "true"), ("adalah", "acceptable")] }

def ex_47a : Datum :=
  { id := "arka2013_47a"
    source := ⟨"arka-2013", "(47a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Ali bukan/*tidak guru itu."
    glossedTokens := [("Ali", "Ali"), ("bukan", "NEG"), ("guru", "teacher"), ("itu", "that")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "nominal"), ("bukan", "acceptable"), ("tidak", "ungrammatical")] }

def ex_47b : Datum :=
  { id := "arka2013_47b"
    source := ⟨"arka-2013", "(47b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Guru itu bukan/*tidak Ali."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "nominal"), ("bukan", "acceptable"), ("tidak", "ungrammatical")] }

def ex_48a : Datum :=
  { id := "arka2013_48a"
    source := ⟨"arka-2013", "(48a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "[_ tidur] bukan/*tidak mau=nya"
    glossedTokens := [("tidur", "sleep"), ("bukan", "NEG"), ("mau=nya", "want=DEF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "nominal"), ("nominalised", "true"), ("bukan", "acceptable"), ("tidak", "ungrammatical")] }

def ex_48b : Datum :=
  { id := "arka2013_48b"
    source := ⟨"arka-2013", "(48b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Mau=nya bukan / tidak tidur"
    glossedTokens := [("Mau=nya", "want=DEF"), ("bukan/tidak", "NEG"), ("tidur", "sleep")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("The/his/her/my wish was not to sleep.", .acceptable), ("It is the/her/his/your wish that (I/you/(s)he) would not sleep (but I did sleep).", .acceptable)]
    paperFeatures := [("predicate", "nominal"), ("nominalised", "true"), ("bukan", "acceptable"), ("tidak", "acceptable")] }

def all : List Datum := [ex_3, ex_4a, ex_4b, ex_4c, ex_5a, ex_5b, ex_6a, ex_6b, ex_7, ex_8, ex_10, ex_11a, ex_11c, ex_12a, ex_12b, ex_13a, ex_14a, ex_15a, ex_15c, ex_18a, ex_18b, ex_34a, ex_34b, ex_34d, ex_35a, ex_35c, ex_36a, ex_36c, ex_37a, ex_37b, ex_38a, ex_38b, ex_39a, ex_39b, ex_40a, ex_41, ex_42a, ex_42b, ex_43a, ex_43b, ex_44a, ex_45a, ex_45b, ex_46a, ex_46b, ex_47a, ex_47b, ex_48a, ex_48b]

end Arka2013.Examples
