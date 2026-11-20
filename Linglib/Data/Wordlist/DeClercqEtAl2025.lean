module

public import Linglib.Data.Wordlist.Schema

/-!
# `DeClercqEtAl2025`: word forms

Auto-generated from `Linglib/Data/Wordlist/DeClercqEtAl2025.json` by `scripts/gen_wordlist.py`. Do
not edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
DeClercqEtAl2025.Wordlist`.
-/

@[expose] public section

namespace DeClercqEtAl2025.Wordlist

open CLDF.Wordlist

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

/-- The positive cell, `Degree=Pos`. -/
def pos : Cell := { degree := ↑UD.Degree.Pos }

/-- The comparative cell, `Degree=Cmp`. -/
def cmp : Cell := { degree := ↑UD.Degree.Cmp }

/-- The superlative cell, `Degree=Sup`. -/
def sup : Cell := { degree := ↑UD.Degree.Sup }

/-- The nominative singular cell, `Case=Nom|Number=Sing`. -/
def nom : Cell := { case := ↑UD.Case.Nom, number := ↑UD.Number.Sing }

/-- The accusative singular cell, `Case=Acc|Number=Sing`. -/
def acc : Cell := { case := ↑UD.Case.Acc, number := ↑UD.Number.Sing }

/-- The genitive singular cell, `Case=Gen|Number=Sing`. -/
def gen : Cell := { case := ↑UD.Case.Gen, number := ↑UD.Number.Sing }

/-- The singular cell, `Number=Sing`. -/
def sg : Cell := { number := ↑UD.Number.Sing }

/-- The plural cell, `Number=Plur`. -/
def pl : Cell := { number := ↑UD.Number.Plur }

/-- The first person singular present cell, `Person=1|Number=Sing|Tense=Pres`. -/
def p1 : Cell := { person := ↑UD.Person.first, number := ↑UD.Number.Sing, tense := ↑UD.Tense.Pres }

/-- The second person singular present cell, `Person=2|Number=Sing|Tense=Pres`. -/
def p2 : Cell := { person := ↑UD.Person.second, number := ↑UD.Number.Sing, tense := ↑UD.Tense.Pres }

/-- The third person singular present cell, `Person=3|Number=Sing|Tense=Pres`. -/
def p3 : Cell := { person := ↑UD.Person.third, number := ↑UD.Number.Sing, tense := ↑UD.Tense.Pres }

def Lexemes.tall : Lexeme :=
  { id := "tall", languageId := "stan1293", parameterId := "tall", label := "tall",
    pos := ↑UD.UPOS.ADJ }

def Lexemes.bad : Lexeme :=
  { id := "bad", languageId := "stan1293", parameterId := "bad", label := "bad",
    pos := ↑UD.UPOS.ADJ }

def Lexemes.partsrahasag : Lexeme :=
  { id := "partsrahasag", languageId := "nucl1235", parameterId := "partsrahasag",
    label := "partsrahasag", pos := ↑UD.UPOS.ADJ }

def Lexemes.inteligentni : Lexeme :=
  { id := "inteligentni", languageId := "czec1258", parameterId := "inteligentni",
    label := "inteligentní", pos := ↑UD.UPOS.ADJ }

def Lexemes.chytry : Lexeme :=
  { id := "chytry", languageId := "czec1258", parameterId := "chytry", label := "chytrý",
    pos := ↑UD.UPOS.ADJ }

def Lexemes.chleba : Lexeme :=
  { id := "chleba", languageId := "czec1258", parameterId := "chleba", label := "chleba",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.jazyk : Lexeme :=
  { id := "jazyk", languageId := "czec1258", parameterId := "jazyk", label := "jazyk",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.kipaw : Lexeme :=
  { id := "kipaw", languageId := "kips1239", parameterId := "kipaw", label := "kipaw",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.peel : Lexeme :=
  { id := "peel", languageId := "kips1239", parameterId := "peel", label := "peel",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.pata : Lexeme :=
  { id := "pata", languageId := "kips1239", parameterId := "pata", label := "pata",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.bati : Lexeme :=
  { id := "bati", languageId := "friu1240", variety := "Tualis", parameterId := "bati",
    label := "bati", pos := ↑UD.UPOS.VERB }

def Lexemes.fini : Lexeme :=
  { id := "fini", languageId := "friu1240", variety := "Tualis", parameterId := "fini",
    label := "finî", pos := ↑UD.UPOS.VERB }

def tall : Form Cell :=
  { id := "declercqetal2025_tall"
    lexeme := Lexemes.tall
    cell := pos
    form := "tall"
    morphs := ["tall"]
    source := [
      ⟨"declercq-et-al-2025", "(27)"⟩
    ] }

def taller : Form Cell :=
  { id := "declercqetal2025_taller"
    lexeme := Lexemes.tall
    cell := cmp
    form := "taller"
    morphs := ["tall", "er"]
    source := [
      ⟨"declercq-et-al-2025", "(29)"⟩
    ] }

def tallest : Form Cell :=
  { id := "declercqetal2025_tallest"
    lexeme := Lexemes.tall
    cell := sup
    form := "tallest"
    morphs := ["tall", "est"]
    source := [
      ⟨"declercq-et-al-2025", "(30)"⟩
    ] }

def bad : Form Cell :=
  { id := "declercqetal2025_bad"
    lexeme := Lexemes.bad
    cell := pos
    form := "bad"
    morphs := ["bad"]
    source := [
      ⟨"declercq-et-al-2025", "p. 16"⟩
    ] }

def worse : Form Cell :=
  { id := "declercqetal2025_worse"
    lexeme := Lexemes.bad
    cell := cmp
    form := "worse"
    morphs := ["worse"]
    source := [
      ⟨"declercq-et-al-2025", "Table 1.3"⟩
    ] }

def partsrahasag_pos : Form Cell :=
  { id := "declercqetal2025_partsrahasag_pos"
    lexeme := Lexemes.partsrahasag
    cell := pos
    form := "partsrahasag"
    morphs := ["partsrahasag"]
    source := [
      ⟨"declercq-et-al-2025", "(14a)"⟩
    ] }

def partsrahasag_cmp : Form Cell :=
  { id := "declercqetal2025_partsrahasag_cmp"
    lexeme := Lexemes.partsrahasag
    cell := cmp
    form := "partsrahasag"
    morphs := ["partsrahasag"]
    source := [
      ⟨"declercq-et-al-2025", "(14b)"⟩
    ] }

def partsrahasag_sup : Form Cell :=
  { id := "declercqetal2025_partsrahasag_sup"
    lexeme := Lexemes.partsrahasag
    cell := sup
    form := "partsrahasag"
    morphs := ["partsrahasag"]
    source := [
      ⟨"declercq-et-al-2025", "(14c)"⟩
    ] }

def inteligentni : Form Cell :=
  { id := "declercqetal2025_inteligentni"
    lexeme := Lexemes.inteligentni
    cell := pos
    form := "inteligentní"
    morphs := ["inteligent", "n", "í"]
    source := [
      ⟨"declercq-et-al-2025", "(12a)"⟩
    ] }

def inteligentnejsi : Form Cell :=
  { id := "declercqetal2025_inteligentnejsi"
    lexeme := Lexemes.inteligentni
    cell := cmp
    form := "inteligentnější"
    morphs := ["inteligent", "n", "ějš", "í"]
    source := [
      ⟨"declercq-et-al-2025", "(12b)"⟩
    ] }

def nejinteligentnejsi : Form Cell :=
  { id := "declercqetal2025_nejinteligentnejsi"
    lexeme := Lexemes.inteligentni
    cell := sup
    form := "nejinteligentnější"
    morphs := ["nej", "inteligent", "n", "ějš", "í"]
    source := [
      ⟨"declercq-et-al-2025", "(12c)"⟩
    ] }

def chytry : Form Cell :=
  { id := "declercqetal2025_chytry"
    lexeme := Lexemes.chytry
    cell := pos
    form := "chytrý"
    morphs := ["chytr", "ý"]
    source := [
      ⟨"declercq-et-al-2025", "p. 16"⟩
    ] }

def chytrejsi : Form Cell :=
  { id := "declercqetal2025_chytrejsi"
    lexeme := Lexemes.chytry
    cell := cmp
    form := "chytřejší"
    morphs := ["chytř", "ejš", "í"]
    source := [
      ⟨"declercq-et-al-2025", "p. 16"⟩
    ] }

def chleba_nom : Form Cell :=
  { id := "declercqetal2025_chleba_nom"
    lexeme := Lexemes.chleba
    cell := nom
    form := "chleba"
    morphs := ["chleb", "a"]
    source := [
      ⟨"declercq-et-al-2025", "Table 1.4"⟩
    ] }

def chleba_acc : Form Cell :=
  { id := "declercqetal2025_chleba_acc"
    lexeme := Lexemes.chleba
    cell := acc
    form := "chleba"
    morphs := ["chleb", "a"]
    source := [
      ⟨"declercq-et-al-2025", "Table 1.4"⟩
    ] }

def chleba_gen : Form Cell :=
  { id := "declercqetal2025_chleba_gen"
    lexeme := Lexemes.chleba
    cell := gen
    form := "chleba"
    morphs := ["chleb", "a"]
    source := [
      ⟨"declercq-et-al-2025", "Table 1.4"⟩
    ] }

def jazyk_nom : Form Cell :=
  { id := "declercqetal2025_jazyk_nom"
    lexeme := Lexemes.jazyk
    cell := nom
    form := "jazyk"
    morphs := ["jazyk"]
    source := [
      ⟨"declercq-et-al-2025", "Table 1.4"⟩
    ] }

def jazyk_acc : Form Cell :=
  { id := "declercqetal2025_jazyk_acc"
    lexeme := Lexemes.jazyk
    cell := acc
    form := "jazyk"
    morphs := ["jazyk"]
    source := [
      ⟨"declercq-et-al-2025", "Table 1.4"⟩
    ] }

def jazyka_gen : Form Cell :=
  { id := "declercqetal2025_jazyka_gen"
    lexeme := Lexemes.jazyk
    cell := gen
    form := "jazyka"
    morphs := ["jazyk", "a"]
    source := [
      ⟨"declercq-et-al-2025", "Table 1.4"⟩
    ] }

def kipaw_sg : Form Cell :=
  { id := "declercqetal2025_kipaw_sg"
    lexeme := Lexemes.kipaw
    cell := sg
    form := "kipaw"
    morphs := ["kipaw"]
    source := [
      ⟨"declercq-et-al-2025", "Table 1.6"⟩
    ] }

def kipawtiin_pl : Form Cell :=
  { id := "declercqetal2025_kipawtiin_pl"
    lexeme := Lexemes.kipaw
    cell := pl
    form := "kipawtiin"
    morphs := ["kipaw", "tiin"]
    source := [
      ⟨"declercq-et-al-2025", "Table 1.6"⟩
    ] }

def peelyaan_sg : Form Cell :=
  { id := "declercqetal2025_peelyaan_sg"
    lexeme := Lexemes.peel
    cell := sg
    form := "peelyaan"
    morphs := ["peel", "yaan"]
    source := [
      ⟨"declercq-et-al-2025", "Table 1.6"⟩
    ] }

def peel_pl : Form Cell :=
  { id := "declercqetal2025_peel_pl"
    lexeme := Lexemes.peel
    cell := pl
    form := "peel"
    morphs := ["peel"]
    source := [
      ⟨"declercq-et-al-2025", "Table 1.6"⟩
    ] }

def patayaan_sg : Form Cell :=
  { id := "declercqetal2025_patayaan_sg"
    lexeme := Lexemes.pata
    cell := sg
    form := "patayaan"
    morphs := ["pata", "yaan"]
    source := [
      ⟨"declercq-et-al-2025", "Table 1.6"⟩
    ] }

def pateen_pl : Form Cell :=
  { id := "declercqetal2025_pateen_pl"
    lexeme := Lexemes.pata
    cell := pl
    form := "pateen"
    morphs := ["pat", "een"]
    source := [
      ⟨"declercq-et-al-2025", "Table 1.6"⟩
    ] }

def bat_1 : Form Cell :=
  { id := "declercqetal2025_bat_1"
    lexeme := Lexemes.bati
    cell := p1
    form := "bat"
    morphs := ["bat"]
    source := [
      ⟨"declercq-et-al-2025", "Table 1.9"⟩
    ] }

def bats_2 : Form Cell :=
  { id := "declercqetal2025_bats_2"
    lexeme := Lexemes.bati
    cell := p2
    form := "bats"
    morphs := ["bat", "s"]
    source := [
      ⟨"declercq-et-al-2025", "Table 1.9"⟩
    ] }

def bat_3 : Form Cell :=
  { id := "declercqetal2025_bat_3"
    lexeme := Lexemes.bati
    cell := p3
    form := "bat"
    morphs := ["bat"]
    source := [
      ⟨"declercq-et-al-2025", "Table 1.9"⟩
    ] }

def finis_1 : Form Cell :=
  { id := "declercqetal2025_finis_1"
    lexeme := Lexemes.fini
    cell := p1
    form := "finiʃ"
    morphs := ["fin", "iʃ"]
    source := [
      ⟨"declercq-et-al-2025", "Table 1.9"⟩
    ] }

def finiss_2 : Form Cell :=
  { id := "declercqetal2025_finiss_2"
    lexeme := Lexemes.fini
    cell := p2
    form := "finiʃs"
    morphs := ["fin", "iʃ", "s"]
    source := [
      ⟨"declercq-et-al-2025", "Table 1.9"⟩
    ] }

def finis_3 : Form Cell :=
  { id := "declercqetal2025_finis_3"
    lexeme := Lexemes.fini
    cell := p3
    form := "finiʃ"
    morphs := ["fin", "iʃ"]
    source := [
      ⟨"declercq-et-al-2025", "Table 1.9"⟩
    ] }

def tall.paradigm : Paradigm Cell :=
  { id := "tall", lexeme := Lexemes.tall,
    forms := [tall, taller, tallest],
    source := [
      ⟨"declercq-et-al-2025", ""⟩
    ] }

def bad.paradigm : Paradigm Cell :=
  { id := "bad", lexeme := Lexemes.bad,
    forms := [bad, worse],
    source := [
      ⟨"declercq-et-al-2025", ""⟩
    ] }

def partsrahasag.paradigm : Paradigm Cell :=
  { id := "partsrahasag", lexeme := Lexemes.partsrahasag,
    forms := [partsrahasag_pos, partsrahasag_cmp, partsrahasag_sup],
    source := [
      ⟨"declercq-et-al-2025", ""⟩
    ] }

def inteligentni.paradigm : Paradigm Cell :=
  { id := "inteligentni", lexeme := Lexemes.inteligentni,
    forms := [inteligentni, inteligentnejsi, nejinteligentnejsi],
    source := [
      ⟨"declercq-et-al-2025", ""⟩
    ] }

def chytry.paradigm : Paradigm Cell :=
  { id := "chytry", lexeme := Lexemes.chytry,
    forms := [chytry, chytrejsi],
    source := [
      ⟨"declercq-et-al-2025", ""⟩
    ] }

def chleba.paradigm : Paradigm Cell :=
  { id := "chleba", lexeme := Lexemes.chleba,
    forms := [chleba_nom, chleba_acc, chleba_gen],
    source := [
      ⟨"declercq-et-al-2025", ""⟩
    ] }

def jazyk.paradigm : Paradigm Cell :=
  { id := "jazyk", lexeme := Lexemes.jazyk,
    forms := [jazyk_nom, jazyk_acc, jazyka_gen],
    source := [
      ⟨"declercq-et-al-2025", ""⟩
    ] }

def kipaw.paradigm : Paradigm Cell :=
  { id := "kipaw", lexeme := Lexemes.kipaw,
    forms := [kipaw_sg, kipawtiin_pl],
    source := [
      ⟨"declercq-et-al-2025", ""⟩
    ] }

def peel.paradigm : Paradigm Cell :=
  { id := "peel", lexeme := Lexemes.peel,
    forms := [peelyaan_sg, peel_pl],
    source := [
      ⟨"declercq-et-al-2025", ""⟩
    ] }

def pata.paradigm : Paradigm Cell :=
  { id := "pata", lexeme := Lexemes.pata,
    forms := [patayaan_sg, pateen_pl],
    source := [
      ⟨"declercq-et-al-2025", ""⟩
    ] }

def bati.paradigm : Paradigm Cell :=
  { id := "bati", lexeme := Lexemes.bati,
    forms := [bat_1, bats_2, bat_3],
    source := [
      ⟨"declercq-et-al-2025", ""⟩
    ] }

def fini.paradigm : Paradigm Cell :=
  { id := "fini", lexeme := Lexemes.fini,
    forms := [finis_1, finiss_2, finis_3],
    source := [
      ⟨"declercq-et-al-2025", ""⟩
    ] }

/-- The source's analysis of a form, its parse rather than data. -/
structure Analysis where
  /-- The form analysed. -/
  form : Form Cell
  /-- The `Exponents` column, the exponents of the form in linear order, as the lexicalization
  tables give them. -/
  exponents : (List String)
  deriving DecidableEq, Repr

def tall.analysis : Analysis :=
  { form := tall,
    exponents := ["tall"] }

def taller.analysis : Analysis :=
  { form := taller,
    exponents := ["tall", "er"] }

def tallest.analysis : Analysis :=
  { form := tallest,
    exponents := ["tall", "est"] }

def bad.analysis : Analysis :=
  { form := bad,
    exponents := ["bad"] }

def worse.analysis : Analysis :=
  { form := worse,
    exponents := ["worse"] }

def partsrahasag_pos.analysis : Analysis :=
  { form := partsrahasag_pos,
    exponents := ["partsrahasag"] }

def partsrahasag_cmp.analysis : Analysis :=
  { form := partsrahasag_cmp,
    exponents := ["partsrahasag"] }

def partsrahasag_sup.analysis : Analysis :=
  { form := partsrahasag_sup,
    exponents := ["partsrahasag"] }

def inteligentni.analysis : Analysis :=
  { form := inteligentni,
    exponents := ["inteligent", "n"] }

def inteligentnejsi.analysis : Analysis :=
  { form := inteligentnejsi,
    exponents := ["inteligent", "n", "ějš"] }

def nejinteligentnejsi.analysis : Analysis :=
  { form := nejinteligentnejsi,
    exponents := ["nej", "inteligent", "n", "ějš"] }

def chytry.analysis : Analysis :=
  { form := chytry,
    exponents := ["chytr"] }

def chytrejsi.analysis : Analysis :=
  { form := chytrejsi,
    exponents := ["chytr", "ějš"] }

def chleba_nom.analysis : Analysis :=
  { form := chleba_nom,
    exponents := ["chleb", "a"] }

def chleba_acc.analysis : Analysis :=
  { form := chleba_acc,
    exponents := ["chleb", "a"] }

def chleba_gen.analysis : Analysis :=
  { form := chleba_gen,
    exponents := ["chleb", "a"] }

def jazyk_nom.analysis : Analysis :=
  { form := jazyk_nom,
    exponents := ["jazyk"] }

def jazyk_acc.analysis : Analysis :=
  { form := jazyk_acc,
    exponents := ["jazyk"] }

def jazyka_gen.analysis : Analysis :=
  { form := jazyka_gen,
    exponents := ["jazyk", "a"] }

def kipaw_sg.analysis : Analysis :=
  { form := kipaw_sg,
    exponents := ["kipaw"] }

def kipawtiin_pl.analysis : Analysis :=
  { form := kipawtiin_pl,
    exponents := ["kipaw", "tiin"] }

def peelyaan_sg.analysis : Analysis :=
  { form := peelyaan_sg,
    exponents := ["peel", "yaan"] }

def peel_pl.analysis : Analysis :=
  { form := peel_pl,
    exponents := ["peel"] }

def patayaan_sg.analysis : Analysis :=
  { form := patayaan_sg,
    exponents := ["pata", "yaan"] }

def pateen_pl.analysis : Analysis :=
  { form := pateen_pl,
    exponents := ["pata", "een"] }

def bat_1.analysis : Analysis :=
  { form := bat_1,
    exponents := ["bat"] }

def bats_2.analysis : Analysis :=
  { form := bats_2,
    exponents := ["bat", "s"] }

def bat_3.analysis : Analysis :=
  { form := bat_3,
    exponents := ["bat"] }

def finis_1.analysis : Analysis :=
  { form := finis_1,
    exponents := ["fin", "iʃ"] }

def finiss_2.analysis : Analysis :=
  { form := finiss_2,
    exponents := ["fin", "iʃ", "s"] }

def finis_3.analysis : Analysis :=
  { form := finis_3,
    exponents := ["fin", "iʃ"] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.tall, Lexemes.bad, Lexemes.partsrahasag, Lexemes.inteligentni,
  Lexemes.chytry, Lexemes.chleba, Lexemes.jazyk, Lexemes.kipaw, Lexemes.peel, Lexemes.pata,
  Lexemes.bati, Lexemes.fini]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [tall, taller, tallest, bad, worse, partsrahasag_pos,
  partsrahasag_cmp, partsrahasag_sup, inteligentni, inteligentnejsi, nejinteligentnejsi, chytry,
  chytrejsi, chleba_nom, chleba_acc, chleba_gen, jazyk_nom, jazyk_acc, jazyka_gen, kipaw_sg,
  kipawtiin_pl, peelyaan_sg, peel_pl, patayaan_sg, pateen_pl, bat_1, bats_2, bat_3, finis_1,
  finiss_2, finis_3]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

/-- Every paradigm of the data. -/
def paradigms : List (Paradigm Cell) := [tall.paradigm, bad.paradigm, partsrahasag.paradigm,
  inteligentni.paradigm, chytry.paradigm, chleba.paradigm, jazyk.paradigm, kipaw.paradigm,
  peel.paradigm, pata.paradigm, bati.paradigm, fini.paradigm]

/-- Every analysis of the data. -/
def analyses : List Analysis := [tall.analysis, taller.analysis, tallest.analysis, bad.analysis,
  worse.analysis, partsrahasag_pos.analysis, partsrahasag_cmp.analysis, partsrahasag_sup.analysis,
  inteligentni.analysis, inteligentnejsi.analysis, nejinteligentnejsi.analysis, chytry.analysis,
  chytrejsi.analysis, chleba_nom.analysis, chleba_acc.analysis, chleba_gen.analysis,
  jazyk_nom.analysis, jazyk_acc.analysis, jazyka_gen.analysis, kipaw_sg.analysis,
  kipawtiin_pl.analysis, peelyaan_sg.analysis, peel_pl.analysis, patayaan_sg.analysis,
  pateen_pl.analysis, bat_1.analysis, bats_2.analysis, bat_3.analysis, finis_1.analysis,
  finiss_2.analysis, finis_3.analysis]

end DeClercqEtAl2025.Wordlist
