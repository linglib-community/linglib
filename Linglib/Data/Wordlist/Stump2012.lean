module

public import Linglib.Data.Wordlist.Schema

/-!
# `Stump2012`: word forms

Auto-generated from `Linglib/Data/Wordlist/Stump2012.json` by `scripts/gen_wordlist.py`. Do not edit
by hand; edit the JSON and re-run the generator. Declarations live in `namespace
Stump2012.Wordlist`.
-/

@[expose] public section

namespace Stump2012.Wordlist

open CLDF.Wordlist

/-- The values of `System` the source distinguishes. -/
inductive System where
  /-- The present system, `pres` in the source. -/
  | pres
  /-- The perfect system, `perf` in the source. -/
  | perf
  deriving DecidableEq, Repr

/-- A cell of the source's tables, by its Universal Dependencies features and the features UD
lacks. -/
structure Cell extends UD.MorphFeatures where
  /-- The `System` feature. -/
  system : Flat System := ⊥
  deriving DecidableEq, Repr

/-- The perf_system s1 cell, `Number=Sing|Person=1|System=perf`. -/
def perf_system_s1 : Cell :=
  { number := ↑UD.Number.Sing, person := ↑UD.Person.first, system := ↑System.perf }

/-- The perf_system s2 cell, `Number=Sing|Person=2|System=perf`. -/
def perf_system_s2 : Cell :=
  { number := ↑UD.Number.Sing, person := ↑UD.Person.second, system := ↑System.perf }

/-- The perf_system s3 cell, `Number=Sing|Person=3|System=perf`. -/
def perf_system_s3 : Cell :=
  { number := ↑UD.Number.Sing, person := ↑UD.Person.third, system := ↑System.perf }

/-- The perf_system p1 cell, `Number=Plur|Person=1|System=perf`. -/
def perf_system_p1 : Cell :=
  { number := ↑UD.Number.Plur, person := ↑UD.Person.first, system := ↑System.perf }

/-- The perf_system p2 cell, `Number=Plur|Person=2|System=perf`. -/
def perf_system_p2 : Cell :=
  { number := ↑UD.Number.Plur, person := ↑UD.Person.second, system := ↑System.perf }

/-- The perf_system p3 cell, `Number=Plur|Person=3|System=perf`. -/
def perf_system_p3 : Cell :=
  { number := ↑UD.Number.Plur, person := ↑UD.Person.third, system := ↑System.perf }

/-- The acc sg cell, `Case=Acc|Number=Sing`. -/
def acc_sg : Cell := { case := ↑UD.Case.Acc, number := ↑UD.Number.Sing }

/-- The gen sg cell, `Case=Gen|Number=Sing`. -/
def gen_sg : Cell := { case := ↑UD.Case.Gen, number := ↑UD.Number.Sing }

/-- The dat sg cell, `Case=Dat|Number=Sing`. -/
def dat_sg : Cell := { case := ↑UD.Case.Dat, number := ↑UD.Number.Sing }

/-- The acc pl cell, `Case=Acc|Number=Plur`. -/
def acc_pl : Cell := { case := ↑UD.Case.Acc, number := ↑UD.Number.Plur }

/-- The gen pl cell, `Case=Gen|Number=Plur`. -/
def gen_pl : Cell := { case := ↑UD.Case.Gen, number := ↑UD.Number.Plur }

/-- The dat pl cell, `Case=Dat|Number=Plur`. -/
def dat_pl : Cell := { case := ↑UD.Case.Dat, number := ↑UD.Number.Plur }

/-- The act s1 cell, `Number=Sing|Person=1|Voice=Act`. -/
def act_s1 : Cell :=
  { number := ↑UD.Number.Sing, person := ↑UD.Person.first, voice := ↑UD.Voice.Act }

/-- The act s2 cell, `Number=Sing|Person=2|Voice=Act`. -/
def act_s2 : Cell :=
  { number := ↑UD.Number.Sing, person := ↑UD.Person.second, voice := ↑UD.Voice.Act }

/-- The act s3 cell, `Number=Sing|Person=3|Voice=Act`. -/
def act_s3 : Cell :=
  { number := ↑UD.Number.Sing, person := ↑UD.Person.third, voice := ↑UD.Voice.Act }

/-- The act p1 cell, `Number=Plur|Person=1|Voice=Act`. -/
def act_p1 : Cell :=
  { number := ↑UD.Number.Plur, person := ↑UD.Person.first, voice := ↑UD.Voice.Act }

/-- The act p2 cell, `Number=Plur|Person=2|Voice=Act`. -/
def act_p2 : Cell :=
  { number := ↑UD.Number.Plur, person := ↑UD.Person.second, voice := ↑UD.Voice.Act }

/-- The act p3 cell, `Number=Plur|Person=3|Voice=Act`. -/
def act_p3 : Cell :=
  { number := ↑UD.Number.Plur, person := ↑UD.Person.third, voice := ↑UD.Voice.Act }

/-- The pass s1 cell, `Number=Sing|Person=1|Voice=Pass`. -/
def pass_s1 : Cell :=
  { number := ↑UD.Number.Sing, person := ↑UD.Person.first, voice := ↑UD.Voice.Pass }

/-- The pass s2 cell, `Number=Sing|Person=2|Voice=Pass`. -/
def pass_s2 : Cell :=
  { number := ↑UD.Number.Sing, person := ↑UD.Person.second, voice := ↑UD.Voice.Pass }

/-- The pass s3 cell, `Number=Sing|Person=3|Voice=Pass`. -/
def pass_s3 : Cell :=
  { number := ↑UD.Number.Sing, person := ↑UD.Person.third, voice := ↑UD.Voice.Pass }

/-- The pass p1 cell, `Number=Plur|Person=1|Voice=Pass`. -/
def pass_p1 : Cell :=
  { number := ↑UD.Number.Plur, person := ↑UD.Person.first, voice := ↑UD.Voice.Pass }

/-- The pass p2 cell, `Number=Plur|Person=2|Voice=Pass`. -/
def pass_p2 : Cell :=
  { number := ↑UD.Number.Plur, person := ↑UD.Person.second, voice := ↑UD.Voice.Pass }

/-- The pass p3 cell, `Number=Plur|Person=3|Voice=Pass`. -/
def pass_p3 : Cell :=
  { number := ↑UD.Number.Plur, person := ↑UD.Person.third, voice := ↑UD.Voice.Pass }

/-- The pres_system s1 cell, `Number=Sing|Person=1|System=pres`. -/
def pres_system_s1 : Cell :=
  { number := ↑UD.Number.Sing, person := ↑UD.Person.first, system := ↑System.pres }

/-- The pres_system s2 cell, `Number=Sing|Person=2|System=pres`. -/
def pres_system_s2 : Cell :=
  { number := ↑UD.Number.Sing, person := ↑UD.Person.second, system := ↑System.pres }

/-- The pres_system s3 cell, `Number=Sing|Person=3|System=pres`. -/
def pres_system_s3 : Cell :=
  { number := ↑UD.Number.Sing, person := ↑UD.Person.third, system := ↑System.pres }

/-- The pres_system p1 cell, `Number=Plur|Person=1|System=pres`. -/
def pres_system_p1 : Cell :=
  { number := ↑UD.Number.Plur, person := ↑UD.Person.first, system := ↑System.pres }

/-- The pres_system p2 cell, `Number=Plur|Person=2|System=pres`. -/
def pres_system_p2 : Cell :=
  { number := ↑UD.Number.Plur, person := ↑UD.Person.second, system := ↑System.pres }

/-- The pres_system p3 cell, `Number=Plur|Person=3|System=pres`. -/
def pres_system_p3 : Cell :=
  { number := ↑UD.Number.Plur, person := ↑UD.Person.third, system := ↑System.pres }

/-- The p1sg cell, `Number=Sing|Person=1`. -/
def p1sg : Cell := { number := ↑UD.Number.Sing, person := ↑UD.Person.first }

/-- The p2sg cell, `Number=Sing|Person=2`. -/
def p2sg : Cell := { number := ↑UD.Number.Sing, person := ↑UD.Person.second }

/-- The pres s1 cell, `Number=Sing|Person=1|Tense=Pres`. -/
def pres_s1 : Cell :=
  { number := ↑UD.Number.Sing, person := ↑UD.Person.first, tense := ↑UD.Tense.Pres }

/-- The pres s2 cell, `Number=Sing|Person=2|Tense=Pres`. -/
def pres_s2 : Cell :=
  { number := ↑UD.Number.Sing, person := ↑UD.Person.second, tense := ↑UD.Tense.Pres }

/-- The pres s3 cell, `Number=Sing|Person=3|Tense=Pres`. -/
def pres_s3 : Cell :=
  { number := ↑UD.Number.Sing, person := ↑UD.Person.third, tense := ↑UD.Tense.Pres }

/-- The past s1 cell, `Number=Sing|Person=1|Tense=Past`. -/
def past_s1 : Cell :=
  { number := ↑UD.Number.Sing, person := ↑UD.Person.first, tense := ↑UD.Tense.Past }

/-- The past s2 cell, `Number=Sing|Person=2|Tense=Past`. -/
def past_s2 : Cell :=
  { number := ↑UD.Number.Sing, person := ↑UD.Person.second, tense := ↑UD.Tense.Past }

/-- The past s3 cell, `Number=Sing|Person=3|Tense=Past`. -/
def past_s3 : Cell :=
  { number := ↑UD.Number.Sing, person := ↑UD.Person.third, tense := ↑UD.Tense.Past }

def Lexemes.begin_coepisse : Lexeme :=
  { id := "begin_coepisse", languageId := "lati1261", parameterId := "begin", label := "COEPISSE" }

def Lexemes.war_bellum : Lexeme :=
  { id := "war_bellum", languageId := "lati1261", parameterId := "war", label := "BELLUM" }

def Lexemes.praise_laudare : Lexeme :=
  { id := "praise_laudare", languageId := "lati1261", parameterId := "praise", label := "LAUDĀRE" }

def Lexemes.urge_hortari : Lexeme :=
  { id := "urge_hortari", languageId := "lati1261", parameterId := "urge", label := "HORTĀRĪ" }

def Lexemes.carry_ferre : Lexeme :=
  { id := "carry_ferre", languageId := "lati1261", parameterId := "carry", label := "FERRE" }

def Lexemes.nek_nek : Lexeme :=
  { id := "nek_nek", languageId := "hung1274", parameterId := "nek", label := "NEK" }

def Lexemes.benn_benn : Lexeme :=
  { id := "benn_benn", languageId := "hung1274", parameterId := "benn", label := "BENN" }

def Lexemes.rajt_rajt : Lexeme :=
  { id := "rajt_rajt", languageId := "hung1274", parameterId := "rajt", label := "RAJT" }

def Lexemes.need_urfa : Lexeme :=
  { id := "need_urfa", languageId := "oldn1244", parameterId := "need", label := "ÞURFA" }

def begin_perf_s1 : Form Cell :=
  { id := "stump2012_begin_perf_s1"
    lexeme := Lexemes.begin_coepisse
    cell := perf_system_s1
    form := "coepī"
    segments := ["c", "o", "e", "p", "ī"]
    source := [
      ⟨"stump-2012-mmm8", "(17)"⟩
    ] }

def begin_perf_s2 : Form Cell :=
  { id := "stump2012_begin_perf_s2"
    lexeme := Lexemes.begin_coepisse
    cell := perf_system_s2
    form := "coepistī"
    segments := ["c", "o", "e", "p", "i", "s", "t", "ī"]
    source := [
      ⟨"stump-2012-mmm8", "(17)"⟩
    ] }

def begin_perf_s3 : Form Cell :=
  { id := "stump2012_begin_perf_s3"
    lexeme := Lexemes.begin_coepisse
    cell := perf_system_s3
    form := "coepit"
    segments := ["c", "o", "e", "p", "i", "t"]
    source := [
      ⟨"stump-2012-mmm8", "(17)"⟩
    ] }

def begin_perf_p1 : Form Cell :=
  { id := "stump2012_begin_perf_p1"
    lexeme := Lexemes.begin_coepisse
    cell := perf_system_p1
    form := "coepimus"
    segments := ["c", "o", "e", "p", "i", "m", "u", "s"]
    source := [
      ⟨"stump-2012-mmm8", "(17)"⟩
    ] }

def begin_perf_p2 : Form Cell :=
  { id := "stump2012_begin_perf_p2"
    lexeme := Lexemes.begin_coepisse
    cell := perf_system_p2
    form := "coepistis"
    segments := ["c", "o", "e", "p", "i", "s", "t", "i", "s"]
    source := [
      ⟨"stump-2012-mmm8", "(17)"⟩
    ] }

def begin_perf_p3 : Form Cell :=
  { id := "stump2012_begin_perf_p3"
    lexeme := Lexemes.begin_coepisse
    cell := perf_system_p3
    form := "coepērunt"
    segments := ["c", "o", "e", "p", "ē", "r", "u", "n", "t"]
    source := [
      ⟨"stump-2012-mmm8", "(17)"⟩
    ] }

def war_acc_sg : Form Cell :=
  { id := "stump2012_war_acc_sg"
    lexeme := Lexemes.war_bellum
    cell := acc_sg
    form := "bellum"
    segments := ["b", "e", "l", "l", "u", "m"]
    source := [
      ⟨"stump-2012-mmm8", "(22)"⟩
    ] }

def war_gen_sg : Form Cell :=
  { id := "stump2012_war_gen_sg"
    lexeme := Lexemes.war_bellum
    cell := gen_sg
    form := "bellī"
    segments := ["b", "e", "l", "l", "ī"]
    source := [
      ⟨"stump-2012-mmm8", "(22)"⟩
    ] }

def war_dat_sg : Form Cell :=
  { id := "stump2012_war_dat_sg"
    lexeme := Lexemes.war_bellum
    cell := dat_sg
    form := "bellō"
    segments := ["b", "e", "l", "l", "ō"]
    source := [
      ⟨"stump-2012-mmm8", "(22)"⟩
    ] }

def war_acc_pl : Form Cell :=
  { id := "stump2012_war_acc_pl"
    lexeme := Lexemes.war_bellum
    cell := acc_pl
    form := "bella"
    segments := ["b", "e", "l", "l", "a"]
    source := [
      ⟨"stump-2012-mmm8", "(22)"⟩
    ] }

def war_gen_pl : Form Cell :=
  { id := "stump2012_war_gen_pl"
    lexeme := Lexemes.war_bellum
    cell := gen_pl
    form := "bellōrum"
    segments := ["b", "e", "l", "l", "ō", "r", "u", "m"]
    source := [
      ⟨"stump-2012-mmm8", "(22)"⟩
    ] }

def war_dat_pl : Form Cell :=
  { id := "stump2012_war_dat_pl"
    lexeme := Lexemes.war_bellum
    cell := dat_pl
    form := "bellīs"
    segments := ["b", "e", "l", "l", "ī", "s"]
    source := [
      ⟨"stump-2012-mmm8", "(22)"⟩
    ] }

def praise_act_s1 : Form Cell :=
  { id := "stump2012_praise_act_s1"
    lexeme := Lexemes.praise_laudare
    cell := act_s1
    form := "laudō"
    segments := ["l", "a", "u", "d", "ō"]
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ] }

def praise_act_s2 : Form Cell :=
  { id := "stump2012_praise_act_s2"
    lexeme := Lexemes.praise_laudare
    cell := act_s2
    form := "laudās"
    segments := ["l", "a", "u", "d", "ā", "s"]
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ] }

def praise_act_s3 : Form Cell :=
  { id := "stump2012_praise_act_s3"
    lexeme := Lexemes.praise_laudare
    cell := act_s3
    form := "laudat"
    segments := ["l", "a", "u", "d", "a", "t"]
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ] }

def praise_act_p1 : Form Cell :=
  { id := "stump2012_praise_act_p1"
    lexeme := Lexemes.praise_laudare
    cell := act_p1
    form := "laudāmus"
    segments := ["l", "a", "u", "d", "ā", "m", "u", "s"]
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ] }

def praise_act_p2 : Form Cell :=
  { id := "stump2012_praise_act_p2"
    lexeme := Lexemes.praise_laudare
    cell := act_p2
    form := "laudātis"
    segments := ["l", "a", "u", "d", "ā", "t", "i", "s"]
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ] }

def praise_act_p3 : Form Cell :=
  { id := "stump2012_praise_act_p3"
    lexeme := Lexemes.praise_laudare
    cell := act_p3
    form := "laudant"
    segments := ["l", "a", "u", "d", "a", "n", "t"]
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ] }

def praise_pass_s1 : Form Cell :=
  { id := "stump2012_praise_pass_s1"
    lexeme := Lexemes.praise_laudare
    cell := pass_s1
    form := "laudor"
    segments := ["l", "a", "u", "d", "o", "r"]
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ] }

def praise_pass_s2 : Form Cell :=
  { id := "stump2012_praise_pass_s2"
    lexeme := Lexemes.praise_laudare
    cell := pass_s2
    form := "laudāris"
    segments := ["l", "a", "u", "d", "ā", "r", "i", "s"]
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ] }

def praise_pass_s3 : Form Cell :=
  { id := "stump2012_praise_pass_s3"
    lexeme := Lexemes.praise_laudare
    cell := pass_s3
    form := "laudātur"
    segments := ["l", "a", "u", "d", "ā", "t", "u", "r"]
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ] }

def praise_pass_p1 : Form Cell :=
  { id := "stump2012_praise_pass_p1"
    lexeme := Lexemes.praise_laudare
    cell := pass_p1
    form := "laudāmur"
    segments := ["l", "a", "u", "d", "ā", "m", "u", "r"]
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ] }

def praise_pass_p2 : Form Cell :=
  { id := "stump2012_praise_pass_p2"
    lexeme := Lexemes.praise_laudare
    cell := pass_p2
    form := "laudāminī"
    segments := ["l", "a", "u", "d", "ā", "m", "i", "n", "ī"]
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ] }

def praise_pass_p3 : Form Cell :=
  { id := "stump2012_praise_pass_p3"
    lexeme := Lexemes.praise_laudare
    cell := pass_p3
    form := "laudantur"
    segments := ["l", "a", "u", "d", "a", "n", "t", "u", "r"]
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ] }

def urge_pass_s1 : Form Cell :=
  { id := "stump2012_urge_pass_s1"
    lexeme := Lexemes.urge_hortari
    cell := pass_s1
    form := "hortor"
    segments := ["h", "o", "r", "t", "o", "r"]
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ] }

def urge_pass_s2 : Form Cell :=
  { id := "stump2012_urge_pass_s2"
    lexeme := Lexemes.urge_hortari
    cell := pass_s2
    form := "hortāris"
    segments := ["h", "o", "r", "t", "ā", "r", "i", "s"]
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ] }

def urge_pass_s3 : Form Cell :=
  { id := "stump2012_urge_pass_s3"
    lexeme := Lexemes.urge_hortari
    cell := pass_s3
    form := "hortātur"
    segments := ["h", "o", "r", "t", "ā", "t", "u", "r"]
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ] }

def urge_pass_p1 : Form Cell :=
  { id := "stump2012_urge_pass_p1"
    lexeme := Lexemes.urge_hortari
    cell := pass_p1
    form := "hortāmur"
    segments := ["h", "o", "r", "t", "ā", "m", "u", "r"]
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ] }

def urge_pass_p2 : Form Cell :=
  { id := "stump2012_urge_pass_p2"
    lexeme := Lexemes.urge_hortari
    cell := pass_p2
    form := "hortāminī"
    segments := ["h", "o", "r", "t", "ā", "m", "i", "n", "ī"]
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ] }

def urge_pass_p3 : Form Cell :=
  { id := "stump2012_urge_pass_p3"
    lexeme := Lexemes.urge_hortari
    cell := pass_p3
    form := "hortantur"
    segments := ["h", "o", "r", "t", "a", "n", "t", "u", "r"]
    source := [
      ⟨"stump-2012-mmm8", "(28)"⟩
    ] }

def carry_pres_s1 : Form Cell :=
  { id := "stump2012_carry_pres_s1"
    lexeme := Lexemes.carry_ferre
    cell := pres_system_s1
    form := "ferō"
    segments := ["f", "e", "r", "ō"]
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ] }

def carry_pres_s2 : Form Cell :=
  { id := "stump2012_carry_pres_s2"
    lexeme := Lexemes.carry_ferre
    cell := pres_system_s2
    form := "fers"
    segments := ["f", "e", "r", "s"]
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ] }

def carry_pres_s3 : Form Cell :=
  { id := "stump2012_carry_pres_s3"
    lexeme := Lexemes.carry_ferre
    cell := pres_system_s3
    form := "fert"
    segments := ["f", "e", "r", "t"]
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ] }

def carry_pres_p1 : Form Cell :=
  { id := "stump2012_carry_pres_p1"
    lexeme := Lexemes.carry_ferre
    cell := pres_system_p1
    form := "ferimus"
    segments := ["f", "e", "r", "i", "m", "u", "s"]
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ] }

def carry_pres_p2 : Form Cell :=
  { id := "stump2012_carry_pres_p2"
    lexeme := Lexemes.carry_ferre
    cell := pres_system_p2
    form := "fertis"
    segments := ["f", "e", "r", "t", "i", "s"]
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ] }

def carry_pres_p3 : Form Cell :=
  { id := "stump2012_carry_pres_p3"
    lexeme := Lexemes.carry_ferre
    cell := pres_system_p3
    form := "ferunt"
    segments := ["f", "e", "r", "u", "n", "t"]
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ] }

def carry_perf_s1 : Form Cell :=
  { id := "stump2012_carry_perf_s1"
    lexeme := Lexemes.carry_ferre
    cell := perf_system_s1
    form := "tulī"
    segments := ["t", "u", "l", "ī"]
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ] }

def carry_perf_s2 : Form Cell :=
  { id := "stump2012_carry_perf_s2"
    lexeme := Lexemes.carry_ferre
    cell := perf_system_s2
    form := "tulistī"
    segments := ["t", "u", "l", "i", "s", "t", "ī"]
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ] }

def carry_perf_s3 : Form Cell :=
  { id := "stump2012_carry_perf_s3"
    lexeme := Lexemes.carry_ferre
    cell := perf_system_s3
    form := "tulit"
    segments := ["t", "u", "l", "i", "t"]
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ] }

def carry_perf_p1 : Form Cell :=
  { id := "stump2012_carry_perf_p1"
    lexeme := Lexemes.carry_ferre
    cell := perf_system_p1
    form := "tulimus"
    segments := ["t", "u", "l", "i", "m", "u", "s"]
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ] }

def carry_perf_p2 : Form Cell :=
  { id := "stump2012_carry_perf_p2"
    lexeme := Lexemes.carry_ferre
    cell := perf_system_p2
    form := "tulistis"
    segments := ["t", "u", "l", "i", "s", "t", "i", "s"]
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ] }

def carry_perf_p3 : Form Cell :=
  { id := "stump2012_carry_perf_p3"
    lexeme := Lexemes.carry_ferre
    cell := perf_system_p3
    form := "tulērunt"
    segments := ["t", "u", "l", "ē", "r", "u", "n", "t"]
    source := [
      ⟨"stump-2012-mmm8", "(41)"⟩
    ] }

def nek_p1sg : Form Cell :=
  { id := "stump2012_nek_p1sg"
    lexeme := Lexemes.nek_nek
    cell := p1sg
    form := "nekem"
    segments := ["n", "e", "k", "e", "m"]
    source := [
      ⟨"stump-2012-mmm8", "(36)"⟩
    ] }

def nek_p2sg : Form Cell :=
  { id := "stump2012_nek_p2sg"
    lexeme := Lexemes.nek_nek
    cell := p2sg
    form := "neked"
    segments := ["n", "e", "k", "e", "d"]
    source := [
      ⟨"stump-2012-mmm8", "(36)"⟩
    ] }

def benn_p1sg : Form Cell :=
  { id := "stump2012_benn_p1sg"
    lexeme := Lexemes.benn_benn
    cell := p1sg
    form := "bennem"
    segments := ["b", "e", "n", "n", "e", "m"]
    source := [
      ⟨"stump-2012-mmm8", "(36)"⟩
    ] }

def benn_p2sg : Form Cell :=
  { id := "stump2012_benn_p2sg"
    lexeme := Lexemes.benn_benn
    cell := p2sg
    form := "benned"
    segments := ["b", "e", "n", "n", "e", "d"]
    source := [
      ⟨"stump-2012-mmm8", "(36)"⟩
    ] }

def rajt_p1sg : Form Cell :=
  { id := "stump2012_rajt_p1sg"
    lexeme := Lexemes.rajt_rajt
    cell := p1sg
    form := "rajtam"
    segments := ["r", "a", "j", "t", "a", "m"]
    source := [
      ⟨"stump-2012-mmm8", "(36)"⟩
    ] }

def rajt_p2sg : Form Cell :=
  { id := "stump2012_rajt_p2sg"
    lexeme := Lexemes.rajt_rajt
    cell := p2sg
    form := "rajtad"
    segments := ["r", "a", "j", "t", "a", "d"]
    source := [
      ⟨"stump-2012-mmm8", "(36)"⟩
    ] }

def need_pres_s1 : Form Cell :=
  { id := "stump2012_need_pres_s1"
    lexeme := Lexemes.need_urfa
    cell := pres_s1
    form := "þarf"
    segments := ["þ", "a", "r", "f"]
    source := [
      ⟨"stump-2012-mmm8", "(44)"⟩
    ] }

def need_pres_s2 : Form Cell :=
  { id := "stump2012_need_pres_s2"
    lexeme := Lexemes.need_urfa
    cell := pres_s2
    form := "þarft"
    segments := ["þ", "a", "r", "f", "t"]
    source := [
      ⟨"stump-2012-mmm8", "(44)"⟩
    ] }

def need_pres_s3 : Form Cell :=
  { id := "stump2012_need_pres_s3"
    lexeme := Lexemes.need_urfa
    cell := pres_s3
    form := "þarf"
    segments := ["þ", "a", "r", "f"]
    source := [
      ⟨"stump-2012-mmm8", "(44)"⟩
    ] }

def need_past_s1 : Form Cell :=
  { id := "stump2012_need_past_s1"
    lexeme := Lexemes.need_urfa
    cell := past_s1
    form := "þurfta"
    segments := ["þ", "u", "r", "f", "t", "a"]
    source := [
      ⟨"stump-2012-mmm8", "(44)"⟩
    ] }

def need_past_s2 : Form Cell :=
  { id := "stump2012_need_past_s2"
    lexeme := Lexemes.need_urfa
    cell := past_s2
    form := "þurftir"
    segments := ["þ", "u", "r", "f", "t", "i", "r"]
    source := [
      ⟨"stump-2012-mmm8", "(44)"⟩
    ] }

def need_past_s3 : Form Cell :=
  { id := "stump2012_need_past_s3"
    lexeme := Lexemes.need_urfa
    cell := past_s3
    form := "þurfti"
    segments := ["þ", "u", "r", "f", "t", "i"]
    source := [
      ⟨"stump-2012-mmm8", "(44)"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.begin_coepisse, Lexemes.war_bellum, Lexemes.praise_laudare,
  Lexemes.urge_hortari, Lexemes.carry_ferre, Lexemes.nek_nek, Lexemes.benn_benn, Lexemes.rajt_rajt,
  Lexemes.need_urfa]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [begin_perf_s1, begin_perf_s2, begin_perf_s3, begin_perf_p1,
  begin_perf_p2, begin_perf_p3, war_acc_sg, war_gen_sg, war_dat_sg, war_acc_pl, war_gen_pl,
  war_dat_pl, praise_act_s1, praise_act_s2, praise_act_s3, praise_act_p1, praise_act_p2,
  praise_act_p3, praise_pass_s1, praise_pass_s2, praise_pass_s3, praise_pass_p1, praise_pass_p2,
  praise_pass_p3, urge_pass_s1, urge_pass_s2, urge_pass_s3, urge_pass_p1, urge_pass_p2,
  urge_pass_p3, carry_pres_s1, carry_pres_s2, carry_pres_s3, carry_pres_p1, carry_pres_p2,
  carry_pres_p3, carry_perf_s1, carry_perf_s2, carry_perf_s3, carry_perf_p1, carry_perf_p2,
  carry_perf_p3, nek_p1sg, nek_p2sg, benn_p1sg, benn_p2sg, rajt_p1sg, rajt_p2sg, need_pres_s1,
  need_pres_s2, need_pres_s3, need_past_s1, need_past_s2, need_past_s3]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

end Stump2012.Wordlist
