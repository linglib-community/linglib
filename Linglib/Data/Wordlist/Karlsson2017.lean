module

public import Linglib.Data.Wordlist.Schema

/-!
# `Karlsson2017`: word forms

Auto-generated from `Linglib/Data/Wordlist/Karlsson2017.json` by `scripts/gen_wordlist.py`. Do not
edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
Karlsson2017.Wordlist`.
-/

@[expose] public section

namespace Karlsson2017.Wordlist

open CLDF.Wordlist

/-- The values of `Possessor` the source distinguishes. -/
inductive Possessor where
  /-- The possessive suffix of the 1st person singular, `1sg` in the source. -/
  | sg1
  /-- The possessive suffix of the 2nd person singular, `2sg` in the source. -/
  | sg2
  /-- The possessive suffix of the 3rd person singular, `3sg` in the source. -/
  | sg3
  /-- The possessive suffix of the 1st person plural, `1pl` in the source. -/
  | pl1
  /-- The possessive suffix of the 2nd person plural, `2pl` in the source. -/
  | pl2
  /-- The possessive suffix of the 3rd person plural, `3pl` in the source. -/
  | pl3
  deriving DecidableEq, Repr

/-- The values of `Infinitive` the source distinguishes. -/
inductive Infinitive where
  /-- The first infinitive, in -A, `a` in the source. -/
  | a
  /-- The second infinitive, in -e, `e` in the source. -/
  | e
  /-- The third infinitive, in -mA, `ma` in the source. -/
  | ma
  deriving DecidableEq, Repr

/-- The values of `Clitic` the source distinguishes. -/
inductive Clitic where
  /-- The interrogative clitic, `kO` in the source. -/
  | kO
  /-- The additive clitic, `kin` in the source. -/
  | kin
  /-- The clitic of familiarity, `hAn` in the source. -/
  | hAn
  /-- The negative-polarity clitic, `kAAn` in the source. -/
  | kAAn
  deriving DecidableEq, Repr

/-- A cell of the source's tables, by its Universal Dependencies features and the features UD
lacks. -/
structure Cell extends UD.MorphFeatures where
  /-- The `Possessor` feature. -/
  possessor : Flat Possessor := ⊥
  /-- The `Infinitive` feature. -/
  infinitive : Flat Infinitive := ⊥
  /-- The `Clitic` feature. -/
  clitic : Flat Clitic := ⊥
  deriving DecidableEq, Repr

/-- The nom cell, `Case=Nom`. -/
def nom : Cell := { case := ↑UD.Case.Nom }

/-- The gen cell, `Case=Gen`. -/
def gen : Cell := { case := ↑UD.Case.Gen }

/-- The acc cell, `Case=Acc`. -/
def acc : Cell := { case := ↑UD.Case.Acc }

/-- The part cell, `Case=Par`. -/
def part : Cell := { case := ↑UD.Case.Par }

/-- The ine cell, `Case=Ine`. -/
def ine : Cell := { case := ↑UD.Case.Ine }

/-- The ela cell, `Case=Ela`. -/
def ela : Cell := { case := ↑UD.Case.Ela }

/-- The ill cell, `Case=Ill`. -/
def ill : Cell := { case := ↑UD.Case.Ill }

/-- The ade cell, `Case=Ade`. -/
def ade : Cell := { case := ↑UD.Case.Ade }

/-- The abl cell, `Case=Abl`. -/
def abl : Cell := { case := ↑UD.Case.Abl }

/-- The all cell, `Case=All`. -/
def allat : Cell := { case := ↑UD.Case.All }

/-- The ess cell, `Case=Ess`. -/
def ess : Cell := { case := ↑UD.Case.Ess }

/-- The transl cell, `Case=Tra`. -/
def transl : Cell := { case := ↑UD.Case.Tra }

/-- The com 1sg possessor cell, `Case=Com|Possessor=1sg`. -/
def com_px1sg : Cell := { case := ↑UD.Case.Com, possessor := ↑Possessor.sg1 }

/-- The abess cell, `Case=Abe`. -/
def abess : Cell := { case := ↑UD.Case.Abe }

/-- The inst cell, `Case=Ins`. -/
def inst : Cell := { case := ↑UD.Case.Ins }

/-- The nom 1sg possessor cell, `Case=Nom|Possessor=1sg`. -/
def nom_px1sg : Cell := { case := ↑UD.Case.Nom, possessor := ↑Possessor.sg1 }

/-- The nom 2sg possessor cell, `Case=Nom|Possessor=2sg`. -/
def nom_px2sg : Cell := { case := ↑UD.Case.Nom, possessor := ↑Possessor.sg2 }

/-- The nom 3sg possessor cell, `Case=Nom|Possessor=3sg`. -/
def nom_px3sg : Cell := { case := ↑UD.Case.Nom, possessor := ↑Possessor.sg3 }

/-- The ela 1sg possessor cell, `Case=Ela|Possessor=1sg`. -/
def ela_px1sg : Cell := { case := ↑UD.Case.Ela, possessor := ↑Possessor.sg1 }

/-- The all 2sg possessor cell, `Case=All|Possessor=2sg`. -/
def allat_px2sg : Cell := { case := ↑UD.Case.All, possessor := ↑Possessor.sg2 }

/-- The ine 1sg possessor cell, `Case=Ine|Possessor=1sg`. -/
def ine_px1sg : Cell := { case := ↑UD.Case.Ine, possessor := ↑Possessor.sg1 }

/-- The ill 2sg possessor cell, `Case=Ill|Possessor=2sg`. -/
def ill_px2sg : Cell := { case := ↑UD.Case.Ill, possessor := ↑Possessor.sg2 }

/-- The nom a-infinitive cell, `Case=Nom|VerbForm=Inf|Infinitive=a`. -/
def nom_infa : Cell :=
  { case := ↑UD.Case.Nom, verbForm := ↑UD.VerbForm.Inf, infinitive := ↑Infinitive.a }

/-- The transl a-infinitive 1pl possessor cell, `Case=Tra|VerbForm=Inf|Infinitive=a|Possessor=1pl`.
-/
def transl_infa_px1pl : Cell :=
  { case := ↑UD.Case.Tra, verbForm := ↑UD.VerbForm.Inf, infinitive := ↑Infinitive.a,
    possessor := ↑Possessor.pl1 }

/-- The ine e-infinitive 1sg possessor cell, `Case=Ine|VerbForm=Inf|Infinitive=e|Possessor=1sg`. -/
def ine_infe_px1sg : Cell :=
  { case := ↑UD.Case.Ine, verbForm := ↑UD.VerbForm.Inf, infinitive := ↑Infinitive.e,
    possessor := ↑Possessor.sg1 }

/-- The ine e-infinitive 1pl possessor cell, `Case=Ine|VerbForm=Inf|Infinitive=e|Possessor=1pl`. -/
def ine_infe_px1pl : Cell :=
  { case := ↑UD.Case.Ine, verbForm := ↑UD.VerbForm.Inf, infinitive := ↑Infinitive.e,
    possessor := ↑Possessor.pl1 }

/-- The inst e-infinitive cell, `Case=Ins|VerbForm=Inf|Infinitive=e`. -/
def inst_infe : Cell :=
  { case := ↑UD.Case.Ins, verbForm := ↑UD.VerbForm.Inf, infinitive := ↑Infinitive.e }

/-- The ade ma-infinitive cell, `Case=Ade|VerbForm=Inf|Infinitive=ma`. -/
def ade_infma : Cell :=
  { case := ↑UD.Case.Ade, verbForm := ↑UD.VerbForm.Inf, infinitive := ↑Infinitive.ma }

/-- The abess ma-infinitive cell, `Case=Abe|VerbForm=Inf|Infinitive=ma`. -/
def abess_infma : Cell :=
  { case := ↑UD.Case.Abe, verbForm := ↑UD.VerbForm.Inf, infinitive := ↑Infinitive.ma }

/-- The ill ma-infinitive cell, `Case=Ill|VerbForm=Inf|Infinitive=ma`. -/
def ill_infma : Cell :=
  { case := ↑UD.Case.Ill, verbForm := ↑UD.VerbForm.Inf, infinitive := ↑Infinitive.ma }

/-- The transl a-infinitive 2sg possessor cell, `Case=Tra|VerbForm=Inf|Infinitive=a|Possessor=2sg`.
-/
def transl_infa_px2sg : Cell :=
  { case := ↑UD.Case.Tra, verbForm := ↑UD.VerbForm.Inf, infinitive := ↑Infinitive.a,
    possessor := ↑Possessor.sg2 }

/-- The ade 1sg possessor cell, `Case=Ade|Possessor=1sg`. -/
def ade_px1sg : Cell := { case := ↑UD.Case.Ade, possessor := ↑Possessor.sg1 }

/-- The ela 2sg possessor cell, `Case=Ela|Possessor=2sg`. -/
def ela_px2sg : Cell := { case := ↑UD.Case.Ela, possessor := ↑Possessor.sg2 }

/-- The ill 1sg possessor cell, `Case=Ill|Possessor=1sg`. -/
def ill_px1sg : Cell := { case := ↑UD.Case.Ill, possessor := ↑Possessor.sg1 }

/-- The nom 1pl possessor cell, `Case=Nom|Possessor=1pl`. -/
def nom_px1pl : Cell := { case := ↑UD.Case.Nom, possessor := ↑Possessor.pl1 }

/-- The nom 2pl possessor cell, `Case=Nom|Possessor=2pl`. -/
def nom_px2pl : Cell := { case := ↑UD.Case.Nom, possessor := ↑Possessor.pl2 }

/-- The nom 3pl possessor cell, `Case=Nom|Possessor=3pl`. -/
def nom_px3pl : Cell := { case := ↑UD.Case.Nom, possessor := ↑Possessor.pl3 }

/-- The part 3sg possessor cell, `Case=Par|Possessor=3sg`. -/
def part_px3sg : Cell := { case := ↑UD.Case.Par, possessor := ↑Possessor.sg3 }

/-- The ess 3pl possessor cell, `Case=Ess|Possessor=3pl`. -/
def ess_px3pl : Cell := { case := ↑UD.Case.Ess, possessor := ↑Possessor.pl3 }

/-- The transl a-infinitive 3sg possessor cell, `Case=Tra|VerbForm=Inf|Infinitive=a|Possessor=3sg`.
-/
def transl_infa_px3sg : Cell :=
  { case := ↑UD.Case.Tra, verbForm := ↑UD.VerbForm.Inf, infinitive := ↑Infinitive.a,
    possessor := ↑Possessor.sg3 }

/-- The ine 3pl possessor cell, `Case=Ine|Possessor=3pl`. -/
def ine_px3pl : Cell := { case := ↑UD.Case.Ine, possessor := ↑Possessor.pl3 }

/-- The ade 3sg possessor cell, `Case=Ade|Possessor=3sg`. -/
def ade_px3sg : Cell := { case := ↑UD.Case.Ade, possessor := ↑Possessor.sg3 }

/-- The all 3pl possessor cell, `Case=All|Possessor=3pl`. -/
def allat_px3pl : Cell := { case := ↑UD.Case.All, possessor := ↑Possessor.pl3 }

/-- The abl 3sg possessor cell, `Case=Abl|Possessor=3sg`. -/
def abl_px3sg : Cell := { case := ↑UD.Case.Abl, possessor := ↑Possessor.sg3 }

/-- The ill 3pl possessor cell, `Case=Ill|Possessor=3pl`. -/
def ill_px3pl : Cell := { case := ↑UD.Case.Ill, possessor := ↑Possessor.pl3 }

/-- The transl a-infinitive 1sg possessor cell, `Case=Tra|VerbForm=Inf|Infinitive=a|Possessor=1sg`.
-/
def transl_infa_px1sg : Cell :=
  { case := ↑UD.Case.Tra, verbForm := ↑UD.VerbForm.Inf, infinitive := ↑Infinitive.a,
    possessor := ↑Possessor.sg1 }

/-- The transl a-infinitive 2pl possessor cell, `Case=Tra|VerbForm=Inf|Infinitive=a|Possessor=2pl`.
-/
def transl_infa_px2pl : Cell :=
  { case := ↑UD.Case.Tra, verbForm := ↑UD.VerbForm.Inf, infinitive := ↑Infinitive.a,
    possessor := ↑Possessor.pl2 }

/-- The ine ma-infinitive cell, `Case=Ine|VerbForm=Inf|Infinitive=ma`. -/
def ine_infma : Cell :=
  { case := ↑UD.Case.Ine, verbForm := ↑UD.VerbForm.Inf, infinitive := ↑Infinitive.ma }

/-- The ela ma-infinitive cell, `Case=Ela|VerbForm=Inf|Infinitive=ma`. -/
def ela_infma : Cell :=
  { case := ↑UD.Case.Ela, verbForm := ↑UD.VerbForm.Inf, infinitive := ↑Infinitive.ma }

/-- The inst ma-infinitive cell, `Case=Ins|VerbForm=Inf|Infinitive=ma`. -/
def inst_infma : Cell :=
  { case := ↑UD.Case.Ins, verbForm := ↑UD.VerbForm.Inf, infinitive := ↑Infinitive.ma }

/-- The nom plural cell, `Case=Nom|Number=Plur`. -/
def nom_pl : Cell := { case := ↑UD.Case.Nom, number := ↑UD.Number.Plur }

/-- The nom -kin cell, `Case=Nom|Clitic=kin`. -/
def nom_kin : Cell := { case := ↑UD.Case.Nom, clitic := ↑Clitic.kin }

/-- The ela plural cell, `Case=Ela|Number=Plur`. -/
def ela_pl : Cell := { case := ↑UD.Case.Ela, number := ↑UD.Number.Plur }

/-- The ine -hAn cell, `Case=Ine|Clitic=hAn`. -/
def ine_han : Cell := { case := ↑UD.Case.Ine, clitic := ↑Clitic.hAn }

/-- The nom plural -kin cell, `Case=Nom|Number=Plur|Clitic=kin`. -/
def nom_pl_kin : Cell := { case := ↑UD.Case.Nom, number := ↑UD.Number.Plur, clitic := ↑Clitic.kin }

/-- The ine 2sg possessor -kO cell, `Case=Ine|Possessor=2sg|Clitic=kO`. -/
def ine_px2sg_ko : Cell :=
  { case := ↑UD.Case.Ine, possessor := ↑Possessor.sg2, clitic := ↑Clitic.kO }

/-- The ine plural 1pl possessor cell, `Case=Ine|Number=Plur|Possessor=1pl`. -/
def ine_pl_px1pl : Cell :=
  { case := ↑UD.Case.Ine, number := ↑UD.Number.Plur, possessor := ↑Possessor.pl1 }

/-- The ela plural -kAAn cell, `Case=Ela|Number=Plur|Clitic=kAAn`. -/
def ela_pl_kaan : Cell :=
  { case := ↑UD.Case.Ela, number := ↑UD.Number.Plur, clitic := ↑Clitic.kAAn }

/-- The ine plural 2pl possessor -kin cell, `Case=Ine|Number=Plur|Possessor=2pl|Clitic=kin`. -/
def ine_pl_px2pl_kin : Cell :=
  { case := ↑UD.Case.Ine, number := ↑UD.Number.Plur, possessor := ↑Possessor.pl2,
    clitic := ↑Clitic.kin }

/-- The abl -kO cell, `Case=Abl|Clitic=kO`. -/
def abl_ko : Cell := { case := ↑UD.Case.Abl, clitic := ↑Clitic.kO }

/-- The nom plural -kO cell, `Case=Nom|Number=Plur|Clitic=kO`. -/
def nom_pl_ko : Cell := { case := ↑UD.Case.Nom, number := ↑UD.Number.Plur, clitic := ↑Clitic.kO }

/-- The gen -hAn cell, `Case=Gen|Clitic=hAn`. -/
def gen_han : Cell := { case := ↑UD.Case.Gen, clitic := ↑Clitic.hAn }

/-- The nom 3sg possessor -kO cell, `Case=Nom|Possessor=3sg|Clitic=kO`. -/
def nom_px3sg_ko : Cell :=
  { case := ↑UD.Case.Nom, possessor := ↑Possessor.sg3, clitic := ↑Clitic.kO }

/-- The ade plural 1pl possessor cell, `Case=Ade|Number=Plur|Possessor=1pl`. -/
def ade_pl_px1pl : Cell :=
  { case := ↑UD.Case.Ade, number := ↑UD.Number.Plur, possessor := ↑Possessor.pl1 }

/-- The ine plural 1pl possessor -hAn cell, `Case=Ine|Number=Plur|Possessor=1pl|Clitic=hAn`. -/
def ine_pl_px1pl_han : Cell :=
  { case := ↑UD.Case.Ine, number := ↑UD.Number.Plur, possessor := ↑Possessor.pl1,
    clitic := ↑Clitic.hAn }

/-- The ill ma-infinitive -kO cell, `Case=Ill|VerbForm=Inf|Infinitive=ma|Clitic=kO`. -/
def ill_infma_ko : Cell :=
  { case := ↑UD.Case.Ill, verbForm := ↑UD.VerbForm.Inf, infinitive := ↑Infinitive.ma,
    clitic := ↑Clitic.kO }

/-- The ade ma-infinitive -kin cell, `Case=Ade|VerbForm=Inf|Infinitive=ma|Clitic=kin`. -/
def ade_infma_kin : Cell :=
  { case := ↑UD.Case.Ade, verbForm := ↑UD.VerbForm.Inf, infinitive := ↑Infinitive.ma,
    clitic := ↑Clitic.kin }

/-- The abess ma-infinitive -kAAn cell, `Case=Abe|VerbForm=Inf|Infinitive=ma|Clitic=kAAn`. -/
def abess_infma_kaan : Cell :=
  { case := ↑UD.Case.Abe, verbForm := ↑UD.VerbForm.Inf, infinitive := ↑Infinitive.ma,
    clitic := ↑Clitic.kAAn }

/-- The transl a-infinitive 3sg possessor -hAn cell,
`Case=Tra|VerbForm=Inf|Infinitive=a|Possessor=3sg|Clitic=hAn`. -/
def transl_infa_px3sg_han : Cell :=
  { case := ↑UD.Case.Tra, verbForm := ↑UD.VerbForm.Inf, infinitive := ↑Infinitive.a,
    possessor := ↑Possessor.sg3, clitic := ↑Clitic.hAn }

/-- The part 1pl possessor cell, `Case=Par|Possessor=1pl`. -/
def part_px1pl : Cell := { case := ↑UD.Case.Par, possessor := ↑Possessor.pl1 }

/-- The nom 2pl possessor -kin cell, `Case=Nom|Possessor=2pl|Clitic=kin`. -/
def nom_px2pl_kin : Cell :=
  { case := ↑UD.Case.Nom, possessor := ↑Possessor.pl2, clitic := ↑Clitic.kin }

/-- The abl 1sg possessor -hAn cell, `Case=Abl|Possessor=1sg|Clitic=hAn`. -/
def abl_px1sg_han : Cell :=
  { case := ↑UD.Case.Abl, possessor := ↑Possessor.sg1, clitic := ↑Clitic.hAn }

/-- The all 2sg possessor -kO cell, `Case=All|Possessor=2sg|Clitic=kO`. -/
def allat_px2sg_ko : Cell :=
  { case := ↑UD.Case.All, possessor := ↑Possessor.sg2, clitic := ↑Clitic.kO }

/-- The ill 1pl possessor cell, `Case=Ill|Possessor=1pl`. -/
def ill_px1pl : Cell := { case := ↑UD.Case.Ill, possessor := ↑Possessor.pl1 }

/-- The part plural 3sg possessor cell, `Case=Par|Number=Plur|Possessor=3sg`. -/
def part_pl_px3sg : Cell :=
  { case := ↑UD.Case.Par, number := ↑UD.Number.Plur, possessor := ↑Possessor.sg3 }

/-- The ill 3sg possessor cell, `Case=Ill|Possessor=3sg`. -/
def ill_px3sg : Cell := { case := ↑UD.Case.Ill, possessor := ↑Possessor.sg3 }

/-- The ill plural 3sg possessor cell, `Case=Ill|Number=Plur|Possessor=3sg`. -/
def ill_pl_px3sg : Cell :=
  { case := ↑UD.Case.Ill, number := ↑UD.Number.Plur, possessor := ↑Possessor.sg3 }

/-- The ine plural cell, `Case=Ine|Number=Plur`. -/
def ine_pl : Cell := { case := ↑UD.Case.Ine, number := ↑UD.Number.Plur }

/-- The ill plural cell, `Case=Ill|Number=Plur`. -/
def ill_pl : Cell := { case := ↑UD.Case.Ill, number := ↑UD.Number.Plur }

/-- The ess plural cell, `Case=Ess|Number=Plur`. -/
def ess_pl : Cell := { case := ↑UD.Case.Ess, number := ↑UD.Number.Plur }

/-- The all plural cell, `Case=All|Number=Plur`. -/
def allat_pl : Cell := { case := ↑UD.Case.All, number := ↑UD.Number.Plur }

/-- The transl plural cell, `Case=Tra|Number=Plur`. -/
def transl_pl : Cell := { case := ↑UD.Case.Tra, number := ↑UD.Number.Plur }

/-- The part plural cell, `Case=Par|Number=Plur`. -/
def part_pl : Cell := { case := ↑UD.Case.Par, number := ↑UD.Number.Plur }

/-- The gen plural cell, `Case=Gen|Number=Plur`. -/
def gen_pl : Cell := { case := ↑UD.Case.Gen, number := ↑UD.Number.Plur }

/-- The gen plural 3sg possessor cell, `Case=Gen|Number=Plur|Possessor=3sg`. -/
def gen_pl_px3sg : Cell :=
  { case := ↑UD.Case.Gen, number := ↑UD.Number.Plur, possessor := ↑Possessor.sg3 }

def Lexemes.car : Lexeme :=
  { id := "car", languageId := "finn1318", parameterId := "car" }

def Lexemes.him_her : Lexeme :=
  { id := "him_her", languageId := "finn1318", parameterId := "him_her" }

def Lexemes.milk : Lexeme :=
  { id := "milk", languageId := "finn1318", parameterId := "milk" }

def Lexemes.water : Lexeme :=
  { id := "water", languageId := "finn1318", parameterId := "water" }

def Lexemes.family : Lexeme :=
  { id := "family", languageId := "finn1318", parameterId := "family" }

def Lexemes.country : Lexeme :=
  { id := "country", languageId := "finn1318", parameterId := "country" }

def Lexemes.porvoo : Lexeme :=
  { id := "porvoo", languageId := "finn1318", parameterId := "porvoo" }

def Lexemes.table : Lexeme :=
  { id := "table", languageId := "finn1318", parameterId := "table" }

def Lexemes.teacher : Lexeme :=
  { id := "teacher", languageId := "finn1318", parameterId := "teacher" }

def Lexemes.wife : Lexeme :=
  { id := "wife", languageId := "finn1318", parameterId := "wife" }

def Lexemes.passport : Lexeme :=
  { id := "passport", languageId := "finn1318", parameterId := "passport" }

def Lexemes.foot : Lexeme :=
  { id := "foot", languageId := "finn1318", parameterId := "foot" }

def Lexemes.book : Lexeme :=
  { id := "book", languageId := "finn1318", parameterId := "book" }

def Lexemes.bottle : Lexeme :=
  { id := "bottle", languageId := "finn1318", parameterId := "bottle" }

def Lexemes.shelf : Lexeme :=
  { id := "shelf", languageId := "finn1318", parameterId := "shelf" }

def Lexemes.house : Lexeme :=
  { id := "house", languageId := "finn1318", parameterId := "house" }

def Lexemes.hand : Lexeme :=
  { id := "hand", languageId := "finn1318", parameterId := "hand" }

def Lexemes.say : Lexeme :=
  { id := "say", languageId := "finn1318", parameterId := "say" }

def Lexemes.eat : Lexeme :=
  { id := "eat", languageId := "finn1318", parameterId := "eat" }

def Lexemes.run : Lexeme :=
  { id := "run", languageId := "finn1318", parameterId := "run" }

def Lexemes.speak : Lexeme :=
  { id := "speak", languageId := "finn1318", parameterId := "speak" }

def Lexemes.bag : Lexeme :=
  { id := "bag", languageId := "finn1318", parameterId := "bag" }

def Lexemes.guest : Lexeme :=
  { id := "guest", languageId := "finn1318", parameterId := "guest" }

def Lexemes.get : Lexeme :=
  { id := "get", languageId := "finn1318", parameterId := "get" }

def Lexemes.father : Lexeme :=
  { id := "father", languageId := "finn1318", parameterId := "father" }

def Lexemes.mother : Lexeme :=
  { id := "mother", languageId := "finn1318", parameterId := "mother" }

def Lexemes.live : Lexeme :=
  { id := "live", languageId := "finn1318", parameterId := "live" }

def Lexemes.meet : Lexeme :=
  { id := "meet", languageId := "finn1318", parameterId := "meet" }

def Lexemes.drink : Lexeme :=
  { id := "drink", languageId := "finn1318", parameterId := "drink" }

def Lexemes.be : Lexeme :=
  { id := "be", languageId := "finn1318", parameterId := "be" }

def Lexemes.rest : Lexeme :=
  { id := "rest", languageId := "finn1318", parameterId := "rest" }

def Lexemes.pull : Lexeme :=
  { id := "pull", languageId := "finn1318", parameterId := "pull" }

def Lexemes.mention : Lexeme :=
  { id := "mention", languageId := "finn1318", parameterId := "mention" }

def Lexemes.do : Lexeme :=
  { id := "do", languageId := "finn1318", parameterId := "do" }

def Lexemes.come : Lexeme :=
  { id := "come", languageId := "finn1318", parameterId := "come" }

def Lexemes.learn : Lexeme :=
  { id := "learn", languageId := "finn1318", parameterId := "learn" }

def Lexemes.son : Lexeme :=
  { id := "son", languageId := "finn1318", parameterId := "son" }

def Lexemes.ring : Lexeme :=
  { id := "ring", languageId := "finn1318", parameterId := "ring" }

def Lexemes.head : Lexeme :=
  { id := "head", languageId := "finn1318", parameterId := "head" }

def Lexemes.fish : Lexeme :=
  { id := "fish", languageId := "finn1318", parameterId := "fish" }

def Lexemes.girl : Lexeme :=
  { id := "girl", languageId := "finn1318", parameterId := "girl" }

def Lexemes.cross : Lexeme :=
  { id := "cross", languageId := "finn1318", parameterId := "cross" }

def Lexemes.stone : Lexeme :=
  { id := "stone", languageId := "finn1318", parameterId := "stone" }

def Lexemes.child : Lexeme :=
  { id := "child", languageId := "finn1318", parameterId := "child" }

def Lexemes.boy : Lexeme :=
  { id := "boy", languageId := "finn1318", parameterId := "boy" }

def Lexemes.day : Lexeme :=
  { id := "day", languageId := "finn1318", parameterId := "day" }

def Lexemes.road : Lexeme :=
  { id := "road", languageId := "finn1318", parameterId := "road" }

def Lexemes.obstacle : Lexeme :=
  { id := "obstacle", languageId := "finn1318", parameterId := "obstacle" }

def Lexemes.state : Lexeme :=
  { id := "state", languageId := "finn1318", parameterId := "state" }

def auto : Form Cell :=
  { id := "karlsson2017_auto"
    lexeme := Lexemes.car
    cell := nom
    form := "auto"
    segments := ["auto"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def auton : Form Cell :=
  { id := "karlsson2017_auton"
    lexeme := Lexemes.car
    cell := gen
    form := "auton"
    segments := ["auto", "n"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def hanet : Form Cell :=
  { id := "karlsson2017_hanet"
    lexeme := Lexemes.him_her
    cell := acc
    form := "hänet"
    segments := ["häne", "t"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def maitoa : Form Cell :=
  { id := "karlsson2017_maitoa"
    lexeme := Lexemes.milk
    cell := part
    form := "maitoa"
    segments := ["maito", "a"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def vetta : Form Cell :=
  { id := "karlsson2017_vetta"
    lexeme := Lexemes.water
    cell := part
    form := "vettä"
    segments := ["vet", "tä"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def perhetta : Form Cell :=
  { id := "karlsson2017_perhetta"
    lexeme := Lexemes.family
    cell := part
    form := "perhettä"
    segments := ["perhe", "ttä"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def autossa : Form Cell :=
  { id := "karlsson2017_autossa"
    lexeme := Lexemes.car
    cell := ine
    form := "autossa"
    segments := ["auto", "ssa"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def autosta : Form Cell :=
  { id := "karlsson2017_autosta"
    lexeme := Lexemes.car
    cell := ela
    form := "autosta"
    segments := ["auto", "sta"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def autoon : Form Cell :=
  { id := "karlsson2017_autoon"
    lexeme := Lexemes.car
    cell := ill
    form := "autoon"
    segments := ["auto", "on"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def maahan : Form Cell :=
  { id := "karlsson2017_maahan"
    lexeme := Lexemes.country
    cell := ill
    form := "maahan"
    segments := ["maa", "han"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def porvooseen : Form Cell :=
  { id := "karlsson2017_porvooseen"
    lexeme := Lexemes.porvoo
    cell := ill
    form := "Porvooseen"
    segments := ["Porvoo", "seen"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def poydalla : Form Cell :=
  { id := "karlsson2017_poydalla"
    lexeme := Lexemes.table
    cell := ade
    form := "pöydällä"
    segments := ["pöydä", "llä"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def poydalta : Form Cell :=
  { id := "karlsson2017_poydalta"
    lexeme := Lexemes.table
    cell := abl
    form := "pöydältä"
    segments := ["pöydä", "ltä"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def poydalle : Form Cell :=
  { id := "karlsson2017_poydalle"
    lexeme := Lexemes.table
    cell := allat
    form := "pöydälle"
    segments := ["pöydä", "lle"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def opettajana : Form Cell :=
  { id := "karlsson2017_opettajana"
    lexeme := Lexemes.teacher
    cell := ess
    form := "opettajana"
    segments := ["opettaja", "na"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def opettajaksi : Form Cell :=
  { id := "karlsson2017_opettajaksi"
    lexeme := Lexemes.teacher
    cell := transl
    form := "opettajaksi"
    segments := ["opettaja", "ksi"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def vaimoineni : Form Cell :=
  { id := "karlsson2017_vaimoineni"
    lexeme := Lexemes.wife
    cell := com_px1sg
    form := "vaimoineni"
    segments := ["vaimo", "ine", "ni"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def passitta : Form Cell :=
  { id := "karlsson2017_passitta"
    lexeme := Lexemes.passport
    cell := abess
    form := "passitta"
    segments := ["passi", "tta"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def jalan : Form Cell :=
  { id := "karlsson2017_jalan"
    lexeme := Lexemes.foot
    cell := inst
    form := "jalan"
    segments := ["jala", "n"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def kirjani : Form Cell :=
  { id := "karlsson2017_kirjani"
    lexeme := Lexemes.book
    cell := nom_px1sg
    form := "kirjani"
    segments := ["kirja", "ni"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def kirjasi : Form Cell :=
  { id := "karlsson2017_kirjasi"
    lexeme := Lexemes.book
    cell := nom_px2sg
    form := "kirjasi"
    segments := ["kirja", "si"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def kirjansa : Form Cell :=
  { id := "karlsson2017_kirjansa"
    lexeme := Lexemes.book
    cell := nom_px3sg
    form := "kirjansa"
    segments := ["kirja", "nsa"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def pullo : Form Cell :=
  { id := "karlsson2017_pullo"
    lexeme := Lexemes.bottle
    cell := nom
    form := "pullo"
    segments := ["pullo"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def pullossa : Form Cell :=
  { id := "karlsson2017_pullossa"
    lexeme := Lexemes.bottle
    cell := ine
    form := "pullossa"
    segments := ["pullo", "ssa"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def pulloni : Form Cell :=
  { id := "karlsson2017_pulloni"
    lexeme := Lexemes.bottle
    cell := nom_px1sg
    form := "pulloni"
    segments := ["pullo", "ni"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def pullostani : Form Cell :=
  { id := "karlsson2017_pullostani"
    lexeme := Lexemes.bottle
    cell := ela_px1sg
    form := "pullostani"
    segments := ["pullo", "sta", "ni"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def hyllyssa : Form Cell :=
  { id := "karlsson2017_hyllyssa"
    lexeme := Lexemes.shelf
    cell := ine
    form := "hyllyssä"
    segments := ["hylly", "ssä"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def hyllylla : Form Cell :=
  { id := "karlsson2017_hyllylla"
    lexeme := Lexemes.shelf
    cell := ade
    form := "hyllyllä"
    segments := ["hylly", "llä"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def hyllysi : Form Cell :=
  { id := "karlsson2017_hyllysi"
    lexeme := Lexemes.shelf
    cell := nom_px2sg
    form := "hyllysi"
    segments := ["hylly", "si"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def hyllyllesi : Form Cell :=
  { id := "karlsson2017_hyllyllesi"
    lexeme := Lexemes.shelf
    cell := allat_px2sg
    form := "hyllyllesi"
    segments := ["hylly", "lle", "si"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def taloon : Form Cell :=
  { id := "karlsson2017_taloon"
    lexeme := Lexemes.house
    cell := ill
    form := "taloon"
    segments := ["talo", "on"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def hyllynsa : Form Cell :=
  { id := "karlsson2017_hyllynsa"
    lexeme := Lexemes.shelf
    cell := nom_px3sg
    form := "hyllynsä"
    segments := ["hylly", "nsä"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def kadessani : Form Cell :=
  { id := "karlsson2017_kadessani"
    lexeme := Lexemes.hand
    cell := ine_px1sg
    form := "kädessäni"
    segments := ["käde", "ssä", "ni"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def kateen : Form Cell :=
  { id := "karlsson2017_kateen"
    lexeme := Lexemes.hand
    cell := ill
    form := "käteen"
    segments := ["käte", "en"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def kateesi : Form Cell :=
  { id := "karlsson2017_kateesi"
    lexeme := Lexemes.hand
    cell := ill_px2sg
    form := "käteesi"
    segments := ["käte", "e", "si"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def katta : Form Cell :=
  { id := "karlsson2017_katta"
    lexeme := Lexemes.hand
    cell := part
    form := "kättä"
    segments := ["kät", "tä"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def sanoa : Form Cell :=
  { id := "karlsson2017_sanoa"
    lexeme := Lexemes.say
    cell := nom_infa
    form := "sanoa"
    segments := ["sano", "a"]
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ] }

def syoda : Form Cell :=
  { id := "karlsson2017_syoda"
    lexeme := Lexemes.eat
    cell := nom_infa
    form := "syödä"
    segments := ["syö", "dä"]
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ] }

def juosta : Form Cell :=
  { id := "karlsson2017_juosta"
    lexeme := Lexemes.run
    cell := nom_infa
    form := "juosta"
    segments := ["juos", "ta"]
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ] }

def juostaksemme : Form Cell :=
  { id := "karlsson2017_juostaksemme"
    lexeme := Lexemes.run
    cell := transl_infa_px1pl
    form := "juostaksemme"
    segments := ["juos", "ta", "kse", "mme"]
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ] }

def sanoessani : Form Cell :=
  { id := "karlsson2017_sanoessani"
    lexeme := Lexemes.say
    cell := ine_infe_px1sg
    form := "sanoessani"
    segments := ["sano", "e", "ssa", "ni"]
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ] }

def syodessamme : Form Cell :=
  { id := "karlsson2017_syodessamme"
    lexeme := Lexemes.eat
    cell := ine_infe_px1pl
    form := "syödessämme"
    segments := ["syö", "de", "ssä", "mme"]
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ] }

def juosten : Form Cell :=
  { id := "karlsson2017_juosten"
    lexeme := Lexemes.run
    cell := inst_infe
    form := "juosten"
    segments := ["juos", "te", "n"]
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ] }

def syomalla : Form Cell :=
  { id := "karlsson2017_syomalla"
    lexeme := Lexemes.eat
    cell := ade_infma
    form := "syömällä"
    segments := ["syö", "mä", "llä"]
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ] }

def sanomatta : Form Cell :=
  { id := "karlsson2017_sanomatta"
    lexeme := Lexemes.say
    cell := abess_infma
    form := "sanomatta"
    segments := ["sano", "ma", "tta"]
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ] }

def sanomaan : Form Cell :=
  { id := "karlsson2017_sanomaan"
    lexeme := Lexemes.say
    cell := ill_infma
    form := "sanomaan"
    segments := ["sano", "ma", "an"]
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ] }

def puhuaksesi : Form Cell :=
  { id := "karlsson2017_puhuaksesi"
    lexeme := Lexemes.speak
    cell := transl_infa_px2sg
    form := "puhuaksesi"
    segments := ["puhu", "a", "kse", "si"]
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ] }

def puhumalla : Form Cell :=
  { id := "karlsson2017_puhumalla"
    lexeme := Lexemes.speak
    cell := ade_infma
    form := "puhumalla"
    segments := ["puhu", "ma", "lla"]
    source := [
      ⟨"karlsson-2017", "§3.3"⟩
    ] }

def autollani : Form Cell :=
  { id := "karlsson2017_autollani"
    lexeme := Lexemes.car
    cell := ade_px1sg
    form := "autollani"
    segments := ["auto", "lla", "ni"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def autostasi : Form Cell :=
  { id := "karlsson2017_autostasi"
    lexeme := Lexemes.car
    cell := ela_px2sg
    form := "autostasi"
    segments := ["auto", "sta", "si"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def autooni : Form Cell :=
  { id := "karlsson2017_autooni"
    lexeme := Lexemes.car
    cell := ill_px1sg
    form := "autooni"
    segments := ["auto", "o", "ni"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def laukkuni : Form Cell :=
  { id := "karlsson2017_laukkuni"
    lexeme := Lexemes.bag
    cell := nom_px1sg
    form := "laukkuni"
    segments := ["laukku", "ni"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def laukkusi : Form Cell :=
  { id := "karlsson2017_laukkusi"
    lexeme := Lexemes.bag
    cell := nom_px2sg
    form := "laukkusi"
    segments := ["laukku", "si"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def laukkunsa_3sg : Form Cell :=
  { id := "karlsson2017_laukkunsa_3sg"
    lexeme := Lexemes.bag
    cell := nom_px3sg
    form := "laukkunsa"
    segments := ["laukku", "nsa"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def laukkumme : Form Cell :=
  { id := "karlsson2017_laukkumme"
    lexeme := Lexemes.bag
    cell := nom_px1pl
    form := "laukkumme"
    segments := ["laukku", "mme"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def laukkunne : Form Cell :=
  { id := "karlsson2017_laukkunne"
    lexeme := Lexemes.bag
    cell := nom_px2pl
    form := "laukkunne"
    segments := ["laukku", "nne"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def laukkunsa_3pl : Form Cell :=
  { id := "karlsson2017_laukkunsa_3pl"
    lexeme := Lexemes.bag
    cell := nom_px3pl
    form := "laukkunsa"
    segments := ["laukku", "nsa"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def taloaan : Form Cell :=
  { id := "karlsson2017_taloaan"
    lexeme := Lexemes.house
    cell := part_px3sg
    form := "taloaan"
    segments := ["talo", "a", "an"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def vieraanaan : Form Cell :=
  { id := "karlsson2017_vieraanaan"
    lexeme := Lexemes.guest
    cell := ess_px3pl
    form := "vieraanaan"
    segments := ["vieraa", "na", "an"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def saadakseen : Form Cell :=
  { id := "karlsson2017_saadakseen"
    lexeme := Lexemes.get
    cell := transl_infa_px3sg
    form := "saadakseen"
    segments := ["saa", "da", "kse", "en"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def talossaan : Form Cell :=
  { id := "karlsson2017_talossaan"
    lexeme := Lexemes.house
    cell := ine_px3pl
    form := "talossaan"
    segments := ["talo", "ssa", "an"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def autollaan : Form Cell :=
  { id := "karlsson2017_autollaan"
    lexeme := Lexemes.car
    cell := ade_px3sg
    form := "autollaan"
    segments := ["auto", "lla", "an"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def isalleen : Form Cell :=
  { id := "karlsson2017_isalleen"
    lexeme := Lexemes.father
    cell := allat_px3pl
    form := "isälleen"
    segments := ["isä", "lle", "en"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def aidiltaan : Form Cell :=
  { id := "karlsson2017_aidiltaan"
    lexeme := Lexemes.mother
    cell := abl_px3sg
    form := "äidiltään"
    segments := ["äidi", "ltä", "än"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def aitiaan : Form Cell :=
  { id := "karlsson2017_aitiaan"
    lexeme := Lexemes.mother
    cell := part_px3sg
    form := "äitiään"
    segments := ["äiti", "ä", "än"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def talonsa : Form Cell :=
  { id := "karlsson2017_talonsa"
    lexeme := Lexemes.house
    cell := ill_px3pl
    form := "taloonsa"
    segments := ["talo", "o", "nsa"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def autonsa : Form Cell :=
  { id := "karlsson2017_autonsa"
    lexeme := Lexemes.car
    cell := nom_px3sg
    form := "autonsa"
    segments := ["auto", "nsa"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def isaansa : Form Cell :=
  { id := "karlsson2017_isaansa"
    lexeme := Lexemes.father
    cell := ill_px3pl
    form := "isäänsä"
    segments := ["isä", "ä", "nsä"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def aitinsa : Form Cell :=
  { id := "karlsson2017_aitinsa"
    lexeme := Lexemes.mother
    cell := nom_px3sg
    form := "äitinsä"
    segments := ["äiti", "nsä"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def sanoakseni : Form Cell :=
  { id := "karlsson2017_sanoakseni"
    lexeme := Lexemes.say
    cell := transl_infa_px1sg
    form := "sanoakseni"
    segments := ["sano", "a", "kse", "ni"]
    source := [
      ⟨"karlsson-2017", "§22.2.2"⟩
    ] }

def elaaksemme : Form Cell :=
  { id := "karlsson2017_elaaksemme"
    lexeme := Lexemes.live
    cell := transl_infa_px1pl
    form := "elääksemme"
    segments := ["elä", "ä", "kse", "mme"]
    source := [
      ⟨"karlsson-2017", "§22.2.2"⟩
    ] }

def tavataksesi : Form Cell :=
  { id := "karlsson2017_tavataksesi"
    lexeme := Lexemes.meet
    cell := transl_infa_px2sg
    form := "tavataksesi"
    segments := ["tavat", "a", "kse", "si"]
    source := [
      ⟨"karlsson-2017", "§22.2.2"⟩
    ] }

def juodakseen : Form Cell :=
  { id := "karlsson2017_juodakseen"
    lexeme := Lexemes.drink
    cell := transl_infa_px3sg
    form := "juodakseen"
    segments := ["juo", "da", "kse", "en"]
    source := [
      ⟨"karlsson-2017", "§22.2.2"⟩
    ] }

def ollaksenne : Form Cell :=
  { id := "karlsson2017_ollaksenne"
    lexeme := Lexemes.be
    cell := transl_infa_px2pl
    form := "ollaksenne"
    segments := ["ol", "la", "kse", "nne"]
    source := [
      ⟨"karlsson-2017", "§22.2.2"⟩
    ] }

def lepaamassa : Form Cell :=
  { id := "karlsson2017_lepaamassa"
    lexeme := Lexemes.rest
    cell := ine_infma
    form := "lepäämässä"
    segments := ["lepää", "mä", "ssä"]
    source := [
      ⟨"karlsson-2017", "§22.4.1"⟩
    ] }

def lepaamaan : Form Cell :=
  { id := "karlsson2017_lepaamaan"
    lexeme := Lexemes.rest
    cell := ill_infma
    form := "lepäämään"
    segments := ["lepää", "mä", "än"]
    source := [
      ⟨"karlsson-2017", "§22.4.1"⟩
    ] }

def vetamalla : Form Cell :=
  { id := "karlsson2017_vetamalla"
    lexeme := Lexemes.pull
    cell := ade_infma
    form := "vetämällä"
    segments := ["vetä", "mä", "llä"]
    source := [
      ⟨"karlsson-2017", "§22.4.1"⟩
    ] }

def mainitsematta : Form Cell :=
  { id := "karlsson2017_mainitsematta"
    lexeme := Lexemes.mention
    cell := abess_infma
    form := "mainitsematta"
    segments := ["mainitse", "ma", "tta"]
    source := [
      ⟨"karlsson-2017", "§22.4.1"⟩
    ] }

def tekemasta : Form Cell :=
  { id := "karlsson2017_tekemasta"
    lexeme := Lexemes.do
    cell := ela_infma
    form := "tekemästä"
    segments := ["teke", "mä", "stä"]
    source := [
      ⟨"karlsson-2017", "§22.4.1"⟩
    ] }

def tuleman : Form Cell :=
  { id := "karlsson2017_tuleman"
    lexeme := Lexemes.come
    cell := inst_infma
    form := "tuleman"
    segments := ["tule", "ma", "n"]
    source := [
      ⟨"karlsson-2017", "§22.4.1"⟩
    ] }

def pullot : Form Cell :=
  { id := "karlsson2017_pullot"
    lexeme := Lexemes.bottle
    cell := nom_pl
    form := "pullot"
    segments := ["pullo", "t"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def pullokin : Form Cell :=
  { id := "karlsson2017_pullokin"
    lexeme := Lexemes.bottle
    cell := nom_kin
    form := "pullokin"
    segments := ["pullo", "kin"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def pulloista : Form Cell :=
  { id := "karlsson2017_pulloista"
    lexeme := Lexemes.bottle
    cell := ela_pl
    form := "pulloista"
    segments := ["pullo", "i", "sta"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def pullossahan : Form Cell :=
  { id := "karlsson2017_pullossahan"
    lexeme := Lexemes.bottle
    cell := ine_han
    form := "pullossahan"
    segments := ["pullo", "ssa", "han"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def pullotkin : Form Cell :=
  { id := "karlsson2017_pullotkin"
    lexeme := Lexemes.bottle
    cell := nom_pl_kin
    form := "pullotkin"
    segments := ["pullo", "t", "kin"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def pullossasiko : Form Cell :=
  { id := "karlsson2017_pullossasiko"
    lexeme := Lexemes.bottle
    cell := ine_px2sg_ko
    form := "pullossasiko"
    segments := ["pullo", "ssa", "si", "ko"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def pulloissamme : Form Cell :=
  { id := "karlsson2017_pulloissamme"
    lexeme := Lexemes.bottle
    cell := ine_pl_px1pl
    form := "pulloissamme"
    segments := ["pullo", "i", "ssa", "mme"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def pulloistakaan : Form Cell :=
  { id := "karlsson2017_pulloistakaan"
    lexeme := Lexemes.bottle
    cell := ela_pl_kaan
    form := "pulloistakaan"
    segments := ["pullo", "i", "sta", "kaan"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def pulloissannekin : Form Cell :=
  { id := "karlsson2017_pulloissannekin"
    lexeme := Lexemes.bottle
    cell := ine_pl_px2pl_kin
    form := "pulloissannekin"
    segments := ["pullo", "i", "ssa", "nne", "kin"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def hyllyltako : Form Cell :=
  { id := "karlsson2017_hyllyltako"
    lexeme := Lexemes.shelf
    cell := abl_ko
    form := "hyllyltäkö"
    segments := ["hylly", "ltä", "kö"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def hyllytko : Form Cell :=
  { id := "karlsson2017_hyllytko"
    lexeme := Lexemes.shelf
    cell := nom_pl_ko
    form := "hyllytkö"
    segments := ["hylly", "t", "kö"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def hyllynhan : Form Cell :=
  { id := "karlsson2017_hyllynhan"
    lexeme := Lexemes.shelf
    cell := gen_han
    form := "hyllynhän"
    segments := ["hylly", "n", "hän"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def talonsako : Form Cell :=
  { id := "karlsson2017_talonsako"
    lexeme := Lexemes.house
    cell := nom_px3sg_ko
    form := "talonsako"
    segments := ["talo", "nsa", "ko"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def hyllyillamme : Form Cell :=
  { id := "karlsson2017_hyllyillamme"
    lexeme := Lexemes.shelf
    cell := ade_pl_px1pl
    form := "hyllyillämme"
    segments := ["hylly", "i", "llä", "mme"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def kasi : Form Cell :=
  { id := "karlsson2017_kasi"
    lexeme := Lexemes.hand
    cell := nom
    form := "käsi"
    segments := ["käsi"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def kadet : Form Cell :=
  { id := "karlsson2017_kadet"
    lexeme := Lexemes.hand
    cell := nom_pl
    form := "kädet"
    segments := ["käde", "t"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def kasissammehan : Form Cell :=
  { id := "karlsson2017_kasissammehan"
    lexeme := Lexemes.hand
    cell := ine_pl_px1pl_han
    form := "käsissämmehän"
    segments := ["käs", "i", "ssä", "mme", "hän"]
    source := [
      ⟨"karlsson-2017", "§3.1"⟩
    ] }

def lepaamaanko : Form Cell :=
  { id := "karlsson2017_lepaamaanko"
    lexeme := Lexemes.rest
    cell := ill_infma_ko
    form := "lepäämäänkö"
    segments := ["lepää", "mä", "än", "kö"]
    source := [
      ⟨"karlsson-2017", "§22.4.1"⟩
    ] }

def vetamallakin : Form Cell :=
  { id := "karlsson2017_vetamallakin"
    lexeme := Lexemes.pull
    cell := ade_infma_kin
    form := "vetämälläkin"
    segments := ["vetä", "mä", "llä", "kin"]
    source := [
      ⟨"karlsson-2017", "§22.4.1"⟩
    ] }

def mainitsemattakaan : Form Cell :=
  { id := "karlsson2017_mainitsemattakaan"
    lexeme := Lexemes.mention
    cell := abess_infma_kaan
    form := "mainitsemattakaan"
    segments := ["mainitse", "ma", "tta", "kaan"]
    source := [
      ⟨"karlsson-2017", "§22.4.1"⟩
    ] }

def oppiakseenhan : Form Cell :=
  { id := "karlsson2017_oppiakseenhan"
    lexeme := Lexemes.learn
    cell := transl_infa_px3sg_han
    form := "oppiakseenhan"
    segments := ["oppi", "a", "kse", "en", "han"]
    source := [
      ⟨"karlsson-2017", "§22.2.2"⟩
    ] }

def maatamme : Form Cell :=
  { id := "karlsson2017_maatamme"
    lexeme := Lexemes.country
    cell := part_px1pl
    form := "maatamme"
    segments := ["maa", "ta", "mme"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def poikannekin : Form Cell :=
  { id := "karlsson2017_poikannekin"
    lexeme := Lexemes.son
    cell := nom_px2pl_kin
    form := "poikannekin"
    segments := ["poika", "nne", "kin"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def aidiltanihan : Form Cell :=
  { id := "karlsson2017_aidiltanihan"
    lexeme := Lexemes.mother
    cell := abl_px1sg_han
    form := "äidiltänihän"
    segments := ["äidi", "ltä", "ni", "hän"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def isallesiko : Form Cell :=
  { id := "karlsson2017_isallesiko"
    lexeme := Lexemes.father
    cell := allat_px2sg_ko
    form := "isällesikö"
    segments := ["isä", "lle", "si", "kö"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def maahamme : Form Cell :=
  { id := "karlsson2017_maahamme"
    lexeme := Lexemes.country
    cell := ill_px1pl
    form := "maahamme"
    segments := ["maa", "ha", "mme"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def perhettaan : Form Cell :=
  { id := "karlsson2017_perhettaan"
    lexeme := Lexemes.family
    cell := part_px3sg
    form := "perhettään"
    segments := ["perhe", "ttä", "än"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def talojaan : Form Cell :=
  { id := "karlsson2017_talojaan"
    lexeme := Lexemes.house
    cell := part_pl_px3sg
    form := "talojaan"
    segments := ["talo", "j", "a", "an"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def renkaitaan : Form Cell :=
  { id := "karlsson2017_renkaitaan"
    lexeme := Lexemes.ring
    cell := part_pl_px3sg
    form := "renkaitaan"
    segments := ["renka", "i", "ta", "an"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def paataan : Form Cell :=
  { id := "karlsson2017_paataan"
    lexeme := Lexemes.head
    cell := part_px3sg
    form := "päätään"
    segments := ["pää", "tä", "än"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def taloansa : Form Cell :=
  { id := "karlsson2017_taloansa"
    lexeme := Lexemes.house
    cell := part_px3sg
    form := "taloansa"
    segments := ["talo", "a", "nsa"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def kalansa : Form Cell :=
  { id := "karlsson2017_kalansa"
    lexeme := Lexemes.fish
    cell := nom_px3sg
    form := "kalansa"
    segments := ["kala", "nsa"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def kalaansa_ill : Form Cell :=
  { id := "karlsson2017_kalaansa_ill"
    lexeme := Lexemes.fish
    cell := ill_px3sg
    form := "kalaansa"
    segments := ["kala", "a", "nsa"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def kalaansa_part : Form Cell :=
  { id := "karlsson2017_kalaansa_part"
    lexeme := Lexemes.fish
    cell := part_px3sg
    form := "kalaansa"
    segments := ["kala", "a", "nsa"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def kaloihinsa : Form Cell :=
  { id := "karlsson2017_kaloihinsa"
    lexeme := Lexemes.fish
    cell := ill_pl_px3sg
    form := "kaloihinsa"
    segments := ["kalo", "i", "hi", "nsa"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

def taloissa : Form Cell :=
  { id := "karlsson2017_taloissa"
    lexeme := Lexemes.house
    cell := ine_pl
    form := "taloissa"
    segments := ["talo", "i", "ssa"]
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ] }

def taloihin : Form Cell :=
  { id := "karlsson2017_taloihin"
    lexeme := Lexemes.house
    cell := ill_pl
    form := "taloihin"
    segments := ["talo", "i", "hin"]
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ] }

def taloina : Form Cell :=
  { id := "karlsson2017_taloina"
    lexeme := Lexemes.house
    cell := ess_pl
    form := "taloina"
    segments := ["talo", "i", "na"]
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ] }

def taloille : Form Cell :=
  { id := "karlsson2017_taloille"
    lexeme := Lexemes.house
    cell := allat_pl
    form := "taloille"
    segments := ["talo", "i", "lle"]
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ] }

def taloiksi : Form Cell :=
  { id := "karlsson2017_taloiksi"
    lexeme := Lexemes.house
    cell := transl_pl
    form := "taloiksi"
    segments := ["talo", "i", "ksi"]
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ] }

def hyllyja : Form Cell :=
  { id := "karlsson2017_hyllyja"
    lexeme := Lexemes.shelf
    cell := part_pl
    form := "hyllyjä"
    segments := ["hylly", "j", "ä"]
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ] }

def hyllyjen : Form Cell :=
  { id := "karlsson2017_hyllyjen"
    lexeme := Lexemes.shelf
    cell := gen_pl
    form := "hyllyjen"
    segments := ["hylly", "j", "en"]
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ] }

def pulloja : Form Cell :=
  { id := "karlsson2017_pulloja"
    lexeme := Lexemes.bottle
    cell := part_pl
    form := "pulloja"
    segments := ["pullo", "j", "a"]
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ] }

def pullojen : Form Cell :=
  { id := "karlsson2017_pullojen"
    lexeme := Lexemes.bottle
    cell := gen_pl
    form := "pullojen"
    segments := ["pullo", "j", "en"]
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ] }

def tyttoja : Form Cell :=
  { id := "karlsson2017_tyttoja"
    lexeme := Lexemes.girl
    cell := part_pl
    form := "tyttöjä"
    segments := ["tyttö", "j", "ä"]
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ] }

def tyttojen : Form Cell :=
  { id := "karlsson2017_tyttojen"
    lexeme := Lexemes.girl
    cell := gen_pl
    form := "tyttöjen"
    segments := ["tyttö", "j", "en"]
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ] }

def pulloissa : Form Cell :=
  { id := "karlsson2017_pulloissa"
    lexeme := Lexemes.bottle
    cell := ine_pl
    form := "pulloissa"
    segments := ["pullo", "i", "ssa"]
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ] }

def maissa : Form Cell :=
  { id := "karlsson2017_maissa"
    lexeme := Lexemes.country
    cell := ine_pl
    form := "maissa"
    segments := ["ma", "i", "ssa"]
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ] }

def risteissa : Form Cell :=
  { id := "karlsson2017_risteissa"
    lexeme := Lexemes.cross
    cell := ine_pl
    form := "risteissä"
    segments := ["riste", "i", "ssä"]
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ] }

def kivissa : Form Cell :=
  { id := "karlsson2017_kivissa"
    lexeme := Lexemes.stone
    cell := ine_pl
    form := "kivissä"
    segments := ["kiv", "i", "ssä"]
    source := [
      ⟨"karlsson-2017", "§5.4"⟩
    ] }

def lapsia : Form Cell :=
  { id := "karlsson2017_lapsia"
    lexeme := Lexemes.child
    cell := part_pl
    form := "lapsia"
    segments := ["laps", "i", "a"]
    source := [
      ⟨"karlsson-2017", "§8.4"⟩
    ] }

def talojen : Form Cell :=
  { id := "karlsson2017_talojen"
    lexeme := Lexemes.house
    cell := gen_pl
    form := "talojen"
    segments := ["talo", "j", "en"]
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ] }

def poikia : Form Cell :=
  { id := "karlsson2017_poikia"
    lexeme := Lexemes.boy
    cell := part_pl
    form := "poikia"
    segments := ["poik", "i", "a"]
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ] }

def poikien : Form Cell :=
  { id := "karlsson2017_poikien"
    lexeme := Lexemes.boy
    cell := gen_pl
    form := "poikien"
    segments := ["poik", "i", "en"]
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ] }

def kirjoja : Form Cell :=
  { id := "karlsson2017_kirjoja"
    lexeme := Lexemes.book
    cell := part_pl
    form := "kirjoja"
    segments := ["kirjo", "j", "a"]
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ] }

def kirjojen : Form Cell :=
  { id := "karlsson2017_kirjojen"
    lexeme := Lexemes.book
    cell := gen_pl
    form := "kirjojen"
    segments := ["kirjo", "j", "en"]
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ] }

def paivia : Form Cell :=
  { id := "karlsson2017_paivia"
    lexeme := Lexemes.day
    cell := part_pl
    form := "päiviä"
    segments := ["päiv", "i", "ä"]
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ] }

def paivien : Form Cell :=
  { id := "karlsson2017_paivien"
    lexeme := Lexemes.day
    cell := gen_pl
    form := "päivien"
    segments := ["päiv", "i", "en"]
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ] }

def kasien : Form Cell :=
  { id := "karlsson2017_kasien"
    lexeme := Lexemes.hand
    cell := gen_pl
    form := "käsien"
    segments := ["käs", "i", "en"]
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ] }

def maita : Form Cell :=
  { id := "karlsson2017_maita"
    lexeme := Lexemes.country
    cell := part_pl
    form := "maita"
    segments := ["ma", "i", "ta"]
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ] }

def maiden : Form Cell :=
  { id := "karlsson2017_maiden"
    lexeme := Lexemes.country
    cell := gen_pl
    form := "maiden"
    segments := ["ma", "i", "den"]
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ] }

def maitten : Form Cell :=
  { id := "karlsson2017_maitten"
    lexeme := Lexemes.country
    cell := gen_pl
    form := "maitten"
    segments := ["ma", "i", "tten"]
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ] }

def teita : Form Cell :=
  { id := "karlsson2017_teita"
    lexeme := Lexemes.road
    cell := part_pl
    form := "teitä"
    segments := ["te", "i", "tä"]
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ] }

def teiden : Form Cell :=
  { id := "karlsson2017_teiden"
    lexeme := Lexemes.road
    cell := gen_pl
    form := "teiden"
    segments := ["te", "i", "den"]
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ] }

def esteitten : Form Cell :=
  { id := "karlsson2017_esteitten"
    lexeme := Lexemes.obstacle
    cell := gen_pl
    form := "esteitten"
    segments := ["este", "i", "tten"]
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ] }

def valtioiden : Form Cell :=
  { id := "karlsson2017_valtioiden"
    lexeme := Lexemes.state
    cell := gen_pl
    form := "valtioiden"
    segments := ["valtio", "i", "den"]
    source := [
      ⟨"karlsson-2017", "§13.1.2"⟩
    ] }

def kalojensa : Form Cell :=
  { id := "karlsson2017_kalojensa"
    lexeme := Lexemes.fish
    cell := gen_pl_px3sg
    form := "kalojensa"
    segments := ["kalo", "je", "nsa"]
    source := [
      ⟨"karlsson-2017", "§14.1"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.car, Lexemes.him_her, Lexemes.milk, Lexemes.water,
  Lexemes.family, Lexemes.country, Lexemes.porvoo, Lexemes.table, Lexemes.teacher, Lexemes.wife,
  Lexemes.passport, Lexemes.foot, Lexemes.book, Lexemes.bottle, Lexemes.shelf, Lexemes.house,
  Lexemes.hand, Lexemes.say, Lexemes.eat, Lexemes.run, Lexemes.speak, Lexemes.bag, Lexemes.guest,
  Lexemes.get, Lexemes.father, Lexemes.mother, Lexemes.live, Lexemes.meet, Lexemes.drink,
  Lexemes.be, Lexemes.rest, Lexemes.pull, Lexemes.mention, Lexemes.do, Lexemes.come, Lexemes.learn,
  Lexemes.son, Lexemes.ring, Lexemes.head, Lexemes.fish, Lexemes.girl, Lexemes.cross, Lexemes.stone,
  Lexemes.child, Lexemes.boy, Lexemes.day, Lexemes.road, Lexemes.obstacle, Lexemes.state]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [auto, auton, hanet, maitoa, vetta, perhetta, autossa, autosta,
  autoon, maahan, porvooseen, poydalla, poydalta, poydalle, opettajana, opettajaksi, vaimoineni,
  passitta, jalan, kirjani, kirjasi, kirjansa, pullo, pullossa, pulloni, pullostani, hyllyssa,
  hyllylla, hyllysi, hyllyllesi, taloon, hyllynsa, kadessani, kateen, kateesi, katta, sanoa, syoda,
  juosta, juostaksemme, sanoessani, syodessamme, juosten, syomalla, sanomatta, sanomaan, puhuaksesi,
  puhumalla, autollani, autostasi, autooni, laukkuni, laukkusi, laukkunsa_3sg, laukkumme, laukkunne,
  laukkunsa_3pl, taloaan, vieraanaan, saadakseen, talossaan, autollaan, isalleen, aidiltaan,
  aitiaan, talonsa, autonsa, isaansa, aitinsa, sanoakseni, elaaksemme, tavataksesi, juodakseen,
  ollaksenne, lepaamassa, lepaamaan, vetamalla, mainitsematta, tekemasta, tuleman, pullot, pullokin,
  pulloista, pullossahan, pullotkin, pullossasiko, pulloissamme, pulloistakaan, pulloissannekin,
  hyllyltako, hyllytko, hyllynhan, talonsako, hyllyillamme, kasi, kadet, kasissammehan, lepaamaanko,
  vetamallakin, mainitsemattakaan, oppiakseenhan, maatamme, poikannekin, aidiltanihan, isallesiko,
  maahamme, perhettaan, talojaan, renkaitaan, paataan, taloansa, kalansa, kalaansa_ill,
  kalaansa_part, kaloihinsa, taloissa, taloihin, taloina, taloille, taloiksi, hyllyja, hyllyjen,
  pulloja, pullojen, tyttoja, tyttojen, pulloissa, maissa, risteissa, kivissa, lapsia, talojen,
  poikia, poikien, kirjoja, kirjojen, paivia, paivien, kasien, maita, maiden, maitten, teita,
  teiden, esteitten, valtioiden, kalojensa]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

end Karlsson2017.Wordlist
