module

public import Linglib.Data.Wordlist.Schema

/-!
# `Bobaljik2012`: word forms

Auto-generated from `Linglib/Data/Wordlist/Bobaljik2012.json` by `scripts/gen_wordlist.py`. Do not
edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
Bobaljik2012.Wordlist`.
-/

@[expose] public section

namespace Bobaljik2012.Wordlist

open CLDF.Wordlist

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

/-- The positive cell, `Degree=Pos`. -/
def positive : Cell := { degree := ↑UD.Degree.Pos }

/-- The comparative cell, `Degree=Cmp`. -/
def comparative : Cell := { degree := ↑UD.Degree.Cmp }

/-- The superlative cell, `Degree=Sup`. -/
def superlative : Cell := { degree := ↑UD.Degree.Sup }

def Lexemes.eng_good : Lexeme :=
  { id := "eng_good", languageId := "stan1293", parameterId := "good", label := "good" }

def Lexemes.swe_good : Lexeme :=
  { id := "swe_good", languageId := "swed1254", parameterId := "good", label := "bra" }

def Lexemes.got_good : Lexeme :=
  { id := "got_good", languageId := "goth1244", parameterId := "good", label := "gôd" }

def Lexemes.cim_good : Lexeme :=
  { id := "cim_good", languageId := "tred1238", parameterId := "good", label := "guot" }

def Lexemes.ces_good : Lexeme :=
  { id := "ces_good", languageId := "czec1258", parameterId := "good", label := "dobrý" }

def Lexemes.hbs_good : Lexeme :=
  { id := "hbs_good", languageId := "sout1528", parameterId := "good", label := "dobar" }

def Lexemes.sorb_good : Lexeme :=
  { id := "sorb_good", languageId := "sorb1249", parameterId := "good", label := "dobry" }

def Lexemes.ukr_good_dobr : Lexeme :=
  { id := "ukr_good_dobr", languageId := "ukra1253", parameterId := "good", label := "dobryj" }

def Lexemes.ukr_good_harn : Lexeme :=
  { id := "ukr_good_harn", languageId := "ukra1253", parameterId := "good", label := "harnyj" }

def Lexemes.rus_good : Lexeme :=
  { id := "rus_good", languageId := "russ1263", parameterId := "good", label := "xorošij" }

def Lexemes.lat_good : Lexeme :=
  { id := "lat_good", languageId := "lati1261", parameterId := "good", label := "bonus" }

def Lexemes.cym_good : Lexeme :=
  { id := "cym_good", languageId := "wels1247", parameterId := "good", label := "da" }

def Lexemes.sga_good : Lexeme :=
  { id := "sga_good", languageId := "oldi1246", parameterId := "good", label := "maith" }

def Lexemes.bre_good : Lexeme :=
  { id := "bre_good", languageId := "bret1244", parameterId := "good", label := "mat" }

def Lexemes.grc_good : Lexeme :=
  { id := "grc_good", languageId := "anci1242", parameterId := "good", label := "agathós" }

def Lexemes.san_good : Lexeme :=
  { id := "san_good", languageId := "sans1269", parameterId := "good", label := "praśásyas" }

def Lexemes.kho_good : Lexeme :=
  { id := "kho_good", languageId := "khot1251", parameterId := "good", label := "śśära" }

def Lexemes.pal_good : Lexeme :=
  { id := "pal_good", languageId := "pahl1241", parameterId := "good", label := "xōb" }

def Lexemes.fas_good : Lexeme :=
  { id := "fas_good", languageId := "west2369", parameterId := "good", label := "xub" }

def Lexemes.eus_good : Lexeme :=
  { id := "eus_good", languageId := "basq1248", parameterId := "good", label := "on" }

def Lexemes.fin_good : Lexeme :=
  { id := "fin_good", languageId := "finn1318", parameterId := "good", label := "hyvä" }

def Lexemes.sjd_good : Lexeme :=
  { id := "sjd_good", languageId := "kild1236", parameterId := "good", label := "š’ig’" }

def Lexemes.kat_good : Lexeme :=
  { id := "kat_good", languageId := "nucl1302", parameterId := "good", label := "k’argii" }

def Lexemes.sva_good : Lexeme :=
  { id := "sva_good", languageId := "svan1243", parameterId := "good", label := "ezär" }

def Lexemes.chr_good : Lexeme :=
  { id := "chr_good", languageId := "cher1273", parameterId := "good", label := "osda" }

def Lexemes.eng_bad : Lexeme :=
  { id := "eng_bad", languageId := "stan1293", parameterId := "bad", label := "bad" }

def Lexemes.goh_bad : Lexeme :=
  { id := "goh_bad", languageId := "oldh1241", parameterId := "bad", label := "ubil" }

def Lexemes.non_bad_vandr : Lexeme :=
  { id := "non_bad_vandr", languageId := "oldn1244", parameterId := "bad", label := "vándr" }

def Lexemes.non_bad_illr : Lexeme :=
  { id := "non_bad_illr", languageId := "oldn1244", parameterId := "bad", label := "íllr" }

def Lexemes.dan_bad : Lexeme :=
  { id := "dan_bad", languageId := "dani1285", parameterId := "bad", label := "slem" }

def Lexemes.fao_bad : Lexeme :=
  { id := "fao_bad", languageId := "faro1244", parameterId := "bad", label := "ringur" }

def Lexemes.swe_bad : Lexeme :=
  { id := "swe_bad", languageId := "swed1254", parameterId := "bad", label := "dålig" }

def Lexemes.yid_bad : Lexeme :=
  { id := "yid_bad", languageId := "east2295", parameterId := "bad", label := "šlext" }

def Lexemes.pol_bad : Lexeme :=
  { id := "pol_bad", languageId := "poli1260", parameterId := "bad", label := "zły" }

def Lexemes.ces_bad : Lexeme :=
  { id := "ces_bad", languageId := "czec1258", parameterId := "bad", label := "špatný" }

def Lexemes.ukr_bad : Lexeme :=
  { id := "ukr_bad", languageId := "ukra1253", parameterId := "bad", label := "pohanyj" }

def Lexemes.bel_bad_drenn : Lexeme :=
  { id := "bel_bad_drenn", languageId := "bela1254", parameterId := "bad", label := "drènny" }

def Lexemes.bel_bad_blah : Lexeme :=
  { id := "bel_bad_blah", languageId := "bela1254", parameterId := "bad", label := "blahi" }

def Lexemes.hbs_bad : Lexeme :=
  { id := "hbs_bad", languageId := "sout1528", parameterId := "bad", label := "loš" }

def Lexemes.rus_bad : Lexeme :=
  { id := "rus_bad", languageId := "russ1263", parameterId := "bad", label := "ploxoj" }

def Lexemes.lat_bad : Lexeme :=
  { id := "lat_bad", languageId := "lati1261", parameterId := "bad", label := "malus" }

def Lexemes.sga_bad : Lexeme :=
  { id := "sga_bad", languageId := "oldi1246", parameterId := "bad", label := "olc" }

def Lexemes.cym_bad : Lexeme :=
  { id := "cym_bad", languageId := "wels1247", parameterId := "bad", label := "drwg" }

def Lexemes.bre_bad : Lexeme :=
  { id := "bre_bad", languageId := "bret1244", parameterId := "bad", label := "fall" }

def Lexemes.grc_bad : Lexeme :=
  { id := "grc_bad", languageId := "anci1242", parameterId := "bad", label := "kakós" }

def Lexemes.got_big : Lexeme :=
  { id := "got_big", languageId := "goth1244", parameterId := "big", label := "mikils" }

def Lexemes.ces_big : Lexeme :=
  { id := "ces_big", languageId := "czec1258", parameterId := "big", label := "velký" }

def Lexemes.ukr_big : Lexeme :=
  { id := "ukr_big", languageId := "ukra1253", parameterId := "big", label := "velykyj" }

def Lexemes.pol_big : Lexeme :=
  { id := "pol_big", languageId := "poli1260", parameterId := "big", label := "duży" }

def Lexemes.cym_big : Lexeme :=
  { id := "cym_big", languageId := "wels1247", parameterId := "big", label := "mawr" }

def Lexemes.pal_big : Lexeme :=
  { id := "pal_big", languageId := "pahl1241", parameterId := "big", label := "wazurg" }

def Lexemes.sva_big : Lexeme :=
  { id := "sva_big", languageId := "svan1243", parameterId := "big", label := "d͜zɣəd" }

def Lexemes.got_small : Lexeme :=
  { id := "got_small", languageId := "goth1244", parameterId := "small", label := "leitils" }

def Lexemes.ang_small : Lexeme :=
  { id := "ang_small", languageId := "olde1238", parameterId := "small", label := "lýtel" }

def Lexemes.dan_small : Lexeme :=
  { id := "dan_small", languageId := "dani1285", parameterId := "small", label := "små" }

def Lexemes.hbs_small : Lexeme :=
  { id := "hbs_small", languageId := "sout1528", parameterId := "small", label := "mali" }

def Lexemes.lat_small : Lexeme :=
  { id := "lat_small", languageId := "lati1261", parameterId := "small", label := "parvus" }

def Lexemes.cym_small : Lexeme :=
  { id := "cym_small", languageId := "wels1247", parameterId := "small", label := "bach" }

def Lexemes.grc_small : Lexeme :=
  { id := "grc_small", languageId := "anci1242", parameterId := "small", label := "mikrós" }

def Lexemes.pal_small : Lexeme :=
  { id := "pal_small", languageId := "pahl1241", parameterId := "small", label := "kōdag" }

def Lexemes.non_old : Lexeme :=
  { id := "non_old", languageId := "oldn1244", parameterId := "old", label := "gamall" }

def Lexemes.cym_near : Lexeme :=
  { id := "cym_near", languageId := "wels1247", parameterId := "near", label := "agos" }

def Lexemes.cym_strong : Lexeme :=
  { id := "cym_strong", languageId := "wels1247", parameterId := "strong", label := "cryf" }

def Lexemes.eng_many : Lexeme :=
  { id := "eng_many", languageId := "stan1293", parameterId := "many_much", label := "many" }

def Lexemes.eng_much : Lexeme :=
  { id := "eng_much", languageId := "stan1293", parameterId := "many_much", label := "much" }

def Lexemes.eng_lot : Lexeme :=
  { id := "eng_lot", languageId := "stan1293", parameterId := "many_much", label := "(a) lot" }

def Lexemes.deu_many : Lexeme :=
  { id := "deu_many", languageId := "stan1295", parameterId := "many_much", label := "viel" }

def Lexemes.fao_many : Lexeme :=
  { id := "fao_many", languageId := "faro1244", parameterId := "many_much", label := "nógvur" }

def Lexemes.afr_many_party : Lexeme :=
  { id := "afr_many_party", languageId := "afri1274", parameterId := "many_much", label := "party" }

def Lexemes.afr_many_baie : Lexeme :=
  { id := "afr_many_baie", languageId := "afri1274", parameterId := "many_much", label := "baie" }

def Lexemes.yid_many : Lexeme :=
  { id := "yid_many", languageId := "east2295", parameterId := "many_much", label := "sakh" }

def Lexemes.dan_many : Lexeme :=
  { id := "dan_many", languageId := "dani1285", parameterId := "many_much", label := "mange" }

def Lexemes.ces_many : Lexeme :=
  { id := "ces_many", languageId := "czec1258", parameterId := "many_much", label := "mnoho" }

def Lexemes.rus_many : Lexeme :=
  { id := "rus_many", languageId := "russ1263", parameterId := "many_much", label := "mnogo" }

def Lexemes.bul_many : Lexeme :=
  { id := "bul_many", languageId := "bulg1262", parameterId := "many_much", label := "mnogo" }

def Lexemes.pol_many : Lexeme :=
  { id := "pol_many", languageId := "poli1260", parameterId := "many_much", label := "wiele" }

def Lexemes.hbs_many : Lexeme :=
  { id := "hbs_many", languageId := "sout1528", parameterId := "many_much", label := "puno" }

def Lexemes.ukr_many_bahato : Lexeme :=
  { id := "ukr_many_bahato", languageId := "ukra1253", parameterId := "many_much",
    label := "baháto" }

def Lexemes.ukr_many_duze : Lexeme :=
  { id := "ukr_many_duze", languageId := "ukra1253", parameterId := "many_much", label := "dúže" }

def Lexemes.lav_many : Lexeme :=
  { id := "lav_many", languageId := "latv1249", parameterId := "many_much", label := "daudz" }

def Lexemes.lat_many : Lexeme :=
  { id := "lat_many", languageId := "lati1261", parameterId := "many_much", label := "mult" }

def Lexemes.bre_many : Lexeme :=
  { id := "bre_many", languageId := "bret1244", parameterId := "many_much", label := "kalz" }

def Lexemes.cym_many : Lexeme :=
  { id := "cym_many", languageId := "wels1247", parameterId := "many_much", label := "llawer" }

def Lexemes.grc_many : Lexeme :=
  { id := "grc_many", languageId := "anci1242", parameterId := "many_much", label := "polús" }

def Lexemes.hye_many : Lexeme :=
  { id := "hye_many", languageId := "nucl1235", parameterId := "many_much", label := "šaterë" }

def Lexemes.fas_many_xele : Lexeme :=
  { id := "fas_many_xele", languageId := "west2369", parameterId := "many_much", label := "xele" }

def Lexemes.fas_many_ziad : Lexeme :=
  { id := "fas_many_ziad", languageId := "west2369", parameterId := "many_much", label := "ziad" }

def Lexemes.eus_many : Lexeme :=
  { id := "eus_many", languageId := "basq1248", parameterId := "many_much", label := "asko" }

def Lexemes.fin_many_monet : Lexeme :=
  { id := "fin_many_monet", languageId := "finn1318", parameterId := "many_much", label := "monet" }

def Lexemes.fin_many_paljon : Lexeme :=
  { id := "fin_many_paljon", languageId := "finn1318", parameterId := "many_much",
    label := "paljon" }

def Lexemes.krl_many : Lexeme :=
  { id := "krl_many", languageId := "kare1335", parameterId := "many_much", label := "äijä" }

def Lexemes.hun_many : Lexeme :=
  { id := "hun_many", languageId := "hung1274", parameterId := "many_much", label := "sok" }

def Lexemes.kat_many : Lexeme :=
  { id := "kat_many", languageId := "nucl1302", parameterId := "many_much", label := "bevri" }

def Lexemes.kbd_many : Lexeme :=
  { id := "kbd_many", languageId := "kaba1278", parameterId := "many_much", label := "kwad" }

def Lexemes.eng_few : Lexeme :=
  { id := "eng_few", languageId := "stan1293", parameterId := "few", label := "(a) little" }

def Lexemes.afr_few : Lexeme :=
  { id := "afr_few", languageId := "afri1274", parameterId := "few", label := "weinig" }

def Lexemes.fry_few : Lexeme :=
  { id := "fry_few", languageId := "west2354", parameterId := "few", label := "(en) bytsje" }

def Lexemes.ukr_few : Lexeme :=
  { id := "ukr_few", languageId := "ukra1253", parameterId := "few", label := "troxi" }

def Lexemes.lat_few : Lexeme :=
  { id := "lat_few", languageId := "lati1261", parameterId := "few", label := "paucus" }

def Lexemes.grc_few : Lexeme :=
  { id := "grc_few", languageId := "anci1242", parameterId := "few", label := "olígos" }

def Lexemes.krl_many_onego : Lexeme :=
  { id := "krl_many_onego", languageId := "kare1335", parameterId := "many_much", label := "äijy" }

def eng_good_positive : Form Cell :=
  { id := "eng_good_positive"
    lexeme := Lexemes.eng_good
    cell := positive
    form := "good"
    morphs := ["good"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def eng_good_comparative : Form Cell :=
  { id := "eng_good_comparative"
    lexeme := Lexemes.eng_good
    cell := comparative
    form := "better"
    morphs := ["bett", "er"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def eng_good_superlative : Form Cell :=
  { id := "eng_good_superlative"
    lexeme := Lexemes.eng_good
    cell := superlative
    form := "best"
    morphs := ["be", "st"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def swe_good_positive : Form Cell :=
  { id := "swe_good_positive"
    lexeme := Lexemes.swe_good
    cell := positive
    form := "bra"
    morphs := ["bra"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def swe_good_comparative : Form Cell :=
  { id := "swe_good_comparative"
    lexeme := Lexemes.swe_good
    cell := comparative
    form := "bättre"
    morphs := ["bätt", "re"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def swe_good_superlative : Form Cell :=
  { id := "swe_good_superlative"
    lexeme := Lexemes.swe_good
    cell := superlative
    form := "bäst"
    morphs := ["bä", "st"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def got_good_positive : Form Cell :=
  { id := "got_good_positive"
    lexeme := Lexemes.got_good
    cell := positive
    form := "gôd"
    morphs := ["gôd"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def got_good_comparative : Form Cell :=
  { id := "got_good_comparative"
    lexeme := Lexemes.got_good
    cell := comparative
    form := "sêlra"
    morphs := ["sêl", "ra"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def got_good_superlative : Form Cell :=
  { id := "got_good_superlative"
    lexeme := Lexemes.got_good
    cell := superlative
    form := "sêlost"
    morphs := ["sêl", "ost"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cim_good_positive : Form Cell :=
  { id := "cim_good_positive"
    lexeme := Lexemes.cim_good
    cell := positive
    form := "guot"
    morphs := ["guot"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cim_good_comparative : Form Cell :=
  { id := "cim_good_comparative"
    lexeme := Lexemes.cim_good
    cell := comparative
    form := "ƀegur"
    morphs := ["ƀeg", "ur"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cim_good_superlative : Form Cell :=
  { id := "cim_good_superlative"
    lexeme := Lexemes.cim_good
    cell := superlative
    form := "ƀegurste"
    morphs := ["ƀeg", "ur", "ste"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ces_good_positive : Form Cell :=
  { id := "ces_good_positive"
    lexeme := Lexemes.ces_good
    cell := positive
    form := "dobrý"
    morphs := ["dobr", "ý"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ces_good_comparative : Form Cell :=
  { id := "ces_good_comparative"
    lexeme := Lexemes.ces_good
    cell := comparative
    form := "lepší"
    morphs := ["lep", "ší"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ces_good_superlative : Form Cell :=
  { id := "ces_good_superlative"
    lexeme := Lexemes.ces_good
    cell := superlative
    form := "nejlepší"
    morphs := ["nej", "lep", "ší"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def hbs_good_positive : Form Cell :=
  { id := "hbs_good_positive"
    lexeme := Lexemes.hbs_good
    cell := positive
    form := "dobar"
    morphs := ["dobar"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def hbs_good_comparative : Form Cell :=
  { id := "hbs_good_comparative"
    lexeme := Lexemes.hbs_good
    cell := comparative
    form := "bolji"
    morphs := ["bol", "ji"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def hbs_good_superlative : Form Cell :=
  { id := "hbs_good_superlative"
    lexeme := Lexemes.hbs_good
    cell := superlative
    form := "najbolji"
    morphs := ["naj", "bol", "ji"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sorb_good_positive : Form Cell :=
  { id := "sorb_good_positive"
    lexeme := Lexemes.sorb_good
    cell := positive
    form := "dobry"
    morphs := ["dobr", "y"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sorb_good_comparative : Form Cell :=
  { id := "sorb_good_comparative"
    lexeme := Lexemes.sorb_good
    cell := comparative
    form := "redliši"
    morphs := ["redl", "iši"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_good_dobr_positive : Form Cell :=
  { id := "ukr_good_dobr_positive"
    lexeme := Lexemes.ukr_good_dobr
    cell := positive
    form := "dobryj"
    morphs := ["dobr", "yj"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_good_dobr_comparative : Form Cell :=
  { id := "ukr_good_dobr_comparative"
    lexeme := Lexemes.ukr_good_dobr
    cell := comparative
    form := "kraščyj"
    morphs := ["krašč", "yj"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_good_dobr_superlative : Form Cell :=
  { id := "ukr_good_dobr_superlative"
    lexeme := Lexemes.ukr_good_dobr
    cell := superlative
    form := "najkraščyj"
    morphs := ["naj", "krašč", "yj"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_good_harn_positive : Form Cell :=
  { id := "ukr_good_harn_positive"
    lexeme := Lexemes.ukr_good_harn
    cell := positive
    form := "harnyj"
    morphs := ["harn", "yj"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_good_harn_comparative : Form Cell :=
  { id := "ukr_good_harn_comparative"
    lexeme := Lexemes.ukr_good_harn
    cell := comparative
    form := "kraščyj"
    morphs := ["krašč", "yj"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_good_harn_superlative : Form Cell :=
  { id := "ukr_good_harn_superlative"
    lexeme := Lexemes.ukr_good_harn
    cell := superlative
    form := "najkraščyj"
    morphs := ["naj", "krašč", "yj"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def rus_good_positive : Form Cell :=
  { id := "rus_good_positive"
    lexeme := Lexemes.rus_good
    cell := positive
    form := "xorošij"
    morphs := ["xoroš", "ij"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def rus_good_comparative : Form Cell :=
  { id := "rus_good_comparative"
    lexeme := Lexemes.rus_good
    cell := comparative
    form := "lučše"
    morphs := ["luč", "še"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def rus_good_superlative : Form Cell :=
  { id := "rus_good_superlative"
    lexeme := Lexemes.rus_good
    cell := superlative
    form := "nailučšij"
    morphs := ["nai", "luč", "š", "ij"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def lat_good_positive : Form Cell :=
  { id := "lat_good_positive"
    lexeme := Lexemes.lat_good
    cell := positive
    form := "bonus"
    morphs := ["bon", "us"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def lat_good_comparative : Form Cell :=
  { id := "lat_good_comparative"
    lexeme := Lexemes.lat_good
    cell := comparative
    form := "melior"
    morphs := ["mel", "ior"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def lat_good_superlative : Form Cell :=
  { id := "lat_good_superlative"
    lexeme := Lexemes.lat_good
    cell := superlative
    form := "optimus"
    morphs := ["opt", "imus"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_good_positive : Form Cell :=
  { id := "cym_good_positive"
    lexeme := Lexemes.cym_good
    cell := positive
    form := "da"
    morphs := ["da"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_good_comparative : Form Cell :=
  { id := "cym_good_comparative"
    lexeme := Lexemes.cym_good
    cell := comparative
    form := "gwell"
    morphs := ["gwell"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_good_superlative : Form Cell :=
  { id := "cym_good_superlative"
    lexeme := Lexemes.cym_good
    cell := superlative
    form := "gorau"
    morphs := ["gor", "au"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sga_good_positive : Form Cell :=
  { id := "sga_good_positive"
    lexeme := Lexemes.sga_good
    cell := positive
    form := "maith"
    morphs := ["maith"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sga_good_comparative : Form Cell :=
  { id := "sga_good_comparative"
    lexeme := Lexemes.sga_good
    cell := comparative
    form := "ferr"
    morphs := ["ferr"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sga_good_superlative : Form Cell :=
  { id := "sga_good_superlative"
    lexeme := Lexemes.sga_good
    cell := superlative
    form := "dech"
    morphs := ["dech"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bre_good_positive : Form Cell :=
  { id := "bre_good_positive"
    lexeme := Lexemes.bre_good
    cell := positive
    form := "mat"
    morphs := ["mat"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bre_good_comparative : Form Cell :=
  { id := "bre_good_comparative"
    lexeme := Lexemes.bre_good
    cell := comparative
    form := "gwell(oc’h)"
    morphs := ["gwell", "(oc’h)"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bre_good_superlative : Form Cell :=
  { id := "bre_good_superlative"
    lexeme := Lexemes.bre_good
    cell := superlative
    form := "gwellañ"
    morphs := ["gwell", "añ"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_good_positive : Form Cell :=
  { id := "grc_good_positive"
    lexeme := Lexemes.grc_good
    cell := positive
    form := "agathós"
    morphs := ["agath", "ós"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_good_comparative : Form Cell :=
  { id := "grc_good_comparative"
    lexeme := Lexemes.grc_good
    cell := comparative
    form := "ameínōn"
    morphs := ["ameín", "ōn"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_good_superlative : Form Cell :=
  { id := "grc_good_superlative"
    lexeme := Lexemes.grc_good
    cell := superlative
    form := "(phéristos)"
    morphs := ["(phér", "ist", "os)"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_good_comparative_2 : Form Cell :=
  { id := "grc_good_comparative_2"
    lexeme := Lexemes.grc_good
    cell := comparative
    form := "areíōn"
    morphs := ["areí", "ōn"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_good_superlative_2 : Form Cell :=
  { id := "grc_good_superlative_2"
    lexeme := Lexemes.grc_good
    cell := superlative
    form := "áristos"
    morphs := ["ár", "ist", "os"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_good_comparative_3 : Form Cell :=
  { id := "grc_good_comparative_3"
    lexeme := Lexemes.grc_good
    cell := comparative
    form := "beltíōn"
    morphs := ["belt", "íōn"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_good_superlative_3 : Form Cell :=
  { id := "grc_good_superlative_3"
    lexeme := Lexemes.grc_good
    cell := superlative
    form := "béltistos"
    morphs := ["bélt", "ist", "os"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_good_comparative_4 : Form Cell :=
  { id := "grc_good_comparative_4"
    lexeme := Lexemes.grc_good
    cell := comparative
    form := "kreíssōn"
    morphs := ["kreíss", "ōn"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_good_superlative_4 : Form Cell :=
  { id := "grc_good_superlative_4"
    lexeme := Lexemes.grc_good
    cell := superlative
    form := "krátistos"
    morphs := ["krát", "ist", "os"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_good_comparative_5 : Form Cell :=
  { id := "grc_good_comparative_5"
    lexeme := Lexemes.grc_good
    cell := comparative
    form := "lóïon"
    morphs := ["ló", "ïon"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_good_superlative_5 : Form Cell :=
  { id := "grc_good_superlative_5"
    lexeme := Lexemes.grc_good
    cell := superlative
    form := "lõistos"
    morphs := ["lõ", "ist", "os"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def san_good_positive : Form Cell :=
  { id := "san_good_positive"
    lexeme := Lexemes.san_good
    cell := positive
    form := "praśásyas"
    morphs := ["pra", "śásya", "s"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def san_good_comparative : Form Cell :=
  { id := "san_good_comparative"
    lexeme := Lexemes.san_good
    cell := comparative
    form := "śréyān"
    morphs := ["śré", "yān"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def san_good_superlative : Form Cell :=
  { id := "san_good_superlative"
    lexeme := Lexemes.san_good
    cell := superlative
    form := "śréṣṭhas"
    morphs := ["śré", "ṣṭhas"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def san_good_comparative_2 : Form Cell :=
  { id := "san_good_comparative_2"
    lexeme := Lexemes.san_good
    cell := comparative
    form := "jyāyān"
    morphs := ["jyā", "yān"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def san_good_superlative_2 : Form Cell :=
  { id := "san_good_superlative_2"
    lexeme := Lexemes.san_good
    cell := superlative
    form := "jyēṣṭhas"
    morphs := ["jyē", "ṣṭhas"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def kho_good_positive : Form Cell :=
  { id := "kho_good_positive"
    lexeme := Lexemes.kho_good
    cell := positive
    form := "śśära"
    morphs := ["śśära-"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def kho_good_comparative : Form Cell :=
  { id := "kho_good_comparative"
    lexeme := Lexemes.kho_good
    cell := comparative
    form := "hastara"
    morphs := ["has", "tara"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def kho_good_superlative : Form Cell :=
  { id := "kho_good_superlative"
    lexeme := Lexemes.kho_good
    cell := superlative
    form := "hastama"
    morphs := ["has", "tama"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pal_good_positive : Form Cell :=
  { id := "pal_good_positive"
    lexeme := Lexemes.pal_good
    cell := positive
    form := "xōb"
    morphs := ["xōb"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pal_good_comparative : Form Cell :=
  { id := "pal_good_comparative"
    lexeme := Lexemes.pal_good
    cell := comparative
    form := "weh/wahīy"
    morphs := ["weh/wah", "īy"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pal_good_superlative : Form Cell :=
  { id := "pal_good_superlative"
    lexeme := Lexemes.pal_good
    cell := superlative
    form := "pahlom"
    morphs := ["pahl", "om"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pal_good_superlative_2 : Form Cell :=
  { id := "pal_good_superlative_2"
    lexeme := Lexemes.pal_good
    cell := superlative
    form := "pāšom"
    morphs := ["pāš", "om"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def fas_good_positive : Form Cell :=
  { id := "fas_good_positive"
    lexeme := Lexemes.fas_good
    cell := positive
    form := "xub"
    morphs := ["xub"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def fas_good_comparative : Form Cell :=
  { id := "fas_good_comparative"
    lexeme := Lexemes.fas_good
    cell := comparative
    form := "behtær"
    morphs := ["beh", "tær"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def fas_good_superlative : Form Cell :=
  { id := "fas_good_superlative"
    lexeme := Lexemes.fas_good
    cell := superlative
    form := "behtærin"
    morphs := ["beh", "tær", "in"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def eus_good_positive : Form Cell :=
  { id := "eus_good_positive"
    lexeme := Lexemes.eus_good
    cell := positive
    form := "on"
    morphs := ["on"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def eus_good_comparative : Form Cell :=
  { id := "eus_good_comparative"
    lexeme := Lexemes.eus_good
    cell := comparative
    form := "hobe"
    morphs := ["hobe"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def eus_good_superlative : Form Cell :=
  { id := "eus_good_superlative"
    lexeme := Lexemes.eus_good
    cell := superlative
    form := "hoberen"
    morphs := ["hobe", "ren"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def eus_good_superlative_2 : Form Cell :=
  { id := "eus_good_superlative_2"
    lexeme := Lexemes.eus_good
    cell := superlative
    form := "onen"
    morphs := ["on", "en"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def fin_good_positive : Form Cell :=
  { id := "fin_good_positive"
    lexeme := Lexemes.fin_good
    cell := positive
    form := "hyvä"
    morphs := ["hyvä"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def fin_good_comparative : Form Cell :=
  { id := "fin_good_comparative"
    lexeme := Lexemes.fin_good
    cell := comparative
    form := "parempi"
    morphs := ["pare", "mpi"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def fin_good_superlative : Form Cell :=
  { id := "fin_good_superlative"
    lexeme := Lexemes.fin_good
    cell := superlative
    form := "parhain"
    morphs := ["parha", "i", "n"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sjd_good_positive : Form Cell :=
  { id := "sjd_good_positive"
    lexeme := Lexemes.sjd_good
    cell := positive
    form := "š’ig’"
    morphs := ["š’ig’"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sjd_good_comparative : Form Cell :=
  { id := "sjd_good_comparative"
    lexeme := Lexemes.sjd_good
    cell := comparative
    form := "pɛr’amp"
    morphs := ["pɛr’a", "mp"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sjd_good_superlative : Form Cell :=
  { id := "sjd_good_superlative"
    lexeme := Lexemes.sjd_good
    cell := superlative
    form := "pɛr’mus"
    morphs := ["pɛr’", "mus"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def kat_good_positive : Form Cell :=
  { id := "kat_good_positive"
    lexeme := Lexemes.kat_good
    cell := positive
    form := "k’argii"
    morphs := ["k’argi", "i"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def kat_good_comparative : Form Cell :=
  { id := "kat_good_comparative"
    lexeme := Lexemes.kat_good
    cell := comparative
    form := "umǰobesi"
    morphs := ["u", "mǰob", "es", "i"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def kat_good_superlative : Form Cell :=
  { id := "kat_good_superlative"
    lexeme := Lexemes.kat_good
    cell := superlative
    form := "saumǰobeso"
    morphs := ["sa", "u", "mǰob", "es", "o"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def kat_good_comparative_2 : Form Cell :=
  { id := "kat_good_comparative_2"
    lexeme := Lexemes.kat_good
    cell := comparative
    form := "uk’etesi"
    morphs := ["u", "k’et", "es", "i"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def kat_good_superlative_2 : Form Cell :=
  { id := "kat_good_superlative_2"
    lexeme := Lexemes.kat_good
    cell := superlative
    form := "sauk’eteso"
    morphs := ["sa", "u", "k’et", "es", "o"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sva_good_positive : Form Cell :=
  { id := "sva_good_positive"
    lexeme := Lexemes.sva_good
    cell := positive
    form := "ezär"
    morphs := ["ezär"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sva_good_comparative : Form Cell :=
  { id := "sva_good_comparative"
    lexeme := Lexemes.sva_good
    cell := comparative
    form := "xoča"
    morphs := ["xo", "č", "a"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sva_good_comparative_2 : Form Cell :=
  { id := "sva_good_comparative_2"
    lexeme := Lexemes.sva_good
    cell := comparative
    form := "xočēl"
    morphs := ["xo", "č", "ēl"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sva_good_superlative : Form Cell :=
  { id := "sva_good_superlative"
    lexeme := Lexemes.sva_good
    cell := superlative
    form := "mačēne"
    morphs := ["ma", "č", "ēne"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def chr_good_positive : Form Cell :=
  { id := "chr_good_positive"
    lexeme := Lexemes.chr_good
    cell := positive
    form := "osda"
    morphs := ["osda"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def chr_good_comparative : Form Cell :=
  { id := "chr_good_comparative"
    lexeme := Lexemes.chr_good
    cell := comparative
    form := "dajehla"
    morphs := ["dajehla"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def chr_good_superlative : Form Cell :=
  { id := "chr_good_superlative"
    lexeme := Lexemes.chr_good
    cell := superlative
    form := "widajehlʌ̃ʔi"
    morphs := ["wi", "dajehl", "ʌ̃ʔi"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def eng_bad_positive : Form Cell :=
  { id := "eng_bad_positive"
    lexeme := Lexemes.eng_bad
    cell := positive
    form := "bad"
    morphs := ["bad"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def eng_bad_comparative : Form Cell :=
  { id := "eng_bad_comparative"
    lexeme := Lexemes.eng_bad
    cell := comparative
    form := "worse"
    morphs := ["worse"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def eng_bad_superlative : Form Cell :=
  { id := "eng_bad_superlative"
    lexeme := Lexemes.eng_bad
    cell := superlative
    form := "worst"
    morphs := ["wors", "t"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def goh_bad_positive : Form Cell :=
  { id := "goh_bad_positive"
    lexeme := Lexemes.goh_bad
    cell := positive
    form := "ubil"
    morphs := ["ubil"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def goh_bad_comparative : Form Cell :=
  { id := "goh_bad_comparative"
    lexeme := Lexemes.goh_bad
    cell := comparative
    form := "wirsiro"
    morphs := ["wirsi", "ro"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def goh_bad_superlative : Form Cell :=
  { id := "goh_bad_superlative"
    lexeme := Lexemes.goh_bad
    cell := superlative
    form := "wirsisto"
    morphs := ["wirsi", "sto"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def non_bad_vandr_positive : Form Cell :=
  { id := "non_bad_vandr_positive"
    lexeme := Lexemes.non_bad_vandr
    cell := positive
    form := "vándr"
    morphs := ["vándr"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def non_bad_vandr_comparative : Form Cell :=
  { id := "non_bad_vandr_comparative"
    lexeme := Lexemes.non_bad_vandr
    cell := comparative
    form := "verre"
    morphs := ["ver", "re"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def non_bad_vandr_superlative : Form Cell :=
  { id := "non_bad_vandr_superlative"
    lexeme := Lexemes.non_bad_vandr
    cell := superlative
    form := "verstr"
    morphs := ["ver", "str"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def non_bad_illr_positive : Form Cell :=
  { id := "non_bad_illr_positive"
    lexeme := Lexemes.non_bad_illr
    cell := positive
    form := "íllr"
    morphs := ["íllr"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def non_bad_illr_comparative : Form Cell :=
  { id := "non_bad_illr_comparative"
    lexeme := Lexemes.non_bad_illr
    cell := comparative
    form := "verre"
    morphs := ["ver", "re"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def non_bad_illr_superlative : Form Cell :=
  { id := "non_bad_illr_superlative"
    lexeme := Lexemes.non_bad_illr
    cell := superlative
    form := "verstr"
    morphs := ["ver", "str"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def dan_bad_positive : Form Cell :=
  { id := "dan_bad_positive"
    lexeme := Lexemes.dan_bad
    cell := positive
    form := "slem"
    morphs := ["slem"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def dan_bad_comparative : Form Cell :=
  { id := "dan_bad_comparative"
    lexeme := Lexemes.dan_bad
    cell := comparative
    form := "værre"
    morphs := ["vær", "re"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def dan_bad_superlative : Form Cell :=
  { id := "dan_bad_superlative"
    lexeme := Lexemes.dan_bad
    cell := superlative
    form := "værst"
    morphs := ["vær", "st"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def fao_bad_positive : Form Cell :=
  { id := "fao_bad_positive"
    lexeme := Lexemes.fao_bad
    cell := positive
    form := "ringur"
    morphs := ["ringur"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def fao_bad_comparative : Form Cell :=
  { id := "fao_bad_comparative"
    lexeme := Lexemes.fao_bad
    cell := comparative
    form := "verri"
    morphs := ["ver", "ri"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def fao_bad_superlative : Form Cell :=
  { id := "fao_bad_superlative"
    lexeme := Lexemes.fao_bad
    cell := superlative
    form := "verstur"
    morphs := ["ver", "st", "ur"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def swe_bad_positive : Form Cell :=
  { id := "swe_bad_positive"
    lexeme := Lexemes.swe_bad
    cell := positive
    form := "dålig"
    morphs := ["dålig"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def swe_bad_comparative : Form Cell :=
  { id := "swe_bad_comparative"
    lexeme := Lexemes.swe_bad
    cell := comparative
    form := "värre"
    morphs := ["vär", "re"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def swe_bad_superlative : Form Cell :=
  { id := "swe_bad_superlative"
    lexeme := Lexemes.swe_bad
    cell := superlative
    form := "värst"
    morphs := ["vär", "st"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def swe_bad_comparative_2 : Form Cell :=
  { id := "swe_bad_comparative_2"
    lexeme := Lexemes.swe_bad
    cell := comparative
    form := "sämre"
    morphs := ["säm", "re"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def swe_bad_superlative_2 : Form Cell :=
  { id := "swe_bad_superlative_2"
    lexeme := Lexemes.swe_bad
    cell := superlative
    form := "sämst"
    morphs := ["säm", "st"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def yid_bad_positive : Form Cell :=
  { id := "yid_bad_positive"
    lexeme := Lexemes.yid_bad
    cell := positive
    form := "šlext"
    morphs := ["šlext"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def yid_bad_comparative : Form Cell :=
  { id := "yid_bad_comparative"
    lexeme := Lexemes.yid_bad
    cell := comparative
    form := "erger"
    morphs := ["erg", "er"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def yid_bad_superlative : Form Cell :=
  { id := "yid_bad_superlative"
    lexeme := Lexemes.yid_bad
    cell := superlative
    form := "ergst"
    morphs := ["erg", "st"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pol_bad_positive : Form Cell :=
  { id := "pol_bad_positive"
    lexeme := Lexemes.pol_bad
    cell := positive
    form := "zły"
    morphs := ["zł", "y"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pol_bad_comparative : Form Cell :=
  { id := "pol_bad_comparative"
    lexeme := Lexemes.pol_bad
    cell := comparative
    form := "gorszy"
    morphs := ["gor", "szy"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pol_bad_superlative : Form Cell :=
  { id := "pol_bad_superlative"
    lexeme := Lexemes.pol_bad
    cell := superlative
    form := "najgorszy"
    morphs := ["naj", "gor", "szy"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ces_bad_positive : Form Cell :=
  { id := "ces_bad_positive"
    lexeme := Lexemes.ces_bad
    cell := positive
    form := "špatný"
    morphs := ["špatn", "ý"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ces_bad_comparative : Form Cell :=
  { id := "ces_bad_comparative"
    lexeme := Lexemes.ces_bad
    cell := comparative
    form := "horší"
    morphs := ["hor", "ší"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ces_bad_superlative : Form Cell :=
  { id := "ces_bad_superlative"
    lexeme := Lexemes.ces_bad
    cell := superlative
    form := "nejhorší"
    morphs := ["nej", "hor", "ší"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_bad_positive : Form Cell :=
  { id := "ukr_bad_positive"
    lexeme := Lexemes.ukr_bad
    cell := positive
    form := "pohanyj"
    morphs := ["pohan", "yj"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_bad_comparative : Form Cell :=
  { id := "ukr_bad_comparative"
    lexeme := Lexemes.ukr_bad
    cell := comparative
    form := "hiršyj"
    morphs := ["hir", "šyj"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_bad_superlative : Form Cell :=
  { id := "ukr_bad_superlative"
    lexeme := Lexemes.ukr_bad
    cell := superlative
    form := "najhiršyj"
    morphs := ["naj", "hir", "šyj"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bel_bad_drenn_positive : Form Cell :=
  { id := "bel_bad_drenn_positive"
    lexeme := Lexemes.bel_bad_drenn
    cell := positive
    form := "drènny"
    morphs := ["drènn", "y"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bel_bad_drenn_comparative : Form Cell :=
  { id := "bel_bad_drenn_comparative"
    lexeme := Lexemes.bel_bad_drenn
    cell := comparative
    form := "horšy"
    morphs := ["hor", "šy"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bel_bad_drenn_superlative : Form Cell :=
  { id := "bel_bad_drenn_superlative"
    lexeme := Lexemes.bel_bad_drenn
    cell := superlative
    form := "najhoršy"
    morphs := ["naj", "hor", "šy"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bel_bad_blah_positive : Form Cell :=
  { id := "bel_bad_blah_positive"
    lexeme := Lexemes.bel_bad_blah
    cell := positive
    form := "blahi"
    morphs := ["blah", "i"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bel_bad_blah_comparative : Form Cell :=
  { id := "bel_bad_blah_comparative"
    lexeme := Lexemes.bel_bad_blah
    cell := comparative
    form := "horšy"
    morphs := ["hor", "šy"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bel_bad_blah_superlative : Form Cell :=
  { id := "bel_bad_blah_superlative"
    lexeme := Lexemes.bel_bad_blah
    cell := superlative
    form := "najhoršy"
    morphs := ["naj", "hor", "šy"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def hbs_bad_positive : Form Cell :=
  { id := "hbs_bad_positive"
    lexeme := Lexemes.hbs_bad
    cell := positive
    form := "loš"
    morphs := ["loš"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def hbs_bad_comparative : Form Cell :=
  { id := "hbs_bad_comparative"
    lexeme := Lexemes.hbs_bad
    cell := comparative
    form := "gori"
    morphs := ["gor", "i"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def hbs_bad_superlative : Form Cell :=
  { id := "hbs_bad_superlative"
    lexeme := Lexemes.hbs_bad
    cell := superlative
    form := "najgori"
    morphs := ["naj", "gor", "i"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def rus_bad_positive : Form Cell :=
  { id := "rus_bad_positive"
    lexeme := Lexemes.rus_bad
    cell := positive
    form := "ploxoj"
    morphs := ["plox", "oj"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def rus_bad_comparative : Form Cell :=
  { id := "rus_bad_comparative"
    lexeme := Lexemes.rus_bad
    cell := comparative
    form := "xuže"
    morphs := ["xuž", "e"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def rus_bad_superlative : Form Cell :=
  { id := "rus_bad_superlative"
    lexeme := Lexemes.rus_bad
    cell := superlative
    form := "naixudšij"
    morphs := ["nai", "xud", "š", "ij"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def lat_bad_positive : Form Cell :=
  { id := "lat_bad_positive"
    lexeme := Lexemes.lat_bad
    cell := positive
    form := "malus"
    morphs := ["malus"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def lat_bad_comparative : Form Cell :=
  { id := "lat_bad_comparative"
    lexeme := Lexemes.lat_bad
    cell := comparative
    form := "pējor"
    morphs := ["pēj", "or"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def lat_bad_superlative : Form Cell :=
  { id := "lat_bad_superlative"
    lexeme := Lexemes.lat_bad
    cell := superlative
    form := "pessimus"
    morphs := ["pe", "ssimus"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sga_bad_positive : Form Cell :=
  { id := "sga_bad_positive"
    lexeme := Lexemes.sga_bad
    cell := positive
    form := "olc"
    morphs := ["olc"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sga_bad_comparative : Form Cell :=
  { id := "sga_bad_comparative"
    lexeme := Lexemes.sga_bad
    cell := comparative
    form := "messa"
    morphs := ["messa"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sga_bad_superlative : Form Cell :=
  { id := "sga_bad_superlative"
    lexeme := Lexemes.sga_bad
    cell := superlative
    form := "messam"
    morphs := ["messa", "m"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_bad_positive : Form Cell :=
  { id := "cym_bad_positive"
    lexeme := Lexemes.cym_bad
    cell := positive
    form := "drwg"
    morphs := ["drwg"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_bad_comparative : Form Cell :=
  { id := "cym_bad_comparative"
    lexeme := Lexemes.cym_bad
    cell := comparative
    form := "gwaeth"
    morphs := ["gwaeth"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_bad_superlative : Form Cell :=
  { id := "cym_bad_superlative"
    lexeme := Lexemes.cym_bad
    cell := superlative
    form := "gwaethaf"
    morphs := ["gwaeth", "af"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bre_bad_positive : Form Cell :=
  { id := "bre_bad_positive"
    lexeme := Lexemes.bre_bad
    cell := positive
    form := "fall"
    morphs := ["fall"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bre_bad_comparative : Form Cell :=
  { id := "bre_bad_comparative"
    lexeme := Lexemes.bre_bad
    cell := comparative
    form := "gwash(oc’h)"
    morphs := ["gwash", "(oc’h)"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def bre_bad_superlative : Form Cell :=
  { id := "bre_bad_superlative"
    lexeme := Lexemes.bre_bad
    cell := superlative
    form := "gwashañ"
    morphs := ["gwash", "añ"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_bad_positive : Form Cell :=
  { id := "grc_bad_positive"
    lexeme := Lexemes.grc_bad
    cell := positive
    form := "kakós"
    morphs := ["kak", "ós"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_bad_comparative : Form Cell :=
  { id := "grc_bad_comparative"
    lexeme := Lexemes.grc_bad
    cell := comparative
    form := "cheírōn"
    morphs := ["cheír", "ōn"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_bad_superlative : Form Cell :=
  { id := "grc_bad_superlative"
    lexeme := Lexemes.grc_bad
    cell := superlative
    form := "cheíristos"
    morphs := ["cheír", "ist", "os"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_bad_comparative_2 : Form Cell :=
  { id := "grc_bad_comparative_2"
    lexeme := Lexemes.grc_bad
    cell := comparative
    form := "héssōn"
    morphs := ["héssōn"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_bad_superlative_2 : Form Cell :=
  { id := "grc_bad_superlative_2"
    lexeme := Lexemes.grc_bad
    cell := superlative
    form := "hékistos"
    morphs := ["hék", "ist", "os"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def got_big_positive : Form Cell :=
  { id := "got_big_positive"
    lexeme := Lexemes.got_big
    cell := positive
    form := "mikils"
    morphs := ["mikil", "s"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def got_big_comparative : Form Cell :=
  { id := "got_big_comparative"
    lexeme := Lexemes.got_big
    cell := comparative
    form := "maiza"
    morphs := ["mai", "za"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def got_big_superlative : Form Cell :=
  { id := "got_big_superlative"
    lexeme := Lexemes.got_big
    cell := superlative
    form := "maists"
    morphs := ["mai", "sts"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ces_big_positive : Form Cell :=
  { id := "ces_big_positive"
    lexeme := Lexemes.ces_big
    cell := positive
    form := "velký"
    morphs := ["velk", "ý"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ces_big_comparative : Form Cell :=
  { id := "ces_big_comparative"
    lexeme := Lexemes.ces_big
    cell := comparative
    form := "větší"
    morphs := ["vět", "ší"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ces_big_superlative : Form Cell :=
  { id := "ces_big_superlative"
    lexeme := Lexemes.ces_big
    cell := superlative
    form := "největší"
    morphs := ["nej", "vět", "ší"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_big_positive : Form Cell :=
  { id := "ukr_big_positive"
    lexeme := Lexemes.ukr_big
    cell := positive
    form := "velykyj"
    morphs := ["velyk", "yj"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_big_comparative : Form Cell :=
  { id := "ukr_big_comparative"
    lexeme := Lexemes.ukr_big
    cell := comparative
    form := "bil’šyj"
    morphs := ["bil’", "šyj"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ukr_big_superlative : Form Cell :=
  { id := "ukr_big_superlative"
    lexeme := Lexemes.ukr_big
    cell := superlative
    form := "najbil’šyj"
    morphs := ["naj", "bil’", "šyj"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pol_big_positive : Form Cell :=
  { id := "pol_big_positive"
    lexeme := Lexemes.pol_big
    cell := positive
    form := "duży"
    morphs := ["duż", "y"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pol_big_comparative : Form Cell :=
  { id := "pol_big_comparative"
    lexeme := Lexemes.pol_big
    cell := comparative
    form := "większy"
    morphs := ["więk", "szy"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pol_big_superlative : Form Cell :=
  { id := "pol_big_superlative"
    lexeme := Lexemes.pol_big
    cell := superlative
    form := "największy"
    morphs := ["naj", "więk", "szy"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_big_positive : Form Cell :=
  { id := "cym_big_positive"
    lexeme := Lexemes.cym_big
    cell := positive
    form := "mawr"
    morphs := ["mawr"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_big_comparative : Form Cell :=
  { id := "cym_big_comparative"
    lexeme := Lexemes.cym_big
    cell := comparative
    form := "mwy"
    morphs := ["mwy"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_big_superlative : Form Cell :=
  { id := "cym_big_superlative"
    lexeme := Lexemes.cym_big
    cell := superlative
    form := "mwyaf"
    morphs := ["mwy", "af"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pal_big_positive : Form Cell :=
  { id := "pal_big_positive"
    lexeme := Lexemes.pal_big
    cell := positive
    form := "wazurg"
    morphs := ["wazurg"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pal_big_comparative : Form Cell :=
  { id := "pal_big_comparative"
    lexeme := Lexemes.pal_big
    cell := comparative
    form := "meh/mahīy"
    morphs := ["meh/mah", "īy"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pal_big_superlative : Form Cell :=
  { id := "pal_big_superlative"
    lexeme := Lexemes.pal_big
    cell := superlative
    form := "mahist"
    morphs := ["mah", "ist"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sva_big_positive : Form Cell :=
  { id := "sva_big_positive"
    lexeme := Lexemes.sva_big
    cell := positive
    form := "d͜zɣəd"
    morphs := ["d͜zɣəd"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sva_big_comparative : Form Cell :=
  { id := "sva_big_comparative"
    lexeme := Lexemes.sva_big
    cell := comparative
    form := "xoša"
    morphs := ["xo", "š", "a"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sva_big_comparative_2 : Form Cell :=
  { id := "sva_big_comparative_2"
    lexeme := Lexemes.sva_big
    cell := comparative
    form := "xošēl"
    morphs := ["xo", "š", "ēl"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def sva_big_superlative : Form Cell :=
  { id := "sva_big_superlative"
    lexeme := Lexemes.sva_big
    cell := superlative
    form := "mašēne"
    morphs := ["ma", "š", "ēne"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def got_small_positive : Form Cell :=
  { id := "got_small_positive"
    lexeme := Lexemes.got_small
    cell := positive
    form := "leitils"
    morphs := ["leitils"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def got_small_comparative : Form Cell :=
  { id := "got_small_comparative"
    lexeme := Lexemes.got_small
    cell := comparative
    form := "minniza"
    morphs := ["minn", "iza"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def got_small_superlative : Form Cell :=
  { id := "got_small_superlative"
    lexeme := Lexemes.got_small
    cell := superlative
    form := "minnists"
    morphs := ["minn", "ists"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ang_small_positive : Form Cell :=
  { id := "ang_small_positive"
    lexeme := Lexemes.ang_small
    cell := positive
    form := "lýtel"
    morphs := ["lýtel"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ang_small_comparative : Form Cell :=
  { id := "ang_small_comparative"
    lexeme := Lexemes.ang_small
    cell := comparative
    form := "læssa"
    morphs := ["læssa"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def ang_small_superlative : Form Cell :=
  { id := "ang_small_superlative"
    lexeme := Lexemes.ang_small
    cell := superlative
    form := "læst"
    morphs := ["læ", "st"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def dan_small_positive : Form Cell :=
  { id := "dan_small_positive"
    lexeme := Lexemes.dan_small
    cell := positive
    form := "små"
    morphs := ["små"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def dan_small_comparative : Form Cell :=
  { id := "dan_small_comparative"
    lexeme := Lexemes.dan_small
    cell := comparative
    form := "mindre"
    morphs := ["mind", "re"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def dan_small_superlative : Form Cell :=
  { id := "dan_small_superlative"
    lexeme := Lexemes.dan_small
    cell := superlative
    form := "mindst"
    morphs := ["mind", "st"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def hbs_small_positive : Form Cell :=
  { id := "hbs_small_positive"
    lexeme := Lexemes.hbs_small
    cell := positive
    form := "mali"
    morphs := ["mali"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def hbs_small_positive_2 : Form Cell :=
  { id := "hbs_small_positive_2"
    lexeme := Lexemes.hbs_small
    cell := positive
    form := "malen"
    morphs := ["malen"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def hbs_small_comparative : Form Cell :=
  { id := "hbs_small_comparative"
    lexeme := Lexemes.hbs_small
    cell := comparative
    form := "manji"
    morphs := ["man", "ji"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def hbs_small_superlative : Form Cell :=
  { id := "hbs_small_superlative"
    lexeme := Lexemes.hbs_small
    cell := superlative
    form := "najmanji"
    morphs := ["naj", "man", "ji"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def lat_small_positive : Form Cell :=
  { id := "lat_small_positive"
    lexeme := Lexemes.lat_small
    cell := positive
    form := "parvus"
    morphs := ["parvus"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def lat_small_positive_2 : Form Cell :=
  { id := "lat_small_positive_2"
    lexeme := Lexemes.lat_small
    cell := positive
    form := "paulum"
    morphs := ["paulum"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def lat_small_comparative : Form Cell :=
  { id := "lat_small_comparative"
    lexeme := Lexemes.lat_small
    cell := comparative
    form := "minor"
    morphs := ["min", "or"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def lat_small_superlative : Form Cell :=
  { id := "lat_small_superlative"
    lexeme := Lexemes.lat_small
    cell := superlative
    form := "minimus"
    morphs := ["min", "imus"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_small_positive : Form Cell :=
  { id := "cym_small_positive"
    lexeme := Lexemes.cym_small
    cell := positive
    form := "bach"
    morphs := ["bach"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_small_comparative : Form Cell :=
  { id := "cym_small_comparative"
    lexeme := Lexemes.cym_small
    cell := comparative
    form := "llai"
    morphs := ["llai"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_small_superlative : Form Cell :=
  { id := "cym_small_superlative"
    lexeme := Lexemes.cym_small
    cell := superlative
    form := "lleiaf"
    morphs := ["llei", "af"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_small_positive : Form Cell :=
  { id := "grc_small_positive"
    lexeme := Lexemes.grc_small
    cell := positive
    form := "mikrós"
    morphs := ["mikr", "ós"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_small_comparative : Form Cell :=
  { id := "grc_small_comparative"
    lexeme := Lexemes.grc_small
    cell := comparative
    form := "meíōn"
    morphs := ["meí", "ōn"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_small_superlative : Form Cell :=
  { id := "grc_small_superlative"
    lexeme := Lexemes.grc_small
    cell := superlative
    form := "meĩstos"
    morphs := ["meĩ", "st", "os"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_small_comparative_2 : Form Cell :=
  { id := "grc_small_comparative_2"
    lexeme := Lexemes.grc_small
    cell := comparative
    form := "elássōn"
    morphs := ["eláss", "ōn"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def grc_small_superlative_2 : Form Cell :=
  { id := "grc_small_superlative_2"
    lexeme := Lexemes.grc_small
    cell := superlative
    form := "elachistos"
    morphs := ["elach", "ist", "os"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pal_small_positive : Form Cell :=
  { id := "pal_small_positive"
    lexeme := Lexemes.pal_small
    cell := positive
    form := "kōdag"
    morphs := ["kōdag"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pal_small_comparative : Form Cell :=
  { id := "pal_small_comparative"
    lexeme := Lexemes.pal_small
    cell := comparative
    form := "keh"
    morphs := ["keh"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def pal_small_superlative : Form Cell :=
  { id := "pal_small_superlative"
    lexeme := Lexemes.pal_small
    cell := superlative
    form := "kasišts"
    morphs := ["kas", "išts"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def non_old_positive : Form Cell :=
  { id := "non_old_positive"
    lexeme := Lexemes.non_old
    cell := positive
    form := "gamall"
    morphs := ["gamall"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def non_old_comparative : Form Cell :=
  { id := "non_old_comparative"
    lexeme := Lexemes.non_old
    cell := comparative
    form := "ellre"
    morphs := ["ell", "re"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def non_old_superlative : Form Cell :=
  { id := "non_old_superlative"
    lexeme := Lexemes.non_old
    cell := superlative
    form := "ellztr"
    morphs := ["ell", "ztr"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_near_positive : Form Cell :=
  { id := "cym_near_positive"
    lexeme := Lexemes.cym_near
    cell := positive
    form := "agos"
    morphs := ["agos"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_near_comparative : Form Cell :=
  { id := "cym_near_comparative"
    lexeme := Lexemes.cym_near
    cell := comparative
    form := "nes"
    morphs := ["nes"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_near_superlative : Form Cell :=
  { id := "cym_near_superlative"
    lexeme := Lexemes.cym_near
    cell := superlative
    form := "nesaf"
    morphs := ["nes", "af"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_strong_positive : Form Cell :=
  { id := "cym_strong_positive"
    lexeme := Lexemes.cym_strong
    cell := positive
    form := "cryf"
    morphs := ["cryf"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_strong_comparative : Form Cell :=
  { id := "cym_strong_comparative"
    lexeme := Lexemes.cym_strong
    cell := comparative
    form := "trech"
    morphs := ["trech"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def cym_strong_superlative : Form Cell :=
  { id := "cym_strong_superlative"
    lexeme := Lexemes.cym_strong
    cell := superlative
    form := "trechaf"
    morphs := ["trech", "af"]
    source := [
      ⟨"bobaljik-2012", "Table 4.1"⟩
    ] }

def eng_many_positive : Form Cell :=
  { id := "eng_many_positive"
    lexeme := Lexemes.eng_many
    cell := positive
    form := "many"
    morphs := ["many"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eng_many_comparative : Form Cell :=
  { id := "eng_many_comparative"
    lexeme := Lexemes.eng_many
    cell := comparative
    form := "more"
    morphs := ["mo", "re"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eng_many_superlative : Form Cell :=
  { id := "eng_many_superlative"
    lexeme := Lexemes.eng_many
    cell := superlative
    form := "most"
    morphs := ["mo", "st"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eng_much_positive : Form Cell :=
  { id := "eng_much_positive"
    lexeme := Lexemes.eng_much
    cell := positive
    form := "much"
    morphs := ["much"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eng_much_comparative : Form Cell :=
  { id := "eng_much_comparative"
    lexeme := Lexemes.eng_much
    cell := comparative
    form := "more"
    morphs := ["mo", "re"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eng_much_superlative : Form Cell :=
  { id := "eng_much_superlative"
    lexeme := Lexemes.eng_much
    cell := superlative
    form := "most"
    morphs := ["mo", "st"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eng_lot_positive : Form Cell :=
  { id := "eng_lot_positive"
    lexeme := Lexemes.eng_lot
    cell := positive
    form := "(a) lot"
    morphs := ["(a) lot"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eng_lot_comparative : Form Cell :=
  { id := "eng_lot_comparative"
    lexeme := Lexemes.eng_lot
    cell := comparative
    form := "more"
    morphs := ["mo", "re"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eng_lot_superlative : Form Cell :=
  { id := "eng_lot_superlative"
    lexeme := Lexemes.eng_lot
    cell := superlative
    form := "most"
    morphs := ["mo", "st"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def deu_many_positive : Form Cell :=
  { id := "deu_many_positive"
    lexeme := Lexemes.deu_many
    cell := positive
    form := "viel"
    morphs := ["viel"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def deu_many_comparative : Form Cell :=
  { id := "deu_many_comparative"
    lexeme := Lexemes.deu_many
    cell := comparative
    form := "mehr"
    morphs := ["me", "hr"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def deu_many_superlative : Form Cell :=
  { id := "deu_many_superlative"
    lexeme := Lexemes.deu_many
    cell := superlative
    form := "meist"
    morphs := ["mei", "st"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fao_many_positive : Form Cell :=
  { id := "fao_many_positive"
    lexeme := Lexemes.fao_many
    cell := positive
    form := "nógvur"
    morphs := ["nógv", "ur"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fao_many_comparative : Form Cell :=
  { id := "fao_many_comparative"
    lexeme := Lexemes.fao_many
    cell := comparative
    form := "meiri"
    morphs := ["mei", "ri"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fao_many_superlative : Form Cell :=
  { id := "fao_many_superlative"
    lexeme := Lexemes.fao_many
    cell := superlative
    form := "mestur"
    morphs := ["me", "st", "ur"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def afr_many_party_positive : Form Cell :=
  { id := "afr_many_party_positive"
    lexeme := Lexemes.afr_many_party
    cell := positive
    form := "party"
    morphs := ["party"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def afr_many_party_comparative : Form Cell :=
  { id := "afr_many_party_comparative"
    lexeme := Lexemes.afr_many_party
    cell := comparative
    form := "meer"
    morphs := ["me", "er"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def afr_many_party_superlative : Form Cell :=
  { id := "afr_many_party_superlative"
    lexeme := Lexemes.afr_many_party
    cell := superlative
    form := "meeste"
    morphs := ["mee", "ste"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def afr_many_baie_positive : Form Cell :=
  { id := "afr_many_baie_positive"
    lexeme := Lexemes.afr_many_baie
    cell := positive
    form := "baie"
    morphs := ["baie"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def afr_many_baie_comparative : Form Cell :=
  { id := "afr_many_baie_comparative"
    lexeme := Lexemes.afr_many_baie
    cell := comparative
    form := "meer"
    morphs := ["me", "er"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def afr_many_baie_superlative : Form Cell :=
  { id := "afr_many_baie_superlative"
    lexeme := Lexemes.afr_many_baie
    cell := superlative
    form := "meeste"
    morphs := ["mee", "ste"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def yid_many_positive : Form Cell :=
  { id := "yid_many_positive"
    lexeme := Lexemes.yid_many
    cell := positive
    form := "sakh"
    morphs := ["sakh"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def yid_many_comparative : Form Cell :=
  { id := "yid_many_comparative"
    lexeme := Lexemes.yid_many
    cell := comparative
    form := "mer"
    morphs := ["me", "r"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def yid_many_superlative : Form Cell :=
  { id := "yid_many_superlative"
    lexeme := Lexemes.yid_many
    cell := superlative
    form := "merste"
    morphs := ["me", "r", "ste"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def dan_many_positive : Form Cell :=
  { id := "dan_many_positive"
    lexeme := Lexemes.dan_many
    cell := positive
    form := "mange"
    morphs := ["mange"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def dan_many_comparative : Form Cell :=
  { id := "dan_many_comparative"
    lexeme := Lexemes.dan_many
    cell := comparative
    form := "flere"
    morphs := ["fle", "re"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def dan_many_superlative : Form Cell :=
  { id := "dan_many_superlative"
    lexeme := Lexemes.dan_many
    cell := superlative
    form := "flest"
    morphs := ["fle", "st"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ces_many_positive : Form Cell :=
  { id := "ces_many_positive"
    lexeme := Lexemes.ces_many
    cell := positive
    form := "mnoho"
    morphs := ["mnoho"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ces_many_comparative : Form Cell :=
  { id := "ces_many_comparative"
    lexeme := Lexemes.ces_many
    cell := comparative
    form := "více"
    morphs := ["víc", "e"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ces_many_superlative : Form Cell :=
  { id := "ces_many_superlative"
    lexeme := Lexemes.ces_many
    cell := superlative
    form := "nejvíce"
    morphs := ["nej", "víc", "e"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def rus_many_positive : Form Cell :=
  { id := "rus_many_positive"
    lexeme := Lexemes.rus_many
    cell := positive
    form := "mnogo"
    morphs := ["mnogo"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def rus_many_comparative : Form Cell :=
  { id := "rus_many_comparative"
    lexeme := Lexemes.rus_many
    cell := comparative
    form := "bol’še"
    morphs := ["bol’š", "e"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def rus_many_superlative : Form Cell :=
  { id := "rus_many_superlative"
    lexeme := Lexemes.rus_many
    cell := superlative
    form := "najbo’lšij"
    morphs := ["naj", "bo’lš", "ij"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def bul_many_positive : Form Cell :=
  { id := "bul_many_positive"
    lexeme := Lexemes.bul_many
    cell := positive
    form := "mnogo"
    morphs := ["mnogo"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def bul_many_comparative : Form Cell :=
  { id := "bul_many_comparative"
    lexeme := Lexemes.bul_many
    cell := comparative
    form := "poveče"
    morphs := ["po", "več", "e"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def bul_many_superlative : Form Cell :=
  { id := "bul_many_superlative"
    lexeme := Lexemes.bul_many
    cell := superlative
    form := "najmnogo"
    morphs := ["naj", "mnogo"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def pol_many_positive : Form Cell :=
  { id := "pol_many_positive"
    lexeme := Lexemes.pol_many
    cell := positive
    form := "wiele"
    morphs := ["wiele"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def pol_many_comparative : Form Cell :=
  { id := "pol_many_comparative"
    lexeme := Lexemes.pol_many
    cell := comparative
    form := "więcej"
    morphs := ["więc", "ej"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def pol_many_superlative : Form Cell :=
  { id := "pol_many_superlative"
    lexeme := Lexemes.pol_many
    cell := superlative
    form := "najwięcej"
    morphs := ["naj", "więc", "ej"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def hbs_many_positive : Form Cell :=
  { id := "hbs_many_positive"
    lexeme := Lexemes.hbs_many
    cell := positive
    form := "puno"
    morphs := ["puno"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def hbs_many_comparative : Form Cell :=
  { id := "hbs_many_comparative"
    lexeme := Lexemes.hbs_many
    cell := comparative
    form := "veće"
    morphs := ["već", "e"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def hbs_many_superlative : Form Cell :=
  { id := "hbs_many_superlative"
    lexeme := Lexemes.hbs_many
    cell := superlative
    form := "najveće"
    morphs := ["naj", "već", "e"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ukr_many_bahato_positive : Form Cell :=
  { id := "ukr_many_bahato_positive"
    lexeme := Lexemes.ukr_many_bahato
    cell := positive
    form := "baháto"
    morphs := ["baháto"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ukr_many_bahato_comparative : Form Cell :=
  { id := "ukr_many_bahato_comparative"
    lexeme := Lexemes.ukr_many_bahato
    cell := comparative
    form := "bil’šyj"
    morphs := ["bil’", "šyj"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ukr_many_bahato_superlative : Form Cell :=
  { id := "ukr_many_bahato_superlative"
    lexeme := Lexemes.ukr_many_bahato
    cell := superlative
    form := "najbil’šyj"
    morphs := ["naj", "bil’", "šyj"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ukr_many_duze_positive : Form Cell :=
  { id := "ukr_many_duze_positive"
    lexeme := Lexemes.ukr_many_duze
    cell := positive
    form := "dúže"
    morphs := ["dúže"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ukr_many_duze_comparative : Form Cell :=
  { id := "ukr_many_duze_comparative"
    lexeme := Lexemes.ukr_many_duze
    cell := comparative
    form := "bil’šyj"
    morphs := ["bil’", "šyj"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ukr_many_duze_superlative : Form Cell :=
  { id := "ukr_many_duze_superlative"
    lexeme := Lexemes.ukr_many_duze
    cell := superlative
    form := "najbil’šyj"
    morphs := ["naj", "bil’", "šyj"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def lav_many_positive : Form Cell :=
  { id := "lav_many_positive"
    lexeme := Lexemes.lav_many
    cell := positive
    form := "daudz"
    morphs := ["daudz"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def lav_many_comparative : Form Cell :=
  { id := "lav_many_comparative"
    lexeme := Lexemes.lav_many
    cell := comparative
    form := "vairâk"
    morphs := ["vair", "âk"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def lav_many_superlative : Form Cell :=
  { id := "lav_many_superlative"
    lexeme := Lexemes.lav_many
    cell := superlative
    form := "visvairâk"
    morphs := ["vis", "vair", "âk"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def lat_many_positive : Form Cell :=
  { id := "lat_many_positive"
    lexeme := Lexemes.lat_many
    cell := positive
    form := "mult"
    morphs := ["mult-"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def lat_many_comparative : Form Cell :=
  { id := "lat_many_comparative"
    lexeme := Lexemes.lat_many
    cell := comparative
    form := "plūs"
    morphs := ["plū", "s"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def lat_many_superlative : Form Cell :=
  { id := "lat_many_superlative"
    lexeme := Lexemes.lat_many
    cell := superlative
    form := "plūrimus"
    morphs := ["plūr", "imu", "s"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def bre_many_positive : Form Cell :=
  { id := "bre_many_positive"
    lexeme := Lexemes.bre_many
    cell := positive
    form := "kalz"
    morphs := ["kalz"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def bre_many_comparative : Form Cell :=
  { id := "bre_many_comparative"
    lexeme := Lexemes.bre_many
    cell := comparative
    form := "mui(oc’h)"
    morphs := ["mui", "(oc’h)"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def bre_many_superlative : Form Cell :=
  { id := "bre_many_superlative"
    lexeme := Lexemes.bre_many
    cell := superlative
    form := "muiañ"
    morphs := ["mui", "añ"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def cym_many_positive : Form Cell :=
  { id := "cym_many_positive"
    lexeme := Lexemes.cym_many
    cell := positive
    form := "llawer"
    morphs := ["llawer"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def cym_many_comparative : Form Cell :=
  { id := "cym_many_comparative"
    lexeme := Lexemes.cym_many
    cell := comparative
    form := "mwy"
    morphs := ["mwy"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def cym_many_superlative : Form Cell :=
  { id := "cym_many_superlative"
    lexeme := Lexemes.cym_many
    cell := superlative
    form := "mwyaf"
    morphs := ["mwy", "af"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def grc_many_positive : Form Cell :=
  { id := "grc_many_positive"
    lexeme := Lexemes.grc_many
    cell := positive
    form := "polús"
    morphs := ["pol", "ús"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def grc_many_comparative : Form Cell :=
  { id := "grc_many_comparative"
    lexeme := Lexemes.grc_many
    cell := comparative
    form := "pleíōn"
    morphs := ["ple", "íōn"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def grc_many_superlative : Form Cell :=
  { id := "grc_many_superlative"
    lexeme := Lexemes.grc_many
    cell := superlative
    form := "pleĩstos"
    morphs := ["ple", "ĩst", "os"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def hye_many_positive : Form Cell :=
  { id := "hye_many_positive"
    lexeme := Lexemes.hye_many
    cell := positive
    form := "šaterë"
    morphs := ["šat", "erë"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def hye_many_comparative : Form Cell :=
  { id := "hye_many_comparative"
    lexeme := Lexemes.hye_many
    cell := comparative
    form := "aveli"
    morphs := ["aveli"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def hye_many_superlative : Form Cell :=
  { id := "hye_many_superlative"
    lexeme := Lexemes.hye_many
    cell := superlative
    form := "amenašat"
    morphs := ["amena", "šat"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fas_many_xele_positive : Form Cell :=
  { id := "fas_many_xele_positive"
    lexeme := Lexemes.fas_many_xele
    cell := positive
    form := "xele"
    morphs := ["xele"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fas_many_xele_comparative : Form Cell :=
  { id := "fas_many_xele_comparative"
    lexeme := Lexemes.fas_many_xele
    cell := comparative
    form := "beš(tar)"
    morphs := ["beš", "(tar)"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fas_many_xele_superlative : Form Cell :=
  { id := "fas_many_xele_superlative"
    lexeme := Lexemes.fas_many_xele
    cell := superlative
    form := "beštarin"
    morphs := ["beš", "tar", "in"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fas_many_ziad_positive : Form Cell :=
  { id := "fas_many_ziad_positive"
    lexeme := Lexemes.fas_many_ziad
    cell := positive
    form := "ziad"
    morphs := ["ziad"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fas_many_ziad_comparative : Form Cell :=
  { id := "fas_many_ziad_comparative"
    lexeme := Lexemes.fas_many_ziad
    cell := comparative
    form := "beš(tar)"
    morphs := ["beš", "(tar)"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fas_many_ziad_superlative : Form Cell :=
  { id := "fas_many_ziad_superlative"
    lexeme := Lexemes.fas_many_ziad
    cell := superlative
    form := "beštarin"
    morphs := ["beš", "tar", "in"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eus_many_positive : Form Cell :=
  { id := "eus_many_positive"
    lexeme := Lexemes.eus_many
    cell := positive
    form := "asko"
    morphs := ["asko"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eus_many_comparative : Form Cell :=
  { id := "eus_many_comparative"
    lexeme := Lexemes.eus_many
    cell := comparative
    form := "gehiago"
    morphs := ["gehi", "ago"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eus_many_superlative : Form Cell :=
  { id := "eus_many_superlative"
    lexeme := Lexemes.eus_many
    cell := superlative
    form := "gehien"
    morphs := ["gehi", "en"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fin_many_monet_positive : Form Cell :=
  { id := "fin_many_monet_positive"
    lexeme := Lexemes.fin_many_monet
    cell := positive
    form := "monet"
    morphs := ["monet"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fin_many_monet_comparative : Form Cell :=
  { id := "fin_many_monet_comparative"
    lexeme := Lexemes.fin_many_monet
    cell := comparative
    form := "useammat"
    morphs := ["usea", "mmat"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fin_many_monet_superlative : Form Cell :=
  { id := "fin_many_monet_superlative"
    lexeme := Lexemes.fin_many_monet
    cell := superlative
    form := "useimmat"
    morphs := ["use", "i", "mmat"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fin_many_paljon_positive : Form Cell :=
  { id := "fin_many_paljon_positive"
    lexeme := Lexemes.fin_many_paljon
    cell := positive
    form := "paljon"
    morphs := ["paljon"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fin_many_paljon_comparative : Form Cell :=
  { id := "fin_many_paljon_comparative"
    lexeme := Lexemes.fin_many_paljon
    cell := comparative
    form := "enemmän"
    morphs := ["ene", "mmän"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fin_many_paljon_superlative : Form Cell :=
  { id := "fin_many_paljon_superlative"
    lexeme := Lexemes.fin_many_paljon
    cell := superlative
    form := "eniten"
    morphs := ["en", "iten"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def krl_many_positive : Form Cell :=
  { id := "krl_many_positive"
    lexeme := Lexemes.krl_many
    cell := positive
    form := "äijä"
    morphs := ["äijä"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def krl_many_comparative : Form Cell :=
  { id := "krl_many_comparative"
    lexeme := Lexemes.krl_many
    cell := comparative
    form := "enämpi"
    morphs := ["enä", "mpi"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def krl_many_superlative : Form Cell :=
  { id := "krl_many_superlative"
    lexeme := Lexemes.krl_many
    cell := superlative
    form := "äijin"
    morphs := ["äij", "in"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def krl_many_superlative_questionnaire : Form Cell :=
  { id := "krl_many_superlative_questionnaire"
    lexeme := Lexemes.krl_many
    cell := superlative
    form := "äijin"
    morphs := ["äij", "in"]
    judgment := .ungrammatical
    source := [
      ⟨"bobaljik-2012", "p. 130"⟩
    ] }

def hun_many_positive : Form Cell :=
  { id := "hun_many_positive"
    lexeme := Lexemes.hun_many
    cell := positive
    form := "sok"
    morphs := ["sok"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def hun_many_comparative : Form Cell :=
  { id := "hun_many_comparative"
    lexeme := Lexemes.hun_many
    cell := comparative
    form := "több"
    morphs := ["tö", "bb"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def hun_many_superlative : Form Cell :=
  { id := "hun_many_superlative"
    lexeme := Lexemes.hun_many
    cell := superlative
    form := "legtöbb"
    morphs := ["leg", "tö", "bb"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def kat_many_positive : Form Cell :=
  { id := "kat_many_positive"
    lexeme := Lexemes.kat_many
    cell := positive
    form := "bevri"
    morphs := ["bevri"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def kat_many_comparative : Form Cell :=
  { id := "kat_many_comparative"
    lexeme := Lexemes.kat_many
    cell := comparative
    form := "met’i"
    morphs := ["met’", "i"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def kat_many_superlative : Form Cell :=
  { id := "kat_many_superlative"
    lexeme := Lexemes.kat_many
    cell := superlative
    form := "umet’esi"
    morphs := ["u", "met’", "es", "i"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def kbd_many_positive : Form Cell :=
  { id := "kbd_many_positive"
    lexeme := Lexemes.kbd_many
    cell := positive
    form := "kwad"
    morphs := ["kwad"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def kbd_many_positive_2 : Form Cell :=
  { id := "kbd_many_positive_2"
    lexeme := Lexemes.kbd_many
    cell := positive
    form := "ba"
    morphs := ["ba"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def kbd_many_comparative : Form Cell :=
  { id := "kbd_many_comparative"
    lexeme := Lexemes.kbd_many
    cell := comparative
    form := "nax"
    morphs := ["nax"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def kbd_many_superlative : Form Cell :=
  { id := "kbd_many_superlative"
    lexeme := Lexemes.kbd_many
    cell := superlative
    form := "naxdeda"
    morphs := ["nax", "deda"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eng_few_positive : Form Cell :=
  { id := "eng_few_positive"
    lexeme := Lexemes.eng_few
    cell := positive
    form := "(a) little"
    morphs := ["(a) little"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eng_few_comparative : Form Cell :=
  { id := "eng_few_comparative"
    lexeme := Lexemes.eng_few
    cell := comparative
    form := "less"
    morphs := ["less"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def eng_few_superlative : Form Cell :=
  { id := "eng_few_superlative"
    lexeme := Lexemes.eng_few
    cell := superlative
    form := "least"
    morphs := ["leas", "t"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def afr_few_positive : Form Cell :=
  { id := "afr_few_positive"
    lexeme := Lexemes.afr_few
    cell := positive
    form := "weinig"
    morphs := ["weinig"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def afr_few_comparative : Form Cell :=
  { id := "afr_few_comparative"
    lexeme := Lexemes.afr_few
    cell := comparative
    form := "minder"
    morphs := ["mind", "er"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def afr_few_superlative : Form Cell :=
  { id := "afr_few_superlative"
    lexeme := Lexemes.afr_few
    cell := superlative
    form := "mindste"
    morphs := ["mind", "ste"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fry_few_positive : Form Cell :=
  { id := "fry_few_positive"
    lexeme := Lexemes.fry_few
    cell := positive
    form := "(en) bytsje"
    morphs := ["(en) bytsje"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fry_few_comparative : Form Cell :=
  { id := "fry_few_comparative"
    lexeme := Lexemes.fry_few
    cell := comparative
    form := "minder"
    morphs := ["mind", "er"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def fry_few_superlative : Form Cell :=
  { id := "fry_few_superlative"
    lexeme := Lexemes.fry_few
    cell := superlative
    form := "minst"
    morphs := ["minst"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ukr_few_positive : Form Cell :=
  { id := "ukr_few_positive"
    lexeme := Lexemes.ukr_few
    cell := positive
    form := "troxi"
    morphs := ["troxi"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ukr_few_comparative : Form Cell :=
  { id := "ukr_few_comparative"
    lexeme := Lexemes.ukr_few
    cell := comparative
    form := "menše"
    morphs := ["men", "še"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def ukr_few_superlative : Form Cell :=
  { id := "ukr_few_superlative"
    lexeme := Lexemes.ukr_few
    cell := superlative
    form := "najmenšij"
    morphs := ["naj", "men", "šij"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def lat_few_positive : Form Cell :=
  { id := "lat_few_positive"
    lexeme := Lexemes.lat_few
    cell := positive
    form := "paucus"
    morphs := ["paucus"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def lat_few_comparative : Form Cell :=
  { id := "lat_few_comparative"
    lexeme := Lexemes.lat_few
    cell := comparative
    form := "minor"
    morphs := ["min", "or"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def lat_few_superlative : Form Cell :=
  { id := "lat_few_superlative"
    lexeme := Lexemes.lat_few
    cell := superlative
    form := "minimus"
    morphs := ["min", "imus"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def grc_few_positive : Form Cell :=
  { id := "grc_few_positive"
    lexeme := Lexemes.grc_few
    cell := positive
    form := "olígos"
    morphs := ["olíg", "os"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def grc_few_comparative : Form Cell :=
  { id := "grc_few_comparative"
    lexeme := Lexemes.grc_few
    cell := comparative
    form := "héssōn"
    morphs := ["héss", "ōn"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def grc_few_superlative : Form Cell :=
  { id := "grc_few_superlative"
    lexeme := Lexemes.grc_few
    cell := superlative
    form := "hékistos"
    morphs := ["hék", "ist", "os"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def grc_few_comparative_2 : Form Cell :=
  { id := "grc_few_comparative_2"
    lexeme := Lexemes.grc_few
    cell := comparative
    form := "meíōn"
    morphs := ["meí", "ōn"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def grc_few_superlative_2 : Form Cell :=
  { id := "grc_few_superlative_2"
    lexeme := Lexemes.grc_few
    cell := superlative
    form := "meĩstos"
    morphs := ["meĩ", "st", "os"]
    source := [
      ⟨"bobaljik-2012", "Table 4.2"⟩
    ] }

def krl_many_onego_positive : Form Cell :=
  { id := "krl_many_onego_positive"
    lexeme := Lexemes.krl_many_onego
    cell := positive
    form := "äijy"
    morphs := ["äijy"]
    source := [
      ⟨"bobaljik-2012", "(170)"⟩
    ] }

def krl_many_onego_comparative : Form Cell :=
  { id := "krl_many_onego_comparative"
    lexeme := Lexemes.krl_many_onego
    cell := comparative
    form := "enämbi"
    morphs := ["enä", "mbi"]
    source := [
      ⟨"bobaljik-2012", "(170)"⟩
    ] }

def krl_many_onego_superlative : Form Cell :=
  { id := "krl_many_onego_superlative"
    lexeme := Lexemes.krl_many_onego
    cell := superlative
    form := "enin"
    morphs := ["en", "in"]
    source := [
      ⟨"bobaljik-2012", "(170)"⟩
    ] }

def eng_good.roots : RootClasses Cell :=
  { id := "eng_good", lexeme := Lexemes.eng_good,
    forms := [eng_good_positive, eng_good_comparative, eng_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def swe_good.roots : RootClasses Cell :=
  { id := "swe_good", lexeme := Lexemes.swe_good,
    forms := [swe_good_positive, swe_good_comparative, swe_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def got_good.roots : RootClasses Cell :=
  { id := "got_good", lexeme := Lexemes.got_good,
    forms := [got_good_positive, got_good_comparative, got_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def cim_good.roots : RootClasses Cell :=
  { id := "cim_good", lexeme := Lexemes.cim_good,
    forms := [cim_good_positive, cim_good_comparative, cim_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def ces_good.roots : RootClasses Cell :=
  { id := "ces_good", lexeme := Lexemes.ces_good,
    forms := [ces_good_positive, ces_good_comparative, ces_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def hbs_good.roots : RootClasses Cell :=
  { id := "hbs_good", lexeme := Lexemes.hbs_good,
    forms := [hbs_good_positive, hbs_good_comparative, hbs_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def sorb_good.roots : RootClasses Cell :=
  { id := "sorb_good", lexeme := Lexemes.sorb_good,
    forms := [sorb_good_positive, sorb_good_comparative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "Table 4.1, note a"⟩
    ] }

def ukr_good_dobr.roots : RootClasses Cell :=
  { id := "ukr_good_dobr", lexeme := Lexemes.ukr_good_dobr,
    forms := [ukr_good_dobr_positive, ukr_good_dobr_comparative, ukr_good_dobr_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def ukr_good_harn.roots : RootClasses Cell :=
  { id := "ukr_good_harn", lexeme := Lexemes.ukr_good_harn,
    forms := [ukr_good_harn_positive, ukr_good_harn_comparative, ukr_good_harn_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def rus_good.roots : RootClasses Cell :=
  { id := "rus_good", lexeme := Lexemes.rus_good,
    forms := [rus_good_positive, rus_good_comparative, rus_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def lat_good.roots : RootClasses Cell :=
  { id := "lat_good", lexeme := Lexemes.lat_good,
    forms := [lat_good_positive, lat_good_comparative, lat_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 2)],
    source := [
      ⟨"bobaljik-2012", "(31a)"⟩
    ] }

def cym_good.roots : RootClasses Cell :=
  { id := "cym_good", lexeme := Lexemes.cym_good,
    forms := [cym_good_positive, cym_good_comparative, cym_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 2)],
    source := [
      ⟨"bobaljik-2012", "(31b)"⟩
    ] }

def sga_good.roots : RootClasses Cell :=
  { id := "sga_good", lexeme := Lexemes.sga_good,
    forms := [sga_good_positive, sga_good_comparative, sga_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 2)],
    source := [
      ⟨"bobaljik-2012", "(31c)"⟩
    ] }

def bre_good.roots : RootClasses Cell :=
  { id := "bre_good", lexeme := Lexemes.bre_good,
    forms := [bre_good_positive, bre_good_comparative, bre_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def grc_good_amein.roots : RootClasses Cell :=
  { id := "grc_good_amein", lexeme := Lexemes.grc_good,
    forms := [grc_good_positive, grc_good_comparative, grc_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 2)],
    source := [
      ⟨"bobaljik-2012", "p. 112"⟩
    ] }

def grc_good_arei.roots : RootClasses Cell :=
  { id := "grc_good_arei", lexeme := Lexemes.grc_good,
    forms := [grc_good_positive, grc_good_comparative_2, grc_good_superlative_2],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def grc_good_belt.roots : RootClasses Cell :=
  { id := "grc_good_belt", lexeme := Lexemes.grc_good,
    forms := [grc_good_positive, grc_good_comparative_3, grc_good_superlative_3],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def grc_good_kreiss.roots : RootClasses Cell :=
  { id := "grc_good_kreiss", lexeme := Lexemes.grc_good,
    forms := [grc_good_positive, grc_good_comparative_4, grc_good_superlative_4],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def grc_good_lo.roots : RootClasses Cell :=
  { id := "grc_good_lo", lexeme := Lexemes.grc_good,
    forms := [grc_good_positive, grc_good_comparative_5, grc_good_superlative_5],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def san_good_sre.roots : RootClasses Cell :=
  { id := "san_good_sre", lexeme := Lexemes.san_good,
    forms := [san_good_positive, san_good_comparative, san_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def san_good_jya.roots : RootClasses Cell :=
  { id := "san_good_jya", lexeme := Lexemes.san_good,
    forms := [san_good_positive, san_good_comparative_2, san_good_superlative_2],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def kho_good.roots : RootClasses Cell :=
  { id := "kho_good", lexeme := Lexemes.kho_good,
    forms := [kho_good_positive, kho_good_comparative, kho_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def pal_good.roots : RootClasses Cell :=
  { id := "pal_good", lexeme := Lexemes.pal_good,
    forms := [pal_good_positive, pal_good_comparative, pal_good_superlative,
      pal_good_superlative_2],
    classes := [(positive, 0), (comparative, 1), (superlative, 2)],
    source := [
      ⟨"bobaljik-2012", "(31d)"⟩
    ] }

def fas_good.roots : RootClasses Cell :=
  { id := "fas_good", lexeme := Lexemes.fas_good,
    forms := [fas_good_positive, fas_good_comparative, fas_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def eus_good_hobe.roots : RootClasses Cell :=
  { id := "eus_good_hobe", lexeme := Lexemes.eus_good,
    forms := [eus_good_positive, eus_good_comparative, eus_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def eus_good_on.roots : RootClasses Cell :=
  { id := "eus_good_on", lexeme := Lexemes.eus_good,
    forms := [eus_good_positive, eus_good_comparative, eus_good_superlative_2],
    classes := [(positive, 0), (comparative, 1), (superlative, 0)],
    source := [
      ⟨"bobaljik-2012", "(143)"⟩
    ] }

def fin_good.roots : RootClasses Cell :=
  { id := "fin_good", lexeme := Lexemes.fin_good,
    forms := [fin_good_positive, fin_good_comparative, fin_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def sjd_good.roots : RootClasses Cell :=
  { id := "sjd_good", lexeme := Lexemes.sjd_good,
    forms := [sjd_good_positive, sjd_good_comparative, sjd_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def kat_good_mjob.roots : RootClasses Cell :=
  { id := "kat_good_mjob", lexeme := Lexemes.kat_good,
    forms := [kat_good_positive, kat_good_comparative, kat_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def kat_good_ket.roots : RootClasses Cell :=
  { id := "kat_good_ket", lexeme := Lexemes.kat_good,
    forms := [kat_good_positive, kat_good_comparative_2, kat_good_superlative_2],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def sva_good.roots : RootClasses Cell :=
  { id := "sva_good", lexeme := Lexemes.sva_good,
    forms := [sva_good_positive, sva_good_comparative, sva_good_comparative_2,
      sva_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def chr_good.roots : RootClasses Cell :=
  { id := "chr_good", lexeme := Lexemes.chr_good,
    forms := [chr_good_positive, chr_good_comparative, chr_good_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def eng_bad.roots : RootClasses Cell :=
  { id := "eng_bad", lexeme := Lexemes.eng_bad,
    forms := [eng_bad_positive, eng_bad_comparative, eng_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def goh_bad.roots : RootClasses Cell :=
  { id := "goh_bad", lexeme := Lexemes.goh_bad,
    forms := [goh_bad_positive, goh_bad_comparative, goh_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def non_bad_vandr.roots : RootClasses Cell :=
  { id := "non_bad_vandr", lexeme := Lexemes.non_bad_vandr,
    forms := [non_bad_vandr_positive, non_bad_vandr_comparative, non_bad_vandr_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def non_bad_illr.roots : RootClasses Cell :=
  { id := "non_bad_illr", lexeme := Lexemes.non_bad_illr,
    forms := [non_bad_illr_positive, non_bad_illr_comparative, non_bad_illr_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def dan_bad.roots : RootClasses Cell :=
  { id := "dan_bad", lexeme := Lexemes.dan_bad,
    forms := [dan_bad_positive, dan_bad_comparative, dan_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def fao_bad.roots : RootClasses Cell :=
  { id := "fao_bad", lexeme := Lexemes.fao_bad,
    forms := [fao_bad_positive, fao_bad_comparative, fao_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def swe_bad_var.roots : RootClasses Cell :=
  { id := "swe_bad_var", lexeme := Lexemes.swe_bad,
    forms := [swe_bad_positive, swe_bad_comparative, swe_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def swe_bad_sam.roots : RootClasses Cell :=
  { id := "swe_bad_sam", lexeme := Lexemes.swe_bad,
    forms := [swe_bad_positive, swe_bad_comparative_2, swe_bad_superlative_2],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def yid_bad.roots : RootClasses Cell :=
  { id := "yid_bad", lexeme := Lexemes.yid_bad,
    forms := [yid_bad_positive, yid_bad_comparative, yid_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def pol_bad.roots : RootClasses Cell :=
  { id := "pol_bad", lexeme := Lexemes.pol_bad,
    forms := [pol_bad_positive, pol_bad_comparative, pol_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def ces_bad.roots : RootClasses Cell :=
  { id := "ces_bad", lexeme := Lexemes.ces_bad,
    forms := [ces_bad_positive, ces_bad_comparative, ces_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def ukr_bad.roots : RootClasses Cell :=
  { id := "ukr_bad", lexeme := Lexemes.ukr_bad,
    forms := [ukr_bad_positive, ukr_bad_comparative, ukr_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def bel_bad_drenn.roots : RootClasses Cell :=
  { id := "bel_bad_drenn", lexeme := Lexemes.bel_bad_drenn,
    forms := [bel_bad_drenn_positive, bel_bad_drenn_comparative, bel_bad_drenn_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def bel_bad_blah.roots : RootClasses Cell :=
  { id := "bel_bad_blah", lexeme := Lexemes.bel_bad_blah,
    forms := [bel_bad_blah_positive, bel_bad_blah_comparative, bel_bad_blah_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def hbs_bad.roots : RootClasses Cell :=
  { id := "hbs_bad", lexeme := Lexemes.hbs_bad,
    forms := [hbs_bad_positive, hbs_bad_comparative, hbs_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def rus_bad.roots : RootClasses Cell :=
  { id := "rus_bad", lexeme := Lexemes.rus_bad,
    forms := [rus_bad_positive, rus_bad_comparative, rus_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def lat_bad.roots : RootClasses Cell :=
  { id := "lat_bad", lexeme := Lexemes.lat_bad,
    forms := [lat_bad_positive, lat_bad_comparative, lat_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def sga_bad.roots : RootClasses Cell :=
  { id := "sga_bad", lexeme := Lexemes.sga_bad,
    forms := [sga_bad_positive, sga_bad_comparative, sga_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def cym_bad.roots : RootClasses Cell :=
  { id := "cym_bad", lexeme := Lexemes.cym_bad,
    forms := [cym_bad_positive, cym_bad_comparative, cym_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def bre_bad.roots : RootClasses Cell :=
  { id := "bre_bad", lexeme := Lexemes.bre_bad,
    forms := [bre_bad_positive, bre_bad_comparative, bre_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def grc_bad_cheir.roots : RootClasses Cell :=
  { id := "grc_bad_cheir", lexeme := Lexemes.grc_bad,
    forms := [grc_bad_positive, grc_bad_comparative, grc_bad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def grc_bad_hess.roots : RootClasses Cell :=
  { id := "grc_bad_hess", lexeme := Lexemes.grc_bad,
    forms := [grc_bad_positive, grc_bad_comparative_2, grc_bad_superlative_2],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def got_big.roots : RootClasses Cell :=
  { id := "got_big", lexeme := Lexemes.got_big,
    forms := [got_big_positive, got_big_comparative, got_big_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def ces_big.roots : RootClasses Cell :=
  { id := "ces_big", lexeme := Lexemes.ces_big,
    forms := [ces_big_positive, ces_big_comparative, ces_big_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def ukr_big.roots : RootClasses Cell :=
  { id := "ukr_big", lexeme := Lexemes.ukr_big,
    forms := [ukr_big_positive, ukr_big_comparative, ukr_big_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def pol_big.roots : RootClasses Cell :=
  { id := "pol_big", lexeme := Lexemes.pol_big,
    forms := [pol_big_positive, pol_big_comparative, pol_big_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def cym_big.roots : RootClasses Cell :=
  { id := "cym_big", lexeme := Lexemes.cym_big,
    forms := [cym_big_positive, cym_big_comparative, cym_big_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def pal_big.roots : RootClasses Cell :=
  { id := "pal_big", lexeme := Lexemes.pal_big,
    forms := [pal_big_positive, pal_big_comparative, pal_big_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def sva_big.roots : RootClasses Cell :=
  { id := "sva_big", lexeme := Lexemes.sva_big,
    forms := [sva_big_positive, sva_big_comparative, sva_big_comparative_2, sva_big_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def got_small.roots : RootClasses Cell :=
  { id := "got_small", lexeme := Lexemes.got_small,
    forms := [got_small_positive, got_small_comparative, got_small_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def ang_small.roots : RootClasses Cell :=
  { id := "ang_small", lexeme := Lexemes.ang_small,
    forms := [ang_small_positive, ang_small_comparative, ang_small_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def dan_small.roots : RootClasses Cell :=
  { id := "dan_small", lexeme := Lexemes.dan_small,
    forms := [dan_small_positive, dan_small_comparative, dan_small_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def hbs_small.roots : RootClasses Cell :=
  { id := "hbs_small", lexeme := Lexemes.hbs_small,
    forms := [hbs_small_positive, hbs_small_positive_2, hbs_small_comparative,
      hbs_small_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def lat_small.roots : RootClasses Cell :=
  { id := "lat_small", lexeme := Lexemes.lat_small,
    forms := [lat_small_positive, lat_small_positive_2, lat_small_comparative,
      lat_small_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def cym_small.roots : RootClasses Cell :=
  { id := "cym_small", lexeme := Lexemes.cym_small,
    forms := [cym_small_positive, cym_small_comparative, cym_small_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def grc_small_mei.roots : RootClasses Cell :=
  { id := "grc_small_mei", lexeme := Lexemes.grc_small,
    forms := [grc_small_positive, grc_small_comparative, grc_small_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def grc_small_elass.roots : RootClasses Cell :=
  { id := "grc_small_elass", lexeme := Lexemes.grc_small,
    forms := [grc_small_positive, grc_small_comparative_2, grc_small_superlative_2],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def pal_small.roots : RootClasses Cell :=
  { id := "pal_small", lexeme := Lexemes.pal_small,
    forms := [pal_small_positive, pal_small_comparative, pal_small_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def non_old.roots : RootClasses Cell :=
  { id := "non_old", lexeme := Lexemes.non_old,
    forms := [non_old_positive, non_old_comparative, non_old_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def cym_near.roots : RootClasses Cell :=
  { id := "cym_near", lexeme := Lexemes.cym_near,
    forms := [cym_near_positive, cym_near_comparative, cym_near_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def cym_strong.roots : RootClasses Cell :=
  { id := "cym_strong", lexeme := Lexemes.cym_strong,
    forms := [cym_strong_positive, cym_strong_comparative, cym_strong_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 109"⟩
    ] }

def eng_many.roots : RootClasses Cell :=
  { id := "eng_many", lexeme := Lexemes.eng_many,
    forms := [eng_many_positive, eng_many_comparative, eng_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def eng_much.roots : RootClasses Cell :=
  { id := "eng_much", lexeme := Lexemes.eng_much,
    forms := [eng_much_positive, eng_much_comparative, eng_much_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def eng_lot.roots : RootClasses Cell :=
  { id := "eng_lot", lexeme := Lexemes.eng_lot,
    forms := [eng_lot_positive, eng_lot_comparative, eng_lot_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def deu_many.roots : RootClasses Cell :=
  { id := "deu_many", lexeme := Lexemes.deu_many,
    forms := [deu_many_positive, deu_many_comparative, deu_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def fao_many.roots : RootClasses Cell :=
  { id := "fao_many", lexeme := Lexemes.fao_many,
    forms := [fao_many_positive, fao_many_comparative, fao_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def afr_many_party.roots : RootClasses Cell :=
  { id := "afr_many_party", lexeme := Lexemes.afr_many_party,
    forms := [afr_many_party_positive, afr_many_party_comparative, afr_many_party_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def afr_many_baie.roots : RootClasses Cell :=
  { id := "afr_many_baie", lexeme := Lexemes.afr_many_baie,
    forms := [afr_many_baie_positive, afr_many_baie_comparative, afr_many_baie_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def yid_many.roots : RootClasses Cell :=
  { id := "yid_many", lexeme := Lexemes.yid_many,
    forms := [yid_many_positive, yid_many_comparative, yid_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def dan_many.roots : RootClasses Cell :=
  { id := "dan_many", lexeme := Lexemes.dan_many,
    forms := [dan_many_positive, dan_many_comparative, dan_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def ces_many.roots : RootClasses Cell :=
  { id := "ces_many", lexeme := Lexemes.ces_many,
    forms := [ces_many_positive, ces_many_comparative, ces_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def rus_many.roots : RootClasses Cell :=
  { id := "rus_many", lexeme := Lexemes.rus_many,
    forms := [rus_many_positive, rus_many_comparative, rus_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def bul_many.roots : RootClasses Cell :=
  { id := "bul_many", lexeme := Lexemes.bul_many,
    forms := [bul_many_positive, bul_many_comparative, bul_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 0)],
    source := [
      ⟨"bobaljik-2012", "(165c)"⟩
    ] }

def pol_many.roots : RootClasses Cell :=
  { id := "pol_many", lexeme := Lexemes.pol_many,
    forms := [pol_many_positive, pol_many_comparative, pol_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def hbs_many.roots : RootClasses Cell :=
  { id := "hbs_many", lexeme := Lexemes.hbs_many,
    forms := [hbs_many_positive, hbs_many_comparative, hbs_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def ukr_many_bahato.roots : RootClasses Cell :=
  { id := "ukr_many_bahato", lexeme := Lexemes.ukr_many_bahato,
    forms := [ukr_many_bahato_positive, ukr_many_bahato_comparative, ukr_many_bahato_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def ukr_many_duze.roots : RootClasses Cell :=
  { id := "ukr_many_duze", lexeme := Lexemes.ukr_many_duze,
    forms := [ukr_many_duze_positive, ukr_many_duze_comparative, ukr_many_duze_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def lav_many.roots : RootClasses Cell :=
  { id := "lav_many", lexeme := Lexemes.lav_many,
    forms := [lav_many_positive, lav_many_comparative, lav_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def lat_many.roots : RootClasses Cell :=
  { id := "lat_many", lexeme := Lexemes.lat_many,
    forms := [lat_many_positive, lat_many_comparative, lat_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def bre_many.roots : RootClasses Cell :=
  { id := "bre_many", lexeme := Lexemes.bre_many,
    forms := [bre_many_positive, bre_many_comparative, bre_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def cym_many.roots : RootClasses Cell :=
  { id := "cym_many", lexeme := Lexemes.cym_many,
    forms := [cym_many_positive, cym_many_comparative, cym_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def grc_many.roots : RootClasses Cell :=
  { id := "grc_many", lexeme := Lexemes.grc_many,
    forms := [grc_many_positive, grc_many_comparative, grc_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def hye_many.roots : RootClasses Cell :=
  { id := "hye_many", lexeme := Lexemes.hye_many,
    forms := [hye_many_positive, hye_many_comparative, hye_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 0)],
    source := [
      ⟨"bobaljik-2012", "(165b)"⟩
    ] }

def fas_many_xele.roots : RootClasses Cell :=
  { id := "fas_many_xele", lexeme := Lexemes.fas_many_xele,
    forms := [fas_many_xele_positive, fas_many_xele_comparative, fas_many_xele_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def fas_many_ziad.roots : RootClasses Cell :=
  { id := "fas_many_ziad", lexeme := Lexemes.fas_many_ziad,
    forms := [fas_many_ziad_positive, fas_many_ziad_comparative, fas_many_ziad_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def eus_many.roots : RootClasses Cell :=
  { id := "eus_many", lexeme := Lexemes.eus_many,
    forms := [eus_many_positive, eus_many_comparative, eus_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def fin_many_monet.roots : RootClasses Cell :=
  { id := "fin_many_monet", lexeme := Lexemes.fin_many_monet,
    forms := [fin_many_monet_positive, fin_many_monet_comparative, fin_many_monet_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def fin_many_paljon.roots : RootClasses Cell :=
  { id := "fin_many_paljon", lexeme := Lexemes.fin_many_paljon,
    forms := [fin_many_paljon_positive, fin_many_paljon_comparative, fin_many_paljon_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def krl_many.roots : RootClasses Cell :=
  { id := "krl_many", lexeme := Lexemes.krl_many,
    forms := [krl_many_positive, krl_many_comparative, krl_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 0)],
    source := [
      ⟨"bobaljik-2012", "(165a)"⟩
    ] }

def hun_many.roots : RootClasses Cell :=
  { id := "hun_many", lexeme := Lexemes.hun_many,
    forms := [hun_many_positive, hun_many_comparative, hun_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def kat_many.roots : RootClasses Cell :=
  { id := "kat_many", lexeme := Lexemes.kat_many,
    forms := [kat_many_positive, kat_many_comparative, kat_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def kbd_many.roots : RootClasses Cell :=
  { id := "kbd_many", lexeme := Lexemes.kbd_many,
    forms := [kbd_many_positive, kbd_many_positive_2, kbd_many_comparative, kbd_many_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def eng_few.roots : RootClasses Cell :=
  { id := "eng_few", lexeme := Lexemes.eng_few,
    forms := [eng_few_positive, eng_few_comparative, eng_few_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def afr_few.roots : RootClasses Cell :=
  { id := "afr_few", lexeme := Lexemes.afr_few,
    forms := [afr_few_positive, afr_few_comparative, afr_few_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def fry_few.roots : RootClasses Cell :=
  { id := "fry_few", lexeme := Lexemes.fry_few,
    forms := [fry_few_positive, fry_few_comparative, fry_few_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def ukr_few.roots : RootClasses Cell :=
  { id := "ukr_few", lexeme := Lexemes.ukr_few,
    forms := [ukr_few_positive, ukr_few_comparative, ukr_few_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def lat_few.roots : RootClasses Cell :=
  { id := "lat_few", lexeme := Lexemes.lat_few,
    forms := [lat_few_positive, lat_few_comparative, lat_few_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def grc_few_hess.roots : RootClasses Cell :=
  { id := "grc_few_hess", lexeme := Lexemes.grc_few,
    forms := [grc_few_positive, grc_few_comparative, grc_few_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def grc_few_mei.roots : RootClasses Cell :=
  { id := "grc_few_mei", lexeme := Lexemes.grc_few,
    forms := [grc_few_positive, grc_few_comparative_2, grc_few_superlative_2],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "p. 126"⟩
    ] }

def krl_many_onego.roots : RootClasses Cell :=
  { id := "krl_many_onego", lexeme := Lexemes.krl_many_onego,
    forms := [krl_many_onego_positive, krl_many_onego_comparative, krl_many_onego_superlative],
    classes := [(positive, 0), (comparative, 1), (superlative, 1)],
    source := [
      ⟨"bobaljik-2012", "(170)"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.eng_good, Lexemes.swe_good, Lexemes.got_good,
  Lexemes.cim_good, Lexemes.ces_good, Lexemes.hbs_good, Lexemes.sorb_good, Lexemes.ukr_good_dobr,
  Lexemes.ukr_good_harn, Lexemes.rus_good, Lexemes.lat_good, Lexemes.cym_good, Lexemes.sga_good,
  Lexemes.bre_good, Lexemes.grc_good, Lexemes.san_good, Lexemes.kho_good, Lexemes.pal_good,
  Lexemes.fas_good, Lexemes.eus_good, Lexemes.fin_good, Lexemes.sjd_good, Lexemes.kat_good,
  Lexemes.sva_good, Lexemes.chr_good, Lexemes.eng_bad, Lexemes.goh_bad, Lexemes.non_bad_vandr,
  Lexemes.non_bad_illr, Lexemes.dan_bad, Lexemes.fao_bad, Lexemes.swe_bad, Lexemes.yid_bad,
  Lexemes.pol_bad, Lexemes.ces_bad, Lexemes.ukr_bad, Lexemes.bel_bad_drenn, Lexemes.bel_bad_blah,
  Lexemes.hbs_bad, Lexemes.rus_bad, Lexemes.lat_bad, Lexemes.sga_bad, Lexemes.cym_bad,
  Lexemes.bre_bad, Lexemes.grc_bad, Lexemes.got_big, Lexemes.ces_big, Lexemes.ukr_big,
  Lexemes.pol_big, Lexemes.cym_big, Lexemes.pal_big, Lexemes.sva_big, Lexemes.got_small,
  Lexemes.ang_small, Lexemes.dan_small, Lexemes.hbs_small, Lexemes.lat_small, Lexemes.cym_small,
  Lexemes.grc_small, Lexemes.pal_small, Lexemes.non_old, Lexemes.cym_near, Lexemes.cym_strong,
  Lexemes.eng_many, Lexemes.eng_much, Lexemes.eng_lot, Lexemes.deu_many, Lexemes.fao_many,
  Lexemes.afr_many_party, Lexemes.afr_many_baie, Lexemes.yid_many, Lexemes.dan_many,
  Lexemes.ces_many, Lexemes.rus_many, Lexemes.bul_many, Lexemes.pol_many, Lexemes.hbs_many,
  Lexemes.ukr_many_bahato, Lexemes.ukr_many_duze, Lexemes.lav_many, Lexemes.lat_many,
  Lexemes.bre_many, Lexemes.cym_many, Lexemes.grc_many, Lexemes.hye_many, Lexemes.fas_many_xele,
  Lexemes.fas_many_ziad, Lexemes.eus_many, Lexemes.fin_many_monet, Lexemes.fin_many_paljon,
  Lexemes.krl_many, Lexemes.hun_many, Lexemes.kat_many, Lexemes.kbd_many, Lexemes.eng_few,
  Lexemes.afr_few, Lexemes.fry_few, Lexemes.ukr_few, Lexemes.lat_few, Lexemes.grc_few,
  Lexemes.krl_many_onego]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [eng_good_positive, eng_good_comparative, eng_good_superlative,
  swe_good_positive, swe_good_comparative, swe_good_superlative, got_good_positive,
  got_good_comparative, got_good_superlative, cim_good_positive, cim_good_comparative,
  cim_good_superlative, ces_good_positive, ces_good_comparative, ces_good_superlative,
  hbs_good_positive, hbs_good_comparative, hbs_good_superlative, sorb_good_positive,
  sorb_good_comparative, ukr_good_dobr_positive, ukr_good_dobr_comparative,
  ukr_good_dobr_superlative, ukr_good_harn_positive, ukr_good_harn_comparative,
  ukr_good_harn_superlative, rus_good_positive, rus_good_comparative, rus_good_superlative,
  lat_good_positive, lat_good_comparative, lat_good_superlative, cym_good_positive,
  cym_good_comparative, cym_good_superlative, sga_good_positive, sga_good_comparative,
  sga_good_superlative, bre_good_positive, bre_good_comparative, bre_good_superlative,
  grc_good_positive, grc_good_comparative, grc_good_superlative, grc_good_comparative_2,
  grc_good_superlative_2, grc_good_comparative_3, grc_good_superlative_3, grc_good_comparative_4,
  grc_good_superlative_4, grc_good_comparative_5, grc_good_superlative_5, san_good_positive,
  san_good_comparative, san_good_superlative, san_good_comparative_2, san_good_superlative_2,
  kho_good_positive, kho_good_comparative, kho_good_superlative, pal_good_positive,
  pal_good_comparative, pal_good_superlative, pal_good_superlative_2, fas_good_positive,
  fas_good_comparative, fas_good_superlative, eus_good_positive, eus_good_comparative,
  eus_good_superlative, eus_good_superlative_2, fin_good_positive, fin_good_comparative,
  fin_good_superlative, sjd_good_positive, sjd_good_comparative, sjd_good_superlative,
  kat_good_positive, kat_good_comparative, kat_good_superlative, kat_good_comparative_2,
  kat_good_superlative_2, sva_good_positive, sva_good_comparative, sva_good_comparative_2,
  sva_good_superlative, chr_good_positive, chr_good_comparative, chr_good_superlative,
  eng_bad_positive, eng_bad_comparative, eng_bad_superlative, goh_bad_positive, goh_bad_comparative,
  goh_bad_superlative, non_bad_vandr_positive, non_bad_vandr_comparative, non_bad_vandr_superlative,
  non_bad_illr_positive, non_bad_illr_comparative, non_bad_illr_superlative, dan_bad_positive,
  dan_bad_comparative, dan_bad_superlative, fao_bad_positive, fao_bad_comparative,
  fao_bad_superlative, swe_bad_positive, swe_bad_comparative, swe_bad_superlative,
  swe_bad_comparative_2, swe_bad_superlative_2, yid_bad_positive, yid_bad_comparative,
  yid_bad_superlative, pol_bad_positive, pol_bad_comparative, pol_bad_superlative, ces_bad_positive,
  ces_bad_comparative, ces_bad_superlative, ukr_bad_positive, ukr_bad_comparative,
  ukr_bad_superlative, bel_bad_drenn_positive, bel_bad_drenn_comparative, bel_bad_drenn_superlative,
  bel_bad_blah_positive, bel_bad_blah_comparative, bel_bad_blah_superlative, hbs_bad_positive,
  hbs_bad_comparative, hbs_bad_superlative, rus_bad_positive, rus_bad_comparative,
  rus_bad_superlative, lat_bad_positive, lat_bad_comparative, lat_bad_superlative, sga_bad_positive,
  sga_bad_comparative, sga_bad_superlative, cym_bad_positive, cym_bad_comparative,
  cym_bad_superlative, bre_bad_positive, bre_bad_comparative, bre_bad_superlative, grc_bad_positive,
  grc_bad_comparative, grc_bad_superlative, grc_bad_comparative_2, grc_bad_superlative_2,
  got_big_positive, got_big_comparative, got_big_superlative, ces_big_positive, ces_big_comparative,
  ces_big_superlative, ukr_big_positive, ukr_big_comparative, ukr_big_superlative, pol_big_positive,
  pol_big_comparative, pol_big_superlative, cym_big_positive, cym_big_comparative,
  cym_big_superlative, pal_big_positive, pal_big_comparative, pal_big_superlative, sva_big_positive,
  sva_big_comparative, sva_big_comparative_2, sva_big_superlative, got_small_positive,
  got_small_comparative, got_small_superlative, ang_small_positive, ang_small_comparative,
  ang_small_superlative, dan_small_positive, dan_small_comparative, dan_small_superlative,
  hbs_small_positive, hbs_small_positive_2, hbs_small_comparative, hbs_small_superlative,
  lat_small_positive, lat_small_positive_2, lat_small_comparative, lat_small_superlative,
  cym_small_positive, cym_small_comparative, cym_small_superlative, grc_small_positive,
  grc_small_comparative, grc_small_superlative, grc_small_comparative_2, grc_small_superlative_2,
  pal_small_positive, pal_small_comparative, pal_small_superlative, non_old_positive,
  non_old_comparative, non_old_superlative, cym_near_positive, cym_near_comparative,
  cym_near_superlative, cym_strong_positive, cym_strong_comparative, cym_strong_superlative,
  eng_many_positive, eng_many_comparative, eng_many_superlative, eng_much_positive,
  eng_much_comparative, eng_much_superlative, eng_lot_positive, eng_lot_comparative,
  eng_lot_superlative, deu_many_positive, deu_many_comparative, deu_many_superlative,
  fao_many_positive, fao_many_comparative, fao_many_superlative, afr_many_party_positive,
  afr_many_party_comparative, afr_many_party_superlative, afr_many_baie_positive,
  afr_many_baie_comparative, afr_many_baie_superlative, yid_many_positive, yid_many_comparative,
  yid_many_superlative, dan_many_positive, dan_many_comparative, dan_many_superlative,
  ces_many_positive, ces_many_comparative, ces_many_superlative, rus_many_positive,
  rus_many_comparative, rus_many_superlative, bul_many_positive, bul_many_comparative,
  bul_many_superlative, pol_many_positive, pol_many_comparative, pol_many_superlative,
  hbs_many_positive, hbs_many_comparative, hbs_many_superlative, ukr_many_bahato_positive,
  ukr_many_bahato_comparative, ukr_many_bahato_superlative, ukr_many_duze_positive,
  ukr_many_duze_comparative, ukr_many_duze_superlative, lav_many_positive, lav_many_comparative,
  lav_many_superlative, lat_many_positive, lat_many_comparative, lat_many_superlative,
  bre_many_positive, bre_many_comparative, bre_many_superlative, cym_many_positive,
  cym_many_comparative, cym_many_superlative, grc_many_positive, grc_many_comparative,
  grc_many_superlative, hye_many_positive, hye_many_comparative, hye_many_superlative,
  fas_many_xele_positive, fas_many_xele_comparative, fas_many_xele_superlative,
  fas_many_ziad_positive, fas_many_ziad_comparative, fas_many_ziad_superlative, eus_many_positive,
  eus_many_comparative, eus_many_superlative, fin_many_monet_positive, fin_many_monet_comparative,
  fin_many_monet_superlative, fin_many_paljon_positive, fin_many_paljon_comparative,
  fin_many_paljon_superlative, krl_many_positive, krl_many_comparative, krl_many_superlative,
  hun_many_positive, hun_many_comparative, hun_many_superlative, kat_many_positive,
  kat_many_comparative, kat_many_superlative, kbd_many_positive, kbd_many_positive_2,
  kbd_many_comparative, kbd_many_superlative, eng_few_positive, eng_few_comparative,
  eng_few_superlative, afr_few_positive, afr_few_comparative, afr_few_superlative, fry_few_positive,
  fry_few_comparative, fry_few_superlative, ukr_few_positive, ukr_few_comparative,
  ukr_few_superlative, lat_few_positive, lat_few_comparative, lat_few_superlative, grc_few_positive,
  grc_few_comparative, grc_few_superlative, grc_few_comparative_2, grc_few_superlative_2,
  krl_many_onego_positive, krl_many_onego_comparative, krl_many_onego_superlative]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := [krl_many_superlative_questionnaire]

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

/-- Every root-class judgment of the data. -/
def rootClasses : List (RootClasses Cell) := [eng_good.roots, swe_good.roots, got_good.roots,
  cim_good.roots, ces_good.roots, hbs_good.roots, sorb_good.roots, ukr_good_dobr.roots,
  ukr_good_harn.roots, rus_good.roots, lat_good.roots, cym_good.roots, sga_good.roots,
  bre_good.roots, grc_good_amein.roots, grc_good_arei.roots, grc_good_belt.roots,
  grc_good_kreiss.roots, grc_good_lo.roots, san_good_sre.roots, san_good_jya.roots, kho_good.roots,
  pal_good.roots, fas_good.roots, eus_good_hobe.roots, eus_good_on.roots, fin_good.roots,
  sjd_good.roots, kat_good_mjob.roots, kat_good_ket.roots, sva_good.roots, chr_good.roots,
  eng_bad.roots, goh_bad.roots, non_bad_vandr.roots, non_bad_illr.roots, dan_bad.roots,
  fao_bad.roots, swe_bad_var.roots, swe_bad_sam.roots, yid_bad.roots, pol_bad.roots, ces_bad.roots,
  ukr_bad.roots, bel_bad_drenn.roots, bel_bad_blah.roots, hbs_bad.roots, rus_bad.roots,
  lat_bad.roots, sga_bad.roots, cym_bad.roots, bre_bad.roots, grc_bad_cheir.roots,
  grc_bad_hess.roots, got_big.roots, ces_big.roots, ukr_big.roots, pol_big.roots, cym_big.roots,
  pal_big.roots, sva_big.roots, got_small.roots, ang_small.roots, dan_small.roots, hbs_small.roots,
  lat_small.roots, cym_small.roots, grc_small_mei.roots, grc_small_elass.roots, pal_small.roots,
  non_old.roots, cym_near.roots, cym_strong.roots, eng_many.roots, eng_much.roots, eng_lot.roots,
  deu_many.roots, fao_many.roots, afr_many_party.roots, afr_many_baie.roots, yid_many.roots,
  dan_many.roots, ces_many.roots, rus_many.roots, bul_many.roots, pol_many.roots, hbs_many.roots,
  ukr_many_bahato.roots, ukr_many_duze.roots, lav_many.roots, lat_many.roots, bre_many.roots,
  cym_many.roots, grc_many.roots, hye_many.roots, fas_many_xele.roots, fas_many_ziad.roots,
  eus_many.roots, fin_many_monet.roots, fin_many_paljon.roots, krl_many.roots, hun_many.roots,
  kat_many.roots, kbd_many.roots, eng_few.roots, afr_few.roots, fry_few.roots, ukr_few.roots,
  lat_few.roots, grc_few_hess.roots, grc_few_mei.roots, krl_many_onego.roots]

end Bobaljik2012.Wordlist
