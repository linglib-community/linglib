module

public import Linglib.Data.Wordlist.Schema

/-!
# `Arad2005`: word forms

Auto-generated from `Linglib/Data/Wordlist/Arad2005.json` by `scripts/gen_wordlist.py`. Do not edit
by hand; edit the JSON and re-run the generator. Declarations live in `namespace Arad2005.Wordlist`.
-/

@[expose] public section

namespace Arad2005.Wordlist

open Data.Wordlist

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.learn : Lexeme :=
  { id := "learn", languageId := "hebr1245", parameterId := "learn", pos := ↑UD.UPOS.VERB }

def Lexemes.learn_passive : Lexeme :=
  { id := "learn_passive", languageId := "hebr1245", parameterId := "learn_passive",
    pos := ↑UD.UPOS.VERB }

def Lexemes.tell : Lexeme :=
  { id := "tell", languageId := "hebr1245", parameterId := "tell", pos := ↑UD.UPOS.VERB }

def Lexemes.tell_passive : Lexeme :=
  { id := "tell_passive", languageId := "hebr1245", parameterId := "tell_passive",
    pos := ↑UD.UPOS.VERB }

def Lexemes.record : Lexeme :=
  { id := "record", languageId := "hebr1245", parameterId := "record", pos := ↑UD.UPOS.VERB }

def Lexemes.record_passive : Lexeme :=
  { id := "record_passive", languageId := "hebr1245", parameterId := "record_passive",
    pos := ↑UD.UPOS.VERB }

def Lexemes.pray : Lexeme :=
  { id := "pray", languageId := "hebr1245", parameterId := "pray", pos := ↑UD.UPOS.VERB }

def Lexemes.shatter : Lexeme :=
  { id := "shatter", languageId := "hebr1245", parameterId := "shatter", pos := ↑UD.UPOS.VERB }

def Lexemes.shatter_passive : Lexeme :=
  { id := "shatter_passive", languageId := "hebr1245", parameterId := "shatter_passive",
    pos := ↑UD.UPOS.VERB }

def Lexemes.divide : Lexeme :=
  { id := "divide", languageId := "hebr1245", parameterId := "divide", pos := ↑UD.UPOS.VERB }

def Lexemes.divide_passive : Lexeme :=
  { id := "divide_passive", languageId := "hebr1245", parameterId := "divide_passive",
    pos := ↑UD.UPOS.VERB }

def Lexemes.hide : Lexeme :=
  { id := "hide", languageId := "hebr1245", parameterId := "hide", pos := ↑UD.UPOS.VERB }

def Lexemes.hide_passive : Lexeme :=
  { id := "hide_passive", languageId := "hebr1245", parameterId := "hide_passive",
    pos := ↑UD.UPOS.VERB }

def Lexemes.deposit : Lexeme :=
  { id := "deposit", languageId := "hebr1245", parameterId := "deposit", pos := ↑UD.UPOS.VERB }

def Lexemes.deposit_passive : Lexeme :=
  { id := "deposit_passive", languageId := "hebr1245", parameterId := "deposit_passive",
    pos := ↑UD.UPOS.VERB }

def Lexemes.guard : Lexeme :=
  { id := "guard", languageId := "hebr1245", parameterId := "guard", pos := ↑UD.UPOS.VERB }

def Lexemes.translate : Lexeme :=
  { id := "translate", languageId := "hebr1245", parameterId := "translate", pos := ↑UD.UPOS.VERB }

def Lexemes.receive : Lexeme :=
  { id := "receive", languageId := "hebr1245", parameterId := "receive", pos := ↑UD.UPOS.VERB }

def Lexemes.become_soft : Lexeme :=
  { id := "become_soft", languageId := "hebr1245", parameterId := "become_soft",
    pos := ↑UD.UPOS.VERB }

def Lexemes.oil_grease : Lexeme :=
  { id := "oil_grease", languageId := "hebr1245", parameterId := "oil_grease",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.cream : Lexeme :=
  { id := "cream", languageId := "hebr1245", parameterId := "cream", pos := ↑UD.UPOS.NOUN }

def Lexemes.fat : Lexeme :=
  { id := "fat", languageId := "hebr1245", parameterId := "fat", pos := ↑UD.UPOS.NOUN }

def Lexemes.fat_adj : Lexeme :=
  { id := "fat_adj", languageId := "hebr1245", parameterId := "fat_adj", pos := ↑UD.UPOS.ADJ }

def Lexemes.grow_fat_fatten : Lexeme :=
  { id := "grow_fat_fatten", languageId := "hebr1245", parameterId := "grow_fat_fatten",
    pos := ↑UD.UPOS.VERB }

def Lexemes.grease : Lexeme :=
  { id := "grease", languageId := "hebr1245", parameterId := "grease", pos := ↑UD.UPOS.VERB }

def Lexemes.to_think : Lexeme :=
  { id := "to_think", languageId := "hebr1245", parameterId := "to_think", pos := ↑UD.UPOS.VERB }

def Lexemes.to_calculate : Lexeme :=
  { id := "to_calculate", languageId := "hebr1245", parameterId := "to_calculate",
    pos := ↑UD.UPOS.VERB }

def Lexemes.to_consider : Lexeme :=
  { id := "to_consider", languageId := "hebr1245", parameterId := "to_consider",
    pos := ↑UD.UPOS.VERB }

def Lexemes.to_be_considerate : Lexeme :=
  { id := "to_be_considerate", languageId := "hebr1245", parameterId := "to_be_considerate",
    pos := ↑UD.UPOS.VERB }

def Lexemes.computer : Lexeme :=
  { id := "computer", languageId := "hebr1245", parameterId := "computer", pos := ↑UD.UPOS.NOUN }

def Lexemes.a_thought : Lexeme :=
  { id := "a_thought", languageId := "hebr1245", parameterId := "a_thought", pos := ↑UD.UPOS.NOUN }

def Lexemes.importance : Lexeme :=
  { id := "importance", languageId := "hebr1245", parameterId := "importance",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.arithmetic_bill : Lexeme :=
  { id := "arithmetic_bill", languageId := "hebr1245", parameterId := "arithmetic_bill",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.calculus : Lexeme :=
  { id := "calculus", languageId := "hebr1245", parameterId := "calculus", pos := ↑UD.UPOS.NOUN }

def Lexemes.to_absorb_receive : Lexeme :=
  { id := "to_absorb_receive", languageId := "hebr1245", parameterId := "to_absorb_receive",
    pos := ↑UD.UPOS.VERB }

def Lexemes.a_shelter : Lexeme :=
  { id := "a_shelter", languageId := "hebr1245", parameterId := "a_shelter", pos := ↑UD.UPOS.NOUN }

def Lexemes.a_receiver : Lexeme :=
  { id := "a_receiver", languageId := "hebr1245", parameterId := "a_receiver",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.a_record : Lexeme :=
  { id := "a_record", languageId := "hebr1245", parameterId := "a_record", pos := ↑UD.UPOS.NOUN }

def Lexemes.a_cassette : Lexeme :=
  { id := "a_cassette", languageId := "hebr1245", parameterId := "a_cassette",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.input : Lexeme :=
  { id := "input", languageId := "hebr1245", parameterId := "input", pos := ↑UD.UPOS.NOUN }

def Lexemes.close : Lexeme :=
  { id := "close", languageId := "hebr1245", parameterId := "close", pos := ↑UD.UPOS.VERB }

def Lexemes.extradite : Lexeme :=
  { id := "extradite", languageId := "hebr1245", parameterId := "extradite", pos := ↑UD.UPOS.VERB }

def Lexemes.cocoon_oneself : Lexeme :=
  { id := "cocoon_oneself", languageId := "hebr1245", parameterId := "cocoon_oneself",
    pos := ↑UD.UPOS.VERB }

def Lexemes.closure : Lexeme :=
  { id := "closure", languageId := "hebr1245", parameterId := "closure", pos := ↑UD.UPOS.NOUN }

def Lexemes.parentheses : Lexeme :=
  { id := "parentheses", languageId := "hebr1245", parameterId := "parentheses",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.frame : Lexeme :=
  { id := "frame", languageId := "hebr1245", parameterId := "frame", pos := ↑UD.UPOS.NOUN }

def Lexemes.open_causative : Lexeme :=
  { id := "open_causative", languageId := "hebr1245", parameterId := "open_causative",
    pos := ↑UD.UPOS.VERB }

def Lexemes.open_inchoative : Lexeme :=
  { id := "open_inchoative", languageId := "hebr1245", parameterId := "open_inchoative",
    pos := ↑UD.UPOS.VERB }

def Lexemes.freeze_inchoative : Lexeme :=
  { id := "freeze_inchoative", languageId := "hebr1245", parameterId := "freeze_inchoative",
    pos := ↑UD.UPOS.VERB }

def Lexemes.freeze_causative : Lexeme :=
  { id := "freeze_causative", languageId := "hebr1245", parameterId := "freeze_causative",
    pos := ↑UD.UPOS.VERB }

def Lexemes.melt_inchoative : Lexeme :=
  { id := "melt_inchoative", languageId := "hebr1245", parameterId := "melt_inchoative",
    pos := ↑UD.UPOS.VERB }

def Lexemes.melt_causative : Lexeme :=
  { id := "melt_causative", languageId := "hebr1245", parameterId := "melt_causative",
    pos := ↑UD.UPOS.VERB }

def Lexemes.heat_inchoative : Lexeme :=
  { id := "heat_inchoative", languageId := "hebr1245", parameterId := "heat_inchoative",
    pos := ↑UD.UPOS.VERB }

def Lexemes.heat_causative : Lexeme :=
  { id := "heat_causative", languageId := "hebr1245", parameterId := "heat_causative",
    pos := ↑UD.UPOS.VERB }

def Lexemes.become_clear : Lexeme :=
  { id := "become_clear", languageId := "hebr1245", parameterId := "become_clear",
    pos := ↑UD.UPOS.VERB }

def Lexemes.make_clear : Lexeme :=
  { id := "make_clear", languageId := "hebr1245", parameterId := "make_clear",
    pos := ↑UD.UPOS.VERB }

def Lexemes.be_red : Lexeme :=
  { id := "be_red", languageId := "hebr1245", parameterId := "be_red", pos := ↑UD.UPOS.VERB }

def Lexemes.redden : Lexeme :=
  { id := "redden", languageId := "hebr1245", parameterId := "redden", pos := ↑UD.UPOS.VERB }

def Lexemes.budget : Lexeme :=
  { id := "budget", languageId := "hebr1245", parameterId := "budget", pos := ↑UD.UPOS.NOUN }

def Lexemes.to_budget : Lexeme :=
  { id := "to_budget", languageId := "hebr1245", parameterId := "to_budget", pos := ↑UD.UPOS.VERB }

def Lexemes.telephone : Lexeme :=
  { id := "telephone", languageId := "hebr1245", parameterId := "telephone", pos := ↑UD.UPOS.NOUN }

def Lexemes.to_telephone : Lexeme :=
  { id := "to_telephone", languageId := "hebr1245", parameterId := "to_telephone",
    pos := ↑UD.UPOS.VERB }

def Lexemes.drunk : Lexeme :=
  { id := "drunk", languageId := "hebr1245", parameterId := "drunk", pos := ↑UD.UPOS.ADJ }

def Lexemes.to_get_drunk : Lexeme :=
  { id := "to_get_drunk", languageId := "hebr1245", parameterId := "to_get_drunk",
    pos := ↑UD.UPOS.VERB }

def Lexemes.a_snooze : Lexeme :=
  { id := "a_snooze", languageId := "hebr1245", parameterId := "a_snooze", pos := ↑UD.UPOS.NOUN }

def Lexemes.to_snooze : Lexeme :=
  { id := "to_snooze", languageId := "hebr1245", parameterId := "to_snooze", pos := ↑UD.UPOS.VERB }

def Lexemes.to_computerize : Lexeme :=
  { id := "to_computerize", languageId := "hebr1245", parameterId := "to_computerize",
    pos := ↑UD.UPOS.VERB }

def Lexemes.maintenance : Lexeme :=
  { id := "maintenance", languageId := "hebr1245", parameterId := "maintenance",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.to_maintain : Lexeme :=
  { id := "to_maintain", languageId := "hebr1245", parameterId := "to_maintain",
    pos := ↑UD.UPOS.VERB }

def Lexemes.to_frame : Lexeme :=
  { id := "to_frame", languageId := "hebr1245", parameterId := "to_frame", pos := ↑UD.UPOS.VERB }

def Lexemes.was_framed : Lexeme :=
  { id := "was_framed", languageId := "hebr1245", parameterId := "was_framed",
    pos := ↑UD.UPOS.VERB }

def Lexemes.censorship : Lexeme :=
  { id := "censorship", languageId := "hebr1245", parameterId := "censorship",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.to_censor : Lexeme :=
  { id := "to_censor", languageId := "hebr1245", parameterId := "to_censor", pos := ↑UD.UPOS.VERB }

def Lexemes.line : Lexeme :=
  { id := "line", languageId := "hebr1245", parameterId := "line", pos := ↑UD.UPOS.NOUN }

def Lexemes.to_draw_a_dotted_line : Lexeme :=
  { id := "to_draw_a_dotted_line", languageId := "hebr1245", parameterId := "to_draw_a_dotted_line",
    pos := ↑UD.UPOS.VERB }

def Lexemes.debt : Lexeme :=
  { id := "debt", languageId := "hebr1245", parameterId := "debt", pos := ↑UD.UPOS.NOUN }

def Lexemes.to_debit_oblige : Lexeme :=
  { id := "to_debit_oblige", languageId := "hebr1245", parameterId := "to_debit_oblige",
    pos := ↑UD.UPOS.VERB }

def Lexemes.fax : Lexeme :=
  { id := "fax", languageId := "hebr1245", parameterId := "fax", pos := ↑UD.UPOS.NOUN }

def Lexemes.to_fax : Lexeme :=
  { id := "to_fax", languageId := "hebr1245", parameterId := "to_fax", pos := ↑UD.UPOS.VERB }

def Lexemes.transfer : Lexeme :=
  { id := "transfer", languageId := "hebr1245", parameterId := "transfer", pos := ↑UD.UPOS.NOUN }

def Lexemes.to_transfer : Lexeme :=
  { id := "to_transfer", languageId := "hebr1245", parameterId := "to_transfer",
    pos := ↑UD.UPOS.VERB }

def Lexemes.striptease : Lexeme :=
  { id := "striptease", languageId := "hebr1245", parameterId := "striptease",
    pos := ↑UD.UPOS.NOUN }

def Lexemes.to_perform_a_striptease : Lexeme :=
  { id := "to_perform_a_striptease", languageId := "hebr1245",
    parameterId := "to_perform_a_striptease", pos := ↑UD.UPOS.VERB }

def Lexemes.synchronic : Lexeme :=
  { id := "synchronic", languageId := "hebr1245", parameterId := "synchronic", pos := ↑UD.UPOS.ADJ }

def Lexemes.synchronize : Lexeme :=
  { id := "synchronize", languageId := "hebr1245", parameterId := "synchronize",
    pos := ↑UD.UPOS.VERB }

def Lexemes.a_click : Lexeme :=
  { id := "a_click", languageId := "hebr1245", parameterId := "a_click", pos := ↑UD.UPOS.NOUN }

def Lexemes.to_click : Lexeme :=
  { id := "to_click", languageId := "hebr1245", parameterId := "to_click", pos := ↑UD.UPOS.VERB }

def Lexemes.a_slap : Lexeme :=
  { id := "a_slap", languageId := "hebr1245", parameterId := "a_slap", pos := ↑UD.UPOS.NOUN }

def Lexemes.to_slap : Lexeme :=
  { id := "to_slap", languageId := "hebr1245", parameterId := "to_slap", pos := ↑UD.UPOS.VERB }

def Lexemes.a_splash : Lexeme :=
  { id := "a_splash", languageId := "hebr1245", parameterId := "a_splash", pos := ↑UD.UPOS.NOUN }

def Lexemes.to_splash : Lexeme :=
  { id := "to_splash", languageId := "hebr1245", parameterId := "to_splash", pos := ↑UD.UPOS.VERB }

def Lexemes.law : Lexeme :=
  { id := "law", languageId := "hebr1245", parameterId := "law", pos := ↑UD.UPOS.NOUN }

def Lexemes.legislate : Lexeme :=
  { id := "legislate", languageId := "hebr1245", parameterId := "legislate", pos := ↑UD.UPOS.VERB }

def Lexemes.code : Lexeme :=
  { id := "code", languageId := "hebr1245", parameterId := "code", pos := ↑UD.UPOS.NOUN }

def Lexemes.codify : Lexeme :=
  { id := "codify", languageId := "hebr1245", parameterId := "codify", pos := ↑UD.UPOS.VERB }

def Lexemes.blood : Lexeme :=
  { id := "blood", languageId := "hebr1245", parameterId := "blood", pos := ↑UD.UPOS.NOUN }

def Lexemes.bleed : Lexeme :=
  { id := "bleed", languageId := "hebr1245", parameterId := "bleed", pos := ↑UD.UPOS.VERB }

def Lexemes.chat : Lexeme :=
  { id := "chat", languageId := "hebr1245", parameterId := "chat", pos := ↑UD.UPOS.NOUN }

def Lexemes.to_chat : Lexeme :=
  { id := "to_chat", languageId := "hebr1245", parameterId := "to_chat", pos := ↑UD.UPOS.VERB }

def lamad : Form Cell :=
  { id := "arad2005_lamad"
    lexeme := Lexemes.learn
    cell := {}
    form := "lamad"
    segments := ["l", "a", "m", "a", "d"]
    source := [
      ⟨"arad-2005", "Ch. 2 (3)"⟩
    ] }

def nilmad : Form Cell :=
  { id := "arad2005_nilmad"
    lexeme := Lexemes.learn_passive
    cell := {}
    form := "nilmad"
    segments := ["n", "i", "l", "m", "a", "d"]
    source := [
      ⟨"arad-2005", "Ch. 2 (3)"⟩
    ] }

def siper : Form Cell :=
  { id := "arad2005_siper"
    lexeme := Lexemes.tell
    cell := {}
    form := "siper"
    segments := ["s", "i", "p", "e", "r"]
    source := [
      ⟨"arad-2005", "Ch. 2 (3)"⟩
    ] }

def supar : Form Cell :=
  { id := "arad2005_supar"
    lexeme := Lexemes.tell_passive
    cell := {}
    form := "supar"
    segments := ["s", "u", "p", "a", "r"]
    source := [
      ⟨"arad-2005", "Ch. 2 (3)"⟩
    ] }

def hiqlit : Form Cell :=
  { id := "arad2005_hiqlit"
    lexeme := Lexemes.record
    cell := {}
    form := "hiqlit"
    segments := ["h", "i", "q", "l", "i", "t"]
    source := [
      ⟨"arad-2005", "Ch. 2 (3)"⟩,
      ⟨"arad-2005", "Ch. 7 (4b)"⟩
    ] }

def huqlat : Form Cell :=
  { id := "arad2005_huqlat"
    lexeme := Lexemes.record_passive
    cell := {}
    form := "huqlat"
    segments := ["h", "u", "q", "l", "a", "t"]
    source := [
      ⟨"arad-2005", "Ch. 2 (3)"⟩
    ] }

def hitpalel : Form Cell :=
  { id := "arad2005_hitpalel"
    lexeme := Lexemes.pray
    cell := {}
    form := "hitpalel"
    segments := ["h", "i", "t", "p", "a", "l", "e", "l"]
    source := [
      ⟨"arad-2005", "Ch. 2 (3)"⟩
    ] }

def nipec : Form Cell :=
  { id := "arad2005_nipec"
    lexeme := Lexemes.shatter
    cell := {}
    form := "nipec"
    segments := ["n", "i", "p", "e", "c"]
    source := [
      ⟨"arad-2005", "Ch. 2 (6a)"⟩
    ] }

def nupac : Form Cell :=
  { id := "arad2005_nupac"
    lexeme := Lexemes.shatter_passive
    cell := {}
    form := "nupac"
    segments := ["n", "u", "p", "a", "c"]
    source := [
      ⟨"arad-2005", "Ch. 2 (6a)"⟩
    ] }

def xileq : Form Cell :=
  { id := "arad2005_xileq"
    lexeme := Lexemes.divide
    cell := {}
    form := "xileq"
    segments := ["x", "i", "l", "e", "q"]
    source := [
      ⟨"arad-2005", "Ch. 2 (6b)"⟩
    ] }

def xulaq : Form Cell :=
  { id := "arad2005_xulaq"
    lexeme := Lexemes.divide_passive
    cell := {}
    form := "xulaq"
    segments := ["x", "u", "l", "a", "q"]
    source := [
      ⟨"arad-2005", "Ch. 2 (6b)"⟩
    ] }

def histir : Form Cell :=
  { id := "arad2005_histir"
    lexeme := Lexemes.hide
    cell := {}
    form := "histir"
    segments := ["h", "i", "s", "t", "i", "r"]
    source := [
      ⟨"arad-2005", "Ch. 2 (6c)"⟩
    ] }

def hustar : Form Cell :=
  { id := "arad2005_hustar"
    lexeme := Lexemes.hide_passive
    cell := {}
    form := "hustar"
    segments := ["h", "u", "s", "t", "a", "r"]
    source := [
      ⟨"arad-2005", "Ch. 2 (6c)"⟩
    ] }

def hifqid : Form Cell :=
  { id := "arad2005_hifqid"
    lexeme := Lexemes.deposit
    cell := {}
    form := "hifqid"
    segments := ["h", "i", "f", "q", "i", "d"]
    source := [
      ⟨"arad-2005", "Ch. 2 (6d)"⟩
    ] }

def hufqad : Form Cell :=
  { id := "arad2005_hufqad"
    lexeme := Lexemes.deposit_passive
    cell := {}
    form := "hufqad"
    segments := ["h", "u", "f", "q", "a", "d"]
    source := [
      ⟨"arad-2005", "Ch. 2 (6d)"⟩
    ] }

def shamar : Form Cell :=
  { id := "arad2005_shamar"
    lexeme := Lexemes.guard
    cell := {}
    form := "šamar"
    segments := ["š", "a", "m", "a", "r"]
    source := [
      ⟨"arad-2005", "Ch. 2 (27)"⟩
    ] }

def tirgem : Form Cell :=
  { id := "arad2005_tirgem"
    lexeme := Lexemes.translate
    cell := {}
    form := "tirgem"
    segments := ["t", "i", "r", "g", "e", "m"]
    source := [
      ⟨"arad-2005", "p. 28"⟩
    ] }

def qibel : Form Cell :=
  { id := "arad2005_qibel"
    lexeme := Lexemes.receive
    cell := {}
    form := "qibel"
    segments := ["q", "i", "b", "e", "l"]
    source := [
      ⟨"arad-2005", "p. 29"⟩
    ] }

def hitrakex : Form Cell :=
  { id := "arad2005_hitrakex"
    lexeme := Lexemes.become_soft
    cell := {}
    form := "hitrakex"
    segments := ["h", "i", "t", "r", "a", "k", "e", "x"]
    source := [
      ⟨"arad-2005", "p. 29"⟩
    ] }

def shemen : Form Cell :=
  { id := "arad2005_shemen"
    lexeme := Lexemes.oil_grease
    cell := {}
    form := "šemen"
    segments := ["š", "e", "m", "e", "n"]
    source := [
      ⟨"arad-2005", "Ch. 7 (2a)"⟩
    ] }

def shamenet : Form Cell :=
  { id := "arad2005_shamenet"
    lexeme := Lexemes.cream
    cell := {}
    form := "šamenet"
    segments := ["š", "a", "m", "e", "n", "e", "t"]
    source := [
      ⟨"arad-2005", "Ch. 7 (2b)"⟩
    ] }

def shuman : Form Cell :=
  { id := "arad2005_shuman"
    lexeme := Lexemes.fat
    cell := {}
    form := "šuman"
    segments := ["š", "u", "m", "a", "n"]
    source := [
      ⟨"arad-2005", "Ch. 7 (2c)"⟩
    ] }

def shamen : Form Cell :=
  { id := "arad2005_shamen"
    lexeme := Lexemes.fat_adj
    cell := {}
    form := "šamen"
    segments := ["š", "a", "m", "e", "n"]
    source := [
      ⟨"arad-2005", "Ch. 7 (2d)"⟩
    ] }

def hishmin : Form Cell :=
  { id := "arad2005_hishmin"
    lexeme := Lexemes.grow_fat_fatten
    cell := {}
    form := "hišmin"
    segments := ["h", "i", "š", "m", "i", "n"]
    source := [
      ⟨"arad-2005", "Ch. 7 (2e)"⟩
    ] }

def shimen : Form Cell :=
  { id := "arad2005_shimen"
    lexeme := Lexemes.grease
    cell := {}
    form := "šimen"
    segments := ["š", "i", "m", "e", "n"]
    source := [
      ⟨"arad-2005", "Ch. 7 (2f)"⟩
    ] }

def xashav : Form Cell :=
  { id := "arad2005_xashav"
    lexeme := Lexemes.to_think
    cell := {}
    form := "xašav"
    segments := ["x", "a", "š", "a", "v"]
    source := [
      ⟨"arad-2005", "Ch. 7 (3a)"⟩
    ] }

def xishev : Form Cell :=
  { id := "arad2005_xishev"
    lexeme := Lexemes.to_calculate
    cell := {}
    form := "xišev"
    segments := ["x", "i", "š", "e", "v"]
    source := [
      ⟨"arad-2005", "Ch. 7 (3b)"⟩
    ] }

def hexshiv : Form Cell :=
  { id := "arad2005_hexshiv"
    lexeme := Lexemes.to_consider
    cell := {}
    form := "hexšiv"
    segments := ["h", "e", "x", "š", "i", "v"]
    source := [
      ⟨"arad-2005", "Ch. 7 (3c)"⟩
    ] }

def hitxashev : Form Cell :=
  { id := "arad2005_hitxashev"
    lexeme := Lexemes.to_be_considerate
    cell := {}
    form := "hitxašev"
    segments := ["h", "i", "t", "x", "a", "š", "e", "v"]
    source := [
      ⟨"arad-2005", "Ch. 7 (3d)"⟩
    ] }

def maxshev : Form Cell :=
  { id := "arad2005_maxshev"
    lexeme := Lexemes.computer
    cell := {}
    form := "maxšev"
    segments := ["m", "a", "x", "š", "e", "v"]
    source := [
      ⟨"arad-2005", "Ch. 2 (29d)"⟩,
      ⟨"arad-2005", "Ch. 7 (3e)"⟩
    ] }

def maxshava : Form Cell :=
  { id := "arad2005_maxshava"
    lexeme := Lexemes.a_thought
    cell := {}
    form := "maxšava"
    segments := ["m", "a", "x", "š", "a", "v", "a"]
    source := [
      ⟨"arad-2005", "Ch. 7 (3f)"⟩
    ] }

def xashivut : Form Cell :=
  { id := "arad2005_xashivut"
    lexeme := Lexemes.importance
    cell := {}
    form := "xašivut"
    segments := ["x", "a", "š", "i", "v", "u", "t"]
    source := [
      ⟨"arad-2005", "Ch. 7 (3g)"⟩
    ] }

def xeshbon : Form Cell :=
  { id := "arad2005_xeshbon"
    lexeme := Lexemes.arithmetic_bill
    cell := {}
    form := "xešbon"
    segments := ["x", "e", "š", "b", "o", "n"]
    source := [
      ⟨"arad-2005", "Ch. 7 (3h)"⟩
    ] }

def taxshiv : Form Cell :=
  { id := "arad2005_taxshiv"
    lexeme := Lexemes.calculus
    cell := {}
    form := "taxšiv"
    segments := ["t", "a", "x", "š", "i", "v"]
    source := [
      ⟨"arad-2005", "Ch. 7 (3i)"⟩
    ] }

def qalat : Form Cell :=
  { id := "arad2005_qalat"
    lexeme := Lexemes.to_absorb_receive
    cell := {}
    form := "qalat"
    segments := ["q", "a", "l", "a", "t"]
    source := [
      ⟨"arad-2005", "Ch. 7 (4a)"⟩
    ] }

def miqlat : Form Cell :=
  { id := "arad2005_miqlat"
    lexeme := Lexemes.a_shelter
    cell := {}
    form := "miqlat"
    segments := ["m", "i", "q", "l", "a", "t"]
    source := [
      ⟨"arad-2005", "Ch. 7 (4c)"⟩
    ] }

def maqlet : Form Cell :=
  { id := "arad2005_maqlet"
    lexeme := Lexemes.a_receiver
    cell := {}
    form := "maqlet"
    segments := ["m", "a", "q", "l", "e", "t"]
    source := [
      ⟨"arad-2005", "Ch. 7 (4d)"⟩
    ] }

def taqlit : Form Cell :=
  { id := "arad2005_taqlit"
    lexeme := Lexemes.a_record
    cell := {}
    form := "taqlit"
    segments := ["t", "a", "q", "l", "i", "t"]
    source := [
      ⟨"arad-2005", "Ch. 7 (4e)"⟩
    ] }

def qaletet : Form Cell :=
  { id := "arad2005_qaletet"
    lexeme := Lexemes.a_cassette
    cell := {}
    form := "qaletet"
    segments := ["q", "a", "l", "e", "t", "e", "t"]
    source := [
      ⟨"arad-2005", "Ch. 7 (4f)"⟩
    ] }

def qelet : Form Cell :=
  { id := "arad2005_qelet"
    lexeme := Lexemes.input
    cell := {}
    form := "qelet"
    segments := ["q", "e", "l", "e", "t"]
    source := [
      ⟨"arad-2005", "Ch. 7 (4g)"⟩
    ] }

def sagar : Form Cell :=
  { id := "arad2005_sagar"
    lexeme := Lexemes.close
    cell := {}
    form := "sagar"
    segments := ["s", "a", "g", "a", "r"]
    source := [
      ⟨"arad-2005", "Ch. 7 (5a)"⟩
    ] }

def hisgir : Form Cell :=
  { id := "arad2005_hisgir"
    lexeme := Lexemes.extradite
    cell := {}
    form := "hisgir"
    segments := ["h", "i", "s", "g", "i", "r"]
    source := [
      ⟨"arad-2005", "Ch. 7 (5b)"⟩
    ] }

def histager : Form Cell :=
  { id := "arad2005_histager"
    lexeme := Lexemes.cocoon_oneself
    cell := {}
    form := "histager"
    segments := ["h", "i", "s", "t", "a", "g", "e", "r"]
    source := [
      ⟨"arad-2005", "Ch. 7 (5c)"⟩
    ] }

def seger : Form Cell :=
  { id := "arad2005_seger"
    lexeme := Lexemes.closure
    cell := {}
    form := "seger"
    segments := ["s", "e", "g", "e", "r"]
    source := [
      ⟨"arad-2005", "Ch. 7 (5d)"⟩
    ] }

def sograyim : Form Cell :=
  { id := "arad2005_sograyim"
    lexeme := Lexemes.parentheses
    cell := {}
    form := "sograyim"
    segments := ["s", "o", "g", "r", "a", "y", "i", "m"]
    source := [
      ⟨"arad-2005", "Ch. 7 (5e)"⟩
    ] }

def misgeret : Form Cell :=
  { id := "arad2005_misgeret"
    lexeme := Lexemes.frame
    cell := {}
    form := "misgeret"
    segments := ["m", "i", "s", "g", "e", "r", "+", "e", "t"]
    source := [
      ⟨"arad-2005", "Ch. 2 (32b)"⟩,
      ⟨"arad-2005", "Ch. 7 (5f)"⟩,
      ⟨"arad-2005", "Ch. 7 (6a)"⟩
    ] }

def patax : Form Cell :=
  { id := "arad2005_patax"
    lexeme := Lexemes.open_causative
    cell := {}
    form := "patax"
    segments := ["p", "a", "t", "a", "x"]
    source := [
      ⟨"arad-2005", "Ch. 6 (47)"⟩
    ] }

def niftax : Form Cell :=
  { id := "arad2005_niftax"
    lexeme := Lexemes.open_inchoative
    cell := {}
    form := "niftax"
    segments := ["n", "i", "f", "t", "a", "x"]
    source := [
      ⟨"arad-2005", "Ch. 6 (47)"⟩
    ] }

def qafa : Form Cell :=
  { id := "arad2005_qafa"
    lexeme := Lexemes.freeze_inchoative
    cell := {}
    form := "qafaʔ"
    segments := ["q", "a", "f", "a", "ʔ"]
    source := [
      ⟨"arad-2005", "Ch. 6 (48)"⟩
    ] }

def hiqpi : Form Cell :=
  { id := "arad2005_hiqpi"
    lexeme := Lexemes.freeze_causative
    cell := {}
    form := "hiqpiʔ"
    segments := ["h", "i", "q", "p", "i", "ʔ"]
    source := [
      ⟨"arad-2005", "Ch. 6 (48)"⟩
    ] }

def namas : Form Cell :=
  { id := "arad2005_namas"
    lexeme := Lexemes.melt_inchoative
    cell := {}
    form := "namas"
    segments := ["n", "a", "m", "a", "s"]
    source := [
      ⟨"arad-2005", "Ch. 6 (49)"⟩
    ] }

def hemes : Form Cell :=
  { id := "arad2005_hemes"
    lexeme := Lexemes.melt_causative
    cell := {}
    form := "hemes"
    segments := ["h", "e", "m", "e", "s"]
    source := [
      ⟨"arad-2005", "Ch. 6 (49)"⟩
    ] }

def hitxamem : Form Cell :=
  { id := "arad2005_hitxamem"
    lexeme := Lexemes.heat_inchoative
    cell := {}
    form := "hitxamem"
    segments := ["h", "i", "t", "x", "a", "m", "e", "m"]
    source := [
      ⟨"arad-2005", "Ch. 6 (50)"⟩
    ] }

def ximem : Form Cell :=
  { id := "arad2005_ximem"
    lexeme := Lexemes.heat_causative
    cell := {}
    form := "ximem"
    segments := ["x", "i", "m", "e", "m"]
    source := [
      ⟨"arad-2005", "Ch. 6 (50)"⟩
    ] }

def hitbaher : Form Cell :=
  { id := "arad2005_hitbaher"
    lexeme := Lexemes.become_clear
    cell := {}
    form := "hitbaher"
    segments := ["h", "i", "t", "b", "a", "h", "e", "r"]
    source := [
      ⟨"arad-2005", "Ch. 6 (51)"⟩
    ] }

def hivhir : Form Cell :=
  { id := "arad2005_hivhir"
    lexeme := Lexemes.make_clear
    cell := {}
    form := "hivhir"
    segments := ["h", "i", "v", "h", "i", "r"]
    source := [
      ⟨"arad-2005", "Ch. 6 (51)"⟩
    ] }

def heedim_inchoative : Form Cell :=
  { id := "arad2005_heedim_inchoative"
    lexeme := Lexemes.be_red
    cell := {}
    form := "heʔedim"
    segments := ["h", "e", "ʔ", "e", "d", "i", "m"]
    source := [
      ⟨"arad-2005", "Ch. 6 (52)"⟩
    ] }

def heedim_causative : Form Cell :=
  { id := "arad2005_heedim_causative"
    lexeme := Lexemes.redden
    cell := {}
    form := "heʔedim"
    segments := ["h", "e", "ʔ", "e", "d", "i", "m"]
    source := [
      ⟨"arad-2005", "Ch. 6 (52)"⟩
    ] }

def taqciv : Form Cell :=
  { id := "arad2005_taqciv"
    lexeme := Lexemes.budget
    cell := {}
    form := "taqciv"
    segments := ["t", "a", "q", "c", "i", "v"]
    source := [
      ⟨"arad-2005", "Ch. 1 (12a)"⟩
    ] }

def tiqcev : Form Cell :=
  { id := "arad2005_tiqcev"
    lexeme := Lexemes.to_budget
    cell := {}
    form := "tiqcev"
    segments := ["t", "i", "q", "c", "e", "v"]
    source := [
      ⟨"arad-2005", "Ch. 1 (12a)"⟩
    ] }

def telefon : Form Cell :=
  { id := "arad2005_telefon"
    lexeme := Lexemes.telephone
    cell := {}
    form := "telefon"
    segments := ["t", "e", "l", "e", "f", "o", "n"]
    source := [
      ⟨"arad-2005", "Ch. 2 (29a)"⟩
    ] }

def tilfen : Form Cell :=
  { id := "arad2005_tilfen"
    lexeme := Lexemes.to_telephone
    cell := {}
    form := "tilfen"
    segments := ["t", "i", "l", "f", "e", "n"]
    source := [
      ⟨"arad-2005", "Ch. 2 (29a)"⟩
    ] }

def mastul : Form Cell :=
  { id := "arad2005_mastul"
    lexeme := Lexemes.drunk
    cell := {}
    form := "mastul"
    segments := ["m", "a", "s", "t", "u", "l"]
    source := [
      ⟨"arad-2005", "Ch. 2 (29b)"⟩
    ] }

def hitmastel : Form Cell :=
  { id := "arad2005_hitmastel"
    lexeme := Lexemes.to_get_drunk
    cell := {}
    form := "hitmastel"
    segments := ["h", "i", "t", "m", "a", "s", "t", "e", "l"]
    source := [
      ⟨"arad-2005", "Ch. 2 (29b)"⟩
    ] }

def xrop : Form Cell :=
  { id := "arad2005_xrop"
    lexeme := Lexemes.a_snooze
    cell := {}
    form := "xrop"
    segments := ["x", "r", "o", "p"]
    source := [
      ⟨"arad-2005", "Ch. 2 (29c)"⟩
    ] }

def xarap : Form Cell :=
  { id := "arad2005_xarap"
    lexeme := Lexemes.to_snooze
    cell := {}
    form := "xarap"
    segments := ["x", "a", "r", "a", "p"]
    source := [
      ⟨"arad-2005", "Ch. 2 (29c)"⟩
    ] }

def mixshev : Form Cell :=
  { id := "arad2005_mixshev"
    lexeme := Lexemes.to_computerize
    cell := {}
    form := "mixšev"
    segments := ["m", "i", "x", "š", "e", "v"]
    source := [
      ⟨"arad-2005", "Ch. 1 (12b)"⟩,
      ⟨"arad-2005", "Ch. 2 (29d)"⟩
    ] }

def taxzuqa : Form Cell :=
  { id := "arad2005_taxzuqa"
    lexeme := Lexemes.maintenance
    cell := {}
    form := "taxzuqa"
    segments := ["t", "a", "x", "z", "u", "q", "+", "a"]
    source := [
      ⟨"arad-2005", "Ch. 2 (32a)"⟩
    ] }

def tixzeq : Form Cell :=
  { id := "arad2005_tixzeq"
    lexeme := Lexemes.to_maintain
    cell := {}
    form := "tixzeq"
    segments := ["t", "i", "x", "z", "e", "q"]
    source := [
      ⟨"arad-2005", "Ch. 2 (32a)"⟩
    ] }

def misger : Form Cell :=
  { id := "arad2005_misger"
    lexeme := Lexemes.to_frame
    cell := {}
    form := "misger"
    segments := ["m", "i", "s", "g", "e", "r"]
    source := [
      ⟨"arad-2005", "Ch. 2 (32b)"⟩,
      ⟨"arad-2005", "Ch. 7 (6b)"⟩
    ] }

def musgar : Form Cell :=
  { id := "arad2005_musgar"
    lexeme := Lexemes.was_framed
    cell := {}
    form := "musgar"
    segments := ["m", "u", "s", "g", "a", "r"]
    source := [
      ⟨"arad-2005", "Ch. 7 fn. 2"⟩
    ] }

def cenzura : Form Cell :=
  { id := "arad2005_cenzura"
    lexeme := Lexemes.censorship
    cell := {}
    form := "cenzura"
    segments := ["c", "e", "n", "z", "u", "r", "a"]
    source := [
      ⟨"arad-2005", "Ch. 2 (32c)"⟩
    ] }

def cinzer : Form Cell :=
  { id := "arad2005_cinzer"
    lexeme := Lexemes.to_censor
    cell := {}
    form := "cinzer"
    segments := ["c", "i", "n", "z", "e", "r"]
    source := [
      ⟨"arad-2005", "Ch. 2 (32c)"⟩
    ] }

def qav : Form Cell :=
  { id := "arad2005_qav"
    lexeme := Lexemes.line
    cell := {}
    form := "qav"
    segments := ["q", "a", "v"]
    source := [
      ⟨"arad-2005", "Ch. 2 (33a)"⟩
    ] }

def qivqev : Form Cell :=
  { id := "arad2005_qivqev"
    lexeme := Lexemes.to_draw_a_dotted_line
    cell := {}
    form := "qivqev"
    segments := ["q", "i", "v", "q", "e", "v"]
    source := [
      ⟨"arad-2005", "Ch. 2 (33a)"⟩
    ] }

def xov : Form Cell :=
  { id := "arad2005_xov"
    lexeme := Lexemes.debt
    cell := {}
    form := "xov"
    segments := ["x", "o", "v"]
    source := [
      ⟨"arad-2005", "Ch. 2 (33b)"⟩
    ] }

def xiyev : Form Cell :=
  { id := "arad2005_xiyev"
    lexeme := Lexemes.to_debit_oblige
    cell := {}
    form := "xiyev"
    segments := ["x", "i", "y", "e", "v"]
    source := [
      ⟨"arad-2005", "Ch. 2 (33b)"⟩
    ] }

def faks : Form Cell :=
  { id := "arad2005_faks"
    lexeme := Lexemes.fax
    cell := {}
    form := "faks"
    segments := ["f", "a", "k", "s"]
    source := [
      ⟨"arad-2005", "Ch. 2 (33c)"⟩,
      ⟨"arad-2005", "Ch. 7 (41d)"⟩
    ] }

def fikses : Form Cell :=
  { id := "arad2005_fikses"
    lexeme := Lexemes.to_fax
    cell := {}
    form := "fikses"
    segments := ["f", "i", "k", "s", "e", "s"]
    source := [
      ⟨"arad-2005", "Ch. 2 (33c)"⟩,
      ⟨"arad-2005", "Ch. 7 (41d)"⟩
    ] }

def transfer : Form Cell :=
  { id := "arad2005_transfer"
    lexeme := Lexemes.transfer
    cell := {}
    form := "transfer"
    segments := ["t", "r", "a", "n", "s", "f", "e", "r"]
    source := [
      ⟨"arad-2005", "Ch. 1 (12d)"⟩,
      ⟨"arad-2005", "Ch. 7 (39a)"⟩
    ] }

def trinsfer : Form Cell :=
  { id := "arad2005_trinsfer"
    lexeme := Lexemes.to_transfer
    cell := {}
    form := "trinsfer"
    segments := ["t", "r", "i", "n", "s", "f", "e", "r"]
    source := [
      ⟨"arad-2005", "Ch. 1 (12d)"⟩,
      ⟨"arad-2005", "Ch. 7 (39a)"⟩
    ] }

def streptiz : Form Cell :=
  { id := "arad2005_streptiz"
    lexeme := Lexemes.striptease
    cell := {}
    form := "streptiz"
    segments := ["s", "t", "r", "e", "p", "t", "i", "z"]
    source := [
      ⟨"arad-2005", "Ch. 7 (39b)"⟩
    ] }

def striptez : Form Cell :=
  { id := "arad2005_striptez"
    lexeme := Lexemes.to_perform_a_striptease
    cell := {}
    form := "striptez"
    segments := ["s", "t", "r", "i", "p", "t", "e", "z"]
    source := [
      ⟨"arad-2005", "Ch. 1 (12e)"⟩,
      ⟨"arad-2005", "Ch. 7 (39b)"⟩
    ] }

def sinxroni : Form Cell :=
  { id := "arad2005_sinxroni"
    lexeme := Lexemes.synchronic
    cell := {}
    form := "sinxroni"
    segments := ["s", "i", "n", "x", "r", "o", "n", "i"]
    source := [
      ⟨"arad-2005", "Ch. 7 (39c)"⟩
    ] }

def sinxren : Form Cell :=
  { id := "arad2005_sinxren"
    lexeme := Lexemes.synchronize
    cell := {}
    form := "sinxren"
    segments := ["s", "i", "n", "x", "r", "e", "n"]
    source := [
      ⟨"arad-2005", "Ch. 7 (39c)"⟩
    ] }

def qliq : Form Cell :=
  { id := "arad2005_qliq"
    lexeme := Lexemes.a_click
    cell := {}
    form := "qliq"
    segments := ["q", "l", "i", "q"]
    source := [
      ⟨"arad-2005", "Ch. 1 (12c)"⟩,
      ⟨"arad-2005", "Ch. 7 (40a)"⟩
    ] }

def hiqliq : Form Cell :=
  { id := "arad2005_hiqliq"
    lexeme := Lexemes.to_click
    cell := {}
    form := "hiqliq"
    segments := ["h", "i", "q", "l", "i", "q"]
    source := [
      ⟨"arad-2005", "Ch. 1 (12c)"⟩,
      ⟨"arad-2005", "Ch. 7 (40a)"⟩
    ] }

def fliq : Form Cell :=
  { id := "arad2005_fliq"
    lexeme := Lexemes.a_slap
    cell := {}
    form := "fliq"
    segments := ["f", "l", "i", "q"]
    source := [
      ⟨"arad-2005", "Ch. 7 (40b)"⟩
    ] }

def hifliq : Form Cell :=
  { id := "arad2005_hifliq"
    lexeme := Lexemes.to_slap
    cell := {}
    form := "hifliq"
    segments := ["h", "i", "f", "l", "i", "q"]
    source := [
      ⟨"arad-2005", "Ch. 7 (40b)"⟩
    ] }

def shpritz : Form Cell :=
  { id := "arad2005_shpritz"
    lexeme := Lexemes.a_splash
    cell := {}
    form := "špritz"
    segments := ["š", "p", "r", "i", "t", "z"]
    source := [
      ⟨"arad-2005", "Ch. 7 (40c)"⟩
    ] }

def hishpritz : Form Cell :=
  { id := "arad2005_hishpritz"
    lexeme := Lexemes.to_splash
    cell := {}
    form := "hišpritz"
    segments := ["h", "i", "š", "p", "r", "i", "t", "z"]
    source := [
      ⟨"arad-2005", "Ch. 7 (40c)"⟩
    ] }

def xoq : Form Cell :=
  { id := "arad2005_xoq"
    lexeme := Lexemes.law
    cell := {}
    form := "xoq"
    segments := ["x", "o", "q"]
    source := [
      ⟨"arad-2005", "Ch. 7 (41a)"⟩
    ] }

def xoqeq : Form Cell :=
  { id := "arad2005_xoqeq"
    lexeme := Lexemes.legislate
    cell := {}
    form := "xoqeq"
    segments := ["x", "o", "q", "e", "q"]
    source := [
      ⟨"arad-2005", "Ch. 7 (41a)"⟩
    ] }

def qod : Form Cell :=
  { id := "arad2005_qod"
    lexeme := Lexemes.code
    cell := {}
    form := "qod"
    segments := ["q", "o", "d"]
    source := [
      ⟨"arad-2005", "Ch. 7 (41b)"⟩
    ] }

def qoded : Form Cell :=
  { id := "arad2005_qoded"
    lexeme := Lexemes.codify
    cell := {}
    form := "qoded"
    segments := ["q", "o", "d", "e", "d"]
    source := [
      ⟨"arad-2005", "Ch. 7 (41b)"⟩
    ] }

def dam : Form Cell :=
  { id := "arad2005_dam"
    lexeme := Lexemes.blood
    cell := {}
    form := "dam"
    segments := ["d", "a", "m"]
    source := [
      ⟨"arad-2005", "Ch. 7 (41c)"⟩
    ] }

def dimem : Form Cell :=
  { id := "arad2005_dimem"
    lexeme := Lexemes.bleed
    cell := {}
    form := "dimem"
    segments := ["d", "i", "m", "e", "m"]
    source := [
      ⟨"arad-2005", "Ch. 7 (41c)"⟩
    ] }

def chat : Form Cell :=
  { id := "arad2005_chat"
    lexeme := Lexemes.chat
    cell := {}
    form := "čat"
    segments := ["č", "a", "t"]
    source := [
      ⟨"arad-2005", "Ch. 7 (41e)"⟩
    ] }

def chitet : Form Cell :=
  { id := "arad2005_chitet"
    lexeme := Lexemes.to_chat
    cell := {}
    form := "čitet"
    segments := ["č", "i", "t", "e", "t"]
    source := [
      ⟨"arad-2005", "Ch. 7 (41e)"⟩
    ] }

/-- The source's analysis of a form, its parse rather than data. -/
structure Analysis where
  /-- The form analysed. -/
  form : Form Cell
  /-- The `Root` column. -/
  root : Option String := none
  /-- The `Binyan` column. -/
  binyan : Option String := none
  /-- The `Pattern` column. -/
  pattern : Option String := none
  /-- The `Conjugation` column. -/
  conjugation : Option String := none
  /-- The `Alternant` column. -/
  alternant : Option String := none
  deriving DecidableEq, Repr

def lamad.analysis : Analysis :=
  { form := lamad,
    root := some "lmd",
    binyan := some "1" }

def nilmad.analysis : Analysis :=
  { form := nilmad,
    root := some "lmd",
    binyan := some "2" }

def siper.analysis : Analysis :=
  { form := siper,
    root := some "spr",
    binyan := some "3" }

def supar.analysis : Analysis :=
  { form := supar,
    root := some "spr",
    binyan := some "4" }

def hiqlit.analysis : Analysis :=
  { form := hiqlit,
    root := some "qlt",
    binyan := some "5" }

def huqlat.analysis : Analysis :=
  { form := huqlat,
    root := some "qlt",
    binyan := some "6" }

def hitpalel.analysis : Analysis :=
  { form := hitpalel,
    root := some "pll",
    binyan := some "7" }

def nipec.analysis : Analysis :=
  { form := nipec,
    root := some "npc",
    binyan := some "3" }

def nupac.analysis : Analysis :=
  { form := nupac,
    root := some "npc",
    binyan := some "4" }

def xileq.analysis : Analysis :=
  { form := xileq,
    root := some "xlq",
    binyan := some "3" }

def xulaq.analysis : Analysis :=
  { form := xulaq,
    root := some "xlq",
    binyan := some "4" }

def histir.analysis : Analysis :=
  { form := histir,
    root := some "str",
    binyan := some "5" }

def hustar.analysis : Analysis :=
  { form := hustar,
    root := some "str",
    binyan := some "6" }

def hifqid.analysis : Analysis :=
  { form := hifqid,
    root := some "pqd",
    binyan := some "5" }

def hufqad.analysis : Analysis :=
  { form := hufqad,
    root := some "pqd",
    binyan := some "6" }

def shamar.analysis : Analysis :=
  { form := shamar,
    root := some "šmr",
    binyan := some "1" }

def tirgem.analysis : Analysis :=
  { form := tirgem,
    root := some "trgm",
    binyan := some "3" }

def qibel.analysis : Analysis :=
  { form := qibel,
    root := some "qbl",
    binyan := some "3" }

def hitrakex.analysis : Analysis :=
  { form := hitrakex,
    root := some "rkk",
    binyan := some "7" }

def shemen.analysis : Analysis :=
  { form := shemen,
    root := some "šmn",
    pattern := some "CeCeC" }

def shamenet.analysis : Analysis :=
  { form := shamenet,
    root := some "šmn",
    pattern := some "CaCCeCet" }

def shuman.analysis : Analysis :=
  { form := shuman,
    root := some "šmn",
    pattern := some "CuCaC" }

def shamen.analysis : Analysis :=
  { form := shamen,
    root := some "šmn",
    pattern := some "CaCeC" }

def hishmin.analysis : Analysis :=
  { form := hishmin,
    root := some "šmn",
    binyan := some "5" }

def shimen.analysis : Analysis :=
  { form := shimen,
    root := some "šmn",
    binyan := some "3" }

def xashav.analysis : Analysis :=
  { form := xashav,
    root := some "xšb",
    binyan := some "1" }

def xishev.analysis : Analysis :=
  { form := xishev,
    root := some "xšb",
    binyan := some "3" }

def hexshiv.analysis : Analysis :=
  { form := hexshiv,
    root := some "xšb",
    binyan := some "5" }

def hitxashev.analysis : Analysis :=
  { form := hitxashev,
    root := some "xšb",
    binyan := some "7" }

def maxshev.analysis : Analysis :=
  { form := maxshev,
    root := some "xšb",
    pattern := some "maCCeC" }

def maxshava.analysis : Analysis :=
  { form := maxshava,
    root := some "xšb",
    pattern := some "maCCaCa" }

def xashivut.analysis : Analysis :=
  { form := xashivut,
    root := some "xšb",
    pattern := some "CCiCut" }

def xeshbon.analysis : Analysis :=
  { form := xeshbon,
    root := some "xšb",
    pattern := some "CiCCon" }

def taxshiv.analysis : Analysis :=
  { form := taxshiv,
    root := some "xšb",
    pattern := some "taCCiC" }

def qalat.analysis : Analysis :=
  { form := qalat,
    root := some "qlt",
    binyan := some "1" }

def miqlat.analysis : Analysis :=
  { form := miqlat,
    root := some "qlt",
    pattern := some "miCCaC" }

def maqlet.analysis : Analysis :=
  { form := maqlet,
    root := some "qlt",
    pattern := some "maCCeC" }

def taqlit.analysis : Analysis :=
  { form := taqlit,
    root := some "qlt",
    pattern := some "taCCiC" }

def qaletet.analysis : Analysis :=
  { form := qaletet,
    root := some "qlt",
    pattern := some "CaCCeCet" }

def qelet.analysis : Analysis :=
  { form := qelet,
    root := some "qlt",
    pattern := some "CeCeC" }

def sagar.analysis : Analysis :=
  { form := sagar,
    root := some "sgr",
    binyan := some "1" }

def hisgir.analysis : Analysis :=
  { form := hisgir,
    root := some "sgr",
    binyan := some "5" }

def histager.analysis : Analysis :=
  { form := histager,
    root := some "sgr",
    binyan := some "7" }

def seger.analysis : Analysis :=
  { form := seger,
    root := some "sgr",
    pattern := some "CeCeC" }

def sograyim.analysis : Analysis :=
  { form := sograyim,
    root := some "sgr",
    pattern := some "CoCCayim" }

def misgeret.analysis : Analysis :=
  { form := misgeret,
    root := some "sgr",
    pattern := some "miCCeCet" }

def patax.analysis : Analysis :=
  { form := patax,
    root := some "ptx",
    binyan := some "1",
    conjugation := some "1",
    alternant := some "causative" }

def niftax.analysis : Analysis :=
  { form := niftax,
    root := some "ptx",
    binyan := some "2",
    conjugation := some "1",
    alternant := some "inchoative" }

def qafa.analysis : Analysis :=
  { form := qafa,
    root := some "qpʔ",
    binyan := some "1",
    conjugation := some "2",
    alternant := some "non-causative" }

def hiqpi.analysis : Analysis :=
  { form := hiqpi,
    root := some "qpʔ",
    binyan := some "5",
    conjugation := some "2",
    alternant := some "causative" }

def namas.analysis : Analysis :=
  { form := namas,
    root := some "mss",
    binyan := some "2",
    conjugation := some "3",
    alternant := some "inchoative" }

def hemes.analysis : Analysis :=
  { form := hemes,
    root := some "mss",
    binyan := some "5",
    conjugation := some "3",
    alternant := some "causative" }

def hitxamem.analysis : Analysis :=
  { form := hitxamem,
    root := some "xmm",
    binyan := some "7",
    conjugation := some "4",
    alternant := some "inchoative" }

def ximem.analysis : Analysis :=
  { form := ximem,
    root := some "xmm",
    binyan := some "3",
    conjugation := some "4",
    alternant := some "causative" }

def hitbaher.analysis : Analysis :=
  { form := hitbaher,
    root := some "bhr",
    binyan := some "7",
    conjugation := some "5",
    alternant := some "inchoative" }

def hivhir.analysis : Analysis :=
  { form := hivhir,
    root := some "bhr",
    binyan := some "5",
    conjugation := some "5",
    alternant := some "causative" }

def heedim_inchoative.analysis : Analysis :=
  { form := heedim_inchoative,
    root := some "ʔdm",
    binyan := some "5",
    conjugation := some "6",
    alternant := some "inchoative" }

def heedim_causative.analysis : Analysis :=
  { form := heedim_causative,
    root := some "ʔdm",
    binyan := some "5",
    conjugation := some "6",
    alternant := some "causative" }

def taqciv.analysis : Analysis :=
  { form := taqciv }

def tiqcev.analysis : Analysis :=
  { form := tiqcev }

def telefon.analysis : Analysis :=
  { form := telefon }

def tilfen.analysis : Analysis :=
  { form := tilfen,
    binyan := some "3" }

def mastul.analysis : Analysis :=
  { form := mastul }

def hitmastel.analysis : Analysis :=
  { form := hitmastel,
    binyan := some "7" }

def xrop.analysis : Analysis :=
  { form := xrop }

def xarap.analysis : Analysis :=
  { form := xarap,
    binyan := some "1" }

def mixshev.analysis : Analysis :=
  { form := mixshev,
    binyan := some "3" }

def taxzuqa.analysis : Analysis :=
  { form := taxzuqa,
    root := some "xzq" }

def tixzeq.analysis : Analysis :=
  { form := tixzeq }

def misger.analysis : Analysis :=
  { form := misger,
    binyan := some "3" }

def musgar.analysis : Analysis :=
  { form := musgar,
    binyan := some "4" }

def cenzura.analysis : Analysis :=
  { form := cenzura }

def cinzer.analysis : Analysis :=
  { form := cinzer }

def qav.analysis : Analysis :=
  { form := qav }

def qivqev.analysis : Analysis :=
  { form := qivqev }

def xov.analysis : Analysis :=
  { form := xov }

def xiyev.analysis : Analysis :=
  { form := xiyev }

def faks.analysis : Analysis :=
  { form := faks }

def fikses.analysis : Analysis :=
  { form := fikses }

def transfer.analysis : Analysis :=
  { form := transfer }

def trinsfer.analysis : Analysis :=
  { form := trinsfer }

def streptiz.analysis : Analysis :=
  { form := streptiz }

def striptez.analysis : Analysis :=
  { form := striptez }

def sinxroni.analysis : Analysis :=
  { form := sinxroni }

def sinxren.analysis : Analysis :=
  { form := sinxren }

def qliq.analysis : Analysis :=
  { form := qliq }

def hiqliq.analysis : Analysis :=
  { form := hiqliq,
    binyan := some "5" }

def fliq.analysis : Analysis :=
  { form := fliq }

def hifliq.analysis : Analysis :=
  { form := hifliq,
    binyan := some "5" }

def shpritz.analysis : Analysis :=
  { form := shpritz }

def hishpritz.analysis : Analysis :=
  { form := hishpritz,
    binyan := some "5" }

def xoq.analysis : Analysis :=
  { form := xoq }

def xoqeq.analysis : Analysis :=
  { form := xoqeq }

def qod.analysis : Analysis :=
  { form := qod }

def qoded.analysis : Analysis :=
  { form := qoded }

def dam.analysis : Analysis :=
  { form := dam }

def dimem.analysis : Analysis :=
  { form := dimem }

def chat.analysis : Analysis :=
  { form := chat }

def chitet.analysis : Analysis :=
  { form := chitet }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.learn, Lexemes.learn_passive, Lexemes.tell,
  Lexemes.tell_passive, Lexemes.record, Lexemes.record_passive, Lexemes.pray, Lexemes.shatter,
  Lexemes.shatter_passive, Lexemes.divide, Lexemes.divide_passive, Lexemes.hide,
  Lexemes.hide_passive, Lexemes.deposit, Lexemes.deposit_passive, Lexemes.guard, Lexemes.translate,
  Lexemes.receive, Lexemes.become_soft, Lexemes.oil_grease, Lexemes.cream, Lexemes.fat,
  Lexemes.fat_adj, Lexemes.grow_fat_fatten, Lexemes.grease, Lexemes.to_think, Lexemes.to_calculate,
  Lexemes.to_consider, Lexemes.to_be_considerate, Lexemes.computer, Lexemes.a_thought,
  Lexemes.importance, Lexemes.arithmetic_bill, Lexemes.calculus, Lexemes.to_absorb_receive,
  Lexemes.a_shelter, Lexemes.a_receiver, Lexemes.a_record, Lexemes.a_cassette, Lexemes.input,
  Lexemes.close, Lexemes.extradite, Lexemes.cocoon_oneself, Lexemes.closure, Lexemes.parentheses,
  Lexemes.frame, Lexemes.open_causative, Lexemes.open_inchoative, Lexemes.freeze_inchoative,
  Lexemes.freeze_causative, Lexemes.melt_inchoative, Lexemes.melt_causative,
  Lexemes.heat_inchoative, Lexemes.heat_causative, Lexemes.become_clear, Lexemes.make_clear,
  Lexemes.be_red, Lexemes.redden, Lexemes.budget, Lexemes.to_budget, Lexemes.telephone,
  Lexemes.to_telephone, Lexemes.drunk, Lexemes.to_get_drunk, Lexemes.a_snooze, Lexemes.to_snooze,
  Lexemes.to_computerize, Lexemes.maintenance, Lexemes.to_maintain, Lexemes.to_frame,
  Lexemes.was_framed, Lexemes.censorship, Lexemes.to_censor, Lexemes.line,
  Lexemes.to_draw_a_dotted_line, Lexemes.debt, Lexemes.to_debit_oblige, Lexemes.fax, Lexemes.to_fax,
  Lexemes.transfer, Lexemes.to_transfer, Lexemes.striptease, Lexemes.to_perform_a_striptease,
  Lexemes.synchronic, Lexemes.synchronize, Lexemes.a_click, Lexemes.to_click, Lexemes.a_slap,
  Lexemes.to_slap, Lexemes.a_splash, Lexemes.to_splash, Lexemes.law, Lexemes.legislate,
  Lexemes.code, Lexemes.codify, Lexemes.blood, Lexemes.bleed, Lexemes.chat, Lexemes.to_chat]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [lamad, nilmad, siper, supar, hiqlit, huqlat, hitpalel, nipec, nupac,
  xileq, xulaq, histir, hustar, hifqid, hufqad, shamar, tirgem, qibel, hitrakex, shemen, shamenet,
  shuman, shamen, hishmin, shimen, xashav, xishev, hexshiv, hitxashev, maxshev, maxshava, xashivut,
  xeshbon, taxshiv, qalat, miqlat, maqlet, taqlit, qaletet, qelet, sagar, hisgir, histager, seger,
  sograyim, misgeret, patax, niftax, qafa, hiqpi, namas, hemes, hitxamem, ximem, hitbaher, hivhir,
  heedim_inchoative, heedim_causative, taqciv, tiqcev, telefon, tilfen, mastul, hitmastel, xrop,
  xarap, mixshev, taxzuqa, tixzeq, misger, musgar, cenzura, cinzer, qav, qivqev, xov, xiyev, faks,
  fikses, transfer, trinsfer, streptiz, striptez, sinxroni, sinxren, qliq, hiqliq, fliq, hifliq,
  shpritz, hishpritz, xoq, xoqeq, qod, qoded, dam, dimem, chat, chitet]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := [
  { id := "arad2005_tiqcev_from_taqciv", form := taqciv, target := tiqcev, relation := "denominal",
    source := [
      ⟨"arad-2005", "Ch. 1 (12a)"⟩
    ] },
  { id := "arad2005_tilfen_from_telefon", form := telefon, target := tilfen,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 2 (29a)"⟩
    ] },
  { id := "arad2005_hitmastel_from_mastul", form := mastul, target := hitmastel,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 2 (29b)"⟩
    ] },
  { id := "arad2005_xarap_from_xrop", form := xrop, target := xarap, relation := "denominal",
    source := [
      ⟨"arad-2005", "Ch. 2 (29c)"⟩
    ] },
  { id := "arad2005_mixshev_from_maxshev", form := maxshev, target := mixshev,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 1 (12b)"⟩,
      ⟨"arad-2005", "Ch. 2 (29d)"⟩
    ] },
  { id := "arad2005_tixzeq_from_taxzuqa", form := taxzuqa, target := tixzeq,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 2 (32a)"⟩
    ] },
  { id := "arad2005_misger_from_misgeret", form := misgeret, target := misger,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 2 (32b)"⟩,
      ⟨"arad-2005", "Ch. 7 (6b)"⟩,
      ⟨"arad-2005", "Ch. 7 (7b)"⟩
    ] },
  { id := "arad2005_musgar_from_misgeret", form := misgeret, target := musgar,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 7 fn. 2"⟩
    ] },
  { id := "arad2005_cinzer_from_cenzura", form := cenzura, target := cinzer,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 2 (32c)"⟩
    ] },
  { id := "arad2005_qivqev_from_qav", form := qav, target := qivqev, relation := "denominal",
    source := [
      ⟨"arad-2005", "Ch. 2 (33a)"⟩
    ] },
  { id := "arad2005_xiyev_from_xov", form := xov, target := xiyev, relation := "denominal",
    source := [
      ⟨"arad-2005", "Ch. 2 (33b)"⟩
    ] },
  { id := "arad2005_fikses_from_faks", form := faks, target := fikses, relation := "denominal",
    source := [
      ⟨"arad-2005", "Ch. 2 (33c)"⟩,
      ⟨"arad-2005", "Ch. 7 (41d)"⟩
    ] },
  { id := "arad2005_trinsfer_from_transfer", form := transfer, target := trinsfer,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 1 (12d)"⟩,
      ⟨"arad-2005", "Ch. 7 (39a)"⟩
    ] },
  { id := "arad2005_striptez_from_streptiz", form := streptiz, target := striptez,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 1 (12e)"⟩,
      ⟨"arad-2005", "Ch. 7 (39b)"⟩
    ] },
  { id := "arad2005_sinxren_from_sinxroni", form := sinxroni, target := sinxren,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 7 (39c)"⟩
    ] },
  { id := "arad2005_hiqliq_from_qliq", form := qliq, target := hiqliq, relation := "denominal",
    source := [
      ⟨"arad-2005", "Ch. 1 (12c)"⟩,
      ⟨"arad-2005", "Ch. 7 (40a)"⟩
    ] },
  { id := "arad2005_hifliq_from_fliq", form := fliq, target := hifliq, relation := "denominal",
    source := [
      ⟨"arad-2005", "Ch. 7 (40b)"⟩
    ] },
  { id := "arad2005_hishpritz_from_shpritz", form := shpritz, target := hishpritz,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 7 (40c)"⟩
    ] },
  { id := "arad2005_xoqeq_from_xoq", form := xoq, target := xoqeq, relation := "denominal",
    source := [
      ⟨"arad-2005", "Ch. 7 (41a)"⟩
    ] },
  { id := "arad2005_qoded_from_qod", form := qod, target := qoded, relation := "denominal",
    source := [
      ⟨"arad-2005", "Ch. 7 (41b)"⟩
    ] },
  { id := "arad2005_dimem_from_dam", form := dam, target := dimem, relation := "denominal",
    source := [
      ⟨"arad-2005", "Ch. 7 (41c)"⟩
    ] },
  { id := "arad2005_chitet_from_chat", form := chat, target := chitet, relation := "denominal",
    source := [
      ⟨"arad-2005", "Ch. 7 (41e)"⟩
    ] }]

/-- Every relation the sources assert, between the forms' analyses. -/
def analysisRelations : List (FormRelation Analysis) := [
  { id := "arad2005_tiqcev_from_taqciv", form := taqciv.analysis, target := tiqcev.analysis,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 1 (12a)"⟩
    ] },
  { id := "arad2005_tilfen_from_telefon", form := telefon.analysis, target := tilfen.analysis,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 2 (29a)"⟩
    ] },
  { id := "arad2005_hitmastel_from_mastul", form := mastul.analysis, target := hitmastel.analysis,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 2 (29b)"⟩
    ] },
  { id := "arad2005_xarap_from_xrop", form := xrop.analysis, target := xarap.analysis,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 2 (29c)"⟩
    ] },
  { id := "arad2005_mixshev_from_maxshev", form := maxshev.analysis, target := mixshev.analysis,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 1 (12b)"⟩,
      ⟨"arad-2005", "Ch. 2 (29d)"⟩
    ] },
  { id := "arad2005_tixzeq_from_taxzuqa", form := taxzuqa.analysis, target := tixzeq.analysis,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 2 (32a)"⟩
    ] },
  { id := "arad2005_misger_from_misgeret", form := misgeret.analysis, target := misger.analysis,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 2 (32b)"⟩,
      ⟨"arad-2005", "Ch. 7 (6b)"⟩,
      ⟨"arad-2005", "Ch. 7 (7b)"⟩
    ] },
  { id := "arad2005_musgar_from_misgeret", form := misgeret.analysis, target := musgar.analysis,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 7 fn. 2"⟩
    ] },
  { id := "arad2005_cinzer_from_cenzura", form := cenzura.analysis, target := cinzer.analysis,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 2 (32c)"⟩
    ] },
  { id := "arad2005_qivqev_from_qav", form := qav.analysis, target := qivqev.analysis,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 2 (33a)"⟩
    ] },
  { id := "arad2005_xiyev_from_xov", form := xov.analysis, target := xiyev.analysis,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 2 (33b)"⟩
    ] },
  { id := "arad2005_fikses_from_faks", form := faks.analysis, target := fikses.analysis,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 2 (33c)"⟩,
      ⟨"arad-2005", "Ch. 7 (41d)"⟩
    ] },
  { id := "arad2005_trinsfer_from_transfer", form := transfer.analysis, target := trinsfer.analysis,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 1 (12d)"⟩,
      ⟨"arad-2005", "Ch. 7 (39a)"⟩
    ] },
  { id := "arad2005_striptez_from_streptiz", form := streptiz.analysis, target := striptez.analysis,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 1 (12e)"⟩,
      ⟨"arad-2005", "Ch. 7 (39b)"⟩
    ] },
  { id := "arad2005_sinxren_from_sinxroni", form := sinxroni.analysis, target := sinxren.analysis,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 7 (39c)"⟩
    ] },
  { id := "arad2005_hiqliq_from_qliq", form := qliq.analysis, target := hiqliq.analysis,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 1 (12c)"⟩,
      ⟨"arad-2005", "Ch. 7 (40a)"⟩
    ] },
  { id := "arad2005_hifliq_from_fliq", form := fliq.analysis, target := hifliq.analysis,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 7 (40b)"⟩
    ] },
  { id := "arad2005_hishpritz_from_shpritz", form := shpritz.analysis, target := hishpritz.analysis,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 7 (40c)"⟩
    ] },
  { id := "arad2005_xoqeq_from_xoq", form := xoq.analysis, target := xoqeq.analysis,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 7 (41a)"⟩
    ] },
  { id := "arad2005_qoded_from_qod", form := qod.analysis, target := qoded.analysis,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 7 (41b)"⟩
    ] },
  { id := "arad2005_dimem_from_dam", form := dam.analysis, target := dimem.analysis,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 7 (41c)"⟩
    ] },
  { id := "arad2005_chitet_from_chat", form := chat.analysis, target := chitet.analysis,
    relation := "denominal", source := [
      ⟨"arad-2005", "Ch. 7 (41e)"⟩
    ] }]

/-- Every analysis of the data. -/
def analyses : List Analysis := [lamad.analysis, nilmad.analysis, siper.analysis, supar.analysis,
  hiqlit.analysis, huqlat.analysis, hitpalel.analysis, nipec.analysis, nupac.analysis,
  xileq.analysis, xulaq.analysis, histir.analysis, hustar.analysis, hifqid.analysis,
  hufqad.analysis, shamar.analysis, tirgem.analysis, qibel.analysis, hitrakex.analysis,
  shemen.analysis, shamenet.analysis, shuman.analysis, shamen.analysis, hishmin.analysis,
  shimen.analysis, xashav.analysis, xishev.analysis, hexshiv.analysis, hitxashev.analysis,
  maxshev.analysis, maxshava.analysis, xashivut.analysis, xeshbon.analysis, taxshiv.analysis,
  qalat.analysis, miqlat.analysis, maqlet.analysis, taqlit.analysis, qaletet.analysis,
  qelet.analysis, sagar.analysis, hisgir.analysis, histager.analysis, seger.analysis,
  sograyim.analysis, misgeret.analysis, patax.analysis, niftax.analysis, qafa.analysis,
  hiqpi.analysis, namas.analysis, hemes.analysis, hitxamem.analysis, ximem.analysis,
  hitbaher.analysis, hivhir.analysis, heedim_inchoative.analysis, heedim_causative.analysis,
  tilfen.analysis, hitmastel.analysis, xarap.analysis, mixshev.analysis, taxzuqa.analysis,
  misger.analysis, musgar.analysis, hiqliq.analysis, hifliq.analysis, hishpritz.analysis]

end Arad2005.Wordlist
