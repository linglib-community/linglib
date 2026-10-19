module

public import Linglib.Data.Forms.Schema

/-!
# `Istratkova2004`: word forms

Auto-generated from `Linglib/Data/Forms/Istratkova2004.json` by `scripts/gen_forms.py`. Do not edit
by hand; edit the JSON and re-run the generator. Declarations live in `namespace
Istratkova2004.Forms`.
-/

@[expose] public section

namespace Istratkova2004.Forms

open Data.Forms

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

/-- The 1sg.prs cell, `Tense=Pres|Number=Sing|Person=1`. -/
def prs_1sg : Cell :=
  { tense := ↑UD.Tense.Pres, number := ↑UD.Number.Sing, person := ↑UD.Person.first }

def Lexemes.zapisa : Lexeme :=
  { id := "zapisa", languageId := "bulg1262", parameterId := "put_down_in_writing",
    pos := ↑UD.UPOS.VERB }

def Lexemes.napisa : Lexeme :=
  { id := "napisa", languageId := "bulg1262", parameterId := "write_down", pos := ↑UD.UPOS.VERB }

def Lexemes.prepisa : Lexeme :=
  { id := "prepisa", languageId := "bulg1262", parameterId := "copy_cheat", pos := ↑UD.UPOS.VERB }

def Lexemes.podpisa : Lexeme :=
  { id := "podpisa", languageId := "bulg1262", parameterId := "sign", pos := ↑UD.UPOS.VERB }

def Lexemes.doveda : Lexeme :=
  { id := "doveda", languageId := "bulg1262", parameterId := "bring_someone", pos := ↑UD.UPOS.VERB }

def Lexemes.zaveda : Lexeme :=
  { id := "zaveda", languageId := "bulg1262", parameterId := "take_someone", pos := ↑UD.UPOS.VERB }

def Lexemes.izveda : Lexeme :=
  { id := "izveda", languageId := "bulg1262", parameterId := "take_someone_out",
    pos := ↑UD.UPOS.VERB }

def Lexemes.vida : Lexeme :=
  { id := "vida", languageId := "bulg1262", parameterId := "see", pos := ↑UD.UPOS.VERB }

def Lexemes.zavida : Lexeme :=
  { id := "zavida", languageId := "bulg1262", parameterId := "envy", pos := ↑UD.UPOS.VERB }

def Lexemes.obuja : Lexeme :=
  { id := "obuja", languageId := "bulg1262", parameterId := "put_on_shoes_trousers_etc",
    pos := ↑UD.UPOS.VERB }

def Lexemes.preobuja : Lexeme :=
  { id := "preobuja", languageId := "bulg1262", parameterId := "change_shoes_trousers_etc",
    pos := ↑UD.UPOS.VERB }

def Lexemes.misla : Lexeme :=
  { id := "misla", languageId := "bulg1262", parameterId := "think", pos := ↑UD.UPOS.VERB }

def Lexemes.obicam : Lexeme :=
  { id := "obicam", languageId := "bulg1262", parameterId := "love", pos := ↑UD.UPOS.VERB }

def Lexemes.znam : Lexeme :=
  { id := "znam", languageId := "bulg1262", parameterId := "know", pos := ↑UD.UPOS.VERB }

def Lexemes.blesta : Lexeme :=
  { id := "blesta", languageId := "bulg1262", parameterId := "glitter", pos := ↑UD.UPOS.VERB }

def Lexemes.spa : Lexeme :=
  { id := "spa", languageId := "bulg1262", parameterId := "sleep", pos := ↑UD.UPOS.VERB }

def Lexemes.pisa : Lexeme :=
  { id := "pisa", languageId := "bulg1262", parameterId := "write", pos := ↑UD.UPOS.VERB }

def Lexemes.ziveja : Lexeme :=
  { id := "ziveja", languageId := "bulg1262", parameterId := "live", pos := ↑UD.UPOS.VERB }

def Lexemes.ceta : Lexeme :=
  { id := "ceta", languageId := "bulg1262", parameterId := "read", pos := ↑UD.UPOS.VERB }

def Lexemes.izmisla : Lexeme :=
  { id := "izmisla", languageId := "bulg1262", parameterId := "make_up_a_story",
    pos := ↑UD.UPOS.VERB }

def Lexemes.zaobicam : Lexeme :=
  { id := "zaobicam", languageId := "bulg1262", parameterId := "start_to_love",
    pos := ↑UD.UPOS.VERB }

def Lexemes.poznam : Lexeme :=
  { id := "poznam", languageId := "bulg1262", parameterId := "guess", pos := ↑UD.UPOS.VERB }

def Lexemes.zablesta : Lexeme :=
  { id := "zablesta", languageId := "bulg1262", parameterId := "start_to_glitter",
    pos := ↑UD.UPOS.VERB }

def Lexemes.blesna : Lexeme :=
  { id := "blesna", languageId := "bulg1262", parameterId := "flash", pos := ↑UD.UPOS.VERB }

def Lexemes.zaspa : Lexeme :=
  { id := "zaspa", languageId := "bulg1262", parameterId := "fall_asleep", pos := ↑UD.UPOS.VERB }

def Lexemes.doziveja : Lexeme :=
  { id := "doziveja", languageId := "bulg1262", parameterId := "live_through",
    pos := ↑UD.UPOS.VERB }

def Lexemes.proceta : Lexeme :=
  { id := "proceta", languageId := "bulg1262", parameterId := "read_completely",
    pos := ↑UD.UPOS.VERB }

def Lexemes.kupa : Lexeme :=
  { id := "kupa", languageId := "bulg1262", parameterId := "buy", pos := ↑UD.UPOS.VERB }

def Lexemes.dam : Lexeme :=
  { id := "dam", languageId := "bulg1262", parameterId := "give", pos := ↑UD.UPOS.VERB }

def Lexemes.izkupa : Lexeme :=
  { id := "izkupa", languageId := "bulg1262", parameterId := "buy_everything_completely",
    pos := ↑UD.UPOS.VERB }

def Lexemes.prodam : Lexeme :=
  { id := "prodam", languageId := "bulg1262", parameterId := "sell", pos := ↑UD.UPOS.VERB }

def Lexemes.zavisa : Lexeme :=
  { id := "zavisa", languageId := "bulg1262", parameterId := "depend", pos := ↑UD.UPOS.VERB }

def Lexemes.visa : Lexeme :=
  { id := "visa", languageId := "bulg1262", parameterId := "the_simplex_of_depend",
    pos := ↑UD.UPOS.VERB }

def Lexemes.podleza : Lexeme :=
  { id := "podleza", languageId := "bulg1262", parameterId := "be_subject_to",
    pos := ↑UD.UPOS.VERB }

def Lexemes.leza : Lexeme :=
  { id := "leza", languageId := "bulg1262", parameterId := "the_simplex_of_be_subject_to",
    pos := ↑UD.UPOS.VERB }

def Lexemes.predcuvstvam : Lexeme :=
  { id := "predcuvstvam", languageId := "bulg1262", parameterId := "sense", pos := ↑UD.UPOS.VERB }

def Lexemes.cuvstvam : Lexeme :=
  { id := "cuvstvam", languageId := "bulg1262", parameterId := "the_simplex_of_sense",
    pos := ↑UD.UPOS.VERB }

def Lexemes.predsestvam : Lexeme :=
  { id := "predsestvam", languageId := "bulg1262", parameterId := "precede", pos := ↑UD.UPOS.VERB }

def Lexemes.sestvam : Lexeme :=
  { id := "sestvam", languageId := "bulg1262", parameterId := "the_simplex_of_precede",
    pos := ↑UD.UPOS.VERB }

def Lexemes.predstoja : Lexeme :=
  { id := "predstoja", languageId := "bulg1262", parameterId := "be_due", pos := ↑UD.UPOS.VERB }

def Lexemes.stoja : Lexeme :=
  { id := "stoja", languageId := "bulg1262", parameterId := "the_simplex_of_be_due",
    pos := ↑UD.UPOS.VERB }

def Lexemes.otstoja : Lexeme :=
  { id := "otstoja", languageId := "bulg1262", parameterId := "be_distant_from",
    pos := ↑UD.UPOS.VERB }

def Lexemes.otstoja_2 : Lexeme :=
  { id := "otstoja_2", languageId := "bulg1262", parameterId := "defend_ones_opinion",
    pos := ↑UD.UPOS.VERB }

def Lexemes.izponarazprodam : Lexeme :=
  { id := "izponarazprodam", languageId := "bulg1262",
    parameterId := "sell_completely_many_things_in_excess_one_by_one", pos := ↑UD.UPOS.VERB }

def Lexemes.izkaza : Lexeme :=
  { id := "izkaza", languageId := "bulg1262", parameterId := "express", pos := ↑UD.UPOS.VERB }

def Lexemes.razkaza : Lexeme :=
  { id := "razkaza", languageId := "bulg1262", parameterId := "narrate", pos := ↑UD.UPOS.VERB }

def Lexemes.izdam : Lexeme :=
  { id := "izdam", languageId := "bulg1262", parameterId := "publish", pos := ↑UD.UPOS.VERB }

def Lexemes.razdam : Lexeme :=
  { id := "razdam", languageId := "bulg1262", parameterId := "distribute", pos := ↑UD.UPOS.VERB }

def Lexemes.izrazkaza : Lexeme :=
  { id := "izrazkaza", languageId := "bulg1262", parameterId := "narrate_completely",
    pos := ↑UD.UPOS.VERB }

def Lexemes.izrazdam : Lexeme :=
  { id := "izrazdam", languageId := "bulg1262", parameterId := "distribute_completely",
    pos := ↑UD.UPOS.VERB }

def Lexemes.nadam : Lexeme :=
  { id := "nadam", languageId := "bulg1262", parameterId := "give_many_things_or_to_many",
    pos := ↑UD.UPOS.VERB }

def Lexemes.nakaza : Lexeme :=
  { id := "nakaza", languageId := "bulg1262", parameterId := "punish_say_many_things",
    pos := ↑UD.UPOS.VERB }

def Lexemes.izponakaza : Lexeme :=
  { id := "izponakaza", languageId := "bulg1262",
    parameterId := "punish_completely_little_by_little_tell_many_things_complete",
    pos := ↑UD.UPOS.VERB }

def Lexemes.razpreprodam : Lexeme :=
  { id := "razpreprodam", languageId := "bulg1262", parameterId := "sell_again_in_excess",
    pos := ↑UD.UPOS.VERB }

def Lexemes.popreprodam : Lexeme :=
  { id := "popreprodam", languageId := "bulg1262", parameterId := "sell_again_a_little_bit",
    pos := ↑UD.UPOS.VERB }

def Lexemes.napreprodam : Lexeme :=
  { id := "napreprodam", languageId := "bulg1262", parameterId := "sell_again_many_things",
    pos := ↑UD.UPOS.VERB }

def Lexemes.naprerazkaza : Lexeme :=
  { id := "naprerazkaza", languageId := "bulg1262", parameterId := "narrate_again_a_lot",
    pos := ↑UD.UPOS.VERB }

def Lexemes.izpreprodam : Lexeme :=
  { id := "izpreprodam", languageId := "bulg1262", parameterId := "sell_again_completely",
    pos := ↑UD.UPOS.VERB }

def Lexemes.izprerazkaza : Lexeme :=
  { id := "izprerazkaza", languageId := "bulg1262", parameterId := "completely_narrate_again",
    pos := ↑UD.UPOS.VERB }

def Lexemes.porazpreprodam : Lexeme :=
  { id := "porazpreprodam", languageId := "bulg1262",
    parameterId := "sell_again_a_few_things_with_low_intensity", pos := ↑UD.UPOS.VERB }

def Lexemes.izrazpreprodam : Lexeme :=
  { id := "izrazpreprodam", languageId := "bulg1262",
    parameterId := "completely_sell_again_to_the_very_end_in_excess", pos := ↑UD.UPOS.VERB }

def Lexemes.napreprodam_2 : Lexeme :=
  { id := "napreprodam_2", languageId := "bulg1262", parameterId := "sell_again_a_lot_of_things",
    pos := ↑UD.UPOS.VERB }

def Lexemes.naprodam : Lexeme :=
  { id := "naprodam", languageId := "bulg1262", parameterId := "sell_a_lot", pos := ↑UD.UPOS.VERB }

def Lexemes.ponaprodam : Lexeme :=
  { id := "ponaprodam", languageId := "bulg1262", parameterId := "sell_a_little",
    pos := ↑UD.UPOS.VERB }

def Lexemes.narazprodam : Lexeme :=
  { id := "narazprodam", languageId := "bulg1262", parameterId := "sell_a_lot_to_the_end",
    pos := ↑UD.UPOS.VERB }

def Lexemes.iznaprodam : Lexeme :=
  { id := "iznaprodam", languageId := "bulg1262", parameterId := "completely_sell_a_lot",
    pos := ↑UD.UPOS.VERB }

def Lexemes.izponaprodam : Lexeme :=
  { id := "izponaprodam", languageId := "bulg1262",
    parameterId := "sell_completely_a_lot_of_things_one_by_one_or_little_by_litt",
    pos := ↑UD.UPOS.VERB }

def Lexemes.izporazprodam : Lexeme :=
  { id := "izporazprodam", languageId := "bulg1262",
    parameterId := "sell_in_excess_a_lot_of_things_one_by_one_or_little_by_littl",
    pos := ↑UD.UPOS.VERB }

def Lexemes.izpopreprodam : Lexeme :=
  { id := "izpopreprodam", languageId := "bulg1262",
    parameterId := "completely_sell_again_one_by_one", pos := ↑UD.UPOS.VERB }

def Lexemes.porazprodam : Lexeme :=
  { id := "porazprodam", languageId := "bulg1262", parameterId := "sell_almost_everything",
    pos := ↑UD.UPOS.VERB }

def Lexemes.poizprodam : Lexeme :=
  { id := "poizprodam", languageId := "bulg1262", parameterId := "sell_almost_completely",
    pos := ↑UD.UPOS.VERB }

def Lexemes.poprodam : Lexeme :=
  { id := "poprodam", languageId := "bulg1262", parameterId := "sell_a_little_bit",
    pos := ↑UD.UPOS.VERB }

def Lexemes.poprodavam : Lexeme :=
  { id := "poprodavam", languageId := "bulg1262", parameterId := "sell_a_little_bit_for_a_while",
    pos := ↑UD.UPOS.VERB }

def Lexemes.zaizponareda : Lexeme :=
  { id := "zaizponareda", languageId := "bulg1262", parameterId := "start_arranging",
    pos := ↑UD.UPOS.VERB }

def Lexemes.zapeja : Lexeme :=
  { id := "zapeja", languageId := "bulg1262", parameterId := "start_singing", pos := ↑UD.UPOS.VERB }

def Lexemes.doprodam : Lexeme :=
  { id := "doprodam", languageId := "bulg1262", parameterId := "finish_selling",
    pos := ↑UD.UPOS.VERB }

def Lexemes.dopreprodam : Lexeme :=
  { id := "dopreprodam", languageId := "bulg1262", parameterId := "finish_selling_again",
    pos := ↑UD.UPOS.VERB }

def Lexemes.dorazpreprodam : Lexeme :=
  { id := "dorazpreprodam", languageId := "bulg1262",
    parameterId := "finish_selling_again_to_the_very_end", pos := ↑UD.UPOS.VERB }

def Lexemes.doprerazprodam : Lexeme :=
  { id := "doprerazprodam", languageId := "bulg1262",
    parameterId := "finish_selling_again_to_the_very_end", pos := ↑UD.UPOS.VERB }

def Lexemes.doizporazpreprodam : Lexeme :=
  { id := "doizporazpreprodam", languageId := "bulg1262",
    parameterId := "finish_re_selling_everything_to_the_end", pos := ↑UD.UPOS.VERB }

def Lexemes.podoizrazprodam : Lexeme :=
  { id := "podoizrazprodam", languageId := "bulg1262",
    parameterId := "almost_finish_reselling_to_the_end", pos := ↑UD.UPOS.VERB }

def Lexemes.zadoizponarazpreprodam : Lexeme :=
  { id := "zadoizponarazpreprodam", languageId := "bulg1262",
    parameterId := "start_to_finish_re_selling_everything_to_the_end", pos := ↑UD.UPOS.VERB }

def Lexemes.dopeja : Lexeme :=
  { id := "dopeja", languageId := "bulg1262", parameterId := "finish_singing",
    pos := ↑UD.UPOS.VERB }

def Lexemes.popeja : Lexeme :=
  { id := "popeja", languageId := "bulg1262", parameterId := "sing_for_a_while",
    pos := ↑UD.UPOS.VERB }

def Lexemes.poigraja : Lexeme :=
  { id := "poigraja", languageId := "bulg1262", parameterId := "play_for_a_while",
    pos := ↑UD.UPOS.VERB }

def Lexemes.izprodam : Lexeme :=
  { id := "izprodam", languageId := "bulg1262", parameterId := "completely_sell",
    pos := ↑UD.UPOS.VERB }

def Lexemes.izpoprodam : Lexeme :=
  { id := "izpoprodam", languageId := "bulg1262", parameterId := "sell_completely_one_by_one",
    pos := ↑UD.UPOS.VERB }

def Lexemes.iznarazkaza : Lexeme :=
  { id := "iznarazkaza", languageId := "bulg1262", parameterId := "the_source_gives_no_translation",
    pos := ↑UD.UPOS.VERB }

def Lexemes.izporazkaza : Lexeme :=
  { id := "izporazkaza", languageId := "bulg1262", parameterId := "narrate_completely_one_by_one",
    pos := ↑UD.UPOS.VERB }

def Lexemes.izponarazkaza : Lexeme :=
  { id := "izponarazkaza", languageId := "bulg1262",
    parameterId := "narrate_completely_many_stories_one_by_one", pos := ↑UD.UPOS.VERB }

def Lexemes.zaizponarazkaza : Lexeme :=
  { id := "zaizponarazkaza", languageId := "bulg1262",
    parameterId := "start_narrating_many_stories_one_by_one", pos := ↑UD.UPOS.VERB }

def Lexemes.prerazprodam : Lexeme :=
  { id := "prerazprodam", languageId := "bulg1262",
    parameterId := "sell_get_back_and_then_sell_again_to_the_end", pos := ↑UD.UPOS.VERB }

def Lexemes.izpoproceta : Lexeme :=
  { id := "izpoproceta", languageId := "bulg1262",
    parameterId := "read_through_completely_little_by_little", pos := ↑UD.UPOS.VERB }

def Lexemes.pozapeja : Lexeme :=
  { id := "pozapeja", languageId := "bulg1262", parameterId := "start_singing_a_bit",
    pos := ↑UD.UPOS.VERB }

def Lexemes.izponareza : Lexeme :=
  { id := "izponareza", languageId := "bulg1262",
    parameterId := "cut_completely_into_many_pieces_little_by_little", pos := ↑UD.UPOS.VERB }

def Lexemes.napoprodam : Lexeme :=
  { id := "napoprodam", languageId := "bulg1262", parameterId := "the_source_gives_no_translation",
    pos := ↑UD.UPOS.VERB }

def Lexemes.razpoprodam : Lexeme :=
  { id := "razpoprodam", languageId := "bulg1262", parameterId := "the_source_gives_no_translation",
    pos := ↑UD.UPOS.VERB }

def Lexemes.prenarazdam : Lexeme :=
  { id := "prenarazdam", languageId := "bulg1262", parameterId := "the_source_gives_no_translation",
    pos := ↑UD.UPOS.VERB }

def Lexemes.poprenarazdam : Lexeme :=
  { id := "poprenarazdam", languageId := "bulg1262",
    parameterId := "the_source_gives_no_translation", pos := ↑UD.UPOS.VERB }

def Lexemes.naprerazdam : Lexeme :=
  { id := "naprerazdam", languageId := "bulg1262", parameterId := "the_source_gives_no_translation",
    pos := ↑UD.UPOS.VERB }

def Lexemes.ponarazkaza : Lexeme :=
  { id := "ponarazkaza", languageId := "bulg1262", parameterId := "tell_a_few_stories",
    pos := ↑UD.UPOS.VERB }

def Lexemes.izponaprerazkaza : Lexeme :=
  { id := "izponaprerazkaza", languageId := "bulg1262",
    parameterId := "narrate_again_many_stories_completely_little_by_little", pos := ↑UD.UPOS.VERB }

def f_1a : Form Cell :=
  { id := "istratkova2004_1a"
    lexeme := Lexemes.zapisa
    cell := prs_1sg
    form := "zapiša"
    morphs := ["za", "piša"]
    source := [
      ⟨"istratkova-2004", "(1a)"⟩
    ] }

def f_1a_ipf : Form Cell :=
  { id := "istratkova2004_1a_ipf"
    lexeme := Lexemes.zapisa
    cell := prs_1sg
    form := "zapisvam"
    morphs := ["za", "pis", "va", "m"]
    source := [
      ⟨"istratkova-2004", "(1a)"⟩
    ] }

def f_1b : Form Cell :=
  { id := "istratkova2004_1b"
    lexeme := Lexemes.napisa
    cell := prs_1sg
    form := "napiša"
    morphs := ["na", "piša"]
    source := [
      ⟨"istratkova-2004", "(1b)"⟩
    ] }

def f_1b_ipf : Form Cell :=
  { id := "istratkova2004_1b_ipf"
    lexeme := Lexemes.napisa
    cell := prs_1sg
    form := "napisvam"
    morphs := ["na", "pis", "va", "m"]
    source := [
      ⟨"istratkova-2004", "(1b)"⟩
    ] }

def f_1c : Form Cell :=
  { id := "istratkova2004_1c"
    lexeme := Lexemes.prepisa
    cell := prs_1sg
    form := "prepiša"
    morphs := ["pre", "piša"]
    source := [
      ⟨"istratkova-2004", "(1c)"⟩,
      ⟨"istratkova-2004", "(3g)"⟩
    ] }

def f_1c_ipf : Form Cell :=
  { id := "istratkova2004_1c_ipf"
    lexeme := Lexemes.prepisa
    cell := prs_1sg
    form := "prepisvam"
    morphs := ["pre", "pis", "va", "m"]
    source := [
      ⟨"istratkova-2004", "(1c)"⟩
    ] }

def f_1d : Form Cell :=
  { id := "istratkova2004_1d"
    lexeme := Lexemes.podpisa
    cell := prs_1sg
    form := "podpiša"
    morphs := ["pod", "piša"]
    source := [
      ⟨"istratkova-2004", "(1d)"⟩
    ] }

def f_1d_ipf : Form Cell :=
  { id := "istratkova2004_1d_ipf"
    lexeme := Lexemes.podpisa
    cell := prs_1sg
    form := "podpisvam"
    morphs := ["pod", "pis", "va", "m"]
    source := [
      ⟨"istratkova-2004", "(1d)"⟩
    ] }

def f_1e : Form Cell :=
  { id := "istratkova2004_1e"
    lexeme := Lexemes.doveda
    cell := prs_1sg
    form := "doveda"
    morphs := ["do", "veda"]
    source := [
      ⟨"istratkova-2004", "(1e)"⟩
    ] }

def f_1e_ipf : Form Cell :=
  { id := "istratkova2004_1e_ipf"
    lexeme := Lexemes.doveda
    cell := prs_1sg
    form := "doveždam"
    morphs := ["do", "vežd", "a", "m"]
    source := [
      ⟨"istratkova-2004", "(1e)"⟩
    ] }

def f_1f : Form Cell :=
  { id := "istratkova2004_1f"
    lexeme := Lexemes.zaveda
    cell := prs_1sg
    form := "zaveda"
    morphs := ["za", "veda"]
    source := [
      ⟨"istratkova-2004", "(1f)"⟩
    ] }

def f_1f_ipf : Form Cell :=
  { id := "istratkova2004_1f_ipf"
    lexeme := Lexemes.zaveda
    cell := prs_1sg
    form := "zaveždam"
    morphs := ["za", "vežd", "a", "m"]
    source := [
      ⟨"istratkova-2004", "(1f)"⟩
    ] }

def f_1g : Form Cell :=
  { id := "istratkova2004_1g"
    lexeme := Lexemes.izveda
    cell := prs_1sg
    form := "izveda"
    morphs := ["iz", "veda"]
    source := [
      ⟨"istratkova-2004", "(1g)"⟩
    ] }

def f_1g_ipf : Form Cell :=
  { id := "istratkova2004_1g_ipf"
    lexeme := Lexemes.izveda
    cell := prs_1sg
    form := "izveždam"
    morphs := ["iz", "vežd", "a", "m"]
    source := [
      ⟨"istratkova-2004", "(1g)"⟩
    ] }

def f_1h : Form Cell :=
  { id := "istratkova2004_1h"
    lexeme := Lexemes.vida
    cell := prs_1sg
    form := "vid'a"
    morphs := ["vid'a"]
    source := [
      ⟨"istratkova-2004", "(1h)"⟩
    ] }

def f_1h_ipf : Form Cell :=
  { id := "istratkova2004_1h_ipf"
    lexeme := Lexemes.vida
    cell := prs_1sg
    form := "viždam"
    morphs := ["vižd", "a", "m"]
    source := [
      ⟨"istratkova-2004", "(1h)"⟩
    ] }

def f_1i : Form Cell :=
  { id := "istratkova2004_1i"
    lexeme := Lexemes.zavida
    cell := prs_1sg
    form := "zavid'a"
    morphs := ["za", "vid'a"]
    source := [
      ⟨"istratkova-2004", "(1i)"⟩
    ] }

def f_1i_ipf : Form Cell :=
  { id := "istratkova2004_1i_ipf"
    lexeme := Lexemes.zavida
    cell := prs_1sg
    form := "zaviždam"
    morphs := ["za", "vižd", "a", "m"]
    source := [
      ⟨"istratkova-2004", "(1i)"⟩
    ] }

def f_1j : Form Cell :=
  { id := "istratkova2004_1j"
    lexeme := Lexemes.obuja
    cell := prs_1sg
    form := "obuja"
    morphs := ["obuja"]
    source := [
      ⟨"istratkova-2004", "(1j)"⟩
    ] }

def f_1j_ipf : Form Cell :=
  { id := "istratkova2004_1j_ipf"
    lexeme := Lexemes.obuja
    cell := prs_1sg
    form := "obuvam"
    morphs := ["obu", "va", "m"]
    source := [
      ⟨"istratkova-2004", "(1j)"⟩
    ] }

def f_1k : Form Cell :=
  { id := "istratkova2004_1k"
    lexeme := Lexemes.preobuja
    cell := prs_1sg
    form := "preobuja"
    morphs := ["pre", "obuja"]
    source := [
      ⟨"istratkova-2004", "(1k)"⟩
    ] }

def f_1k_ipf : Form Cell :=
  { id := "istratkova2004_1k_ipf"
    lexeme := Lexemes.preobuja
    cell := prs_1sg
    form := "preobuvam"
    morphs := ["pre", "obu", "va", "m"]
    source := [
      ⟨"istratkova-2004", "(1k)"⟩
    ] }

def f_2a : Form Cell :=
  { id := "istratkova2004_2a"
    lexeme := Lexemes.misla
    cell := prs_1sg
    form := "misl'a"
    morphs := ["misl'a"]
    source := [
      ⟨"istratkova-2004", "(2a)"⟩
    ] }

def f_2b : Form Cell :=
  { id := "istratkova2004_2b"
    lexeme := Lexemes.obicam
    cell := prs_1sg
    form := "običam"
    morphs := ["običam"]
    source := [
      ⟨"istratkova-2004", "(2b)"⟩
    ] }

def f_2c : Form Cell :=
  { id := "istratkova2004_2c"
    lexeme := Lexemes.znam
    cell := prs_1sg
    form := "znam"
    morphs := ["znam"]
    source := [
      ⟨"istratkova-2004", "(2c)"⟩
    ] }

def f_2d : Form Cell :=
  { id := "istratkova2004_2d"
    lexeme := Lexemes.blesta
    cell := prs_1sg
    form := "blest'a"
    morphs := ["blest'a"]
    source := [
      ⟨"istratkova-2004", "(2d)"⟩
    ] }

def f_2e : Form Cell :=
  { id := "istratkova2004_2e"
    lexeme := Lexemes.spa
    cell := prs_1sg
    form := "sp'a"
    morphs := ["sp'a"]
    source := [
      ⟨"istratkova-2004", "(2e)"⟩
    ] }

def f_2f : Form Cell :=
  { id := "istratkova2004_2f"
    lexeme := Lexemes.pisa
    cell := prs_1sg
    form := "piša"
    morphs := ["piša"]
    source := [
      ⟨"istratkova-2004", "(2f)"⟩
    ] }

def f_2g : Form Cell :=
  { id := "istratkova2004_2g"
    lexeme := Lexemes.ziveja
    cell := prs_1sg
    form := "živeja"
    morphs := ["živeja"]
    source := [
      ⟨"istratkova-2004", "(2g)"⟩
    ] }

def f_2h : Form Cell :=
  { id := "istratkova2004_2h"
    lexeme := Lexemes.ceta
    cell := prs_1sg
    form := "četa"
    morphs := ["četa"]
    source := [
      ⟨"istratkova-2004", "(2h)"⟩
    ] }

def f_3a : Form Cell :=
  { id := "istratkova2004_3a"
    lexeme := Lexemes.izmisla
    cell := prs_1sg
    form := "izmisl'a"
    morphs := ["iz", "misl'a"]
    source := [
      ⟨"istratkova-2004", "(3a)"⟩
    ] }

def f_3a_ipf : Form Cell :=
  { id := "istratkova2004_3a_ipf"
    lexeme := Lexemes.izmisla
    cell := prs_1sg
    form := "izmisl'am"
    morphs := ["iz", "misl'", "a", "m"]
    source := [
      ⟨"istratkova-2004", "(3a)"⟩
    ] }

def f_3b : Form Cell :=
  { id := "istratkova2004_3b"
    lexeme := Lexemes.zaobicam
    cell := prs_1sg
    form := "zaobičam"
    morphs := ["za", "običam"]
    source := [
      ⟨"istratkova-2004", "(3b)"⟩
    ] }

def f_3b_ipf : Form Cell :=
  { id := "istratkova2004_3b_ipf"
    lexeme := Lexemes.zaobicam
    cell := prs_1sg
    form := "zaobičvam"
    morphs := ["za", "obič", "va", "m"]
    source := [
      ⟨"istratkova-2004", "(3b)"⟩
    ] }

def f_3c : Form Cell :=
  { id := "istratkova2004_3c"
    lexeme := Lexemes.poznam
    cell := prs_1sg
    form := "poznam"
    morphs := ["po", "znam"]
    source := [
      ⟨"istratkova-2004", "(3c)"⟩
    ] }

def f_3c_ipf : Form Cell :=
  { id := "istratkova2004_3c_ipf"
    lexeme := Lexemes.poznam
    cell := prs_1sg
    form := "poznavam"
    morphs := ["po", "zna", "va", "m"]
    source := [
      ⟨"istratkova-2004", "(3c)"⟩
    ] }

def f_3d : Form Cell :=
  { id := "istratkova2004_3d"
    lexeme := Lexemes.zablesta
    cell := prs_1sg
    form := "zablest'a"
    morphs := ["za", "blest'a"]
    source := [
      ⟨"istratkova-2004", "(3d)"⟩
    ] }

def f_3d_ipf : Form Cell :=
  { id := "istratkova2004_3d_ipf"
    lexeme := Lexemes.zablesta
    cell := prs_1sg
    form := "zablet'avam"
    morphs := ["za", "blet'", "ava", "m"]
    source := [
      ⟨"istratkova-2004", "(3d)"⟩
    ] }

def f_3e : Form Cell :=
  { id := "istratkova2004_3e"
    lexeme := Lexemes.blesna
    cell := prs_1sg
    form := "blesna"
    morphs := ["bles", "na"]
    source := [
      ⟨"istratkova-2004", "(3e)"⟩
    ] }

def f_3e_ipf : Form Cell :=
  { id := "istratkova2004_3e_ipf"
    lexeme := Lexemes.blesna
    cell := prs_1sg
    form := "blesvam"
    morphs := ["bles", "va", "m"]
    source := [
      ⟨"istratkova-2004", "(3e)"⟩
    ] }

def f_3f : Form Cell :=
  { id := "istratkova2004_3f"
    lexeme := Lexemes.zaspa
    cell := prs_1sg
    form := "zasp'a"
    morphs := ["za", "sp'a"]
    source := [
      ⟨"istratkova-2004", "(3f)"⟩
    ] }

def f_3f_ipf : Form Cell :=
  { id := "istratkova2004_3f_ipf"
    lexeme := Lexemes.zaspa
    cell := prs_1sg
    form := "zaspivam"
    morphs := ["za", "spi", "va", "m"]
    source := [
      ⟨"istratkova-2004", "(3f)"⟩
    ] }

def f_3h : Form Cell :=
  { id := "istratkova2004_3h"
    lexeme := Lexemes.doziveja
    cell := prs_1sg
    form := "doživeja"
    morphs := ["do", "živeja"]
    source := [
      ⟨"istratkova-2004", "(3h)"⟩
    ] }

def f_3h_ipf : Form Cell :=
  { id := "istratkova2004_3h_ipf"
    lexeme := Lexemes.doziveja
    cell := prs_1sg
    form := "doživ'avam"
    morphs := ["do", "živ'", "ava", "m"]
    source := [
      ⟨"istratkova-2004", "(3h)"⟩
    ] }

def f_3i : Form Cell :=
  { id := "istratkova2004_3i"
    lexeme := Lexemes.proceta
    cell := prs_1sg
    form := "pročeta"
    morphs := ["pro", "četa"]
    source := [
      ⟨"istratkova-2004", "(3i)"⟩
    ] }

def f_3i_ipf : Form Cell :=
  { id := "istratkova2004_3i_ipf"
    lexeme := Lexemes.proceta
    cell := prs_1sg
    form := "pročitam"
    morphs := ["pro", "čit", "a", "m"]
    source := [
      ⟨"istratkova-2004", "(3i)"⟩
    ] }

def f_4a : Form Cell :=
  { id := "istratkova2004_4a"
    lexeme := Lexemes.kupa
    cell := prs_1sg
    form := "kup'a"
    morphs := ["kup'a"]
    source := [
      ⟨"istratkova-2004", "(4a)"⟩
    ] }

def f_4a_ipf : Form Cell :=
  { id := "istratkova2004_4a_ipf"
    lexeme := Lexemes.kupa
    cell := prs_1sg
    form := "kupuvam"
    morphs := ["kup", "uva", "m"]
    source := [
      ⟨"istratkova-2004", "(4a)"⟩
    ] }

def f_4b : Form Cell :=
  { id := "istratkova2004_4b"
    lexeme := Lexemes.dam
    cell := prs_1sg
    form := "dam"
    morphs := ["dam"]
    source := [
      ⟨"istratkova-2004", "(4b)"⟩
    ] }

def f_4b_ipf : Form Cell :=
  { id := "istratkova2004_4b_ipf"
    lexeme := Lexemes.dam
    cell := prs_1sg
    form := "davam"
    morphs := ["da", "va", "m"]
    source := [
      ⟨"istratkova-2004", "(4b)"⟩
    ] }

def f_5a : Form Cell :=
  { id := "istratkova2004_5a"
    lexeme := Lexemes.izkupa
    cell := prs_1sg
    form := "izkup'a"
    morphs := ["iz", "kup'a"]
    source := [
      ⟨"istratkova-2004", "(5a)"⟩
    ] }

def f_5a_ipf : Form Cell :=
  { id := "istratkova2004_5a_ipf"
    lexeme := Lexemes.izkupa
    cell := prs_1sg
    form := "izkupuvam"
    morphs := ["iz", "kup", "uva", "m"]
    source := [
      ⟨"istratkova-2004", "(5a)"⟩
    ] }

def f_5b : Form Cell :=
  { id := "istratkova2004_5b"
    lexeme := Lexemes.prodam
    cell := prs_1sg
    form := "prodam"
    morphs := ["pro", "dam"]
    source := [
      ⟨"istratkova-2004", "(5b)"⟩
    ] }

def f_5b_ipf : Form Cell :=
  { id := "istratkova2004_5b_ipf"
    lexeme := Lexemes.prodam
    cell := prs_1sg
    form := "prodavam"
    morphs := ["pro", "da", "va", "m"]
    source := [
      ⟨"istratkova-2004", "(5b)"⟩
    ] }

def f_6a : Form Cell :=
  { id := "istratkova2004_6a"
    lexeme := Lexemes.zavisa
    cell := prs_1sg
    form := "zavis'a"
    morphs := ["za", "vis'a"]
    source := [
      ⟨"istratkova-2004", "(6a)"⟩
    ] }

def f_6a_alt : Form Cell :=
  { id := "istratkova2004_6a_alt"
    lexeme := Lexemes.zavisa
    cell := prs_1sg
    form := "zavis'avam"
    morphs := ["za", "vis'a", "va", "m"]
    judgment := .ungrammatical
    source := [
      ⟨"istratkova-2004", "(6a)"⟩
    ] }

def f_6a_base : Form Cell :=
  { id := "istratkova2004_6a_base"
    lexeme := Lexemes.visa
    cell := prs_1sg
    form := "vis'a"
    morphs := ["vis'a"]
    source := [
      ⟨"istratkova-2004", "(6a)"⟩
    ] }

def f_6b : Form Cell :=
  { id := "istratkova2004_6b"
    lexeme := Lexemes.podleza
    cell := prs_1sg
    form := "podleža"
    morphs := ["pod", "leža"]
    source := [
      ⟨"istratkova-2004", "(6b)"⟩
    ] }

def f_6b_alt : Form Cell :=
  { id := "istratkova2004_6b_alt"
    lexeme := Lexemes.podleza
    cell := prs_1sg
    form := "podležavam"
    morphs := ["pod", "leža", "va", "m"]
    judgment := .ungrammatical
    source := [
      ⟨"istratkova-2004", "(6b)"⟩
    ] }

def f_6b_base : Form Cell :=
  { id := "istratkova2004_6b_base"
    lexeme := Lexemes.leza
    cell := prs_1sg
    form := "leža"
    morphs := ["leža"]
    source := [
      ⟨"istratkova-2004", "(6b)"⟩
    ] }

def f_6c : Form Cell :=
  { id := "istratkova2004_6c"
    lexeme := Lexemes.predcuvstvam
    cell := prs_1sg
    form := "predčuvstvam"
    morphs := ["pred", "čuvstvam"]
    source := [
      ⟨"istratkova-2004", "(6c)"⟩
    ] }

def f_6c_alt : Form Cell :=
  { id := "istratkova2004_6c_alt"
    lexeme := Lexemes.predcuvstvam
    cell := prs_1sg
    form := "predčuvstvavam"
    morphs := ["pred", "čuvstva", "va", "m"]
    judgment := .ungrammatical
    source := [
      ⟨"istratkova-2004", "(6c)"⟩
    ] }

def f_6c_base : Form Cell :=
  { id := "istratkova2004_6c_base"
    lexeme := Lexemes.cuvstvam
    cell := prs_1sg
    form := "čuvstvam"
    morphs := ["čuvstvam"]
    source := [
      ⟨"istratkova-2004", "(6c)"⟩
    ] }

def f_6d : Form Cell :=
  { id := "istratkova2004_6d"
    lexeme := Lexemes.predsestvam
    cell := prs_1sg
    form := "predšestvam"
    morphs := ["pred", "šestvam"]
    source := [
      ⟨"istratkova-2004", "(6d)"⟩
    ] }

def f_6d_alt : Form Cell :=
  { id := "istratkova2004_6d_alt"
    lexeme := Lexemes.predsestvam
    cell := prs_1sg
    form := "predšestvavam"
    morphs := ["pred", "šestva", "va", "m"]
    judgment := .ungrammatical
    source := [
      ⟨"istratkova-2004", "(6d)"⟩
    ] }

def f_6d_base : Form Cell :=
  { id := "istratkova2004_6d_base"
    lexeme := Lexemes.sestvam
    cell := prs_1sg
    form := "šestvam"
    morphs := ["šestvam"]
    source := [
      ⟨"istratkova-2004", "(6d)"⟩
    ] }

def f_6e : Form Cell :=
  { id := "istratkova2004_6e"
    lexeme := Lexemes.predstoja
    cell := prs_1sg
    form := "predstoja"
    morphs := ["pred", "stoja"]
    source := [
      ⟨"istratkova-2004", "(6e)"⟩
    ] }

def f_6e_alt : Form Cell :=
  { id := "istratkova2004_6e_alt"
    lexeme := Lexemes.predstoja
    cell := prs_1sg
    form := "predstojavam"
    morphs := ["pred", "stoja", "va", "m"]
    judgment := .ungrammatical
    source := [
      ⟨"istratkova-2004", "(6e)"⟩
    ] }

def f_6e_base : Form Cell :=
  { id := "istratkova2004_6e_base"
    lexeme := Lexemes.stoja
    cell := prs_1sg
    form := "stoja"
    morphs := ["stoja"]
    source := [
      ⟨"istratkova-2004", "(6e)"⟩
    ] }

def f_6f : Form Cell :=
  { id := "istratkova2004_6f"
    lexeme := Lexemes.otstoja
    cell := prs_1sg
    form := "otstoja"
    morphs := ["ot", "stoja"]
    source := [
      ⟨"istratkova-2004", "(6f)"⟩
    ] }

def f_6f_alt : Form Cell :=
  { id := "istratkova2004_6f_alt"
    lexeme := Lexemes.otstoja
    cell := prs_1sg
    form := "otstojavam"
    morphs := ["ot", "stoja", "va", "m"]
    judgment := .ungrammatical
    source := [
      ⟨"istratkova-2004", "(6f)"⟩
    ] }

def f_7 : Form Cell :=
  { id := "istratkova2004_7"
    lexeme := Lexemes.otstoja_2
    cell := prs_1sg
    form := "otstoja"
    morphs := ["ot", "stoja"]
    source := [
      ⟨"istratkova-2004", "(7)"⟩
    ] }

def f_7_ipf : Form Cell :=
  { id := "istratkova2004_7_ipf"
    lexeme := Lexemes.otstoja_2
    cell := prs_1sg
    form := "otstojavam"
    morphs := ["ot", "stoja", "va", "m"]
    source := [
      ⟨"istratkova-2004", "(7)"⟩
    ] }

def f_11 : Form Cell :=
  { id := "istratkova2004_11"
    lexeme := Lexemes.izponarazprodam
    cell := prs_1sg
    form := "izponarazprodam"
    morphs := ["iz", "po", "na", "raz", "pro", "dam"]
    source := [
      ⟨"istratkova-2004", "(11)"⟩
    ] }

def f_12a : Form Cell :=
  { id := "istratkova2004_12a"
    lexeme := Lexemes.izkaza
    cell := prs_1sg
    form := "izkaža"
    morphs := ["iz", "kaža"]
    source := [
      ⟨"istratkova-2004", "(12)"⟩
    ] }

def f_12b : Form Cell :=
  { id := "istratkova2004_12b"
    lexeme := Lexemes.razkaza
    cell := prs_1sg
    form := "razkaža"
    morphs := ["raz", "kaža"]
    source := [
      ⟨"istratkova-2004", "(12)"⟩
    ] }

def f_12c : Form Cell :=
  { id := "istratkova2004_12c"
    lexeme := Lexemes.izdam
    cell := prs_1sg
    form := "izdam"
    morphs := ["iz", "dam"]
    source := [
      ⟨"istratkova-2004", "(12)"⟩
    ] }

def f_12d : Form Cell :=
  { id := "istratkova2004_12d"
    lexeme := Lexemes.razdam
    cell := prs_1sg
    form := "razdam"
    morphs := ["raz", "dam"]
    source := [
      ⟨"istratkova-2004", "(12)"⟩
    ] }

def f_13a : Form Cell :=
  { id := "istratkova2004_13a"
    lexeme := Lexemes.izrazkaza
    cell := prs_1sg
    form := "izrazkaža"
    morphs := ["iz", "raz", "kaža"]
    source := [
      ⟨"istratkova-2004", "(13)"⟩
    ] }

def f_13b : Form Cell :=
  { id := "istratkova2004_13b"
    lexeme := Lexemes.izrazdam
    cell := prs_1sg
    form := "izrazdam"
    morphs := ["iz", "raz", "dam"]
    source := [
      ⟨"istratkova-2004", "(13)"⟩
    ] }

def f_14a : Form Cell :=
  { id := "istratkova2004_14a"
    lexeme := Lexemes.nadam
    cell := prs_1sg
    form := "nadam"
    morphs := ["na", "dam"]
    source := [
      ⟨"istratkova-2004", "(14a)"⟩,
      ⟨"istratkova-2004", "(20a)"⟩
    ] }

def f_14b : Form Cell :=
  { id := "istratkova2004_14b"
    lexeme := Lexemes.nakaza
    cell := prs_1sg
    form := "nakaža"
    morphs := ["na", "kaža"]
    source := [
      ⟨"istratkova-2004", "(14b)"⟩
    ] }

def f_15 : Form Cell :=
  { id := "istratkova2004_15"
    lexeme := Lexemes.izponakaza
    cell := prs_1sg
    form := "izponakaža"
    morphs := ["iz", "po", "na", "kaža"]
    source := [
      ⟨"istratkova-2004", "(15)"⟩
    ] }

def f_18a : Form Cell :=
  { id := "istratkova2004_18a"
    lexeme := Lexemes.razpreprodam
    cell := prs_1sg
    form := "razpreprodam"
    morphs := ["raz", "pre", "pro", "dam"]
    source := [
      ⟨"istratkova-2004", "(18a)"⟩,
      ⟨"istratkova-2004", "(30a)"⟩
    ] }

def f_18b : Form Cell :=
  { id := "istratkova2004_18b"
    lexeme := Lexemes.popreprodam
    cell := prs_1sg
    form := "popreprodam"
    morphs := ["po", "pre", "pro", "dam"]
    source := [
      ⟨"istratkova-2004", "(18b)"⟩
    ] }

def f_18c : Form Cell :=
  { id := "istratkova2004_18c"
    lexeme := Lexemes.napreprodam
    cell := prs_1sg
    form := "napreprodam"
    morphs := ["na", "pre", "pro", "dam"]
    judgment := .marginal
    source := [
      ⟨"istratkova-2004", "(18c)"⟩
    ] }

def f_18d : Form Cell :=
  { id := "istratkova2004_18d"
    lexeme := Lexemes.naprerazkaza
    cell := prs_1sg
    form := "naprerazkaža"
    morphs := ["na", "pre", "raz", "kaža"]
    judgment := .ungrammatical
    source := [
      ⟨"istratkova-2004", "(18d)"⟩
    ] }

def f_18e : Form Cell :=
  { id := "istratkova2004_18e"
    lexeme := Lexemes.izpreprodam
    cell := prs_1sg
    form := "izpreprodam"
    morphs := ["iz", "pre", "pro", "dam"]
    judgment := .marginal
    source := [
      ⟨"istratkova-2004", "(18e)"⟩
    ] }

def f_18f : Form Cell :=
  { id := "istratkova2004_18f"
    lexeme := Lexemes.izprerazkaza
    cell := prs_1sg
    form := "izprerazkaža"
    morphs := ["iz", "pre", "raz", "kaža"]
    judgment := .marginal
    source := [
      ⟨"istratkova-2004", "(18f)"⟩
    ] }

def f_19a : Form Cell :=
  { id := "istratkova2004_19a"
    lexeme := Lexemes.porazpreprodam
    cell := prs_1sg
    form := "porazpreprodam"
    morphs := ["po", "raz", "pre", "pro", "dam"]
    source := [
      ⟨"istratkova-2004", "(19a)"⟩
    ] }

def f_19b : Form Cell :=
  { id := "istratkova2004_19b"
    lexeme := Lexemes.izrazpreprodam
    cell := prs_1sg
    form := "izrazpreprodam"
    morphs := ["iz", "raz", "pre", "pro", "dam"]
    source := [
      ⟨"istratkova-2004", "(19b)"⟩
    ] }

def f_20b : Form Cell :=
  { id := "istratkova2004_20b"
    lexeme := Lexemes.napreprodam_2
    cell := prs_1sg
    form := "napreprodam"
    morphs := ["na", "pre", "pro", "dam"]
    source := [
      ⟨"istratkova-2004", "(20b)"⟩
    ] }

def f_20c : Form Cell :=
  { id := "istratkova2004_20c"
    lexeme := Lexemes.naprodam
    cell := prs_1sg
    form := "naprodam"
    morphs := ["na", "pro", "dam"]
    source := [
      ⟨"istratkova-2004", "(20c)"⟩
    ] }

def f_20d : Form Cell :=
  { id := "istratkova2004_20d"
    lexeme := Lexemes.ponaprodam
    cell := prs_1sg
    form := "ponaprodam"
    morphs := ["po", "na", "pro", "dam"]
    source := [
      ⟨"istratkova-2004", "(20d)"⟩
    ] }

def f_20e : Form Cell :=
  { id := "istratkova2004_20e"
    lexeme := Lexemes.narazprodam
    cell := prs_1sg
    form := "narazprodam"
    morphs := ["na", "raz", "pro", "dam"]
    judgment := .ungrammatical
    source := [
      ⟨"istratkova-2004", "(20e)"⟩
    ] }

def f_20f : Form Cell :=
  { id := "istratkova2004_20f"
    lexeme := Lexemes.iznaprodam
    cell := prs_1sg
    form := "iznaprodam"
    morphs := ["iz", "na", "pro", "dam"]
    judgment := .ungrammatical
    source := [
      ⟨"istratkova-2004", "(20f)"⟩,
      ⟨"istratkova-2004", "(27a)"⟩
    ] }

def f_21a : Form Cell :=
  { id := "istratkova2004_21a"
    lexeme := Lexemes.izponaprodam
    cell := prs_1sg
    form := "izponaprodam"
    morphs := ["iz", "po", "na", "pro", "dam"]
    source := [
      ⟨"istratkova-2004", "(21a)"⟩,
      ⟨"istratkova-2004", "(27d)"⟩
    ] }

def f_21b : Form Cell :=
  { id := "istratkova2004_21b"
    lexeme := Lexemes.izporazprodam
    cell := prs_1sg
    form := "izporazprodam"
    morphs := ["iz", "po", "raz", "pro", "dam"]
    source := [
      ⟨"istratkova-2004", "(21b)"⟩
    ] }

def f_21c : Form Cell :=
  { id := "istratkova2004_21c"
    lexeme := Lexemes.izpopreprodam
    cell := prs_1sg
    form := "izpopreprodam"
    morphs := ["iz", "po", "pre", "pro", "dam"]
    source := [
      ⟨"istratkova-2004", "(21c)"⟩
    ] }

def f_23b : Form Cell :=
  { id := "istratkova2004_23b"
    lexeme := Lexemes.porazprodam
    cell := prs_1sg
    form := "porazprodam"
    morphs := ["po", "raz", "pro", "dam"]
    source := [
      ⟨"istratkova-2004", "(23b)"⟩
    ] }

def f_23d : Form Cell :=
  { id := "istratkova2004_23d"
    lexeme := Lexemes.poizprodam
    cell := prs_1sg
    form := "poizprodam"
    morphs := ["po", "iz", "pro", "dam"]
    source := [
      ⟨"istratkova-2004", "(23d)"⟩
    ] }

def f_23e : Form Cell :=
  { id := "istratkova2004_23e"
    lexeme := Lexemes.poprodam
    cell := prs_1sg
    form := "poprodam"
    morphs := ["po", "pro", "dam"]
    source := [
      ⟨"istratkova-2004", "(23e)"⟩
    ] }

def f_23f : Form Cell :=
  { id := "istratkova2004_23f"
    lexeme := Lexemes.poprodavam
    cell := prs_1sg
    form := "poprodavam"
    morphs := ["po", "pro", "da", "va", "m"]
    source := [
      ⟨"istratkova-2004", "(23f)"⟩
    ] }

def f_24a : Form Cell :=
  { id := "istratkova2004_24a"
    lexeme := Lexemes.zaizponareda
    cell := prs_1sg
    form := "zaizponared'a"
    morphs := ["za", "iz", "po", "nared'a"]
    judgment := .ungrammatical
    source := [
      ⟨"istratkova-2004", "(24a)"⟩
    ] }

def f_24a_alt : Form Cell :=
  { id := "istratkova2004_24a_alt"
    lexeme := Lexemes.zaizponareda
    cell := prs_1sg
    form := "zaizponareždam"
    morphs := ["za", "iz", "po", "narežd", "a", "m"]
    source := [
      ⟨"istratkova-2004", "(24a)"⟩
    ] }

def f_24b : Form Cell :=
  { id := "istratkova2004_24b"
    lexeme := Lexemes.zapeja
    cell := prs_1sg
    form := "zapeja"
    morphs := ["za", "peja"]
    source := [
      ⟨"istratkova-2004", "(24b)"⟩
    ] }

def f_24b_ipf : Form Cell :=
  { id := "istratkova2004_24b_ipf"
    lexeme := Lexemes.zapeja
    cell := prs_1sg
    form := "zap'avam"
    morphs := ["za", "p'a", "va", "m"]
    source := [
      ⟨"istratkova-2004", "(24b)"⟩
    ] }

def f_25a : Form Cell :=
  { id := "istratkova2004_25a"
    lexeme := Lexemes.doprodam
    cell := prs_1sg
    form := "doprodam"
    morphs := ["do", "pro", "dam"]
    source := [
      ⟨"istratkova-2004", "(25a)"⟩
    ] }

def f_25b : Form Cell :=
  { id := "istratkova2004_25b"
    lexeme := Lexemes.dopreprodam
    cell := prs_1sg
    form := "dopreprodam"
    morphs := ["do", "pre", "pro", "dam"]
    source := [
      ⟨"istratkova-2004", "(25b)"⟩
    ] }

def f_25b_alt : Form Cell :=
  { id := "istratkova2004_25b_alt"
    lexeme := Lexemes.dopreprodam
    cell := prs_1sg
    form := "predoprodam"
    morphs := ["pre", "do", "prodam"]
    judgment := .ungrammatical
    source := [
      ⟨"istratkova-2004", "(25b)"⟩
    ] }

def f_25c1 : Form Cell :=
  { id := "istratkova2004_25c1"
    lexeme := Lexemes.dorazpreprodam
    cell := prs_1sg
    form := "dorazpreprodam"
    morphs := ["do", "raz", "pre", "pro", "dam"]
    source := [
      ⟨"istratkova-2004", "(25c)"⟩
    ] }

def f_25c2 : Form Cell :=
  { id := "istratkova2004_25c2"
    lexeme := Lexemes.doprerazprodam
    cell := prs_1sg
    form := "doprerazprodam"
    morphs := ["do", "pre", "raz", "pro", "dam"]
    source := [
      ⟨"istratkova-2004", "(25c)"⟩
    ] }

def f_25d : Form Cell :=
  { id := "istratkova2004_25d"
    lexeme := Lexemes.doizporazpreprodam
    cell := prs_1sg
    form := "doizporazpreprodam"
    morphs := ["do", "iz", "po", "raz", "pre", "pro", "dam"]
    source := [
      ⟨"istratkova-2004", "(25d)"⟩
    ] }

def f_25e : Form Cell :=
  { id := "istratkova2004_25e"
    lexeme := Lexemes.podoizrazprodam
    cell := prs_1sg
    form := "podoizrazprodam"
    morphs := ["po", "do", "iz", "raz", "pro", "dam"]
    source := [
      ⟨"istratkova-2004", "(25e)"⟩
    ] }

def f_25f : Form Cell :=
  { id := "istratkova2004_25f"
    lexeme := Lexemes.zadoizponarazpreprodam
    cell := prs_1sg
    form := "zadoizponarazpreprodam"
    morphs := ["za", "do", "iz", "po", "na", "raz", "pre", "pro", "dam"]
    judgment := .marginal
    source := [
      ⟨"istratkova-2004", "(25f)"⟩
    ] }

def f_25g : Form Cell :=
  { id := "istratkova2004_25g"
    lexeme := Lexemes.dopeja
    cell := prs_1sg
    form := "dopeja"
    morphs := ["do", "peja"]
    source := [
      ⟨"istratkova-2004", "(25g)"⟩
    ] }

def f_25g_ipf : Form Cell :=
  { id := "istratkova2004_25g_ipf"
    lexeme := Lexemes.dopeja
    cell := prs_1sg
    form := "dop'avam"
    morphs := ["do", "p'a", "va", "m"]
    source := [
      ⟨"istratkova-2004", "(25g)"⟩
    ] }

def f_26a : Form Cell :=
  { id := "istratkova2004_26a"
    lexeme := Lexemes.popeja
    cell := prs_1sg
    form := "popeja"
    morphs := ["po", "peja"]
    source := [
      ⟨"istratkova-2004", "(26a)"⟩
    ] }

def f_26a_ipf : Form Cell :=
  { id := "istratkova2004_26a_ipf"
    lexeme := Lexemes.popeja
    cell := prs_1sg
    form := "pop'avam"
    morphs := ["po", "p'a", "va", "m"]
    source := [
      ⟨"istratkova-2004", "(26a)"⟩
    ] }

def f_26b : Form Cell :=
  { id := "istratkova2004_26b"
    lexeme := Lexemes.poigraja
    cell := prs_1sg
    form := "poigraja"
    morphs := ["po", "igraja"]
    source := [
      ⟨"istratkova-2004", "(26b)"⟩
    ] }

def f_26b_ipf : Form Cell :=
  { id := "istratkova2004_26b_ipf"
    lexeme := Lexemes.poigraja
    cell := prs_1sg
    form := "poigravam"
    morphs := ["po", "igra", "va", "m"]
    source := [
      ⟨"istratkova-2004", "(26b)"⟩
    ] }

def f_27b : Form Cell :=
  { id := "istratkova2004_27b"
    lexeme := Lexemes.izprodam
    cell := prs_1sg
    form := "izprodam"
    morphs := ["iz", "pro", "dam"]
    judgment := .marginal
    source := [
      ⟨"istratkova-2004", "(27b)"⟩,
      ⟨"istratkova-2004", "(22c)"⟩
    ] }

def f_27c : Form Cell :=
  { id := "istratkova2004_27c"
    lexeme := Lexemes.izpoprodam
    cell := prs_1sg
    form := "izpoprodam"
    morphs := ["iz", "po", "pro", "dam"]
    source := [
      ⟨"istratkova-2004", "(27c)"⟩,
      ⟨"istratkova-2004", "(22c)"⟩
    ] }

def f_28a : Form Cell :=
  { id := "istratkova2004_28a"
    lexeme := Lexemes.iznarazkaza
    cell := prs_1sg
    form := "iznarazkaža"
    morphs := ["iz", "na", "raz", "kaža"]
    judgment := .ungrammatical
    source := [
      ⟨"istratkova-2004", "(28a)"⟩
    ] }

def f_28b : Form Cell :=
  { id := "istratkova2004_28b"
    lexeme := Lexemes.izrazkaza
    cell := prs_1sg
    form := "izrazkaža"
    morphs := ["iz", "raz", "kaža"]
    judgment := .marginal
    source := [
      ⟨"istratkova-2004", "(28b)"⟩
    ] }

def f_28c : Form Cell :=
  { id := "istratkova2004_28c"
    lexeme := Lexemes.izporazkaza
    cell := prs_1sg
    form := "izporazkaža"
    morphs := ["iz", "po", "raz", "kaža"]
    source := [
      ⟨"istratkova-2004", "(28c)"⟩
    ] }

def f_28d : Form Cell :=
  { id := "istratkova2004_28d"
    lexeme := Lexemes.izponarazkaza
    cell := prs_1sg
    form := "izponarazkaža"
    morphs := ["iz", "po", "na", "raz", "kaža"]
    source := [
      ⟨"istratkova-2004", "(28d)"⟩
    ] }

def f_29 : Form Cell :=
  { id := "istratkova2004_29"
    lexeme := Lexemes.zaizponarazkaza
    cell := prs_1sg
    form := "zaizponarazkaža"
    morphs := ["za", "iz", "po", "na", "raz", "kaža"]
    source := [
      ⟨"istratkova-2004", "(29)"⟩
    ] }

def f_29_alt : Form Cell :=
  { id := "istratkova2004_29_alt"
    lexeme := Lexemes.zaizponarazkaza
    cell := prs_1sg
    form := "zaponarazkaža"
    morphs := ["za", "po", "na", "raz", "kaža"]
    judgment := .ungrammatical
    source := [
      ⟨"istratkova-2004", "(29)"⟩
    ] }

def f_30b : Form Cell :=
  { id := "istratkova2004_30b"
    lexeme := Lexemes.prerazprodam
    cell := prs_1sg
    form := "prerazprodam"
    morphs := ["pre", "raz", "pro", "dam"]
    judgment := .marginal
    source := [
      ⟨"istratkova-2004", "(30b)"⟩
    ] }

def f_33a : Form Cell :=
  { id := "istratkova2004_33a"
    lexeme := Lexemes.izpoproceta
    cell := prs_1sg
    form := "izpopročeta"
    morphs := ["iz", "po", "pro", "četa"]
    source := [
      ⟨"istratkova-2004", "(33a)"⟩
    ] }

def f_34a : Form Cell :=
  { id := "istratkova2004_34a"
    lexeme := Lexemes.pozapeja
    cell := prs_1sg
    form := "pozapeja"
    morphs := ["po", "za", "peja"]
    source := [
      ⟨"istratkova-2004", "(34a)"⟩
    ] }

def f_35a : Form Cell :=
  { id := "istratkova2004_35a"
    lexeme := Lexemes.izponareza
    cell := prs_1sg
    form := "izponareža"
    morphs := ["iz", "po", "na", "reža"]
    source := [
      ⟨"istratkova-2004", "(35a)"⟩
    ] }

def t3_na_po_pro_dam : Form Cell :=
  { id := "istratkova2004_t3_na_po_pro_dam"
    lexeme := Lexemes.napoprodam
    cell := prs_1sg
    form := "napoprodam"
    morphs := ["na", "po", "pro", "dam"]
    judgment := .ungrammatical
    source := [
      ⟨"istratkova-2004", "Table 3"⟩
    ] }

def t3_raz_po_pro_dam : Form Cell :=
  { id := "istratkova2004_t3_raz_po_pro_dam"
    lexeme := Lexemes.razpoprodam
    cell := prs_1sg
    form := "razpoprodam"
    morphs := ["raz", "po", "pro", "dam"]
    judgment := .ungrammatical
    source := [
      ⟨"istratkova-2004", "Table 3"⟩
    ] }

def t2_pre_na_raz_dam : Form Cell :=
  { id := "istratkova2004_t2_pre_na_raz_dam"
    lexeme := Lexemes.prenarazdam
    cell := prs_1sg
    form := "prenarazdam"
    morphs := ["pre", "na", "raz", "dam"]
    judgment := .ungrammatical
    source := [
      ⟨"istratkova-2004", "Table 2"⟩
    ] }

def t2_po_pre_na_raz_dam : Form Cell :=
  { id := "istratkova2004_t2_po_pre_na_raz_dam"
    lexeme := Lexemes.poprenarazdam
    cell := prs_1sg
    form := "poprenarazdam"
    morphs := ["po", "pre", "na", "raz", "dam"]
    judgment := .ungrammatical
    source := [
      ⟨"istratkova-2004", "Table 2"⟩
    ] }

def t2_na_pre_raz_dam : Form Cell :=
  { id := "istratkova2004_t2_na_pre_raz_dam"
    lexeme := Lexemes.naprerazdam
    cell := prs_1sg
    form := "naprerazdam"
    morphs := ["na", "pre", "raz", "dam"]
    judgment := .ungrammatical
    source := [
      ⟨"istratkova-2004", "Table 2"⟩
    ] }

def t1_po_na_raz_kazha : Form Cell :=
  { id := "istratkova2004_t1_po_na_raz_kazha"
    lexeme := Lexemes.ponarazkaza
    cell := prs_1sg
    form := "ponarazkaža"
    morphs := ["po", "na", "raz", "kaža"]
    source := [
      ⟨"istratkova-2004", "Table 1"⟩
    ] }

def t1_iz_po_na_pre_raz_kazha : Form Cell :=
  { id := "istratkova2004_t1_iz_po_na_pre_raz_kazha"
    lexeme := Lexemes.izponaprerazkaza
    cell := prs_1sg
    form := "izponaprerazkaža"
    morphs := ["iz", "po", "na", "pre", "raz", "kaža"]
    source := [
      ⟨"istratkova-2004", "Table 1"⟩
    ] }

/-- The source's analysis of a form, its parse rather than data. -/
structure Analysis where
  /-- The form analysed. -/
  form : Form Cell
  /-- The `Stack` column, the classes the paper gives the prefixes of the stack. -/
  stack : Option String := none
  /-- The `Class` column, the paper's class of a simplex verb. -/
  class_ : Option String := none
  /-- The `Prefix` column, the paper's class of a single prefix. -/
  prefix_ : Option String := none
  deriving DecidableEq, Repr

def f_1a.analysis : Analysis :=
  { form := f_1a }

def f_1a_ipf.analysis : Analysis :=
  { form := f_1a_ipf }

def f_1b.analysis : Analysis :=
  { form := f_1b }

def f_1b_ipf.analysis : Analysis :=
  { form := f_1b_ipf }

def f_1c.analysis : Analysis :=
  { form := f_1c }

def f_1c_ipf.analysis : Analysis :=
  { form := f_1c_ipf }

def f_1d.analysis : Analysis :=
  { form := f_1d }

def f_1d_ipf.analysis : Analysis :=
  { form := f_1d_ipf }

def f_1e.analysis : Analysis :=
  { form := f_1e }

def f_1e_ipf.analysis : Analysis :=
  { form := f_1e_ipf }

def f_1f.analysis : Analysis :=
  { form := f_1f }

def f_1f_ipf.analysis : Analysis :=
  { form := f_1f_ipf }

def f_1g.analysis : Analysis :=
  { form := f_1g }

def f_1g_ipf.analysis : Analysis :=
  { form := f_1g_ipf }

def f_1h.analysis : Analysis :=
  { form := f_1h }

def f_1h_ipf.analysis : Analysis :=
  { form := f_1h_ipf }

def f_1i.analysis : Analysis :=
  { form := f_1i }

def f_1i_ipf.analysis : Analysis :=
  { form := f_1i_ipf }

def f_1j.analysis : Analysis :=
  { form := f_1j }

def f_1j_ipf.analysis : Analysis :=
  { form := f_1j_ipf }

def f_1k.analysis : Analysis :=
  { form := f_1k }

def f_1k_ipf.analysis : Analysis :=
  { form := f_1k_ipf }

def f_2a.analysis : Analysis :=
  { form := f_2a,
    class_ := some "simplex homogeneous verb, no perfective counterpart" }

def f_2b.analysis : Analysis :=
  { form := f_2b,
    class_ := some "simplex homogeneous verb, no perfective counterpart" }

def f_2c.analysis : Analysis :=
  { form := f_2c,
    class_ := some "simplex homogeneous verb, no perfective counterpart" }

def f_2d.analysis : Analysis :=
  { form := f_2d,
    class_ := some "simplex homogeneous verb, no perfective counterpart" }

def f_2e.analysis : Analysis :=
  { form := f_2e,
    class_ := some "simplex homogeneous verb, no perfective counterpart" }

def f_2f.analysis : Analysis :=
  { form := f_2f,
    class_ := some "simplex homogeneous verb, no perfective counterpart" }

def f_2g.analysis : Analysis :=
  { form := f_2g,
    class_ := some "simplex homogeneous verb, no perfective counterpart" }

def f_2h.analysis : Analysis :=
  { form := f_2h,
    class_ := some "simplex homogeneous verb, no perfective counterpart" }

def f_3a.analysis : Analysis :=
  { form := f_3a }

def f_3a_ipf.analysis : Analysis :=
  { form := f_3a_ipf }

def f_3b.analysis : Analysis :=
  { form := f_3b }

def f_3b_ipf.analysis : Analysis :=
  { form := f_3b_ipf }

def f_3c.analysis : Analysis :=
  { form := f_3c }

def f_3c_ipf.analysis : Analysis :=
  { form := f_3c_ipf }

def f_3d.analysis : Analysis :=
  { form := f_3d }

def f_3d_ipf.analysis : Analysis :=
  { form := f_3d_ipf }

def f_3e.analysis : Analysis :=
  { form := f_3e }

def f_3e_ipf.analysis : Analysis :=
  { form := f_3e_ipf }

def f_3f.analysis : Analysis :=
  { form := f_3f }

def f_3f_ipf.analysis : Analysis :=
  { form := f_3f_ipf }

def f_3h.analysis : Analysis :=
  { form := f_3h }

def f_3h_ipf.analysis : Analysis :=
  { form := f_3h_ipf }

def f_3i.analysis : Analysis :=
  { form := f_3i }

def f_3i_ipf.analysis : Analysis :=
  { form := f_3i_ipf }

def f_4a.analysis : Analysis :=
  { form := f_4a,
    class_ := some "simplex quantized verb" }

def f_4a_ipf.analysis : Analysis :=
  { form := f_4a_ipf }

def f_4b.analysis : Analysis :=
  { form := f_4b,
    class_ := some "simplex quantized verb" }

def f_4b_ipf.analysis : Analysis :=
  { form := f_4b_ipf }

def f_5a.analysis : Analysis :=
  { form := f_5a }

def f_5a_ipf.analysis : Analysis :=
  { form := f_5a_ipf }

def f_5b.analysis : Analysis :=
  { form := f_5b }

def f_5b_ipf.analysis : Analysis :=
  { form := f_5b_ipf }

def f_6a.analysis : Analysis :=
  { form := f_6a }

def f_6a_alt.analysis : Analysis :=
  { form := f_6a_alt }

def f_6a_base.analysis : Analysis :=
  { form := f_6a_base }

def f_6b.analysis : Analysis :=
  { form := f_6b }

def f_6b_alt.analysis : Analysis :=
  { form := f_6b_alt }

def f_6b_base.analysis : Analysis :=
  { form := f_6b_base }

def f_6c.analysis : Analysis :=
  { form := f_6c }

def f_6c_alt.analysis : Analysis :=
  { form := f_6c_alt }

def f_6c_base.analysis : Analysis :=
  { form := f_6c_base }

def f_6d.analysis : Analysis :=
  { form := f_6d }

def f_6d_alt.analysis : Analysis :=
  { form := f_6d_alt }

def f_6d_base.analysis : Analysis :=
  { form := f_6d_base }

def f_6e.analysis : Analysis :=
  { form := f_6e }

def f_6e_alt.analysis : Analysis :=
  { form := f_6e_alt }

def f_6e_base.analysis : Analysis :=
  { form := f_6e_base }

def f_6f.analysis : Analysis :=
  { form := f_6f }

def f_6f_alt.analysis : Analysis :=
  { form := f_6f_alt }

def f_7.analysis : Analysis :=
  { form := f_7 }

def f_7_ipf.analysis : Analysis :=
  { form := f_7_ipf }

def f_11.analysis : Analysis :=
  { form := f_11,
    stack := some "completive iz-, distributive po-, cumulative na-, excessive raz-, lexical pro-" }

def f_12a.analysis : Analysis :=
  { form := f_12a,
    prefix_ := some "lexical iz-" }

def f_12b.analysis : Analysis :=
  { form := f_12b,
    prefix_ := some "lexical raz-" }

def f_12c.analysis : Analysis :=
  { form := f_12c,
    prefix_ := some "lexical iz-" }

def f_12d.analysis : Analysis :=
  { form := f_12d,
    prefix_ := some "lexical raz-" }

def f_13a.analysis : Analysis :=
  { form := f_13a,
    stack := some "completive iz- outside lexical raz-" }

def f_13b.analysis : Analysis :=
  { form := f_13b,
    stack := some "completive iz- outside lexical raz-" }

def f_14a.analysis : Analysis :=
  { form := f_14a,
    prefix_ := some "cumulative na- on a simplex" }

def f_14b.analysis : Analysis :=
  { form := f_14b,
    prefix_ := some "lexical or cumulative na-" }

def f_15.analysis : Analysis :=
  { form := f_15,
    stack := some "innermost prefix read as lexical out of context" }

def f_18a.analysis : Analysis :=
  { form := f_18a,
    stack := some "excessive raz-, repetitive pre-, lexical pro-" }

def f_18b.analysis : Analysis :=
  { form := f_18b,
    stack := some "attenuative po-, repetitive pre-, lexical pro-" }

def f_18c.analysis : Analysis :=
  { form := f_18c,
    stack := some "cumulative na-, repetitive pre-, lexical pro-" }

def f_18d.analysis : Analysis :=
  { form := f_18d,
    stack := some "cumulative na-, repetitive pre-, lexical raz-" }

def f_18e.analysis : Analysis :=
  { form := f_18e,
    stack := some "completive iz-, repetitive pre-, lexical pro-" }

def f_18f.analysis : Analysis :=
  { form := f_18f,
    stack := some "completive iz-, repetitive pre-, lexical raz-" }

def f_19a.analysis : Analysis :=
  { form := f_19a,
    stack := some "attenuative po- over excessive raz- over repetitive pre-" }

def f_19b.analysis : Analysis :=
  { form := f_19b,
    stack := some "completive iz- over excessive raz- over repetitive pre-" }

def f_20b.analysis : Analysis :=
  { form := f_20b,
    stack := some "cumulative na- over repetitive pre-" }

def f_20c.analysis : Analysis :=
  { form := f_20c,
    stack := some "cumulative na- over lexical pro-" }

def f_20d.analysis : Analysis :=
  { form := f_20d,
    stack := some "attenuative po- modifies cumulative na-" }

def f_20e.analysis : Analysis :=
  { form := f_20e,
    stack := some "cumulative na- over excessive raz-" }

def f_20f.analysis : Analysis :=
  { form := f_20f,
    stack := some "completive iz- directly over cumulative na-" }

def f_21a.analysis : Analysis :=
  { form := f_21a,
    stack := some "completive iz-, distributive po-, cumulative na-, lexical pro-" }

def f_21b.analysis : Analysis :=
  { form := f_21b,
    stack := some "completive iz-, distributive po-, excessive raz-, lexical pro-" }

def f_21c.analysis : Analysis :=
  { form := f_21c,
    stack := some "completive iz-, distributive po-, repetitive pre-, lexical pro-" }

def f_23b.analysis : Analysis :=
  { form := f_23b,
    stack := some "attenuative po- lowers the intensity of excessive raz-" }

def f_23d.analysis : Analysis :=
  { form := f_23d,
    stack := some "attenuative po- over completive iz-" }

def f_23e.analysis : Analysis :=
  { form := f_23e,
    stack := some "attenuative po- over lexical pro-" }

def f_23f.analysis : Analysis :=
  { form := f_23f }

def f_24a.analysis : Analysis :=
  { form := f_24a,
    stack := some "high inceptive za- outside completive iz-" }

def f_24a_alt.analysis : Analysis :=
  { form := f_24a_alt }

def f_24b.analysis : Analysis :=
  { form := f_24b,
    stack := some "low inceptive za- on a homogeneous simplex" }

def f_24b_ipf.analysis : Analysis :=
  { form := f_24b_ipf }

def f_25a.analysis : Analysis :=
  { form := f_25a,
    stack := some "terminative do- over lexical pro-" }

def f_25b.analysis : Analysis :=
  { form := f_25b,
    stack := some "terminative do- over repetitive pre-" }

def f_25b_alt.analysis : Analysis :=
  { form := f_25b_alt }

def f_25c1.analysis : Analysis :=
  { form := f_25c1,
    stack := some "terminative do-, excessive raz-, repetitive pre-" }

def f_25c2.analysis : Analysis :=
  { form := f_25c2,
    stack := some "terminative do-, repetitive pre-, excessive raz-" }

def f_25d.analysis : Analysis :=
  { form := f_25d,
    stack := some "six prefixes in hierarchy order" }

def f_25e.analysis : Analysis :=
  { form := f_25e,
    stack := some "attenuative po- outermost, over terminative do-" }

def f_25f.analysis : Analysis :=
  { form := f_25f,
    stack := some "seven prefixes" }

def f_25g.analysis : Analysis :=
  { form := f_25g,
    stack := some "low terminative do- on a homogeneous simplex" }

def f_25g_ipf.analysis : Analysis :=
  { form := f_25g_ipf }

def f_26a.analysis : Analysis :=
  { form := f_26a,
    stack := some "delimitative po- on a simplex atelic verb; no stacking" }

def f_26a_ipf.analysis : Analysis :=
  { form := f_26a_ipf }

def f_26b.analysis : Analysis :=
  { form := f_26b,
    stack := some "delimitative po-" }

def f_26b_ipf.analysis : Analysis :=
  { form := f_26b_ipf }

def f_27b.analysis : Analysis :=
  { form := f_27b,
    stack := some "completive iz- over lexical pro-" }

def f_27c.analysis : Analysis :=
  { form := f_27c,
    stack := some "completive iz-, distributive po-, lexical pro-" }

def f_28a.analysis : Analysis :=
  { form := f_28a,
    stack := some "completive iz- directly over cumulative na-" }

def f_28b.analysis : Analysis :=
  { form := f_28b,
    stack := some "completive iz- over lexical raz-" }

def f_28c.analysis : Analysis :=
  { form := f_28c,
    stack := some "completive iz-, distributive po-, lexical raz-" }

def f_28d.analysis : Analysis :=
  { form := f_28d,
    stack := some "completive iz-, distributive po-, cumulative na-, lexical raz-" }

def f_29.analysis : Analysis :=
  { form := f_29,
    stack := some "inceptive za- requires completive iz- inside" }

def f_29_alt.analysis : Analysis :=
  { form := f_29_alt }

def f_30b.analysis : Analysis :=
  { form := f_30b,
    stack := some "repetitive pre- over excessive raz-" }

def f_33a.analysis : Analysis :=
  { form := f_33a,
    stack := some "superlexicals above AspP over lexical pro- in Q1" }

def f_34a.analysis : Analysis :=
  { form := f_34a,
    stack := some "attenuative po- over low inceptive za- in Q2" }

def f_35a.analysis : Analysis :=
  { form := f_35a,
    stack := some "completive iz-, distributive po- over low cumulative na- in Q2" }

def t3_na_po_pro_dam.analysis : Analysis :=
  { form := t3_na_po_pro_dam,
    stack := some "cumulative na- over po-" }

def t3_raz_po_pro_dam.analysis : Analysis :=
  { form := t3_raz_po_pro_dam,
    stack := some "excessive raz- over po-" }

def t2_pre_na_raz_dam.analysis : Analysis :=
  { form := t2_pre_na_raz_dam,
    stack := some "repetitive pre- over cumulative na-" }

def t2_po_pre_na_raz_dam.analysis : Analysis :=
  { form := t2_po_pre_na_raz_dam,
    stack := some "repetitive pre- over cumulative na-" }

def t2_na_pre_raz_dam.analysis : Analysis :=
  { form := t2_na_pre_raz_dam,
    stack := some "cumulative na- over repetitive pre-" }

def t1_po_na_raz_kazha.analysis : Analysis :=
  { form := t1_po_na_raz_kazha,
    stack := some "attenuative po- over cumulative na- over lexical raz-" }

def t1_iz_po_na_pre_raz_kazha.analysis : Analysis :=
  { form := t1_iz_po_na_pre_raz_kazha,
    stack := some "completive iz-, distributive po-, cumulative na-, repetitive pre-, lexical raz-" }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.zapisa, Lexemes.napisa, Lexemes.prepisa, Lexemes.podpisa,
  Lexemes.doveda, Lexemes.zaveda, Lexemes.izveda, Lexemes.vida, Lexemes.zavida, Lexemes.obuja,
  Lexemes.preobuja, Lexemes.misla, Lexemes.obicam, Lexemes.znam, Lexemes.blesta, Lexemes.spa,
  Lexemes.pisa, Lexemes.ziveja, Lexemes.ceta, Lexemes.izmisla, Lexemes.zaobicam, Lexemes.poznam,
  Lexemes.zablesta, Lexemes.blesna, Lexemes.zaspa, Lexemes.doziveja, Lexemes.proceta, Lexemes.kupa,
  Lexemes.dam, Lexemes.izkupa, Lexemes.prodam, Lexemes.zavisa, Lexemes.visa, Lexemes.podleza,
  Lexemes.leza, Lexemes.predcuvstvam, Lexemes.cuvstvam, Lexemes.predsestvam, Lexemes.sestvam,
  Lexemes.predstoja, Lexemes.stoja, Lexemes.otstoja, Lexemes.otstoja_2, Lexemes.izponarazprodam,
  Lexemes.izkaza, Lexemes.razkaza, Lexemes.izdam, Lexemes.razdam, Lexemes.izrazkaza,
  Lexemes.izrazdam, Lexemes.nadam, Lexemes.nakaza, Lexemes.izponakaza, Lexemes.razpreprodam,
  Lexemes.popreprodam, Lexemes.napreprodam, Lexemes.naprerazkaza, Lexemes.izpreprodam,
  Lexemes.izprerazkaza, Lexemes.porazpreprodam, Lexemes.izrazpreprodam, Lexemes.napreprodam_2,
  Lexemes.naprodam, Lexemes.ponaprodam, Lexemes.narazprodam, Lexemes.iznaprodam,
  Lexemes.izponaprodam, Lexemes.izporazprodam, Lexemes.izpopreprodam, Lexemes.porazprodam,
  Lexemes.poizprodam, Lexemes.poprodam, Lexemes.poprodavam, Lexemes.zaizponareda, Lexemes.zapeja,
  Lexemes.doprodam, Lexemes.dopreprodam, Lexemes.dorazpreprodam, Lexemes.doprerazprodam,
  Lexemes.doizporazpreprodam, Lexemes.podoizrazprodam, Lexemes.zadoizponarazpreprodam,
  Lexemes.dopeja, Lexemes.popeja, Lexemes.poigraja, Lexemes.izprodam, Lexemes.izpoprodam,
  Lexemes.iznarazkaza, Lexemes.izporazkaza, Lexemes.izponarazkaza, Lexemes.zaizponarazkaza,
  Lexemes.prerazprodam, Lexemes.izpoproceta, Lexemes.pozapeja, Lexemes.izponareza,
  Lexemes.napoprodam, Lexemes.razpoprodam, Lexemes.prenarazdam, Lexemes.poprenarazdam,
  Lexemes.naprerazdam, Lexemes.ponarazkaza, Lexemes.izponaprerazkaza]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [f_1a, f_1a_ipf, f_1b, f_1b_ipf, f_1c, f_1c_ipf, f_1d, f_1d_ipf, f_1e,
  f_1e_ipf, f_1f, f_1f_ipf, f_1g, f_1g_ipf, f_1h, f_1h_ipf, f_1i, f_1i_ipf, f_1j, f_1j_ipf, f_1k,
  f_1k_ipf, f_2a, f_2b, f_2c, f_2d, f_2e, f_2f, f_2g, f_2h, f_3a, f_3a_ipf, f_3b, f_3b_ipf, f_3c,
  f_3c_ipf, f_3d, f_3d_ipf, f_3e, f_3e_ipf, f_3f, f_3f_ipf, f_3h, f_3h_ipf, f_3i, f_3i_ipf, f_4a,
  f_4a_ipf, f_4b, f_4b_ipf, f_5a, f_5a_ipf, f_5b, f_5b_ipf, f_6a, f_6a_base, f_6b, f_6b_base, f_6c,
  f_6c_base, f_6d, f_6d_base, f_6e, f_6e_base, f_6f, f_7, f_7_ipf, f_11, f_12a, f_12b, f_12c, f_12d,
  f_13a, f_13b, f_14a, f_14b, f_15, f_18a, f_18b, f_19a, f_19b, f_20b, f_20c, f_20d, f_21a, f_21b,
  f_21c, f_23b, f_23d, f_23e, f_23f, f_24a_alt, f_24b, f_24b_ipf, f_25a, f_25b, f_25c1, f_25c2,
  f_25d, f_25e, f_25g, f_25g_ipf, f_26a, f_26a_ipf, f_26b, f_26b_ipf, f_27c, f_28c, f_28d, f_29,
  f_33a, f_34a, f_35a, t1_po_na_raz_kazha, t1_iz_po_na_pre_raz_kazha]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := [f_6a_alt, f_6b_alt, f_6c_alt, f_6d_alt, f_6e_alt, f_6f_alt, f_18c,
  f_18d, f_18e, f_18f, f_20e, f_20f, f_24a, f_25b_alt, f_25f, f_27b, f_28a, f_28b, f_29_alt, f_30b,
  t3_na_po_pro_dam, t3_raz_po_pro_dam, t2_pre_na_raz_dam, t2_po_pre_na_raz_dam, t2_na_pre_raz_dam]

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := [
  { id := "istratkova2004_r_1a_ipf_imperfective", form := f_1a, target := f_1a_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(1a)"⟩
    ] },
  { id := "istratkova2004_r_1b_ipf_imperfective", form := f_1b, target := f_1b_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(1b)"⟩
    ] },
  { id := "istratkova2004_r_1c_ipf_imperfective", form := f_1c, target := f_1c_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(1c)"⟩
    ] },
  { id := "istratkova2004_r_1d_ipf_imperfective", form := f_1d, target := f_1d_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(1d)"⟩
    ] },
  { id := "istratkova2004_r_1e_ipf_imperfective", form := f_1e, target := f_1e_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(1e)"⟩
    ] },
  { id := "istratkova2004_r_1f_ipf_imperfective", form := f_1f, target := f_1f_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(1f)"⟩
    ] },
  { id := "istratkova2004_r_1g_ipf_imperfective", form := f_1g, target := f_1g_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(1g)"⟩
    ] },
  { id := "istratkova2004_r_1h_ipf_imperfective", form := f_1h, target := f_1h_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(1h)"⟩
    ] },
  { id := "istratkova2004_r_1i_ipf_imperfective", form := f_1i, target := f_1i_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(1i)"⟩
    ] },
  { id := "istratkova2004_r_1j_ipf_imperfective", form := f_1j, target := f_1j_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(1j)"⟩
    ] },
  { id := "istratkova2004_r_1k_ipf_imperfective", form := f_1k, target := f_1k_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(1k)"⟩
    ] },
  { id := "istratkova2004_r_3a_ipf_imperfective", form := f_3a, target := f_3a_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(3a)"⟩
    ] },
  { id := "istratkova2004_r_3b_ipf_imperfective", form := f_3b, target := f_3b_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(3b)"⟩
    ] },
  { id := "istratkova2004_r_3c_ipf_imperfective", form := f_3c, target := f_3c_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(3c)"⟩
    ] },
  { id := "istratkova2004_r_3d_ipf_imperfective", form := f_3d, target := f_3d_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(3d)"⟩
    ] },
  { id := "istratkova2004_r_3e_ipf_imperfective", form := f_3e, target := f_3e_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(3e)"⟩
    ] },
  { id := "istratkova2004_r_3f_ipf_imperfective", form := f_3f, target := f_3f_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(3f)"⟩
    ] },
  { id := "istratkova2004_r_3h_ipf_imperfective", form := f_3h, target := f_3h_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(3h)"⟩
    ] },
  { id := "istratkova2004_r_3i_ipf_imperfective", form := f_3i, target := f_3i_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(3i)"⟩
    ] },
  { id := "istratkova2004_r_4a_ipf_imperfective", form := f_4a, target := f_4a_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(4a)"⟩
    ] },
  { id := "istratkova2004_r_4b_ipf_imperfective", form := f_4b, target := f_4b_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(4b)"⟩
    ] },
  { id := "istratkova2004_r_5a_ipf_imperfective", form := f_5a, target := f_5a_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(5a)"⟩
    ] },
  { id := "istratkova2004_r_5b_ipf_imperfective", form := f_5b, target := f_5b_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(5b)"⟩
    ] },
  { id := "istratkova2004_r_6a_alt_imperfective", form := f_6a, target := f_6a_alt,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(6a)"⟩
    ] },
  { id := "istratkova2004_r_6a_prefixation", form := f_6a_base, target := f_6a,
    relation := "prefixation", source := [
      ⟨"istratkova-2004", "(6a)"⟩
    ] },
  { id := "istratkova2004_r_6b_alt_imperfective", form := f_6b, target := f_6b_alt,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(6b)"⟩
    ] },
  { id := "istratkova2004_r_6b_prefixation", form := f_6b_base, target := f_6b,
    relation := "prefixation", source := [
      ⟨"istratkova-2004", "(6b)"⟩
    ] },
  { id := "istratkova2004_r_6c_alt_imperfective", form := f_6c, target := f_6c_alt,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(6c)"⟩
    ] },
  { id := "istratkova2004_r_6c_prefixation", form := f_6c_base, target := f_6c,
    relation := "prefixation", source := [
      ⟨"istratkova-2004", "(6c)"⟩
    ] },
  { id := "istratkova2004_r_6d_alt_imperfective", form := f_6d, target := f_6d_alt,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(6d)"⟩
    ] },
  { id := "istratkova2004_r_6d_prefixation", form := f_6d_base, target := f_6d,
    relation := "prefixation", source := [
      ⟨"istratkova-2004", "(6d)"⟩
    ] },
  { id := "istratkova2004_r_6e_alt_imperfective", form := f_6e, target := f_6e_alt,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(6e)"⟩
    ] },
  { id := "istratkova2004_r_6e_prefixation", form := f_6e_base, target := f_6e,
    relation := "prefixation", source := [
      ⟨"istratkova-2004", "(6e)"⟩
    ] },
  { id := "istratkova2004_r_6f_alt_imperfective", form := f_6f, target := f_6f_alt,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(6f)"⟩
    ] },
  { id := "istratkova2004_r_6f_prefixation", form := f_6e_base, target := f_6f,
    relation := "prefixation", source := [
      ⟨"istratkova-2004", "(6f)"⟩
    ] },
  { id := "istratkova2004_r_7_ipf_imperfective", form := f_7, target := f_7_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(7)"⟩
    ] },
  { id := "istratkova2004_r_24a_alt_imperfective", form := f_24a, target := f_24a_alt,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(24a)"⟩
    ] },
  { id := "istratkova2004_r_24b_ipf_imperfective", form := f_24b, target := f_24b_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(24b)"⟩
    ] },
  { id := "istratkova2004_r_25g_ipf_imperfective", form := f_25g, target := f_25g_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(25g)"⟩
    ] },
  { id := "istratkova2004_r_26a_ipf_imperfective", form := f_26a, target := f_26a_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(26a)"⟩
    ] },
  { id := "istratkova2004_r_26b_ipf_imperfective", form := f_26b, target := f_26b_ipf,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(26b)"⟩
    ] }]

/-- Every relation the sources assert, between the forms' analyses. -/
def analysisRelations : List (FormRelation Analysis) := [
  { id := "istratkova2004_r_1a_ipf_imperfective", form := f_1a.analysis,
    target := f_1a_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(1a)"⟩
    ] },
  { id := "istratkova2004_r_1b_ipf_imperfective", form := f_1b.analysis,
    target := f_1b_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(1b)"⟩
    ] },
  { id := "istratkova2004_r_1c_ipf_imperfective", form := f_1c.analysis,
    target := f_1c_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(1c)"⟩
    ] },
  { id := "istratkova2004_r_1d_ipf_imperfective", form := f_1d.analysis,
    target := f_1d_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(1d)"⟩
    ] },
  { id := "istratkova2004_r_1e_ipf_imperfective", form := f_1e.analysis,
    target := f_1e_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(1e)"⟩
    ] },
  { id := "istratkova2004_r_1f_ipf_imperfective", form := f_1f.analysis,
    target := f_1f_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(1f)"⟩
    ] },
  { id := "istratkova2004_r_1g_ipf_imperfective", form := f_1g.analysis,
    target := f_1g_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(1g)"⟩
    ] },
  { id := "istratkova2004_r_1h_ipf_imperfective", form := f_1h.analysis,
    target := f_1h_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(1h)"⟩
    ] },
  { id := "istratkova2004_r_1i_ipf_imperfective", form := f_1i.analysis,
    target := f_1i_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(1i)"⟩
    ] },
  { id := "istratkova2004_r_1j_ipf_imperfective", form := f_1j.analysis,
    target := f_1j_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(1j)"⟩
    ] },
  { id := "istratkova2004_r_1k_ipf_imperfective", form := f_1k.analysis,
    target := f_1k_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(1k)"⟩
    ] },
  { id := "istratkova2004_r_3a_ipf_imperfective", form := f_3a.analysis,
    target := f_3a_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(3a)"⟩
    ] },
  { id := "istratkova2004_r_3b_ipf_imperfective", form := f_3b.analysis,
    target := f_3b_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(3b)"⟩
    ] },
  { id := "istratkova2004_r_3c_ipf_imperfective", form := f_3c.analysis,
    target := f_3c_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(3c)"⟩
    ] },
  { id := "istratkova2004_r_3d_ipf_imperfective", form := f_3d.analysis,
    target := f_3d_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(3d)"⟩
    ] },
  { id := "istratkova2004_r_3e_ipf_imperfective", form := f_3e.analysis,
    target := f_3e_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(3e)"⟩
    ] },
  { id := "istratkova2004_r_3f_ipf_imperfective", form := f_3f.analysis,
    target := f_3f_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(3f)"⟩
    ] },
  { id := "istratkova2004_r_3h_ipf_imperfective", form := f_3h.analysis,
    target := f_3h_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(3h)"⟩
    ] },
  { id := "istratkova2004_r_3i_ipf_imperfective", form := f_3i.analysis,
    target := f_3i_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(3i)"⟩
    ] },
  { id := "istratkova2004_r_4a_ipf_imperfective", form := f_4a.analysis,
    target := f_4a_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(4a)"⟩
    ] },
  { id := "istratkova2004_r_4b_ipf_imperfective", form := f_4b.analysis,
    target := f_4b_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(4b)"⟩
    ] },
  { id := "istratkova2004_r_5a_ipf_imperfective", form := f_5a.analysis,
    target := f_5a_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(5a)"⟩
    ] },
  { id := "istratkova2004_r_5b_ipf_imperfective", form := f_5b.analysis,
    target := f_5b_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(5b)"⟩
    ] },
  { id := "istratkova2004_r_6a_alt_imperfective", form := f_6a.analysis,
    target := f_6a_alt.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(6a)"⟩
    ] },
  { id := "istratkova2004_r_6a_prefixation", form := f_6a_base.analysis, target := f_6a.analysis,
    relation := "prefixation", source := [
      ⟨"istratkova-2004", "(6a)"⟩
    ] },
  { id := "istratkova2004_r_6b_alt_imperfective", form := f_6b.analysis,
    target := f_6b_alt.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(6b)"⟩
    ] },
  { id := "istratkova2004_r_6b_prefixation", form := f_6b_base.analysis, target := f_6b.analysis,
    relation := "prefixation", source := [
      ⟨"istratkova-2004", "(6b)"⟩
    ] },
  { id := "istratkova2004_r_6c_alt_imperfective", form := f_6c.analysis,
    target := f_6c_alt.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(6c)"⟩
    ] },
  { id := "istratkova2004_r_6c_prefixation", form := f_6c_base.analysis, target := f_6c.analysis,
    relation := "prefixation", source := [
      ⟨"istratkova-2004", "(6c)"⟩
    ] },
  { id := "istratkova2004_r_6d_alt_imperfective", form := f_6d.analysis,
    target := f_6d_alt.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(6d)"⟩
    ] },
  { id := "istratkova2004_r_6d_prefixation", form := f_6d_base.analysis, target := f_6d.analysis,
    relation := "prefixation", source := [
      ⟨"istratkova-2004", "(6d)"⟩
    ] },
  { id := "istratkova2004_r_6e_alt_imperfective", form := f_6e.analysis,
    target := f_6e_alt.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(6e)"⟩
    ] },
  { id := "istratkova2004_r_6e_prefixation", form := f_6e_base.analysis, target := f_6e.analysis,
    relation := "prefixation", source := [
      ⟨"istratkova-2004", "(6e)"⟩
    ] },
  { id := "istratkova2004_r_6f_alt_imperfective", form := f_6f.analysis,
    target := f_6f_alt.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(6f)"⟩
    ] },
  { id := "istratkova2004_r_6f_prefixation", form := f_6e_base.analysis, target := f_6f.analysis,
    relation := "prefixation", source := [
      ⟨"istratkova-2004", "(6f)"⟩
    ] },
  { id := "istratkova2004_r_7_ipf_imperfective", form := f_7.analysis, target := f_7_ipf.analysis,
    relation := "imperfective", source := [
      ⟨"istratkova-2004", "(7)"⟩
    ] },
  { id := "istratkova2004_r_24a_alt_imperfective", form := f_24a.analysis,
    target := f_24a_alt.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(24a)"⟩
    ] },
  { id := "istratkova2004_r_24b_ipf_imperfective", form := f_24b.analysis,
    target := f_24b_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(24b)"⟩
    ] },
  { id := "istratkova2004_r_25g_ipf_imperfective", form := f_25g.analysis,
    target := f_25g_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(25g)"⟩
    ] },
  { id := "istratkova2004_r_26a_ipf_imperfective", form := f_26a.analysis,
    target := f_26a_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(26a)"⟩
    ] },
  { id := "istratkova2004_r_26b_ipf_imperfective", form := f_26b.analysis,
    target := f_26b_ipf.analysis, relation := "imperfective", source := [
      ⟨"istratkova-2004", "(26b)"⟩
    ] }]

/-- Every analysis of the data. -/
def analyses : List Analysis := [f_2a.analysis, f_2b.analysis, f_2c.analysis, f_2d.analysis,
  f_2e.analysis, f_2f.analysis, f_2g.analysis, f_2h.analysis, f_4a.analysis, f_4b.analysis,
  f_11.analysis, f_12a.analysis, f_12b.analysis, f_12c.analysis, f_12d.analysis, f_13a.analysis,
  f_13b.analysis, f_14a.analysis, f_14b.analysis, f_15.analysis, f_18a.analysis, f_18b.analysis,
  f_18c.analysis, f_18d.analysis, f_18e.analysis, f_18f.analysis, f_19a.analysis, f_19b.analysis,
  f_20b.analysis, f_20c.analysis, f_20d.analysis, f_20e.analysis, f_20f.analysis, f_21a.analysis,
  f_21b.analysis, f_21c.analysis, f_23b.analysis, f_23d.analysis, f_23e.analysis, f_24a.analysis,
  f_24b.analysis, f_25a.analysis, f_25b.analysis, f_25c1.analysis, f_25c2.analysis, f_25d.analysis,
  f_25e.analysis, f_25f.analysis, f_25g.analysis, f_26a.analysis, f_26b.analysis, f_27b.analysis,
  f_27c.analysis, f_28a.analysis, f_28b.analysis, f_28c.analysis, f_28d.analysis, f_29.analysis,
  f_30b.analysis, f_33a.analysis, f_34a.analysis, f_35a.analysis, t3_na_po_pro_dam.analysis,
  t3_raz_po_pro_dam.analysis, t2_pre_na_raz_dam.analysis, t2_po_pre_na_raz_dam.analysis,
  t2_na_pre_raz_dam.analysis, t1_po_na_raz_kazha.analysis, t1_iz_po_na_pre_raz_kazha.analysis]

end Istratkova2004.Forms
