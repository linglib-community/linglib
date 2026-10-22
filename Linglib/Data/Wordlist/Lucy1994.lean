module

public import Linglib.Data.Wordlist.Schema

/-!
# `Lucy1994`: word forms

Auto-generated from `Linglib/Data/Wordlist/Lucy1994.json` by `scripts/gen_wordlist.py`. Do not edit
by hand; edit the JSON and re-run the generator. Declarations live in `namespace Lucy1994.Wordlist`.
-/

@[expose] public section

namespace Lucy1994.Wordlist

open CLDF.Wordlist

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.afct : Lexeme :=
  { id := "afct", languageId := "yuca1254", parameterId := "AFCT" }

def Lexemes.root : Lexeme :=
  { id := "root", languageId := "yuca1254", parameterId := "ROOT" }

def Lexemes.caus : Lexeme :=
  { id := "caus", languageId := "yuca1254", parameterId := "CAUS" }

def Lexemes.pos : Lexeme :=
  { id := "pos", languageId := "yuca1254", parameterId := "POS" }

def Lexemes.jump : Lexeme :=
  { id := "jump", languageId := "yuca1254", parameterId := "jump" }

def Lexemes.jump_over : Lexeme :=
  { id := "jump_over", languageId := "yuca1254", parameterId := "jump-over" }

def Lexemes.write : Lexeme :=
  { id := "write", languageId := "yuca1254", parameterId := "write" }

def Lexemes.sweep : Lexeme :=
  { id := "sweep", languageId := "yuca1254", parameterId := "sweep" }

def Lexemes.smile : Lexeme :=
  { id := "smile", languageId := "yuca1254", parameterId := "smile" }

def Lexemes.weed : Lexeme :=
  { id := "weed", languageId := "yuca1254", parameterId := "weed" }

def Lexemes.carry : Lexeme :=
  { id := "carry", languageId := "yuca1254", parameterId := "carry" }

def Lexemes.carry_tr : Lexeme :=
  { id := "carry_tr", languageId := "yuca1254", parameterId := "carry-tr" }

def Lexemes.cut : Lexeme :=
  { id := "cut", languageId := "yuca1254", parameterId := "cut" }

def Lexemes.measure : Lexeme :=
  { id := "measure", languageId := "yuca1254", parameterId := "measure" }

def Lexemes.whip : Lexeme :=
  { id := "whip", languageId := "yuca1254", parameterId := "whip" }

def Lexemes.punch : Lexeme :=
  { id := "punch", languageId := "yuca1254", parameterId := "punch" }

def Lexemes.awaken : Lexeme :=
  { id := "awaken", languageId := "yuca1254", parameterId := "awaken" }

def Lexemes.wake_someone : Lexeme :=
  { id := "wake_someone", languageId := "yuca1254", parameterId := "wake-someone" }

def Lexemes.fall_asleep : Lexeme :=
  { id := "fall_asleep", languageId := "yuca1254", parameterId := "fall-asleep" }

def Lexemes.put_to_sleep : Lexeme :=
  { id := "put_to_sleep", languageId := "yuca1254", parameterId := "put-to-sleep" }

def Lexemes.be_born : Lexeme :=
  { id := "be_born", languageId := "yuca1254", parameterId := "be-born" }

def Lexemes.give_birth : Lexeme :=
  { id := "give_birth", languageId := "yuca1254", parameterId := "give-birth" }

def Lexemes.die : Lexeme :=
  { id := "die", languageId := "yuca1254", parameterId := "die" }

def Lexemes.kill : Lexeme :=
  { id := "kill", languageId := "yuca1254", parameterId := "kill" }

def Lexemes.forget : Lexeme :=
  { id := "forget", languageId := "yuca1254", parameterId := "forget" }

def Lexemes.distract : Lexeme :=
  { id := "distract", languageId := "yuca1254", parameterId := "distract" }

def Lexemes.remember : Lexeme :=
  { id := "remember", languageId := "yuca1254", parameterId := "remember" }

def Lexemes.remind : Lexeme :=
  { id := "remind", languageId := "yuca1254", parameterId := "remind" }

def Lexemes.begin_activity : Lexeme :=
  { id := "begin_activity", languageId := "yuca1254", parameterId := "begin-activity" }

def Lexemes.cause_to_begin : Lexeme :=
  { id := "cause_to_begin", languageId := "yuca1254", parameterId := "cause-to-begin" }

def Lexemes.stop : Lexeme :=
  { id := "stop", languageId := "yuca1254", parameterId := "stop" }

def Lexemes.cause_to_stop : Lexeme :=
  { id := "cause_to_stop", languageId := "yuca1254", parameterId := "cause-to-stop" }

def Lexemes.begin : Lexeme :=
  { id := "begin", languageId := "yuca1254", parameterId := "begin" }

def Lexemes.cause_to_start : Lexeme :=
  { id := "cause_to_start", languageId := "yuca1254", parameterId := "cause-to-start" }

def Lexemes.cease : Lexeme :=
  { id := "cease", languageId := "yuca1254", parameterId := "cease" }

def Lexemes.revoke : Lexeme :=
  { id := "revoke", languageId := "yuca1254", parameterId := "revoke" }

def Lexemes.rest : Lexeme :=
  { id := "rest", languageId := "yuca1254", parameterId := "rest" }

def Lexemes.rest_tr : Lexeme :=
  { id := "rest_tr", languageId := "yuca1254", parameterId := "rest-tr" }

def Lexemes.remain : Lexeme :=
  { id := "remain", languageId := "yuca1254", parameterId := "remain" }

def Lexemes.abandon : Lexeme :=
  { id := "abandon", languageId := "yuca1254", parameterId := "abandon" }

def Lexemes.pass_by : Lexeme :=
  { id := "pass_by", languageId := "yuca1254", parameterId := "pass-by" }

def Lexemes.transport : Lexeme :=
  { id := "transport", languageId := "yuca1254", parameterId := "transport" }

def Lexemes.move : Lexeme :=
  { id := "move", languageId := "yuca1254", parameterId := "move" }

def Lexemes.cause_to_move : Lexeme :=
  { id := "cause_to_move", languageId := "yuca1254", parameterId := "cause-to-move" }

def Lexemes.go : Lexeme :=
  { id := "go", languageId := "yuca1254", parameterId := "go" }

def Lexemes.take : Lexeme :=
  { id := "take", languageId := "yuca1254", parameterId := "take" }

def Lexemes.come : Lexeme :=
  { id := "come", languageId := "yuca1254", parameterId := "come" }

def Lexemes.bring : Lexeme :=
  { id := "bring", languageId := "yuca1254", parameterId := "bring" }

def Lexemes.arrive_here : Lexeme :=
  { id := "arrive_here", languageId := "yuca1254", parameterId := "arrive-here" }

def Lexemes.bring_here : Lexeme :=
  { id := "bring_here", languageId := "yuca1254", parameterId := "bring-here" }

def Lexemes.enter : Lexeme :=
  { id := "enter", languageId := "yuca1254", parameterId := "enter" }

def Lexemes.move_in : Lexeme :=
  { id := "move_in", languageId := "yuca1254", parameterId := "move-in" }

def Lexemes.fall : Lexeme :=
  { id := "fall", languageId := "yuca1254", parameterId := "fall" }

def Lexemes.fell : Lexeme :=
  { id := "fell", languageId := "yuca1254", parameterId := "fell" }

def Lexemes.rise : Lexeme :=
  { id := "rise", languageId := "yuca1254", parameterId := "rise" }

def Lexemes.raise : Lexeme :=
  { id := "raise", languageId := "yuca1254", parameterId := "raise" }

def Lexemes.ascend : Lexeme :=
  { id := "ascend", languageId := "yuca1254", parameterId := "ascend" }

def Lexemes.raise_2 : Lexeme :=
  { id := "raise_2", languageId := "yuca1254", parameterId := "raise-2" }

def Lexemes.bend : Lexeme :=
  { id := "bend", languageId := "yuca1254", parameterId := "bend" }

def Lexemes.bend_tr : Lexeme :=
  { id := "bend_tr", languageId := "yuca1254", parameterId := "bend-tr" }

def Lexemes.become_bent : Lexeme :=
  { id := "become_bent", languageId := "yuca1254", parameterId := "become-bent" }

def Lexemes.lie_down : Lexeme :=
  { id := "lie_down", languageId := "yuca1254", parameterId := "lie-down" }

def AFCT : Form Cell :=
  { id := "lucy1994_AFCT"
    lexeme := Lexemes.afct
    cell := {}
    form := "=t"
    segments := ["=t"]
    source := [
      ⟨"lucy-1994", "(1a)"⟩
    ] }

def ROOT : Form Cell :=
  { id := "lucy1994_ROOT"
    lexeme := Lexemes.root
    cell := {}
    form := "=∅"
    segments := ["=∅"]
    source := [
      ⟨"lucy-1994", "(1b)"⟩
    ] }

def CAUS : Form Cell :=
  { id := "lucy1994_CAUS"
    lexeme := Lexemes.caus
    cell := {}
    form := "=s"
    segments := ["=s"]
    source := [
      ⟨"lucy-1994", "(1c)"⟩
    ] }

def POS : Form Cell :=
  { id := "lucy1994_POS"
    lexeme := Lexemes.pos
    cell := {}
    form := "=lah"
    segments := ["=lah"]
    source := [
      ⟨"lucy-1994", "(5)"⟩
    ] }

def siit : Form Cell :=
  { id := "lucy1994_siit"
    lexeme := Lexemes.jump
    cell := {}
    form := "síit'"
    segments := ["síit'"]
    source := [
      ⟨"lucy-1994", "(1a)"⟩
    ] }

def siit_t : Form Cell :=
  { id := "lucy1994_siit_t"
    lexeme := Lexemes.jump_over
    cell := {}
    form := "síit'=t"
    segments := ["síit'", "=t"]
    source := [
      ⟨"lucy-1994", "(1a)"⟩
    ] }

def tziib : Form Cell :=
  { id := "lucy1994_tziib"
    lexeme := Lexemes.write
    cell := {}
    form := "¢'iib'"
    segments := ["¢'iib'"]
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def miis : Form Cell :=
  { id := "lucy1994_miis"
    lexeme := Lexemes.sweep
    cell := {}
    form := "mìis"
    segments := ["mìis"]
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def cheh : Form Cell :=
  { id := "lucy1994_cheh"
    lexeme := Lexemes.smile
    cell := {}
    form := "čé'eh"
    segments := ["čé'eh"]
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def paak : Form Cell :=
  { id := "lucy1994_paak"
    lexeme := Lexemes.weed
    cell := {}
    form := "páak"
    segments := ["páak"]
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def kuc : Form Cell :=
  { id := "lucy1994_kuc"
    lexeme := Lexemes.carry
    cell := {}
    form := "kuč"
    segments := ["kuč"]
    source := [
      ⟨"lucy-1994", "(1b)"⟩
    ] }

def kuc_0 : Form Cell :=
  { id := "lucy1994_kuc_0"
    lexeme := Lexemes.carry_tr
    cell := {}
    form := "kuč=∅"
    segments := ["kuč", "=∅"]
    source := [
      ⟨"lucy-1994", "(1b)"⟩
    ] }

def kos : Form Cell :=
  { id := "lucy1994_kos"
    lexeme := Lexemes.cut
    cell := {}
    form := "k'os"
    segments := ["k'os"]
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def pis : Form Cell :=
  { id := "lucy1994_pis"
    lexeme := Lexemes.measure
    cell := {}
    form := "p'is"
    segments := ["p'is"]
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def hats : Form Cell :=
  { id := "lucy1994_hats"
    lexeme := Lexemes.whip
    cell := {}
    form := "ha¢"
    segments := ["ha¢"]
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def los : Form Cell :=
  { id := "lucy1994_los"
    lexeme := Lexemes.punch
    cell := {}
    form := "loš"
    segments := ["loš"]
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def ah : Form Cell :=
  { id := "lucy1994_ah"
    lexeme := Lexemes.awaken
    cell := {}
    form := "'ah"
    segments := ["'ah"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def ah_s : Form Cell :=
  { id := "lucy1994_ah_s"
    lexeme := Lexemes.wake_someone
    cell := {}
    form := "'ah=s"
    segments := ["'ah", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def wen : Form Cell :=
  { id := "lucy1994_wen"
    lexeme := Lexemes.fall_asleep
    cell := {}
    form := "wen"
    segments := ["wen"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def wen_s : Form Cell :=
  { id := "lucy1994_wen_s"
    lexeme := Lexemes.put_to_sleep
    cell := {}
    form := "ween=s"
    segments := ["ween", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def siih : Form Cell :=
  { id := "lucy1994_siih"
    lexeme := Lexemes.be_born
    cell := {}
    form := "siih"
    segments := ["siih"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def siih_s : Form Cell :=
  { id := "lucy1994_siih_s"
    lexeme := Lexemes.give_birth
    cell := {}
    form := "siih=s"
    segments := ["siih", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def kiim : Form Cell :=
  { id := "lucy1994_kiim"
    lexeme := Lexemes.die
    cell := {}
    form := "kíim"
    segments := ["kíim"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def kiim_s : Form Cell :=
  { id := "lucy1994_kiim_s"
    lexeme := Lexemes.kill
    cell := {}
    form := "kíim=s"
    segments := ["kíim", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def tuub : Form Cell :=
  { id := "lucy1994_tuub"
    lexeme := Lexemes.forget
    cell := {}
    form := "tú'ub'"
    segments := ["tú'ub'"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def tuub_s : Form Cell :=
  { id := "lucy1994_tuub_s"
    lexeme := Lexemes.distract
    cell := {}
    form := "tú'ub'=s"
    segments := ["tú'ub'", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def kaah : Form Cell :=
  { id := "lucy1994_kaah"
    lexeme := Lexemes.remember
    cell := {}
    form := "k'a'ah"
    segments := ["k'a'ah"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def kaah_s : Form Cell :=
  { id := "lucy1994_kaah_s"
    lexeme := Lexemes.remind
    cell := {}
    form := "k'á'ah=s"
    segments := ["k'á'ah", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def chuun : Form Cell :=
  { id := "lucy1994_chuun"
    lexeme := Lexemes.begin_activity
    cell := {}
    form := "ču'un"
    segments := ["ču'un"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def chuun_s : Form Cell :=
  { id := "lucy1994_chuun_s"
    lexeme := Lexemes.cause_to_begin
    cell := {}
    form := "ču'un=s"
    segments := ["ču'un", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def chen : Form Cell :=
  { id := "lucy1994_chen"
    lexeme := Lexemes.stop
    cell := {}
    form := "č'en"
    segments := ["č'en"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def chen_s : Form Cell :=
  { id := "lucy1994_chen_s"
    lexeme := Lexemes.cause_to_stop
    cell := {}
    form := "č'en=s"
    segments := ["č'en", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def hoop : Form Cell :=
  { id := "lucy1994_hoop"
    lexeme := Lexemes.begin
    cell := {}
    form := "hó'op'"
    segments := ["hó'op'"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def hoop_s : Form Cell :=
  { id := "lucy1994_hoop_s"
    lexeme := Lexemes.cause_to_start
    cell := {}
    form := "hó'op'=s"
    segments := ["hó'op'", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def haaw : Form Cell :=
  { id := "lucy1994_haaw"
    lexeme := Lexemes.cease
    cell := {}
    form := "háaw"
    segments := ["háaw"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def haaw_s : Form Cell :=
  { id := "lucy1994_haaw_s"
    lexeme := Lexemes.revoke
    cell := {}
    form := "háaw=s"
    segments := ["háaw", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def heel : Form Cell :=
  { id := "lucy1994_heel"
    lexeme := Lexemes.rest
    cell := {}
    form := "hé'el"
    segments := ["hé'el"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def heel_s : Form Cell :=
  { id := "lucy1994_heel_s"
    lexeme := Lexemes.rest_tr
    cell := {}
    form := "hé'e(l)=s"
    segments := ["hé'e(l)", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def paat : Form Cell :=
  { id := "lucy1994_paat"
    lexeme := Lexemes.remain
    cell := {}
    form := "p'át"
    segments := ["p'át"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def paat_s : Form Cell :=
  { id := "lucy1994_paat_s"
    lexeme := Lexemes.abandon
    cell := {}
    form := "p'át=s"
    segments := ["p'át", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def maan : Form Cell :=
  { id := "lucy1994_maan"
    lexeme := Lexemes.pass_by
    cell := {}
    form := "máan"
    segments := ["máan"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def maan_s : Form Cell :=
  { id := "lucy1994_maan_s"
    lexeme := Lexemes.transport
    cell := {}
    form := "maan=s"
    segments := ["maan", "=s"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def peek : Form Cell :=
  { id := "lucy1994_peek"
    lexeme := Lexemes.move
    cell := {}
    form := "péek"
    segments := ["péek"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def peek_s : Form Cell :=
  { id := "lucy1994_peek_s"
    lexeme := Lexemes.cause_to_move
    cell := {}
    form := "pek=s"
    segments := ["pek", "=s"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def bin : Form Cell :=
  { id := "lucy1994_bin"
    lexeme := Lexemes.go
    cell := {}
    form := "b'in"
    segments := ["b'in"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def bin_s : Form Cell :=
  { id := "lucy1994_bin_s"
    lexeme := Lexemes.take
    cell := {}
    form := "bi(n)=s"
    segments := ["bi(n)", "=s"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def taal : Form Cell :=
  { id := "lucy1994_taal"
    lexeme := Lexemes.come
    cell := {}
    form := "tàal"
    segments := ["tàal"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def taal_s : Form Cell :=
  { id := "lucy1994_taal_s"
    lexeme := Lexemes.bring
    cell := {}
    form := "taa(l)=s"
    segments := ["taa(l)", "=s"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def uul : Form Cell :=
  { id := "lucy1994_uul"
    lexeme := Lexemes.arrive_here
    cell := {}
    form := "'ú'ul"
    segments := ["'ú'ul"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def uul_s : Form Cell :=
  { id := "lucy1994_uul_s"
    lexeme := Lexemes.bring_here
    cell := {}
    form := "'u'uh=s"
    segments := ["'u'uh", "=s"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def ok : Form Cell :=
  { id := "lucy1994_ok"
    lexeme := Lexemes.enter
    cell := {}
    form := "'ok"
    segments := ["'ok"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def ok_s : Form Cell :=
  { id := "lucy1994_ok_s"
    lexeme := Lexemes.move_in
    cell := {}
    form := "'ook=s"
    segments := ["'ook", "=s"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def luub : Form Cell :=
  { id := "lucy1994_luub"
    lexeme := Lexemes.fall
    cell := {}
    form := "lúub'"
    segments := ["lúub'"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def luub_s : Form Cell :=
  { id := "lucy1994_luub_s"
    lexeme := Lexemes.fell
    cell := {}
    form := "luub'=s"
    segments := ["luub'", "=s"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def liik : Form Cell :=
  { id := "lucy1994_liik"
    lexeme := Lexemes.rise
    cell := {}
    form := "líik'"
    segments := ["líik'"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def liik_s : Form Cell :=
  { id := "lucy1994_liik_s"
    lexeme := Lexemes.raise
    cell := {}
    form := "lii(k)'=s"
    segments := ["lii(k)'", "=s"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def naak : Form Cell :=
  { id := "lucy1994_naak"
    lexeme := Lexemes.ascend
    cell := {}
    form := "ná'ak"
    segments := ["ná'ak"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def naak_s : Form Cell :=
  { id := "lucy1994_naak_s"
    lexeme := Lexemes.raise_2
    cell := {}
    form := "na'ak=s"
    segments := ["na'ak", "=s"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def cin : Form Cell :=
  { id := "lucy1994_cin"
    lexeme := Lexemes.bend
    cell := {}
    form := "čin"
    segments := ["čin"]
    source := [
      ⟨"lucy-1994", "(5)"⟩
    ] }

def cin_0 : Form Cell :=
  { id := "lucy1994_cin_0"
    lexeme := Lexemes.bend_tr
    cell := {}
    form := "čin=∅"
    segments := ["čin", "=∅"]
    source := [
      ⟨"lucy-1994", "(6)"⟩
    ] }

def cin_lah : Form Cell :=
  { id := "lucy1994_cin_lah"
    lexeme := Lexemes.become_bent
    cell := {}
    form := "čin=lah"
    segments := ["čin", "=lah"]
    source := [
      ⟨"lucy-1994", "(5c)"⟩
    ] }

def cil : Form Cell :=
  { id := "lucy1994_cil"
    lexeme := Lexemes.lie_down
    cell := {}
    form := "čil"
    segments := ["čil"]
    source := [
      ⟨"lucy-1994", "(7)"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.afct, Lexemes.root, Lexemes.caus, Lexemes.pos, Lexemes.jump,
  Lexemes.jump_over, Lexemes.write, Lexemes.sweep, Lexemes.smile, Lexemes.weed, Lexemes.carry,
  Lexemes.carry_tr, Lexemes.cut, Lexemes.measure, Lexemes.whip, Lexemes.punch, Lexemes.awaken,
  Lexemes.wake_someone, Lexemes.fall_asleep, Lexemes.put_to_sleep, Lexemes.be_born,
  Lexemes.give_birth, Lexemes.die, Lexemes.kill, Lexemes.forget, Lexemes.distract, Lexemes.remember,
  Lexemes.remind, Lexemes.begin_activity, Lexemes.cause_to_begin, Lexemes.stop,
  Lexemes.cause_to_stop, Lexemes.begin, Lexemes.cause_to_start, Lexemes.cease, Lexemes.revoke,
  Lexemes.rest, Lexemes.rest_tr, Lexemes.remain, Lexemes.abandon, Lexemes.pass_by,
  Lexemes.transport, Lexemes.move, Lexemes.cause_to_move, Lexemes.go, Lexemes.take, Lexemes.come,
  Lexemes.bring, Lexemes.arrive_here, Lexemes.bring_here, Lexemes.enter, Lexemes.move_in,
  Lexemes.fall, Lexemes.fell, Lexemes.rise, Lexemes.raise, Lexemes.ascend, Lexemes.raise_2,
  Lexemes.bend, Lexemes.bend_tr, Lexemes.become_bent, Lexemes.lie_down]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [AFCT, ROOT, CAUS, POS, siit, siit_t, tziib, miis, cheh, paak, kuc,
  kuc_0, kos, pis, hats, los, ah, ah_s, wen, wen_s, siih, siih_s, kiim, kiim_s, tuub, tuub_s, kaah,
  kaah_s, chuun, chuun_s, chen, chen_s, hoop, hoop_s, haaw, haaw_s, heel, heel_s, paat, paat_s,
  maan, maan_s, peek, peek_s, bin, bin_s, taal, taal_s, uul, uul_s, ok, ok_s, luub, luub_s, liik,
  liik_s, naak, naak_s, cin, cin_0, cin_lah, cil]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := [
  { id := "lucy1994_siit_t", form := siit, target := siit_t, relation := "affective", source := [
      ⟨"lucy-1994", "(1a)"⟩
    ] },
  { id := "lucy1994_tziib_t", form := tziib, target := AFCT, relation := "affective", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_miis_t", form := miis, target := AFCT, relation := "affective", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_cheh_t", form := cheh, target := AFCT, relation := "affective", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_paak_t", form := paak, target := AFCT, relation := "affective", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_kuc_0", form := kuc, target := kuc_0, relation := "root", source := [
      ⟨"lucy-1994", "(1b)"⟩
    ] },
  { id := "lucy1994_kos_0", form := kos, target := ROOT, relation := "root", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_pis_0", form := pis, target := ROOT, relation := "root", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_hats_0", form := hats, target := ROOT, relation := "root", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_los_0", form := los, target := ROOT, relation := "root", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_ah_s", form := ah, target := ah_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_wen_s", form := wen, target := wen_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_siih_s", form := siih, target := siih_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_kiim_s", form := kiim, target := kiim_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_tuub_s", form := tuub, target := tuub_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_kaah_s", form := kaah, target := kaah_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_chuun_s", form := chuun, target := chuun_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_chen_s", form := chen, target := chen_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_hoop_s", form := hoop, target := hoop_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_haaw_s", form := haaw, target := haaw_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_heel_s", form := heel, target := heel_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_paat_s", form := paat, target := paat_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_maan_s", form := maan, target := maan_s, relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_peek_s", form := peek, target := peek_s, relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_bin_s", form := bin, target := bin_s, relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_taal_s", form := taal, target := taal_s, relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_uul_s", form := uul, target := uul_s, relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_ok_s", form := ok, target := ok_s, relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_luub_s", form := luub, target := luub_s, relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_liik_s", form := liik, target := liik_s, relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_naak_s", form := naak, target := naak_s, relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_cin_0", form := cin, target := cin_0, relation := "root", source := [
      ⟨"lucy-1994", "(6)"⟩
    ] },
  { id := "lucy1994_cin_lah", form := cin, target := cin_lah, relation := "positional", source := [
      ⟨"lucy-1994", "(5c)"⟩
    ] },
  { id := "lucy1994_cil_lah", form := cil, target := POS, relation := "positional", source := [
      ⟨"lucy-1994", "(7)"⟩
    ] }]

end Lucy1994.Wordlist
