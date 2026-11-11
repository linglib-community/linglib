module

public import Linglib.Data.Wordlist.Schema

/-!
# `Sneddon1996`: word forms

Auto-generated from `Linglib/Data/Wordlist/Sneddon1996.json` by `scripts/gen_wordlist.py`. Do not
edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
Sneddon1996.Wordlist`.
-/

@[expose] public section

namespace Sneddon1996.Wordlist

open CLDF.Wordlist

/-- The values of `Prefix` the source distinguishes. -/
inductive Prefix where
  /-- The verbal prefix, `meN-` in the source. -/
  | meN
  /-- The nominal prefix, `peN-` in the source. -/
  | peN
  /-- The prefix, `ber-` in the source. -/
  | ber
  /-- The prefix, `per-` in the source. -/
  | per
  /-- The prefix, `ter-` in the source. -/
  | ter
  deriving DecidableEq, Repr

/-- The values of `Inner` the source distinguishes. -/
inductive Inner where
  /-- The prefix *per-* between a nasal prefix and the base, `per-` in the source. -/
  | per
  deriving DecidableEq, Repr

/-- The values of `Suffix` the source distinguishes. -/
inductive Suffix where
  /-- The suffix, `-kan` in the source. -/
  | kan
  /-- The suffix, `-i` in the source. -/
  | i
  /-- The suffix, `-an` in the source. -/
  | an
  deriving DecidableEq, Repr

/-- The values of `Origin` the source distinguishes. -/
inductive Origin where
  /-- A word the grammar calls borrowed from another language, `borrowed` in the source. -/
  | borrowed
  deriving DecidableEq, Repr

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.renang : Lexeme :=
  { id := "renang", languageId := "indo1316", parameterId := "renang" }

def Lexemes.berenang : Lexeme :=
  { id := "berenang", languageId := "indo1316", parameterId := "berenang" }

def Lexemes.rusak : Lexeme :=
  { id := "rusak", languageId := "indo1316", parameterId := "rusak" }

def Lexemes.perusak : Lexeme :=
  { id := "perusak", languageId := "indo1316", parameterId := "perusak" }

def Lexemes.rasa : Lexeme :=
  { id := "rasa", languageId := "indo1316", parameterId := "rasa" }

def Lexemes.terasa : Lexeme :=
  { id := "terasa", languageId := "indo1316", parameterId := "terasa" }

def Lexemes.serta : Lexeme :=
  { id := "serta", languageId := "indo1316", parameterId := "serta" }

def Lexemes.beserta : Lexeme :=
  { id := "beserta", languageId := "indo1316", parameterId := "beserta" }

def Lexemes.terbang : Lexeme :=
  { id := "terbang", languageId := "indo1316", parameterId := "terbang" }

def Lexemes.beterbangan : Lexeme :=
  { id := "beterbangan", languageId := "indo1316", parameterId := "beterbangan" }

def Lexemes.kerja : Lexeme :=
  { id := "kerja", languageId := "indo1316", parameterId := "kerja" }

def Lexemes.pekerjaan : Lexeme :=
  { id := "pekerjaan", languageId := "indo1316", parameterId := "pekerjaan" }

def Lexemes.pergok : Lexeme :=
  { id := "pergok", languageId := "indo1316", parameterId := "pergok" }

def Lexemes.tepergok : Lexeme :=
  { id := "tepergok", languageId := "indo1316", parameterId := "tepergok" }

def Lexemes.percaya : Lexeme :=
  { id := "percaya", languageId := "indo1316", parameterId := "percaya" }

def Lexemes.tepercaya : Lexeme :=
  { id := "tepercaya", languageId := "indo1316", parameterId := "tepercaya" }

def Lexemes.terpercaya : Lexeme :=
  { id := "terpercaya", languageId := "indo1316", parameterId := "terpercaya" }

def Lexemes.lanjur : Lexeme :=
  { id := "lanjur", languageId := "indo1316", parameterId := "lanjur" }

def Lexemes.telanjur : Lexeme :=
  { id := "telanjur", languageId := "indo1316", parameterId := "telanjur" }

def Lexemes.terlanjur : Lexeme :=
  { id := "terlanjur", languageId := "indo1316", parameterId := "terlanjur" }

def Lexemes.lantar : Lexeme :=
  { id := "lantar", languageId := "indo1316", parameterId := "lantar" }

def Lexemes.telantar : Lexeme :=
  { id := "telantar", languageId := "indo1316", parameterId := "telantar" }

def Lexemes.terlantar : Lexeme :=
  { id := "terlantar", languageId := "indo1316", parameterId := "terlantar" }

def Lexemes.ajar : Lexeme :=
  { id := "ajar", languageId := "indo1316", parameterId := "ajar" }

def Lexemes.belajar : Lexeme :=
  { id := "belajar", languageId := "indo1316", parameterId := "belajar" }

def Lexemes.pelajaran : Lexeme :=
  { id := "pelajaran", languageId := "indo1316", parameterId := "pelajaran" }

def Lexemes.mengajar : Lexeme :=
  { id := "mengajar", languageId := "indo1316", parameterId := "mengajar" }

def Lexemes.ekspor : Lexeme :=
  { id := "ekspor", languageId := "indo1316", parameterId := "ekspor" }

def Lexemes.mengekspor : Lexeme :=
  { id := "mengekspor", languageId := "indo1316", parameterId := "mengekspor" }

def Lexemes.erang : Lexeme :=
  { id := "erang", languageId := "indo1316", parameterId := "erang" }

def Lexemes.mengerang : Lexeme :=
  { id := "mengerang", languageId := "indo1316", parameterId := "mengerang" }

def Lexemes.olah : Lexeme :=
  { id := "olah", languageId := "indo1316", parameterId := "olah" }

def Lexemes.mengolah : Lexeme :=
  { id := "mengolah", languageId := "indo1316", parameterId := "mengolah" }

def Lexemes.urus : Lexeme :=
  { id := "urus", languageId := "indo1316", parameterId := "urus" }

def Lexemes.mengurus : Lexeme :=
  { id := "mengurus", languageId := "indo1316", parameterId := "mengurus" }

def Lexemes.beli : Lexeme :=
  { id := "beli", languageId := "indo1316", parameterId := "beli" }

def Lexemes.membeli : Lexeme :=
  { id := "membeli", languageId := "indo1316", parameterId := "membeli" }

def Lexemes.pakai : Lexeme :=
  { id := "pakai", languageId := "indo1316", parameterId := "pakai" }

def Lexemes.memakai : Lexeme :=
  { id := "memakai", languageId := "indo1316", parameterId := "memakai" }

def Lexemes.fitnah : Lexeme :=
  { id := "fitnah", languageId := "indo1316", parameterId := "fitnah" }

def Lexemes.memfitnah : Lexeme :=
  { id := "memfitnah", languageId := "indo1316", parameterId := "memfitnah" }

def Lexemes.dengar : Lexeme :=
  { id := "dengar", languageId := "indo1316", parameterId := "dengar" }

def Lexemes.mendengar : Lexeme :=
  { id := "mendengar", languageId := "indo1316", parameterId := "mendengar" }

def Lexemes.tulis : Lexeme :=
  { id := "tulis", languageId := "indo1316", parameterId := "tulis" }

def Lexemes.menulis : Lexeme :=
  { id := "menulis", languageId := "indo1316", parameterId := "menulis" }

def Lexemes.cari : Lexeme :=
  { id := "cari", languageId := "indo1316", parameterId := "cari" }

def Lexemes.mencari : Lexeme :=
  { id := "mencari", languageId := "indo1316", parameterId := "mencari" }

def Lexemes.jual : Lexeme :=
  { id := "jual", languageId := "indo1316", parameterId := "jual" }

def Lexemes.menjual : Lexeme :=
  { id := "menjual", languageId := "indo1316", parameterId := "menjual" }

def Lexemes.syarat : Lexeme :=
  { id := "syarat", languageId := "indo1316", parameterId := "syarat" }

def Lexemes.mensyaratkan : Lexeme :=
  { id := "mensyaratkan", languageId := "indo1316", parameterId := "mensyaratkan" }

def Lexemes.ziarah : Lexeme :=
  { id := "ziarah", languageId := "indo1316", parameterId := "ziarah" }

def Lexemes.menziarahi : Lexeme :=
  { id := "menziarahi", languageId := "indo1316", parameterId := "menziarahi" }

def Lexemes.sewa : Lexeme :=
  { id := "sewa", languageId := "indo1316", parameterId := "sewa" }

def Lexemes.menyewa : Lexeme :=
  { id := "menyewa", languageId := "indo1316", parameterId := "menyewa" }

def Lexemes.ganggu : Lexeme :=
  { id := "ganggu", languageId := "indo1316", parameterId := "ganggu" }

def Lexemes.mengganggu : Lexeme :=
  { id := "mengganggu", languageId := "indo1316", parameterId := "mengganggu" }

def Lexemes.kirim : Lexeme :=
  { id := "kirim", languageId := "indo1316", parameterId := "kirim" }

def Lexemes.mengirim : Lexeme :=
  { id := "mengirim", languageId := "indo1316", parameterId := "mengirim" }

def Lexemes.hilang : Lexeme :=
  { id := "hilang", languageId := "indo1316", parameterId := "hilang" }

def Lexemes.menghilang : Lexeme :=
  { id := "menghilang", languageId := "indo1316", parameterId := "menghilang" }

def Lexemes.khawatir : Lexeme :=
  { id := "khawatir", languageId := "indo1316", parameterId := "khawatir" }

def Lexemes.mengkhawatirkan : Lexeme :=
  { id := "mengkhawatirkan", languageId := "indo1316", parameterId := "mengkhawatirkan" }

def Lexemes.lihat : Lexeme :=
  { id := "lihat", languageId := "indo1316", parameterId := "lihat" }

def Lexemes.melihat : Lexeme :=
  { id := "melihat", languageId := "indo1316", parameterId := "melihat" }

def Lexemes.merasa : Lexeme :=
  { id := "merasa", languageId := "indo1316", parameterId := "merasa" }

def Lexemes.masak : Lexeme :=
  { id := "masak", languageId := "indo1316", parameterId := "masak" }

def Lexemes.memasak : Lexeme :=
  { id := "memasak", languageId := "indo1316", parameterId := "memasak" }

def Lexemes.nanti : Lexeme :=
  { id := "nanti", languageId := "indo1316", parameterId := "nanti" }

def Lexemes.menanti : Lexeme :=
  { id := "menanti", languageId := "indo1316", parameterId := "menanti" }

def Lexemes.nyanyi : Lexeme :=
  { id := "nyanyi", languageId := "indo1316", parameterId := "nyanyi" }

def Lexemes.menyanyi : Lexeme :=
  { id := "menyanyi", languageId := "indo1316", parameterId := "menyanyi" }

def Lexemes.nganga : Lexeme :=
  { id := "nganga", languageId := "indo1316", parameterId := "nganga" }

def Lexemes.menganga : Lexeme :=
  { id := "menganga", languageId := "indo1316", parameterId := "menganga" }

def Lexemes.wakil : Lexeme :=
  { id := "wakil", languageId := "indo1316", parameterId := "wakil" }

def Lexemes.mewakili : Lexeme :=
  { id := "mewakili", languageId := "indo1316", parameterId := "mewakili" }

def Lexemes.yakin : Lexeme :=
  { id := "yakin", languageId := "indo1316", parameterId := "yakin" }

def Lexemes.meyakini : Lexeme :=
  { id := "meyakini", languageId := "indo1316", parameterId := "meyakini" }

def Lexemes.karang : Lexeme :=
  { id := "karang", languageId := "indo1316", parameterId := "karang" }

def Lexemes.mengarang_karang : Lexeme :=
  { id := "mengarang_karang", languageId := "indo1316", parameterId := "mengarang_karang" }

def Lexemes.arang : Lexeme :=
  { id := "arang", languageId := "indo1316", parameterId := "arang" }

def Lexemes.mengarang_arang : Lexeme :=
  { id := "mengarang_arang", languageId := "indo1316", parameterId := "mengarang_arang" }

def Lexemes.penulis : Lexeme :=
  { id := "penulis", languageId := "indo1316", parameterId := "penulis" }

def Lexemes.penulisan : Lexeme :=
  { id := "penulisan", languageId := "indo1316", parameterId := "penulisan" }

def Lexemes.lebar : Lexeme :=
  { id := "lebar", languageId := "indo1316", parameterId := "lebar" }

def Lexemes.memperlebar : Lexeme :=
  { id := "memperlebar", languageId := "indo1316", parameterId := "memperlebar" }

def Lexemes.oleh : Lexeme :=
  { id := "oleh", languageId := "indo1316", parameterId := "oleh" }

def Lexemes.memperoleh : Lexeme :=
  { id := "memperoleh", languageId := "indo1316", parameterId := "memperoleh" }

def Lexemes.mempercayai : Lexeme :=
  { id := "mempercayai", languageId := "indo1316", parameterId := "mempercayai" }

def Lexemes.mempergoki : Lexeme :=
  { id := "mempergoki", languageId := "indo1316", parameterId := "mempergoki" }

def Lexemes.memergoki : Lexeme :=
  { id := "memergoki", languageId := "indo1316", parameterId := "memergoki" }

def Lexemes.percik : Lexeme :=
  { id := "percik", languageId := "indo1316", parameterId := "percik" }

def Lexemes.memerciki : Lexeme :=
  { id := "memerciki", languageId := "indo1316", parameterId := "memerciki" }

def Lexemes.satu : Lexeme :=
  { id := "satu", languageId := "indo1316", parameterId := "satu" }

def Lexemes.pemersatu : Lexeme :=
  { id := "pemersatu", languageId := "indo1316", parameterId := "pemersatu" }

def Lexemes.pemerolehan : Lexeme :=
  { id := "pemerolehan", languageId := "indo1316", parameterId := "pemerolehan" }

def Lexemes.perkosa : Lexeme :=
  { id := "perkosa", languageId := "indo1316", parameterId := "perkosa" }

def Lexemes.pemerkosa : Lexeme :=
  { id := "pemerkosa", languageId := "indo1316", parameterId := "pemerkosa" }

def Lexemes.proklamasi : Lexeme :=
  { id := "proklamasi", languageId := "indo1316", parameterId := "proklamasi" }

def Lexemes.memproklamasikan : Lexeme :=
  { id := "memproklamasikan", languageId := "indo1316", parameterId := "memproklamasikan" }

def Lexemes.traktir : Lexeme :=
  { id := "traktir", languageId := "indo1316", parameterId := "traktir" }

def Lexemes.mentraktir : Lexeme :=
  { id := "mentraktir", languageId := "indo1316", parameterId := "mentraktir" }

def Lexemes.swadaya : Lexeme :=
  { id := "swadaya", languageId := "indo1316", parameterId := "swadaya" }

def Lexemes.menswadayakan : Lexeme :=
  { id := "menswadayakan", languageId := "indo1316", parameterId := "menswadayakan" }

def Lexemes.klasifikasi : Lexeme :=
  { id := "klasifikasi", languageId := "indo1316", parameterId := "klasifikasi" }

def Lexemes.mengklasifikasikan : Lexeme :=
  { id := "mengklasifikasikan", languageId := "indo1316", parameterId := "mengklasifikasikan" }

def Lexemes.protes : Lexeme :=
  { id := "protes", languageId := "indo1316", parameterId := "protes" }

def Lexemes.memprotes : Lexeme :=
  { id := "memprotes", languageId := "indo1316", parameterId := "memprotes" }

def Lexemes.memrotes : Lexeme :=
  { id := "memrotes", languageId := "indo1316", parameterId := "memrotes" }

def Lexemes.taat : Lexeme :=
  { id := "taat", languageId := "indo1316", parameterId := "taat" }

def Lexemes.mentaati : Lexeme :=
  { id := "mentaati", languageId := "indo1316", parameterId := "mentaati" }

def Lexemes.menaati : Lexeme :=
  { id := "menaati", languageId := "indo1316", parameterId := "menaati" }

def Lexemes.sukses : Lexeme :=
  { id := "sukses", languageId := "indo1316", parameterId := "sukses" }

def Lexemes.mensukseskan : Lexeme :=
  { id := "mensukseskan", languageId := "indo1316", parameterId := "mensukseskan" }

def Lexemes.menyukseskan : Lexeme :=
  { id := "menyukseskan", languageId := "indo1316", parameterId := "menyukseskan" }

def Lexemes.kritik : Lexeme :=
  { id := "kritik", languageId := "indo1316", parameterId := "kritik" }

def Lexemes.mengkritik : Lexeme :=
  { id := "mengkritik", languageId := "indo1316", parameterId := "mengkritik" }

def Lexemes.mengritik : Lexeme :=
  { id := "mengritik", languageId := "indo1316", parameterId := "mengritik" }

def Lexemes.pengaruh : Lexeme :=
  { id := "pengaruh", languageId := "indo1316", parameterId := "pengaruh" }

def Lexemes.mempengaruhi : Lexeme :=
  { id := "mempengaruhi", languageId := "indo1316", parameterId := "mempengaruhi" }

def Lexemes.punya : Lexeme :=
  { id := "punya", languageId := "indo1316", parameterId := "punya" }

def Lexemes.mempunyai : Lexeme :=
  { id := "mempunyai", languageId := "indo1316", parameterId := "mempunyai" }

def Lexemes.kaji : Lexeme :=
  { id := "kaji", languageId := "indo1316", parameterId := "kaji" }

def Lexemes.mengaji : Lexeme :=
  { id := "mengaji", languageId := "indo1316", parameterId := "mengaji" }

def Lexemes.mengkaji : Lexeme :=
  { id := "mengkaji", languageId := "indo1316", parameterId := "mengkaji" }

def Lexemes.pengajian : Lexeme :=
  { id := "pengajian", languageId := "indo1316", parameterId := "pengajian" }

def Lexemes.pengkajian : Lexeme :=
  { id := "pengkajian", languageId := "indo1316", parameterId := "pengkajian" }

def Lexemes.penglihatan : Lexeme :=
  { id := "penglihatan", languageId := "indo1316", parameterId := "penglihatan" }

def Lexemes.rajin : Lexeme :=
  { id := "rajin", languageId := "indo1316", parameterId := "rajin" }

def Lexemes.pengrajin : Lexeme :=
  { id := "pengrajin", languageId := "indo1316", parameterId := "pengrajin" }

def Lexemes.perajin : Lexeme :=
  { id := "perajin", languageId := "indo1316", parameterId := "perajin" }

def Lexemes.lepas : Lexeme :=
  { id := "lepas", languageId := "indo1316", parameterId := "lepas" }

def Lexemes.penglepasan : Lexeme :=
  { id := "penglepasan", languageId := "indo1316", parameterId := "penglepasan" }

def Lexemes.pelepasan : Lexeme :=
  { id := "pelepasan", languageId := "indo1316", parameterId := "pelepasan" }

def Lexemes.syair : Lexeme :=
  { id := "syair", languageId := "indo1316", parameterId := "syair" }

def Lexemes.menyair : Lexeme :=
  { id := "menyair", languageId := "indo1316", parameterId := "menyair" }

def Lexemes.penyair : Lexeme :=
  { id := "penyair", languageId := "indo1316", parameterId := "penyair" }

def Lexemes.besar : Lexeme :=
  { id := "besar", languageId := "indo1316", parameterId := "besar" }

def Lexemes.memperbesar : Lexeme :=
  { id := "memperbesar", languageId := "indo1316", parameterId := "memperbesar" }

def renang : Form Cell :=
  { id := "sneddon1996_renang"
    lexeme := Lexemes.renang
    cell := {}
    form := "renang"
    segments := ["r", "ə", "n", "a", "ŋ"]
    source := [
      ⟨"sneddon-1996", "p. 8"⟩
    ] }

def berenang : Form Cell :=
  { id := "sneddon1996_berenang"
    lexeme := Lexemes.berenang
    cell := {}
    form := "berenang"
    segments := ["b", "ə", "r", "ə", "n", "a", "ŋ"]
    source := [
      ⟨"sneddon-1996", "p. 8"⟩
    ] }

def rusak : Form Cell :=
  { id := "sneddon1996_rusak"
    lexeme := Lexemes.rusak
    cell := {}
    form := "rusak"
    segments := ["r", "u", "s", "a", "k"]
    source := [
      ⟨"sneddon-1996", "p. 8"⟩
    ] }

def perusak : Form Cell :=
  { id := "sneddon1996_perusak"
    lexeme := Lexemes.perusak
    cell := {}
    form := "perusak"
    segments := ["p", "ə", "r", "u", "s", "a", "k"]
    source := [
      ⟨"sneddon-1996", "p. 8"⟩
    ] }

def rasa : Form Cell :=
  { id := "sneddon1996_rasa"
    lexeme := Lexemes.rasa
    cell := {}
    form := "rasa"
    segments := ["r", "a", "s", "a"]
    source := [
      ⟨"sneddon-1996", "p. 8"⟩
    ] }

def terasa : Form Cell :=
  { id := "sneddon1996_terasa"
    lexeme := Lexemes.terasa
    cell := {}
    form := "terasa"
    segments := ["t", "ə", "r", "a", "s", "a"]
    source := [
      ⟨"sneddon-1996", "p. 8"⟩
    ] }

def serta : Form Cell :=
  { id := "sneddon1996_serta"
    lexeme := Lexemes.serta
    cell := {}
    form := "serta"
    segments := ["s", "ə", "r", "t", "a"]
    source := [
      ⟨"sneddon-1996", "p. 8"⟩
    ] }

def beserta : Form Cell :=
  { id := "sneddon1996_beserta"
    lexeme := Lexemes.beserta
    cell := {}
    form := "beserta"
    segments := ["b", "ə", "s", "ə", "r", "t", "a"]
    source := [
      ⟨"sneddon-1996", "p. 8"⟩
    ] }

def terbang : Form Cell :=
  { id := "sneddon1996_terbang"
    lexeme := Lexemes.terbang
    cell := {}
    form := "terbang"
    segments := ["t", "ə", "r", "b", "a", "ŋ"]
    source := [
      ⟨"sneddon-1996", "p. 8"⟩
    ] }

def beterbangan : Form Cell :=
  { id := "sneddon1996_beterbangan"
    lexeme := Lexemes.beterbangan
    cell := {}
    form := "beterbangan"
    segments := ["b", "ə", "t", "ə", "r", "b", "a", "ŋ", "a", "n"]
    source := [
      ⟨"sneddon-1996", "p. 8"⟩
    ] }

def kerja : Form Cell :=
  { id := "sneddon1996_kerja"
    lexeme := Lexemes.kerja
    cell := {}
    form := "kerja"
    segments := ["k", "ə", "r", "d̠ʒ", "a"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def pekerjaan : Form Cell :=
  { id := "sneddon1996_pekerjaan"
    lexeme := Lexemes.pekerjaan
    cell := {}
    form := "pekerjaan"
    segments := ["p", "ə", "k", "ə", "r", "d̠ʒ", "a", "a", "n"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def pergok : Form Cell :=
  { id := "sneddon1996_pergok"
    lexeme := Lexemes.pergok
    cell := {}
    form := "pergok"
    segments := ["p", "ə", "r", "ɡ", "o", "k"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def tepergok : Form Cell :=
  { id := "sneddon1996_tepergok"
    lexeme := Lexemes.tepergok
    cell := {}
    form := "tepergok"
    segments := ["t", "ə", "p", "ə", "r", "ɡ", "o", "k"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def percaya : Form Cell :=
  { id := "sneddon1996_percaya"
    lexeme := Lexemes.percaya
    cell := {}
    form := "percaya"
    segments := ["p", "ə", "r", "t̠ʃ", "a", "j", "a"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def tepercaya : Form Cell :=
  { id := "sneddon1996_tepercaya"
    lexeme := Lexemes.tepercaya
    cell := {}
    form := "tepercaya"
    segments := ["t", "ə", "p", "ə", "r", "t̠ʃ", "a", "j", "a"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def terpercaya : Form Cell :=
  { id := "sneddon1996_terpercaya"
    lexeme := Lexemes.terpercaya
    cell := {}
    form := "terpercaya"
    segments := ["t", "ə", "r", "p", "ə", "r", "t̠ʃ", "a", "j", "a"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def lanjur : Form Cell :=
  { id := "sneddon1996_lanjur"
    lexeme := Lexemes.lanjur
    cell := {}
    form := "lanjur"
    segments := ["l", "a", "n", "d̠ʒ", "u", "r"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def telanjur : Form Cell :=
  { id := "sneddon1996_telanjur"
    lexeme := Lexemes.telanjur
    cell := {}
    form := "telanjur"
    segments := ["t", "ə", "l", "a", "n", "d̠ʒ", "u", "r"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def terlanjur : Form Cell :=
  { id := "sneddon1996_terlanjur"
    lexeme := Lexemes.terlanjur
    cell := {}
    form := "terlanjur"
    segments := ["t", "ə", "r", "l", "a", "n", "d̠ʒ", "u", "r"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def lantar : Form Cell :=
  { id := "sneddon1996_lantar"
    lexeme := Lexemes.lantar
    cell := {}
    form := "lantar"
    segments := ["l", "a", "n", "t", "a", "r"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def telantar : Form Cell :=
  { id := "sneddon1996_telantar"
    lexeme := Lexemes.telantar
    cell := {}
    form := "telantar"
    segments := ["t", "ə", "l", "a", "n", "t", "a", "r"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def terlantar : Form Cell :=
  { id := "sneddon1996_terlantar"
    lexeme := Lexemes.terlantar
    cell := {}
    form := "terlantar"
    segments := ["t", "ə", "r", "l", "a", "n", "t", "a", "r"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def ajar : Form Cell :=
  { id := "sneddon1996_ajar"
    lexeme := Lexemes.ajar
    cell := {}
    form := "ajar"
    segments := ["a", "d̠ʒ", "a", "r"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def belajar : Form Cell :=
  { id := "sneddon1996_belajar"
    lexeme := Lexemes.belajar
    cell := {}
    form := "belajar"
    segments := ["b", "ə", "l", "a", "d̠ʒ", "a", "r"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def pelajaran : Form Cell :=
  { id := "sneddon1996_pelajaran"
    lexeme := Lexemes.pelajaran
    cell := {}
    form := "pelajaran"
    segments := ["p", "ə", "l", "a", "d̠ʒ", "a", "r", "a", "n"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def mengajar : Form Cell :=
  { id := "sneddon1996_mengajar"
    lexeme := Lexemes.mengajar
    cell := {}
    form := "mengajar"
    segments := ["m", "ə", "ŋ", "a", "d̠ʒ", "a", "r"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def ekspor : Form Cell :=
  { id := "sneddon1996_ekspor"
    lexeme := Lexemes.ekspor
    cell := {}
    form := "ekspor"
    segments := ["e", "k", "s", "p", "o", "r"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def mengekspor : Form Cell :=
  { id := "sneddon1996_mengekspor"
    lexeme := Lexemes.mengekspor
    cell := {}
    form := "mengekspor"
    segments := ["m", "ə", "ŋ", "e", "k", "s", "p", "o", "r"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def erang : Form Cell :=
  { id := "sneddon1996_erang"
    lexeme := Lexemes.erang
    cell := {}
    form := "erang"
    segments := ["ə", "r", "a", "ŋ"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def mengerang : Form Cell :=
  { id := "sneddon1996_mengerang"
    lexeme := Lexemes.mengerang
    cell := {}
    form := "mengerang"
    segments := ["m", "ə", "ŋ", "ə", "r", "a", "ŋ"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def olah : Form Cell :=
  { id := "sneddon1996_olah"
    lexeme := Lexemes.olah
    cell := {}
    form := "olah"
    segments := ["o", "l", "a", "h"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def mengolah : Form Cell :=
  { id := "sneddon1996_mengolah"
    lexeme := Lexemes.mengolah
    cell := {}
    form := "mengolah"
    segments := ["m", "ə", "ŋ", "o", "l", "a", "h"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def urus : Form Cell :=
  { id := "sneddon1996_urus"
    lexeme := Lexemes.urus
    cell := {}
    form := "urus"
    segments := ["u", "r", "u", "s"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def mengurus : Form Cell :=
  { id := "sneddon1996_mengurus"
    lexeme := Lexemes.mengurus
    cell := {}
    form := "mengurus"
    segments := ["m", "ə", "ŋ", "u", "r", "u", "s"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def beli : Form Cell :=
  { id := "sneddon1996_beli"
    lexeme := Lexemes.beli
    cell := {}
    form := "beli"
    segments := ["b", "ə", "l", "i"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def membeli : Form Cell :=
  { id := "sneddon1996_membeli"
    lexeme := Lexemes.membeli
    cell := {}
    form := "membeli"
    segments := ["m", "ə", "m", "b", "ə", "l", "i"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def pakai : Form Cell :=
  { id := "sneddon1996_pakai"
    lexeme := Lexemes.pakai
    cell := {}
    form := "pakai"
    segments := ["p", "a", "k", "a", "i"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def memakai : Form Cell :=
  { id := "sneddon1996_memakai"
    lexeme := Lexemes.memakai
    cell := {}
    form := "memakai"
    segments := ["m", "ə", "m", "a", "k", "a", "i"]
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] }

def fitnah : Form Cell :=
  { id := "sneddon1996_fitnah"
    lexeme := Lexemes.fitnah
    cell := {}
    form := "fitnah"
    segments := ["f", "i", "t", "n", "a", "h"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def memfitnah : Form Cell :=
  { id := "sneddon1996_memfitnah"
    lexeme := Lexemes.memfitnah
    cell := {}
    form := "memfitnah"
    segments := ["m", "ə", "m", "f", "i", "t", "n", "a", "h"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def dengar : Form Cell :=
  { id := "sneddon1996_dengar"
    lexeme := Lexemes.dengar
    cell := {}
    form := "dengar"
    segments := ["d", "ə", "ŋ", "a", "r"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def mendengar : Form Cell :=
  { id := "sneddon1996_mendengar"
    lexeme := Lexemes.mendengar
    cell := {}
    form := "mendengar"
    segments := ["m", "ə", "n", "d", "ə", "ŋ", "a", "r"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def tulis : Form Cell :=
  { id := "sneddon1996_tulis"
    lexeme := Lexemes.tulis
    cell := {}
    form := "tulis"
    segments := ["t", "u", "l", "i", "s"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def menulis : Form Cell :=
  { id := "sneddon1996_menulis"
    lexeme := Lexemes.menulis
    cell := {}
    form := "menulis"
    segments := ["m", "ə", "n", "u", "l", "i", "s"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def cari : Form Cell :=
  { id := "sneddon1996_cari"
    lexeme := Lexemes.cari
    cell := {}
    form := "cari"
    segments := ["t̠ʃ", "a", "r", "i"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def mencari : Form Cell :=
  { id := "sneddon1996_mencari"
    lexeme := Lexemes.mencari
    cell := {}
    form := "mencari"
    segments := ["m", "ə", "n", "t̠ʃ", "a", "r", "i"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def jual : Form Cell :=
  { id := "sneddon1996_jual"
    lexeme := Lexemes.jual
    cell := {}
    form := "jual"
    segments := ["d̠ʒ", "u", "a", "l"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def menjual : Form Cell :=
  { id := "sneddon1996_menjual"
    lexeme := Lexemes.menjual
    cell := {}
    form := "menjual"
    segments := ["m", "ə", "n", "d̠ʒ", "u", "a", "l"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def syarat : Form Cell :=
  { id := "sneddon1996_syarat"
    lexeme := Lexemes.syarat
    cell := {}
    form := "syarat"
    segments := ["ʃ", "a", "r", "a", "t"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def mensyaratkan : Form Cell :=
  { id := "sneddon1996_mensyaratkan"
    lexeme := Lexemes.mensyaratkan
    cell := {}
    form := "mensyaratkan"
    segments := ["m", "ə", "n", "ʃ", "a", "r", "a", "t", "k", "a", "n"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def ziarah : Form Cell :=
  { id := "sneddon1996_ziarah"
    lexeme := Lexemes.ziarah
    cell := {}
    form := "ziarah"
    segments := ["z", "i", "a", "r", "a", "h"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def menziarahi : Form Cell :=
  { id := "sneddon1996_menziarahi"
    lexeme := Lexemes.menziarahi
    cell := {}
    form := "menziarahi"
    segments := ["m", "ə", "n", "z", "i", "a", "r", "a", "h", "i"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def sewa : Form Cell :=
  { id := "sneddon1996_sewa"
    lexeme := Lexemes.sewa
    cell := {}
    form := "sewa"
    segments := ["s", "e", "w", "a"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def menyewa : Form Cell :=
  { id := "sneddon1996_menyewa"
    lexeme := Lexemes.menyewa
    cell := {}
    form := "menyewa"
    segments := ["m", "ə", "ɲ", "e", "w", "a"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def ganggu : Form Cell :=
  { id := "sneddon1996_ganggu"
    lexeme := Lexemes.ganggu
    cell := {}
    form := "ganggu"
    segments := ["ɡ", "a", "ŋ", "ɡ", "u"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def mengganggu : Form Cell :=
  { id := "sneddon1996_mengganggu"
    lexeme := Lexemes.mengganggu
    cell := {}
    form := "mengganggu"
    segments := ["m", "ə", "ŋ", "ɡ", "a", "ŋ", "ɡ", "u"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def kirim : Form Cell :=
  { id := "sneddon1996_kirim"
    lexeme := Lexemes.kirim
    cell := {}
    form := "kirim"
    segments := ["k", "i", "r", "i", "m"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def mengirim : Form Cell :=
  { id := "sneddon1996_mengirim"
    lexeme := Lexemes.mengirim
    cell := {}
    form := "mengirim"
    segments := ["m", "ə", "ŋ", "i", "r", "i", "m"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def hilang : Form Cell :=
  { id := "sneddon1996_hilang"
    lexeme := Lexemes.hilang
    cell := {}
    form := "hilang"
    segments := ["h", "i", "l", "a", "ŋ"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def menghilang : Form Cell :=
  { id := "sneddon1996_menghilang"
    lexeme := Lexemes.menghilang
    cell := {}
    form := "menghilang"
    segments := ["m", "ə", "ŋ", "h", "i", "l", "a", "ŋ"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def khawatir : Form Cell :=
  { id := "sneddon1996_khawatir"
    lexeme := Lexemes.khawatir
    cell := {}
    form := "khawatir"
    segments := ["x", "a", "w", "a", "t", "i", "r"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def mengkhawatirkan : Form Cell :=
  { id := "sneddon1996_mengkhawatirkan"
    lexeme := Lexemes.mengkhawatirkan
    cell := {}
    form := "mengkhawatirkan"
    segments := ["m", "ə", "ŋ", "x", "a", "w", "a", "t", "i", "r", "k", "a", "n"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def lihat : Form Cell :=
  { id := "sneddon1996_lihat"
    lexeme := Lexemes.lihat
    cell := {}
    form := "lihat"
    segments := ["l", "i", "h", "a", "t"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def melihat : Form Cell :=
  { id := "sneddon1996_melihat"
    lexeme := Lexemes.melihat
    cell := {}
    form := "melihat"
    segments := ["m", "ə", "l", "i", "h", "a", "t"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def merasa : Form Cell :=
  { id := "sneddon1996_merasa"
    lexeme := Lexemes.merasa
    cell := {}
    form := "merasa"
    segments := ["m", "ə", "r", "a", "s", "a"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def masak : Form Cell :=
  { id := "sneddon1996_masak"
    lexeme := Lexemes.masak
    cell := {}
    form := "masak"
    segments := ["m", "a", "s", "a", "k"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def memasak : Form Cell :=
  { id := "sneddon1996_memasak"
    lexeme := Lexemes.memasak
    cell := {}
    form := "memasak"
    segments := ["m", "ə", "m", "a", "s", "a", "k"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def nanti : Form Cell :=
  { id := "sneddon1996_nanti"
    lexeme := Lexemes.nanti
    cell := {}
    form := "nanti"
    segments := ["n", "a", "n", "t", "i"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def menanti : Form Cell :=
  { id := "sneddon1996_menanti"
    lexeme := Lexemes.menanti
    cell := {}
    form := "menanti"
    segments := ["m", "ə", "n", "a", "n", "t", "i"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def nyanyi : Form Cell :=
  { id := "sneddon1996_nyanyi"
    lexeme := Lexemes.nyanyi
    cell := {}
    form := "nyanyi"
    segments := ["ɲ", "a", "ɲ", "i"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def menyanyi : Form Cell :=
  { id := "sneddon1996_menyanyi"
    lexeme := Lexemes.menyanyi
    cell := {}
    form := "menyanyi"
    segments := ["m", "ə", "ɲ", "a", "ɲ", "i"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def nganga : Form Cell :=
  { id := "sneddon1996_nganga"
    lexeme := Lexemes.nganga
    cell := {}
    form := "nganga"
    segments := ["ŋ", "a", "ŋ", "a"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def menganga : Form Cell :=
  { id := "sneddon1996_menganga"
    lexeme := Lexemes.menganga
    cell := {}
    form := "menganga"
    segments := ["m", "ə", "ŋ", "a", "ŋ", "a"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def wakil : Form Cell :=
  { id := "sneddon1996_wakil"
    lexeme := Lexemes.wakil
    cell := {}
    form := "wakil"
    segments := ["w", "a", "k", "i", "l"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def mewakili : Form Cell :=
  { id := "sneddon1996_mewakili"
    lexeme := Lexemes.mewakili
    cell := {}
    form := "mewakili"
    segments := ["m", "ə", "w", "a", "k", "i", "l", "i"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def yakin : Form Cell :=
  { id := "sneddon1996_yakin"
    lexeme := Lexemes.yakin
    cell := {}
    form := "yakin"
    segments := ["j", "a", "k", "i", "n"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def meyakini : Form Cell :=
  { id := "sneddon1996_meyakini"
    lexeme := Lexemes.meyakini
    cell := {}
    form := "meyakini"
    segments := ["m", "ə", "j", "a", "k", "i", "n", "i"]
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] }

def karang : Form Cell :=
  { id := "sneddon1996_karang"
    lexeme := Lexemes.karang
    cell := {}
    form := "karang"
    segments := ["k", "a", "r", "a", "ŋ"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def mengarang_karang : Form Cell :=
  { id := "sneddon1996_mengarang_karang"
    lexeme := Lexemes.mengarang_karang
    cell := {}
    form := "mengarang"
    segments := ["m", "ə", "ŋ", "a", "r", "a", "ŋ"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def arang : Form Cell :=
  { id := "sneddon1996_arang"
    lexeme := Lexemes.arang
    cell := {}
    form := "arang"
    segments := ["a", "r", "a", "ŋ"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def mengarang_arang : Form Cell :=
  { id := "sneddon1996_mengarang_arang"
    lexeme := Lexemes.mengarang_arang
    cell := {}
    form := "mengarang"
    segments := ["m", "ə", "ŋ", "a", "r", "a", "ŋ"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def penulis : Form Cell :=
  { id := "sneddon1996_penulis"
    lexeme := Lexemes.penulis
    cell := {}
    form := "penulis"
    segments := ["p", "ə", "n", "u", "l", "i", "s"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def penulisan : Form Cell :=
  { id := "sneddon1996_penulisan"
    lexeme := Lexemes.penulisan
    cell := {}
    form := "penulisan"
    segments := ["p", "ə", "n", "u", "l", "i", "s", "a", "n"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def lebar : Form Cell :=
  { id := "sneddon1996_lebar"
    lexeme := Lexemes.lebar
    cell := {}
    form := "lebar"
    segments := ["l", "e", "b", "a", "r"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def memperlebar : Form Cell :=
  { id := "sneddon1996_memperlebar"
    lexeme := Lexemes.memperlebar
    cell := {}
    form := "memperlebar"
    segments := ["m", "ə", "m", "p", "ə", "r", "l", "e", "b", "a", "r"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def oleh : Form Cell :=
  { id := "sneddon1996_oleh"
    lexeme := Lexemes.oleh
    cell := {}
    form := "oleh"
    segments := ["o", "l", "e", "h"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def memperoleh : Form Cell :=
  { id := "sneddon1996_memperoleh"
    lexeme := Lexemes.memperoleh
    cell := {}
    form := "memperoleh"
    segments := ["m", "ə", "m", "p", "ə", "r", "o", "l", "e", "h"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def mempercayai : Form Cell :=
  { id := "sneddon1996_mempercayai"
    lexeme := Lexemes.mempercayai
    cell := {}
    form := "mempercayai"
    segments := ["m", "ə", "m", "p", "ə", "r", "t̠ʃ", "a", "j", "a", "i"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def mempergoki : Form Cell :=
  { id := "sneddon1996_mempergoki"
    lexeme := Lexemes.mempergoki
    cell := {}
    form := "mempergoki"
    segments := ["m", "ə", "m", "p", "ə", "r", "ɡ", "o", "k", "i"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def memergoki : Form Cell :=
  { id := "sneddon1996_memergoki"
    lexeme := Lexemes.memergoki
    cell := {}
    form := "memergoki"
    segments := ["m", "ə", "m", "ə", "r", "ɡ", "o", "k", "i"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def percik : Form Cell :=
  { id := "sneddon1996_percik"
    lexeme := Lexemes.percik
    cell := {}
    form := "percik"
    segments := ["p", "ə", "r", "t̠ʃ", "i", "k"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def memerciki : Form Cell :=
  { id := "sneddon1996_memerciki"
    lexeme := Lexemes.memerciki
    cell := {}
    form := "memerciki"
    segments := ["m", "ə", "m", "ə", "r", "t̠ʃ", "i", "k", "i"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def satu : Form Cell :=
  { id := "sneddon1996_satu"
    lexeme := Lexemes.satu
    cell := {}
    form := "satu"
    segments := ["s", "a", "t", "u"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def pemersatu : Form Cell :=
  { id := "sneddon1996_pemersatu"
    lexeme := Lexemes.pemersatu
    cell := {}
    form := "pemersatu"
    segments := ["p", "ə", "m", "ə", "r", "s", "a", "t", "u"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def pemerolehan : Form Cell :=
  { id := "sneddon1996_pemerolehan"
    lexeme := Lexemes.pemerolehan
    cell := {}
    form := "pemerolehan"
    segments := ["p", "ə", "m", "ə", "r", "o", "l", "e", "h", "a", "n"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def perkosa : Form Cell :=
  { id := "sneddon1996_perkosa"
    lexeme := Lexemes.perkosa
    cell := {}
    form := "perkosa"
    segments := ["p", "ə", "r", "k", "o", "s", "a"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def pemerkosa : Form Cell :=
  { id := "sneddon1996_pemerkosa"
    lexeme := Lexemes.pemerkosa
    cell := {}
    form := "pemerkosa"
    segments := ["p", "ə", "m", "ə", "r", "k", "o", "s", "a"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def proklamasi : Form Cell :=
  { id := "sneddon1996_proklamasi"
    lexeme := Lexemes.proklamasi
    cell := {}
    form := "proklamasi"
    segments := ["p", "r", "o", "k", "l", "a", "m", "a", "s", "i"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def memproklamasikan : Form Cell :=
  { id := "sneddon1996_memproklamasikan"
    lexeme := Lexemes.memproklamasikan
    cell := {}
    form := "memproklamasikan"
    segments := ["m", "ə", "m", "p", "r", "o", "k", "l", "a", "m", "a", "s", "i", "k", "a", "n"]
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] }

def traktir : Form Cell :=
  { id := "sneddon1996_traktir"
    lexeme := Lexemes.traktir
    cell := {}
    form := "traktir"
    segments := ["t", "r", "a", "k", "t", "i", "r"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def mentraktir : Form Cell :=
  { id := "sneddon1996_mentraktir"
    lexeme := Lexemes.mentraktir
    cell := {}
    form := "mentraktir"
    segments := ["m", "ə", "n", "t", "r", "a", "k", "t", "i", "r"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def swadaya : Form Cell :=
  { id := "sneddon1996_swadaya"
    lexeme := Lexemes.swadaya
    cell := {}
    form := "swadaya"
    segments := ["s", "w", "a", "d", "a", "j", "a"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def menswadayakan : Form Cell :=
  { id := "sneddon1996_menswadayakan"
    lexeme := Lexemes.menswadayakan
    cell := {}
    form := "menswadayakan"
    segments := ["m", "ə", "n", "s", "w", "a", "d", "a", "j", "a", "k", "a", "n"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def klasifikasi : Form Cell :=
  { id := "sneddon1996_klasifikasi"
    lexeme := Lexemes.klasifikasi
    cell := {}
    form := "klasifikasi"
    segments := ["k", "l", "a", "s", "i", "f", "i", "k", "a", "s", "i"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def mengklasifikasikan : Form Cell :=
  { id := "sneddon1996_mengklasifikasikan"
    lexeme := Lexemes.mengklasifikasikan
    cell := {}
    form := "mengklasifikasikan"
    segments := ["m", "ə", "ŋ", "k", "l", "a", "s", "i", "f", "i", "k", "a", "s", "i", "k", "a",
      "n"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def protes : Form Cell :=
  { id := "sneddon1996_protes"
    lexeme := Lexemes.protes
    cell := {}
    form := "protes"
    segments := ["p", "r", "o", "t", "e", "s"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def memprotes : Form Cell :=
  { id := "sneddon1996_memprotes"
    lexeme := Lexemes.memprotes
    cell := {}
    form := "memprotes"
    segments := ["m", "ə", "m", "p", "r", "o", "t", "e", "s"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def memrotes : Form Cell :=
  { id := "sneddon1996_memrotes"
    lexeme := Lexemes.memrotes
    cell := {}
    form := "memrotes"
    segments := ["m", "ə", "m", "r", "o", "t", "e", "s"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def taat : Form Cell :=
  { id := "sneddon1996_taat"
    lexeme := Lexemes.taat
    cell := {}
    form := "taat"
    segments := ["t", "a", "a", "t"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def mentaati : Form Cell :=
  { id := "sneddon1996_mentaati"
    lexeme := Lexemes.mentaati
    cell := {}
    form := "mentaati"
    segments := ["m", "ə", "n", "t", "a", "a", "t", "i"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def menaati : Form Cell :=
  { id := "sneddon1996_menaati"
    lexeme := Lexemes.menaati
    cell := {}
    form := "menaati"
    segments := ["m", "ə", "n", "a", "a", "t", "i"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def sukses : Form Cell :=
  { id := "sneddon1996_sukses"
    lexeme := Lexemes.sukses
    cell := {}
    form := "sukses"
    segments := ["s", "u", "k", "s", "e", "s"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def mensukseskan : Form Cell :=
  { id := "sneddon1996_mensukseskan"
    lexeme := Lexemes.mensukseskan
    cell := {}
    form := "mensukseskan"
    segments := ["m", "ə", "n", "s", "u", "k", "s", "e", "s", "k", "a", "n"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def menyukseskan : Form Cell :=
  { id := "sneddon1996_menyukseskan"
    lexeme := Lexemes.menyukseskan
    cell := {}
    form := "menyukseskan"
    segments := ["m", "ə", "ɲ", "u", "k", "s", "e", "s", "k", "a", "n"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def kritik : Form Cell :=
  { id := "sneddon1996_kritik"
    lexeme := Lexemes.kritik
    cell := {}
    form := "kritik"
    segments := ["k", "r", "i", "t", "i", "k"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def mengkritik : Form Cell :=
  { id := "sneddon1996_mengkritik"
    lexeme := Lexemes.mengkritik
    cell := {}
    form := "mengkritik"
    segments := ["m", "ə", "ŋ", "k", "r", "i", "t", "i", "k"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def mengritik : Form Cell :=
  { id := "sneddon1996_mengritik"
    lexeme := Lexemes.mengritik
    cell := {}
    form := "mengritik"
    segments := ["m", "ə", "ŋ", "r", "i", "t", "i", "k"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def pengaruh : Form Cell :=
  { id := "sneddon1996_pengaruh"
    lexeme := Lexemes.pengaruh
    cell := {}
    form := "pengaruh"
    segments := ["p", "ə", "ŋ", "a", "r", "u", "h"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def mempengaruhi : Form Cell :=
  { id := "sneddon1996_mempengaruhi"
    lexeme := Lexemes.mempengaruhi
    cell := {}
    form := "mempengaruhi"
    segments := ["m", "ə", "m", "p", "ə", "ŋ", "a", "r", "u", "h", "i"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def punya : Form Cell :=
  { id := "sneddon1996_punya"
    lexeme := Lexemes.punya
    cell := {}
    form := "punya"
    segments := ["p", "u", "ɲ", "a"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def mempunyai : Form Cell :=
  { id := "sneddon1996_mempunyai"
    lexeme := Lexemes.mempunyai
    cell := {}
    form := "mempunyai"
    segments := ["m", "ə", "m", "p", "u", "ɲ", "a", "i"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def kaji : Form Cell :=
  { id := "sneddon1996_kaji"
    lexeme := Lexemes.kaji
    cell := {}
    form := "kaji"
    segments := ["k", "a", "d̠ʒ", "i"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def mengaji : Form Cell :=
  { id := "sneddon1996_mengaji"
    lexeme := Lexemes.mengaji
    cell := {}
    form := "mengaji"
    segments := ["m", "ə", "ŋ", "a", "d̠ʒ", "i"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def mengkaji : Form Cell :=
  { id := "sneddon1996_mengkaji"
    lexeme := Lexemes.mengkaji
    cell := {}
    form := "mengkaji"
    segments := ["m", "ə", "ŋ", "k", "a", "d̠ʒ", "i"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def pengajian : Form Cell :=
  { id := "sneddon1996_pengajian"
    lexeme := Lexemes.pengajian
    cell := {}
    form := "pengajian"
    segments := ["p", "ə", "ŋ", "a", "d̠ʒ", "i", "a", "n"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def pengkajian : Form Cell :=
  { id := "sneddon1996_pengkajian"
    lexeme := Lexemes.pengkajian
    cell := {}
    form := "pengkajian"
    segments := ["p", "ə", "ŋ", "k", "a", "d̠ʒ", "i", "a", "n"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def penglihatan : Form Cell :=
  { id := "sneddon1996_penglihatan"
    lexeme := Lexemes.penglihatan
    cell := {}
    form := "penglihatan"
    segments := ["p", "ə", "ŋ", "l", "i", "h", "a", "t", "a", "n"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def rajin : Form Cell :=
  { id := "sneddon1996_rajin"
    lexeme := Lexemes.rajin
    cell := {}
    form := "rajin"
    segments := ["r", "a", "d̠ʒ", "i", "n"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def pengrajin : Form Cell :=
  { id := "sneddon1996_pengrajin"
    lexeme := Lexemes.pengrajin
    cell := {}
    form := "pengrajin"
    segments := ["p", "ə", "ŋ", "r", "a", "d̠ʒ", "i", "n"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def perajin : Form Cell :=
  { id := "sneddon1996_perajin"
    lexeme := Lexemes.perajin
    cell := {}
    form := "perajin"
    segments := ["p", "ə", "r", "a", "d̠ʒ", "i", "n"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def lepas : Form Cell :=
  { id := "sneddon1996_lepas"
    lexeme := Lexemes.lepas
    cell := {}
    form := "lepas"
    segments := ["l", "ə", "p", "a", "s"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def penglepasan : Form Cell :=
  { id := "sneddon1996_penglepasan"
    lexeme := Lexemes.penglepasan
    cell := {}
    form := "penglepasan"
    segments := ["p", "ə", "ŋ", "l", "ə", "p", "a", "s", "a", "n"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def pelepasan : Form Cell :=
  { id := "sneddon1996_pelepasan"
    lexeme := Lexemes.pelepasan
    cell := {}
    form := "pelepasan"
    segments := ["p", "ə", "l", "ə", "p", "a", "s", "a", "n"]
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] }

def syair : Form Cell :=
  { id := "sneddon1996_syair"
    lexeme := Lexemes.syair
    cell := {}
    form := "syair"
    segments := ["ʃ", "a", "i", "r"]
    source := [
      ⟨"sneddon-1996", "p. 13"⟩
    ] }

def menyair : Form Cell :=
  { id := "sneddon1996_menyair"
    lexeme := Lexemes.menyair
    cell := {}
    form := "menyair"
    segments := ["m", "ə", "ɲ", "a", "i", "r"]
    source := [
      ⟨"sneddon-1996", "p. 13"⟩
    ] }

def penyair : Form Cell :=
  { id := "sneddon1996_penyair"
    lexeme := Lexemes.penyair
    cell := {}
    form := "penyair"
    segments := ["p", "ə", "ɲ", "a", "i", "r"]
    source := [
      ⟨"sneddon-1996", "p. 13"⟩
    ] }

def besar : Form Cell :=
  { id := "sneddon1996_besar"
    lexeme := Lexemes.besar
    cell := {}
    form := "besar"
    segments := ["b", "ə", "s", "a", "r"]
    source := [
      ⟨"sneddon-1996", "p. 26"⟩
    ] }

def memperbesar : Form Cell :=
  { id := "sneddon1996_memperbesar"
    lexeme := Lexemes.memperbesar
    cell := {}
    form := "memperbesar"
    segments := ["m", "ə", "m", "p", "ə", "r", "b", "ə", "s", "a", "r"]
    source := [
      ⟨"sneddon-1996", "p. 26"⟩
    ] }

/-- The source's analysis of a form, its parse rather than data. -/
structure Analysis where
  /-- The form analysed. -/
  form : Form Cell
  /-- The `Prefix` column, the prefix the grammar attaches to the base. -/
  pre : Option Prefix := none
  /-- The `Inner` column, the prefix the grammar puts between that prefix and the base. -/
  inner : Option Inner := none
  /-- The `Suffix` column, the suffix the grammar attaches after the base. -/
  suffix : Option Suffix := none
  /-- The `Origin` column, the grammar's statement of where the word comes from. -/
  origin : Option Origin := none
  deriving DecidableEq, Repr

def renang.analysis : Analysis :=
  { form := renang }

def berenang.analysis : Analysis :=
  { form := berenang,
    pre := some Prefix.ber }

def rusak.analysis : Analysis :=
  { form := rusak }

def perusak.analysis : Analysis :=
  { form := perusak,
    pre := some Prefix.per }

def rasa.analysis : Analysis :=
  { form := rasa }

def terasa.analysis : Analysis :=
  { form := terasa,
    pre := some Prefix.ter }

def serta.analysis : Analysis :=
  { form := serta }

def beserta.analysis : Analysis :=
  { form := beserta,
    pre := some Prefix.ber }

def terbang.analysis : Analysis :=
  { form := terbang }

def beterbangan.analysis : Analysis :=
  { form := beterbangan,
    pre := some Prefix.ber,
    suffix := some Suffix.an }

def kerja.analysis : Analysis :=
  { form := kerja }

def pekerjaan.analysis : Analysis :=
  { form := pekerjaan,
    pre := some Prefix.per,
    suffix := some Suffix.an }

def pergok.analysis : Analysis :=
  { form := pergok }

def tepergok.analysis : Analysis :=
  { form := tepergok,
    pre := some Prefix.ter }

def percaya.analysis : Analysis :=
  { form := percaya }

def tepercaya.analysis : Analysis :=
  { form := tepercaya,
    pre := some Prefix.ter }

def terpercaya.analysis : Analysis :=
  { form := terpercaya,
    pre := some Prefix.ter }

def lanjur.analysis : Analysis :=
  { form := lanjur }

def telanjur.analysis : Analysis :=
  { form := telanjur,
    pre := some Prefix.ter }

def terlanjur.analysis : Analysis :=
  { form := terlanjur,
    pre := some Prefix.ter }

def lantar.analysis : Analysis :=
  { form := lantar }

def telantar.analysis : Analysis :=
  { form := telantar,
    pre := some Prefix.ter }

def terlantar.analysis : Analysis :=
  { form := terlantar,
    pre := some Prefix.ter }

def ajar.analysis : Analysis :=
  { form := ajar }

def belajar.analysis : Analysis :=
  { form := belajar,
    pre := some Prefix.ber }

def pelajaran.analysis : Analysis :=
  { form := pelajaran,
    pre := some Prefix.per,
    suffix := some Suffix.an }

def mengajar.analysis : Analysis :=
  { form := mengajar,
    pre := some Prefix.meN }

def ekspor.analysis : Analysis :=
  { form := ekspor }

def mengekspor.analysis : Analysis :=
  { form := mengekspor,
    pre := some Prefix.meN }

def erang.analysis : Analysis :=
  { form := erang }

def mengerang.analysis : Analysis :=
  { form := mengerang,
    pre := some Prefix.meN }

def olah.analysis : Analysis :=
  { form := olah }

def mengolah.analysis : Analysis :=
  { form := mengolah,
    pre := some Prefix.meN }

def urus.analysis : Analysis :=
  { form := urus }

def mengurus.analysis : Analysis :=
  { form := mengurus,
    pre := some Prefix.meN }

def beli.analysis : Analysis :=
  { form := beli }

def membeli.analysis : Analysis :=
  { form := membeli,
    pre := some Prefix.meN }

def pakai.analysis : Analysis :=
  { form := pakai }

def memakai.analysis : Analysis :=
  { form := memakai,
    pre := some Prefix.meN }

def fitnah.analysis : Analysis :=
  { form := fitnah }

def memfitnah.analysis : Analysis :=
  { form := memfitnah,
    pre := some Prefix.meN }

def dengar.analysis : Analysis :=
  { form := dengar }

def mendengar.analysis : Analysis :=
  { form := mendengar,
    pre := some Prefix.meN }

def tulis.analysis : Analysis :=
  { form := tulis }

def menulis.analysis : Analysis :=
  { form := menulis,
    pre := some Prefix.meN }

def cari.analysis : Analysis :=
  { form := cari }

def mencari.analysis : Analysis :=
  { form := mencari,
    pre := some Prefix.meN }

def jual.analysis : Analysis :=
  { form := jual }

def menjual.analysis : Analysis :=
  { form := menjual,
    pre := some Prefix.meN }

def syarat.analysis : Analysis :=
  { form := syarat }

def mensyaratkan.analysis : Analysis :=
  { form := mensyaratkan,
    pre := some Prefix.meN,
    suffix := some Suffix.kan }

def ziarah.analysis : Analysis :=
  { form := ziarah }

def menziarahi.analysis : Analysis :=
  { form := menziarahi,
    pre := some Prefix.meN,
    suffix := some Suffix.i }

def sewa.analysis : Analysis :=
  { form := sewa }

def menyewa.analysis : Analysis :=
  { form := menyewa,
    pre := some Prefix.meN }

def ganggu.analysis : Analysis :=
  { form := ganggu }

def mengganggu.analysis : Analysis :=
  { form := mengganggu,
    pre := some Prefix.meN }

def kirim.analysis : Analysis :=
  { form := kirim }

def mengirim.analysis : Analysis :=
  { form := mengirim,
    pre := some Prefix.meN }

def hilang.analysis : Analysis :=
  { form := hilang }

def menghilang.analysis : Analysis :=
  { form := menghilang,
    pre := some Prefix.meN }

def khawatir.analysis : Analysis :=
  { form := khawatir }

def mengkhawatirkan.analysis : Analysis :=
  { form := mengkhawatirkan,
    pre := some Prefix.meN,
    suffix := some Suffix.kan }

def lihat.analysis : Analysis :=
  { form := lihat }

def melihat.analysis : Analysis :=
  { form := melihat,
    pre := some Prefix.meN }

def merasa.analysis : Analysis :=
  { form := merasa,
    pre := some Prefix.meN }

def masak.analysis : Analysis :=
  { form := masak }

def memasak.analysis : Analysis :=
  { form := memasak,
    pre := some Prefix.meN }

def nanti.analysis : Analysis :=
  { form := nanti }

def menanti.analysis : Analysis :=
  { form := menanti,
    pre := some Prefix.meN }

def nyanyi.analysis : Analysis :=
  { form := nyanyi }

def menyanyi.analysis : Analysis :=
  { form := menyanyi,
    pre := some Prefix.meN }

def nganga.analysis : Analysis :=
  { form := nganga }

def menganga.analysis : Analysis :=
  { form := menganga,
    pre := some Prefix.meN }

def wakil.analysis : Analysis :=
  { form := wakil }

def mewakili.analysis : Analysis :=
  { form := mewakili,
    pre := some Prefix.meN,
    suffix := some Suffix.i }

def yakin.analysis : Analysis :=
  { form := yakin }

def meyakini.analysis : Analysis :=
  { form := meyakini,
    pre := some Prefix.meN,
    suffix := some Suffix.i }

def karang.analysis : Analysis :=
  { form := karang }

def mengarang_karang.analysis : Analysis :=
  { form := mengarang_karang,
    pre := some Prefix.meN }

def arang.analysis : Analysis :=
  { form := arang }

def mengarang_arang.analysis : Analysis :=
  { form := mengarang_arang,
    pre := some Prefix.meN }

def penulis.analysis : Analysis :=
  { form := penulis,
    pre := some Prefix.peN }

def penulisan.analysis : Analysis :=
  { form := penulisan,
    pre := some Prefix.peN,
    suffix := some Suffix.an }

def lebar.analysis : Analysis :=
  { form := lebar }

def memperlebar.analysis : Analysis :=
  { form := memperlebar,
    pre := some Prefix.meN,
    inner := some Inner.per }

def oleh.analysis : Analysis :=
  { form := oleh }

def memperoleh.analysis : Analysis :=
  { form := memperoleh,
    pre := some Prefix.meN,
    inner := some Inner.per }

def mempercayai.analysis : Analysis :=
  { form := mempercayai,
    pre := some Prefix.meN,
    suffix := some Suffix.i }

def mempergoki.analysis : Analysis :=
  { form := mempergoki,
    pre := some Prefix.meN,
    suffix := some Suffix.i }

def memergoki.analysis : Analysis :=
  { form := memergoki,
    pre := some Prefix.meN,
    suffix := some Suffix.i }

def percik.analysis : Analysis :=
  { form := percik }

def memerciki.analysis : Analysis :=
  { form := memerciki,
    pre := some Prefix.meN,
    suffix := some Suffix.i }

def satu.analysis : Analysis :=
  { form := satu }

def pemersatu.analysis : Analysis :=
  { form := pemersatu,
    pre := some Prefix.peN,
    inner := some Inner.per }

def pemerolehan.analysis : Analysis :=
  { form := pemerolehan,
    pre := some Prefix.peN,
    inner := some Inner.per,
    suffix := some Suffix.an }

def perkosa.analysis : Analysis :=
  { form := perkosa }

def pemerkosa.analysis : Analysis :=
  { form := pemerkosa,
    pre := some Prefix.peN }

def proklamasi.analysis : Analysis :=
  { form := proklamasi,
    origin := some Origin.borrowed }

def memproklamasikan.analysis : Analysis :=
  { form := memproklamasikan,
    pre := some Prefix.meN,
    suffix := some Suffix.kan }

def traktir.analysis : Analysis :=
  { form := traktir,
    origin := some Origin.borrowed }

def mentraktir.analysis : Analysis :=
  { form := mentraktir,
    pre := some Prefix.meN }

def swadaya.analysis : Analysis :=
  { form := swadaya,
    origin := some Origin.borrowed }

def menswadayakan.analysis : Analysis :=
  { form := menswadayakan,
    pre := some Prefix.meN,
    suffix := some Suffix.kan }

def klasifikasi.analysis : Analysis :=
  { form := klasifikasi,
    origin := some Origin.borrowed }

def mengklasifikasikan.analysis : Analysis :=
  { form := mengklasifikasikan,
    pre := some Prefix.meN,
    suffix := some Suffix.kan }

def protes.analysis : Analysis :=
  { form := protes,
    origin := some Origin.borrowed }

def memprotes.analysis : Analysis :=
  { form := memprotes,
    pre := some Prefix.meN }

def memrotes.analysis : Analysis :=
  { form := memrotes,
    pre := some Prefix.meN }

def taat.analysis : Analysis :=
  { form := taat,
    origin := some Origin.borrowed }

def mentaati.analysis : Analysis :=
  { form := mentaati,
    pre := some Prefix.meN,
    suffix := some Suffix.i }

def menaati.analysis : Analysis :=
  { form := menaati,
    pre := some Prefix.meN,
    suffix := some Suffix.i }

def sukses.analysis : Analysis :=
  { form := sukses,
    origin := some Origin.borrowed }

def mensukseskan.analysis : Analysis :=
  { form := mensukseskan,
    pre := some Prefix.meN,
    suffix := some Suffix.kan }

def menyukseskan.analysis : Analysis :=
  { form := menyukseskan,
    pre := some Prefix.meN,
    suffix := some Suffix.kan }

def kritik.analysis : Analysis :=
  { form := kritik,
    origin := some Origin.borrowed }

def mengkritik.analysis : Analysis :=
  { form := mengkritik,
    pre := some Prefix.meN }

def mengritik.analysis : Analysis :=
  { form := mengritik,
    pre := some Prefix.meN }

def pengaruh.analysis : Analysis :=
  { form := pengaruh }

def mempengaruhi.analysis : Analysis :=
  { form := mempengaruhi,
    pre := some Prefix.meN,
    suffix := some Suffix.i }

def punya.analysis : Analysis :=
  { form := punya }

def mempunyai.analysis : Analysis :=
  { form := mempunyai,
    pre := some Prefix.meN,
    suffix := some Suffix.i }

def kaji.analysis : Analysis :=
  { form := kaji }

def mengaji.analysis : Analysis :=
  { form := mengaji,
    pre := some Prefix.meN }

def mengkaji.analysis : Analysis :=
  { form := mengkaji,
    pre := some Prefix.meN }

def pengajian.analysis : Analysis :=
  { form := pengajian,
    pre := some Prefix.peN,
    suffix := some Suffix.an }

def pengkajian.analysis : Analysis :=
  { form := pengkajian,
    pre := some Prefix.peN,
    suffix := some Suffix.an }

def penglihatan.analysis : Analysis :=
  { form := penglihatan,
    pre := some Prefix.peN,
    suffix := some Suffix.an }

def rajin.analysis : Analysis :=
  { form := rajin }

def pengrajin.analysis : Analysis :=
  { form := pengrajin,
    pre := some Prefix.peN }

def perajin.analysis : Analysis :=
  { form := perajin,
    pre := some Prefix.peN }

def lepas.analysis : Analysis :=
  { form := lepas }

def penglepasan.analysis : Analysis :=
  { form := penglepasan,
    pre := some Prefix.peN,
    suffix := some Suffix.an }

def pelepasan.analysis : Analysis :=
  { form := pelepasan,
    pre := some Prefix.peN,
    suffix := some Suffix.an }

def syair.analysis : Analysis :=
  { form := syair }

def menyair.analysis : Analysis :=
  { form := menyair,
    pre := some Prefix.meN }

def penyair.analysis : Analysis :=
  { form := penyair,
    pre := some Prefix.peN }

def besar.analysis : Analysis :=
  { form := besar }

def memperbesar.analysis : Analysis :=
  { form := memperbesar,
    pre := some Prefix.meN,
    inner := some Inner.per }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.renang, Lexemes.berenang, Lexemes.rusak, Lexemes.perusak,
  Lexemes.rasa, Lexemes.terasa, Lexemes.serta, Lexemes.beserta, Lexemes.terbang,
  Lexemes.beterbangan, Lexemes.kerja, Lexemes.pekerjaan, Lexemes.pergok, Lexemes.tepergok,
  Lexemes.percaya, Lexemes.tepercaya, Lexemes.terpercaya, Lexemes.lanjur, Lexemes.telanjur,
  Lexemes.terlanjur, Lexemes.lantar, Lexemes.telantar, Lexemes.terlantar, Lexemes.ajar,
  Lexemes.belajar, Lexemes.pelajaran, Lexemes.mengajar, Lexemes.ekspor, Lexemes.mengekspor,
  Lexemes.erang, Lexemes.mengerang, Lexemes.olah, Lexemes.mengolah, Lexemes.urus, Lexemes.mengurus,
  Lexemes.beli, Lexemes.membeli, Lexemes.pakai, Lexemes.memakai, Lexemes.fitnah, Lexemes.memfitnah,
  Lexemes.dengar, Lexemes.mendengar, Lexemes.tulis, Lexemes.menulis, Lexemes.cari, Lexemes.mencari,
  Lexemes.jual, Lexemes.menjual, Lexemes.syarat, Lexemes.mensyaratkan, Lexemes.ziarah,
  Lexemes.menziarahi, Lexemes.sewa, Lexemes.menyewa, Lexemes.ganggu, Lexemes.mengganggu,
  Lexemes.kirim, Lexemes.mengirim, Lexemes.hilang, Lexemes.menghilang, Lexemes.khawatir,
  Lexemes.mengkhawatirkan, Lexemes.lihat, Lexemes.melihat, Lexemes.merasa, Lexemes.masak,
  Lexemes.memasak, Lexemes.nanti, Lexemes.menanti, Lexemes.nyanyi, Lexemes.menyanyi, Lexemes.nganga,
  Lexemes.menganga, Lexemes.wakil, Lexemes.mewakili, Lexemes.yakin, Lexemes.meyakini,
  Lexemes.karang, Lexemes.mengarang_karang, Lexemes.arang, Lexemes.mengarang_arang, Lexemes.penulis,
  Lexemes.penulisan, Lexemes.lebar, Lexemes.memperlebar, Lexemes.oleh, Lexemes.memperoleh,
  Lexemes.mempercayai, Lexemes.mempergoki, Lexemes.memergoki, Lexemes.percik, Lexemes.memerciki,
  Lexemes.satu, Lexemes.pemersatu, Lexemes.pemerolehan, Lexemes.perkosa, Lexemes.pemerkosa,
  Lexemes.proklamasi, Lexemes.memproklamasikan, Lexemes.traktir, Lexemes.mentraktir,
  Lexemes.swadaya, Lexemes.menswadayakan, Lexemes.klasifikasi, Lexemes.mengklasifikasikan,
  Lexemes.protes, Lexemes.memprotes, Lexemes.memrotes, Lexemes.taat, Lexemes.mentaati,
  Lexemes.menaati, Lexemes.sukses, Lexemes.mensukseskan, Lexemes.menyukseskan, Lexemes.kritik,
  Lexemes.mengkritik, Lexemes.mengritik, Lexemes.pengaruh, Lexemes.mempengaruhi, Lexemes.punya,
  Lexemes.mempunyai, Lexemes.kaji, Lexemes.mengaji, Lexemes.mengkaji, Lexemes.pengajian,
  Lexemes.pengkajian, Lexemes.penglihatan, Lexemes.rajin, Lexemes.pengrajin, Lexemes.perajin,
  Lexemes.lepas, Lexemes.penglepasan, Lexemes.pelepasan, Lexemes.syair, Lexemes.menyair,
  Lexemes.penyair, Lexemes.besar, Lexemes.memperbesar]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [renang, berenang, rusak, perusak, rasa, terasa, serta, beserta,
  terbang, beterbangan, kerja, pekerjaan, pergok, tepergok, percaya, tepercaya, terpercaya, lanjur,
  telanjur, terlanjur, lantar, telantar, terlantar, ajar, belajar, pelajaran, mengajar, ekspor,
  mengekspor, erang, mengerang, olah, mengolah, urus, mengurus, beli, membeli, pakai, memakai,
  fitnah, memfitnah, dengar, mendengar, tulis, menulis, cari, mencari, jual, menjual, syarat,
  mensyaratkan, ziarah, menziarahi, sewa, menyewa, ganggu, mengganggu, kirim, mengirim, hilang,
  menghilang, khawatir, mengkhawatirkan, lihat, melihat, merasa, masak, memasak, nanti, menanti,
  nyanyi, menyanyi, nganga, menganga, wakil, mewakili, yakin, meyakini, karang, mengarang_karang,
  arang, mengarang_arang, penulis, penulisan, lebar, memperlebar, oleh, memperoleh, mempercayai,
  mempergoki, memergoki, percik, memerciki, satu, pemersatu, pemerolehan, perkosa, pemerkosa,
  proklamasi, memproklamasikan, traktir, mentraktir, swadaya, menswadayakan, klasifikasi,
  mengklasifikasikan, protes, memprotes, memrotes, taat, mentaati, menaati, sukses, mensukseskan,
  menyukseskan, kritik, mengkritik, mengritik, pengaruh, mempengaruhi, punya, mempunyai, kaji,
  mengaji, mengkaji, pengajian, pengkajian, penglihatan, rajin, pengrajin, perajin, lepas,
  penglepasan, pelepasan, syair, menyair, penyair, besar, memperbesar]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := [
  { id := "sneddon1996_renang_berenang", form := renang, target := berenang, relation := "ber-",
    source := [
      ⟨"sneddon-1996", "p. 8"⟩
    ] },
  { id := "sneddon1996_rusak_perusak", form := rusak, target := perusak, relation := "per-",
    source := [
      ⟨"sneddon-1996", "p. 8"⟩
    ] },
  { id := "sneddon1996_rasa_terasa", form := rasa, target := terasa, relation := "ter-", source := [
      ⟨"sneddon-1996", "p. 8"⟩
    ] },
  { id := "sneddon1996_serta_beserta", form := serta, target := beserta, relation := "ber-",
    source := [
      ⟨"sneddon-1996", "p. 8"⟩
    ] },
  { id := "sneddon1996_terbang_beterbangan", form := terbang, target := beterbangan,
    relation := "ber- -an", source := [
      ⟨"sneddon-1996", "p. 8"⟩
    ] },
  { id := "sneddon1996_kerja_pekerjaan", form := kerja, target := pekerjaan, relation := "per- -an",
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_pergok_tepergok", form := pergok, target := tepergok, relation := "ter-",
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_percaya_tepercaya", form := percaya, target := tepercaya, relation := "ter-",
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_percaya_terpercaya", form := percaya, target := terpercaya,
    relation := "ter-", source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_lanjur_telanjur", form := lanjur, target := telanjur, relation := "ter-",
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_lanjur_terlanjur", form := lanjur, target := terlanjur, relation := "ter-",
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_lantar_telantar", form := lantar, target := telantar, relation := "ter-",
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_lantar_terlantar", form := lantar, target := terlantar, relation := "ter-",
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_ajar_belajar", form := ajar, target := belajar, relation := "ber-",
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_ajar_pelajaran", form := ajar, target := pelajaran, relation := "per- -an",
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_ajar_mengajar", form := ajar, target := mengajar, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_ekspor_mengekspor", form := ekspor, target := mengekspor, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_erang_mengerang", form := erang, target := mengerang, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_olah_mengolah", form := olah, target := mengolah, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_urus_mengurus", form := urus, target := mengurus, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_beli_membeli", form := beli, target := membeli, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_pakai_memakai", form := pakai, target := memakai, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_fitnah_memfitnah", form := fitnah, target := memfitnah, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_dengar_mendengar", form := dengar, target := mendengar, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_tulis_menulis", form := tulis, target := menulis, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_cari_mencari", form := cari, target := mencari, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_jual_menjual", form := jual, target := menjual, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_syarat_mensyaratkan", form := syarat, target := mensyaratkan,
    relation := "meN- -kan", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_ziarah_menziarahi", form := ziarah, target := menziarahi,
    relation := "meN- -i", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_sewa_menyewa", form := sewa, target := menyewa, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_ganggu_mengganggu", form := ganggu, target := mengganggu, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_kirim_mengirim", form := kirim, target := mengirim, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_hilang_menghilang", form := hilang, target := menghilang, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_khawatir_mengkhawatirkan", form := khawatir, target := mengkhawatirkan,
    relation := "meN- -kan", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_lihat_melihat", form := lihat, target := melihat, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_rasa_merasa", form := rasa, target := merasa, relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_masak_memasak", form := masak, target := memasak, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_nanti_menanti", form := nanti, target := menanti, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_nyanyi_menyanyi", form := nyanyi, target := menyanyi, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_nganga_menganga", form := nganga, target := menganga, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_wakil_mewakili", form := wakil, target := mewakili, relation := "meN- -i",
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_yakin_meyakini", form := yakin, target := meyakini, relation := "meN- -i",
    source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_karang_mengarang_karang", form := karang, target := mengarang_karang,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_arang_mengarang_arang", form := arang, target := mengarang_arang,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_tulis_penulis", form := tulis, target := penulis, relation := "peN-",
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_tulis_penulisan", form := tulis, target := penulisan, relation := "peN- -an",
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_lebar_memperlebar", form := lebar, target := memperlebar,
    relation := "meN- per-", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_oleh_memperoleh", form := oleh, target := memperoleh,
    relation := "meN- per-", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_percaya_mempercayai", form := percaya, target := mempercayai,
    relation := "meN- -i", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_pergok_mempergoki", form := pergok, target := mempergoki,
    relation := "meN- -i", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_pergok_memergoki", form := pergok, target := memergoki,
    relation := "meN- -i", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_percik_memerciki", form := percik, target := memerciki,
    relation := "meN- -i", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_satu_pemersatu", form := satu, target := pemersatu, relation := "peN- per-",
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_oleh_pemerolehan", form := oleh, target := pemerolehan,
    relation := "peN- per- -an", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_perkosa_pemerkosa", form := perkosa, target := pemerkosa, relation := "peN-",
    source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_proklamasi_memproklamasikan", form := proklamasi, target := memproklamasikan,
    relation := "meN- -kan", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_traktir_mentraktir", form := traktir, target := mentraktir,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_swadaya_menswadayakan", form := swadaya, target := menswadayakan,
    relation := "meN- -kan", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_klasifikasi_mengklasifikasikan", form := klasifikasi,
    target := mengklasifikasikan, relation := "meN- -kan", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_protes_memprotes", form := protes, target := memprotes, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_protes_memrotes", form := protes, target := memrotes, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_taat_mentaati", form := taat, target := mentaati, relation := "meN- -i",
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_taat_menaati", form := taat, target := menaati, relation := "meN- -i",
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_sukses_mensukseskan", form := sukses, target := mensukseskan,
    relation := "meN- -kan", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_sukses_menyukseskan", form := sukses, target := menyukseskan,
    relation := "meN- -kan", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_kritik_mengkritik", form := kritik, target := mengkritik, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_kritik_mengritik", form := kritik, target := mengritik, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_pengaruh_mempengaruhi", form := pengaruh, target := mempengaruhi,
    relation := "meN- -i", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_punya_mempunyai", form := punya, target := mempunyai, relation := "meN- -i",
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_kaji_mengaji", form := kaji, target := mengaji, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_kaji_mengkaji", form := kaji, target := mengkaji, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_kaji_pengajian", form := kaji, target := pengajian, relation := "peN- -an",
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_kaji_pengkajian", form := kaji, target := pengkajian, relation := "peN- -an",
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_lihat_penglihatan", form := lihat, target := penglihatan,
    relation := "peN- -an", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_rajin_pengrajin", form := rajin, target := pengrajin, relation := "peN-",
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_rajin_perajin", form := rajin, target := perajin, relation := "peN-",
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_lepas_penglepasan", form := lepas, target := penglepasan,
    relation := "peN- -an", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_lepas_pelepasan", form := lepas, target := pelepasan, relation := "peN- -an",
    source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_syair_menyair", form := syair, target := menyair, relation := "meN-",
    source := [
      ⟨"sneddon-1996", "p. 13"⟩
    ] },
  { id := "sneddon1996_syair_penyair", form := syair, target := penyair, relation := "peN-",
    source := [
      ⟨"sneddon-1996", "p. 13"⟩
    ] },
  { id := "sneddon1996_besar_memperbesar", form := besar, target := memperbesar,
    relation := "meN- per-", source := [
      ⟨"sneddon-1996", "p. 26"⟩
    ] }]

/-- Every relation the sources assert, between the forms' analyses. -/
def analysisRelations : List (FormRelation Analysis) := [
  { id := "sneddon1996_renang_berenang", form := renang.analysis, target := berenang.analysis,
    relation := "ber-", source := [
      ⟨"sneddon-1996", "p. 8"⟩
    ] },
  { id := "sneddon1996_rusak_perusak", form := rusak.analysis, target := perusak.analysis,
    relation := "per-", source := [
      ⟨"sneddon-1996", "p. 8"⟩
    ] },
  { id := "sneddon1996_rasa_terasa", form := rasa.analysis, target := terasa.analysis,
    relation := "ter-", source := [
      ⟨"sneddon-1996", "p. 8"⟩
    ] },
  { id := "sneddon1996_serta_beserta", form := serta.analysis, target := beserta.analysis,
    relation := "ber-", source := [
      ⟨"sneddon-1996", "p. 8"⟩
    ] },
  { id := "sneddon1996_terbang_beterbangan", form := terbang.analysis,
    target := beterbangan.analysis, relation := "ber- -an", source := [
      ⟨"sneddon-1996", "p. 8"⟩
    ] },
  { id := "sneddon1996_kerja_pekerjaan", form := kerja.analysis, target := pekerjaan.analysis,
    relation := "per- -an", source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_pergok_tepergok", form := pergok.analysis, target := tepergok.analysis,
    relation := "ter-", source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_percaya_tepercaya", form := percaya.analysis, target := tepercaya.analysis,
    relation := "ter-", source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_percaya_terpercaya", form := percaya.analysis, target := terpercaya.analysis,
    relation := "ter-", source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_lanjur_telanjur", form := lanjur.analysis, target := telanjur.analysis,
    relation := "ter-", source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_lanjur_terlanjur", form := lanjur.analysis, target := terlanjur.analysis,
    relation := "ter-", source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_lantar_telantar", form := lantar.analysis, target := telantar.analysis,
    relation := "ter-", source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_lantar_terlantar", form := lantar.analysis, target := terlantar.analysis,
    relation := "ter-", source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_ajar_belajar", form := ajar.analysis, target := belajar.analysis,
    relation := "ber-", source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_ajar_pelajaran", form := ajar.analysis, target := pelajaran.analysis,
    relation := "per- -an", source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_ajar_mengajar", form := ajar.analysis, target := mengajar.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_ekspor_mengekspor", form := ekspor.analysis, target := mengekspor.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_erang_mengerang", form := erang.analysis, target := mengerang.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_olah_mengolah", form := olah.analysis, target := mengolah.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_urus_mengurus", form := urus.analysis, target := mengurus.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_beli_membeli", form := beli.analysis, target := membeli.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_pakai_memakai", form := pakai.analysis, target := memakai.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 9"⟩
    ] },
  { id := "sneddon1996_fitnah_memfitnah", form := fitnah.analysis, target := memfitnah.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_dengar_mendengar", form := dengar.analysis, target := mendengar.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_tulis_menulis", form := tulis.analysis, target := menulis.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_cari_mencari", form := cari.analysis, target := mencari.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_jual_menjual", form := jual.analysis, target := menjual.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_syarat_mensyaratkan", form := syarat.analysis,
    target := mensyaratkan.analysis, relation := "meN- -kan", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_ziarah_menziarahi", form := ziarah.analysis, target := menziarahi.analysis,
    relation := "meN- -i", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_sewa_menyewa", form := sewa.analysis, target := menyewa.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_ganggu_mengganggu", form := ganggu.analysis, target := mengganggu.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_kirim_mengirim", form := kirim.analysis, target := mengirim.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_hilang_menghilang", form := hilang.analysis, target := menghilang.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_khawatir_mengkhawatirkan", form := khawatir.analysis,
    target := mengkhawatirkan.analysis, relation := "meN- -kan", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_lihat_melihat", form := lihat.analysis, target := melihat.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_rasa_merasa", form := rasa.analysis, target := merasa.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_masak_memasak", form := masak.analysis, target := memasak.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_nanti_menanti", form := nanti.analysis, target := menanti.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_nyanyi_menyanyi", form := nyanyi.analysis, target := menyanyi.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_nganga_menganga", form := nganga.analysis, target := menganga.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_wakil_mewakili", form := wakil.analysis, target := mewakili.analysis,
    relation := "meN- -i", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_yakin_meyakini", form := yakin.analysis, target := meyakini.analysis,
    relation := "meN- -i", source := [
      ⟨"sneddon-1996", "p. 10"⟩
    ] },
  { id := "sneddon1996_karang_mengarang_karang", form := karang.analysis,
    target := mengarang_karang.analysis, relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_arang_mengarang_arang", form := arang.analysis,
    target := mengarang_arang.analysis, relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_tulis_penulis", form := tulis.analysis, target := penulis.analysis,
    relation := "peN-", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_tulis_penulisan", form := tulis.analysis, target := penulisan.analysis,
    relation := "peN- -an", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_lebar_memperlebar", form := lebar.analysis, target := memperlebar.analysis,
    relation := "meN- per-", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_oleh_memperoleh", form := oleh.analysis, target := memperoleh.analysis,
    relation := "meN- per-", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_percaya_mempercayai", form := percaya.analysis,
    target := mempercayai.analysis, relation := "meN- -i", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_pergok_mempergoki", form := pergok.analysis, target := mempergoki.analysis,
    relation := "meN- -i", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_pergok_memergoki", form := pergok.analysis, target := memergoki.analysis,
    relation := "meN- -i", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_percik_memerciki", form := percik.analysis, target := memerciki.analysis,
    relation := "meN- -i", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_satu_pemersatu", form := satu.analysis, target := pemersatu.analysis,
    relation := "peN- per-", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_oleh_pemerolehan", form := oleh.analysis, target := pemerolehan.analysis,
    relation := "peN- per- -an", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_perkosa_pemerkosa", form := perkosa.analysis, target := pemerkosa.analysis,
    relation := "peN-", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_proklamasi_memproklamasikan", form := proklamasi.analysis,
    target := memproklamasikan.analysis, relation := "meN- -kan", source := [
      ⟨"sneddon-1996", "p. 11"⟩
    ] },
  { id := "sneddon1996_traktir_mentraktir", form := traktir.analysis, target := mentraktir.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_swadaya_menswadayakan", form := swadaya.analysis,
    target := menswadayakan.analysis, relation := "meN- -kan", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_klasifikasi_mengklasifikasikan", form := klasifikasi.analysis,
    target := mengklasifikasikan.analysis, relation := "meN- -kan", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_protes_memprotes", form := protes.analysis, target := memprotes.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_protes_memrotes", form := protes.analysis, target := memrotes.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_taat_mentaati", form := taat.analysis, target := mentaati.analysis,
    relation := "meN- -i", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_taat_menaati", form := taat.analysis, target := menaati.analysis,
    relation := "meN- -i", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_sukses_mensukseskan", form := sukses.analysis,
    target := mensukseskan.analysis, relation := "meN- -kan", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_sukses_menyukseskan", form := sukses.analysis,
    target := menyukseskan.analysis, relation := "meN- -kan", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_kritik_mengkritik", form := kritik.analysis, target := mengkritik.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_kritik_mengritik", form := kritik.analysis, target := mengritik.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_pengaruh_mempengaruhi", form := pengaruh.analysis,
    target := mempengaruhi.analysis, relation := "meN- -i", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_punya_mempunyai", form := punya.analysis, target := mempunyai.analysis,
    relation := "meN- -i", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_kaji_mengaji", form := kaji.analysis, target := mengaji.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_kaji_mengkaji", form := kaji.analysis, target := mengkaji.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_kaji_pengajian", form := kaji.analysis, target := pengajian.analysis,
    relation := "peN- -an", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_kaji_pengkajian", form := kaji.analysis, target := pengkajian.analysis,
    relation := "peN- -an", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_lihat_penglihatan", form := lihat.analysis, target := penglihatan.analysis,
    relation := "peN- -an", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_rajin_pengrajin", form := rajin.analysis, target := pengrajin.analysis,
    relation := "peN-", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_rajin_perajin", form := rajin.analysis, target := perajin.analysis,
    relation := "peN-", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_lepas_penglepasan", form := lepas.analysis, target := penglepasan.analysis,
    relation := "peN- -an", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_lepas_pelepasan", form := lepas.analysis, target := pelepasan.analysis,
    relation := "peN- -an", source := [
      ⟨"sneddon-1996", "p. 12"⟩
    ] },
  { id := "sneddon1996_syair_menyair", form := syair.analysis, target := menyair.analysis,
    relation := "meN-", source := [
      ⟨"sneddon-1996", "p. 13"⟩
    ] },
  { id := "sneddon1996_syair_penyair", form := syair.analysis, target := penyair.analysis,
    relation := "peN-", source := [
      ⟨"sneddon-1996", "p. 13"⟩
    ] },
  { id := "sneddon1996_besar_memperbesar", form := besar.analysis, target := memperbesar.analysis,
    relation := "meN- per-", source := [
      ⟨"sneddon-1996", "p. 26"⟩
    ] }]

/-- Every analysis of the data. -/
def analyses : List Analysis := [berenang.analysis, perusak.analysis, terasa.analysis,
  beserta.analysis, beterbangan.analysis, pekerjaan.analysis, tepergok.analysis, tepercaya.analysis,
  terpercaya.analysis, telanjur.analysis, terlanjur.analysis, telantar.analysis, terlantar.analysis,
  belajar.analysis, pelajaran.analysis, mengajar.analysis, mengekspor.analysis, mengerang.analysis,
  mengolah.analysis, mengurus.analysis, membeli.analysis, memakai.analysis, memfitnah.analysis,
  mendengar.analysis, menulis.analysis, mencari.analysis, menjual.analysis, mensyaratkan.analysis,
  menziarahi.analysis, menyewa.analysis, mengganggu.analysis, mengirim.analysis,
  menghilang.analysis, mengkhawatirkan.analysis, melihat.analysis, merasa.analysis,
  memasak.analysis, menanti.analysis, menyanyi.analysis, menganga.analysis, mewakili.analysis,
  meyakini.analysis, mengarang_karang.analysis, mengarang_arang.analysis, penulis.analysis,
  penulisan.analysis, memperlebar.analysis, memperoleh.analysis, mempercayai.analysis,
  mempergoki.analysis, memergoki.analysis, memerciki.analysis, pemersatu.analysis,
  pemerolehan.analysis, pemerkosa.analysis, proklamasi.analysis, memproklamasikan.analysis,
  traktir.analysis, mentraktir.analysis, swadaya.analysis, menswadayakan.analysis,
  klasifikasi.analysis, mengklasifikasikan.analysis, protes.analysis, memprotes.analysis,
  memrotes.analysis, taat.analysis, mentaati.analysis, menaati.analysis, sukses.analysis,
  mensukseskan.analysis, menyukseskan.analysis, kritik.analysis, mengkritik.analysis,
  mengritik.analysis, mempengaruhi.analysis, mempunyai.analysis, mengaji.analysis,
  mengkaji.analysis, pengajian.analysis, pengkajian.analysis, penglihatan.analysis,
  pengrajin.analysis, perajin.analysis, penglepasan.analysis, pelepasan.analysis, menyair.analysis,
  penyair.analysis, memperbesar.analysis]

end Sneddon1996.Wordlist
