module

public import Linglib.Phonology.Tone.Basic
public import Linglib.Phonology.Autosegmental.Melody
public import Linglib.Morphology.Morph

/-!
# Poko Tonal Fragment

Lexical tone data for Poko (Poko-Rawo; Glottolog `rawo1244`, ISO 639-3
`rwa`), a Skou language of Sandaun Province, Papua New Guinea (~100
speakers, [mcpherson-dryer-2021]). Three contrastive tone levels (H,
M, L) plus toneless syllables and floating tones; the TBU is the
syllable. Lexical melodies span `Ø`, `M`, `MH`, `LM`, `LH`, `M^H` and
double-floating `^L∅^H`, with floating L only stem-initial and
floating H only stem-final ([mcpherson-lamont-2026] ex. 3, §2.2);
simple `L` and `H` melodies are absent — [mcpherson-2022] derives the
gap from edge constraints (`NonInitial(H)`, `NonFinal(L)`), while
[mcpherson-lamont-2026] speculate an extreme OCP response.

Just enough stems for the [mcpherson-lamont-2026] tableaux; promote to
a fuller fragment when a second Poko paper arrives.

## Main definitions

* `Poko.Syll` — the stems, one morpheme each (`Syll.morpheme`).
* `Poko.Syll.melody` — each stem's lexical melody: tones, TBU, and
  pre-linking ([rolle-2018] §2.1; the floating H of `/M^H/` stems is
  the unlinked element).
* `Poko.Form` — autosegmental forms (`Form Syll TRN Morph`).
-/

@[expose] public section

namespace Poko

open Autosegmental
open Morphology (Morph)
open Tone (TRN)

/-! ### Syllables -/

/-- Poko syllables for the [mcpherson-lamont-2026] tableaux: fig. 3
    (`kak`, `ri`, `do`); eq. (24) (`nan`, `ri`, `na`); eq. (27)
    (`kak`, `ka`); eq. (30) (`kak`, `ili`); eq. (22a) (`ne`). -/
inductive Syll
  /-- 3sg.m possessive `kāk` (melody `/M^H/`). -/
  | kak
  /-- Pig stem `rī` (melody `/M^H/`). -/
  | ri
  /-- Get verb `dō` (melody `/M^H/`). -/
  | do
  /-- 1sg pronoun `nãn` — possessor 'my' and subject 'I' (melody `/M/`). -/
  | nan
  /-- Eat verb `nã` (melody `/M/`). -/
  | na
  /-- Friend stem `kǎ` (melody `/MH/`, surfacing as a rise; eq. 26a). -/
  | ka
  /-- Bamboo stem `ìlí` (melody `/LH/`; disyllabic in the language,
      collapsed to a single backbone element here; eq. 28a). -/
  | ili
  /-- Make.1sg verb stem `ne` (toneless; eq. 22a). -/
  | ne
  deriving DecidableEq, Repr

/-! ### Morphemes and melodies -/

/-- Stable morpheme per stem, keyed by the syllable's surface form. -/
def Syll.morpheme : Syll → Morph
  | .kak => .root "kak"
  | .ri  => .root "ri"
  | .do  => .root "do"
  | .nan => .root "nan"
  | .na  => .root "na"
  | .ka  => .root "ka"
  | .ili => .root "ili"
  | .ne  => .root "ne"

/-- Each stem's lexical melody ([mcpherson-lamont-2026] ex. 3): tones
    over the stem's single TBU, with the lexical pre-linking — the H of
    an `/M^H/` stem is the sole unlinked (floating) element. -/
def Syll.melody (s : Syll) : Form Syll TRN Morph :=
  match s with
  | .kak => .melody s.morpheme [.M, .H] [s] {(0, 0)}          -- /M^H/
  | .ri  => .melody s.morpheme [.M, .H] [s] {(0, 0)}          -- /M^H/
  | .do  => .melody s.morpheme [.M, .H] [s] {(0, 0)}          -- /M^H/
  | .nan => .melody s.morpheme [.M] [s] {(0, 0)}              -- /M/
  | .na  => .melody s.morpheme [.M] [s] {(0, 0)}              -- /M/
  | .ka  => .melody s.morpheme [.M, .H] [s] {(0, 0), (1, 0)}  -- /MH/, both linked
  | .ili => .melody s.morpheme [.L, .H] [s] {(0, 0), (1, 0)}  -- /LH/, both linked
  | .ne  => .melody s.morpheme [] [s] ∅                       -- toneless

/-- The underlying form of a stem sequence is the product of its melodies, left to right,
    in the concatenation monoid. -/
def word (ss : List Syll) : Form Syll TRN Morph := (ss.map Syll.melody).prod

/-- Poko autosegmental forms have a syllable backbone, a `TRN` tone tier, and morpheme
    sponsors. -/
abbrev Form := Autosegmental.Form Syll TRN Morph

end Poko
