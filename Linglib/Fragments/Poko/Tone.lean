/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Fragments.Poko.Phonology
public import Linglib.Phonology.Tone.Basic
public import Linglib.Phonology.Autosegmental.Melody

/-!
# Poko tone

Poko (Poko-Rawo; Glottolog `rawo1244`, ISO 639-3 `rwa`) is a Skou language of Sandaun Province,
Papua New Guinea, with no more than a hundred speakers [mcpherson-dryer-2021]. It contrasts
three tone levels, H, M and L, beside toneless syllables and floating tones, and its
tone-bearing unit is the syllable. The tones of a stem form one of a few lexical melodies, `∅`,
`M`, `MH`, `LM`, `LH` and `M^H`, and on disyllables also `^L∅^H`, none with more than two tones.
H is never initial and L never final, floating or not, so the simple melodies `L` and `H` are
missing: [mcpherson-2022] accounts for the gap with the edge constraints Non-Initial(H) and
Non-Final(L), each evaluated over the melody and over the tones linked to the stem, and
[mcpherson-lamont-2026] suggest an extreme response to the OCP.

The entries are the stems of [mcpherson-lamont-2026]'s tableaux. Each is a melody over the
stem's syllables with its lexical pre-linking, in which the H of an `M^H` stem is the one
unlinked, floating element ([rolle-2018]). Every stem ends in a vowel underlyingly, but a
polysyllabic stem loses its final vowel except phrase-finally and the vowel's tone moves to
the syllable before it, so the pronouns enter the tableaux in their reduced forms. A phrase is
the product of its stems in the concatenation monoid.

## Implementation notes

A syllable is the string of its segments. A stem takes the morpheme that sponsors its tones and
syllables as an argument, so that a study gives each token in a phrase a sponsor of its own,
as the source colours each stem of a tableau.

## References

* [mcpherson-dryer-2021]
* [mcpherson-lamont-2026]
* [mcpherson-2022]
* [rolle-2018]
-/

@[expose] public section

open Phonology (Segment)
open Tone (TRN)

namespace Poko

/-- A Poko form has syllables of Poko segments on its lower tier and tonal root nodes on its
upper tier, each element sponsored by a morpheme in `M`. -/
abbrev Form (M : Type*) := Autosegmental.Form (List Segment) TRN M

variable {M : Type*} (x : M)

/-! ### `M^H` stems -/

/-- /kāk^H/, the 3SG.M pronoun, as possessor 'his' and subject 'he' ((12a), (12c)); the reduced
form of /kākā^H/ ([mcpherson-dryer-2021] (7)). -/
def kak : Form M := .melody x [.M, .H] [[k, a, k]] {(0, 0)}

/-- /rī^H/ 'pig' ((12)). -/
def ri : Form M := .melody x [.M, .H] [[r, i]] {(0, 0)}

/-- /dō^H/ 'get' ((12b), (12c)). -/
def «do» : Form M := .melody x [.M, .H] [[d, o]] {(0, 0)}

/-! ### `M` stems -/

/-- /nān/, the 1SG pronoun, as possessor 'my' and subject 'I' ((19), (22)); the reduced form of
/nānē/ ((1a)). -/
def nan : Form M := .melody x [.M] [[n, a, n]] {(0, 0)}

/-- /nā/ 'eat (1SG)' ((22b)). -/
def na : Form M := .melody x [.M] [[n, a]] {(0, 0)}

/-! ### Contour, disyllabic and toneless stems -/

/-- /kǎ/ 'friend', its M and H both linked to its one syllable ((3), (26a)). -/
def ka : Form M := .melody x [.M, .H] [[k, a]] {(0, 0), (1, 0)}

/-- /ìlí/ 'bamboo', L on the first syllable and H on the second ((1b), (28a)). -/
def ili : Form M := .melody x [.L, .H] [[i], [l, i]] {(0, 0), (1, 1)}

/-- /ne/ 'make (1SG)', toneless ((22a)). -/
def ne : Form M := .melody x [] [[n, e]] ∅

end Poko
