/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

module

/-!
# Laal prosodic fragment

[lionnet-2022]

Theory-neutral tone data for Laal (language isolate, southern Chad): the three
contrastive tone heights H/M/L, the attested stem-level tone melodies (Table 2),
and verb roots illustrating M-lowering. Transcriptional facts only — the
subtonal `[±upper]`/`[±raised]` featural analysis and the M-lowering mechanism
live in `Studies/Lionnet2022.lean`.
-/

@[expose] public section

namespace Laal.Prosody

/-- The three contrastive tone heights of Laal, contrasted in the minimal triplet
`kúmá`/`kūmā`/`kùmà` (ex. 8). Theory-neutral transcription. -/
inductive Tone where
  | H
  | M
  | L
  deriving DecidableEq, Repr, Inhabited

/-- A Laal stem: segmental form, gloss, and stem-level tone melody. -/
structure StemEntry where
  form : String
  gloss : String
  melody : List Tone
  deriving Repr, DecidableEq

/-- The minimal tone triplet on a `kVmV` segmental frame (ex. 8): three stems
contrasting in tone alone. -/
def minimalTriplet : List StemEntry :=
  [ ⟨"kúmá", "type of basket", [Tone.H]⟩,
    ⟨"kūmā", "to hide",        [Tone.M]⟩,
    ⟨"kùmà", "medicine",       [Tone.L]⟩ ]

/-- The seven regular stem-level tone melodies on mono- and disyllabic stems
(Table 2). Every combination of H and L is attested; M occurs only as the sole
tone — the empirical basis of the M-exclusivity (`*MX/XM`) generalisation. -/
def attestedMelodies : List (List Tone) :=
  [ [Tone.H], [Tone.M], [Tone.L],
    [Tone.L, Tone.H], [Tone.H, Tone.L],
    [Tone.L, Tone.H, Tone.L], [Tone.H, Tone.L, Tone.H] ]

/-- Verb roots illustrating M-lowering: under stratum-2 suffixation the M-toned
root lowers to L, while H- and L-toned roots are stable (ex. 10–11, 60). -/
def mLoweringRoots : List StemEntry :=
  [ ⟨"kár", "put",       [Tone.H]⟩,
    ⟨"dāg", "drag",      [Tone.M]⟩,
    ⟨"jàr", "sacrifice", [Tone.L]⟩ ]

end Laal.Prosody
