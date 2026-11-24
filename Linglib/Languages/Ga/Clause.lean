/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Category.Complementizer.Basic
public import Linglib.Syntax.Category.Verb.ArgumentFrame.Takes

/-!
# Gã complementizers and embedded clause types

The three complementizers of [allotey-2021] (Gã, ISO 639-3 `gaa`; Kwa, Ghana)
as `Complementizer` entries, and the three-way embedded clause typology they
head, each type with the complement `ArgumentFrame` a verb selecting it records.
The frames are the frames the complementizers type (`ArgumentFrame.typedBy`),
so complementizer selection is read off the entries rather than restated. The
pronouns are in `Languages/Ga/Pronouns` and the complement-taking verbs in
`Languages/Ga/Verbs`.

## Implementation notes

The paper's finiteness diagnostics (tense restriction, focus fronting, NPI
licensing, negation placement; exx 104–125) all split the `ni`-clause from the
other two, so they are not stored as clause properties: finiteness is read off
the complementizer (`Complementizer.IsFinite`), and each diagnostic is a theorem
over the paper's rows in `Studies/Allotey2021`. The verb-movement diagnostic
(exx 120–125, after [pollock-1989]) needs phrase-structure substrate this
language file does not carry. Lean does not accept `ɛ` in plain identifiers, so names use Latin
letters (`ake`, `keji`) and the orthography lives in the morphs.

## References

* [allotey-2021]
* [noonan-2007]
* [pollock-1989]
-/

@[expose] public section

namespace Ga

/-! ### Complementizers -/

/-- *akɛ* — the finite declarative complementizer, typing the complements of
    utterance and attitude verbs (exx 47–49, 89a). -/
def ake : Complementizer where
  morphs := [.free "akɛ"]
  coding := some .indicative
  types := .only .declarative
  verbForm := some .Fin

/-- *kɛji* — the finite complementizer of conditional clauses (ex 97a) and,
    under *le* 'know', of polar and alternative questions ('know if they will
    come', 'know whether you or he bought it', exx 104, 108); glossed COND
    throughout the paper. -/
def keji : Complementizer where
  morphs := [.free "kɛji"]
  coding := some .indicative
  types := .of {.polar, .alternative}
  verbForm := some .Fin

/-- *ni* — the irrealis complementizer of controlled clauses, glossed C with the
    complement's verb glossed INF: a weak CP with no focus fronting and no
    independent tense (exx 107–109). Optionally overt with some control verbs
    (*tao* 'want', ex 34) and obligatory with others (*hiɛ-kã-nɔ* 'hope', ex 35);
    homophonous with the focus marker (ex 27). -/
def ni : Complementizer where
  morphs := [.free "ni"]
  coding := some .infinitive
  verbForm := some .Inf

/-- The three clause introducers that can head an embedded C (§5.5.1). -/
def complementizers : List Complementizer := [ake, keji, ni]

/-! ### Embedded clause typology -/

/-- The finite declarative frame `akɛ` types is definitionally the library's generic
    `ArgumentFrame.finiteClause`. -/
def akeFrame : ArgumentFrame := .typedBy ake

/-- The finite interrogative frame `kɛji` types. -/
def kejiFrame : ArgumentFrame := .typedBy keji

/-- The controlled irrealis frame `ni` types is [noonan-2007]-infinitival, the paper's own
    term, with a subject that is an overt pronoun in the subjective (nominative) form of
    Table 3, never null and never a lexical DP (exx 40–42). -/
def niFrame : ArgumentFrame := .typedBy ni (some (.overt (some .nom)))

/-- The three embedded clause types of [allotey-2021], named by the
    complementizer heading them (§5.5.1). The `ni` type is the controlled
    irrealis clause; `ni` also introduces true subjunctives with lexical subjects
    (ex 105) and, under *dwɛŋ* 'think', finite low-tone complements
    (exx 110–111), which are not of this type. -/
inductive EmbeddedClauseType where
  | ake
  | keji
  | ni
  deriving DecidableEq, Repr

namespace EmbeddedClauseType

/-- The complementizer heading the clause type. -/
def complementizer : EmbeddedClauseType → Complementizer
  | ake => Ga.ake
  | keji => Ga.keji
  | ni => Ga.ni

/-- The complement frame a verb selecting the clause type records. -/
def frame : EmbeddedClauseType → ArgumentFrame
  | ake => akeFrame
  | keji => kejiFrame
  | ni => niFrame

end EmbeddedClauseType

end Ga
