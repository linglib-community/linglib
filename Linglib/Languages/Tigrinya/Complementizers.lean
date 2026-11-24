module

public import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Tigrinya Complementizers

Tigrinya (Ethio-Semitic, head-final) types its embedded clauses with
prefixes on the embedded verb. *zɨ-* marks relative, comparative and
subject noun-complement clauses; *kɛmzɨ-* — the similative *kɛm* 'like'
plus *zɨ-* — introduces the complements of factive, cognitive
non-factive, fiction, utterance and perception verbs; the subjunctive
*kɨ-* introduces the complements of directive, desire, modal,
emotive-factive, control and ECM verbs and marks purpose, future and
sentential-subject clauses. The one clause-final complementizer, *ʔɨlu*,
is an inflected 'say' form agreeing with the matrix subject and overlaps
with *kɛmzɨ-* on cognitive non-factive, fiction and utterance verbs. All
three prefixes attach to fully inflected (subject-marked) Imperfective
or Perfective verbs; none carries φ-features of its own.

This file provides the four as `Complementizer` entries and the prefix
morphs.

## References

* [cacchioli-2026], chs. 2–4, Table 6.1
* [cacchioli-2023]
-/

@[expose] public section

namespace Tigrinya.Complementizers

open Morphology (Morph)

/-- The prefix *zɨ-* as a morph. -/
def zi.morph : Morph := .pref "zɨ"

/-- *zɨ-* — relativizer and general subordinator: relative clauses,
comparatives and superlatives, subject noun-complement clauses,
*seem*-clauses, and the clauses of particles such as *ʔɨntɛ* 'if' and
*sɨlɛ* 'because'. Doubles on verb and auxiliary in periphrastic tenses. -/
def zi : Complementizer where
  morphs := [zi.morph]
  coding := some .indicative
  verbForm := some .Fin

/-- The prefix *kɛm-*, the similative preposition 'like' grammaticalized
as a clause-linker; it requires a *zɨ-*-marked verb. -/
def kem : Morph := .pref "kɛm"

/-- *kɛmzɨ-* — 'that' on complement clauses of factive ('know',
'forget'), cognitive non-factive ('think', 'believe'), fiction ('dream'),
utterance ('say', 'ask') and perception ('see', 'hear') verbs, including
embedded questions. Factivity tracks the matrix verb, so no lexical
`factive` value is recorded. -/
def kemzi : Complementizer where
  morphs := [kem, zi.morph]
  coding := some .indicative
  verbForm := some .Fin

/-- The prefix *kɨ-* as a morph. -/
def ki.morph : Morph := .pref "kɨ"

/-- *kɨ-* — subjunctive marker on Imperfective verbs: complements of
directive, desire, modal, emotive-factive, control and ECM verbs;
purpose clauses, the future construction, sentential subjects. -/
def ki : Complementizer where
  morphs := [ki.morph]
  coding := some .subjunctive
  verbForm := some .Fin

/-- *ʔɨlu* — the clause-final complementizer, an inflected form of 'say'
agreeing with the matrix subject (*ʔɨl-ɛ* 'COMP-1SG'). Limited to
cognitive non-factive, fiction and utterance verbs. -/
def ilu : Complementizer where
  morphs := [.free "ʔɨlu"]
  coding := some .indicative
  types := .only .declarative

/-- The complementizer inventory. -/
def complementizers : List Complementizer := [zi, kemzi, ki, ilu]

end Tigrinya.Complementizers
