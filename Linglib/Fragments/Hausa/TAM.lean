module

public import Linglib.Syntax.Agreement.Paradigm
public import Mathlib.Data.Fintype.Basic

/-!
# Hausa tense, aspect and mood

Hausa marks tense, aspect and mood not on the verb but on a preverbal person-aspect complex (PAC),
which a clause requires whether or not its subject is expressed: *Tàlātù zā tà dafà àbinci*
'Talatu will cook food' against *Tàlātù tanā̀ dafà àbinci* 'Talatu is cooking food'. A PAC is a
weak subject pronoun and a TAM marker, the marker following the pronoun except in the future and
the allative, and in the completive the two are fused into a single heavy-syllable pronoun. The
pronoun distinguishes nine cells: 1s, 2m, 2f, 3m, 3f, 1p, 2p, 3p, and the impersonal 4p, which
patterns with the plurals. A TAM is the paradigm of its PACs.

[newman-2000] classifies the TAMs by three rubrics. The general ones occur in ordinary affirmative
clauses. The relative ones are those allowed or required in Rel environments, where the verb
follows the relativizer *dà*, a question word, or any other focused element. The negative ones
are not recorded here. The continuous is replaced in Rel environments by the Rel-continuous1 or
the Rel-continuous2, which occur nowhere else; the completive does not occur there, and its Rel
counterpart is the preterite, which occurs in both; the potential's Rel counterpart is the future;
the rhetorical occurs only in Rel environments; and the subjunctive neither occurs in them nor has
a counterpart there.

## Main definitions

* `Hausa.pacCells` — the nine subject cells of a PAC paradigm
* `Hausa.TAM`, `Hausa.TAM.paradigm` — the affirmative TAMs and their PACs
* `Hausa.TAM.general`, `Hausa.TAM.rel` — the TAMs of general clauses and of Rel environments
* `Hausa.TAM.relCounterparts` — the TAMs a Rel environment takes in place of a TAM

## Main results

* `Hausa.TAM.mem_rel_iff` — a TAM occurs in Rel environments exactly when it is its own Rel
  counterpart, so Newman's statement of the counterparts agrees with his overview table
* `Hausa.TAM.form_ne_of_mem_relCounterparts` — a counterpart that is another TAM differs from it
  in every cell, so the replacement is always audible

## Implementation notes

The forms are those of Newman's paradigm tables, in his orthography: an unmarked vowel is high,
a grave accent marks low tone, a circumflex a falling tone on a long vowel, and a macron vowel
length. Where he gives two Standard Hausa forms the first is recorded, the contracted *zân* and
*zâi* of the future and the allative among them; dialect variants are left out. The neutral, the
bare pronoun a clause takes when it repeats the TAM of the one before, is not recorded.

## References

* [newman-2000]
-/

@[expose] public section

namespace Hausa

open Agreement

/-- The impersonal 4p is plural with no person, and patterns with the plurals. -/
def impersonal : Bundle := .set .number .plural ⊥

/-- The nine cells of a PAC paradigm in [newman-2000]'s order: 1s, 2m, 2f, 3m, 3f, 1p, 2p, 3p
and the impersonal 4p. -/
def pacCells : List Bundle :=
  [.personNumber .first .singular,
    (Bundle.personNumber .second .singular).set .gender .masculine,
    (Bundle.personNumber .second .singular).set .gender .feminine,
    (Bundle.personNumber .third .singular).set .gender .masculine,
    (Bundle.personNumber .third .singular).set .gender .feminine,
    .personNumber .first .plural, .personNumber .second .plural, .personNumber .third .plural,
    impersonal]

/-- The affirmative TAMs of the PAC. -/
inductive TAM where
  /-- The completive, a portmanteau of pronoun and TAM: *Mūsā yā tàfi Bicì* 'Musa went, has gone
  to Bichi'. -/
  | completive
  /-- The preterite, or Rel-completive. -/
  | preterite
  | continuous
  /-- The Rel-continuous1, the marker *-kḕ*. -/
  | relContinuous1
  /-- The Rel-continuous2, the short-vowel marker *-kè*. -/
  | relContinuous2
  | future
  /-- The allative, imminent or future motion toward a place. -/
  | allative
  /-- The potential, a future of lesser certainty. -/
  | potential
  /-- The rhetorical, the marker *-kā̀*. -/
  | rhetorical
  | habitual
  | subjunctive
  deriving DecidableEq, Repr, Fintype

namespace TAM

/-- The PACs of a TAM, from [newman-2000]'s paradigm tables. -/
def paradigm : TAM → Paradigm String
  | .completive => pacCells.zip ["nā", "kā", "kin", "yā", "tā", "mun", "kun", "sun", "an"]
  | .preterite => pacCells.zip ["na", "ka", "kikà", "ya", "ta", "mukà", "kukà", "sukà", "akà"]
  | .continuous =>
    pacCells.zip ["inā̀", "kanā̀", "kinā̀", "yanā̀", "tanā̀", "munā̀", "kunā̀", "sunā̀", "anā̀"]
  | .relContinuous1 =>
    pacCells.zip ["nakḕ", "kakḕ", "kikḕ", "yakḕ", "takḕ", "mukḕ", "kukḕ", "sukḕ", "akḕ"]
  | .relContinuous2 =>
    pacCells.zip ["nakè", "kakè", "kikè", "yakè", "takè", "mukè", "kukè", "sukè", "akè"]
  | .future =>
    pacCells.zip ["zân", "zā kà", "zā kì", "zâi", "zā tà", "zā mù", "zā kù", "zā sù", "zā à"]
  | .allative =>
    pacCells.zip ["zâ ni", "zâ ka", "zâ ki", "zâ shi", "zâ ta", "zâ mu", "zâ ku", "zâ su", "zâ a"]
  | .potential => pacCells.zip ["nâ", "kâ", "kyâ", "yâ", "tâ", "mâ", "kwâ", "sâ", "â"]
  | .rhetorical =>
    pacCells.zip ["nikā̀", "kakā̀", "kikā̀", "yakā̀", "takā̀", "mukā̀", "kukā̀", "sukā̀", "akā̀"]
  | .habitual =>
    pacCells.zip ["nakàn", "kakàn", "kikàn", "yakàn", "takàn", "mukàn", "kukàn", "sukàn", "akàn"]
  | .subjunctive => pacCells.zip ["ìn", "kà", "kì", "yà", "tà", "mù", "kù", "sù", "à"]

/-- The PAC of a TAM in a subject cell. -/
def form (t : TAM) (c : Bundle) : Option String := t.paradigm.realize c

/-- The TAMs of general clauses are all but the rhetorical and the two Rel-continuous ones. -/
def general : Finset TAM :=
  {completive, preterite, continuous, future, allative, potential, habitual, subjunctive}

/-- The TAMs of Rel environments. -/
def rel : Finset TAM :=
  {preterite, relContinuous1, relContinuous2, future, allative, rhetorical, habitual}

/-- A Rel environment takes the TAM itself if it occurs there, the preterite for the completive, the
Rel-continuous1 or Rel-continuous2 for the continuous, the future for the potential, and none for
the subjunctive. -/
def relCounterparts : TAM → Finset TAM
  | completive => {preterite}
  | continuous => {relContinuous1, relContinuous2}
  | potential => {future}
  | subjunctive => ∅
  | t => {t}

theorem form_isSome : ∀ t : TAM, ∀ c ∈ pacCells, (t.form c).isSome := by decide

theorem relCounterparts_subset_rel : ∀ t : TAM, t.relCounterparts ⊆ rel := by decide

theorem mem_rel_iff : ∀ t : TAM, t ∈ rel ↔ t.relCounterparts = {t} := by decide

theorem general_union_rel : general ∪ rel = Finset.univ := by decide

theorem relCounterparts_eq_empty_iff : ∀ t : TAM, t.relCounterparts = ∅ ↔ t = subjunctive := by
  decide

theorem ne_iff_not_mem_rel :
    ∀ t : TAM, ∀ t' ∈ t.relCounterparts, t' ≠ t ↔ t ∉ rel := by
  decide

theorem form_ne_of_mem_relCounterparts :
    ∀ t : TAM, ∀ t' ∈ t.relCounterparts, t' ≠ t → ∀ c ∈ pacCells, t'.form c ≠ t.form c := by
  decide

end TAM

end Hausa
