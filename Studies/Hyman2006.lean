module

public import Linglib.Fragments.Japanese.Prosody
public import Linglib.Phonology.Prosody.Grid
public import Linglib.Phonology.Tone.Basic
public import Mathlib.Data.Finset.Card

/-!
# Hyman (2006): Word-prosodic typology

This file formalizes [hyman-2006]'s two prototypes of word prosody and the argument that
pitch accent is no third. A language has tone when an indication of pitch enters the lexical
realization of some morpheme, definition (3) (`Tonal`); it has stress accent when word-level
metrical structure marks a head syllable in every lexical word, definition (5), which separates
into obligatoriness, at least one head (`Obligatory`), and culminativity, at most one
(`Culminative`), the pair that the usual *one and only one* conflates
(`obligatory_and_culminative_iff`). Obligatoriness is the definitional criterion, OBLHEAD,
and it targets syllables: a language whose words may lack syllables cannot have stress
accent (`not_obligatory_of_no_units`, Bella Coola), and an obligatory H assigned by mora is
restricted tone rather than stress accent (`kinga_not_stressAccent`).

The four combinations of the two criteria are all attested among restricted-H systems, Table
II: Kinga's antepenultimate-mora H is obligatory and culminative, Creek's tonal accent
obligatory but not culminative, Tokyo Japanese's accent culminative but not obligatory,
read off the accent lexicon of the Japanese fragment (`tokyo_not_obligatory`), and Seneca's
trochaic H neither, derived from the analysis of (21) (`seneca_not_obligatory`). So neither
criterion implies the other, no hierarchical typology can cut first by one and then by the
other, and the cut by OBLHEAD and the reviewer's cut by culminativity of Section 7 classify
Creek and Tokyo Japanese oppositely (`cuts_differ`).

## Implementation notes

* A `Marking` records, for each lexical word, its units and the units bearing the mark, the
  primary stress or the restricted tone; the tone-bearing unit is `Tone.TBUKind`. Tone is
  stated on a lexicon of morphemes with an optional pitch specification.
* Table I's languages are not listed; its two dimensions are `Tonal` and `StressAccent`,
  which `Studies/Lionnet2025` evaluates for Drubea.

## References

* [hyman-2006]
* [lionnet-2025]
-/

@[expose] public section

namespace Hyman2006

open Tone

/-! ### The two prototypes -/

/-- Definition (3): a lexicon is tonal when an indication of pitch enters the lexical
realization of at least one morpheme. -/
def Tonal {M P : Type*} (pitch : M → Option P) : Prop := ∃ μ, (pitch μ).isSome

/-- A word-level marking: the units of each lexical word and those bearing the mark, the
highest degree of metrical prominence or the restricted tone, on units of a kind. -/
structure Marking (Word U : Type*) where
  units : Word → Finset U
  marked : Word → Finset U
  marked_subset : ∀ w, marked w ⊆ units w
  tbu : TBUKind

variable {Word U : Type*}

/-- (5a): every lexical word has at least one marked unit, OBLHEAD. -/
def Obligatory (m : Marking Word U) : Prop := ∀ w, (m.marked w).Nonempty

/-- (5b): every lexical word has at most one marked unit. -/
def Culminative (m : Marking Word U) : Prop := ∀ w, (m.marked w).card ≤ 1

/-- Definition (5): stress accent is an obligatory, culminative marking of syllables. -/
def StressAccent (m : Marking Word U) : Prop :=
  m.tbu = .syllable ∧ Obligatory m ∧ Culminative m

/-- The two criteria together are the *one and only one* head of McCarthy's HEAD(PWd), which
(5) separates. -/
theorem obligatory_and_culminative_iff (m : Marking Word U) :
    Obligatory m ∧ Culminative m ↔ ∀ w, (m.marked w).card = 1 := by
  simp only [Obligatory, Culminative, ← Finset.card_pos, ← forall_and]
  exact forall_congr' λ w => by omega

theorem grid_isCulminative_iff (g : Prosody.Grid) :
    Prosody.Grid.IsCulminative g ↔
      1 ≤ g.countP (· == Prosody.Grid.peak g) ∧ g.countP (· == Prosody.Grid.peak g) ≤ 1 := by
  unfold Prosody.Grid.IsCulminative; omega

/-- A marking assigned by a rule that names one unit of every word is obligatory and
culminative. -/
def Marking.ofRule (units : Word → Finset U) (pos : Word → U) (h : ∀ w, pos w ∈ units w)
    (tbu : TBUKind) : Marking Word U :=
  ⟨units, λ w => {pos w}, λ w => Finset.singleton_subset_iff.2 (h w), tbu⟩

theorem obligatory_ofRule (units : Word → Finset U) (pos : Word → U) (h : ∀ w, pos w ∈ units w)
    (tbu : TBUKind) : Obligatory (Marking.ofRule units pos h tbu) :=
  λ _ => Finset.singleton_nonempty _

theorem culminative_ofRule (units : Word → Finset U) (pos : Word → U)
    (h : ∀ w, pos w ∈ units w) (tbu : TBUKind) : Culminative (Marking.ofRule units pos h tbu) :=
  λ _ => (Finset.card_singleton _).le

/-- A word without units of the marked kind bears no head, so the language fails OBLHEAD (Section
4). -/
theorem not_obligatory_of_no_units {m : Marking Word U} {w : Word} (h : m.units w = ∅) :
    ¬ Obligatory m := λ ho =>
  (ho w).ne_empty (Finset.subset_empty.1 (h ▸ m.marked_subset w))

theorem not_stressAccent_of_no_units {m : Marking Word U} {w : Word} (h : m.units w = ∅) :
    ¬ StressAccent m := λ hs => not_obligatory_of_no_units h hs.2.1

/-! ### Tokyo Japanese -/

open Japanese.Prosody in
/-- The accent of Tokyo Japanese as a marking of moras: the accented mora of each lexical
entry of the fragment, or none. -/
def tokyo : Marking ProsodicEntry ℕ where
  units e := Finset.range e.nMorae
  marked e := (Finset.range e.nMorae).filter (e.accentMora = some ·)
  marked_subset _ := Finset.filter_subset _ _
  tbu := .mora

open Japanese.Prosody in
-- (3)
theorem tokyo_tonal : Tonal (λ e : ProsodicEntry => e.accentMora) := ⟨ameRain, rfl⟩

theorem tokyo_culminative : Culminative tokyo := λ e => by
  refine (Finset.card_le_one.2 λ a ha b hb => ?_)
  simp only [tokyo, Finset.mem_filter] at ha hb
  exact Option.some.inj (ha.2.symm.trans hb.2)

open Japanese.Prosody in
theorem tokyo_not_obligatory : ¬ Obligatory tokyo := λ h =>
  (h ameCandy).ne_empty (by decide)

-- Section 5.2
theorem tokyo_not_stressAccent : ¬ StressAccent tokyo := λ h => tokyo_not_obligatory h.2.1

/-! ### Kinga -/

/-- The words of (18b). -/
inductive KingaWord where
  | ukuheka
  | ukuvala
  | ukugeenda
  | ukugeendelela
  | ukuhwaanana
  deriving DecidableEq, Repr

/-- The mora counts of the words. -/
def KingaWord.nMorae : KingaWord → ℕ
  | .ukuheka => 4
  | .ukuvala => 4
  | .ukugeenda => 5
  | .ukugeendelela => 7
  | .ukuhwaanana => 6

/-- Kinga's obligatory H falls on the antepenultimate mora, (18b). -/
def kinga : Marking KingaWord ℕ :=
  Marking.ofRule (λ w => Finset.range w.nMorae) (λ w => w.nMorae - 3)
    (λ w => by cases w <;> decide) .mora

theorem kinga_obligatory : Obligatory kinga := obligatory_ofRule _ _ _ _

theorem kinga_culminative : Culminative kinga := culminative_ofRule _ _ _ _

/-- Section 5.2: assigned by mora, the obligatory H of Kinga is restricted tone, not stress
accent. -/
theorem kinga_not_stressAccent : ¬ StressAccent kinga := λ h => absurd h.1 (by decide)

/-! ### Creek -/

/-- The words of (20) and the fixed-accent /náfka:kís/ of Section 5.3. -/
inductive CreekWord where
  | hicita
  | ahicita
  | caalo
  | sokca
  | nafkaakis
  deriving DecidableEq, Repr

def CreekWord.nSyllables : CreekWord → ℕ
  | .hicita => 3
  | .ahicita => 4
  | .caalo => 2
  | .sokca => 2
  | .nafkaakis => 3

/-- The tonal accents: the last even-numbered light syllable (20a), a heavy penult (20b), and
the two fixed accents of /náfka:kís/. -/
def CreekWord.accents : CreekWord → Finset ℕ
  | .hicita => {1}
  | .ahicita => {3}
  | .caalo => {0}
  | .sokca => {0}
  | .nafkaakis => {0, 2}

def creek : Marking CreekWord ℕ where
  units w := Finset.range w.nSyllables
  marked := CreekWord.accents
  marked_subset w := by cases w <;> decide
  tbu := .syllable

theorem creek_obligatory : Obligatory creek := λ w => by cases w <;> decide

theorem creek_not_culminative : ¬ Culminative creek := λ h => absurd (h .nafkaakis) (by decide)

/-! ### Seneca -/

/-- The trochaic analysis of (21): the first syllable is extrametrical, disyllabic trochees are
built left to right, and a trochee's initial syllable takes H when the trochee contains a
closed syllable. A word is its syllables' closedness. -/
def senecaH (closed : List Bool) : Finset ℕ :=
  ((List.range closed.length).filter λ i =>
    1 ≤ i ∧ (i - 1) % 2 = 0 ∧ i + 1 < closed.length ∧
      (closed.getD i false || closed.getD (i + 1) false)).toFinset

/-- The words of (23), with a closed syllable marked `true`. -/
inductive SenecaWord where
  | willing
  | busy
  | necktie
  deriving DecidableEq, Repr

def SenecaWord.closed : SenecaWord → List Bool
  | .willing => [false, false, false, true, true]
  | .busy => [false, false, true, false, false, true, true]
  | .necktie => [false, false, false, false, false, true]

def seneca : Marking SenecaWord ℕ where
  units w := Finset.range w.closed.length
  marked w := senecaH w.closed
  marked_subset w := by cases w <;> decide
  tbu := .syllable

-- (23a)
theorem seneca_willing : seneca.marked .willing = {3} := by decide

-- (23b)
theorem seneca_busy : seneca.marked .busy = {1, 5} := by decide

-- (23c)
theorem seneca_necktie : seneca.marked .necktie = ∅ := by decide

theorem seneca_not_obligatory : ¬ Obligatory seneca := λ h =>
  (h .necktie).ne_empty seneca_necktie

theorem seneca_not_culminative : ¬ Culminative seneca := λ h => absurd (h .busy) (by decide)

/-! ### The cuts of Section 7 -/

-- Table II
theorem tableII :
    (Obligatory kinga ∧ Culminative kinga) ∧ (Obligatory creek ∧ ¬ Culminative creek) ∧
      (¬ Obligatory tokyo ∧ Culminative tokyo) ∧ (¬ Obligatory seneca ∧ ¬ Culminative seneca) :=
  ⟨⟨kinga_obligatory, kinga_culminative⟩, ⟨creek_obligatory, creek_not_culminative⟩,
    ⟨tokyo_not_obligatory, tokyo_culminative⟩, ⟨seneca_not_obligatory, seneca_not_culminative⟩⟩

theorem cuts_differ :
    (Obligatory creek ∧ ¬ Obligatory tokyo) ∧ (Culminative tokyo ∧ ¬ Culminative creek) :=
  ⟨⟨creek_obligatory, tokyo_not_obligatory⟩, ⟨tokyo_culminative, creek_not_culminative⟩⟩

end Hyman2006
