module

public import Mathlib.Data.Fintype.Perm
public import Linglib.Phonology.Autosegmental.Skeleton
public import Linglib.Phonology.OptimalityTheory.Typology
public import Linglib.Phonology.Prosody.Mora
public import Studies.Hayes1989

/-!
# Broselow, Chen and Huffman (1997): Syllable weight: convergence of phonology and phonetics

A coda consonant either heads a mora of its own or shares the mora of the vowel before it, and
four ranked constraints make the choice: one against shared morae, one against syllables of more
than two morae, one against morae headed by consonants, and one against changing the number of
morae linked to a segment. [Their twenty-four rankings give four patterns of syllable weight and
no more](##range_language): every coda moraic, as in Hindi; every coda sharing, as in Malayalam;
codas sharing only after a long vowel, as in Levantine Arabic; and long vowels shortened before a
coda, as in Egyptian Arabic. [The two complementary patterns are underivable](##notMem_range).
Because faithfulness counts the morae of a segment and not whether they are shared, [a Malayalam
geminate keeps its mora by sharing the vowel's](##malayalam_geminate).

## Implementation notes

* The forms are schematic, over consonantal and vocalic slots, as the paper's are. A mora is
  placed at the segment that heads it, so that NOCMORA reads its head, and a syllable at its
  vowel.
* Every candidate satisfies MORAICCODA, which the paper takes to be undominated in all four
  languages and leaves out of its tableaux: a coda is linked to a mora of its own or a shared one.
* The candidates neither delete nor insert segments, so MORAFAITH compares each segment with the
  segment at the same slot of the input.

## TODO

* The durational evidence: in all three languages measured, a segment sharing a mora is shorter
  than one with a mora of its own.

## References

* [broselow-chen-huffman-1997]
* [hayes-1989]
* [mccarthy-prince-1995]
-/

@[expose] public section

namespace BroselowChenHuffman1997

open OptimalityTheory Prosody Autosegmental Slot

/-! ### The forms -/

/-- The inputs: a syllable with a short or a long vowel, open or closed. -/
inductive Input
  | cv
  | cvv
  | cvc
  | cvvc
  deriving DecidableEq, Fintype, Repr

/-- The underlying forms, in which a vowel is linked to one mora, or to two if long, and a
consonant to none. -/
def input : Input → MoraicForm Slot
  | .cv =>
    .ofLines [C, V] (moraSegment := {(.of 1, 1)})
  | .cvv =>
    .ofLines [C, V] (moraSegment := {(.of 1, 1), (.of 1 1, 1)})
  | .cvc =>
    .ofLines [C, V, C] (moraSegment := {(.of 1, 1)})
  | .cvvc =>
    .ofLines [C, V, C] (moraSegment := {(.of 1, 1), (.of 1 1, 1)})

/-- An open syllable with a short vowel. -/
def openShort : MoraicForm Slot :=
  .ofLines [C, V] (syllableMora := {(1, .of 1)}) (syllableSegment := {(1, 0)})
    (moraSegment := {(.of 1, 1)})

/-- An open syllable with a long vowel. -/
def openLong : MoraicForm Slot :=
  .ofLines [C, V] (syllableMora := {(1, .of 1), (1, .of 1 1)}) (syllableSegment := {(1, 0)})
    (moraSegment := {(.of 1, 1), (.of 1 1, 1)})

/-- A closed syllable whose coda heads a mora of its own ((29a)), which is also the long vowel
shortened before a moraic coda ((29e)). -/
def closedMoraic : MoraicForm Slot :=
  .ofLines [C, V, C] (syllableMora := {(1, .of 1), (1, .of 2)}) (syllableSegment := {(1, 0)})
    (moraSegment := {(.of 1, 1), (.of 2, 2)})

/-- A closed syllable whose coda shares the vowel's mora ((29b)). -/
def closedShared : MoraicForm Slot :=
  .ofLines [C, V, C] (syllableMora := {(1, .of 1)}) (syllableSegment := {(1, 0)})
    (moraSegment := {(.of 1, 1), (.of 1, 2)})

/-- A trimoraic syllable, a long vowel and a moraic coda ((29c)). -/
def trimoraic : MoraicForm Slot :=
  .ofLines [C, V, C] (syllableMora := {(1, .of 1), (1, .of 1 1), (1, .of 2)})
    (syllableSegment := {(1, 0)}) (moraSegment := {(.of 1, 1), (.of 1 1, 1), (.of 2, 2)})

/-- A long vowel whose second mora the coda shares ((29d)). -/
def longShared : MoraicForm Slot :=
  .ofLines [C, V, C] (syllableMora := {(1, .of 1), (1, .of 1 1)}) (syllableSegment := {(1, 0)})
    (moraSegment := {(.of 1, 1), (.of 1 1, 1), (.of 1 1, 2)})

/-- The candidates of each input. -/
def gen : Input → Finset (MoraicForm Slot)
  | .cv => {openShort}
  | .cvv => {openLong}
  | .cvc => {closedMoraic, closedShared}
  | .cvvc => {trimoraic, longShared, closedMoraic}

-- Every candidate is well formed, free of crossing lines, and has its coda linked to a mora.
theorem gen_wellFormed : ∀ i, ∀ o ∈ gen i, o.WellFormed ∧ o.NoCrossing ∧
    ∀ s ∈ o.syllables, ∀ c ∈ o.coda s, (o.moraeAt c).Nonempty := by
  decide

/-! ### The constraints -/

/-- NOSHAREDMORA (27b): a violation for each mora linked to more than one segment. -/
def noSharedMora {α : Type*} : Constraint (MoraicForm α) := fun X ↦
  (X.morae.filter fun m ↦ 1 < (X.moraSpan m).card).card

/-- SYLLBIN (27a): a violation for each syllable of more than two morae. -/
def syllBin {α : Type*} : Constraint (MoraicForm α) := fun X ↦
  (X.syllables.filter (2 < X.weight ·)).card

/-- NOCMORA (27c): a violation for each mora whose head is a consonant. -/
def noCMora : Constraint (MoraicForm Slot × MoraicForm Slot) := fun p ↦
  (p.2.morae.filter fun m ↦ p.2.head m = some C).card

/-- MORAFAITH (28): a violation for each segment linked to a different number of morae in the
input and in the output. -/
def moraFaith : Constraint (MoraicForm Slot × MoraicForm Slot) := fun p ↦
  (p.1.slots.filter fun i ↦ (p.1.moraeAt i).card ≠ (p.2.moraeAt i).card).card

/-- The constraints. -/
inductive Con
  | noSharedMora
  | syllBin
  | noCMora
  | moraFaith
  deriving DecidableEq, Fintype, Repr

/-- The constraint set, on pairs of an input and an output form. -/
def con : ConstraintSet (MoraicForm Slot × MoraicForm Slot) Con
  | .noSharedMora => noSharedMora.comap Prod.snd
  | .syllBin => syllBin.comap Prod.snd
  | .noCMora => noCMora
  | .moraFaith => moraFaith

/-- The constraint system of the four inputs. -/
def system : ConstraintSystem Input (MoraicForm Slot) Con where
  gen := gen
  con := con.comap fun p ↦ (input p.1, p.2)

/-! ### The typology -/

/-- The Hindi pattern: every coda heads a mora, and a long vowel before one makes a trimoraic
syllable. -/
def hindi : Input → Finset (MoraicForm Slot)
  | .cv => {openShort} | .cvv => {openLong} | .cvc => {closedMoraic} | .cvvc => {trimoraic}

/-- The Malayalam pattern: every coda shares the vowel's mora. -/
def malayalam : Input → Finset (MoraicForm Slot)
  | .cv => {openShort} | .cvv => {openLong} | .cvc => {closedShared} | .cvvc => {longShared}

/-- The Levantine Arabic pattern: a coda heads a mora after a short vowel and shares one after a
long vowel. -/
def levantine : Input → Finset (MoraicForm Slot)
  | .cv => {openShort} | .cvv => {openLong} | .cvc => {closedMoraic} | .cvvc => {longShared}

/-- The Egyptian Arabic pattern: every coda heads a mora, and a long vowel before one shortens. -/
def egyptian : Input → Finset (MoraicForm Slot)
  | .cv => {openShort} | .cvv => {openLong} | .cvc => {closedMoraic} | .cvvc => {closedMoraic}

/-- The anti-Levantine pattern (36): a coda shares a mora after a short vowel and heads one after
a long vowel. -/
def antiLevantine : Input → Finset (MoraicForm Slot)
  | .cv => {openShort} | .cvv => {openLong} | .cvc => {closedShared} | .cvvc => {trimoraic}

/-- The anti-Egyptian pattern (37): a coda shares a mora after a short vowel, and a long vowel
before one shortens. -/
def antiEgyptian : Input → Finset (MoraicForm Slot)
  | .cv => {openShort} | .cvv => {openLong} | .cvc => {closedShared} | .cvvc => {closedMoraic}

/-- The ranking of (29). -/
def hindiRanking : Ranking Con 4 := .ofList [.noSharedMora, .moraFaith, .syllBin, .noCMora]

/-- The ranking of (30). -/
def malayalamRanking : Ranking Con 4 := .ofList [.noCMora, .moraFaith, .syllBin, .noSharedMora]

/-- The ranking of (31). -/
def levantineRanking : Ranking Con 4 := .ofList [.syllBin, .moraFaith, .noSharedMora, .noCMora]

/-- The ranking of (32). -/
def egyptianRanking : Ranking Con 4 := .ofList [.syllBin, .noSharedMora, .moraFaith, .noCMora]

-- (29)–(32): each ranking selects its language's outputs.
theorem language_rankings :
    system.language hindiRanking = hindi ∧ system.language malayalamRanking = malayalam ∧
    system.language levantineRanking = levantine ∧
    system.language egyptianRanking = egyptian := by
  decide

/-- The twenty-four rankings of the four constraints give exactly four languages, those of
Hindi, Malayalam, Levantine Arabic and Egyptian Arabic (35). -/
theorem range_language :
    Set.range (system.language (n := 4)) = {hindi, malayalam, levantine, egyptian} := by
  have h : ∀ r : Ranking Con 4, system.language r = hindi ∨ system.language r = malayalam ∨
      system.language r = levantine ∨ system.language r = egyptian := by
    decide
  ext L
  constructor
  · rintro ⟨r, rfl⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h r
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl | rfl | rfl)
    exacts [⟨_, language_rankings.1⟩, ⟨_, language_rankings.2.1⟩,
      ⟨_, language_rankings.2.2.1⟩, ⟨_, language_rankings.2.2.2⟩]

/-- No ranking derives the anti-Levantine pattern (36) or the anti-Egyptian pattern (37), in
which a coda shares a mora after a short vowel but not after a long one. -/
theorem notMem_range : antiLevantine ∉ Set.range (system.language (n := 4)) ∧
    antiEgyptian ∉ Set.range (system.language (n := 4)) := by
  rw [range_language]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  decide

/-! ### Geminates in Malayalam -/

/-- An intervocalic geminate, which is underlyingly moraic ((33)). -/
def geminate : MoraicForm Slot :=
  .ofLines [V, C, V] (moraSegment := {(.of 0, 0), (.of 1, 1), (.of 2, 2)})

/-- An intervocalic single consonant ((34)). -/
def single : MoraicForm Slot :=
  .ofLines [V, C, V] (moraSegment := {(.of 0, 0), (.of 2, 2)})

/-- The consonant shares the preceding vowel's mora and is the onset of the next syllable
((33a), (34a)). -/
def sharedOnset : MoraicForm Slot :=
  .ofLines [V, C, V] (syllableMora := {(0, .of 0), (2, .of 2)}) (syllableSegment := {(2, 1)})
    (moraSegment := {(.of 0, 0), (.of 0, 1), (.of 2, 2)})

/-- The consonant is only the onset of the next syllable ((33b), (34b)). -/
def plainOnset : MoraicForm Slot :=
  .ofLines [V, C, V] (syllableMora := {(0, .of 0), (2, .of 2)}) (syllableSegment := {(2, 1)})
    (moraSegment := {(.of 0, 0), (.of 2, 2)})

/-- The consonant heads a mora of its own and is the onset of the next syllable ((33c)). -/
def moraicOnset : MoraicForm Slot :=
  .ofLines [V, C, V] (syllableMora := {(0, .of 0), (0, .of 1), (2, .of 2)})
    (syllableSegment := {(2, 1)}) (moraSegment := {(.of 0, 0), (.of 1, 1), (.of 2, 2)})

/-- Under the Malayalam ranking a geminate keeps its mora by sharing the preceding vowel's,
leaving the syllable before it light ((33)), while a single consonant stays a bare onset ((34)):
faithfulness counts the morae of a segment, not whether they are shared. -/
theorem malayalam_geminate :
    (Tableau.ofRanking (con.comap (geminate, ·)) malayalamRanking
      {sharedOnset, plainOnset, moraicOnset}).optimal = {sharedOnset} ∧
    (Tableau.ofRanking (con.comap (single, ·)) malayalamRanking
      {sharedOnset, plainOnset}).optimal = {plainOnset} := by
  decide

/-! ### Weight by Position -/

-- Without Weight by Position the syllabification of [hayes-1989] shares the vowel's mora with
-- the coda, the Malayalam closed syllable; with it the coda heads its own, and a long vowel
-- before it gives the Levantine syllable under a two-mora limit and the Hindi one under three.
theorem syllabify_eq :
    Hayes1989.Underlying.syllabify [(C, 0), (V, 1), (C, 0)] false = closedShared ∧
    Hayes1989.Underlying.syllabify [(C, 0), (V, 1), (C, 0)] true = closedMoraic ∧
    Hayes1989.Underlying.syllabify [(C, 0), (V, 2), (C, 0)] true = longShared ∧
    Hayes1989.Underlying.syllabify [(C, 0), (V, 2), (C, 0)] true 3 = trimoraic := by
  decide

end BroselowChenHuffman1997
