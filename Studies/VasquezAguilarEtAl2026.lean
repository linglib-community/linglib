module

public import Linglib.Fragments.Shiwilu.Phonology
public import Linglib.Phonology.OptimalityTheory.Correspondence.Deletion
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Phonology.Prosody.Mora
public import Linglib.Phonology.Segmental.NaturalClass
public import Studies.BroselowChenHuffman1997
public import Studies.Hayes1989

/-!
# Vásquez-Aguilar, Gordon, Katsika and Gries (2026): Moraicity, gemination and syllable well-formedness in Shiwilu

The interior vowel of Shiwilu, [the one non-low central vowel](##naturalClass_interior), never
bears a mora, and a consonant after it geminates so that its syllable has one. The paper derives
this from two constraints, one requiring every syllable to have a mora and one banning moraic
interior vowels, both ranked above the ban on moraic consonants. [Its ranking selects the attested
output of every tableau](##figure5_derives), and [reranking the three constraints gives the
three outcomes for an interior vowel before a consonant](##typology): Shiwilu's geminate, the
moraless syllable of Piuma Paiwan and Northwest Mari, and the moraic interior vowel.

## Implementation notes

* A candidate is the correspondence of its output with the input together with the prosodic
  structure of the output, a `Prosody.MoraicForm` over the output string, so that MAX-IO reads
  the correspondence and the markedness constraints the structure.
* *μ/x counts the morae linked to a single segment of the class x, the restriction the paper
  places on it, and a geminate tap is a tap with two association lines.
* The hypothetical word boundary has /ta/ for the following word, so that its first syllable
  has a nucleus.
* Of the arrows the paper draws, one is not a ranking argument from the printed tableaux:
  [a ranking with *μ/C over *GemTap selects every attested output](##gemTap_unforced). The arrow
  from CrispEdge to *μ/C also follows from the arrows through Max-IntV.

## TODO

* The durational evidence, by which the interior vowel is the shortest vowel and a consonant is
  longest after it.
* The constraint against a moraic glottal stop, and the split of *μ/C into obstruents and
  sonorants that the comparison with Kwak'wala needs.
* The typology of mora augmentation, which needs the Stress-to-Weight Principle and a foot.

## References

* [vasquez-aguilar-etal-2026]
* [broselow-chen-huffman-1997]
* [hayes-1989]
* [prince-smolensky-1993]
* [mccarthy-prince-1995]
-/

@[expose] public section

namespace VasquezAguilarEtAl2026

open OptimalityTheory Phonology Prosody Shiwilu

/-! ### Interior vowels -/

/-- The description of an interior vowel, a non-low central vowel. -/
def interior : Segment :=
  .ofSpecs [(.syllabic, true), (.consonantal, false), (.low, false), (.front, false),
    (.back, false)]

/-- The interior vowel of Shiwilu is /ɘ/ alone; /i u a/ are peripheral (§3.2). -/
theorem naturalClass_interior : interior.naturalClass Shiwilu.inventory = {«ɘ»} := by decide

/-! ### Candidates and constraints -/

/-- A candidate: the correspondence of the output with the input, and the prosodic structure of
the output. -/
structure Candidate where
  /-- The input–output correspondence. -/
  io : Correspondence.Diagram BinaryRole Segment
  /-- The prosodic structure of the output. -/
  form : MoraicForm Segment

/-- The candidate with correspondence `io` whose output form, over the output string of `io`, has
the given lines. -/
def Candidate.ofIO (io : Correspondence.Diagram BinaryRole Segment)
    (wordSyllable : Finset (ℕ × ℕ) := ∅) (syllableMora : Finset (ℕ × Mora) := ∅)
    (wordSegment : Finset (ℕ × ℕ) := ∅) (syllableSegment : Finset (ℕ × ℕ) := ∅)
    (moraSegment : Finset (Mora × ℕ) := ∅) : Candidate :=
  ⟨io, .ofLines (io.form .rhs) wordSyllable syllableMora wordSegment syllableSegment
    moraSegment⟩

section Classes

variable (X : MoraicForm Segment)

/-- The segment at slot `i` is in the class `P`. -/
def HasAt (P : Segment → Prop) (i : ℕ) : Prop := ∃ h : i < X.melody.length, P X.melody[i]

instance (P : Segment → Prop) [DecidablePred P] (i : ℕ) : Decidable (HasAt X P i) :=
  inferInstanceAs (Decidable (∃ h : i < X.melody.length, P X.melody[i]))

/-- Mora `m` is linked to its head alone, and its head is in the class `P`. -/
def BearsOnly (P : Segment → Prop) (m : Mora) : Prop :=
  X.moraSpan m = {m.slot} ∧ ∃ x ∈ X.head m, P x

instance (P : Segment → Prop) [DecidablePred P] (m : Mora) : Decidable (BearsOnly X P m) :=
  inferInstanceAs (Decidable (_ ∧ ∃ x ∈ X.head m, P x))

end Classes

/-- HEADEDNESS-σ (12): a violation for each syllable without a mora. -/
def headedness : Constraint Candidate := fun c ↦
  (c.form.syllables.filter (c.form.weight · = 0)).card

/-- *μ/x (13), (14): a violation for each mora linked to a single segment of the class `P`. -/
def starMu (P : Segment → Prop) [DecidablePred P] : Constraint Candidate := fun c ↦
  (c.form.morae.filter (BearsOnly c.form P)).card

/-- NOSHAREDMORA, from [broselow-chen-huffman-1997]: a violation for each mora linked to more
than one segment. -/
def noSharedMora : Constraint Candidate := BroselowChenHuffman1997.noSharedMora.comap (·.form)

/-- ONSET: a violation for each syllable without an onset. -/
def onset : Constraint Candidate := fun c ↦
  (c.form.syllables.filter (c.form.onset · = ∅)).card

/-- *GEMTAP (20): a violation for each tap with two association lines. -/
def gemTap : Constraint Candidate := fun c ↦
  (c.form.slots.filter fun i ↦
    HasAt c.form (·.HasValue .tap true) i ∧ 2 ≤ c.form.lineCount i).card

/-- CRISPEDGE(PRWD) (18): a violation for each consonant that two prosodic words dominate. -/
def crispEdge : Constraint Candidate := fun c ↦
  (c.form.slots.filter fun i ↦ HasAt c.form Segment.IsConsonant i ∧
    1 < (c.form.words.filter (i ∈ c.form.wordYield ·)).card).card

/-- MAX-IO(INTV): a violation for each interior vowel of the input without a correspondent. -/
def maxIntV : Constraint Candidate := fun c ↦
  c.io.maxViolAt (fun i ↦ ∃ x ∈ (c.io.form .lhs)[i]?, interior ≤ x) .lhs .rhs

/-- The constraints of the analysis. -/
inductive Con
  | gemTap
  | starMuIntV
  | headedness
  | noSharedMora
  | crispEdge
  | maxIntV
  | onset
  | starMuC
  deriving DecidableEq, Fintype, Repr

/-- The constraint set. -/
def con : ConstraintSet Candidate Con
  | .gemTap => gemTap
  | .starMuIntV => starMu (interior ≤ ·)
  | .headedness => headedness
  | .noSharedMora => noSharedMora
  | .crispEdge => crispEdge
  | .maxIntV => maxIntV
  | .onset => onset
  | .starMuC => starMu Segment.IsConsonant

/-- The solid arrows of Figure 5, each from a dominating constraint to a dominated one. -/
def figure5 : List (Con × Con) :=
  [(.gemTap, .onset), (.gemTap, .starMuC), (.starMuIntV, .onset), (.starMuIntV, .starMuC),
    (.headedness, .onset), (.headedness, .starMuC), (.noSharedMora, .starMuC),
    (.crispEdge, .maxIntV), (.crispEdge, .starMuC), (.maxIntV, .starMuC)]

/-- The arrows of Figure 5 other than *GemTap over *μ/C. -/
def required : List (Con × Con) := figure5.erase (.gemTap, .starMuC)

/-! ### The tableaux -/

/-- The input of (15), /ð̞ɘk/ 'water'. -/
def input15 : List Segment := [«ð̞», «ɘ», k]

/-- The candidates of (15). -/
inductive C15 | a | b | c | d
  deriving DecidableEq, Fintype, Repr

/-- The candidates of (15): the coda bears the mora (a), the interior vowel bears it (b), the
syllable has none (c), and the vowel and coda share it (d). -/
def cand15 : C15 → Candidate
  | .a => .ofIO (.identity input15) (syllableMora := {(1, .of 2)})
    (syllableSegment := {(1, 0), (1, 1)}) (moraSegment := {(.of 2, 2)})
  | .b => .ofIO (.identity input15) (syllableMora := {(1, .of 1)})
    (syllableSegment := {(1, 0), (1, 2)}) (moraSegment := {(.of 1, 1)})
  | .c => .ofIO (.identity input15) (syllableSegment := {(1, 0), (1, 1), (1, 2)})
  | .d => .ofIO (.identity input15) (syllableMora := {(1, .of 1)}) (syllableSegment := {(1, 0)})
    (moraSegment := {(.of 1, 1), (.of 1, 2)})

/-- The input of (16), /kɘki/ 'sun'. -/
def input16 : List Segment := [k, «ɘ», k, i]

/-- The candidates of (16). -/
inductive C16 | a | b | c
  deriving DecidableEq, Fintype, Repr

/-- The candidates of (16): the medial /k/ geminates (a), the first syllable has no mora (b),
and the interior vowel bears it (c). -/
def cand16 : C16 → Candidate
  | .a => .ofIO (.identity input16) (syllableMora := {(1, .of 2), (3, .of 3)})
    (syllableSegment := {(1, 0), (1, 1), (3, 2)}) (moraSegment := {(.of 2, 2), (.of 3, 3)})
  | .b => .ofIO (.identity input16) (syllableMora := {(3, .of 3)})
    (syllableSegment := {(1, 0), (1, 1), (3, 2)}) (moraSegment := {(.of 3, 3)})
  | .c => .ofIO (.identity input16) (syllableMora := {(1, .of 1), (3, .of 3)})
    (syllableSegment := {(1, 0), (3, 2)}) (moraSegment := {(.of 1, 1), (.of 3, 3)})

/-- The input of (17), /ð̞aka/ 'muena tree'. -/
def input17 : List Segment := [«ð̞», a, k, a]

/-- The candidates of (17). -/
inductive C17 | a | b
  deriving DecidableEq, Fintype, Repr

/-- The candidates of (17): no gemination after the peripheral vowel (a), and gemination (b). -/
def cand17 : C17 → Candidate
  | .a => .ofIO (.identity input17) (syllableMora := {(1, .of 1), (3, .of 3)})
    (syllableSegment := {(1, 0), (3, 2)}) (moraSegment := {(.of 1, 1), (.of 3, 3)})
  | .b => .ofIO (.identity input17) (syllableMora := {(1, .of 1), (1, .of 2), (3, .of 3)})
    (syllableSegment := {(1, 0), (3, 2)}) (moraSegment := {(.of 1, 1), (.of 2, 2), (.of 3, 3)})

/-- The input of (19), /pakɘ#ta/, an interior vowel at the end of a word before /ta/. -/
def input19 : List Segment := [p, a, k, «ɘ», t, a]

/-- The candidates of (19). -/
inductive C19 | a | b
  deriving DecidableEq, Fintype, Repr

/-- The candidates of (19): the interior vowel deletes (a), and the following word's first
consonant geminates to close its syllable (b). -/
def cand19 : C19 → Candidate
  | .a => .ofIO (.eraseIdx input19 ⟨3, by decide⟩) (wordSyllable := {(1, 1), (4, 4)})
    (syllableMora := {(1, .of 1), (4, .of 4)}) (syllableSegment := {(1, 0), (1, 2), (4, 3)})
    (moraSegment := {(.of 1, 1), (.of 4, 4)})
  | .b => .ofIO (.identity input19) (wordSyllable := {(1, 1), (1, 3), (5, 5)})
    (syllableMora := {(1, .of 1), (3, .of 4), (5, .of 5)})
    (syllableSegment := {(1, 0), (3, 2), (3, 3), (5, 4)})
    (moraSegment := {(.of 1, 1), (.of 4, 4), (.of 5, 5)})

/-- The input of (21), /kɘɾutɘk/ 'kind of fish'. -/
def input21 : List Segment := [k, «ɘ», «ɾ», u, t, «ɘ», k]

/-- The candidates of (21). -/
inductive C21 | a | b | c | d
  deriving DecidableEq, Fintype, Repr

/-- The candidates of (21): the tap is a moraic coda (a), an onset after a moraic interior vowel
(b), an onset after a moraless syllable (c), and a geminate (d). -/
def cand21 : C21 → Candidate
  | .a => .ofIO (.identity input21) (syllableMora := {(1, .of 2), (3, .of 3), (5, .of 6)})
    (syllableSegment := {(1, 0), (1, 1), (5, 4), (5, 5)})
    (moraSegment := {(.of 2, 2), (.of 3, 3), (.of 6, 6)})
  | .b => .ofIO (.identity input21) (syllableMora := {(1, .of 1), (3, .of 3), (5, .of 6)})
    (syllableSegment := {(1, 0), (3, 2), (5, 4), (5, 5)})
    (moraSegment := {(.of 1, 1), (.of 3, 3), (.of 6, 6)})
  | .c => .ofIO (.identity input21) (syllableMora := {(3, .of 3), (5, .of 6)})
    (syllableSegment := {(1, 0), (1, 1), (3, 2), (5, 4), (5, 5)})
    (moraSegment := {(.of 3, 3), (.of 6, 6)})
  | .d => .ofIO (.identity input21) (syllableMora := {(1, .of 2), (3, .of 3), (5, .of 6)})
    (syllableSegment := {(1, 0), (1, 1), (3, 2), (5, 4), (5, 5)})
    (moraSegment := {(.of 2, 2), (.of 3, 3), (.of 6, 6)})

-- The candidates are well formed and free of crossing lines.
theorem wellFormed_noCrossing_cand :
    (∀ x, (cand15 x).form.WellFormed ∧ (cand15 x).form.NoCrossing) ∧
    (∀ x, (cand16 x).form.WellFormed ∧ (cand16 x).form.NoCrossing) ∧
    (∀ x, (cand17 x).form.WellFormed ∧ (cand17 x).form.NoCrossing) ∧
    (∀ x, (cand19 x).form.WellFormed ∧ (cand19 x).form.NoCrossing) ∧
    (∀ x, (cand21 x).form.WellFormed ∧ (cand21 x).form.NoCrossing) := by
  decide

/-! ### Figure 5 derives the tableaux -/

section Derivation

variable {r : Ranking Con 8}

-- (15), (16), (17), (19), (21) follow from the arrows of Figure 5 but *GemTap over *μ/C.
theorem derives_of_required (hr : ∀ p ∈ required, r.Dominates p.1 p.2) :
    (Tableau.ofRanking (con.comap cand15) r Finset.univ).optimal = {.a} ∧
    (Tableau.ofRanking (con.comap cand16) r Finset.univ).optimal = {.a} ∧
    (Tableau.ofRanking (con.comap cand17) r Finset.univ).optimal = {.a} ∧
    (Tableau.ofRanking (con.comap cand19) r Finset.univ).optimal = {.a} ∧
    (Tableau.ofRanking (con.comap cand21) r Finset.univ).optimal = {.a} := by
  have hR : (fun i j ↦ (i, j) ∈ required) ≤ r.Dominates := fun i j h ↦ hr (i, j) h
  exact ⟨Tableau.ofRanking_optimal_eq_singleton_of_rel hR (by simp) (by decide),
    Tableau.ofRanking_optimal_eq_singleton_of_rel hR (by simp) (by decide),
    Tableau.ofRanking_optimal_eq_singleton_of_rel hR (by simp) (by decide),
    Tableau.ofRanking_optimal_eq_singleton_of_rel hR (by simp) (by decide),
    Tableau.ofRanking_optimal_eq_singleton_of_rel hR (by simp) (by decide)⟩

/-- Every ranking that respects Figure 5 selects the attested outputs: the coda bears the mora
of /ð̞ɘk/ (15), the consonant after the interior vowel geminates in /kɘki/ (16) but not after a
peripheral vowel in /ð̞aka/ (17), the interior vowel deletes rather than geminate a consonant
across a word boundary (19), and the tap is a moraic coda (21). -/
theorem figure5_derives (hr : ∀ p ∈ figure5, r.Dominates p.1 p.2) :
    (Tableau.ofRanking (con.comap cand15) r Finset.univ).optimal = {.a} ∧
    (Tableau.ofRanking (con.comap cand16) r Finset.univ).optimal = {.a} ∧
    (Tableau.ofRanking (con.comap cand17) r Finset.univ).optimal = {.a} ∧
    (Tableau.ofRanking (con.comap cand19) r Finset.univ).optimal = {.a} ∧
    (Tableau.ofRanking (con.comap cand21) r Finset.univ).optimal = {.a} :=
  derives_of_required fun p hp ↦ hr p (List.mem_of_mem_erase hp)

end Derivation

/-- No printed tableau decides between *GemTap and *μ/C: a ranking that respects every other arrow
of Figure 5 but puts *μ/C above *GemTap selects every attested output. -/
theorem gemTap_unforced : ∃ r : Ranking Con 8, r.Dominates .starMuC .gemTap ∧
    (Tableau.ofRanking (con.comap cand15) r Finset.univ).optimal = {.a} ∧
    (Tableau.ofRanking (con.comap cand16) r Finset.univ).optimal = {.a} ∧
    (Tableau.ofRanking (con.comap cand17) r Finset.univ).optimal = {.a} ∧
    (Tableau.ofRanking (con.comap cand19) r Finset.univ).optimal = {.a} ∧
    (Tableau.ofRanking (con.comap cand21) r Finset.univ).optimal = {.a} :=
  let r : Ranking Con 8 := .ofList [.starMuIntV, .headedness, .noSharedMora, .crispEdge, .maxIntV,
    .starMuC, .gemTap, .onset]
  ⟨r, by decide, derives_of_required (by decide)⟩

/-- A total ranking that respects Figure 5. -/
def shiwilu : Ranking Con 8 :=
  .ofList [.gemTap, .starMuIntV, .headedness, .noSharedMora, .crispEdge, .maxIntV, .onset,
    .starMuC]

-- Figure 5 has a linear extension, so that `figure5_derives` is not vacuous.
theorem shiwilu_respects : ∀ p ∈ figure5, shiwilu.Dominates p.1 p.2 := by decide

/-! ### The syllabification of the tap -/

/-- The reranking of (22), with HEADEDNESS-σ over ONSET over *μ/INTV. -/
def tapOnset₁ : Ranking Con 8 :=
  .ofList [.gemTap, .headedness, .noSharedMora, .crispEdge, .maxIntV, .onset, .starMuIntV,
    .starMuC]

/-- The reranking of (23), with *μ/INTV over ONSET over HEADEDNESS-σ. -/
def tapOnset₂ : Ranking Con 8 :=
  .ofList [.gemTap, .starMuIntV, .noSharedMora, .crispEdge, .maxIntV, .onset, .headedness,
    .starMuC]

-- (22): the tap is an onset and the interior vowel is moraic.
theorem tapOnset₁_optimal :
    (Tableau.ofRanking (con.comap cand21) tapOnset₁ Finset.univ).optimal = {.b} := by decide

-- (23): the tap is an onset and its syllable has no mora.
theorem tapOnset₂_optimal :
    (Tableau.ofRanking (con.comap cand21) tapOnset₂ Finset.univ).optimal = {.c} := by decide

/-! ### The typology of interior vowels -/

/-- The constraint each candidate of (16) violates: *μ/C for the geminate, HEADEDNESS-σ for the
moraless syllable, and *μ/INTV for the moraic interior vowel. -/
def violated : C16 → Con
  | .a => .starMuC
  | .b => .headedness
  | .c => .starMuIntV

theorem violated_injective : Function.Injective violated := by decide

-- Each candidate of (16) violates its constraint once and no other.
theorem con_cand16 : ∀ i x, con i (cand16 x) = if i = violated x then 1 else 0 := by decide

/-- Under any ranking, a consonant after the interior vowel geminates, as in Shiwilu, the
interior vowel's syllable has no mora, as in Piuma Paiwan and Northwest Mari, or the interior
vowel bears the mora; each outcome wins exactly when the one constraint it violates is ranked
below the two the others violate (25). -/
theorem typology (r : Ranking Con 8) (x : C16) :
    (Tableau.ofRanking (con.comap cand16) r Finset.univ).optimal = {x} ↔
      ∀ y, y ≠ x → r.Dominates (violated y) (violated x) := by
  have key (p q : Prop) [Decidable p] [Decidable q] :
      ((if p then 1 else 0 : ℕ) < if q then 1 else 0) ↔ ¬p ∧ q := by
    split_ifs <;> simp_all
  simp only [Tableau.ofRanking_optimal_eq_singleton_iff, Finset.mem_univ, true_and,
    forall_const, ConstraintSet.comap, Constraint.comap, Function.comp_apply, con_cand16, key]
  refine forall₂_congr fun y hy ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨_, ⟨-, rfl⟩, h⟩
    exact h _ ⟨violated_injective.ne hy.symm, rfl⟩
  · exact ⟨_, ⟨violated_injective.ne hy, rfl⟩, fun j ⟨_, hj⟩ ↦ hj ▸ h⟩

-- (25b): the consonant geminates exactly when HEADEDNESS-σ and *μ/INTV both dominate *μ/C.
theorem gemination_iff (r : Ranking Con 8) :
    (Tableau.ofRanking (con.comap cand16) r Finset.univ).optimal = {.a} ↔
      r.Dominates .headedness .starMuC ∧ r.Dominates .starMuIntV .starMuC := by
  rw [typology]
  exact ⟨fun h ↦ ⟨h .b (by decide), h .c (by decide)⟩,
    fun ⟨h₁, h₂⟩ y hy ↦ by cases y <;> first | exact absurd rfl hy | assumption⟩

/-! ### Consistency with Hayes (1989) -/

-- The input of (16), syllabified as [hayes-1989] syllabifies it, every vowel bearing its mora
-- and no coda one, is the candidate with the moraic interior vowel.
theorem syllabify_input16 :
    Hayes1989.Underlying.syllabify (input16.zip [0, 1, 0, 1]) false = (cand16 .c).form := by
  decide

-- The geminate of (16a) is a geminate of [hayes-1989], one consonant with two lines.
theorem lineCount_geminate : (cand16 .a).form.lineCount 2 = 2 := by decide

end VasquezAguilarEtAl2026
