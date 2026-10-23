module

public import Linglib.Phonology.Prosody.Foot
public import Linglib.Phonology.OptimalityTheory.Constraint.Directional
public import Linglib.Phonology.OptimalityTheory.HarmonicSerialism

/-!
# Lamont (2022): A Restrictive, Parsimonious Theory of Footing in Directional Harmonic Serialism

This file formalizes the theory of quantity-insensitive footing of [lamont-2022c]: Harmonic
Serialism ([prince-smolensky-1993]) with a GEN that parses one foot per step ([pruitt-2010],
[pruitt-2012]) and a CON of directionally evaluated constraints ([eisner-2000],
[lamont-2022b]), whose violation vectors record where violations fall and are compared
lexicographically. Under directional evaluation `Parse(σ)` both motivates iterative footing and
decides where feet surface, so that the alignment constraints of [mccarthy-prince-1993] are
unnecessary, and with `Trochee` and `Iamb` both penalizing monosyllabic feet `FtBin` is
unnecessary too ([martinez-paricio-kager-2015]). The paper's tableaux are run as
`HSDerivation`s over footings: the four-syllable step that parses a leftmost trochee (23), the
odd-parity step that parses a final monosyllable when `Parse(σ)` dominates `Trochee` and leaves
it unfooted otherwise ((24), (25), Murinbata ([street-mollinjin-1981]) against Pintupi
([hansen-hansen-1969])), antepenultimate stress placed by `Iamb` where `Hd(ω)` is active (29),
bidirectional footing from a `FootLeft` foot (33), ternary rhythm from `*FootFoot` (36), and the
exhaustive bidirectional footing of Waorani (43), which parses its suffix string first under
indexed constraints (44). A monosyllabic foot is never optimal while a disyllabic foot can be
parsed (`monosyllable_never_optimal`), and `Parse(σ)` orders the placements of a foot type
((13), (14)).

## Implementation notes

A footing is the library's `Prosody.Footing`, a flat sequence of feet and stray syllables
with no head foot, since the paper does not distinguish primary from secondary stress; a
syllable carries no weight, and for Waorani only its affiliation to stem or suffix. Directional
constraints are `OptimalityTheory.directionalBlock`s, one binary constraint per syllable position,
the block reversed for right-to-left evaluation; a foot-form violation is charged at the
rightmost syllable of its foot, as under left-to-right evaluation, which the paper shows is the
only direction that matters for these constraints in iterative footing. The prosodic-word
constraints `Hd(ω)`, `NonFinality`, `FootLeft`, `FootRight`, and `*FootFoot` are counted, their
direction being irrelevant to a word. Each tableau is a `stepOptimum` computation with
convergence checked at the last step; the factorial typology of §4 is not formalized.

## References

* [lamont-2022c]
* [lamont-2022b], [eisner-2000], [prince-smolensky-1993], [pruitt-2010], [pruitt-2012]
* [mccarthy-prince-1993], [martinez-paricio-kager-2015]
* [street-mollinjin-1981], [hansen-hansen-1969]
-/

@[expose] public section

namespace Lamont2022c

open Prosody OptimalityTheory

variable {S : Type*} [DecidableEq S]

/-! ### GEN (§2.1) -/

/-- The footings that parse exactly one more foot: a stray syllable into a monosyllabic foot,
or two adjacent stray syllables into a trochee or an iamb ((9)); feet are never altered. -/
def parseOne : Footing S → List (Footing S)
  | [] => []
  | .inl f :: rest => (parseOne rest).map (.inl f :: ·)
  | .inr a :: rest =>
      (.inl (Foot.monosyllable a) :: rest) ::
        (match rest with
          | .inr b :: rest' => [.inl (Foot.trochee a b) :: rest', .inl (Foot.iamb a b) :: rest']
          | _ => []) ++ (parseOne rest).map (.inr a :: ·)

/-- GEN: the faithful candidate and the parses of one more foot. -/
def gen (fc : Footing S) : Finset (Footing S) := (fc :: parseOne fc).toFinset

/-! ### Constraints (§2.2) -/

/-- `Parse(σ)` evaluated left to right ((10)): one violation at each unfooted syllable. -/
def parseLR (n : ℕ) : List (Constraint (Footing S)) :=
  directionalBlock n λ i fc => fc.strayMarks.getD i.val 0 = 1

/-- `Parse(σ)` evaluated right to left: the block reversed. -/
def parseRL (n : ℕ) : List (Constraint (Footing S)) := (parseLR n).reverse

/-- The violation vector of a foot-form constraint: a foot with the property `P` is charged
at its rightmost syllable, the left-to-right convention. -/
def footMarks (P : Foot S → Bool) (fc : Footing S) : List ℕ :=
  fc.flatMap (Sum.elim
    (λ f => if P f then List.replicate (f.length - 1) 0 ++ [1] else List.replicate f.length 0)
    (λ _ => [0]))

/-- `Trochee` ((15)): one violation per foot whose rightmost syllable is its head, a
monosyllabic foot included. -/
def trochee (n : ℕ) : List (Constraint (Footing S)) :=
  directionalBlock n λ i fc => (footMarks (λ f => decide f.IsIambic) fc).getD i.val 0 = 1

/-- `Iamb` ((18)): one violation per foot whose leftmost syllable is its head, a monosyllabic
foot included. -/
def iamb (n : ℕ) : List (Constraint (Footing S)) :=
  directionalBlock n λ i fc => (footMarks (λ f => decide f.IsTrochaic) fc).getD i.val 0 = 1

/-- `Hd(ω)` ((26)): the word dominates no foot. -/
def hdWord : Constraint (Footing S) := Constraint.binary (·.feet = [])

/-- `NonFinality` ((28)): the rightmost syllable is footed. -/
def nonFinality : Constraint (Footing S) :=
  Constraint.binary (·.strayMarks.getLast? = some 0)

/-- `FootLeft` ((30)): the leftmost syllable is not leftmost in a foot. -/
def footLeft : Constraint (Footing S) := Constraint.binary (·.strayMarks.head? = some 1)

/-- `FootRight` ((31)): the rightmost syllable is not rightmost in a foot. -/
def footRight : Constraint (Footing S) := Constraint.binary (·.strayMarks.getLast? = some 1)

/-- `*FootFoot` ((34)): one violation per pair of adjacent feet. -/
def starFootFoot : Constraint (Footing S) :=
  λ fc => ((fc.zip fc.tail).filter λ p => p.1.isLeft && p.2.isLeft).length

/-- The violation vector of a block of constraints on a footing. -/
def vec (block : List (Constraint (Footing S))) (fc : Footing S) : List ℕ := block.map (· fc)

/-! ### Iterative footing (§2.2)

Quantity-insensitive words are strings of syllables of type `Unit`. -/

/-- An unfooted syllable. -/
abbrev stray : Foot Unit ⊕ Unit := .inr ()

/-- A trochee `(σ́σ)`. -/
abbrev troch : Foot Unit ⊕ Unit := .inl (Foot.trochee () ())

/-- A monosyllabic foot `(σ́)`. -/
abbrev mono : Foot Unit ⊕ Unit := .inl (Foot.monosyllable ())

/-- A string of `n` unfooted syllables. -/
def strays (n : ℕ) : Footing Unit := List.replicate n stray

/-- `Parse(σ)⇒` orders the placements of a trochee, the leftmost best ((13a)). -/
theorem parseLR_orders_trochees :
    vec (parseLR 4) [troch, stray, stray] < vec (parseLR 4) [stray, troch, stray] ∧
      vec (parseLR 4) [stray, troch, stray] < vec (parseLR 4) [stray, stray, troch] := by
  decide +kernel

/-- `Parse(σ)⇐` orders them the other way, the rightmost best ((14a)). -/
theorem parseRL_orders_trochees :
    vec (parseRL 4) [stray, stray, troch] < vec (parseRL 4) [stray, troch, stray] ∧
      vec (parseRL 4) [stray, troch, stray] < vec (parseRL 4) [troch, stray, stray] := by
  decide +kernel

/-- `Parse(σ)⇒ ≫ Trochee ≫ Iamb`: Murinbata's exhaustive left-to-right trochees ((21), (23),
(24)). -/
def murinbata (n : ℕ) : HSDerivation (Footing Unit) :=
  ⟨gen, parseLR n ++ trochee n ++ iamb n⟩

/-- `Trochee ≫ Parse(σ)⇒ ≫ Iamb`: Pintupi's inexhaustive left-to-right trochees ((22),
(25)). -/
def pintupi (n : ℕ) : HSDerivation (Footing Unit) :=
  ⟨gen, trochee n ++ parseLR n ++ iamb n⟩

/-- (23i): the first step parses a trochee at the left edge. -/
theorem step_23i : (murinbata 4).stepOptimum (strays 4) = {[troch, stray, stray]} := by
  decide +kernel

/-- (23m): the second step foots the remaining two syllables. -/
theorem step_23m : (murinbata 4).stepOptimum [troch, stray, stray] = {[troch, troch]} := by
  decide +kernel

theorem converged_23 : (murinbata 4).Converged [troch, troch] := by decide +kernel

/-- The monosyllabic-foot parses of `/σσσσ/` ((23b–e)). -/
def monoParses : List (Footing Unit) :=
  [[mono, stray, stray, stray], [stray, mono, stray, stray], [stray, stray, mono, stray],
    [stray, stray, stray, mono]]

/-- The six rankings of `Parse(σ)`, `Trochee`, and `Iamb`, evaluated left to right. -/
def rankings (n : ℕ) : List (List (Constraint (Footing Unit))) :=
  [parseLR n ++ trochee n ++ iamb n, parseLR n ++ iamb n ++ trochee n,
    trochee n ++ parseLR n ++ iamb n, trochee n ++ iamb n ++ parseLR n,
    iamb n ++ parseLR n ++ trochee n, iamb n ++ trochee n ++ parseLR n]

/-- A monosyllabic foot is never optimal while a disyllabic foot can be parsed ((23)): under
every ranking of the three constraints, no monosyllabic parse of `/σσσσ/` is in the step
optimum, so `FtBin` is unnecessary. -/
theorem monosyllable_never_optimal :
    ∀ r ∈ rankings 4, ∀ m ∈ monoParses,
      m ∉ (HSDerivation.mk gen r).stepOptimum (strays 4) := by
  decide +kernel

/-- (24): with `Parse(σ)` dominant, the final syllable of an odd-parity word is footed. -/
theorem step_24 :
    (murinbata 5).stepOptimum [troch, troch, stray] = {[troch, troch, mono]} := by
  decide +kernel

/-- (25): with `Trochee` dominant, it stays unfooted and the derivation has converged. -/
theorem converged_25 : (pintupi 5).Converged [troch, troch, stray] := by decide +kernel

/-! ### Non-iterative footing (§2.2)

Where `Hd(ω)` alone motivates a foot, `Iamb⇒` places a trochee as far right as `NonFinality`
allows: antepenultimate stress ((27), (29)). -/

/-- `Hd(ω) ≫ Trochee ≫ NonFinality ≫ Iamb⇒ ≫ Parse(σ)`: Macedonian antepenultimate
stress. -/
def macedonian (n : ℕ) : HSDerivation (Footing Unit) :=
  ⟨gen, hdWord :: trochee n ++ nonFinality :: iamb n ++ parseLR n⟩

/-- (29f): the trochee surfaces one syllable from the right edge. -/
theorem step_29f : (macedonian 4).stepOptimum (strays 4) = {[stray, troch, stray]} := by
  decide +kernel

theorem converged_29 : (macedonian 4).Converged [stray, troch, stray] := by decide +kernel

/-! ### Bidirectional and ternary footing (§2.2)

A foot is first parsed at one edge, satisfying `FootLeft`, then feet are parsed from the other
edge by `Parse(σ)⇐`, with word-internal lapse in odd-parity words ((32), (33)); `*FootFoot`
above `Parse(σ)` leaves a syllable between feet ((35), (36)). -/

/-- `FootLeft ≫ Trochee ≫ Parse(σ)⇐ ≫ Iamb`: Garawa's bidirectional trochees. -/
def garawa (n : ℕ) : HSDerivation (Footing Unit) :=
  ⟨gen, footLeft :: trochee n ++ parseRL n ++ iamb n⟩

theorem step_33b : (garawa 7).stepOptimum (strays 7) = {troch :: strays 5} := by decide +kernel

theorem step_33g : (garawa 7).stepOptimum (troch :: strays 5) = {troch :: strays 3 ++ [troch]} := by
  decide +kernel

theorem step_33i :
    (garawa 7).stepOptimum (troch :: strays 3 ++ [troch]) = {[troch, stray, troch, troch]} := by
  decide +kernel

/-- (33j): the third syllable stays unfooted, `Trochee` dominating `Parse(σ)`. -/
theorem converged_33 : (garawa 7).Converged [troch, stray, troch, troch] := by decide +kernel

/-- `NonFinality ≫ *FootFoot ≫ Parse(σ)⇐ ≫ Trochee ≫ Iamb`: Cayuvava's dactyls. -/
def cayuvava (n : ℕ) : HSDerivation (Footing Unit) :=
  ⟨gen, nonFinality :: starFootFoot :: parseRL n ++ trochee n ++ iamb n⟩

theorem step_36h : (cayuvava 9).stepOptimum (strays 9) = {strays 6 ++ [troch, stray]} := by
  decide +kernel

theorem step_36n :
    (cayuvava 9).stepOptimum (strays 6 ++ [troch, stray]) =
      {strays 3 ++ [troch, stray, troch, stray]} := by
  decide +kernel

theorem step_36q :
    (cayuvava 9).stepOptimum (strays 3 ++ [troch, stray, troch, stray]) =
      {[troch, stray, troch, stray, troch, stray]} := by
  decide +kernel

theorem converged_36 : (cayuvava 9).Converged [troch, stray, troch, stray, troch, stray] := by
  decide +kernel

/-! ### Waorani (§3)

The head foot is parsed at the right edge under `FootRight`, then the suffix string is footed
under the indexed `Parse(σ)ₛᵤffix`, then the stem from the left, with a monosyllabic foot
surfacing only in the stem, since the indexed `Trocheeₛᵤffix` dominates `Parse(σ)ₛᵤffix` while
`Parse(σ)` dominates `Trochee` ((37)–(44)). -/

/-- A syllable's affiliation. -/
inductive Morph
  | stem
  | suffix
  deriving DecidableEq, Repr

/-- The suffix syllables. -/
def Morph.isSuffix : Morph → Bool
  | .suffix => true
  | .stem => false

/-- `Parse(σ)` indexed to the suffix string, evaluated left to right. -/
def parseSuffixLR (n : ℕ) : List (Constraint (Footing Morph)) :=
  directionalBlock n λ i fc =>
    (fc.flatMap (Sum.elim (λ f => List.replicate f.length 0)
      (λ s => [if s.isSuffix then 1 else 0]))).getD i.val 0 = 1

/-- `Trochee` indexed to the suffix string: charged to a foot dominating a suffix syllable. -/
def trocheeSuffix (n : ℕ) : List (Constraint (Footing Morph)) :=
  directionalBlock n λ i fc =>
    (footMarks (λ f => decide f.IsIambic && f.syllables.any Morph.isSuffix) fc).getD i.val 0 = 1

/-- `FootRight ≫ Parse(σ)⇒ ≫ Trochee ≫ Iamb` ((43)), with the indexed `Trocheeₛᵤffix ≫
Parse(σ)ₛᵤffix` between `FootRight` and `Parse(σ)` ((44)). -/
def waorani (n : ℕ) : HSDerivation (Footing Morph) :=
  ⟨gen, footRight :: trocheeSuffix n ++ parseSuffixLR n ++ parseLR n ++ trochee n ++ iamb n⟩

/-- An unfooted stem syllable. -/
abbrev st : Foot Morph ⊕ Morph := .inr .stem

/-- An unfooted suffix syllable. -/
abbrev sf : Foot Morph ⊕ Morph := .inr .suffix

/-- A trochee over two stem syllables. -/
abbrev trochSt : Foot Morph ⊕ Morph := .inl (Foot.trochee .stem .stem)

/-- A trochee over two suffix syllables. -/
abbrev trochSf : Foot Morph ⊕ Morph := .inl (Foot.trochee .suffix .suffix)

/-- A monosyllabic foot over a stem syllable. -/
abbrev monoSt : Foot Morph ⊕ Morph := .inl (Foot.monosyllable .stem)

/-- (43): a pentasyllabic stem is footed from the right edge, then from the left, and a
monosyllabic foot surfaces word-medially. -/
theorem steps_43 :
    (waorani 5).stepOptimum [st, st, st, st, st] = {[st, st, st, trochSt]} ∧
    (waorani 5).stepOptimum [st, st, st, trochSt] = {[trochSt, st, trochSt]} ∧
    (waorani 5).stepOptimum [trochSt, st, trochSt] = {[trochSt, monoSt, trochSt]} ∧
    (waorani 5).Converged [trochSt, monoSt, trochSt] := by
  decide +kernel

/-- (44): with a pentasyllabic suffix string, the head foot is parsed at the right edge, the
suffix string is footed from its left edge before the stem, the stem is exhaustively footed,
and the remaining suffix syllable stays unfooted. -/
theorem steps_44 :
    (waorani 10).stepOptimum [st, st, st, st, st, sf, sf, sf, sf, sf] =
        {[st, st, st, st, st, sf, sf, sf, trochSf]} ∧
      (waorani 10).stepOptimum [st, st, st, st, st, sf, sf, sf, trochSf] =
        {[st, st, st, st, st, trochSf, sf, trochSf]} ∧
      (waorani 10).stepOptimum [st, st, st, st, st, trochSf, sf, trochSf] =
        {[trochSt, st, st, st, trochSf, sf, trochSf]} ∧
      (waorani 10).stepOptimum [trochSt, st, st, st, trochSf, sf, trochSf] =
        {[trochSt, trochSt, st, trochSf, sf, trochSf]} ∧
      (waorani 10).stepOptimum [trochSt, trochSt, st, trochSf, sf, trochSf] =
        {[trochSt, trochSt, monoSt, trochSf, sf, trochSf]} ∧
      (waorani 10).Converged [trochSt, trochSt, monoSt, trochSf, sf, trochSf] := by
  decide +kernel

end Lamont2022c
