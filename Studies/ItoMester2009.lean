module

public import Linglib.Phonology.Prosody.Word
public import Linglib.Phonology.Prosody.Match
public import Linglib.Phonology.OptimalityTheory.Tableau

/-!
# Itô and Mester (2009): The Extended Prosodic Word

This file formalizes the prosodification of function-word complexes in [ito-mester-2009]. A
function word followed by its lexical host, English *the dinosaurs* or German *'ne Zigarette*,
has the four prosodic sites of (25): a prosodic word of its own, fusion into the host's word,
adjunction to the host's word, and attachment to the phonological phrase, (20a)–(20d). Each site
violates exactly one of the constraints FtBin, Lex-to-ω, No-Recursion and Parse-into-ω, so the
factorial typology of the four constraints yields the four sites (`fullOmega_optimum` and its
three siblings). With FtBin and Lex-to-ω undominated, the tableaux (33) and (34) leave adjunction
and phrase attachment tied, and the ranking of Parse-into-ω above No-Recursion, which the
evidence of Section 3 supports for English and German, selects the recursive word
`[ω fnc [ω lex]]` (`omegaAdjunction_optimum`), against [selkirk-1996]'s phrase attachment.

## Implementation notes

* Candidates are `Prosody.Tree`s and constraints `Constraint Tree` values: No-Recursion is the
  substrate's `Prosody.noRec` and Parse-into-ω its `Prosody.parseInto`; FtBin at the word level
  is defined here, and Lex-to-ω(L) is the substrate's Align-L of the lexical word's span to the
  ω spans.
* The tableau engine is `OptimalityTheory.Tableau.ofList`; the winning recursive structure
  is a legal prosodic word of the substrate, No-Recursion being violable.

## References

* [ito-mester-2009]
* [selkirk-1996]
* [mccarthy-prince-1993b]
-/

@[expose] public section

namespace ItoMester2009

open Prosody OptimalityTheory

/-! ### Function-word constraints -/

/-- FtBin at the word level assigns a violation to each ω-node whose mora count is below a foot,
such as a subminimal function word parsed as its own ω. -/
def subminimalOmega : Constraint Tree := fun t ↦ go t where
  go : Tree → Nat
    | .node a cs =>
        (if a.level = .om ∧ moraCount (.node a cs) < 2 then 1 else 0)
          + goList cs
  goList : List Tree → Nat
    | []      => 0
    | t :: ts => go t + goList ts

/-! ### The four sites of (25) -/

/-- The function word is one light syllable. -/
def fncσ : Tree := .σ .light

/-- The lexical word as a well-formed, bimoraic ω. -/
def lexω : Tree := .om [.ft false [.σ .heavy]]

/-- `[φ [ω fnc] [ω lex]]` is the full-ω site, (25a) and (20a). -/
def fullOmega : Tree := .ph [.om [fncσ], lexω]

/-- `[ω fnc lex]` is the amalgamated site, (25b) and (20b). -/
def amalgamated : Tree := .om [fncσ, .ft false [.σ .heavy]]

/-- `[ω fnc [ω lex]]` is the ω-adjoined site, (25c) and (20c). -/
def omegaAdjoined : Tree := .om [fncσ, lexω]

/-- `[φ fnc [ω lex]]` is the φ-attached site, (25d) and (20d). -/
def phiAttached : Tree := .ph [fncσ, lexω]

/-- The lexical word is the second syllable of each site. -/
abbrev lex : List (ℕ × ℕ) := [(1, 2)]

/-- Lex-to-ω(L), (12a), the Align(Lex, Left, ω, Left) of [mccarthy-prince-1993b]: a violation when
no prosodic word begins where the lexical word does, as in the amalgamated site (20b). -/
def lexToOmega : Constraint Tree := Constraint.alignLeft.comap fun t ↦ (lex, levelSpans .om t)

/-- The candidate set. -/
def candidates : Finset Tree := {fullOmega, amalgamated, omegaAdjoined, phiAttached}

-- (20)
theorem one_violation_each :
    subminimalOmega fullOmega = 1 ∧ lexToOmega amalgamated = 1 ∧
      noRec omegaAdjoined = 1 ∧ parseInto .om phiAttached = 1 := by
  decide

/-! ### The factorial typology and the ranking for English and German -/

theorem fullOmega_optimum :
    (Tableau.ofList candidates [lexToOmega, parseInto .om, noRec, subminimalOmega]).optimal
      = {fullOmega} := by
  decide

theorem amalgamated_optimum :
    (Tableau.ofList candidates [subminimalOmega, parseInto .om, noRec, lexToOmega]).optimal
      = {amalgamated} := by
  decide

theorem phiAttached_optimum :
    (Tableau.ofList candidates [subminimalOmega, lexToOmega, noRec, parseInto .om]).optimal
      = {phiAttached} := by
  decide

-- (33), (34)
theorem adjoined_attached_tie :
    (Tableau.ofList candidates [subminimalOmega, lexToOmega]).optimal
      = {omegaAdjoined, phiAttached} := by
  decide

theorem omegaAdjunction_optimum :
    (Tableau.ofList candidates [subminimalOmega, lexToOmega, parseInto .om, noRec]).optimal
      = {omegaAdjoined} := by
  decide

theorem winner_recursive_isWord : noRec omegaAdjoined = 1 ∧ IsWord omegaAdjoined := by decide

end ItoMester2009
