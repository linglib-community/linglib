module

public import Linglib.Phonology.Prosody.Word
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
  and Lex-to-ω are defined here, the latter for the fixed lexical word `lexω`.
* The tableau engine is `OptimalityTheory.Tableau.ofList`; the winning recursive structure
  is a legal prosodic word of the substrate, No-Recursion being violable.

## References

* [ito-mester-2009]
* [selkirk-1996]
* [mccarthy-prince-1993]
-/

@[expose] public section

namespace ItoMester2009

open Prosody OptimalityTheory

/-! ### Function-word constraints -/

/-- FtBin at the word level assigns a violation to each ω-node whose mora count is below a foot,
such as a subminimal function word parsed as its own ω. -/
def subminimalOmega : Constraint Tree := λ t => go t where
  go : Tree → Nat
    | .node a cs =>
        (if a.level = .om ∧ moraCount (.node a cs) < 2 then 1 else 0)
          + goList cs
  goList : List Tree → Nat
    | []      => 0
    | t :: ts => go t + goList ts

/-- Whether the lexical word `lex` is realised as its own ω-node somewhere in the tree. -/
def lexHasOmega (lex : Tree) : Tree → Bool := λ t => go t where
  go : Tree → Bool
    | .node a cs => (decide (a.level = .om) && decide ((.node a cs : Tree) = lex)) || goList cs
  goList : List Tree → Bool
    | []      => false
    | t :: ts => go t || goList ts

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

/-- Lex-to-ω, (12), after the alignment constraint of [mccarthy-prince-1993], assigns a
violation when the lexical word is not a ω of its own. -/
def lexToOmega : Constraint Tree := λ t => if lexHasOmega lexω t then 0 else 1

/-- The candidate set. -/
def candidates : Finset Tree := {fullOmega, amalgamated, omegaAdjoined, phiAttached}

/-- Each site violates exactly one of the four constraints, (20). -/
theorem one_violation_each :
    subminimalOmega fullOmega = 1 ∧ lexToOmega amalgamated = 1 ∧
      noRec omegaAdjoined = 1 ∧ parseInto .om phiAttached = 1 := by
  decide

/-! ### The factorial typology and the ranking for English and German -/

/-- Demoting FtBin makes the function word its own prosodic word. -/
theorem fullOmega_optimum :
    (Tableau.ofList candidates [lexToOmega, parseInto .om, noRec, subminimalOmega]).optimal
      = {fullOmega} := by
  decide

/-- Demoting Lex-to-ω fuses the function word into the host. -/
theorem amalgamated_optimum :
    (Tableau.ofList candidates [subminimalOmega, parseInto .om, noRec, lexToOmega]).optimal
      = {amalgamated} := by
  decide

/-- Demoting Parse-into-ω attaches the function word to the phrase, [selkirk-1996]'s site. -/
theorem phiAttached_optimum :
    (Tableau.ofList candidates [subminimalOmega, lexToOmega, noRec, parseInto .om]).optimal
      = {phiAttached} := by
  decide

/-- With FtBin and Lex-to-ω alone ranked, the ω-adjoined and φ-attached sites tie, each
fulfilling both, (33) and (34). -/
theorem adjoined_attached_tie :
    (Tableau.ofList candidates [subminimalOmega, lexToOmega]).optimal
      = {omegaAdjoined, phiAttached} := by
  decide

/-- The function-word complex of English and German is prosodified by ω-adjunction, since under
FtBin, Lex-to-ω ≫ Parse-into-ω ≫ No-Recursion the recursive `[ω fnc [ω lex]]` is the unique
optimum. -/
theorem omegaAdjunction_optimum :
    (Tableau.ofList candidates [subminimalOmega, lexToOmega, parseInto .om, noRec]).optimal
      = {omegaAdjoined} := by
  decide

/-- The winning structure is recursive, ω dominating ω, and a legal prosodic word of the
substrate, so No-Recursion is violable, not part of well-formedness. -/
theorem winner_recursive_isWord : noRec omegaAdjoined = 1 ∧ IsWord omegaAdjoined := by decide

end ItoMester2009
