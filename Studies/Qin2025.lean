module

public import Linglib.Morphology.Root.Basic
public import Linglib.Data.Wordlist.Qin2025
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Qin (2025): Canonical and Non-Canonical Roots: The Diversity of Roots in Mandarin Chinese

This file formalizes [qin-2025]'s canonical typology of roots. The base definition, a
morphologically unanalyzable form that serves as a morphological core of word formation, is the
substrate's `Morphology.Morph.IsCoreIn`, and the paper's *-fer* shows that the judgment is formal
rather than semantic: *-fer* is a core of the primary word *refer* though it has no meaning of its
own (`fer_core`). Four criteria (Table 1), boundness, positional flexibility, phonological
richness, and meaning lexicality, span a space of sixteen cells anchored by the canonical root
that meets all four, and Fig. 1's one way of being canonical against fifteen of being
non-canonical is the binomial count of the tiers (`tier_card`). The case study classifies 122
Mandarin morphemes (Appendix A): the forms carry the appendix's codes on the four criteria, its
five groups are the number of criteria a form fails (`forms_group`), and the property of the
distribution the paper singles out holds of every form, that a phonologically deficient
morpheme, toneless in a tone language, is maximally non-canonical (`deficient_maximal`). The
tiers run from the canonical 厂 *chǎng* of Table 3 through 不 *bù*, 霸 *bà*, and 性 *xìng* to the
toneless 边 *-bian* and 个 *-ge* (`mandarin_tiers`).

## Implementation notes

The appendix's codes are the features of each form's cell in the data: F or B for boundness, FLEX,
SL, or SR for position, 1 or TL for phonology, and L or NL for meaning. A row reads them as a
Boolean judgment on each criterion, the canonical value being `true`; the two fixed positions SL and
SR both count as fixed. The appendix's group is the paper's analysis of the form. The counts of
Tables 2 and 4 are the distribution of the forms and are not restated.

## TODO

The paper says that six of the unattested cells of the space require phonological deficiency;
the appendix leaves seven such cells unattested, since only the maximally non-canonical cell
contains a toneless morpheme, and the cell of free, fixed, toned, lexical morphemes is unattested
as well.

## References

* [qin-2025]
* [bloomfield-1933]
-/

@[expose] public section

namespace Qin2025

open Morphology Data.Wordlist

/-! ### The base definition and *-fer* (§3.1) -/

/-- The bound prefix of *refer*. -/
def re : Morph := .pref "re"

/-- *-fer*, a bound root with no identifiable meaning. -/
def fer : Morph := .root "fer"

/-- The bound prefix of *confer*. -/
def con : Morph := .pref "con"

/-- The mini-fragment *refer* and *confer*, both free forms and both primary, since neither
*re-*, *con-*, nor *-fer* is free. -/
def ferWords : List (List Morph) := [[re, fer], [con, fer]]

/-- *-fer* is a morphological core: it occurs in the primary word *refer*. -/
theorem fer_core : fer.IsCoreIn ferWords ferWords := by decide

/-! ### The four criteria and the theoretical space (§3.2, §3.3) -/

/-- A morpheme's judgment on the four criteria of Table 1, whether it is free, positionally
flexible, phonologically rich, and lexical in meaning. -/
structure Row where
  /-- Whether the morpheme is free rather than bound, criterion C1. -/
  c1 : Bool
  /-- Whether the morpheme is positionally flexible rather than fixed, criterion C2. -/
  c2 : Bool
  /-- Whether the morpheme is phonologically rich rather than deficient, criterion C3. -/
  c3 : Bool
  /-- Whether the morpheme is lexical rather than less lexical in meaning, criterion C4. -/
  c4 : Bool
  deriving DecidableEq, Repr, Fintype

/-- The number of criteria a row fails, its distance from the canonical root. -/
def Row.violations (r : Row) : ℕ :=
  (if r.c1 then 0 else 1) + (if r.c2 then 0 else 1) + (if r.c3 then 0 else 1) +
    (if r.c4 then 0 else 1)

/-- A canonical root satisfies all four criteria. -/
def Row.IsCanonical (r : Row) : Prop := r.violations = 0

instance (r : Row) : Decidable r.IsCanonical := inferInstanceAs (Decidable (r.violations = 0))

/-- The theoretical space of roots has sixteen cells (Fig. 1). -/
theorem space_card : Fintype.card Row = 16 := by decide

/-- Fig. 1 tiers the cells by the criteria they fail. There are `4.choose k` ways to fail exactly
`k` criteria, so fifteen ways of being non-canonical against one of being canonical. -/
theorem tier_card :
    ∀ k : Fin 5, (Finset.univ.filter fun r : Row ↦ r.violations = k).card = Nat.choose 4 k := by
  decide

/-! ### The Mandarin case study (§4, Appendix A) -/

/-- A form's judgments on the four criteria, read from the appendix's codes. -/
def interpret (f : Form Wordlist.Cell) : Option Row := do
  let c1 ← match (f.cell.boundness : Option Wordlist.Boundness) with
    | some .free => some true
    | some .bound => some false
    | none => none
  let c2 ← match (f.cell.positionalFlexibility : Option Wordlist.PositionalFlexibility) with
    | some .flexible => some true
    | some .left | some .right => some false
    | none => none
  let c3 ← match (f.cell.phonologicalRichness : Option Wordlist.PhonologicalRichness) with
    | some .one => some true
    | some .toneless => some false
    | none => none
  let c4 ← match (f.cell.meaningLexicality : Option Wordlist.MeaningLexicality) with
    | some .lexical => some true
    | some .nonLexical => some false
    | none => none
  pure ⟨c1, c2, c3, c4⟩

/-- The number of criteria a form fails. -/
def violations? (f : Form Wordlist.Cell) : Option ℕ := (interpret f).map Row.violations

/-- The appendix's group of a form, canonical roots first, then non-canonical roots by the number
of criteria violated. -/
def group? : String → Option ℕ
  | "1" => some 0
  | "2" => some 1
  | "3" => some 2
  | "4" => some 3
  | "5" => some 4
  | _ => none

/-- Every form is classified on all four criteria, and its group is the number it fails. -/
theorem forms_group :
    ∀ a ∈ Wordlist.analyses, group? a.group = violations? a.form ∧ (violations? a.form).isSome := by
  decide +kernel

/-- A phonologically deficient morpheme is maximally non-canonical: only the bottom cell of the
space holds a toneless morpheme. -/
theorem deficient_maximal :
    ∀ f ∈ Wordlist.all, ∀ row ∈ interpret f, row.c3 = false → row.violations = 4 := by
  decide +kernel

/-- Each of the five tiers has a member: canonical 厂 *chǎng* (Table 3), 不 *bù* deviating on
meaning alone, bound and fixed 霸 *bà*, schematic 性 *xìng*, and the toneless 边 *-bian* and
个 *-ge* meeting no criterion. -/
theorem mandarin_tiers :
    violations? Wordlist.chang = some 0 ∧ violations? Wordlist.bu_2 = some 1 ∧
      violations? Wordlist.ba_2 = some 2 ∧ violations? Wordlist.xing_4 = some 3 ∧
      violations? Wordlist.bian = some 4 ∧ violations? Wordlist.ge_2 = some 4 := by
  decide

end Qin2025
