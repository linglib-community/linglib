module

public import Linglib.Phonology.Prosody.Word
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Phonology.Prosody.Match

/-!
# Bennett 2018: recursive prosodic words in Kaqchikel

This file formalizes Bennett's argument that the prosodic word recurses in Kaqchikel.
Prefixes fall into two prosodic classes: low-attaching prefixes are parsed into their stem's
prosodic word, `[ω Pref Stem]`, and high-attaching prefixes outside it, `[ω Pref [ω Stem]]`.
Two diagnostics converge on the split — an onsetless syllable at the left edge of an ω
receives epenthetic [ʔ], so a vowel-initial stem keeps its glottal stop after a high prefix
but loses it after a low one, and the OCP that fuses adjacent identical consonants is inert
across an ω boundary, so degemination applies across a low-prefix juncture but not a high
one. Stacked high prefixes each receive their own glottal stop, which a non-recursive
prosodic hierarchy could only reproduce by positing one new prosodic category per prefix.
The recursion follows from a lexical subcategorization frame on the high prefixes, ranked
above the constraint that every prosodic word correspond to a morphological word.

## Main definitions

* `flat`, `nested`: the two parses of a prefix sequence over a stem.
* `omegaInitial`, `OmegaSeparates`: the structural side of the two diagnostics — the
  ω-initial leaves, and whether an ω boundary separates two leaves.
* `word`, `subCat`: the span of the morphological word, which `Match (X⁰, ω)` and
  `Match (ω, X⁰)` read as `Prosody.syntaxProsodyMatch` and `Prosody.prosodySyntaxMatch`, and the
  subcategorization frame, aligned with each prefix's index in the frontier.

## References

* [bennett-2018]
* [selkirk-2011]: the Match constraints.
* [inkelas-1990]: prosodic subcategorization.
* [nespor-vogel-1986]: the Strict Layer Hypothesis and the Clitic Group.
-/

@[expose] public section

namespace Bennett2018

open Prosody OptimalityTheory

/-! ### Parses -/

/-- The flat parse `[ω Pref₁ … Prefₙ Stem]`, the structure of low-attaching prefixes (4a). -/
def flat (prefs : List Constituent) (stem : Constituent) : Tree :=
  .om ((prefs ++ [stem]).map RoseTree.leaf)

/-- The recursive parse `[ω Pref₁ [ω … [ω Prefₙ [ω Stem]]]]`, one ω per high-attaching
prefix ((19a), (23)). -/
def nested : List Constituent → Constituent → Tree
  | [], stem => .om [.leaf stem]
  | p :: ps, stem => .om [.leaf p, nested ps stem]

/-- A light prefix syllable. -/
def pref : Constituent := .syl 1

/-- A heavy stem syllable. -/
def stem : Constituent := .syl 2

/-- Each high-attaching prefix as an independent ω under a higher category (25a), the
carrier's φ standing in for a Clitic Group. -/
def phrasal : Tree := .ph [.om [.leaf pref], .om [.leaf stem]]

/-! ### Diagnostics -/

/-- The leftmost leaf of a tree. -/
def leftmost (t : Tree) : Constituent := t.leafList.head t.leafList_ne_nil

/-- The ω-initial leaves, one per ω node: the left edge of an ω is where an onsetless
syllable receives epenthetic [ʔ], the ω being the domain of syllabification. -/
def omegaInitial (t : Tree) : List Constituent :=
  (t.subtrees.filter (·.value.level = .om)).map leftmost

/-- Some ω dominates the leaf `b` but not the leaf `a`: an ω boundary between them, across
which `OCP(X)ω` (18) is inert. -/
def OmegaSeparates (a b : Constituent) (t : Tree) : Prop :=
  ∃ s ∈ t.subtrees, s.value.level = .om ∧ b ∈ s.leafList ∧ a ∉ s.leafList

instance (a b : Constituent) (t : Tree) : Decidable (OmegaSeparates a b t) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- In the recursive parse, `n` high prefixes over a vowel-initial stem give `n + 1` loci of
[ʔ]-insertion ((21)–(23)). -/
theorem omegaInitial_nested {ps : List Constituent} {s : Constituent}
    (hps : ∀ p ∈ ps, p.level ≠ .om) (hs : s.level ≠ .om) :
    omegaInitial (nested ps s) = ps ++ [s] := by
  induction ps with
  | nil => simp [omegaInitial, nested, leftmost, hs]
  | cons p ps ih =>
    have ih := ih fun q hq ↦ hps q (List.mem_cons_of_mem p hq)
    simp only [omegaInitial] at ih
    simp [omegaInitial, nested, leftmost, hps p (List.mem_cons_self ..), ih]

/-- In the flat parse only the first prefix is ω-initial: one locus of [ʔ]-insertion. -/
theorem omegaInitial_flat {p : Constituent} {ps : List Constituent} {s : Constituent}
    (hp : p.level ≠ .om) (hps : ∀ q ∈ ps, q.level ≠ .om) (hs : s.level ≠ .om) :
    omegaInitial (flat (p :: ps) s) = [p] := by
  simpa [omegaInitial, flat, leftmost, hp, hs, List.filter_flatMap,
    List.flatMap_eq_nil_iff] using hps

-- (22)–(23): three high prefixes and a vowel-initial root, four glottal stops.
example : omegaInitial (nested [pref, pref, pref] stem) = [pref, pref, pref, stem] := by decide

-- (15) vs (16)–(17): no ω boundary separates a low prefix from its stem, so `OCP(X)ω`
-- degeminates across the juncture; an ω boundary separates a high prefix from its stem.
example : ¬ OmegaSeparates pref stem (flat [pref] stem) := by decide
example : OmegaSeparates pref stem (nested [pref] stem) := by decide

/-! ### Constraints and the ranking -/

/-- The prefix and the stem form one morphological word over the two syllables, whose span
Match (X⁰, ω) (13), undominated in Kaqchikel, and Match (ω, X⁰) read. -/
abbrev word : List (ℕ × ℕ) := [(0, 2)]

/-- The subcategorization frame `[ω p [ω ]]` (30): an ω whose daughters are a syllable and an ω. -/
def IsFrame (t : Tree) : Prop :=
  t.value.level = .om ∧ t.children.map (·.value.level) = [.syl, .om]

instance : DecidablePred IsFrame := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- `SubCat`: one violation per high-attaching prefix, at its index in the frontier, at which no
frame (30) begins. -/
def subCat (prefs : List ℕ) : Constraint Tree :=
  (Constraint.align fun (i : ℕ) (x : ℕ × ℕ) ↦ i = x.1).comap fun t ↦ (prefs, t.spans IsFrame)

/-- A high-attaching prefix is parsed recursively: under `SubCat ≫ Match (ω, X⁰)`, with
`Match (X⁰, ω)` undominated, the recursive parse is the unique optimum. -/
theorem high_prefix_recursive :
    (Tableau.ofList {nested [pref] stem, flat [pref] stem, phrasal}
      [syntaxProsodyMatch word .om, subCat [0], prosodySyntaxMatch .om word]).optimal =
        {nested [pref] stem} := by
  decide

-- Stacked high prefixes each realise their frame only in the recursive parse.
example : subCat [0, 1] (nested [pref, pref] stem) = 0 := by decide
example : subCat [0, 1] (flat [pref, pref] stem) = 2 := by decide

/-- A low-attaching prefix, carrying no frame, is parsed flat: `Match (ω, X⁰)` alone rules
out the extra ω. -/
theorem low_prefix_flat :
    (Tableau.ofList {nested [pref] stem, flat [pref] stem, phrasal}
      [syntaxProsodyMatch word .om, prosodySyntaxMatch .om word]).optimal =
        {flat [pref] stem} := by
  decide

-- The recursive optimum is a well-formed prosodic word: ω over ω is admitted by
-- Layeredness; only the violable `Match (ω, X⁰)` penalises it.
example : IsWord (nested [pref] stem) := by decide

end Bennett2018
