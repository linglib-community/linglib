module

public import Linglib.Data.Examples.KalinBjorkmanEtAl2026
public import Studies.ZwickyPullum1983
public import Linglib.Data.Examples.Readers

/-!
# Kalin et al. (2026): The Morphology/Syntax Interface

This file formalizes Kalin, Bjorkman et al.'s map of the morphology/syntax interface. Section 2 sets
out the dimensions along which theories vary: whether the morphology is a component separate from
the syntax, lexicalism; the timing of the two computations, an architecture that is parallel or
pre-syntactic exactly in the lexicalist theories and syntactic or post-syntactic in the
non-lexicalist ones, (4); whether complex forms arise from pieces or from processes, which
implicates lexicalism; and whether exponents are independent of the features they realize,
realizational, or built up with them, incremental. Table 2 places seven theories in the space of
lexicalism, mapping and exponence, and its two empty cells are exactly the non-lexicalist
process-based ones (`unattested_iff`), the four representative theories' architectures agreeing with
their lexicalism (`architecture_lexicalism`). Section 3 separates the morphosyntactic word,
diagnosed by cohesiveness, fixed order, selectivity and domainhood, from the phonological word, and
crosses the two kinds of boundness into Table 3's cells (`WordhoodProfile.classify`, `rows_cells`);
Zwicky and Pullum's diagnostics place the English plural affix in the canonical-affix cell and the
auxiliary clitic in the simple-clitic cell (`plural_s_canonicalAffix`). Section 4 distinguishes
seven form-meaning mappings and Table 4 records how each representative theory treats each; the
theories that treat some non-one-to-one mapping as genuine are exactly the realizational ones
(`handlesNatively_iff_realizational`), the purely syntactic Morphology as Syntax reanalyses every
one (`mas_reanalyses`), and no theory treats morphological gaps natively (`no_theory_handles_gaps`).

## Implementation notes

* Table 4 is the Element's own classification of the theories, carried as data; the theorems
  over it are the Element's readings of the table, and the cross-table theorem relates it to
  Table 2.
* The p-boundness of an element is not derived; the wordhood rows carry both boundnesses and
  the cell, and only the morphosyntactic side of the English affix and clitic is read off
  Zwicky and Pullum's profiles.

## References

* [kalin-bjorkman-etal-2026]
* [zwicky-pullum-1983]
* [stump-2001]
* [halle-marantz-1993]
-/

@[expose] public section

namespace KalinBjorkmanEtAl2026

open Morphology.Diagnostics

/-! ### The dimensions of the interface (Section 2.1) -/

/-- Whether the morphology is a component separate from the syntax, Section 2.1.1. -/
inductive Lexicalism
  | lexicalist
  | nonLexicalist
  deriving DecidableEq, Repr, Fintype

/-- The timing of morphology and syntax, (4). -/
inductive Architecture
  | syntactic
  | parallel
  | preSyntactic
  | postSyntactic
  deriving DecidableEq, Repr, Fintype

/-- An architecture's lexicalism, Section 2.1.2: the parallel and pre-syntactic architectures
are inherently lexicalist, the syntactic and post-syntactic ones inherently not. -/
def Architecture.lexicalism : Architecture → Lexicalism
  | .parallel | .preSyntactic => .lexicalist
  | .syntactic | .postSyntactic => .nonLexicalist

/-- Whether complex forms arise from the concatenation of stored pieces or from processes
applied to a stem, Section 2.1.3. -/
inductive Exponence
  | pieceBased
  | processBased
  deriving DecidableEq, Repr, Fintype

/-- Whether exponents realize features given in advance or are built up with them, Section
2.1.4. -/
inductive Mapping
  | realizational
  | incremental
  deriving DecidableEq, Repr, Fintype

/-- A cell of Table 2. -/
structure Cell where
  lexicalism : Lexicalism
  mapping : Mapping
  exponence : Exponence
  deriving DecidableEq, Repr, Fintype

/-- The seven theories Table 2 places. -/
inductive Theory
  | harmonicSerialismMorphology
  | distributedMorphology
  | nanosyntax
  | paradigmFunctionMorphology
  | minimalistMorphology
  | morphologyAsSyntax
  | articulatedMorphology
  deriving DecidableEq, Repr, Fintype

/-- Table 2. -/
def Theory.cell : Theory → Cell
  | .harmonicSerialismMorphology => ⟨.lexicalist, .realizational, .pieceBased⟩
  | .distributedMorphology | .nanosyntax => ⟨.nonLexicalist, .realizational, .pieceBased⟩
  | .paradigmFunctionMorphology => ⟨.lexicalist, .realizational, .processBased⟩
  | .minimalistMorphology => ⟨.lexicalist, .incremental, .pieceBased⟩
  | .morphologyAsSyntax => ⟨.nonLexicalist, .incremental, .pieceBased⟩
  | .articulatedMorphology => ⟨.lexicalist, .incremental, .processBased⟩

/-- Table 2's empty cells are exactly the non-lexicalist process-based ones, Section 2.4: a
process-based morphology computes unlike the syntax, Section 2.1.3. -/
theorem unattested_iff (c : Cell) :
    (∀ t : Theory, t.cell ≠ c) ↔ c.lexicalism = .nonLexicalist ∧ c.exponence = .processBased := by
  revert c; decide

theorem dm_nanosyntax_cell :
    Theory.distributedMorphology.cell = Theory.nanosyntax.cell := rfl

/-- The four theories Sections 2.2 and 2.3 present in detail and Table 4 compares. -/
inductive Representative
  | pfm
  | mas
  | nanosyntax
  | dm
  deriving DecidableEq, Repr, Fintype

/-- The theory a column of Table 4 names. -/
def Representative.theory : Representative → Theory
  | .pfm => .paradigmFunctionMorphology
  | .mas => .morphologyAsSyntax
  | .nanosyntax => .nanosyntax
  | .dm => .distributedMorphology

/-- The architectures of Sections 2.2 and 2.3: Paradigm Function Morphology is parallel, Morphology
as Syntax syntactic, Distributed Morphology and Nanosyntax post-syntactic. -/
def Representative.architecture : Representative → Architecture
  | .pfm => .parallel
  | .mas => .syntactic
  | .nanosyntax | .dm => .postSyntactic

/-- Each representative theory's architecture has the lexicalism of its Table 2 cell. -/
theorem architecture_lexicalism (r : Representative) :
    r.architecture.lexicalism = r.theory.cell.lexicalism := by
  cases r <;> rfl

/-! ### Wordhood (Section 3.2) -/

/-- Morphosyntactic boundness, Section 3.2.1: necessarily internal to a morphosyntactic word. -/
inductive MSBoundness
  | free
  | bound
  deriving DecidableEq, Repr, Fintype

/-- Phonological boundness, Section 3.2.2: necessarily internal to a phonological word. -/
inductive PBoundness
  | free
  | bound
  deriving DecidableEq, Repr, Fintype

/-- An element's two boundnesses. -/
structure WordhoodProfile where
  ms : MSBoundness
  p : PBoundness
  deriving DecidableEq, Repr, Fintype

/-- The cells of Table 3. -/
inductive WordhoodClass
  | canonicalWord
  | simpleClitic
  | nonCoheringAffix
  | canonicalAffix
  deriving DecidableEq, Repr, Fintype

/-- Table 3: crossing the two boundnesses. -/
def WordhoodProfile.classify : WordhoodProfile → WordhoodClass
  | ⟨.free, .free⟩ => .canonicalWord
  | ⟨.free, .bound⟩ => .simpleClitic
  | ⟨.bound, .free⟩ => .nonCoheringAffix
  | ⟨.bound, .bound⟩ => .canonicalAffix

/-- The boundnesses of a cell. -/
def WordhoodClass.profile : WordhoodClass → WordhoodProfile
  | .canonicalWord => ⟨.free, .free⟩
  | .simpleClitic => ⟨.free, .bound⟩
  | .nonCoheringAffix => ⟨.bound, .free⟩
  | .canonicalAffix => ⟨.bound, .bound⟩

/-- Table 3 is a bijection between profiles and cells. -/
def classifyEquiv : WordhoodProfile ≃ WordhoodClass where
  toFun := WordhoodProfile.classify
  invFun := WordhoodClass.profile
  left_inv := by decide
  right_inv := by decide

/-- A morphosyntactic status of [zwicky-pullum-1983]'s diagnostics is a boundness, Section
3.2.3: a clitic is a morphosyntactically free element, an affix a bound one. -/
def msBoundness : MorphStatus → MSBoundness
  | .freeWord | .simpleClitic | .specialClitic => .free
  | .inflAffix | .derivAffix => .bound

theorem msBoundness_eq_bound_iff (s : MorphStatus) : msBoundness s = .bound ↔ s.IsAffix := by
  cases s <;> simp [msBoundness, MorphStatus.IsAffix]

theorem plural_s_canonicalAffix :
    (WordhoodProfile.mk (msBoundness ZwickyPullum1983.affixPluralS.classify) .bound).classify =
        .canonicalAffix ∧
      (WordhoodProfile.mk (msBoundness ZwickyPullum1983.cliticS.classify) .bound).classify =
        .simpleClitic := by
  decide

/-- A row of Table 3: the two boundnesses and the cell. -/
structure WordhoodRow where
  profile : WordhoodProfile
  cell : WordhoodClass
  deriving DecidableEq

def msOf : String → Option MSBoundness
  | "free" => some .free
  | "bound" => some .bound
  | _ => none

def pOf : String → Option PBoundness
  | "free" => some .free
  | "bound" => some .bound
  | _ => none

def cellOf : String → Option WordhoodClass
  | "canonicalWord" => some .canonicalWord
  | "simpleClitic" => some .simpleClitic
  | "nonCoheringAffix" => some .nonCoheringAffix
  | "canonicalAffix" => some .canonicalAffix
  | _ => none

/-- A row from the paper's features. -/
def WordhoodRow.ofDatum (e : Datum) : Option WordhoodRow := do
  let ms ← (e.feature? "ms").bind msOf
  let p ← (e.feature? "p").bind pOf
  let c ← (e.feature? "cell").bind cellOf
  some ⟨⟨ms, p⟩, c⟩

/-- The Element's printed examples of three of the four cells: *cat*, plural *-s* and possessive
*-s*; the fourth, the non-cohering affixes, it describes in prose only. -/
def wordhoodRows : List WordhoodRow := Examples.all.filterMap WordhoodRow.ofDatum

theorem rows_cells : ∀ r ∈ wordhoodRows, r.profile.classify = r.cell := by decide

/-! ### Form-meaning mappings (Section 4) -/

/-- The seven descriptive form-meaning mappings of Section 4: abundance on the form side,
allomorphy and multiple exponence; on the meaning side, syncretism and portmanteaux; and
absence on either, gaps and empty morphs. -/
inductive MappingType
  | oneToOne
  | allomorphy
  | multipleExponence
  | syncretism
  | portmanteau
  | morphologicalGap
  | emptyMorph
  deriving DecidableEq, Repr, Fintype

/-- How a theory treats a mapping in Table 4: as a genuine non-one-to-one mapping by its basic
mechanisms, by reanalysis as another mapping, or by an extra mechanism. -/
inductive Coverage
  | yes
  | no
  | extra
  deriving DecidableEq, Repr, Fintype

/-- Table 4, a list where the subcases of a mapping receive different verdicts. -/
def table4 : MappingType → Representative → List Coverage
  | .oneToOne, _ => [.yes]
  | .allomorphy, .dm => [.yes]
  | .allomorphy, _ => [.no]
  | .multipleExponence, .pfm => [.yes]
  | .multipleExponence, .dm => [.no, .extra]
  | .multipleExponence, _ => [.no]
  | .syncretism, .pfm | .syncretism, .nanosyntax => [.yes, .extra]
  | .syncretism, .dm => [.yes]
  | .syncretism, .mas => [.no]
  | .portmanteau, .pfm => [.yes, .extra]
  | .portmanteau, .nanosyntax => [.yes]
  | .portmanteau, .dm => [.yes, .no, .extra]
  | .portmanteau, .mas => [.no]
  | .morphologicalGap, _ => [.no]
  | .emptyMorph, .pfm => [.yes, .no]
  | .emptyMorph, .dm => [.no, .extra]
  | .emptyMorph, _ => [.no]

/-- A theory treats a mapping natively when some subcase is a genuine mapping for it. -/
def HandlesNatively (m : MappingType) (r : Representative) : Prop := .yes ∈ table4 m r

instance (m : MappingType) (r : Representative) : Decidable (HandlesNatively m r) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- Morphology as Syntax denies every non-one-to-one mapping, reanalysing each, Section 4.6. -/
theorem mas_reanalyses (m : MappingType) (h : m ≠ .oneToOne) : table4 m .mas = [.no] := by
  cases m <;> first | exact absurd rfl h | rfl

theorem no_theory_handles_gaps (r : Representative) : table4 .morphologicalGap r = [.no] := by
  cases r <;> rfl

/-- The theories treating some non-one-to-one mapping as genuine are exactly the realizational ones
of Table 2 (Section 4.6). -/
theorem handlesNatively_iff_realizational (r : Representative) :
    (∃ m, m ≠ .oneToOne ∧ HandlesNatively m r) ↔ r.theory.cell.mapping = .realizational := by
  revert r; decide

theorem allomorphy_multipleExponence (r : Representative) :
    (HandlesNatively .allomorphy r ↔ r = .dm) ∧
      (HandlesNatively .multipleExponence r ↔ r = .pfm) := by
  revert r; decide

end KalinBjorkmanEtAl2026
