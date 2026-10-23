module

public import Studies.Corbett2000
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Grimm (2018): Grammatical Number and the Scale of Individuation

Grimm orders the individuation types of nominal descriptions on a scale, substances below granular
aggregates below collective aggregates below individuals (`IndividuationType`), and argues that a
language's grammatical number categories partition the scale by an order-preserving map (section
3.4). No category then spans two disconnected segments of the scale
(`ordConnected_fiber_of_monotone`), and this is all that order preservation asks: a classification
whose classes are contiguous is monotone for an order on its classes
(`exists_linearOrder_monotone_iff`). The impossible system of Table 21 fails under every ordering of
its classes (`bad_not_monotone`). The systems of Table 20 and section 4.1, Dagaare with a class per
type, the tripartite Welsh, Turkana, Maltese, and Miraña, binary English, and Yudja with number on
humans alone, are monotone classifications (`welsh_monotone` and its siblings). Markedness follows
the scale: the zero-coded value of a class is single reference for individuals and multiple
reference for aggregates, with no contrast at the bottom (`welsh_default_monotone` and its
siblings), and Dagaare's inverse marking is one coded value read in the two directions. Animacy
refines the picture (section 4.2): on the product of the scale with the animacy hierarchy, the
collective/singulative class ascends from below, the inverse of Smith-Stark's plural marking, and
the regions of Maltese, Welsh, and Turkana nest (`collective_regions_nest`).

## Implementation notes

The individuation types are primitive, as in the paper: equivalence classes of nominal
descriptions by individuation properties, which the paper ranks by perceptibility of minimal
units, spatial separation, consistency of shape, and interaction, and which section 4.3 extends
to function for artifacts. Grimm's dissertation derives the middle of the scale from the
strength of the connection relation under which aggregate nouns' referents cluster
(`Mereology.IsCluster`).
Each language's countability classes are an enumeration ordered by scale position, and the
classification of the four individuation types is the language's row of Table 20, 23, or 24.
Turkana and Maltese share Welsh's partition and differ in agreement and animacy reach, Yudja
shares English's and differs in restricting the contrast to humans; the classification does not
record these. The animacy tiers of Fig. 3, inanimates below Haspelmath's lower and higher
animates below humans, are ranks of the library's `AnimacyHierarchy`; the full animacy–individuation
lattice, an Aissen product, and the connected region constraint (28) over it are not
formalized.

## References

* [grimm-2018]
* [corbett-2000]
* [grimm-2012]
* [smith-stark-1974]
* [aissen-2003]
* [haspelmath-2013b]
-/

@[expose] public section

namespace Grimm2018

/-! ### The scale of individuation, section 3.2 -/

/-- The individuation types of (17) and (19) are equivalence classes of nominal descriptions by
their individuation properties, ordered from entities without perceptible minimal units to
independent individuals. -/
inductive IndividuationType where
  /-- Liquids and substances (*water*, *oil*) have no perceptible minimal units. -/
  | substance
  /-- Granular aggregates (*rice*, *sand*) have perceptible units, typically not separated from
  one another. -/
  | granularAggregate
  /-- Collective aggregates (*ants*, *cherries*) have perceptible units, separated from one
  another but connected, spatially near or functionally united. -/
  | collectiveAggregate
  /-- Individuals (*dog*) are independent of one another. -/
  | individualEntity
  deriving DecidableEq, Repr, Fintype

/-- Each type is numbered by its position on the scale. -/
def IndividuationType.toNat : IndividuationType → ℕ
  | .substance => 0
  | .granularAggregate => 1
  | .collectiveAggregate => 2
  | .individualEntity => 3

instance : LinearOrder IndividuationType := .lift' IndividuationType.toNat (by decide)

/-! ### The order-preservation thesis, section 3.4 -/

theorem ordConnected_fiber_of_monotone {α C : Type*} [Preorder α] [PartialOrder C] {f : α → C}
    (hf : Monotone f) (c : C) : (f ⁻¹' {c}).OrdConnected :=
  Set.ordConnected_singleton.preimage_mono hf

theorem exists_linearOrder_monotone_iff {α C : Type*} [LinearOrder α] {f : α → C}
    (hf : Function.Surjective f) :
    (∃ _ : LinearOrder C, Monotone f) ↔ ∀ c, (f ⁻¹' {c}).OrdConnected := by
  refine ⟨fun ⟨_, hm⟩ ↦ ordConnected_fiber_of_monotone hm, fun hc ↦ ?_⟩
  obtain ⟨s, hs⟩ := hf.hasRightInverse
  let _ : LinearOrder C := .lift' s hs.injective
  refine ⟨‹_›, fun i j hij ↦ not_lt.1 fun h ↦ ?_⟩
  have hne : f i ≠ f j := fun he ↦ (show s (f j) < s (f i) from h).ne (by rw [he])
  rcases le_or_gt j (s (f i)) with hj | hj
  · exact hne ((hc (f i)).out rfl (hs (f i)) ⟨hij, hj⟩).symm
  · exact hne ((hs (f i)).symm.trans ((hc (f j)).out (hs (f j)) rfl ⟨h.le, hj.le⟩))

/-! ### The number systems, Tables 20, 23, and 24 -/

/-- A tripartite system has a non-countable, a collective/unit, and a singular/plural class. -/
inductive TripartiteClass where
  | nonCountable
  | collectiveUnit
  | singularPlural
  deriving DecidableEq, Repr, Fintype

/-- Each class is numbered by its position on the scale. -/
def TripartiteClass.toNat : TripartiteClass → ℕ
  | .nonCountable => 0
  | .collectiveUnit => 1
  | .singularPlural => 2

instance : LinearOrder TripartiteClass := .lift' TripartiteClass.toNat (by decide)

/-- In Welsh (Table 20), substances are non-countable (*llefrith* 'milk'), granular and
collective aggregates take the singulative (*adar* ~ *aderyn* 'birds' ~ 'bird'), and individuals
take the plural (*cadair* ~ *cadeiriau* 'chair' ~ 'chairs'). -/
def welshClassify : IndividuationType → TripartiteClass
  | .substance => .nonCountable
  | .granularAggregate | .collectiveAggregate => .collectiveUnit
  | .individualEntity => .singularPlural

theorem welsh_monotone : Monotone welshClassify := by decide

/-- Turkana (section 2.2) partitions the scale as Welsh does; its collective class reaches
types of people. -/
abbrev turkanaClassify := welshClassify

/-- Maltese (section 2.3) partitions the scale as Welsh does; its collective agrees in the
singular and reaches barely beyond insects. -/
abbrev malteseClassify := welshClassify

/-- In Miraña (Table 23), granular aggregates join the substances as non-countable, collective
aggregates form the class whose bare form names a collection and whose class-marked form a
unit, and individuals inflect for plural. -/
def miranaClassify : IndividuationType → TripartiteClass
  | .substance | .granularAggregate => .nonCountable
  | .collectiveAggregate => .collectiveUnit
  | .individualEntity => .singularPlural

theorem mirana_monotone : Monotone miranaClassify := by decide

/-- Dagaare's classes (Table 20) are the non-countable class, the optionally singulative
(*-ruu*) non-countable class, the plural-default class with *-ri* coding the singular, and the
singular-default class with *-ri* coding the plural. -/
inductive DagaareClass where
  | nonCountable
  | singulativeNonCount
  | pluralDefault
  | singularDefault
  deriving DecidableEq, Repr, Fintype

/-- Each class is numbered by its position on the scale. -/
def DagaareClass.toNat : DagaareClass → ℕ
  | .nonCountable => 0
  | .singulativeNonCount => 1
  | .pluralDefault => 2
  | .singularDefault => 3

instance : LinearOrder DagaareClass := .lift' DagaareClass.toNat (by decide)

/-- Dagaare (Table 20) has a class for each individuation type. -/
def dagaareClassify : IndividuationType → DagaareClass
  | .substance => .nonCountable
  | .granularAggregate => .singulativeNonCount
  | .collectiveAggregate => .pluralDefault
  | .individualEntity => .singularDefault

theorem dagaare_monotone : Monotone dagaareClassify := by decide

/-- A binary system has a non-countable and a singular/plural class. -/
inductive BinaryClass where
  | nonCountable
  | singularPlural
  deriving DecidableEq, Repr, Fintype

/-- Each class is numbered by its position on the scale. -/
def BinaryClass.toNat : BinaryClass → ℕ
  | .nonCountable => 0
  | .singularPlural => 1

instance : LinearOrder BinaryClass := .lift' BinaryClass.toNat (by decide)

/-- In English (Table 20), substances and both kinds of aggregate (*rice*, *foliage*) are
non-countable, and individuals take the plural. -/
def englishClassify : IndividuationType → BinaryClass
  | .individualEntity => .singularPlural
  | _ => .nonCountable

theorem english_monotone : Monotone englishClassify := by decide

/-- Yudja (Table 24) cuts the scale where English does, with the optional plural *-i* on
individuals restricted to humans. -/
abbrev yudjaClassify := englishClassify

/-! ### The impossible system, Table 21

Granular aggregates and individuals share a singular/plural class while the collective
aggregates between them form a collective/singulative class, so the singular/plural class is
discontinuous on the scale. -/

/-- Table 21's bad system puts granular aggregates and individuals in one class. -/
def badClassify : IndividuationType → TripartiteClass
  | .substance => .nonCountable
  | .granularAggregate | .individualEntity => .singularPlural
  | .collectiveAggregate => .collectiveUnit

theorem bad_fiber_not_ordConnected :
    ¬ (badClassify ⁻¹' {TripartiteClass.singularPlural}).OrdConnected := by
  intro h
  have : badClassify .collectiveAggregate = .singularPlural :=
    h.out (x := .granularAggregate) rfl (y := .individualEntity) rfl ⟨by decide, by decide⟩
  exact absurd this (by decide)

/-- No ordering of the classes makes the bad system order-preserving, the paper's footnote 21
generalized from its two candidate orders to all. -/
theorem bad_not_monotone (po : PartialOrder TripartiteClass) :
    letI := po
    ¬ Monotone badClassify :=
  fun hf ↦ bad_fiber_not_ordConnected (@ordConnected_fiber_of_monotone _ _ _ po _ hf _)

/-! ### Coding and markedness, sections 3.4 and 4.4

Each class codes one value of its contrast and leaves the other zero. The prediction: the
zero-coded default of a class tracks its individuation, multiple reference for aggregate classes
and single reference for individual classes, with no contrast at the bottom. -/

/-- A countability class codes its number contrast in one of four patterns. -/
inductive ClassCoding where
  /-- The class has no number contrast. -/
  | noContrast
  /-- The aggregate is zero-coded and the unit, the singulative, is coded. -/
  | codedUnit
  /-- The plural is zero-coded and the singular is coded, Dagaare's inverse marking. -/
  | codedSingular
  /-- The singular is zero-coded and the plural is coded. -/
  | codedPlural
  deriving DecidableEq, Repr, Fintype

/-- The zero-coded default of a class is nothing, multiple referents, or a single referent. -/
inductive DefaultReference where
  | none
  | multiple
  | single
  deriving DecidableEq, Repr, Fintype

/-- Each default is numbered by its position on the scale. -/
def DefaultReference.toNat : DefaultReference → ℕ
  | .none => 0
  | .multiple => 1
  | .single => 2

instance : LinearOrder DefaultReference := .lift' DefaultReference.toNat (by decide)

/-- Each coding pattern leaves a zero-coded default. -/
def ClassCoding.default : ClassCoding → DefaultReference
  | .noContrast => .none
  | .codedUnit | .codedSingular => .multiple
  | .codedPlural => .single

/-- Welsh codes its classes (Table 20) with nothing, the singulative *-yn*, and the plural
*-od*. -/
def welshCoding : TripartiteClass → ClassCoding
  | .nonCountable => .noContrast
  | .collectiveUnit => .codedUnit
  | .singularPlural => .codedPlural

/-- Dagaare codes its classes (Table 20) with nothing, the optional singulative *-ruu*, the
singular *-ri*, and the plural *-ri*. -/
def dagaareCoding : DagaareClass → ClassCoding
  | .nonCountable => .noContrast
  | .singulativeNonCount => .codedUnit
  | .pluralDefault => .codedSingular
  | .singularDefault => .codedPlural

/-- English codes its classes (Table 20) with nothing and the plural *-s*. -/
def englishCoding : BinaryClass → ClassCoding
  | .nonCountable => .noContrast
  | .singularPlural => .codedPlural

theorem welsh_default_monotone :
    Monotone fun i ↦ (welshCoding (welshClassify i)).default := by
  decide

theorem dagaare_default_monotone :
    Monotone fun i ↦ (dagaareCoding (dagaareClassify i)).default := by
  decide

theorem english_default_monotone :
    Monotone fun i ↦ (englishCoding (englishClassify i)).default := by
  decide

theorem dagaare_inverse_marking :
    (dagaareCoding .pluralDefault).default = .multiple ∧
      (dagaareCoding .singularDefault).default = .single ∧
      dagaareCoding .pluralDefault ≠ dagaareCoding .singularDefault := by
  decide

/-! ### Countability and animacy, section 4.2

Plural marking descends the animacy hierarchy from the top, as Smith-Stark found; the
collective/singulative class ascends it from below, since the more animate an entity the more it
is construed as occurring singly. Welsh's collective class stops at small and middle-sized
animals, Turkana's reaches types of people, Maltese's barely passes insects (Fig. 4). -/

/-- Fig. 4 compares three tripartite languages. -/
inductive CollectiveLang where
  | maltese
  | welsh
  | turkana
  deriving DecidableEq, Repr, Fintype

/-- Each language's collective/singulative class reaches up to a position on the animacy
hierarchy (Fig. 4) and covers everything from inanimate aggregates up to it. The positions are
Corbett's, with the split of the animates into higher and lower that Grimm takes from
Haspelmath. -/
def collectiveCeiling : CollectiveLang → Corbett2000.AnimacyHierarchy
  | .maltese => .lowerAnimate
  | .welsh => .higherAnimate
  | .turkana => .human

theorem collective_regions_nest :
    collectiveCeiling .maltese ≤ collectiveCeiling .welsh ∧
      collectiveCeiling .welsh ≤ collectiveCeiling .turkana := by
  decide

end Grimm2018
