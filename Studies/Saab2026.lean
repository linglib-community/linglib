module

public import Linglib.Fragments.Romance.Spanish.Binominals
public import Linglib.Syntax.Number.Basic
public import Linglib.Syntax.Minimalist.Ellipsis
public import Linglib.Data.Examples.Saab2026
public import Mathlib.Tactic.DeriveFintype

/-!
# Saab (2026): NP-Ellipsis Patterns in Spanish Binominals

This file formalizes the paper's argument that pseudo-partitive and quantificational
binominals (*un grupo*, *un montón de estudiantes*) and qualitative binominals (*una mierda de
departamento*) have different underlying syntax. In the former the genitive coda is the nP
complement of Num, a primeval genitive in the sense of [pesetsky-2013], so an [E]-feature on
Num licenses NP-ellipsis of the coda under the usual identity condition of [merchant-2001],
and Num controls verbal agreement; in the latter the coda is the specifier of an equative
phrase relating it to an indexical empty noun, so no licensor can elide it and its gap is
resolved by context rather than by an antecedent. A structure is the nominal that is the
complement of Num together with the nominal in the specifier above it (`Structure`).
NP-ellipsis of a nominal is licensed exactly when it is that complement and has internal
structure (`Structure.Elidable`), and the verb agrees with the number of that complement. The
same principle covers the paper's structural ambiguity of quantity nouns: under the
descriptive reading the noun heads the projection, so it can be elided and the verb is
singular, and under the quantificational reading the coda heads it, so the coda can be elided
and the verb is plural (`elidable_first_iff_singular`). The rows are the paper's examples,
with the type of each first noun read from the Spanish fragment, and their ellipsis,
agreement and gap facts follow from the structure assigned to them (`ellipsis_matches`).

## Implementation notes

Identity between an antecedent and an ellipsis site is taken modulo case and number, as the paper
argues: case is assigned at PF or overwritten by D after identity is computed, and number sits on
the licensing head outside the ellipsis domain. The paper's three kinds of nominal gap are
distinguished by the recovery they need, a linguistic antecedent for ellipsis, a contextual
assignment for the indexical empty noun and none for a silent noun. The first two are anaphoric, and
their depth in the sense of [hankamer-sag-1976] is read from the Minimalist model of null sites
(`Minimalist.NullSite`): NP-ellipsis is the nP that [E] on Num silences, a surface anaphor, and the
indexical empty noun is a null pro-form at n, a deep one. The sub-extraction and argument-structure
diagnostics of the rows test for internal structure, and the context diagnostic for a deep anaphor.
Pesetsky's derivation of genitive marking and the equations at the entity and proposition types are
not formalized.

## References

* [saab-2026]
* [pesetsky-2013]
* [merchant-2001]
* [hankamer-sag-1976]
-/

@[expose] public section

namespace Saab2026

open Spanish.Binominals

/-! ### Structures -/

/-- The nominals of a binominal are the first noun, the genitive coda, and the indexical empty
noun of the equative structure. -/
inductive Nominal where
  | first
  | coda
  | index
  deriving DecidableEq, Repr, Fintype

/-- A structure records the nominal that is the complement of Num, the head of the extended
projection, and the nominal in the specifier above it. -/
structure Structure where
  head : Nominal
  spec : Option Nominal
  deriving DecidableEq, Repr, Fintype

/-- In the primeval-genitive structure of pseudo-partitive and quantificational binominals the
coda is the nP complement of Num and the quantity phrase sits in the specifier. -/
def quantificational : Structure := ⟨.coda, some .first⟩

/-- Under the descriptive reading of a quantity noun the noun heads the projection and the coda
is its complement. -/
def descriptive : Structure := ⟨.first, none⟩

/-- In the equative structure of qualitative binominals the complement of Num is the indexical
empty noun, which the equative head relates to the coda in its specifier. -/
def equative : Structure := ⟨.index, some .coda⟩

/-- The gap a structure leaves when its coda is missing, as a null site of the nominal spine.
With the indexical empty noun as the complement of Num the gap is that noun, a null pro-form at n
whose value the assignment function supplies; otherwise it is the nP that [E] on Num silences. -/
def Structure.site (s : Structure) : Minimalist.NullSite Minimalist.Ellipsis.nominalSpine :=
  if s.head = .index then .proform (.head .n)
  else .elided Minimalist.Ellipsis.nPEllipsis ⟨.head .N, by decide⟩

/-- The depth of the gap, read from the Minimalist model of null sites. -/
def Structure.depth (s : Structure) : Anaphor.Depth := Anaphor.DepthModel.depth s.site

theorem Structure.hasInternalStructure_depth_iff (s : Structure) :
    s.depth.HasInternalStructure ↔ s.site.Silences (.head .N) := by
  revert s; decide

/-- A nominal can be elided when it is the complement of Num, whose [E]-feature licenses the
ellipsis of its complement, and the gap has internal structure: the indexical empty noun is an
atomic index, so eliding it is vacuous. -/
def Structure.Elidable (s : Structure) (x : Nominal) : Prop :=
  s.head = x ∧ s.depth.HasInternalStructure

instance (s : Structure) (x : Nominal) : Decidable (s.Elidable x) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The number of a nominal, given the coda's. The first noun is singular, and the indexical
empty noun takes the coda's number through the equation. -/
def Nominal.number (c : Number) : Nominal → Number
  | .first => .singular
  | .coda | .index => c

/-- The verb agrees with the Num head, whose number is that of its complement. -/
def Structure.agreement (s : Structure) (c : Number) : Number := s.head.number c

theorem equative_not_elidable (x : Nominal) : ¬ equative.Elidable x := by
  cases x <;> decide

theorem quantificational_descriptive_elidable :
    quantificational.Elidable .coda ∧ ¬ quantificational.Elidable .first ∧
      descriptive.Elidable .first ∧ ¬ descriptive.Elidable .coda := by
  decide

/-! ### Readings -/

/-- The two readings of a quantity noun. -/
inductive Reading where
  | quantificational
  | descriptive
  deriving DecidableEq, Repr, Fintype

/-- The structure of a binominal of a given type under a reading. -/
def structureOf : BinominalType → Reading → Structure
  | .qualitative, _ => equative
  | _, .quantificational => quantificational
  | _, .descriptive => descriptive

theorem elidable_first_iff_singular (b : BinominalType) (r : Reading) (hb : b ≠ .qualitative) :
    (structureOf b r).Elidable .first ↔ (structureOf b r).agreement .plural = .singular := by
  cases b <;> cases r <;> decide

/-! ### The paper's examples -/

/-- A row's binominal type, from the fragment entry of its first noun. -/
def binominalType? (x : Datum) : Option BinominalType :=
  (x.feature? "noun").bind fun f ↦ (lookup f).map (·.binominalType)

def readings : List (String × Reading) :=
  [("quantificational", .quantificational), ("descriptive", .descriptive)]

/-- The structure the paper assigns to a row follows from its first noun's type and, for a
quantity noun, its reading, which is quantificational unless recorded otherwise. -/
def structure? (x : Datum) : Option Structure :=
  (binominalType? x).map fun b ↦
    structureOf b ((x.parse? "reading" readings).getD .quantificational)

def nominals : List (String × Nominal) := [("first", .first), ("coda", .coda)]

def numbers : List (String × Number) := [("singular", .singular), ("plural", .plural)]

/-- The ellipsis reading of a row is acceptable when the reading's judgment, or the row's if
none is recorded for the reading, is acceptable. -/
def EllipsisAcceptable (x : Datum) : Prop :=
  (x.readings.lookup "ellipsis").getD x.judgment = .acceptable

instance (x : Datum) : Decidable (EllipsisAcceptable x) := by
  unfold EllipsisAcceptable; infer_instance

theorem structure?_isSome : ∀ x ∈ Examples.all, (structure? x).isSome := by decide +kernel

theorem ellipsis_matches :
    ∀ x ∈ Examples.all, ∀ s, structure? x = some s → ∀ e, x.parse? "elided" nominals = some e →
      (EllipsisAcceptable x ↔ s.Elidable e) := by
  decide +kernel

theorem agreement_matches :
    ∀ x ∈ Examples.all, ∀ s, structure? x = some s → (x.feature? "agreement").isSome →
      x.parse? "agreement" numbers = (x.parse? "codaNumber" numbers).map s.agreement := by
  decide +kernel

theorem diagnostics_match :
    ∀ x ∈ Examples.all, ∀ s, structure? x = some s →
      (x.feature? "diagnostic" = some "subextraction" ∨
          x.feature? "diagnostic" = some "argumentStructure" →
        (x.judgment = .acceptable ↔ s.depth.HasInternalStructure)) ∧
      (x.feature? "diagnostic" = some "contextResolved" →
        (x.judgment = .acceptable ↔ s.depth = .deep)) := by
  decide +kernel

end Saab2026
