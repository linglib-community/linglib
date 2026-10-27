module

public import Studies.Ferreira2023
public import Linglib.Semantics.Exhaustification.Disjunctive
public import Linglib.Data.Examples.AghaJeretic2026

/-!
# Agha and Jeretič (2026): Modal force and its realization across languages

This file formalizes the tests and typologies of [agha-jeretic-2026]'s survey of modal force.
Weak necessity is weaker than strong necessity: a strong necessity conjoined with the denial of
another over one domain is contradictory and the conjunction of two is trivial, while *should φ
but you don't have to* is consistent and *should φ, and in fact you must* is informative ((6),
(8), (11), (12)); the decided paradigm of [ferreira-2023] derives this from the force scale, and
the chapter's rows exhibit it across languages. Of the three analyses the chapter surveys,
domain restriction ([von-fintel-iatridou-2008]), comparison ([rubinstein-2014]) and plural
predication ([agha-jeretic-2022]), the first neg-raises only over a decided domain.
Polarity-sensitive variable-force modals are possibility modals whose necessity readings arise
from what they project ([deal-2011], [jeretic-2021b], [newkirk-2022a]): the projections of Nez
Perce *o'qa*, Siona *ba'iji*, Swedish *får* and Kinande *anga* license the readings of the
chapter's table in each environment, and exhaustifying a possibility modal over its subdomain
alternatives yields necessity ([bar-lev-fox-2020]). The scope of the necessity modals under
negation and the determiner–modal generalization for infinitival relatives
([hackl-nissenbaum-1999]) are stated over the rows.

## Main definitions

* `Projection`, `Available`: what a possibility modal projects, and the readings a projection
  licenses in an environment.

## Implementation notes

* `Available` transcribes the chapter's reasoning about each cell of its table; only the
  exhaustification step is derived. *anga*'s `prunable` bit is idle, since its secondary
  ordering already yields weak necessity; why *anga* cannot prune *paswa* as *får* prunes
  *behöva* is the question the chapter leaves open.
* On *must* under higher negation the chapter and the rows of [rubinstein-2014] agree: both
  reject the reading with the negation inside the modal's scope.

## TODO

* The discourse-sensitive variable-force modals, the overt exhaustifiers, collapse variable
  force and the covert modals of the final section have no formal counterpart.

## References

* [agha-jeretic-2026]
* [agha-jeretic-2022]
* [ferreira-2023]
* [von-fintel-iatridou-2008]
* [rubinstein-2014]
* [horn-2001]
* [deal-2011]
* [jeretic-2021a]
* [jeretic-2021b]
* [newkirk-2022a]
* [bar-lev-fox-2020]
* [hackl-nissenbaum-1999]
* [weingartz-hohaus-2024]
-/

@[expose] public section

namespace AghaJeretic2026

open Modality Modality.Directive Exhaustification
open Ferreira2023 (Conjunct Pattern)

variable {W : Type*}

/-! ### Weak and strong necessity (§2.1) -/

/-- Strong necessity conjoined with the denial of strong necessity over one domain is contradictory,
and weak necessity so conjoined is consistent ((6), (8)). -/
theorem contradiction_tests :
    Pattern.Contradictory ⟨⟨.necessity, false, false⟩, ⟨.necessity, true, false⟩⟩ ∧
      Pattern.Consistent ⟨⟨.weakNecessity, false, false⟩, ⟨.necessity, true, false⟩⟩ := by
  decide

/-- A strong necessity after a strong necessity is trivial, and after a weak necessity
informative, (11) and (12). -/
theorem triviality_tests :
    Conjunct.Entails ⟨.necessity, false, false⟩ ⟨.necessity, false, false⟩ ∧
      ¬ Conjunct.Entails ⟨.weakNecessity, false, false⟩ ⟨.necessity, false, false⟩ := by
  decide

/-- The force a row names. -/
def forceTable : List (String × ModalForce) :=
  [("strong", .necessity), ("weak", .weakNecessity)]

theorem tests_covered :
    ∀ e ∈ Examples.all, (e.feature? "test").isSome →
      ((e.feature? "first").isSome ∧ (e.feature? "second").isSome) ∨
        (e.feature? "force").isSome := by
  decide

/-- In the chapter's English tests, `□₁ φ ∧ ¬□₂ φ` is contradictory and `□₁ φ ∧ □₂ φ` trivial
exactly when the first force entails the second. -/
theorem tests_predicted :
    ∀ e ∈ Examples.all, ∀ f₁ ∈ e.parse? "first" forceTable, ∀ f₂ ∈ e.parse? "second" forceTable,
      (e.feature? "test" = some "contradiction" →
        (e.judgment = .unacceptable ↔
          Pattern.Contradictory ⟨⟨f₁, false, false⟩, ⟨f₂, true, false⟩⟩)) ∧
      (e.feature? "test" = some "triviality" →
        (e.judgment = .unacceptable ↔
          Conjunct.Entails ⟨f₁, false, false⟩ ⟨f₂, false, false⟩)) := by
  decide

/-- Across languages, a necessity modal survives the denial of strong necessity exactly when its
force is weak, (15)–(17), (26) and (28). -/
theorem crosslinguistic_tests :
    ∀ e ∈ Examples.all, e.feature? "test" = some "contradiction" →
      ∀ φ ∈ e.parse? "force" forceTable,
        (e.judgment = .acceptable ↔
          Pattern.Consistent ⟨⟨φ, false, false⟩, ⟨.necessity, true, false⟩⟩) := by
  decide

/-- Domain-restriction weak necessity neg-raises for every prejacent iff its nested best-world
domain has at most one world ([horn-2001], §2.5). -/
theorem vfiWeak_negRaises_iff (f g g' : Background W) (w : W) :
    (∀ p : W → Prop, ¬ weakNecessity f g g' p w → weakNecessity f g g' (fun w' ↦ ¬ p w') w) ↔
      ((premisePreorder (g' w)).minimals (bestWorlds f g w)).Subsingleton :=
  ModalLogic.box_not_of_not_box_at_iff
    (R := .ofSuccessors fun _ ↦ (premisePreorder (g' w)).minimals (bestWorlds f g w)) (w := w)

/-! ### Scope under negation ((18)–(20)) -/

/-- A weak necessity modal never takes scope below negation. -/
theorem weak_never_narrow :
    ∀ e ∈ Examples.all, e.feature? "force" = some "weak" → (e.feature? "negation").isSome →
      e.readings.lookup "wide" = some .acceptable ∧
        e.readings.lookup "narrow" = some .unacceptable := by
  decide

/-- *Must* takes scope below negation exactly when the negation is in a higher clause. -/
theorem must_narrow_iff_higher :
    ∀ e ∈ Examples.all, e.feature? "modal" = some "must" →
      (e.readings.lookup "narrow" = some .acceptable ↔ e.feature? "negation" = some "higher") := by
  decide

/-- *Have to* takes scope below negation wherever the negation is. -/
theorem haveTo_always_narrow :
    ∀ e ∈ Examples.all, e.feature? "modal" = some "have to" →
      e.readings.lookup "narrow" = some .acceptable ∧
        e.readings.lookup "wide" = some .unacceptable := by
  decide

/-! ### Polarity-sensitive variable force (§3) -/

/-- The environments the typology distinguishes. -/
inductive Environment
  /-- An unembedded clause. -/
  | unembedded
  /-- Under a clausemate negation. -/
  | clausemateNegation
  /-- Another downward-entailing context. -/
  | otherDE
  deriving DecidableEq, Repr

/-- What a possibility modal projects ([jeretic-2021a], [jeretic-2021b], [newkirk-2022a]). -/
structure Projection where
  /-- Subdomain alternatives. -/
  subdomain : Bool
  /-- A strong-necessity scalemate. -/
  scalemate : Bool
  /-- The scalemate can be pruned. -/
  prunable : Bool
  /-- The domain is restricted by a secondary ordering source. -/
  secondaryOrdering : Bool
  deriving DecidableEq, Repr

/-- The readings a projection licenses in an environment. Unembedded, obligatory
exhaustification of subdomain alternatives removes the possibility reading unless a scalemate
supplies it, and strengthens to strong or weak necessity according to the domain; under
clausemate negation there is no clause boundary for the exhaustifier, and the necessity reading
is no special case of possibility; in other downward-entailing contexts exhaustification is
optional. -/
def Available (π : Projection) : Environment → ModalForce → Prop
  | .unembedded, .possibility => ¬ π.subdomain ∨ π.scalemate
  | .unembedded, .necessity =>
      (¬ π.subdomain ∧ ¬ π.scalemate) ∨
        (π.subdomain ∧ (¬ π.scalemate ∨ π.prunable) ∧ ¬ π.secondaryOrdering)
  | .unembedded, .weakNecessity => π.subdomain ∧ π.secondaryOrdering
  | .clausemateNegation, r => r = .possibility
  | .otherDE, .possibility => True
  | .otherDE, .necessity => π.subdomain ∧ ¬ π.secondaryOrdering
  | .otherDE, .weakNecessity => π.subdomain ∧ π.secondaryOrdering

instance (π : Projection) : ∀ env r, Decidable (Available π env r)
  | .unembedded, .possibility => inferInstanceAs (Decidable (_ ∨ _))
  | .unembedded, .necessity => inferInstanceAs (Decidable (_ ∨ _))
  | .unembedded, .weakNecessity => inferInstanceAs (Decidable (_ ∧ _))
  | .clausemateNegation, _ => inferInstanceAs (Decidable (_ = _))
  | .otherDE, .possibility => inferInstanceAs (Decidable True)
  | .otherDE, .necessity => inferInstanceAs (Decidable (_ ∧ _))
  | .otherDE, .weakNecessity => inferInstanceAs (Decidable (_ ∧ _))

/-- Nez Perce *o'qa* projects nothing ([deal-2011]). -/
def oqa : Projection := ⟨false, false, false, false⟩

/-- Siona *ba'iji* projects subdomain alternatives and has no scalemate. -/
def baiji : Projection := ⟨true, false, false, false⟩

/-- Swedish *får* projects subdomain alternatives and a prunable scalemate, *behöva*. -/
def får : Projection := ⟨true, true, true, false⟩

/-- Kinande *anga* projects subdomain alternatives, has the scalemate *paswa*, and quantifies
over a doubly restricted domain. -/
def anga : Projection := ⟨true, true, false, true⟩

/-- The projection a row concerns. -/
def projection? (e : Datum) : Option Projection :=
  e.parse? "modal" [("o'qa", oqa), ("ba'iji", baiji), ("får", får), ("anga", anga)]

/-- The environment a row concerns. -/
def environment? (e : Datum) : Option Environment :=
  e.parse? "environment" [("unembedded", Environment.unembedded),
    ("clausemate negation", .clausemateNegation), ("other DE", .otherDE)]

/-- The key under which a row records a force's reading. -/
def forceKey : ModalForce → String
  | .possibility => "possibility"
  | .necessity => "necessity"
  | .weakNecessity => "weak necessity"

/-- The projections license exactly the readings the chapter's table records. -/
theorem projection_matches_table :
    ∀ e ∈ Examples.all, e.feature? "table" = some "true" →
      ∀ π ∈ projection? e, ∀ env ∈ environment? e, ∀ r,
        (e.readings.lookup (forceKey r) = some .acceptable ↔ Available π env r) := by
  decide

/-- Every reading the chapter's examples record is licensed, and every reading they exclude is
not. -/
theorem readings_licensed :
    ∀ e ∈ Examples.all, ∀ π ∈ projection? e, ∀ env ∈ environment? e, ∀ r,
      (e.readings.lookup (forceKey r) = some .acceptable → Available π env r) ∧
        (e.readings.lookup (forceKey r) = some .unacceptable → ¬ Available π env r) := by
  decide

/-! ### Exhaustification of subdomain alternatives (§3.2) -/

/-- Over a nonempty domain, exhaustifying the possibility modal against its subdomain alternatives
yields necessity (50). -/
theorem exh_subdomain {ι : Type*} [DecidableEq ι] (M : Finset ι) (hM : M.Nonempty) :
    exhIEII (supClosure ((fun i ↦ {s : ι → Bool | s i = true}) '' M))
        (⋃ i ∈ M, {s : ι → Bool | s i = true}) =
      ⋂ i ∈ M, {s : ι → Bool | s i = true} :=
  exhIEII_supClosure (fun i _ ↦ ⟨fun j ↦ decide (j = i), fun j _ ↦ by simp⟩) hM
    ⟨fun _ ↦ true, fun _ _ ↦ rfl⟩

/-! ### Covert modality (§4) -/

/-- In infinitival relatives a strong determiner forces the *should* reading and excludes the
*could* reading, where a weak determiner allows both, (90)–(92). -/
theorem strong_determiner_should :
    ∀ e ∈ Examples.all, e.feature? "construction" = some "infinitival relative" →
      e.readings.lookup "should" = some .acceptable ∧
        (e.readings.lookup "could" = some .acceptable ↔ e.feature? "determiner" = some "weak") := by
  decide

end AghaJeretic2026
