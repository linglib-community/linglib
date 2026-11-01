module

public import Linglib.Semantics.Homogeneity.Usable
public import Linglib.Semantics.Polarity.Basic
public import Linglib.Data.Examples.AghaJeretic2022
public import Mathlib.Order.Minimal
public import Linglib.Data.Examples.Readers

/-!
# Agha and Jeretič (2022): Weak Necessity Modals as Homogeneous Pluralities of Worlds

Weak necessity modals take obligatory apparent wide scope over negation: *you shouldn't go* cannot
be continued by *but you are allowed to go*, where *you don't have to go* can. Agha and Jeretič
propose that *should* is to *must* what *the* is to *all*: strong necessity quantifies universally
over the best worlds, while weak necessity predicates the prejacent of their plurality, which is
neither true nor false when some best worlds satisfy it and some do not. Weak necessity is derived
from strong necessity by an operator picking out the unique minimal set of a quantifier, which
possibility lacks.

## Implementation notes

`should D p` is Križ's plural predication with the best worlds `D w` as atoms. The grid reads each
example row as a cell (`Cell.ofDatum`): its polarity, its scenario, and the value judged, the
classical value the polarity fixes where all or no best worlds satisfy the prejacent, and the gap
or the recorded classical value in the mixed scenario. The proportional and degree-based rivals,
and the conditionals, generics and habituals of the closing section, are not formalized.

## References

* [agha-jeretic-2022]
* [kriz-2016]
* [kratzer-1981]
* [von-fintel-iatridou-2008]
* [vander-klok-hohaus-2020]
* [barwise-cooper-1981]
* [schlenker-2004a]
-/

@[expose] public section

namespace AghaJeretic2022

open SignType (supervaluation supervaluation_eq_one_iff supervaluation_eq_neg_one_iff
  supervaluation_eq_zero_iff supervaluation_not)
open Homogeneity

variable {W : Type*} (D : W → Finset W) (p : W → Prop) [DecidablePred p]

/-! ### Weak necessity as plural predication over worlds -/

/-- Weak necessity `should D p` predicates the prejacent of the plurality of best worlds `D w`. -/
def should : W → SignType := fun w ↦ supervaluation (D w) p

/-- Strong necessity `must D p` holds when the prejacent holds in every best world. -/
def must : W → SignType := fun w ↦ SignType.ofProp (∀ w' ∈ D w, p w')

theorem should_eq_one_iff (w : W) : should D p w = 1 ↔ ∀ w' ∈ D w, p w' :=
  supervaluation_eq_one_iff ..

theorem should_eq_neg_one_iff (w : W) :
    should D p w = -1 ↔ (D w).Nonempty ∧ ∀ w' ∈ D w, ¬ p w' :=
  supervaluation_eq_neg_one_iff ..

/-- The sentence has a gap when some best worlds satisfy the prejacent and some do not. -/
theorem should_eq_zero_iff (w : W) :
    should D p w = 0 ↔ (∃ w' ∈ D w, p w') ∧ ∃ w' ∈ D w, ¬ p w' :=
  supervaluation_eq_zero_iff ..

/-- Over a nonempty domain negating the prejacent negates the modal sentence, so the gap is
symmetric and negation is scopeless. -/
theorem should_not (w : W) (hne : (D w).Nonempty) :
    should D (fun w' ↦ ¬ p w') w = -should D p w :=
  supervaluation_not _ hne

/-- A true negated weak necessity leaves no best world for the existential continuation. -/
theorem not_exists_of_should_not (w : W) (h : should D (fun w' ↦ ¬ p w') w = 1) :
    ¬ ∃ w' ∈ D w, p w' :=
  fun ⟨w', hw', hp⟩ ↦ (should_eq_one_iff D _ w).1 h w' hw' hp

/-- In a mixed domain a negated strong necessity is true and the existential continuation
holds with it. -/
theorem must_false_of_indet (w : W) (h : should D p w = 0) :
    must D p w = -1 ∧ ∃ w' ∈ D w, p w' := by
  obtain ⟨⟨a, ha, hp⟩, b, hb, hn⟩ := (should_eq_zero_iff D p w).1 h
  have : ¬ ∀ w' ∈ D w, p w' := fun hall ↦ hn (hall b hb)
  exact ⟨by simp [must, this], a, ha, hp⟩

/-! ### Homogeneity removal -/

/-- *Must* is *should* with its gap removed, the universal quantifier being the meta-assertion
of the plural predication, as *all* is of *the*. -/
theorem must_eq_metaAssert_should : must D p = (fun v ↦ SignType.ofProp (v = 1)) ∘ should D p :=
  funext fun w ↦ by simp [must, should, supervaluation_eq_one_iff]

theorem isBivalent_must : Trivalent.IsBivalent (must D p) :=
  must_eq_metaAssert_should D p ▸ Trivalent.isBivalent_ofProp_eq_one _

/-- In a mixed domain the negated bare *should* is not true, while the negated *necessarily
should* is true and compatible with the existential continuation. -/
theorem necessarily_removes_gap (w : W) (h : should D p w = 0) :
    should D (fun w' ↦ ¬ p w') w ≠ 1 ∧ -SignType.ofProp (should D p w = 1) = 1 ∧
      ∃ w' ∈ D w, p w' := by
  obtain ⟨⟨a, ha, hp⟩, -⟩ := (should_eq_zero_iff D p w).1 h
  refine ⟨fun h' ↦ not_exists_of_should_not D p w h' ⟨a, ha, hp⟩, ?_, a, ha, hp⟩
  rw [h]; rfl

/-! ### Borderline cases and exception tolerance -/

/-- The two doors to the living room. -/
inductive Door
  | left
  | right
  deriving DecidableEq, Fintype

/-- Both doors are equally good, so both worlds are best. -/
def doors : Door → Finset Door := fun _ ↦ {.left, .right}

/-- The issue that separates every world from every other. -/
abbrev strict : Setoid Door := ⊥

/-- Taking the right door *should* be taken is neither true nor false — neither assertible nor
deniable — while that it *must* be taken is false. -/
theorem two_doors : ∀ w, should doors (· = .right) w = 0 ∧
    ¬ usable strict (should doors (· = .right)) w ∧ must doors (· = .right) w = -1 := by
  decide

/-- In a world of the perfect-grade scenario the rules require every exercise or only most, and
the addressee does every exercise or only most. -/
inductive Grade
  | strictAll
  | strictMost
  | lenientAll
  | lenientMost
  deriving DecidableEq, Fintype

/-- The perfect-grade worlds under a world's rules. -/
def grade : Grade → Finset Grade
  | .strictAll | .strictMost => {.strictAll}
  | .lenientAll | .lenientMost => {.lenientAll, .lenientMost}

/-- Doing every exercise. -/
def everyExercise (w : Grade) : Prop := w = .strictAll ∨ w = .lenientAll

instance : DecidablePred everyExercise := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- *What is a way to get a perfect grade?* — every world answers alike. -/
abbrev wayQUD : Setoid Grade := ⊤

/-- *What are the minimal requirements?* — worlds are grouped by their rules. -/
abbrev minimalQUD : Setoid Grade := Setoid.ker grade

/-- Where most exercises suffice, *you should do every exercise* is usable under the first
question but not the second, and *you have to do every exercise* under neither. -/
theorem exception_tolerance :
    usable wayQUD (should grade everyExercise) .lenientAll ∧
      ¬ usable minimalQUD (should grade everyExercise) .lenientAll ∧
      ¬ usable wayQUD (must grade everyExercise) .lenientAll ∧
      ¬ usable minimalQUD (must grade everyExercise) .lenientAll := by
  decide

/-! ### Domain restriction -/

theorem domainRestriction_no_contradiction {D' D : Finset W} (h : D' ⊂ D) :
    ∃ q : W → Prop, (∀ w ∈ D', ¬ q w) ∧ ∃ w ∈ D, q w :=
  let ⟨w, hw, hw'⟩ := Finset.exists_of_ssubset h
  ⟨(· ∉ D'), fun _ hw h' ↦ h' hw, w, hw, hw'⟩

/-! ### Deriving weak from strong necessity

The quantifiers are families of sets of worlds, and the operator deriving weak necessity picks
out a minimal set in the family. For the universal quantifier `(D ⊆ ·)` that is mathlib's
`minimal_ge_iff`; the existential quantifier needs the lemma below. -/

section Minimal

open scoped Finset

variable {E : Type*} [DecidableEq E] {s X : Finset E}

theorem minimal_inter_nonempty_iff :
    Minimal (fun X ↦ (s ∩ X).Nonempty) X ↔ ∃ w ∈ s, X = {w} := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨w, hw⟩ := h.1
    obtain ⟨hws, hwX⟩ := Finset.mem_inter.1 hw
    have hsub : {w} ⊆ X := Finset.singleton_subset_iff.2 hwX
    exact ⟨w, hws, (h.2 ⟨w, by simp [hws]⟩ hsub).antisymm hsub⟩
  · rintro ⟨w, hw, rfl⟩
    exact minimal_iff_forall_lt.2 ⟨⟨w, Finset.mem_inter.2 ⟨hw, Finset.mem_singleton_self w⟩⟩,
      fun Y hY ↦ by simp [Finset.ssubset_singleton_iff.1 hY]⟩

theorem exists_minimal_inter_nonempty (h : s.Nonempty) :
    ∃ X, Minimal (fun X ↦ (s ∩ X).Nonempty) X :=
  let ⟨w, hw⟩ := h
  ⟨{w}, minimal_inter_nonempty_iff.2 ⟨w, hw, rfl⟩⟩

theorem not_existsUnique_minimal_inter_nonempty (h : 1 < #s) :
    ¬ ∃! X, Minimal (fun X ↦ (s ∩ X).Nonempty) X := by
  rintro ⟨X, -, huniq⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h
  exact hab <| Finset.singleton_injective <|
    (huniq {a} (minimal_inter_nonempty_iff.2 ⟨a, ha, rfl⟩)).trans
      (huniq {b} (minimal_inter_nonempty_iff.2 ⟨b, hb, rfl⟩)).symm

end Minimal

variable (w : W)

/-- Strong necessity, as a quantifier over sets of worlds, has the domain as its unique minimal
set, so picking that set out yields the plurality weak necessity denotes. -/
theorem x_must :
    (∃! X, Minimal (D w ⊆ ·) X) ∧ ∀ X, Minimal (D w ⊆ ·) X ↔ X = D w :=
  ⟨⟨D w, minimal_ge_iff.2 rfl, fun _ ↦ minimal_ge_iff.1⟩, fun _ ↦ minimal_ge_iff⟩

variable [DecidableEq W]

open scoped Finset in
/-- Possibility over two or more best worlds has minimal sets but no unique one, so a marker that
needs only some minimal set applies to it and one that needs the unique minimal set does not. -/
theorem possibility_witnesses (h : 1 < #(D w)) :
    (∃ X, Minimal (fun X ↦ (D w ∩ X).Nonempty) X) ∧
      ¬ ∃! X, Minimal (fun X ↦ (D w ∩ X).Nonempty) X :=
  ⟨exists_minimal_inter_nonempty (Finset.card_pos.1 (zero_lt_one.trans h)),
    not_existsUnique_minimal_inter_nonempty h⟩

/-! ### The data -/

/-- In the scenarios of the grid all, none, or some but not all of the best worlds satisfy the
prejacent. -/
inductive Scenario where
  | all
  | none
  | gap
  deriving DecidableEq, Repr

/-- A cell of the grid records the polarity of a sentence, its scenario and the value judged. -/
structure Cell where
  /-- The polarity of the sentence. -/
  polarity : Polarity
  /-- The scenario. -/
  scenario : Scenario
  /-- The value judged. -/
  observed : SignType
  deriving DecidableEq

/-- A row reads as a cell from its polarity and scenario. The value judged is the one the
polarity fixes where all or no best worlds satisfy the prejacent, and in the mixed scenario the gap
where the paper reports one and the recorded classical value otherwise. -/
def Cell.ofDatum (e : Datum) : Option Cell := do
  let pol ← e.parse? "polarity" [("positive", .positive), ("negative", .negative)]
  let sc ← e.parse? "condition" [("ALL", .all), ("NONE", .none), ("GAP", .gap)]
  let observed ← match sc, pol with
    | .all, .positive | .none, .negative => some 1
    | .all, .negative | .none, .positive => some (-1)
    | .gap, _ =>
      if e.feature? "gap_detected" = some "true" then some 0
      else e.parse? "classical_value" [("true", 1), ("false", -1)]
  some ⟨pol, sc, observed⟩

/-- The polarity-by-scenario grid for *should*. -/
def shouldGrid : List Cell :=
  (Examples.all.filter (·.feature? "modal" == some "should")).filterMap Cell.ofDatum

/-- A representative domain for each scenario, a world being the prejacent's truth value at it. -/
def scenarioDomain : Scenario → Finset Bool
  | .all => {true}
  | .none => {false}
  | .gap => {true, false}

/-- The plural semantics' value at a cell predicates the negated prejacent at negative polarity. -/
def shouldPredict (pol : Polarity) (s : Scenario) : SignType :=
  match pol with
  | .positive => should (fun _ ↦ scenarioDomain s) (· = true) true
  | .negative => should (fun _ ↦ scenarioDomain s) (· = false) true

/-- Domain restriction's value at a cell is universal quantification, negated by strong Kleene
negation. -/
def domainRestrictionPredict (pol : Polarity) (s : Scenario) : SignType :=
  pol • must (fun _ ↦ scenarioDomain s) (· = true) true

/-- The plural semantics reproduces every cell of the *should* grid. -/
theorem should_matches_grid :
    ∀ d ∈ shouldGrid, shouldPredict d.polarity d.scenario = d.observed := by
  decide

/-- Domain restriction matches the classical cells and fails exactly the gap cells. -/
theorem domainRestriction_fails_exactly_gap :
    ∀ d ∈ shouldGrid,
      (domainRestrictionPredict d.polarity d.scenario = d.observed ↔ d.scenario ≠ .gap) := by
  decide

theorem weak_negated_contradicts :
    ∀ e ∈ Examples.all, e.feature? "force" = some "weak" → (e.feature? "negation").isSome →
      e.feature? "remover" = none → e.feature? "continuation_felicity" = some "infelicitous" := by
  decide

theorem strong_extraclausal_compatible :
    ∀ e ∈ Examples.all, e.feature? "force" = some "strong" →
      e.feature? "negation" = some "extra-clausal" →
        e.feature? "continuation_felicity" = some "felicitous" := by
  decide

theorem necessarily_licenses_continuation :
    ∀ e ∈ Examples.all, e.feature? "remover" = some "necessarily" →
      e.feature? "continuation_felicity" = some "felicitous" := by
  decide

theorem ne_only_necessity :
    ∀ e ∈ Examples.all,
      (e.feature? "derivation" = some "NE" → e.feature? "base" = some "possibility" →
        e.judgment = .ungrammatical) ∧
      (e.feature? "derivation" = some "CF" → e.judgment = .acceptable) := by
  decide

end AghaJeretic2022
