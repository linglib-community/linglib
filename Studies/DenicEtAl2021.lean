module

public import Linglib.Data.Experiments.DenicEtAl2021
public import Linglib.Semantics.Polarity.Licensing
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Fragments.English.PolarityItems
public import Studies.KadmonLandman1993
public import Linglib.Core.Probability.ConditionalProbability

/-!
# Denić et al. (2021): The influence of polarity items on inferential judgments

Participants rated how far a conclusion follows from a premise that differs from it in a superset
and a subset verb phrase (*saw birds*, *saw doves*), inside ten environments the paper classes as
upward entailing, downward entailing, non-monotone (*exactly 12*, *only 12*) or doubly negative, a
downward-entailing operator inside another. A negative polarity item in the premise lowered the
directional rating of the non-monotone environments in all four experiments and the
meta-analysis, and the positive polarity item *some* raised that of the doubly negative ones in
Experiment 3 and the meta-analysis (§8.1); the printed results are in
`Data/Experiments/DenicEtAl2021.json`. Here each environment denotes a function of its verb phrase
built from the substrate's quantifiers, from which the paper's classes and valid inferences follow.
The meaning route of §10.2 combines Kadmon and Landman's domain widening for *any* with Chater and
Oaksford's probabilistic semantics of quantified sentences.

## Main statements

* `Environment.classifies_iff`: the class the paper gives each environment is the one its
  denotation has, the doubly negative ones being upward entailing with the item in a
  downward-entailing constituent (§3.1.2, §5).
* `monotone_wideSome`: on its wide-scope reading *some* sits in an upward-entailing position
  whatever the environment, the confound of (9) and (27).
* `cond_eq_one_of_widen`, `exists_cond_lt_one_of_widen`: widening the domain of the object, (30),
  weakens the bridge premise of the probabilistic downward inference (33), and strictly so for
  some believer, (34).

## Implementation notes

* The English fragment gives *many* no reading; a model fixes one of Partee's cardinal and
  proportional readings, and every result holds for both. *Few* is the fragment's proportional
  reading.
* *Only 12* is its presupposition and assertion together, at least and at most twelve, which is
  *exactly 12* (`Environment.denotation_only12`); the licensing context is still focus *only*,
  downward entailing modulo the presupposition. Under *exactly 12* the substrate licenses no
  polarity item, although the paper finds them acceptable there to a degree (§3).
* *No alien spent a year without seeing birds* is *no* over the aliens and the year-spenders who
  did not see birds.

## References

* [denic-homer-rothschild-chemla-2021]
* [partee-1989]
* [kadmon-landman-1993]
* [chater-oaksford-1999]
-/

@[expose] public section

namespace DenicEtAl2021

open Quantifier GQ PolarityItem English.PolarityItems

/-! ### The environments -/

/-- The readings of *many* put at least a contextual number, or at least a contextual proportion,
of the restrictor in the scope. -/
def manyReadings {ι : Type*} : Set (GQ ι) :=
  Set.range atLeast ∪ Set.range fun p : ℕ × ℕ ↦ (NumberTree.threshold p.1 p.2).toGQ

theorem scopeMonotone_of_mem_manyReadings {ι : Type*} [Finite ι] {q : GQ ι}
    (h : q ∈ manyReadings) : ScopeMonotone q := by
  rcases h with ⟨n, rfl⟩ | ⟨⟨n, d⟩, rfl⟩
  exacts [scopeMonotone_atLeast n, (NumberTree.scopeMonotone_threshold n d).toGQ]

/-- A model fixes what the stimuli's nouns and adjectives are true of and the reading of *many*. -/
structure Model (ι : Type*) where
  /-- The aliens. -/
  alien : ι → Prop
  /-- The purple alien, the restrictor of *the purple alien*. -/
  purpleAlien : ι → Prop
  /-- The hairy individuals. -/
  hairy : ι → Prop
  /-- The individuals who spent a year on Earth. -/
  spentYear : ι → Prop
  /-- The reading of *many*. -/
  many : GQ ι
  /-- The reading of *many* is one the context leaves open. -/
  many_mem : many ∈ manyReadings

namespace Environment

variable {ι : Type*}

/-- The constituent hosting the item, as a function of its verb phrase, is the negated verb phrase
in the negative and doubly negative environments and the verb phrase itself elsewhere. -/
def host : Environment → (ι → Prop) → (ι → Prop)
  | .negative | .everyNot | .noWithout => compl
  | _ => id

/-- The rest of the sentence, as a function of the host constituent. -/
def outer (m : Model ι) : Environment → (ι → Prop) → Prop
  | .positive | .negative => the m.purpleAlien
  | .every => GQ.every m.alien
  | .many => m.many m.alien
  | .no => GQ.no m.alien
  | .few => GQ.few m.alien
  | .exactly12 => exactly 12 m.alien
  | .only12 => (atLeast 12 ⊓ atMost 12 : GQ ι) m.alien
  | .everyNot => fun V ↦ GQ.every (m.alien ⊓ V) m.hairy
  | .noWithout => fun V ↦ GQ.no m.alien (m.spentYear ⊓ V)

/-- The truth of an environment's sentence as a function of its verb phrase. -/
def denotation (e : Environment) (m : Model ι) : (ι → Prop) → Prop := e.outer m ∘ e.host

theorem denotation_only12 (m : Model ι) : only12.denotation m = exactly12.denotation m := by
  simp [denotation, outer, host, exactly_eq_atLeast_inf_atMost]

/-- An inference is valid in an environment when it holds in every finite model, so the
subset-to-superset inference is valid when the denotation is always monotone and the converse when
it is always antitone. -/
def Valid (e : Environment) : Direction → Prop
  | .subsetToSuperset => ∀ (ι : Type) [Fintype ι] (m : Model ι), Monotone (e.denotation m)
  | .supersetToSubset => ∀ (ι : Type) [Fintype ι] (m : Model ι), Antitone (e.denotation m)

/-- An environment's denotation classes it as upward entailing when the subset-to-superset
inference is valid and the item's host is monotone, as doubly negative when that inference is
valid and the host is antitone, as downward entailing when the converse is valid, and as
non-monotone when neither is. -/
def Classifies (e : Environment) : Monotonicity → Prop
  | .ue => e.Valid .subsetToSuperset ∧ ∀ ι : Type, Monotone (e.host (ι := ι))
  | .dn => e.Valid .subsetToSuperset ∧ ∀ ι : Type, Antitone (e.host (ι := ι))
  | .de => e.Valid .supersetToSubset
  | .nm => ¬ e.Valid .subsetToSuperset ∧ ¬ e.Valid .supersetToSubset

theorem valid_subsetToSuperset {e : Environment}
    (he : (environments e).monotonicity = .ue ∨ (environments e).monotonicity = .dn) :
    e.Valid .subsetToSuperset := fun ι _ m ↦ by
  have hc : Antitone (compl : (ι → Prop) → (ι → Prop)) := fun _ _ ↦ compl_le_compl
  cases e <;> simp [environments] at he
  · exact scopeMonotone_the m.purpleAlien
  · exact scopeMonotone_every m.alien
  · exact scopeMonotone_of_mem_manyReadings m.many_mem m.alien
  · exact ((restrictorAntitone_every m.hairy).comp_monotone fun _ _ ↦ inf_le_inf_left _).comp hc
  · exact ((scopeAntitone_no m.alien).comp_monotone fun _ _ ↦ inf_le_inf_left _).comp hc

theorem valid_supersetToSubset {e : Environment} (he : (environments e).monotonicity = .de) :
    e.Valid .supersetToSubset := fun _ _ m ↦ by
  cases e <;> simp [environments] at he
  · exact (scopeMonotone_the m.purpleAlien).comp_antitone fun _ _ ↦ compl_le_compl
  · exact scopeAntitone_no m.alien
  · exact scopeAntitone_few m.alien

/-- The countermodel has thirteen aliens, none hairy, all on Earth for a year, the first one
purple, and reads *many* as *at least one*. -/
def thirteen : Model (Fin 13) := ⟨fun _ ↦ True, (· = 0), fun _ ↦ False, fun _ ↦ True, atLeast 1,
  .inl ⟨1, rfl⟩⟩

theorem not_valid_subsetToSuperset {e : Environment}
    (he : (environments e).monotonicity = .de ∨ (environments e).monotonicity = .nm) :
    ¬ e.Valid .subsetToSuperset := fun h ↦ by
  have h := h _ thirteen
  cases e <;> simp [environments] at he
  case exactly12 => exact not_monotone_exactly (by simp) h
  case only12 => exact not_monotone_exactly (by simp) (denotation_only12 thirteen ▸ h)
  all_goals refine absurd (h (bot_le (a := ⊤)) ?_) ?_ <;>
    simp [denotation, outer, host, thirteen, the_iff, GQ.no, few_apply]

theorem not_valid_supersetToSubset {e : Environment} (he : (environments e).monotonicity ≠ .de) :
    ¬ e.Valid .supersetToSubset := fun h ↦ by
  have h := h _ thirteen
  cases e <;> simp [environments] at he
  case exactly12 => exact not_antitone_exactly (by simp) (by simp) h
  case only12 => exact not_antitone_exactly (by simp) (by simp) (denotation_only12 thirteen ▸ h)
  all_goals refine absurd (h (bot_le (a := ⊤)) ?_) ?_ <;>
    simp [denotation, outer, host, thirteen, the_iff, GQ.every, GQ.no, atLeast_apply]

/-- The paper's monotonicity classification of the ten environments is the one their denotations
give (§3.1.2, §5). -/
theorem classifies_iff (e : Environment) (k : Monotonicity) :
    e.Classifies k ↔ (environments e).monotonicity = k := by
  have hid : ¬ ∀ ι : Type, Antitone (id : (ι → Prop) → (ι → Prop)) := fun h ↦
    (h Unit (bot_le (a := ⊤)) ()) trivial
  have hc : ¬ ∀ ι : Type, Monotone (compl : (ι → Prop) → (ι → Prop)) := fun h ↦
    (h Unit (bot_le (a := ⊤)) () (fun h ↦ h)) trivial
  have hc' : ∀ ι : Type, Antitone (compl : (ι → Prop) → (ι → Prop)) := fun _ _ _ ↦ compl_le_compl
  have := @valid_subsetToSuperset e
  have := @valid_supersetToSubset e
  have := @not_valid_subsetToSuperset e
  have := @not_valid_supersetToSubset e
  cases e <;> cases k <;> simp_all [Classifies, host, environments, monotone_id]

/-! ### Licensing -/

/-- The licensing context of the narrowest operator over the item that the substrate counts as
downward entailing is negation, *no*, *few*, *without*, or focus *only*, downward entailing modulo
its presupposition; the upward-entailing environments and *exactly 12* have none. -/
def licensingContext : Environment → Option LicensingContext
  | .negative | .everyNot => some .negation
  | .no => some .nobody
  | .few => some .few
  | .noWithout => some .withoutClause
  | .only12 => some .onlyFocus
  | .positive | .every | .many | .exactly12 => none

/-- *Any*, *ever* and *at all* are licensed in the downward-entailing environments, by the inner
operator in doubly negative ones (§1, §5), and under *only 12*. -/
theorem licenses_of_mem_licensingContext {e : Environment} {c : LicensingContext}
    (h : c ∈ e.licensingContext) :
    c.licenser.Licenses any ∧ c.licenser.Licenses ever ∧ c.licenser.Licenses atAll := by
  cases e <;> simp only [licensingContext, Option.mem_def, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> decide

end Environment

/-! ### Wide scope of *some* -/

section WideScope

variable {ι ε : Type*}

/-- On the wide-scope reading of *some N* in an environment `f`, (9b) and (27), some member of `N`
is such that `f` holds of seeing it. -/
def wideSome (f : (ι → Prop) → Prop) (saw : ε → ι → Prop) (N : Set ε) : Prop :=
  ∃ y ∈ N, f (saw y)

/-- On its wide-scope reading *some* sits in an upward-entailing position, whatever the
environment, (9). -/
theorem monotone_wideSome (f : (ι → Prop) → Prop) (saw : ε → ι → Prop) :
    Monotone (wideSome f saw) := fun _ _ hN ⟨y, hy, h⟩ ↦ ⟨y, hN hy, h⟩

/-- In an upward-entailing environment the wide-scope reading (27) of *some doves* entails the
narrow-scope sentence about birds, so (26a) entails (26b). -/
theorem narrow_of_wideSome {f : (ι → Prop) → Prop} (hf : Monotone f) {saw : ε → ι → Prop}
    {N N' : Set ε} (hN : N ⊆ N') (h : wideSome f saw N) :
    f (KadmonLandman1993.existsInDomain N' saw) :=
  let ⟨y, hy, hf'⟩ := h; hf (fun _ hx ↦ ⟨y, hN hy, hx⟩) hf'

end WideScope

/-! ### Directional ratings -/

/-- The sign with which a direction enters the directional rating. -/
def Direction.sign : Direction → SignType
  | .subsetToSuperset => 1
  | .supersetToSubset => -1

/-- The directional rating keeps a subset-to-superset rating and reverses a superset-to-subset
one, in percent. -/
def directional : Direction → ℝ → ℝ
  | .subsetToSuperset, r => r
  | .supersetToSubset, r => 100 - r

/-- A response bias enters the directional rating with the sign of the direction, so a yes-bias
common to both directions cancels in their sum (§3.2). -/
theorem directional_add (d : Direction) (r b : ℝ) :
    directional d (r + b) = directional d r + d.sign * b := by
  cases d <;> simp [directional, Direction.sign]; ring

/-! ### The meaning route

On the probabilistic semantics, *No aliens saw birds* says that a random alien saw birds with
probability zero, (33), and the downward inference needs seeing doves to make seeing birds
certain. -/

section MeaningRoute

open MeasureTheory ProbabilityTheory KadmonLandman1993

variable {Ω ε : Type*} [MeasurableSpace Ω]

/-- In the probabilistic downward inference (33), if `e` has probability zero given `s` and
probability one given `u`, then `u` has probability zero given `s`. -/
theorem cond_eq_zero_of_cond_eq_one {μ : Measure Ω} [IsFiniteMeasure μ] {s e u : Set Ω}
    (hs : MeasurableSet s) (he : MeasurableSet e) (hu : MeasurableSet u) (h₁ : μ[e | s] = 0)
    (h₂ : μ[e | u] = 1) : μ[u | s] = 0 := by
  have hu₀ : μ u ≠ 0 := fun h ↦ by simp [cond_eq_zero_of_meas_eq_zero h] at h₂
  have := cond_isProbabilityMeasure (μ := μ) hu₀
  have null {t f : Set Ω} (ht : MeasurableSet t) (h : μ[f | t] = 0) : μ (t ∩ f) = 0 :=
    by_contra fun hne ↦ (cond_pos_of_inter_ne_zero ht hne).ne' h
  have : μ (s ∩ u) = 0 := measure_mono_null
    (fun x ⟨hx, hxu⟩ ↦ (em (x ∈ e)).imp (fun hxe ↦ ⟨hx, hxe⟩) fun hxe ↦ ⟨hxu, hxe⟩)
    (measure_union_null (null hs h₁) (null hu ((prob_compl_eq_zero_iff he).2 h₂)))
  rw [cond_apply hs, this, mul_zero]

/-- Since *any* widens the object's domain (30), seeing doves makes seeing any birds certain
whenever it makes seeing birds certain ((33), (34)). -/
theorem cond_eq_one_of_widen {μ : Measure Ω} {saw : ε → Set Ω}
    {birds anyBirds : Set ε} {D : Set Ω} (h : birds ⊆ anyBirds)
    (hD : μ[existsInDomain birds saw | D] = 1) : μ[existsInDomain anyBirds saw | D] = 1 :=
  le_antisymm prob_le_one (hD ▸ measure_mono (existsInDomain_mono saw h))

/-- Seeing doves can make seeing any birds certain but not seeing birds, the room (34) leaves for
*any* to help. -/
theorem exists_cond_lt_one_of_widen : ∃ (saw : Fin 2 → Set (Fin 2)) (doves birds anyBirds :
    Set (Fin 2)), birds ⊆ anyBirds ∧
      Measure.count[existsInDomain birds saw | existsInDomain doves saw] < 1 ∧
      Measure.count[existsInDomain anyBirds saw | existsInDomain doves saw] = 1 := by
  have h₀ : existsInDomain {0} (fun y : Fin 2 ↦ {y}) = {0} :=
    Set.ext fun _ ↦ ⟨fun ⟨_, hy, hw⟩ ↦ hw.trans hy, fun hw ↦ ⟨0, rfl, hw⟩⟩
  have h₁ : existsInDomain .univ (fun y : Fin 2 ↦ {y}) = .univ :=
    Set.eq_univ_of_forall fun w ↦ ⟨w, trivial, rfl⟩
  exact ⟨fun y ↦ {y}, .univ, {0}, .univ, Set.subset_univ _, by simp [h₀, h₁, cond_apply .univ],
    by simp [h₁]⟩

end MeaningRoute

end DenicEtAl2021
