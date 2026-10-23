module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Linglib.Semantics.Modality.Necessity
public import Linglib.Logic.ComparativeProbability.WorldOrdering

/-!
# Kratzer (2012): Modals and Conditionals

This file formalizes the distinction the book's second chapter draws, in its typology of
conversational backgrounds, between realistic backgrounds representing evidence of things and
informational backgrounds representing the propositional content of a source of information.
A rumor that Roger was elected chief can feed either. As evidence of things it determines the
worlds that contain a counterpart of the rumor, produced the same way; whether Roger's
counterpart was elected there depends on how reliable the source is, so *given the rumor,
Roger must have been elected chief* is false when the rumor rests on shaky evidence and true
only when the source is reliable. As a source of information it determines the worlds
compatible with what it says, so the German reportative *sollen* in *dem Gerücht nach soll
Roger zum Häuptling gewählt worden sein* is true whatever the rumor's provenance, even a lie.
The informational background is therefore not realistic, since the actual world need not be
among the worlds the rumor describes.

The chapter's revised comparative possibility (§2.4) compares two propositions only on the worlds
where they differ. Along a ranking of worlds without ties, the probability measures that preserve
it are exactly those in which each world outweighs all worse worlds together, and Kratzer's toy
measure, giving the world `wᵢ` the probability `2ⁱ/15`, is one of them. Once two worlds are
unranked and a third is not above them, no measure giving that third world weight preserves it, as
the chapter observes for ties. Under the Limit Assumption a ranking without ties has a single best
world, so necessity and possibility collapse (§2.5). With a tie they come apart. The necessary
propositions are then those necessary however the tie is resolved, a supervaluation that Stalnaker
proposed for counterfactuals, and the merely possible ones are those holding at exactly one of the
tied best worlds.

## Implementation notes

The worlds record whether Roger was elected and whether the rumor exists, so every claim is
decided over `Bool × Bool`. The evidence-of-things background at a world lists the status of
the rumor there; the informational background lists the rumor's content. Reliability is stated
generally, as a proposition of the background entailing the content wherever the rumor
exists, rather than as an extra coordinate. Counterparts are identified with the rumor's
status, since the model has no other individuals.

The toy examples' worlds are `Fin 4`, the index of `wᵢ` being `i`, and all of them are
accessible, so comparative possibility is `KratzerLift` of the induced ordering with no modal
base to restrict it. The chapter states the rankings `O₁` and `O₂` of §2.5 directly; here they are
induced by nested ordering sources, and `O₁` is the ranking of §2.4. The general results of
§2.4–§2.5 are Kratzer's question and caveats answered for these operators rather than theorems the
chapter proves.

## References

* [kratzer-2012]
* [kratzer-1981] — the original typology of conversational backgrounds
* [stalnaker-1981] — the supervaluation over resolutions of an ordering, for counterfactuals
* [rullmann-matthewson-davis-2008] — the St'át'imcets reportative the chapter contrasts with
  German *sollen*
-/

@[expose] public section

namespace Kratzer2012

open Modality

/-- A world records whether Roger was elected chief and whether the rumor that he was exists. -/
abbrev World := Bool × Bool

/-- Roger was elected chief. -/
def chief : World → Prop := (·.1 = true)

/-- The rumor exists. -/
def rumor : World → Prop := (·.2 = true)

/-- As evidence of things, the rumor makes the background at `w` record its status in `w`, so
the accessible worlds are those with a counterpart of the actual rumor, or with none if there is
none. -/
def evidence : Background World := fun w ↦ {fun v ↦ v.2 = w.2}

/-- As a source of information, the rumor makes the background list its content. -/
def content : Background World := Function.const World {chief}

/-- Decide a claim about the backgrounds over the four worlds. -/
scoped macro "decide_worlds" : tactic =>
  `(tactic| ((try simp only [simpleNecessity, simplePossibility, ModalLogic.Box,
      ModalLogic.Diamond, Background.mem_accessible, Background.mem_accessibleWorlds,
      Background.IsRealistic, evidence, content, chief, rumor, Function.const_apply,
      Set.mem_singleton_iff, forall_eq, false_implies, implies_true, and_true]) <;>
      decide))

theorem evidence_realistic : evidence.IsRealistic := by decide_worlds

theorem content_not_realistic : ¬ content.IsRealistic := by decide_worlds

/-- The reportative reading of (8b) holds at every world, a lie included, because it reports
the rumor's content. -/
theorem sollen_holds (w : World) : simpleNecessity content chief w := by
  decide_worlds

/-- On shaky evidence (8a) fails, since where the rumor exists the worlds with a counterpart
of it include one where Roger was not elected, so Roger need not have been elected chief. -/
theorem not_must_chief (w : World) : ¬ simpleNecessity evidence chief w := by
  revert w; decide_worlds

theorem can_chief (w : World) (h : rumor w) : simplePossibility evidence chief w := by
  revert h w; decide_worlds

/-- From a reliable source (8a) holds. If the background also records that the rumor is
reliable, a proposition entailing its content wherever the rumor exists, then Roger must have
been elected chief, for any worlds and backgrounds. -/
theorem must_of_reliable {W : Type*} (rumor chief reliable : W → Prop) (f : Background W)
    (hf : ∀ w, rumor w → rumor ∈ f w ∧ reliable ∈ f w)
    (hrel : ∀ v, reliable v → rumor v → chief v) (w : W) (hw : rumor w) :
    simpleNecessity f chief w := fun v hv ↦
  have hv := Background.mem_accessibleWorlds.1 hv
  hrel v (hv reliable (hf w hw).2) (hv rumor (hf w hw).1)

/-! ### Grades of possibility (§2.4–§2.5)

Comparative possibility on a ranking of worlds is the revised lift `KratzerLift`, which compares
two propositions only on the worlds where they differ. Along a ranking without ties, the
probability measures that preserve it are those in which each world outweighs all worse worlds
together, and once two worlds are unranked with a third not above them, no measure giving that
third world weight preserves it. Under the Limit Assumption a ranking without ties has a single
best world, so necessity and possibility coincide. The toy examples of §2.4 and §2.5 are
instances on four worlds. -/

namespace Grades

open MeasureTheory ComparativeProbability
open scoped ENNReal

section Measures

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A measure is superincreasing along a ranking when each world outweighs all worse worlds
together. -/
def Superincreasing [Preorder α] (μ : Measure α) : Prop := ∀ a, μ (Set.Iio a) < μ {a}

theorem Superincreasing.measure_lt_iff [LinearOrder α] [Finite α] (hμ : Superincreasing μ)
    {D E : Set α} (hDE : Disjoint D E) : μ D < μ E ↔ ∃ b ∈ E, ∀ a ∈ D, a < b := by
  refine ⟨fun h ↦ ?_, fun ⟨b, hb, hD⟩ ↦ ?_⟩
  · by_contra hn
    push Not at hn
    obtain ⟨b₀, hb₀⟩ := E.eq_empty_or_nonempty.resolve_left fun hE ↦ by simp [hE] at h
    obtain ⟨a₀, ha₀, -⟩ := hn b₀ hb₀
    obtain ⟨m, hm, hmax⟩ := Set.exists_max_image D id (Set.toFinite D) ⟨a₀, ha₀⟩
    have hE : E ⊆ Set.Iio m := fun b hb ↦
      let ⟨a, ha, hba⟩ := hn b hb
      (hba.trans (hmax a ha)).lt_of_ne fun hbm ↦ Set.disjoint_left.mp hDE (hbm ▸ hm) hb
    exact lt_asymm h ((measure_mono hE).trans_lt
      ((hμ m).trans_le (measure_mono (Set.singleton_subset_iff.2 hm))))
  · exact (measure_mono fun a ha ↦ hD a ha).trans_lt
      ((hμ b).trans_le (measure_mono (Set.singleton_subset_iff.2 hb)))

variable [MeasurableSingletonClass α] [IsFiniteMeasure μ]

/-- No measure giving `c` weight preserves comparative possibility when neither of `a` and `b` is
strictly better than the other and `c` is not strictly better than `a`. The propositions `{a}` and
`{b, c}` are then equally good possibilities, which leaves `c` no weight (p. 41). -/
theorem not_kratzerLift_iff_measure_le {r : α → α → Prop} {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hab' : ¬ (r a b ∧ ¬ r b a))
    (hba : ¬ (r b a ∧ ¬ r a b)) (hca : ¬ (r c a ∧ ¬ r a c)) (hc : μ {c} ≠ 0) :
    ¬ ∀ A B : Set α, KratzerLift r A B ↔ μ B ≤ μ A := by
  intro h
  have ha : a ∉ ({b, c} : Set α) := by simp [hab, hac]
  have h₁ : μ {a} ≤ μ {b} :=
    (h {b} {a}).1 fun ⟨x, ⟨hxa, _⟩, hall⟩ ↦ hab' (hxa ▸ hall b ⟨rfl, Ne.symm hab⟩)
  have h₂ : μ {b, c} ≤ μ {a} := (h {a} {b, c}).1 fun ⟨x, ⟨hx, _⟩, hall⟩ ↦
    hx.elim (fun hxb ↦ hba (hxb ▸ hall a ⟨rfl, ha⟩)) (fun hxc ↦ hca (hxc ▸ hall a ⟨rfl, ha⟩))
  rw [Set.insert_eq, measure_union (Set.disjoint_singleton.2 hbc) (measurableSet_singleton c)]
    at h₂
  refine hc (le_zero_iff.1 ((ENNReal.add_le_add_iff_left (measure_ne_top μ {b})).1 ?_))
  simpa using h₂.trans h₁

variable [Finite α]

private theorem measure_le_iff_diff (A B : Set α) : μ B ≤ μ A ↔ μ (B \ A) ≤ μ (A \ B) := by
  rw [← measure_inter_add_sdiff B (Set.toFinite A).measurableSet,
    ← measure_inter_add_sdiff A (Set.toFinite B).measurableSet, Set.inter_comm,
    ENNReal.add_le_add_iff_left (measure_ne_top μ _)]

theorem kratzerLift_iff_measure_le_iff [LinearOrder α] :
    (∀ A B : Set α, KratzerLift (· ≥ ·) A B ↔ μ B ≤ μ A) ↔ Superincreasing μ := by
  refine ⟨fun h a ↦ not_le.1 fun hle ↦
    (h _ _).2 hle ⟨a, ⟨rfl, lt_irrefl a⟩, fun x hx ↦ ⟨hx.1.le, not_le.2 hx.1⟩⟩, fun hμ A B ↦ ?_⟩
  have key : ∀ a b : α, (b ≥ a ∧ ¬ a ≥ b) ↔ a < b := fun _ _ ↦ lt_iff_le_not_ge.symm
  rw [measure_le_iff_diff, ← not_lt, hμ.measure_lt_iff disjoint_sdiff_sdiff, KratzerLift]
  simp only [key]

end Measures

/-- Under the Limit Assumption, necessity and possibility coincide when no two accessible worlds
are tied or incomparable, since there is then a single best world (§2.5). -/
theorem humanNecessity_iff_humanPossibility {W : Type*} {f g : Background W}
    {w : W} (p : W → Prop) (hlim : LimitAssumption f g w) (hne : (f.accessibleWorlds w).Nonempty)
    (htot : ∀ u ∈ f.accessibleWorlds w, ∀ v ∈ f.accessibleWorlds w, (u ≤[g w] v) ∨ (v ≤[g w] u))
    (hanti : ∀ u ∈ f.accessibleWorlds w, ∀ v ∈ f.accessibleWorlds w,
      (u ≤[g w] v) → (v ≤[g w] u) → u = v) :
    humanNecessity f g p w ↔ humanPossibility f g p w := by
  obtain ⟨u, hu⟩ := hne
  obtain ⟨v, hv, -⟩ := hlim u hu
  have hbest : ∀ x ∈ bestWorlds f g w, x = v := fun x hx ↦
    (htot x hx.1 v hv.1).elim (fun h ↦ hanti x hx.1 v hv.1 h (hv.2 hx.1 h))
      (fun h ↦ hanti x hx.1 v hv.1 (hx.2 hv.1 h) h)
  rw [humanNecessity_iff_necessity hlim, humanPossibility_iff_possibility hlim, necessity_iff,
    possibility_iff]
  exact ⟨fun h ↦ ⟨v, hv, h v hv⟩,
    fun ⟨x, hx, hpx⟩ y hy ↦ (hbest y hy).trans (hbest x hx).symm ▸ hpx⟩

/-! #### The toy example of §2.4 -/

/-- The worlds `w₀`, `w₁`, `w₂`, `w₃` of the toy examples. -/
abbrev World := Fin 4

/-- The ordering source of §2.4, `{w₃}`, `{w₂, w₃}` and `{w₁, w₂, w₃}` at every world, which
induces the ranking `O₁` of §2.5. -/
def ideal : Background World := fun _ ↦ {(3 ≤ ·), (2 ≤ ·), (1 ≤ ·)}

theorem atLeastAsGoodAs_ideal_iff (v w z : World) : (w ≤[ideal v] z) ↔ z ≤ w := by
  simp only [Preorder.ofCriteria_le_iff, ideal, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp,
    forall_eq]
  fin_omega

/-- `p` is a better possibility than `q` when it is at least as good a possibility, in the
revised sense of §2.4, and not conversely. -/
def BetterPossibility (p q : Set World) : Prop :=
  KratzerLift (premisePreorder (ideal 0)).le p q ∧ ¬ KratzerLift (premisePreorder (ideal 0)).le q p

/-- Kratzer's probability measure gives `wᵢ` the probability `2ⁱ/15`. -/
noncomputable def prob : Measure World :=
  ∑ i : World, (2 ^ (i : ℕ) / 15 : ℝ≥0∞) • Measure.dirac i

/-- The probability of a proposition is the sum of `2ⁱ` over its worlds `wᵢ`, divided by 15,
which is the table of p. 42. -/
theorem prob_coe (s : Finset World) : prob s = ((∑ i ∈ s, 2 ^ (i : ℕ) : ℕ) : ℝ≥0∞) / 15 := by
  simp [prob, Set.indicator_apply, Finset.sum_ite_mem, ENNReal.sum_div]

/-- Kratzer's measure is a probability measure. -/
instance : IsProbabilityMeasure prob where
  measure_univ := by
    rw [← Finset.coe_univ, prob_coe, show (∑ i : World, 2 ^ (i : ℕ) : ℕ) = 15 from rfl]
    exact ENNReal.div_self (by norm_num) (by norm_num)

theorem superincreasing_prob : Superincreasing prob := by
  intro a
  rw [← Finset.coe_Iio, ← Finset.coe_singleton, prob_coe, prob_coe,
    ENNReal.div_lt_div_iff_left (by norm_num) (by norm_num), Nat.cast_lt]
  revert a
  decide

/-- One proposition is a better possibility than another exactly when it is more probable, so
the measure preserves comparative possibility (p. 43). -/
theorem betterPossibility_iff (p q : Set World) : BetterPossibility p q ↔ prob q < prob p := by
  have hr : (premisePreorder (ideal 0)).le = (· ≥ ·) :=
    funext₂ fun w z ↦ propext (atLeastAsGoodAs_ideal_iff 0 w z)
  have h := kratzerLift_iff_measure_le_iff.2 superincreasing_prob
  rw [BetterPossibility, hr, h, h, lt_iff_le_not_ge]

/-! #### The rankings of §2.5 -/

/-- The ordering source `{w₂}`, `{w₂, w₃}`, `{w₁, w₂, w₃}`, which induces the ranking `O₂`,
`w₂ < w₃ < w₁ < w₀`. -/
def swapped : Background World := fun _ ↦ {(· = 2), (2 ≤ ·), (1 ≤ ·)}

/-- The ordering source `{w₂, w₃}`, `{w₁, w₂, w₃}` of p. 46, which induces the ranking `O₃`,
`w₂, w₃ < w₁ < w₀`, with a tie. -/
def tied : Background World := fun _ ↦ {(2 ≤ ·), (1 ≤ ·)}

theorem bestWorlds_ideal : bestWorlds ⊥ ideal 0 = {3} := by
  ext x
  simp only [mem_bestWorlds, Background.accessibleWorlds_bot, Set.mem_univ, true_and,
    forall_const, atLeastAsGoodAs_ideal_iff, Set.mem_singleton_iff]
  revert x
  decide

theorem bestWorlds_swapped : bestWorlds ⊥ swapped 0 = {2} := by
  ext x
  simp only [mem_bestWorlds, Background.accessibleWorlds_bot, Set.mem_univ, true_and,
    forall_const, Preorder.ofCriteria_le_iff, swapped, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp,
    forall_eq]
  revert x
  decide

theorem bestWorlds_tied : bestWorlds ⊥ tied 0 = {2, 3} := by
  ext x
  simp only [mem_bestWorlds, Background.accessibleWorlds_bot, Set.mem_univ, true_and,
    forall_const, Preorder.ofCriteria_le_iff, tied, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp,
    forall_eq]
  revert x
  decide

private theorem humanNecessity_iff_forall {g : Background World} (p : World → Prop) :
    humanNecessity ⊥ g p 0 ↔ ∀ v ∈ bestWorlds ⊥ g 0, p v := by
  rw [humanNecessity_iff_necessity (.of_finite _ _ _), necessity_iff]

private theorem humanPossibility_iff_exists {g : Background World} (p : World → Prop) :
    humanPossibility ⊥ g p 0 ↔ ∃ v ∈ bestWorlds ⊥ g 0, p v := by
  rw [humanPossibility_iff_possibility (.of_finite _ _ _), possibility_iff]

/-- A proposition is necessary under `O₁` exactly when its probability is at least `8/15`
(§2.5). -/
theorem humanNecessity_iff (p : World → Prop) :
    humanNecessity ⊥ ideal p 0 ↔ 8 / 15 ≤ prob {w | p w} := by
  classical
  have h : ∀ s : Finset World, 8 ≤ ∑ i ∈ s, 2 ^ (i : ℕ) ↔ 3 ∈ s := by decide
  rw [humanNecessity_iff_forall, bestWorlds_ideal, ← Set.coe_toFinset {w | p w}, prob_coe,
    ← not_lt, ENNReal.div_lt_div_iff_left (by norm_num) (by norm_num),
    ← Nat.cast_ofNat (R := ℝ≥0∞) (n := 8), Nat.cast_lt, not_lt, h, Set.mem_toFinset]
  simp

/-- A proposition is possible under `O₁` exactly when it is necessary, so exactly when its
probability is at least `8/15` (§2.5). -/
theorem humanPossibility_iff (p : World → Prop) :
    humanPossibility ⊥ ideal p 0 ↔ 8 / 15 ≤ prob {w | p w} := by
  refine (humanNecessity_iff_humanPossibility p (.of_finite _ _ _)
    ⟨0, by simp [Background.accessibleWorlds_bot]⟩ (fun u _ v _ ↦ ?_)
    (fun u _ v _ h h' ↦ ?_)).symm.trans (humanNecessity_iff p)
  · simp only [atLeastAsGoodAs_ideal_iff]
    exact le_total v u
  · exact le_antisymm ((atLeastAsGoodAs_ideal_iff 0 v u).1 h')
      ((atLeastAsGoodAs_ideal_iff 0 u v).1 h)

/-- Under `O₃` the necessary propositions are those containing `w₂` and `w₃` (p. 44). -/
theorem humanNecessity_tied_iff (p : World → Prop) :
    humanNecessity ⊥ tied p 0 ↔ p 2 ∧ p 3 := by
  simp [humanNecessity_iff_forall, bestWorlds_tied]

/-- The propositions necessary under `O₃` are those necessary however the tie is resolved, under
both `O₁` and `O₂` (p. 44). -/
theorem humanNecessity_tied_iff_and (p : World → Prop) :
    humanNecessity ⊥ tied p 0 ↔
      humanNecessity ⊥ ideal p 0 ∧ humanNecessity ⊥ swapped p 0 := by
  simp [humanNecessity_iff_forall, bestWorlds_tied, bestWorlds_ideal, bestWorlds_swapped,
    and_comm]

/-- Resolving the tie collapses possibility into necessity, so the propositions possible under
both `O₁` and `O₂` are those necessary under both (p. 45). -/
theorem humanPossibility_and_iff (p : World → Prop) :
    humanPossibility ⊥ ideal p 0 ∧ humanPossibility ⊥ swapped p 0 ↔
      humanNecessity ⊥ ideal p 0 ∧ humanNecessity ⊥ swapped p 0 := by
  simp [humanNecessity_iff_forall, humanPossibility_iff_exists, bestWorlds_ideal,
    bestWorlds_swapped]

/-- Under `O₃` the merely possible propositions, possible but not necessary, are those containing
exactly one of `w₂` and `w₃` (p. 45). -/
theorem merelyPossible_tied_iff (p : World → Prop) :
    (humanPossibility ⊥ tied p 0 ∧ ¬ humanNecessity ⊥ tied p 0) ↔
      Xor (p 2) (p 3) := by
  simp only [humanNecessity_tied_iff, humanPossibility_iff_exists, bestWorlds_tied,
    Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, exists_eq_left]
  rw [xor_iff_or_and_not_and]

/-- The probability measure of p. 46 gives `w₀`, `w₁`, `w₂`, `w₃` the probabilities `1/11`,
`2/11`, `4/11` and `4/11`. -/
noncomputable def probTied : Measure World :=
  ∑ i : World, (((![1, 2, 4, 4] : World → ℕ) i : ℝ≥0∞) / 11) • Measure.dirac i

theorem probTied_coe (s : Finset World) :
    probTied s = ((∑ i ∈ s, (![1, 2, 4, 4] : World → ℕ) i : ℕ) : ℝ≥0∞) / 11 := by
  simp [probTied, Set.indicator_apply, Finset.sum_ite_mem, ENNReal.sum_div]

/-- The measure of p. 46 is a probability measure. -/
instance : IsProbabilityMeasure probTied where
  measure_univ := by
    rw [← Finset.coe_univ, probTied_coe,
      show (∑ i : World, (![1, 2, 4, 4] : World → ℕ) i : ℕ) = 11 from rfl]
    exact ENNReal.div_self (by norm_num) (by norm_num)

/-- Under `O₃` a proposition is necessary exactly when its probability is at least `8/11`
(p. 46). -/
theorem humanNecessity_tied_iff_probTied (p : World → Prop) :
    humanNecessity ⊥ tied p 0 ↔ 8 / 11 ≤ probTied {w | p w} := by
  classical
  have h : ∀ s : Finset World, 8 ≤ ∑ i ∈ s, (![1, 2, 4, 4] : World → ℕ) i ↔ 2 ∈ s ∧ 3 ∈ s := by
    decide
  rw [humanNecessity_tied_iff, ← Set.coe_toFinset {w | p w}, probTied_coe, ← not_lt,
    ENNReal.div_lt_div_iff_left (by norm_num) (by norm_num),
    ← Nat.cast_ofNat (R := ℝ≥0∞) (n := 8), Nat.cast_lt, not_lt, h]
  simp

/-- Under `O₃` a proposition is possible exactly when its probability is at least `4/11`
(p. 46). -/
theorem humanPossibility_tied_iff_probTied (p : World → Prop) :
    humanPossibility ⊥ tied p 0 ↔ 4 / 11 ≤ probTied {w | p w} := by
  classical
  have h : ∀ s : Finset World, 4 ≤ ∑ i ∈ s, (![1, 2, 4, 4] : World → ℕ) i ↔ 2 ∈ s ∨ 3 ∈ s := by
    decide
  rw [humanPossibility_iff_exists, bestWorlds_tied, ← Set.coe_toFinset {w | p w}, probTied_coe,
    ← not_lt, ENNReal.div_lt_div_iff_left (by norm_num) (by norm_num),
    ← Nat.cast_ofNat (R := ℝ≥0∞) (n := 4), Nat.cast_lt, not_lt, h]
  simp

/-- No measure giving `w₁` weight, the measure of p. 46 among them, preserves the comparative
possibility of `O₃`, under which `{w₂}` and `{w₁, w₃}` are equally good possibilities. -/
theorem not_kratzerLift_tied_iff (μ : Measure World) [IsFiniteMeasure μ] (h : μ {1} ≠ 0) :
    ¬ ∀ A B : Set World, KratzerLift (premisePreorder (tied 0)).le A B ↔ μ B ≤ μ A := by
  refine not_kratzerLift_iff_measure_le (a := 2) (b := 3) (c := 1) (by decide) (by decide)
    (by decide) ?_ ?_ ?_ h <;>
  simp [Preorder.ofCriteria_le_iff, tied]

end Grades

end Kratzer2012
