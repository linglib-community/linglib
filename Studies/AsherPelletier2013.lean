module

public import Linglib.Semantics.Genericity.Normality
public import Studies.Cohen1999
public import Linglib.Data.Examples.AsherPelletier2013
public import Mathlib.Probability.ConditionalProbability

/-!
# Asher & Pelletier 2013: generics as modal quantifiers

A characterizing generic *φs ψ* is ∀x(φ(x) > ψ(x)), with > the weak conditional of commonsense
entailment: for each individual, ψ holds throughout the worlds where that individual is a normal φ,
the conditional of a normality on worlds (`Genericity.Normality.gen`). Normality is selected per
restrictor, so *Birds fly* and *Penguins don't fly* hold together, the normal Opus-penguin worlds
not being normal Opus-bird worlds, which a fixed set of normal worlds cannot provide; and what
counts as normal is open to construal, the teleological and the statistical construal disagreeing on
whether turtles live to be a hundred. Against the probabilistic rival, on which a generic is true
when the scope is more likely than not given the restrictor, the paper objects that a margin just
over half verifies generics that are not true, and that embedded generics trivialize the account:
under conditionalization a restrictor compatible with the scope and with its negation is independent
of the scope, so the probability of the conditional collapses to that of the scope. Logical forms
are then built by putting the focused material in the nuclear scope and its alternatives in the
restrictor, which weakens the restrictor where needed (ducks lay eggs), lets a tautologous
restrictor deliver an existential (firemen are available), and, with a further generic over
circumstances, gives mosquitoes their disposition to carry the virus.

Item numbers follow the 2012 preprint.

## Main definitions

* `generic`: the generic quantifier over a normality on worlds, whose conditional is the weak
  conditional.
* `generic_disjoint`, `generic_inter`: contrary generics select disjoint worlds; the scope
  weakens.
* `normal_ofAccess_eq_empty`, `exists_bird_penguin`: a fixed set of normal worlds leaves no normal
  penguin world once birds fly and penguins don't, while a normality from an ordering of worlds
  has one.
* `existentialReading`, `gen_univ`, `doubleGeneric`: the alternatives-based, the tautologous,
  and the circumstantial restrictor.
* `Conditionalizes`, `cond_eq_of_conditionalizes`, `measure_compl_eq_zero_of_conditionalizes`:
  the trivialization of probabilistic generics.

## Implementation notes

Conditionalization is required only of events that leave the restrictor possible,
$\mu(a \cap d) \neq 0$, as in [lewis-1976]. Lewis's argument uses it at three events. Required
of every such event, the rule is stronger than the argument needs: for a restrictor compatible
with the scope and with its negation it already gives the restrictor probability one
(`measure_compl_eq_zero_of_conditionalizes`), [milne-2003]'s two-valuedness, which the paper
cites. `cond_eq_of_conditionalizes` is therefore the reductio Lewis intends, with no model in
which the restrictor has probability below one.

## References

* [asher-pelletier-2013]
* [asher-morreau-1991], [asher-morreau-1995], [pelletier-asher-1997] — the modal account
* [cohen-1999a] — the probabilistic rival
* [leslie-2008] — the counterexamples
* [lewis-1976], [milne-2003] — the triviality argument
-/

@[expose] public section

namespace AsherPelletier2013

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {W E : Type*}

/-! ### The modal quantifier -/

open Genericity

variable (n : Normality W W)

/-- The generic `∀x(φ(x) > ψ(x))` of (2) holds when each individual satisfies `ψ` throughout the
worlds where it is a normal `φ`. -/
def generic (φ ψ : E → Set W) (w : W) : Prop := ∀ a, w ∈ n.gen (φ a) (ψ a)

/-- Contrary generics select disjoint normal worlds for each individual: if birds fly and
penguins don't, the normal Opus-penguin worlds are not normal Opus-bird worlds. -/
theorem generic_disjoint {φ φ' ψ : E → Set W} {w : W} (h : generic n φ ψ w)
    (h' : generic n φ' (fun a ↦ (ψ a)ᶜ) w) (a : E) :
    Disjoint (n.normal w (φ a)) (n.normal w (φ' a)) :=
  n.disjoint_normal_of_disjoint (h a) (h' a) disjoint_compl_right

/-- A generic with a conjoined scope entails the generic with either conjunct. -/
theorem generic_inter {φ ψ χ : E → Set W} {w : W} (h : generic n φ (fun a ↦ ψ a ∩ χ a) w) :
    generic n φ ψ w :=
  fun a _ hv ↦ (h a hv).1

/-- With logical truths selecting the world of evaluation itself, a tautologous restrictor
makes the conditional its consequent at that world. -/
theorem gen_univ {w : W} (h : n.normal w Set.univ = {w}) (q : Set W) :
    w ∈ n.gen Set.univ q ↔ w ∈ q := by
  simp [h]

/-- With a fixed set of normal worlds, *Birds fly* and *Penguins don't fly* leave Opus no normal
penguin world ((7), (8)). -/
theorem normal_ofAccess_eq_empty {B : W → Set W} {bird penguin fly : Set W} {w : W}
    (hpb : penguin ⊆ bird) (hb : w ∈ (Normality.ofAccess B).gen bird fly)
    (hp : w ∈ (Normality.ofAccess B).gen penguin flyᶜ) :
    (Normality.ofAccess B).normal w penguin = ∅ :=
  (Normality.ofAccess B).normal_eq_empty_of_disjoint (Conditional.strictImp_anti_left hpb hb) hp
    disjoint_compl_right

/-- With normality from an ordering of worlds, *Birds fly* and *Penguins don't fly* are compatible
with a normal Opus-penguin world ((7), (8)). -/
theorem exists_bird_penguin :
    ∃ (n : Normality Bool Bool) (bird penguin fly : Set Bool), penguin ⊆ bird ∧
      true ∈ n.gen bird fly ∧ true ∈ n.gen penguin flyᶜ ∧ (n.normal true penguin).Nonempty := by
  refine ⟨.ofOrdering (fun _ ↦ Set.univ) fun _ ↦ inferInstance, Set.univ, {true}, {false},
    Set.subset_univ _, fun x hx ↦ ?_, fun x hx ↦ ?_, true, ⟨trivial, rfl⟩, fun _ h _ ↦ h.2 ▸ le_rfl⟩
  · cases x
    · rfl
    · exact absurd (hx.2 ⟨trivial, trivial⟩ (Bool.false_le true)) (by decide)
  · rw [show x = true from hx.1.2]
    exact Bool.noConfusion

/-- On the teleological construal a turtle's normal worlds are those where it reaches a hundred. -/
def teleological : Normality Bool Bool := .ofAccess fun _ ↦ {true}

/-- On the statistical construal a turtle's normal worlds are those where it dies young. -/
def statistical : Normality Bool Bool := .ofAccess fun _ ↦ {false}

theorem turtles (w : Bool) :
    w ∈ teleological.gen Set.univ {true} ∧ w ∉ statistical.gen Set.univ {true} :=
  ⟨fun _ hx ↦ hx.1, fun h ↦ by simpa using h ⟨rfl, Set.mem_univ false⟩⟩

/-! ### Restrictors -/

/-- The existential reading of *Typhoons arise in this part of the Pacific*: for every
alternative property `P` of the place, normally `P` is the property that typhoons arise
there. -/
def existentialReading (Alt : Set (E → Set W)) (T : E → Set W) (c : E) (w : W) : Prop :=
  ∀ P ∈ Alt, w ∈ n.gen (P c) {_v | P = T}

theorem existentialReading.normal_subset {Alt : Set (E → Set W)} {T : E → Set W} {c : E} {w : W}
    (h : existentialReading n Alt T c w) {P : E → Set W} (hP : P ∈ Alt) :
    n.normal w (P c) ⊆ T c := by
  intro v hv
  have hPT : P = T := h P hP hv
  subst hPT
  exact n.normal_subset w (P c) hv

/-- A double generic holds when for each individual, in its normal worlds, every appropriate
circumstance normally has it carry the virus, a disposition rather than a frequency. -/
def doubleGeneric {Ev : Type*} (φ : E → Set W) (C : Ev → Set W) (ψ : E → Ev → Set W) (w : W) :
    Prop :=
  generic n φ (fun a ↦ {v | ∀ e, v ∈ n.gen (C e) (ψ a e)}) w

theorem doubleGeneric_univ {Ev : Type*} (h : ∀ v, n.normal v Set.univ = {v}) (φ : E → Set W)
    (ψ : E → Ev → Set W) (w : W) :
    doubleGeneric n φ (fun _ ↦ Set.univ) ψ w ↔ generic n φ (fun a ↦ {v | ∀ e, v ∈ ψ a e}) w := by
  simp [doubleGeneric, generic, h]

/-! ### Against the probabilistic account -/

/-- A cat has a tail in 11 of 20 equally normal cases, just over half. -/
def tailed : Fin 20 → Prop := fun w ↦ w.val < 11

instance : DecidablePred tailed := fun w ↦ Nat.decLt w.val 11

theorem cohen_too_weak :
    Cohen1999.gen (Finset.univ : Finset (Fin 20)) (fun _ ↦ True) (fun _ ↦ True) tailed ∧
      (0 : Fin 20) ∉ (⊤ : Normality (Fin 20) (Fin 20)).gen Set.univ {w | tailed w} := by
  refine ⟨by decide, fun h ↦ ?_⟩
  exact absurd (h (Set.mem_univ (11 : Fin 20))) (by decide)

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- A proposition `c` for the conditional `a > b` conditionalizes when its probability given
any `d` that leaves `a` possible is that of `b` given `a` and `d`, [lewis-1976]'s (7). -/
def Conditionalizes (a b c : Set Ω) : Prop :=
  ∀ d, MeasurableSet d → μ (a ∩ d) ≠ 0 → μ[c | d] = μ[b | a ∩ d]

/-- [lewis-1976]'s first triviality result: under conditionalization, a restrictor compatible
with the scope and with its negation is independent of the scope. -/
theorem cond_eq_of_conditionalizes {a b c : Set Ω} (ha : MeasurableSet a)
    (hb : MeasurableSet b) (h : Conditionalizes μ a b c) (h₁ : μ (a ∩ b) ≠ 0)
    (h₂ : μ (a ∩ bᶜ) ≠ 0) : μ[b | a] = μ b := by
  have ha0 : μ a ≠ 0 := fun h0 ↦ h₁ (measure_mono_null Set.inter_subset_left h0)
  have hc : μ c = μ[b | a] := by simpa using h Set.univ .univ (by rwa [Set.inter_univ])
  have hb1 : μ[c | b] = 1 := by
    rw [h b hb h₁, cond_apply (ha.inter hb), Set.inter_assoc, Set.inter_self]
    exact ENNReal.inv_mul_cancel h₁ (measure_ne_top μ _)
  have hb0 : μ[c | bᶜ] = 0 := by
    rw [h bᶜ hb.compl h₂, cond_apply (ha.inter hb.compl), Set.inter_assoc, Set.compl_inter_self,
      Set.inter_empty, measure_empty, mul_zero]
  have htot := cond_add_cond_compl_eq hb μ (t := c)
  rw [hb1, hb0, one_mul, zero_mul, add_zero] at htot
  rw [← hc]
  exact htot.symm

/-- [milne-2003]'s two-valuedness, which the paper cites: under conditionalization, a restrictor
compatible with the scope and with its negation is certain. Conditioning on `(a ∩ b) ∪ aᶜ`
makes `c` certain and conditioning on `(a ∩ bᶜ) ∪ aᶜ` makes it impossible, and `aᶜ` lies in
both events. -/
theorem measure_compl_eq_zero_of_conditionalizes {a b c : Set Ω} (ha : MeasurableSet a)
    (hb : MeasurableSet b) (hc : MeasurableSet c) (h : Conditionalizes μ a b c)
    (h₁ : μ (a ∩ b) ≠ 0) (h₂ : μ (a ∩ bᶜ) ≠ 0) : μ aᶜ = 0 := by
  have hd₁ : MeasurableSet (a ∩ b ∪ aᶜ) := (ha.inter hb).union ha.compl
  have hd₂ : MeasurableSet (a ∩ bᶜ ∪ aᶜ) := (ha.inter hb.compl).union ha.compl
  have ha₁ : a ∩ (a ∩ b ∪ aᶜ) = a ∩ b := by ext; simp +contextual
  have ha₂ : a ∩ (a ∩ bᶜ ∪ aᶜ) = a ∩ bᶜ := by ext; simp +contextual
  have hpos₁ : μ (a ∩ b ∪ aᶜ) ≠ 0 := fun h0 ↦ h₁ (measure_mono_null Set.subset_union_left h0)
  have hpos₂ : μ (a ∩ bᶜ ∪ aᶜ) ≠ 0 := fun h0 ↦ h₂ (measure_mono_null Set.subset_union_left h0)
  -- given `(a ∩ b) ∪ aᶜ`, `c` is certain
  have hone : μ[c | a ∩ b ∪ aᶜ] = 1 := by
    rw [h _ hd₁ (by rwa [ha₁]), ha₁, cond_apply (ha.inter hb), Set.inter_assoc, Set.inter_self]
    exact ENNReal.inv_mul_cancel h₁ (measure_ne_top μ _)
  -- given `(a ∩ bᶜ) ∪ aᶜ`, `c` is impossible
  have hzero : μ[c | a ∩ bᶜ ∪ aᶜ] = 0 := by
    rw [h _ hd₂ (by rwa [ha₂]), ha₂, cond_apply (ha.inter hb.compl), Set.inter_assoc,
      Set.compl_inter_self, Set.inter_empty, measure_empty, mul_zero]
  have hinv₁ : (μ (a ∩ b ∪ aᶜ))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (measure_ne_top μ _)
  have hinv₂ : (μ (a ∩ bᶜ ∪ aᶜ))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (measure_ne_top μ _)
  have hout : μ (aᶜ ∩ cᶜ) = 0 := by
    have := cond_isProbabilityMeasure (μ := μ) hpos₁
    have : μ[cᶜ | a ∩ b ∪ aᶜ] = 0 := by rw [prob_compl_eq_one_sub hc, hone, tsub_self]
    rw [cond_apply hd₁] at this
    exact measure_mono_null (Set.inter_subset_inter_left _ Set.subset_union_right)
      ((mul_eq_zero.1 this).resolve_left hinv₁)
  have hin : μ (aᶜ ∩ c) = 0 := by
    rw [cond_apply hd₂] at hzero
    exact measure_mono_null (Set.inter_subset_inter_left _ Set.subset_union_right)
      ((mul_eq_zero.1 hzero).resolve_left hinv₂)
  rw [← measure_inter_add_sdiff aᶜ hc, Set.sdiff_eq, hin, hout, add_zero]

theorem cohen_iff_scope {a b c : Set Ω} (ha : MeasurableSet a) (hb : MeasurableSet b)
    (h : Conditionalizes μ a b c) (h₁ : μ (a ∩ b) ≠ 0) (h₂ : μ (a ∩ bᶜ) ≠ 0) :
    1 / 2 < μ[b | a] ↔ 1 / 2 < μ b := by
  rw [cond_eq_of_conditionalizes μ ha hb h h₁ h₂]

end AsherPelletier2013
