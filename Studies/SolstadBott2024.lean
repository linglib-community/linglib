module

public import Linglib.Fragments.German.Verbs
public import Linglib.Semantics.Presupposition.Verb
public import Linglib.Data.Experiments.SolstadBott2024
public import Studies.SolstadBott2022
public import Studies.Schlenker2009
public import Studies.Kalomoiros2023
public import Studies.TonhauserEtAl2013

/-!
# Solstad & Bott (2024): Cataphoric Resolution of Projective Content: The Case of Occasion Verbs

An occasion verb such as *gratulieren* 'congratulate' implies that an eventuality before the
agent's action gave the agent reason to act, the occasion. Solstad and Bott show in three rating
experiments that the implication projects, that a sentence with an occasion verb is degraded
unless another sentence supplies the occasion, and that the supporting sentence may follow the
verb's sentence as well as precede it, where pronouns, demonstratives and *auch* 'too' need it to
precede. In the antecedent of a conditional a conjoined clause entailing the occasion filters the
implication from either side, where factive and aspectual triggers are filtered from the left
only.

## Main statements

* `SolstadBott2024.strongContextualFelicity_iff`: of the three constraints a trigger may place
  on the discourse around it, only the one demanding a preceding sentence is a strong contextual
  felicity constraint in the sense of Tonhauser, Beaver, Roberts and Simons.
* `SolstadBott2024.contextTests_iff_licenses`: a supported context differs reliably from the
  neutral one in the paper's tests exactly where the trigger's constraint is met.
* `SolstadBott2024.Account.filters_iff`: incremental local contexts and limited symmetry filter
  the implication only after the clause entailing it, symmetric local contexts on either side,
  and local accommodation everywhere.
* `SolstadBott2024.fits_iff`: of the four accounts only symmetric local contexts fit the
  occasion verbs of Experiment 3, and only the two asymmetric ones the factive and aspectual
  triggers.

## Implementation notes

* A discourse is the information before and after the trigger's sentence, and a constraint is
  met in a context type when it holds whenever the supporting sentence entails the content.
* An antecedent is evaluated in the utterance context, without the conditional around it, and an
  account filters the implication when the antecedent is acceptable in every context.
* A test of Block 1 is reliable when its printed p is below .05, and a contrast of Experiment 3
  when its printed t is at least 2 in absolute value, which agrees with the two tests the paper
  reports for that experiment (`reliable_triggerLast_iff`).
* The Block 1 means are recomputed from the authors' trial-level data. The Block 2 means of the
  established triggers are plotted only.

## TODO

* The paper's suggestion that an occasion verb raises the question why the agent acted, which
  must be addressed before or after the verb, is not formalized.

## References

* [solstad-bott-2024]
* [tonhauser-beaver-roberts-simons-2013]
* [tonhauser-beaver-degen-2018]
* [mandelkern-etal-2020]
* [schlenker-2009]
* [kalomoiros-2023]
* [solstad-bott-2022]
-/

@[expose] public section

namespace SolstadBott2024

open Presupposition Data.Experiments

variable {W : Type*}

/-! ### Contextual constraints -/

/-- The constraint a trigger places on the discourse around its sentence. It places none, or it
demands that what precedes entail the content, the strong contextual felicity of Tonhauser and
colleagues, or that what precedes or what follows entail it, as occasion verbs do. -/
inductive Felicity
  | free
  | strong
  | weak
  deriving DecidableEq, Repr, Fintype

/-- The constraint holds of the content `m`, given the information before and after the
trigger's sentence. -/
def Felicity.Satisfied (m before after : Set W) : Felicity → Prop
  | free => True
  | strong => before ⊆ m
  | weak => before ⊆ m ∨ after ⊆ m

/-- The information before the trigger's sentence in a context type, where the supporting
sentence has the content `p`. -/
def Context.before (p : Set W) : Context → Set W
  | anaphoric => p
  | _ => Set.univ

/-- The information after the trigger's sentence in a context type. -/
def Context.after (p : Set W) : Context → Set W
  | cataphoric => p
  | _ => Set.univ

/-- A constraint is met in a context type when it is satisfied whenever the supporting sentence
entails the content. -/
def Felicity.Licenses (f : Felicity) (k : Context) : Prop :=
  ∀ (W : Type) (m p : Set W), p ⊆ m → f.Satisfied m (k.before p) (k.after p)

variable {f : Felicity} {k : Context} {m : Set W}

/-- The strong constraint is met in an anaphoric context only, and the weak one in an anaphoric
or a cataphoric context. -/
theorem Felicity.licenses_iff :
    f.Licenses k ↔ f = .free ∨ f = .strong ∧ k = .anaphoric ∨ f = .weak ∧ k ≠ .neutral := by
  refine ⟨fun h ↦ ?_, fun h W m p hp ↦ ?_⟩
  · have := h Unit ∅ ∅ subset_rfl
    cases f <;> cases k <;> simp_all [Satisfied, Context.before, Context.after]
  · cases f <;> cases k <;> simp_all [Satisfied, Context.before, Context.after]

instance (f : Felicity) (k : Context) : Decidable (f.Licenses k) :=
  decidable_of_iff' _ Felicity.licenses_iff

/-- Take a sentence acceptable wherever some continuation meets its constraint. It is acceptable
only in contexts that entail the content, the strong contextual felicity of Tonhauser and
colleagues, exactly when the constraint is the strong one or the content is trivial. The
constraint of occasion verbs is therefore not one. -/
theorem strongContextualFelicity_iff :
    TonhauserEtAl2013.StrongContextualFelicity m (fun b ↦ ∃ a, f.Satisfied m b a) ↔
      f = .strong ∨ m = Set.univ := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · cases f
    · exact .inr (Set.univ_subset_iff.1 (h _ ⟨Set.univ, trivial⟩))
    · exact .inl rfl
    · exact .inr (Set.univ_subset_iff.1 (h _ ⟨m, .inr subset_rfl⟩))
  · rintro (rfl | rfl)
    exacts [fun _ ⟨_, h⟩ ↦ h, fun b _ ↦ b.subset_univ]

/-! ### Anaphoric and cataphoric contexts (Block 1) -/

/-- The constraint the paper finds for a trigger type of Experiment 1. -/
def TriggerOne.felicity : TriggerOne → Felicity
  | occasion => .weak
  | pronoun | demonstrative => .strong
  | _ => .free

/-- The constraint the paper finds for a trigger type of Experiment 2. -/
def TriggerTwo.felicity : TriggerTwo → Felicity
  | occasion => .weak
  | too => .strong
  | _ => .free

/-- In both experiments a supported context differs reliably from the neutral one exactly where
the trigger's constraint is met. A following sentence helps occasion verbs and does not help
pronouns, demonstratives or *auch*. -/
theorem contextTests_iff_licenses :
    (∀ r ∈ contextTestsExp1, r.p.toRat < 1 / 20 ↔ r.trigger.felicity.Licenses r.context) ∧
      ∀ r ∈ contextTestsExp2, r.p.toRat < 1 / 20 ↔ r.trigger.felicity.Licenses r.context := by
  decide +kernel

/-- The weak constraint is the only one of the three that the tests on occasion verbs fit. -/
theorem weak_of_occasion_tests (f : Felicity) :
    (∀ r ∈ contextTestsExp1, r.trigger = .occasion →
      (r.p.toRat < 1 / 20 ↔ f.Licenses r.context ∧ ¬ f.Licenses .neutral)) ↔ f = .weak := by
  revert f; decide +kernel

/-- Where a trigger's constraint is met only with a supporting sentence, the supported sentence
is rated above the unsupported one. -/
theorem neutral_lt_of_licenses :
    (∀ t k, ¬ t.felicity.Licenses .neutral → t.felicity.Licenses k →
      (blockOneExp1 t .neutral).mean.toRat < (blockOneExp1 t k).mean.toRat) ∧
      ∀ t k, ¬ t.felicity.Licenses .neutral → t.felicity.Licenses k →
        (blockOneExp2 t .neutral).mean.toRat < (blockOneExp2 t k).mean.toRat := by
  decide +kernel

/-! ### Filtering in the antecedent of a conditional (Experiment 3) -/

/-- The antecedent of a condition of Experiment 3, for a trigger with presupposition `p` and
assertion `p'` and a conjoined clause `q`. -/
def Antecedent.formula {Atom : Type*} (p p' q : Atom) : Antecedent → Formula Atom
  | triggerFirst => .bin .conj (.trigger p p') (.atom q)
  | triggerLast => .bin .conj (.atom q) (.trigger p p')
  | triggerOnly => .trigger p p'

/-- The accounts of filtering the paper weighs. On incremental local contexts and on the limited
symmetry of Kalomoiros only what precedes a trigger in a conjunction can satisfy its
presupposition, on the symmetric local contexts of Schlenker what follows can too, and on local
accommodation the presupposition is asserted in place. -/
inductive Account
  | incremental
  | limitedSymmetry
  | symmetric
  | localAccommodation
  deriving DecidableEq, Repr, Fintype

/-- The formula is acceptable in the context `C` on the account. -/
def Account.Accepts {Atom : Type*} (I : Atom → Set W) (C : Set W) (F : Formula Atom) :
    Account → Prop
  | incremental => Schlenker2009.Satisfaction .incremental C (Formula.occurrences I F)
  | limitedSymmetry => Kalomoiros2023.LimitedSymmetry C (Formula.occurrences I F)
  | symmetric => Schlenker2009.Satisfaction .symmetric C (Formula.occurrences I F)
  | localAccommodation => C ⊆ Function.support fun w ↦ SignType.ofProp (F.middleKleene I w = 1)

/-- An account filters the implication in an antecedent type when the antecedent is acceptable
in every context, provided the conjoined clause entails the implication. -/
def Account.Filters (a : Account) (x : Antecedent) : Prop :=
  ∀ (Atom W : Type) (I : Atom → Set W) (p p' q : Atom), I q ⊆ I p →
    ∀ C, a.Accepts I C (x.formula p p' q)

/-- Incremental local contexts and limited symmetry filter the implication only after the clause
entailing it, symmetric local contexts on either side of it, and local accommodation
everywhere. -/
theorem Account.filters_iff {a : Account} {x : Antecedent} :
    a.Filters x ↔ a = .localAccommodation ∨ a = .symmetric ∧ x ≠ .triggerOnly ∨
      (a = .incremental ∨ a = .limitedSymmetry) ∧ x = .triggerLast := by
  have hno : (∀ (I : Unit → Set Bool) C, a.Accepts I C (x.formula () () ()) → C ⊆ I ()) →
      ¬ a.Filters x := fun h hf ↦
    Bool.false_ne_true (h (fun _ ↦ {true}) Set.univ (hf _ _ _ _ _ _ subset_rfl _) trivial)
  cases a <;> cases x
  · exact iff_of_false (hno fun I C h ↦
      (Schlenker2009.satisfaction_incremental_initial_iff I (c := .conj) nofun).1 h) (by simp)
  · exact iff_of_true (fun _ _ I p p' q hq C ↦
      (Schlenker2009.satisfaction_and_right_iff I .incremental).2 fun _ _ hw ↦ hq hw) (by simp)
  · exact iff_of_false (hno fun I C h ↦
      (Schlenker2009.satisfaction_trigger_iff I .incremental).1 h) (by simp)
  · exact iff_of_false (hno fun I C h ↦ (Kalomoiros2023.limitedSymmetry_and_left I).1 h) (by simp)
  · exact iff_of_true (fun _ _ I p p' q hq C ↦ (Kalomoiros2023.limitedSymmetry_and_right I).2
      fun _ _ hw ↦ hq hw) (by simp)
  · exact iff_of_false (hno fun I C h ↦ (Kalomoiros2023.limitedSymmetry_trigger I).1 h) (by simp)
  · exact iff_of_true (fun _ _ I p p' q hq C ↦
      (Schlenker2009.satisfaction_symmetric_and_left_iff I).2 fun _ _ hw ↦ hq hw) (by simp)
  · exact iff_of_true (fun _ _ I p p' q hq C ↦
      (Schlenker2009.satisfaction_and_right_iff I .symmetric).2 fun _ _ hw ↦ hq hw) (by simp)
  · exact iff_of_false (hno fun I C h ↦
      (Schlenker2009.satisfaction_trigger_iff I .symmetric).1 h) (by simp)
  all_goals exact iff_of_true (fun _ _ _ _ _ _ _ _ _ _ ↦ SignType.ofProp_ne_zero) (by simp)

instance (a : Account) (x : Antecedent) : Decidable (a.Filters x) :=
  decidable_of_iff' _ Account.filters_iff

/-- A contrast with the trigger-first antecedent is reliable for a group of items. -/
def Reliable (g : TriggerGroup) (y : Antecedent) : Prop :=
  (followUp g y).t.toRat ≤ -2 ∨ 2 ≤ (followUp g y).t.toRat

instance (g : TriggerGroup) (y : Antecedent) : Decidable (Reliable g y) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The criterion agrees with the tests the paper reports for the trigger-first against the
trigger-last antecedent. -/
theorem reliable_triggerLast_iff (g : TriggerGroup) :
    Reliable g .triggerLast ↔ (orderTests g).p.toRat < 1 / 20 := by
  revert g; decide +kernel

/-- An account fits a group of items when each other antecedent type differs reliably from the
trigger-first one exactly when the account filters the implication in one of the two and not in
the other, and the antecedent where it is filtered is then the less projective. -/
def Account.Fits (a : Account) (g : TriggerGroup) : Prop :=
  ∀ y, y ≠ .triggerFirst →
    (Reliable g y ↔ ¬ (a.Filters .triggerFirst ↔ a.Filters y)) ∧
      (a.Filters .triggerFirst → ¬ a.Filters y → 0 < (followUp g y).estimate.toRat) ∧
        (¬ a.Filters .triggerFirst → a.Filters y → (followUp g y).estimate.toRat < 0)

instance (a : Account) (g : TriggerGroup) : Decidable (a.Fits g) :=
  inferInstanceAs (Decidable (∀ y : Antecedent, y ≠ .triggerFirst → _))

/-- Only symmetric local contexts fit the occasion verbs, and only the two asymmetric accounts
the factive and aspectual triggers. Local accommodation fits neither, since it makes the trigger
alone as little projective as the trigger after the clause entailing its content. -/
theorem fits_iff (a : Account) (g : TriggerGroup) :
    a.Fits g ↔ g = .occasion ∧ a = .symmetric ∨
      g = .factiveAspectual ∧ (a = .incremental ∨ a = .limitedSymmetry) := by
  revert a g; decide +kernel

/-! ### Projectivity and at-issueness (Block 2) -/

/-- The occasion implication is more projective and less at issue than the implications of the
two classes of psychological verbs. -/
theorem occasion_set_apart_from_psych :
    ∀ o ∈ blockTwo, ∀ r ∈ blockTwo, o.experiment = .exp2 → r.experiment = .exp2 →
      o.trigger = .occasion → r.trigger ≠ .occasion →
        r.projectivity.toRat < o.projectivity.toRat ∧
          o.atIssueness.toRat < r.atIssueness.toRat := by
  decide +kernel

/-- Across trigger types projectivity falls as at-issueness rises in both experiments, the
correlation of Tonhauser, Beaver and Degen. -/
theorem negative_correlation_replicates :
    ∀ r ∈ correlations, r.level = .triggerTypes → r.r.toRat < 0 := by
  decide +kernel

open SolstadBott2022 in
/-- Occasion verbs and experiencer-stimulus verbs share the object bias of implicit causality,
yet the implication of the latter is the less projective, so the bias does not come from
projective content alone. -/
theorem shared_bias_distinct_projectivity :
    VerbClass.agentEvocator.icausBias = VerbClass.expStim.icausBias ∧
      ∀ o ∈ blockTwo, ∀ e ∈ blockTwo, o.experiment = .exp2 → e.experiment = .exp2 →
        o.trigger = .occasion → e.trigger = .experiencerStimulus →
          e.projectivity.toRat < o.projectivity.toRat :=
  ⟨by decide, by decide +kernel⟩

/-! ### The occasion verbs -/

/-- The sixteen occasion verbs of the experiments are triggers in the German lexicon by their
occasion sense alone, being neither factive nor phasal nor implicative. -/
theorem occasion_isTrigger :
    ∀ v ∈ German.Verbs.allVerbs, v.senseTag = .occasion →
      v.toVerb.IsTrigger ∧ ¬ v.toVerb.IsFactive ∧ v.phasal = none ∧ v.implicative = ⊥ := by
  decide

end SolstadBott2024
