module

public import Linglib.Logic.Natural.Additivity
public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Semantics.Conditionals.Horizon
public import Linglib.Semantics.Degree.Superlative
public import Linglib.Semantics.Modality.Background
public import Linglib.Semantics.Focus.Particles
public import Linglib.Semantics.Attitudes.Preference.BestWorlds

/-!
# Strawson entailment

An operator into trivalent propositions is Strawson downward entailing when shrinking its argument
gives a conclusion that the original Strawson-entails, the inference being checked only where the
presuppositions involved hold. Von Fintel introduces the notion to keep the Fauconnier–Ladusaw
theory of negative polarity licensing for focus *only*, the adversative attitudes, superlatives,
temporal *since* and conditional antecedents, none of which is downward entailing in the classical
sense. Gajewski defines Strawson anti-additivity, which the same operators also satisfy.

Strawson entailment adds presuppositions only as premises, so each Strawson property holds as soon
as the operator's values, where defined, follow an assertion with the classical counterpart,
whatever the presupposition; it is the presupposition that defeats the classical property.

## Main definitions

* `IsStrawsonDE`, `IsStrawsonUE`: antitonicity and monotonicity under Strawson entailment.
* `IsStrawsonAntiAdditive`: `f (p ⊔ q)` is Strawson equivalent to `f p` conjoined with `f q`.
* `only`: von Fintel's *only* over a name.

## Main results

* `IsStrawsonDE.of_antitone`, `IsStrawsonUE.of_monotone`,
  `IsStrawsonAntiAdditive.of_isAntiAdditive`: the classical property of an assertion that the
  defined values follow suffices.
* `isStrawsonAntiAdditive_iff`: Strawson anti-additivity is Strawson downward entailingness
  together with the Strawson form of Atlas's pseudo-anti-additivity.
* `isStrawsonDE_ofProp_iff`, `isStrawsonAntiAdditive_ofProp_iff`: without presuppositions the
  Strawson notions are the classical ones.
* `isStrawsonAntiAdditive_only`, `not_antitone_posExt_only`: *only* over a name is Strawson
  anti-additive and not classically downward entailing.
* `not_isStrawsonUE_only`, `not_isStrawsonUE_since`, `Desire.BestWorlds.not_isStrawsonUE_regret`,
  `Degree.not_isStrawsonUE_superlative`, `Conditional.not_isStrawsonUE_horizonCounterfactual`:
  none of the Strawson downward entailing operators is Strawson upward entailing as well.
* `Degree.isStrawsonAntiAdditive_superlative`,
  `Conditional.isStrawsonAntiAdditive_horizonCounterfactual`: the superlative in its class and the
  modal-horizon counterfactual in its antecedent are Strawson anti-additive, and neither is
  classically downward entailing.
* `Desire.BestWorlds.isStrawsonUE_want`, `Desire.BestWorlds.isStrawsonUE_glad`,
  `Desire.BestWorlds.not_isStrawsonDE_glad`, `Desire.BestWorlds.isStrawsonAntiAdditive_regret`:
  *want* and *glad* are Strawson upward entailing and *glad* is not Strawson downward entailing,
  while *sorry* is Strawson anti-additive.
* `Focus.Particles.isStrawsonDE_only`, `Focus.Particles.isStrawsonAntiAdditive_only_subset`,
  `Focus.Particles.isStrawsonDE_only_apply`: the propositional exclusive is Strawson downward
  entailing in its prejacent and, applied to an individual, in its predicate, on scales refining
  entailment; `Focus.Particles.not_isStrawsonDE_only_superset` fails it on the reversed scale.
* `only_eq_only_range`, `only_ne_only_range`: the name-based *only* is the exclusive over the
  alternatives the name generates exactly when no predication entails another's.

## Implementation notes

* Strawson entailment takes the presuppositions of premise and conclusion alike as premises, as
  in von Fintel's Strawson validity and Gajewski's own proofs, rather than the literal clause of
  Gajewski's cross-categorial definition at type `t`.
* `only` is von Fintel's name-based *only*, which excludes individuals; the propositional
  exclusive of Coppock and Beaver, which excludes alternative propositions, is
  `Focus.Particles.only`, and its Strawson facts hold with the alternatives held fixed, as von
  Fintel requires. `only` presupposes that `x` is `P`; Horn's presupposition that something is
  `P` gives the same Strawson facts, as von Fintel notes.
* *Want*, *glad* and *sorry* are the best-worlds entries of `Desire.BestWorlds`; following Heim,
  the factivity of *glad* and *sorry* is doxastic, and with suitable ordering sources *sorry* also
  covers *regret*, *amazed* and *surprised*. Von Fintel calls *glad* upward entailing; its
  presupposition that the domain contains non-`p` worlds can fail at a larger argument, so
  `Desire.BestWorlds.isStrawsonUE_glad` is the Strawson form he states for *want*.
* The other operators live with their owners, the superlative in `Degree.superlative` and the
  conditional in `Conditional.horizonCounterfactual`, and their Strawson facts are proved here,
  as are those of Iatridou's temporal *since*, defined here.

## References

* [strawson-1952]
* [von-fintel-1999]
* [gajewski-2005]
* [gajewski-2011]
* [coppock-beaver-2014]
* [atlas-1996]
* [horn-1996]
* [heim-1992]
* [heim-1999]
-/

@[expose] public section

namespace NaturalLogic

open Presupposition Trivalent

variable {α ι W D : Type*}

/-! ### Strawson monotonicity -/

section Preorder

variable [Preorder α] {f : α → W → SignType}

/-- An operator into trivalent propositions is Strawson downward entailing if `p ≤ q` makes `f q`
Strawson-entail `f p` ([von-fintel-1999]'s (14)). -/
def IsStrawsonDE (f : α → W → SignType) : Prop :=
  ∀ ⦃p q⦄, p ≤ q → strawsonEntails (f q) (f p)

/-- An operator into trivalent propositions is Strawson upward entailing if `p ≤ q` makes `f p`
Strawson-entail `f q`. -/
def IsStrawsonUE (f : α → W → SignType) : Prop :=
  ∀ ⦃p q⦄, p ≤ q → strawsonEntails (f p) (f q)

theorem isStrawsonDE_iff :
    IsStrawsonDE f ↔ ∀ ⦃p q⦄, p ≤ q → ∀ w, f p w ≠ 0 → f q w = 1 → f p w = 1 :=
  forall₂_congr fun _ _ ↦ imp_congr_right fun _ ↦ forall_congr' fun _ ↦
    ⟨fun h a b ↦ h b a, fun h a b ↦ h b a⟩

/-- An operator whose values, where defined, follow an antitone assertion is Strawson downward
entailing, whatever the presupposition. -/
theorem IsStrawsonDE.of_antitone {a : α → W → Prop} (h : Antitone a)
    (hf : ∀ p w, f p w ≠ 0 → (f p w = 1 ↔ a p w)) : IsStrawsonDE f :=
  fun _ _ hpq w hq hp ↦ (hf _ w hp).2 (h hpq w ((hf _ w (by simp [hq])).1 hq))

/-- An operator whose values, where defined, follow a monotone assertion is Strawson upward
entailing, whatever the presupposition. -/
theorem IsStrawsonUE.of_monotone {a : α → W → Prop} (h : Monotone a)
    (hf : ∀ p w, f p w ≠ 0 → (f p w = 1 ↔ a p w)) : IsStrawsonUE f :=
  fun _ _ hpq w hp hq ↦ (hf _ w hq).2 (h hpq w ((hf _ w (by simp [hp])).1 hp))

theorem IsStrawsonDE.of_antitone_posExt (h : Antitone fun p ↦ posExt (f p)) : IsStrawsonDE f :=
  fun _ _ hpq _ hq _ ↦ h hpq hq

open Classical in
/-- Without presuppositions, Strawson downward entailingness is antitonicity. -/
theorem isStrawsonDE_ofProp_iff {g : α → W → Prop} :
    IsStrawsonDE (fun p w ↦ SignType.ofProp (g p w)) ↔ Antitone g :=
  forall₂_congr fun _ _ ↦ imp_congr_right fun _ ↦ by simp [strawsonEntails, Pi.le_def]

open Classical in
theorem isStrawsonUE_ofProp_iff {g : α → W → Prop} :
    IsStrawsonUE (fun p w ↦ SignType.ofProp (g p w)) ↔ Monotone g :=
  forall₂_congr fun _ _ ↦ imp_congr_right fun _ ↦ by simp [strawsonEntails, Pi.le_def]

theorem not_antitone_posExt {p q : α} {w : W} (hpq : p ≤ q) (hq : f q w = 1) (hp : f p w = 0) :
    ¬ Antitone fun p ↦ posExt (f p) :=
  fun h ↦ by simpa [hp] using h hpq hq

theorem not_isStrawsonUE {p q : α} {w : W} (hpq : p ≤ q) (hp : f p w = 1) (hq : f q w = -1) :
    ¬ IsStrawsonUE f :=
  fun h ↦ by simpa [hq] using h hpq w hp (by simp [hq])

end Preorder

/-! ### Strawson anti-additivity -/

section SemilatticeSup

variable [SemilatticeSup α] {f : α → W → SignType}

/-- An operator into trivalent propositions is Strawson anti-additive if `f (p ⊔ q)` is Strawson
equivalent to `f p` conjoined with `f q` ([gajewski-2011]'s (36)), the conjunction being the
classical one, defined where both conjuncts are. -/
def IsStrawsonAntiAdditive (f : α → W → SignType) : Prop :=
  ∀ p q, strawsonEntails (f (p ⊔ q)) (fun w ↦ (f p w).meetWeak (f q w)) ∧
    strawsonEntails (fun w ↦ (f p w).meetWeak (f q w)) (f (p ⊔ q))

/-- An operator whose values, where defined, follow an anti-additive assertion is Strawson
anti-additive, whatever the presupposition. -/
theorem IsStrawsonAntiAdditive.of_isAntiAdditive {a : α → W → Prop} (h : IsAntiAdditive a)
    (hf : ∀ p w, f p w ≠ 0 → (f p w = 1 ↔ a p w)) : IsStrawsonAntiAdditive f := by
  refine fun p q ↦ ⟨fun w h₁ h₂ ↦ ?_, fun w h₁ h₂ ↦ ?_⟩
  · have ha := (hf _ w (by simp [h₁])).1 h₁
    rw [h p q] at ha
    simp only [ne_eq, SignType.meetWeak_eq_zero_iff, not_or] at h₂
    simp [(hf p w h₂.1).2 ha.1, (hf q w h₂.2).2 ha.2]
  · simp only [SignType.meetWeak_eq_one_iff] at h₁
    refine (hf _ w h₂).2 ?_
    rw [h p q]
    exact ⟨(hf p w (by simp [h₁.1])).1 h₁.1, (hf q w (by simp [h₁.2])).1 h₁.2⟩

theorem IsStrawsonAntiAdditive.isStrawsonDE (h : IsStrawsonAntiAdditive f) : IsStrawsonDE f :=
  fun p q hpq w hq hp ↦ by
    rw [← sup_eq_right.2 hpq] at hq
    have := (h p q).1 w hq
    by_cases hq' : f q w = 0
    · simp_all
    · simp_all

/-- Strawson anti-additivity is Strawson downward entailingness plus the Strawson form of
[atlas-1996]'s pseudo-anti-additivity ([von-fintel-1999]'s (25); [gajewski-2011], Appendix 1). -/
theorem isStrawsonAntiAdditive_iff :
    IsStrawsonAntiAdditive f ↔
      IsStrawsonDE f ∧ ∀ p q, strawsonEntails (fun w ↦ (f p w).meetWeak (f q w)) (f (p ⊔ q)) := by
  refine ⟨fun h ↦ ⟨h.isStrawsonDE, fun p q ↦ (h p q).2⟩,
    fun ⟨h, h'⟩ p q ↦ ⟨fun w hs hpq ↦ ?_, h' p q⟩⟩
  simp only [ne_eq, SignType.meetWeak_eq_zero_iff, not_or] at hpq
  simp [h le_sup_left w hs hpq.1, h le_sup_right w hs hpq.2]

open Classical in
/-- Without presuppositions, Strawson anti-additivity is anti-additivity. -/
theorem isStrawsonAntiAdditive_ofProp_iff {g : α → W → Prop} :
    IsStrawsonAntiAdditive (fun p w ↦ SignType.ofProp (g p w)) ↔ IsAntiAdditive g := by
  refine forall₂_congr fun p q ↦ ?_
  simp only [strawsonEntails, SignType.ofProp_eq_one_iff, ne_eq, SignType.ofProp_ne_zero,
    not_false_eq_true, forall_const, SignType.meetWeak_eq_one_iff, SignType.meetWeak_eq_zero_iff,
    or_self, funext_iff, Pi.inf_apply, inf_Prop_eq]
  exact ⟨fun h w ↦ propext ⟨h.1 w, h.2 w⟩, fun h ↦ ⟨fun w ↦ (h w).mp, fun w ↦ (h w).mpr⟩⟩

end SemilatticeSup

/-! ### *Only* -/

section Only

variable (x : ι) (P : ι → Set W)

open Classical in
/-- *Only x is P* presupposes that `x` is `P` and asserts that nothing else is
([von-fintel-1999]'s (15)). -/
noncomputable def only : W → SignType :=
  (P x).indicator fun w ↦ SignType.ofProp (∀ y, y ≠ x → w ∉ P y)

variable {x P} in
private theorem only_eq_one_iff {w : W} (h : only x P w ≠ 0) :
    only x P w = 1 ↔ ∀ y, y ≠ x → w ∉ P y := by
  by_cases hw : w ∈ P x <;> simp_all [only]

theorem isStrawsonAntiAdditive_only : IsStrawsonAntiAdditive (only (W := W) x) :=
  .of_isAntiAdditive (a := fun P w ↦ ∀ y, y ≠ x → w ∉ P y)
    (fun _ _ ↦ funext fun _ ↦ propext <| by
      simp only [Pi.sup_apply, Pi.inf_apply, inf_Prop_eq, Set.sup_eq_union, Set.mem_union,
        not_or, imp_and, forall_and])
    fun _ _ ↦ only_eq_one_iff

theorem isStrawsonDE_only : IsStrawsonDE (only (W := W) x) :=
  (isStrawsonAntiAdditive_only x).isStrawsonDE

/-- *Only John ate vegetables* does not classically entail *only John ate kale*, whose
presupposition may fail ([von-fintel-1999]'s (11)). -/
theorem not_antitone_posExt_only :
    ¬ Antitone fun P : Bool → Set Unit ↦ posExt (only true P) :=
  not_antitone_posExt (p := ⊥) (q := fun y ↦ {_u | y = true}) (w := ()) bot_le
    (by simp [only]) (by simp [only])

/-- *Only John smokes* does not Strawson-entail *only John smokes or drinks*, which is defined and
false when someone else drinks, so *only* is not upward entailing. -/
theorem not_isStrawsonUE_only : ¬ IsStrawsonUE (only (W := Unit) true) :=
  not_isStrawsonUE (p := fun y ↦ {_u | y = true}) (q := ⊤) (w := ()) le_top
    (by simp [only]) (by simp [only])

/-- If the prejacent entails no other individual's predication, name-based *only* equals
`Focus.Particles.only` over the alternatives the name generates ([coppock-beaver-2014]'s (93)). -/
theorem only_eq_only_range (hP : ∀ y, P x ⊆ P y → y = x) :
    only x P = Focus.Particles.only (· ⊆ ·) (Set.range P) (P x) := by
  funext w
  have hx := Focus.Particles.atLeast_subset_eq (Set.mem_range_self (f := P) x)
  refine SignType.eq_of_eq_zero_iff_of_eq_one_iff (by simp [only, hx]) ?_
  simp only [only, Focus.Particles.only_eq_one_iff, hx, indicator_apply_eq_one_iff,
    SignType.ofProp_eq_one_iff, Focus.Particles.mem_atMost, Set.forall_mem_range]
  refine and_congr_right fun _ ↦ ⟨fun h y hw ↦ ?_, fun h y hyx hw ↦ hyx (hP y (h y hw))⟩
  by_cases hyx : y = x
  · exact hyx ▸ subset_rfl
  · exact absurd hw (h y hyx)

/-- Without that condition the two come apart, since two individuals with the same predication
are one alternative, entailed by the prejacent, for the exclusive but two individuals for the
name-based *only*. -/
theorem only_ne_only_range :
    only true (fun _ : Bool ↦ (.univ : Set Unit)) ≠
      Focus.Particles.only (· ⊆ ·) (Set.range fun _ : Bool ↦ (.univ : Set Unit)) .univ := by
  intro h
  have h0 : Focus.Particles.only (· ⊆ ·) (Set.range fun _ : Bool ↦ (.univ : Set Unit)) .univ () =
      1 :=
    Focus.Particles.only_eq_one_iff.2 ⟨⟨.univ, ⟨true, rfl⟩, trivial, subset_rfl⟩,
      fun q ⟨_, hq⟩ _ ↦ hq ▸ subset_rfl⟩
  rw [← h] at h0
  simp [only] at h0

end Only

/-! ### Temporal *since* -/

section Since

variable {T : Type*} [LinearOrder T] (ago : T → T)

open Classical in
/-- *It has been five years since p* presupposes that `p` held at the time `ago t` five years
before the evaluation time `t` and asserts that it has not held since ([von-fintel-1999], after
Iatridou). -/
noncomputable def since (p : Set T) : T → SignType :=
  {t | ago t ∈ p}.indicator fun t ↦ SignType.ofProp (Disjoint (Set.Ioc (ago t) t) p)

theorem isStrawsonAntiAdditive_since : IsStrawsonAntiAdditive (since ago) :=
  .of_isAntiAdditive (a := fun p t ↦ Disjoint (Set.Ioc (ago t) t) p)
    (fun _ _ ↦ funext fun _ ↦ propext Set.disjoint_union_right)
    fun p t h ↦ by by_cases ht : ago t ∈ p <;> simp_all [since]

theorem isStrawsonDE_since : IsStrawsonDE (since ago) :=
  (isStrawsonAntiAdditive_since ago).isStrawsonDE

theorem not_antitone_posExt_since :
    ¬ Antitone fun p : Set ℤ ↦ posExt (since (· - 5) p) :=
  not_antitone_posExt (p := ∅) (q := {-5}) (w := 0) (Set.empty_subset _)
    (by simp [since, Set.disjoint_singleton_right]) (by simp [since])

/-- *It's been five years since I saw an eagle* does not Strawson-entail *it's been five years
since I saw a bird*, defined and false when a sparrow was seen since. -/
theorem not_isStrawsonUE_since : ¬ IsStrawsonUE (since (T := ℤ) (· - 5)) :=
  not_isStrawsonUE (p := {-5}) (q := .univ) (w := 0) (Set.subset_univ _)
    (by simp [since, Set.disjoint_singleton_right])
    (by simpa [since] using Set.nonempty_iff_ne_empty.1 ⟨0, by simp⟩)

end Since

end NaturalLogic

/-! ### The propositional exclusive -/

namespace Focus.Particles

open NaturalLogic Trivalent

variable {W ι : Type*} {S : Set W → Set W → Prop} (C : Set (Set W))

/-- On a scale refining entailment, *only* is Strawson downward entailing in its prejacent with
the alternatives held fixed ([von-fintel-1999], §3.4; [coppock-beaver-2014], fn. 22). -/
theorem isStrawsonDE_only (hS : ∀ ⦃p q r⦄, p ⊆ q → S q r → S p r) : IsStrawsonDE (only S C) :=
  .of_antitone (a := fun p w ↦ w ∈ atMost S C p) (fun _ _ hpq ↦ antitone_atMost hS hpq)
    fun _ _ h ↦ by simp_all

/-- On the entailment scale *only* is Strawson anti-additive in its prejacent. -/
theorem isStrawsonAntiAdditive_only_subset : IsStrawsonAntiAdditive (only (· ⊆ ·) C) :=
  .of_isAntiAdditive (a := fun p w ↦ w ∈ atMost (· ⊆ ·) C p)
    (fun p q ↦ funext fun w ↦ propext <| by
      show w ∈ Exhaustification.excludes C (p ∪ q) ↔
        w ∈ Exhaustification.excludes C p ∧ w ∈ Exhaustification.excludes C q
      rw [Exhaustification.excludes_union]
      exact Iff.rfl)
    fun _ _ h ↦ by simp_all

theorem isStrawsonDE_only_subset : IsStrawsonDE (only (· ⊆ ·) C) :=
  (isStrawsonAntiAdditive_only_subset C).isStrawsonDE

/-- *Only* applied to the predication of an individual is Strawson downward entailing in the
predicate, so it licenses NPIs in the verb phrase ([coppock-beaver-2014]'s (93)). -/
theorem isStrawsonDE_only_apply (hS : ∀ ⦃p q r⦄, p ⊆ q → S q r → S p r) (x : ι) :
    IsStrawsonDE fun P : ι → Set W ↦ only S C (P x) :=
  .of_antitone (a := fun P w ↦ w ∈ atMost S C (P x)) (fun _ _ hPQ ↦ antitone_atMost hS (hPQ x))
    fun _ _ h ↦ by simp_all

/-- *There only was precipitation in Medford* does not classically entail *there only was rain in
Medford*, whose presupposition, the premise [von-fintel-1999]'s (67) adds, may fail. -/
theorem not_antitone_posExt_only_subset :
    ¬ Antitone fun p : Set Bool ↦ posExt (only (· ⊆ ·) {{true}, .univ} p) :=
  not_antitone_posExt (p := {true}) (q := .univ) (w := false) (Set.subset_univ _)
    (only_eq_one_iff.2 ⟨⟨.univ, by simp, trivial, subset_rfl⟩, fun q hq hw ↦ by
      rcases hq with rfl | rfl
      exacts [absurd hw (by simp), subset_rfl]⟩)
    (only_eq_zero_iff.2 fun ⟨_, _, hw, hsub⟩ ↦ by simpa using hsub hw)

/-- On a scale ranked by reverse entailment, *only* is not Strawson downward entailing in its
prejacent, as the footnote claims ([coppock-beaver-2014], fn. 22). -/
theorem not_isStrawsonDE_only_superset :
    ¬ IsStrawsonDE (only (· ⊇ ·) ({{true}, .univ} : Set (Set Bool))) := fun h ↦ by
  have := h (p := {true}) (q := .univ) (Set.subset_univ _) true
    (only_eq_one_iff.2 ⟨⟨.univ, by simp, trivial, subset_rfl⟩, fun _ _ _ ↦ Set.subset_univ _⟩)
    (by rw [Ne, only_eq_zero_iff, not_not]; exact ⟨{true}, by simp, rfl, subset_rfl⟩)
  exact absurd ((only_eq_one_iff.1 this).2 .univ (by simp) trivial (Set.mem_univ false))
    (by simp)

end Focus.Particles

/-! ### *Want*, *glad* and *sorry* -/

namespace Desire.BestWorlds

open Modality NaturalLogic Trivalent

variable {W : Type*} (dox base : W → Set W) (g : W → Set (W → Prop))

/-- *Want* is Strawson upward entailing in its complement ([von-fintel-1999], §3.2). -/
theorem isStrawsonUE_want : IsStrawsonUE (want base g) :=
  .of_monotone (a := fun p w ↦ Want (g w) (base w) p) (fun _ _ h _ hw ↦ hw.trans h)
    fun _ _ h ↦ by simp_all

theorem isStrawsonUE_glad : IsStrawsonUE (glad dox base g) :=
  .of_monotone (a := fun p w ↦ Want (g w) (base w) p) (fun _ _ h _ hw ↦ hw.trans h)
    fun _ _ h ↦ by simp_all [glad]

/-- *Glad* is not Strawson downward entailing ([von-fintel-1999], §3.3). -/
theorem not_isStrawsonDE_glad :
    ¬ IsStrawsonDE (glad (fun _ : Fin 3 ↦ {0}) (fun _ ↦ .univ) (fun _ ↦ {(· = 1)})) := by
  have hb : (premisePreorder {(· = 1)}).minimals (Set.univ : Set (Fin 3)) = {1} := by
    rw [Preorder.minimals_ofCriteria_eq ⟨1, Set.mem_univ _, by simp⟩]
    ext
    simp
  intro h
  have := h (p := {0}) (q := {0, 1}) (by simp) 0
  simp [glad, Want, IsContingent, hb] at this
  exact this ⟨2, by simp⟩ ⟨1, by simp⟩

/-- *Sorry* is Strawson anti-additive in its complement, since wanting a disjunction false is
wanting each disjunct false. -/
theorem isStrawsonAntiAdditive_regret : IsStrawsonAntiAdditive (regret dox base g) :=
  .of_isAntiAdditive (a := fun p w ↦ Want (g w) (base w) pᶜ)
    (fun p q ↦ funext fun w ↦ propext <| by
      show Want (g w) (base w) (p ∪ q)ᶜ ↔ Want (g w) (base w) pᶜ ∧ Want (g w) (base w) qᶜ
      rw [Set.compl_union]
      exact want_inter_iff)
    fun _ _ h ↦ by simp_all [regret]

theorem isStrawsonDE_regret : IsStrawsonDE (regret dox base g) :=
  (isStrawsonAntiAdditive_regret dox base g).isStrawsonDE

/-- *Sorry that Robin bought a car* does not classically entail *sorry that Robin bought a Honda
Civic* ([von-fintel-1999]'s (30)). -/
theorem not_antitone_posExt_regret :
    ¬ Antitone fun p : Set Bool ↦
      posExt (regret (fun _ ↦ {true}) (fun _ ↦ .univ) (fun _ ↦ {(· = false)}) p) := by
  have hb : (premisePreorder {(· = false)}).minimals ({false, true} : Set Bool) = {false} := by
    rw [Preorder.minimals_ofCriteria_eq ⟨false, by simp, by simp⟩]
    ext
    simp
  exact not_antitone_posExt (p := ∅) (q := {true}) (w := true) (Set.empty_subset _)
    (by simp [regret, Want, IsContingent, hb]) (by simp [regret])

/-- *Sorry that Robin bought a Civic* does not Strawson-entail *sorry that Robin bought a Civic or
a Golf*, defined and false when the subject prefers the Golf. The subject believes world `0` and
prefers world `1`. -/
theorem not_isStrawsonUE_regret :
    ¬ IsStrawsonUE (regret (fun _ : Fin 3 ↦ {0}) (fun _ ↦ .univ) (fun _ ↦ {(· = 1)})) := by
  have hb : (premisePreorder {(· = 1)}).minimals (Set.univ : Set (Fin 3)) = {1} := by
    rw [Preorder.minimals_ofCriteria_eq ⟨1, Set.mem_univ _, by simp⟩]
    ext
    simp
  exact not_isStrawsonUE (p := {0}) (q := {0, 1}) (w := 0) (by simp)
    (by simp [regret, Want, IsContingent, hb])
    (by simp [regret, Want, IsContingent, hb]; exact ⟨2, by simp⟩)

end Desire.BestWorlds

/-! ### Superlatives -/

namespace Degree

open NaturalLogic Trivalent

variable {α D W : Type*} [Preorder D] (μ : α → D) (x : α)

/-- The superlative is Strawson anti-additive in its comparison class. -/
theorem isStrawsonAntiAdditive_superlative :
    IsStrawsonAntiAdditive (superlative (W := W) μ · x) :=
  .of_isAntiAdditive (isAntiAdditive_superlative_assertion μ x) fun _ _ h ↦ by simp_all

theorem isStrawsonDE_superlative : IsStrawsonDE (superlative (W := W) μ · x) :=
  (isStrawsonAntiAdditive_superlative μ x).isStrawsonDE

/-- *Emma is the tallest girl in her class* does not classically entail its restriction to girls who
have learned the alphabet ([von-fintel-1999]'s (76)). -/
theorem not_antitone_posExt_superlative :
    ¬ Antitone fun C : Unit → Set Unit ↦ posExt (superlative (fun _ : Unit ↦ (0 : ℕ)) C ()) :=
  not_antitone_posExt (p := ⊥) (q := fun _ ↦ .univ) (w := ()) bot_le (by simp) (by simp)

/-- *Emma is the tallest girl to have learned the alphabet* does not Strawson-entail *Emma is the
tallest girl*, defined and false when a taller girl has not learned it. -/
theorem not_isStrawsonUE_superlative :
    ¬ IsStrawsonUE (superlative (W := Unit) (fun _ : Bool ↦ (0 : ℕ)) · true) :=
  not_isStrawsonUE (p := fun _ ↦ {true}) (q := fun _ ↦ .univ) (w := ())
    (fun _ ↦ Set.subset_univ _) (by simp) (by simp [superlative])

end Degree

/-! ### Conditional antecedents -/

namespace Conditional

open NaturalLogic Trivalent

variable {I W : Type*} (horizon : I → Set W) (q : Set W)

/-- The modal-horizon counterfactual is Strawson anti-additive in its antecedent ([gajewski-2011],
Appendix 1). -/
theorem isStrawsonAntiAdditive_horizonCounterfactual :
    IsStrawsonAntiAdditive (horizonCounterfactual horizon · q) :=
  .of_isAntiAdditive (a := fun p i ↦ i ∈ strictImp horizon p q)
    (fun p p' ↦ funext fun i ↦ propext <| by
      show i ∈ strictImp horizon (p ∪ p') q ↔ i ∈ strictImp horizon p q ∧ i ∈ strictImp horizon p' q
      rw [strictImp_union_left]
      exact Iff.rfl)
    fun _ _ h ↦ by simp_all [mem_strictImp]

theorem isStrawsonDE_horizonCounterfactual :
    IsStrawsonDE (horizonCounterfactual horizon · q) :=
  (isStrawsonAntiAdditive_horizonCounterfactual horizon q).isStrawsonDE

/-- Strengthening the antecedent is not classically valid, since a strengthened antecedent can
fall outside the horizon ([von-fintel-1999], §4.3). -/
theorem not_antitone_posExt_horizonCounterfactual :
    ¬ Antitone fun p : Set Unit ↦
      posExt (horizonCounterfactual (fun _ : Unit ↦ (.univ : Set Unit)) p .univ) :=
  not_antitone_posExt (p := ∅) (q := .univ) (w := ()) (Set.empty_subset _) (by simp) (by simp)

/-- Weakening the antecedent is not Strawson valid either, since the weaker antecedent can admit
worlds the consequent excludes. -/
theorem not_isStrawsonUE_horizonCounterfactual :
    ¬ IsStrawsonUE fun p : Set Bool ↦
      horizonCounterfactual (fun _ : Unit ↦ (.univ : Set Bool)) p {true} :=
  not_isStrawsonUE (p := {true}) (q := .univ) (w := ()) (Set.subset_univ _) (by simp)
    (by simp [Set.subset_def])

end Conditional
