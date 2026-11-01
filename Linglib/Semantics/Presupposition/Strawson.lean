module

public import Linglib.Logic.Natural.Additivity
public import Linglib.Semantics.Presupposition.Basic

/-!
# Strawson monotonicity

This file defines monotonicity under Strawson entailment for operators into trivalent
propositions. An operator is Strawson downward entailing when shrinking its argument gives a
conclusion that the original Strawson-entails, the inference being checked only where the
presuppositions involved hold. Von Fintel introduces the notion to keep the Fauconnier–Ladusaw
theory of negative polarity licensing for operators that are not downward entailing, and Gajewski
adds Strawson anti-additivity. Each property holds as soon as the operator's values, where defined,
[follow an assertion with the classical property](##Presupposition.IsStrawsonDE.of_antitone),
whatever the presupposition, and [without presuppositions the Strawson notions are the classical
ones](##Presupposition.isStrawsonDE_ofProp_iff).

## Implementation notes

Strawson entailment takes the presuppositions of premise and conclusion alike as premises, as in
von Fintel's Strawson validity and Gajewski's own proofs, rather than the literal clause of
Gajewski's cross-categorial definition at type `t`.

## References

* [strawson-1952]
* [von-fintel-1999]
* [gajewski-2005]
* [gajewski-2011]
* [atlas-1996]
-/

@[expose] public section

namespace Presupposition

open NaturalLogic Trivalent

variable {α W : Type*}

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

theorem IsStrawsonDE.of_antitone_posSupport (h : Antitone fun p ↦ posSupport (f p)) :
    IsStrawsonDE f :=
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

theorem not_antitone_posSupport {p q : α} {w : W} (hpq : p ≤ q) (hq : f q w = 1) (hp : f p w = 0) :
    ¬ Antitone fun p ↦ posSupport (f p) :=
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

end Presupposition
