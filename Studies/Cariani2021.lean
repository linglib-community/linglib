/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Studies.CarianiSantorio2018
public import Studies.Condoravdi2002
public import Linglib.Semantics.Modality.BranchingTime
public import Linglib.Semantics.Tense.Quantificational
public import Linglib.Logic.Modal.Basic

/-!
# Cariani (2021): *The Modal Future*

This file formalizes chapters 1, 3, 5 to 8 and 11 of [cariani-2021]: the symmetric paradigm, on
which *will* is Prior's future tense, against the selection semantics of Cariani and Santorio,
on which *will* is a modal that selects a world from its modal base.

## Main results

* `forall_imp_linearWill_linearWas_iff`, `kt_fb`, `kt_bf`: the symmetric paradigm (ch. 1).
* `displacesWorlds_hybrid_iff`, `hybrid_iff_linearWill`: *will* as a modal (§3.1, §7.2).
* `pres_woll_frame_stative_iff`, `pres_woll_frame_eventive_iff`: present-directed *will* (§7.7).
* `forall_hybrid_or_not_iff`, `forall_not_hybrid_and_not_iff`: the hybrid semantics (ch. 5).
* `not_accepts_will_and_might_not`, `not_will_and_might_not_will`: future-might contradictions
  and Kissine's argument (ch. 6).
* `pres_woll_neg_iff`, `not_pres_WOLL_and_neg`: selectional and universal WOLL (ch. 7).
* `willIf_willIf`, `willIf_univ_eq_selectionConditional`: will-conditionals (ch. 8).
* `indeterminate_sat`, `not_exists_convergent_centered_trl`: the open future (ch. 11).

## Implementation notes

* *Will* along a modal base is `SelectionFunction.modal`; an information state is a set of
  worlds.
* The symmetric operators are the substrate's quantificational tenses. *Will* is PRES + WOLL as
  in `Condoravdi2002`, whose `frame` at the present is *by now*.

## TODO

* The text puts *by now* over *will* (p. 129), but its truth conditions for (10) and (11) need
  *by now* under WOLL (`pres_frame_now_iff`).
* Modal subordination and acquaintance inferences (§3.4, §3.5); §8.6 and §8.8.

## References

* [cariani-2021]
* [prior-1967]
* [huddleston-pullum-2002]
* [cariani-santorio-2018]
* [kissine-2008]
* [condoravdi-2002]
* [belnap-green-1994]
-/

@[expose] public section

namespace Cariani2021

open Conditional ModalLogic SelectionFunction
open scoped SetRel

/-! ### The symmetric paradigm

*Was* and *will* as Prior's quantifiers over earlier and later times (p. 8), the substrate's
quantificational tenses. -/

section Symmetric

open scoped Denotes

/-- Linear symmetric *was* (p. 8): `A` held at some earlier time. -/
def linearWas {T : Type*} [LinearOrder T] (A : T → Prop) : T → Prop :=
  ◇[Tense.toSetRel ⟦Tense.past⟧] A

/-- Linear symmetric *will* (p. 8): `A` holds at some later time. -/
def linearWill {T : Type*} [LinearOrder T] (A : T → Prop) : T → Prop :=
  ◇[Tense.toSetRel ⟦Tense.future⟧] A

variable {T : Type*} [LinearOrder T] {A : T → Prop} {t : T}

@[simp] theorem linearWas_iff : linearWas A t ↔ ∃ u < t, A u := Tense.diamond_toSetRel_past

@[simp] theorem linearWill_iff : linearWill A t ↔ ∃ u > t, A u := Tense.diamond_toSetRel_future

/-- *Will* and *was* are mirror images: *will* is *was* on the reversed time line (p. 10). -/
theorem linearWill_iff_linearWas_toDual :
    linearWill A t ↔ linearWas (T := Tᵒᵈ) (A ∘ OrderDual.ofDual) (OrderDual.toDual t) := by
  simp only [linearWill_iff, linearWas_iff]
  exact ⟨fun ⟨u, hu, h⟩ ↦ ⟨OrderDual.toDual u, hu, h⟩, fun ⟨u, hu, h⟩ ↦ ⟨u.ofDual, hu, h⟩⟩

/-- (1a) is valid: a future of a future is a future, by the composition of the future cell with
itself. -/
theorem linearWill_linearWill (h : linearWill (linearWill A) t) : linearWill A t := by
  have := Tense.diamond_diamond_toSetRel h
  rwa [Tense.comp_future_future] at this

/-- (1b) is invalid: what is true now need not be true at a later time. -/
theorem not_forall_imp_linearWill : ¬ ∀ (A : ℤ → Prop) (t : ℤ), A t → linearWill A t :=
  fun h ↦ let ⟨_, hu, hA⟩ := linearWill_iff.1 (h (· = 0) 0 rfl); lt_irrefl (0 : ℤ) (hA ▸ hu)

/-- (1c) is valid on a time line exactly when it has no last moment (p. 9). -/
theorem forall_imp_linearWill_linearWas_iff :
    (∀ (A : T → Prop) (t : T), A t → linearWill (linearWas A) t) ↔ NoMaxOrder T := by
  refine ⟨fun h ↦ ⟨fun t ↦ ?_⟩, fun _ A t hA ↦ ?_⟩
  · obtain ⟨u, hu, -⟩ := linearWill_iff.1 (h (· = t) t rfl)
    exact ⟨u, hu⟩
  · obtain ⟨u, hu⟩ := exists_gt t
    exact linearWill_iff.2 ⟨u, hu, linearWas_iff.2 ⟨t, hu, hA⟩⟩

/-- (1d) is valid on a time line exactly when it has no first moment (p. 9). -/
theorem forall_imp_linearWas_linearWill_iff :
    (∀ (A : T → Prop) (t : T), A t → linearWas (linearWill A) t) ↔ NoMinOrder T := by
  refine ⟨fun h ↦ ⟨fun t ↦ ?_⟩, fun _ A t hA ↦ ?_⟩
  · obtain ⟨u, hu, -⟩ := linearWas_iff.1 (h (· = t) t rfl)
    exact ⟨u, hu⟩
  · obtain ⟨u, hu⟩ := exists_lt t
    exact linearWas_iff.2 ⟨u, hu, linearWill_iff.2 ⟨t, hu, hA⟩⟩

/-- (2a): given a future, what is true will have been true (p. 10). -/
theorem linearWill_linearWas (hA : A t) (h : linearWill (fun _ ↦ True) t) :
    linearWill (linearWas A) t :=
  let ⟨u, hu, _⟩ := linearWill_iff.1 h
  linearWill_iff.2 ⟨u, hu, linearWas_iff.2 ⟨t, hu, hA⟩⟩

/-- (2b): given a past, what is true was going to be true (p. 10). -/
theorem linearWas_linearWill (hA : A t) (h : linearWas (fun _ ↦ True) t) :
    linearWas (linearWill A) t :=
  let ⟨u, hu, _⟩ := linearWas_iff.1 h
  linearWas_iff.2 ⟨u, hu, linearWill_iff.2 ⟨t, hu, hA⟩⟩

/-- The `K_t` axiom FB, *A ⊃ always in the future, was A*, is the unit of the past-future adjunction
(p. 17). -/
theorem kt_fb : A ≤ □[Tense.toSetRel ⟦Tense.future⟧] (linearWas A) :=
  Tense.diamond_past_box_future_gc.le_u_l A

/-- `K_t`'s BF, *A ⊃ always in the past, will A* (p. 17). -/
theorem kt_bf : A ≤ □[Tense.toSetRel ⟦Tense.past⟧] (linearWill A) :=
  Tense.diamond_future_box_past_gc.le_u_l A

end Symmetric

/-! ### The hybrid semantics

The hybrid semantics of §5.2 (p. 80) evaluates the prejacent of *will* at the selected world at
some later time. It is possibility along an index relation that is serial wherever a later time
exists and functional only where at most one does, so it validates excluded middle and loses
non-contradiction and Negation Swap (p. 83), the failure of scopelessness for which chapter 7
rejects it (p. 117). -/

section Hybrid

variable {W T : Type*} [LT T] (s : SelectionFunction W) (H : Set W)

/-- The index relation of the hybrid semantics relates `(w, t)` to the world selected from `H`
at each later time. -/
def hybridRel : SetRel (W × T) (W × T) := {p | p.2.1 = s.sel p.1.1 H ∧ p.1.2 < p.2.2}

/-- Hybrid *will*, possibility along `hybridRel`, holds of `A` at `(w, t)` when `A` holds at the
world selected from `H` at some later time. -/
def hybrid (A : W × T → Prop) : W × T → Prop := ◇[hybridRel s H] A

variable {s H}

theorem exists_hybridRel_iff {i : W × T} : (∃ j, i ~[hybridRel s H] j) ↔ ∃ u, i.2 < u :=
  ⟨fun ⟨j, _, hj⟩ ↦ ⟨j.2, hj⟩, fun ⟨u, hu⟩ ↦ ⟨(s.sel i.1 H, u), rfl, hu⟩⟩

/-- The hybrid semantics validates excluded middle at an index exactly when a later time
exists. -/
theorem forall_hybrid_or_not_iff {i : W × T} :
    (∀ A : W × T → Prop, hybrid s H A i ∨ hybrid s H (fun j ↦ ¬ A j) i) ↔ ∃ u, i.2 < u :=
  diamond_or_diamond_not_at_iff.trans exists_hybridRel_iff

/-- The hybrid semantics validates non-contradiction at an index exactly when at most one later
time exists. -/
theorem forall_not_hybrid_and_not_iff {i : W × T} :
    (∀ A : W × T → Prop, ¬ (hybrid s H A i ∧ hybrid s H (fun j ↦ ¬ A j) i)) ↔
      ∀ ⦃u⦄, i.2 < u → ∀ ⦃u'⦄, i.2 < u' → u = u' := by
  refine (not_diamond_and_diamond_not_at_iff (R := hybridRel s H) (w := i)).trans
    ⟨fun h u hu u' hu' ↦ congrArg Prod.snd
      (h (v := (s.sel i.1 H, u)) ⟨rfl, hu⟩ (u := (s.sel i.1 H, u')) ⟨rfl, hu'⟩),
      fun h _ ⟨hw, hu⟩ _ ⟨hw', hu'⟩ ↦ Prod.ext (hw.trans hw'.symm) (h hu hu')⟩

/-- In the tacos model, *I will have tacos* and *I will not have tacos* are both true on Monday (p.
83). -/
theorem hybrid_tacos (s : SelectionFunction Unit) :
    hybrid s .univ (fun j : Unit × ℕ ↦ j.2 = 1) ((), 0) ∧
      hybrid s .univ (fun j : Unit × ℕ ↦ ¬ j.2 = 1) ((), 0) :=
  ⟨⟨((), 1), ⟨rfl, Nat.one_pos⟩, rfl⟩, ⟨((), 2), ⟨rfl, Nat.two_pos⟩, by decide⟩⟩

end Hybrid

/-! ### What makes *will* a modal

An expression is a modal when its rule intervenes on the world of evaluation (§3.1, p. 43). -/

section Modal

variable {W T : Type*} [LinearOrder T] {s : SelectionFunction W} {H : Set W}

/-- An operator on propositions over world-time indices displaces worlds when it tells apart two
propositions that agree at the world of evaluation. -/
def DisplacesWorlds (O : (W × T → Prop) → W × T → Prop) : Prop :=
  ∃ (A B : W × T → Prop) (i : W × T), (∀ u, A (i.1, u) ↔ B (i.1, u)) ∧ O A i ∧ ¬ O B i

theorem not_displacesWorlds_linearWill :
    ¬ DisplacesWorlds fun (A : W × T → Prop) i ↦ linearWill (fun u ↦ A (i.1, u)) i.2 := by
  rintro ⟨A, B, i, hAB, hA, hB⟩
  obtain ⟨u, hu, h⟩ := linearWill_iff.1 hA
  exact hB (linearWill_iff.2 ⟨u, hu, (hAB u).1 h⟩)

/-- Hybrid *will* displaces worlds exactly when, somewhere with a later time, selection moves off
the world of evaluation. -/
theorem displacesWorlds_hybrid_iff :
    DisplacesWorlds (T := T) (hybrid s H) ↔ ∃ (w : W) (t u : T), t < u ∧ s.sel w H ≠ w := by
  constructor
  · rintro ⟨A, B, ⟨w, t⟩, hAB, ⟨j, ⟨hj, ht⟩, hA⟩, hB⟩
    refine ⟨w, t, j.2, ht, fun hsel ↦ hB ⟨j, ⟨hj, ht⟩, ?_⟩⟩
    obtain ⟨jw, ju⟩ := j
    simp only at hj
    subst hj
    rw [hsel] at hA ⊢
    exact (hAB ju).1 hA
  · rintro ⟨w, t, u, hu, hne⟩
    exact ⟨fun j ↦ j.1 ≠ w, fun _ ↦ False, (w, t), fun _ ↦ by simp,
      ⟨(s.sel w H, u), ⟨rfl, hu⟩, hne⟩, fun ⟨_, _, h⟩ ↦ h⟩

/-- Where the world of evaluation lies in the domain, centering idles selection and hybrid *will*
is symmetric *will* (p. 117). -/
theorem hybrid_iff_linearWill {A : W × T → Prop} {w : W} {t : T} (hw : w ∈ H) :
    hybrid s H A (w, t) ↔ linearWill (fun u ↦ A (w, u)) t := by
  rw [linearWill_iff]
  constructor
  · rintro ⟨⟨jw, ju⟩, ⟨hj, ht⟩, hA⟩
    simp only [s.centering w H hw] at hj
    exact ⟨ju, ht, hj ▸ hA⟩
  · rintro ⟨u, hu, hA⟩
    exact ⟨(w, u), ⟨(s.centering w H hw).symm, hu⟩, hA⟩

/-- Symmetric *will* has no present-directed use, though *The laundry will be done by now* is true
(p. 46). -/
theorem not_linearWill_now {A : T → Prop} {now : T} :
    ¬ linearWill (fun u ↦ u = now ∧ A u) now :=
  fun h ↦ let ⟨_, hu, hnow, _⟩ := linearWill_iff.1 h; lt_irrefl now (hnow ▸ hu)

end Modal

/-! ### The Oedipus model

In Figure 6.1 (p. 94) the historical possibilities of the context, `w0` to `w3`, agree that
Oedipus marries Jocasta, and the epistemic state also admits `w4`, in which he marries Kate.
Over the fixed domain of the historical possibilities, *it is possible that Oedipus will avoid
incest* is false whatever the selection function, since every selection from the domain marries
Jocasta (p. 95). Over the modal base of Figure 6.4 (p. 105), which gives `w4` its own cell, it is
true. -/

section Oedipus

/-- The five worlds of Figure 6.1. -/
inductive World where
  | w0 | w1 | w2 | w3 | w4
  deriving DecidableEq, Repr, Fintype

/-- The proposition that Oedipus avoids incest, marrying Kate. -/
def avoidIncest : Set World := {.w4}

/-- The historical possibilities of the context, in which Oedipus marries Jocasta. -/
def historicalPossibilities : Set World := {.w0, .w1, .w2, .w3}

/-- The epistemic modal base admits every world. -/
def epistemic : SetRel World World := .univ

/-- The historical modal base of Figure 6.4 partitions the worlds into the historical
possibilities of the context and `w4`. -/
def historical : SetRel World World := {p | p.1 = .w4 ↔ p.2 = .w4}

instance : historical.IsRefl := ⟨fun _ ↦ Iff.rfl⟩

/-- Over the historical possibilities as a fixed domain, *it is possible that Oedipus will avoid
incest* is false at the actual world (p. 95). -/
theorem not_diamond_will_fixed (s : SelectionFunction World) :
    ¬ ◇[epistemic] (· ∈ CarianiSantorio2018.will s historicalPossibilities avoidIncest) .w0 := by
  rintro ⟨v, -, hv⟩
  have := s.inclusion v historicalPossibilities ⟨.w0, by simp [historicalPossibilities]⟩
  simp only [CarianiSantorio2018.mem_will, avoidIncest, Set.mem_singleton_iff] at hv
  rw [hv] at this
  simp [historicalPossibilities] at this

/-- Over the historical modal base, *it is possible that Oedipus will avoid incest* is true at
the actual world, `w4` witnessing it (p. 106). -/
theorem diamond_will_historical (s : SelectionFunction World) :
    ◇[epistemic] (· ∈ s.modal historical avoidIncest) .w0 :=
  ⟨.w4, trivial, by rw [modal_eq_id]; rfl⟩

end Oedipus

/-! ### Future-might contradictions

An information state is historically eligible when it cuts through no cell of the historical
partition (p. 109). Over a realistic base, *will B* and historical *might not B*, (20) of p. 107,
are consistent at a world but accepted together by no nonempty eligible state, which classifies
them as coordinated-informationally inconsistent, Fact 6.4 (p. 110, proof p. 114). -/

section FMC

variable {W : Type*} (s : SelectionFunction W) (R : SetRel W W)

/-- An information state is historically eligible for a modal base when it holds every world the
base relates to its own. -/
def IsEligible (S : Set W) : Prop := ∀ w ∈ S, ∀ v, w ~[R] v → v ∈ S

variable {s R}

/-- No nonempty eligible state accepts both *will B* and historical *might not B*, Fact 6.4. -/
theorem not_accepts_will_and_might_not [R.IsRefl] {S B : Set W} (hS : IsEligible R S)
    (hne : S.Nonempty) : ¬ (S ⊆ s.modal R B ∧ S ⊆ R.preimage Bᶜ) := by
  rintro ⟨hwill, hmight⟩
  obtain ⟨z, hz⟩ := hne
  obtain ⟨v, hv, hzv⟩ := hmight hz
  have := hwill (hS z hz v hzv)
  rw [modal_eq_id] at this
  exact hv this

end FMC

theorem fmc_point_consistent (s : SelectionFunction CarianiSantorio2018.W) :
    CarianiSantorio2018.W.cw ∈
      s.modal (CarianiSantorio2018.frame.alt 0) CarianiSantorio2018.warriorsCap ∩
        (CarianiSantorio2018.frame.alt 0).preimage CarianiSantorio2018.warriorsCapᶜ := by
  refine ⟨by rw [modal_eq_id]; rfl, .cg, by simp [CarianiSantorio2018.warriorsCap], ?_⟩
  change CarianiSantorio2018.W.cg ∈ CarianiSantorio2018.frame.alternatives (.cw, 0)
  simp

/-! ### Kissine's argument

Kissine argues against a modal *will* from the inconsistency of *will A and might not will A* and
of *not will A and might will A*, (12) and (15), which holds for a quantificational *will* over a
transitive and over a Euclidean base respectively; over a serial base with both properties
*might will A* collapses to *will A* (`ModalLogic.diamond_box_iff`). The fork model of
footnote 3 (p. 100) is transitive but not Euclidean, and satisfies (15). Selection escapes the
argument, which assumes universal force (p. 101). -/

section Kissine

variable {W : Type*} {R : SetRel W W} {p : W → Prop} {w : W}

/-- Over a transitive base *will A and might not will A* is inconsistent for a quantificational
*will*. -/
theorem not_will_and_might_not_will [R.IsTrans] :
    ¬ (□[R] p w ∧ ◇[R] (fun v ↦ ¬ □[R] p v) w) :=
  fun ⟨h, _, hv, hn⟩ ↦ hn (box_four h _ hv)

theorem not_not_will_and_might_will [IsEuclidean R] :
    ¬ (¬ □[R] p w ∧ ◇[R] (□[R] p) w) :=
  fun ⟨h, h'⟩ ↦ h (box_of_diamond_box h')

/-- The fork model relates `0` to `1` and `2` and each of these to itself. -/
def fork : SetRel (Fin 3) (Fin 3) := {p | p.1 = 0 ∧ p.2 ≠ 0 ∨ p.1 ≠ 0 ∧ p.2 = p.1}

instance : DecidablePred (· ∈ fork) := fun p ↦
  inferInstanceAs (Decidable (p.1 = 0 ∧ p.2 ≠ 0 ∨ p.1 ≠ 0 ∧ p.2 = p.1))

instance : fork.IsTrans := ⟨by decide⟩

theorem not_isEuclidean_fork : ¬ IsEuclidean fork :=
  fun h ↦ absurd (h.eucl 0 1 2 (by decide) (by decide)) (by decide)

theorem fork_not_will_and_might_will :
    ¬ □[fork] (· = 1) 0 ∧ ◇[fork] (□[fork] (· = 1)) 0 :=
  ⟨fun h ↦ absurd (h 2 (by decide)) (by decide),
    ⟨1, by decide, by decide⟩⟩

end Kissine

/-! ### Selection semantics, Condoravdi style

Chapter 7 states *will* in Condoravdi's framework: WOLL selects a world out of the historical
modal base and extends the interval of evaluation forward to the end of time, and the present
locates the interval at *now* (p. 126). Neither contribution quantifies, so *will* and *not*
commute (p. 127), where Condoravdi's universal WOLL does not. Over a realistic base selectional
WOLL is the prejacent at the world itself, the limited collapse Condoravdi's diversity condition
is designed to avoid (p. 128). -/

section Condoravdi

open Aspect
open Condoravdi2002 (PRES WOLL frame)
open Event (τ)

variable {W E T : Type*} [LinearOrder T] [Event.TemporalTrace E T] (s : SelectionFunction W)
  (MB : W → T → Set W) (Q : SortedProperty W E T) {w : W} {now : T}

/-- Selectional WOLL instantiates the property throughout the forward interval from the start of
the reference interval at the world selected from the modal base there (p. 126). -/
def woll : SortedProperty W E T :=
  .temporal fun w t ↦ ∃ t₀ : T, IsLeast (t : Set (WithTop T)) ↑t₀ ∧
    At (Interval.Ici ↑t₀) (s.sel w (MB w t₀)) Q

/-- Negation of a sorted property, true at an interval where the property is not instantiated
(p. 126). -/
def neg : SortedProperty W E T := .temporal fun w t ↦ ¬ At t w Q

variable {s MB Q}

@[simp] theorem pres_woll_iff :
    PRES now (woll s MB Q) w ↔ At (Interval.Ici ↑now) (s.sel w (MB w now)) Q := by
  rw [PRES, Interval.pure]
  refine ⟨fun ⟨t₀, ht₀, h⟩ ↦ ?_, fun h ↦ ⟨now, Interval.isLeast_coe_fst, h⟩⟩
  obtain rfl : t₀ = now := WithTop.coe_eq_coe.1 (ht₀.unique Interval.isLeast_coe_fst)
  exact h

/-- *Will not A* and *not will A* have complementary truth conditions (p. 127). -/
theorem pres_woll_neg_iff : PRES now (woll s MB (neg Q)) w ↔ ¬ PRES now (woll s MB Q) w := by
  rw [pres_woll_iff, pres_woll_iff]
  rfl

/-- Condoravdi's universal WOLL does not commute with negation, since over a base whose worlds
disagree on the property neither *will A* nor *will not A* holds. -/
theorem not_pres_WOLL_and_neg {w₁ w₂ : W} (h₁ : w₁ ∈ MB w now) (h₂ : w₂ ∈ MB w now)
    (hQ₁ : At (Interval.Ici ↑now) w₁ Q) (hQ₂ : ¬ At (Interval.Ici ↑now) w₂ Q) :
    ¬ PRES now (WOLL MB Q) w ∧ ¬ PRES now (WOLL MB (neg Q)) w := by
  rw [Condoravdi2002.pres_woll_iff, Condoravdi2002.pres_woll_iff]
  exact ⟨fun h ↦ hQ₂ (h w₂ h₂), fun h ↦ h w₁ h₁ hQ₁⟩

/-- Over a realistic base selectional WOLL at the present is the prejacent at the world itself
throughout the forward interval (p. 128). -/
theorem pres_woll_iff_of_mem (h : w ∈ MB w now) :
    PRES now (woll s MB Q) w ↔ At (Interval.Ici ↑now) w Q := by
  rw [pres_woll_iff, s.centering w _ h]

theorem pres_woll_of_pres_WOLL (h : w ∈ MB w now) (hW : PRES now (WOLL MB Q) w) :
    PRES now (woll s MB Q) w :=
  (pres_woll_iff_of_mem h).2 (Condoravdi2002.pres_woll_iff.1 hW w h)

/-- Present-directed *will* validates excluded middle (§5.7, (5), p. 87), unlike Condoravdi's
universal WOLL, which like *must* in (6) does not. -/
theorem pres_woll_or_neg : PRES now (woll s MB Q) w ∨ PRES now (woll s MB (neg Q)) w := by
  rw [pres_woll_neg_iff]
  exact em _

/-- Outermost *by now* is idle in the present tense (p. 129). -/
theorem pres_frame_now_iff (X : SortedProperty W E T) :
    PRES now (frame (Interval.pure ↑now) X) w ↔ PRES now X w := by
  simp only [PRES, frame, At, inf_idem]

/-- Present-directed *will* with the stative *The laundry will be done by now* (10) holds when a
state of the selected world overlaps the present (p. 129). -/
theorem pres_woll_frame_stative_iff {P : W → E → Prop} :
    PRES now (woll s MB (frame (Interval.pure ↑now) (.stative P))) w ↔
      ∃ e, P (s.sel w (MB w now)) e ∧ now ∈ τ e := by
  rw [pres_woll_iff]
  change At (Interval.Ici (↑now : WithTop T) ⊓ Interval.pure ↑now) _ (.stative P) ↔ _
  rw [inf_eq_right.2 (Interval.pure_le_Ici.2 le_rfl)]
  simp only [At, Interval.not_disjoint_iff, Interval.mem_pure]
  refine exists_congr fun e ↦ and_congr_right fun _ ↦ ?_
  simp [NonemptyInterval.mem_def]

/-- With an eventive prejacent (11), present-directed *will* requires an instantaneous event at the
present, as in (12) (p. 129). -/
theorem pres_woll_frame_eventive_iff {P : W → E → Prop} :
    PRES now (woll s MB (frame (Interval.pure ↑now) (.eventive P))) w ↔
      ∃ e, P (s.sel w (MB w now)) e ∧ τ e = NonemptyInterval.pure now := by
  rw [pres_woll_iff]
  change At (Interval.Ici (↑now : WithTop T) ⊓ Interval.pure ↑now) _ (.eventive P) ↔ _
  rw [inf_eq_right.2 (Interval.pure_le_Ici.2 le_rfl)]
  simp only [At, Interval.coe_le_iff, Interval.mem_pure]
  refine exists_congr fun e ↦ and_congr_right fun _ ↦ ?_
  simp [NonemptyInterval.ext_iff, Prod.ext_iff, NonemptyInterval.withTop]

end Condoravdi

/-! ### Will-conditionals

An *if*-clause restricts the modal base of the modal in its scope to the antecedent-worlds,
`f + A` (Definition 8.1, p. 137), and *will* contributes the selection, so *if A, will B* holds
where the world selected from the base restricted to `A` is a `B`-world, Stalnaker's
conditional with a modal base (p. 133). Restricting twice is restricting once by the
conjunction, so will-conditionals validate import–export (p. 140), and over a realistic base
the conditional future-might contradiction is accepted by no eligible state, Fact 8.3 (p. 142,
proof p. 152). -/

section Conditionals

variable {W : Type*} (s : SelectionFunction W) (R : SetRel W W) (A B : Set W)

/-- *If A, will B*, selectional *will* along the base restricted to the `A`-worlds. -/
def willIf : CompleteLatticeHom (Set W) (Set W) := s.modal (R ∩ Set.univ ×ˢ A)

variable {s R A B}

/-- Import–export for will-conditionals, *if A, if B, will C* is *if A and B, will C* (p. 140). -/
theorem willIf_willIf (C : Set W) :
    willIf s (R ∩ Set.univ ×ˢ A) B C = willIf s R (A ∩ B) C := by
  rw [willIf, willIf, Set.inter_assoc, Set.prod_inter_prod, Set.inter_self]

/-- Over the universal base, a will-conditional with a possible antecedent is Stalnaker's
conditional (p. 133). -/
theorem willIf_univ_eq_selectionConditional (hA : A.Nonempty) (B : Set W) :
    willIf s .univ A B = selectionConditional s A B := by
  rw [selectionConditional_eq_modal hA, willIf]
  congr 2
  ext ⟨_, _⟩
  simp

/-- *If A, might B* alone entails *might (A and B)*, so semi-closure, Fact 8.2 (p. 142), holds
for the restrictor analysis of *if*. -/
theorem diamond_of_diamond_inter {w : W} {p : W → Prop}
    (h : ◇[R ∩ Set.univ ×ˢ A] p w) : ◇[R] (fun v ↦ v ∈ A ∧ p v) w :=
  let ⟨v, ⟨hwv, _, hv⟩, hp⟩ := h
  ⟨v, hwv, hv, hp⟩

/-- No nonempty eligible state accepts both *if A, will B* and *if A, might not B*, Fact 8.3. -/
theorem not_accepts_willIf_and_mightIf_not [R.IsRefl] {S : Set W} (hS : IsEligible R S)
    (hne : S.Nonempty) : ¬ (S ⊆ willIf s R A B ∧ S ⊆ (R ∩ Set.univ ×ˢ A).preimage Bᶜ) := by
  rintro ⟨hwill, hmight⟩
  obtain ⟨z, hz⟩ := hne
  obtain ⟨v, hv, hzv, -, hvA⟩ := hmight hz
  have := hwill (hS z hz v hzv)
  rw [willIf, mem_modal,
    along_eq_self (R := R ∩ Set.univ ×ˢ A) (w := v) ⟨R.rfl, trivial, hvA⟩] at this
  exact hv this

end Conditionals

/-! ### Indeterminacy and the thin red line

Chapter 11 keeps every context classical, fixing a world, and reads the open future as
indeterminacy over which of the contexts of a cloud an utterance has. A bare prediction has one
content across the cloud, generalized transparency, and its truth there is indeterminate, so the
normative status of asserting it is indeterminate too, the lifting argument of Fact 11.1 (p. 211,
proof pp. 222-223). The determinacy operator `D` is necessity along a relation between contexts,
and its indeterminacy `I φ` is `¬ D φ ∧ ¬ D ¬φ` (p. 211). Against a flexible thin red line,
convergence, that moments on one history share a thin red line, and centering, that the thin
red line at a moment passes through it, are inconsistent once two branches leave a moment
(Figure 11.4, p. 217). -/

section ThinRedLine

variable {C : Type*} (R : SetRel C C)

/-- Indeterminacy along the determinacy relation `R`, `¬ D φ ∧ ¬ D ¬φ` (p. 211). -/
def Indeterminate (φ : C → Prop) (c : C) : Prop := ¬ □[R] φ c ∧ ¬ □[R] (fun c' ↦ ¬ φ c') c

variable {R}

/-- If the truth of `A` in the utterance context is indeterminate, so is whether its determinate
assertion satisfies the truth norm (Fact 11.1, p. 210). -/
theorem indeterminate_sat (cloud : Set C) {cu : C} {holds asserts sat : C → Prop}
    (hind : Indeterminate R holds cu)
    (hbridge : (∀ c ∈ cloud, asserts c) → □[R] asserts cu)
    (hcontent : ∀ c ∈ cloud, asserts c)
    (hnorm : □[R] (fun c ↦ sat c ↔ (asserts c → holds c)) cu) :
    Indeterminate R sat cu :=
  have ha := hbridge hcontent
  ⟨fun h ↦ hind.1 fun c hc ↦ (hnorm c hc).1 (h c hc) (ha c hc),
    fun h ↦ hind.2 fun c hc ht ↦ h c hc ((hnorm c hc).2 fun _ ↦ ht)⟩

/-- A thin red line assigning each moment a history cannot be both convergent and centered once
two incomparable moments follow a common one (Figure 11.4). -/
theorem not_exists_convergent_centered_trl {M : Type*} [PartialOrder M] [IsLeftLinear M]
    {m₁ m₂ m₃ : M} (h₂ : m₁ ≤ m₂) (h₃ : m₁ ≤ m₃) (h₂₃ : ¬ (m₂ ≤ m₃ ∨ m₃ ≤ m₂)) :
    ¬ ∃ trl : M → Flag M, (∀ m, m ∈ trl m) ∧
      ∀ m m' (h : Flag M), m ∈ h → m' ∈ h → trl m = trl m' := by
  rintro ⟨trl, hcen, hconv⟩
  obtain ⟨h, hm₁, hm₂⟩ := BranchingTime.histories_inter_nonempty_iff.2 (.inl h₂)
  obtain ⟨h', hm₁', hm₃⟩ := BranchingTime.histories_inter_nonempty_iff.2 (.inl h₃)
  have htrl : trl m₂ = trl m₃ := (hconv _ _ h hm₁ hm₂).symm.trans (hconv _ _ h' hm₁' hm₃)
  exact h₂₃ ((trl m₂).le_or_le (hcen m₂) (htrl ▸ hcen m₃))

end ThinRedLine

end Cariani2021
