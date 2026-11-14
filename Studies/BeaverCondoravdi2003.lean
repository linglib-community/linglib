/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Studies.Anscombe1964
public import Studies.Heinamaki1974
public import Linglib.Semantics.Modality.HistoricalAlternatives
public import Linglib.Semantics.Presupposition.Strawson
public import Linglib.Semantics.Attitudes.Preference.BestWorlds
public import Linglib.Semantics.Conditionals.Horizon
public import Linglib.Semantics.Degree.Superlative
public import Linglib.Semantics.Focus.Particles
public import Linglib.Semantics.Tense.Since
public import Linglib.Data.Examples.BeaverCondoravdi2003
public import Linglib.Data.Examples.Readers

/-!
# Beaver and Condoravdi (2003): a uniform *before* and *after*

*Before* and *after* differ in their logical properties, in licensing negative polarity items and
in veridicality, which since Anscombe has been taken to show that their meanings are not uniform:
a universal over the temporal clause for *before* and an existential for *after*. Beaver and
Condoravdi show that on an instantiated temporal clause both are one connective, some main-clause
time standing in an order to the earliest temporal-clause time (39), and the earliest time gives
*before* its universal effect: it is downward entailing in its temporal clause wherever defined,
and *after* upward entailing. Where the temporal clause is not instantiated, the earliest time is
taken across alternatives branching from the world of evaluation at the main-clause time (47), so
*after* stays veridical and *before* also has counterfactual and non-committal uses, which the
context sorts (48).

## Implementation notes

* The alternatives come from a T × W frame whose historical equivalence at `t` is agreement at
  all earlier times, and a clause respects it when historically equivalent worlds agree on it
  before `t`. The normality condition on alternatives (p. 50) is a choice of the model.
* In `connective` an undefined earliest time makes the sentence false. A context update discards
  both, so the readings of (48) are unaffected; the trivalent propositions `beforeP` and `afterP`
  keep the definedness condition for von Fintel's Strawson entailment.

## References

* [beaver-condoravdi-2003]
* [anscombe-1964]
* [heinamaki-1974]
* [thomason-1984]
* [von-fintel-1999]
-/

@[expose] public section

namespace BeaverCondoravdi2003

open Tense Anscombe1964 Presupposition

/-! ### Heinämäki's connectives (§4)

Heinämäki's *before* compares reference points of an interval of each clause (35)–(36). Rewriting
them without intervals, (37) and (38), gives Proposition 1, which relates them to Anscombe's. -/

section Heinamaki

open Heinamaki1974

variable {T : Type*} [LinearOrder T] {A B : Clause T} {k : NonemptyInterval T}

-- Off accomplishments, the correct form of the rewriting (36)–(37).
theorem some_before_iff_exists_beforeEver (hA : A.vendler ≠ .accomplishment) :
    A.AtSome B (Before A.vendler) ↔ ∃ K ∈ B.intervals, beforeEver A.intervals {K} := by
  simp only [beforeEver_singleton_right, Clause.AtSome, Before, tr_of_ne hA]
  exact ⟨fun ⟨J, hJ, K, hK, h⟩ ↦ ⟨K, hK, J, hJ, h⟩, fun ⟨K, hK, J, hJ, h⟩ ↦ ⟨J, hJ, K, hK, h⟩⟩

/-- Proposition 1 for *before*, on a temporal clause with a single interval. -/
theorem some_before_iff_beforeEver (hA : A.vendler ≠ .accomplishment) (hB : B.intervals = {k}) :
    A.AtSome B (Before A.vendler) ↔ beforeEver A.intervals B.intervals := by
  rw [some_before_iff_exists_beforeEver hA, hB]
  simp

-- Anscombe's *before* entails Heinämäki's on an instantiated clause, whatever the clause.
theorem some_before_of_beforeEver (hA : A.vendler ≠ .accomplishment) (hB : B.intervals.Nonempty)
    (h : beforeEver A.intervals B.intervals) : A.AtSome B (Before A.vendler) :=
  let ⟨K, hK⟩ := hB
  let ⟨_, ⟨J, hJ, htJ⟩, ht⟩ := h
  ⟨J, hJ, K, hK, (tr_of_ne hA).trans_lt (htJ.1.trans_lt (ht K.fst ⟨K, hK, le_rfl, K.fst_le_snd⟩))⟩

/-- Proposition 1 for *after*, off accomplishments, needs no assumption on the temporal clause. -/
theorem some_after_iff_after (hB : B.vendler ≠ .accomplishment) :
    A.AtSome B (After B.vendler) ↔ Anscombe.after A.intervals B.intervals := by
  simp only [Clause.AtSome, after_iff, tr_of_ne hB, Anscombe.after]
  refine ⟨fun ⟨J, hJ, K, hK, h⟩ ↦ ⟨J.snd, ⟨J, hJ, J.fst_le_snd, le_rfl⟩, K.fst,
    ⟨K, hK, le_rfl, K.fst_le_snd⟩, h⟩, fun ⟨t, ⟨J, hJ, htJ⟩, t', ⟨K, hK, htK⟩, h⟩ ↦
    ⟨J, hJ, K, hK, htK.1.trans_lt (h.trans_le htJ.2)⟩⟩

/-- The clause of an achievement at the given moments. -/
private def achievement (S : Set T) : Clause T where
  vendler := .achievement
  intervals := NonemptyInterval.pure '' S
  isPoint_iff := by
    rintro _ ⟨t, -, rfl⟩
    exact iff_of_true rfl rfl

/-- Proposition 1 as stated fails: a temporal clause holding at two moments is instantiated and
left-bounded, and a time between them is before it for Heinämäki and not for Anscombe. -/
theorem not_forall_some_before_iff_beforeEver :
    ¬ ∀ A B : Clause ℤ, A.vendler ≠ .accomplishment → B.vendler ≠ .accomplishment →
      B.intervals.Nonempty →
      (A.AtSome B (Before A.vendler) ↔ beforeEver A.intervals B.intervals) := by
  intro h
  have hmem : ∀ {S : Set ℤ} {t : ℤ}, t ∈ S → NonemptyInterval.pure t ∈ (achievement S).intervals :=
    fun ht ↦ ⟨_, ht, rfl⟩
  have hB : (1 : ℤ) ∈ ({1, 3} : Set ℤ) := by simp
  have hB' : (3 : ℤ) ∈ ({1, 3} : Set ℤ) := by simp
  have hsome : (achievement {(2 : ℤ)}).AtSome (achievement {1, 3})
      (Before (achievement {(2 : ℤ)}).vendler) :=
    ⟨_, hmem rfl, _, hmem hB', (by decide : (2 : ℤ) < 3)⟩
  obtain ⟨t, ⟨_, ⟨s, hs, rfl⟩, ht⟩, hlt⟩ :=
    (h _ _ (by decide) (by decide) ⟨_, hmem hB⟩).1 hsome
  have hts : t = s := NonemptyInterval.mem_pure.1 ht
  have hs2 : s = 2 := hs
  have h1 := hlt 1 ⟨_, hmem hB, NonemptyInterval.mem_pure_self 1⟩
  rw [hts, hs2] at h1
  exact absurd h1 (by decide)

/-- The culminations of the intervals of a clause, as moments. -/
def culminations (S : Set (NonemptyInterval T)) : Set (NonemptyInterval T) :=
  (fun i ↦ NonemptyInterval.pure i.snd) '' S

-- The extension of Proposition 1 to accomplishments, whose times are their culminations (p. 45).
theorem some_before_accomplishment_iff (hA : A.vendler = .accomplishment) :
    A.AtSome B (Before A.vendler) ↔
      ∃ K ∈ B.intervals, beforeEver (culminations A.intervals) {K} := by
  simp only [beforeEver_singleton_right, Clause.AtSome, Before, hA, tr_accomplishment, culminations,
    Set.exists_mem_image]
  exact ⟨fun ⟨J, hJ, K, hK, h⟩ ↦ ⟨K, hK, J, hJ, h⟩, fun ⟨K, hK, J, hJ, h⟩ ↦ ⟨J, hJ, K, hK, h⟩⟩

-- The same for *after*, with an accomplishment temporal clause (p. 45).
theorem some_after_accomplishment_iff (hB : B.vendler = .accomplishment) :
    A.AtSome B (After B.vendler) ↔ Anscombe.after A.intervals (culminations B.intervals) := by
  simp only [Clause.AtSome, after_iff, hB, tr_accomplishment, Anscombe.after]
  refine ⟨fun ⟨J, hJ, K, hK, h⟩ ↦ ⟨J.snd, ⟨J, hJ, J.fst_le_snd, le_rfl⟩, K.snd,
    ⟨_, ⟨K, hK, rfl⟩, NonemptyInterval.mem_pure_self _⟩, h⟩, ?_⟩
  rintro ⟨t, ⟨J, hJ, htJ⟩, t', ⟨_, ⟨K, hK, rfl⟩, ht'⟩, h⟩
  exact ⟨J, hJ, K, hK, NonemptyInterval.mem_pure.1 ht' ▸ h.trans_le htJ.2⟩

end Heinamaki

/-! ### The uniform connective (39)

Anscombe's *before* (27) quantifies universally over the temporal clause and her *after*
existentially. On a temporal clause with a first time both compare a main-clause time with the
first one, since a time precedes every time of the clause iff it precedes the first, and follows
some time of the clause iff it follows the first (§5). -/

section Uniform

variable {T : Type*} [LinearOrder T]

/-- The uniform connective (39) holds when some time of `A` stands in `cmp` to the earliest time
of `B`. -/
def uniform (cmp : T → T → Prop) (A B : Set T) : Prop := ∃ t ∈ A, ∃ e, IsLeast B e ∧ cmp t e

variable {A B B' : Set (NonemptyInterval T)}

/-- On a temporal clause with a first time, the uniform *before* is Anscombe's universal
*before*, Proposition 2 for *before*. -/
theorem uniform_lt_iff_beforeEver (hB : ∃ e, IsLeast (timeTrace B) e) :
    uniform (· < ·) (timeTrace A) (timeTrace B) ↔ beforeEver A B := by
  obtain ⟨e, he⟩ := hB
  rw [uniform, beforeEver_iff_of_isLeast he]
  exact exists_congr fun _ ↦ and_congr_right fun _ ↦
    ⟨fun ⟨_, he', h⟩ ↦ by rwa [he.unique he'], fun h ↦ ⟨e, he, h⟩⟩

/-- On a temporal clause with a first time, the uniform *after* is Anscombe's existential
*after*, Proposition 2 for *after*. -/
theorem uniform_gt_iff_after (hB : ∃ e, IsLeast (timeTrace B) e) :
    uniform (· > ·) (timeTrace A) (timeTrace B) ↔ Anscombe.after A B := by
  obtain ⟨e, he⟩ := hB
  rw [uniform, after_iff_least_lt he]
  exact exists_congr fun _ ↦ and_congr_right fun _ ↦
    ⟨fun ⟨_, he', h⟩ ↦ by rwa [he.unique he'], fun h ↦ ⟨e, he, h⟩⟩

-- (29)
theorem anscombe_before_complement_DE (h : timeTrace B' ⊆ timeTrace B) :
    beforeEver A B → beforeEver A B' :=
  (·.anti_right h)

-- (31)
theorem anscombe_after_complement_UE (h : timeTrace B ⊆ timeTrace B') :
    Anscombe.after A B → Anscombe.after A B' :=
  fun ⟨t, ht, t', ht', hlt⟩ ↦ ⟨t, ht, t', h ht', hlt⟩

-- (32), (33)
theorem anscombe_before_of_empty (hB : timeTrace B = ∅) (hA : (timeTrace A).Nonempty) :
    beforeEver A B :=
  let ⟨t, ht⟩ := hA
  ⟨t, ht, fun t' ht' ↦ absurd (hB ▸ ht') (Set.notMem_empty t')⟩

/-- The uniform *before* is Anscombe's on a temporal clause exactly when the clause has a first
time, as in Proposition 2, or no strict lower bound. -/
theorem forall_uniform_lt_iff_beforeEver :
    (∀ A, uniform (· < ·) (timeTrace A) (timeTrace B) ↔ beforeEver A B) ↔
      (∃ e, IsLeast (timeTrace B) e) ∨ strictLowerBounds (timeTrace B) = ∅ := by
  refine ⟨fun h ↦ or_iff_not_imp_left.2 fun hB ↦ Set.eq_empty_of_forall_notMem fun t ht ↦ hB ?_,
    fun hB A ↦ hB.elim uniform_lt_iff_beforeEver fun hB ↦ iff_of_false ?_ ?_⟩
  · obtain ⟨_, _, e, he, _⟩ := (h {NonemptyInterval.pure t}).2 ⟨t, by simp, ht⟩
    exact ⟨e, he⟩
  · rintro ⟨t, -, e, he, hte⟩
    exact Set.eq_empty_iff_forall_notMem.1 (he.strictLowerBounds_eq ▸ hB) t hte
  · rintro ⟨t, -, ht⟩
    exact Set.eq_empty_iff_forall_notMem.1 hB t ht

end Uniform

/-! ### Polarity

At a world the uniform connective (45) is a trivalent proposition, defined where the temporal clause
has an earliest time in the world. Its *before* is then downward entailing in the temporal clause
wherever it is defined, since a smaller clause starts no earlier, and its *after* upward
entailing, so *earliest* gives *before* the universal effect that licenses negative polarity
items (§7). -/

section Polarity

variable {W T : Type*} [LinearOrder T]

open Classical in
/-- *A before B* at a world, (45), defined where `B` has an earliest time in the world. -/
noncomputable def beforeP (A B : Set (Index W T)) : W → Trivalent :=
  Trivalent.condEvent (fun w ↦ ∃ e, IsLeast {t | ⟨w, t⟩ ∈ B} e)
    (fun w ↦ uniform (· < ·) {t | ⟨w, t⟩ ∈ A} {t | ⟨w, t⟩ ∈ B})

open Classical in
/-- *A after B* at a world, (45), defined where `B` has an earliest time in the world. -/
noncomputable def afterP (A B : Set (Index W T)) : W → Trivalent :=
  Trivalent.condEvent (fun w ↦ ∃ e, IsLeast {t | ⟨w, t⟩ ∈ B} e)
    (fun w ↦ uniform (· > ·) {t | ⟨w, t⟩ ∈ A} {t | ⟨w, t⟩ ∈ B})

/-- The uniform *before* is Strawson downward entailing in its temporal clause. -/
theorem isStrawsonDE_before (A : Set (Index W T)) : IsStrawsonDE (beforeP A) := by
  intro _ _ hB w hq hp
  simp only [beforeP, Trivalent.condEvent_eq_true_iff, ne_eq, Trivalent.condEvent_eq_undefined_iff,
    not_not] at hq hp ⊢
  obtain ⟨e, he⟩ := hp
  obtain ⟨-, t, ht, _, he', hlt⟩ := hq
  exact ⟨⟨e, he⟩, t, ht, e, he, hlt.trans_le (he'.2 (hB he.1))⟩

/-- The uniform *after* is Strawson upward entailing in its temporal clause. -/
theorem isStrawsonUE_after (A : Set (Index W T)) : IsStrawsonUE (afterP A) := by
  intro _ _ hB w hp hq
  simp only [afterP, Trivalent.condEvent_eq_true_iff, ne_eq, Trivalent.condEvent_eq_undefined_iff,
    not_not] at hq hp ⊢
  obtain ⟨e', he'⟩ := hq
  obtain ⟨-, t, ht, _, he, hlt⟩ := hp
  exact ⟨⟨e', he'⟩, t, ht, e', he', (he'.2 (hB he.1)).trans_lt hlt⟩

end Polarity

/-! ### Alternatives and the modal connective (44)–(47)

Where the temporal clause is not instantiated in the world of evaluation, the earliest time is
taken across alternatives of the world at the main-clause time (47). The alternatives lie among
the historical alternatives at that time, the worlds agreeing with it at all earlier times, the
initial branch point condition, and a world in which the temporal clause is instantiated is its
own only alternative (p. 50). An earlier temporal-clause time then lies before the branching, so
*after* is veridical, while a later one may lie on another branch (§6). -/

section Modal

variable {W T : Type*} [LinearOrder T]

/-- The times at which `B` is instantiated in some world of `worlds` (46). -/
def instTimes (worlds : Set W) (B : Set (Index W T)) : Set T := {t | ∃ w ∈ worlds, ⟨w, t⟩ ∈ B}

/-- `B` is instantiated in `w` when it holds there at some time. -/
def Inst (B : Set (Index W T)) (w : W) : Prop := ∃ t, ⟨w, t⟩ ∈ B

/-- The connective (47) holds at `w` when some main-clause time stands in `cmp` to the earliest
temporal-clause time across the alternatives of `w` at that time. -/
def connective (cmp : T → T → Prop) (A B : Set (Index W T)) (alt : HistoricalAlternatives W T)
    (w : W) : Prop :=
  ∃ t, ⟨w, t⟩ ∈ A ∧ ∃ e, IsLeast (instTimes (alt ⟨w, t⟩) B) e ∧ cmp t e

/-- *A before B* (47). -/
abbrev before (A B : Set (Index W T)) (alt : HistoricalAlternatives W T) (w : W) : Prop :=
  connective (· < ·) A B alt w

/-- *A after B* (47). -/
abbrev after (A B : Set (Index W T)) (alt : HistoricalAlternatives W T) (w : W) : Prop :=
  connective (· > ·) A B alt w

variable {cmp : T → T → Prop} {A B : Set (Index W T)} {alt : HistoricalAlternatives W T} {w : W}

-- (47), (45)
theorem connective_iff_uniform_of_eq_singleton (h : ∀ t, alt ⟨w, t⟩ = {w}) :
    connective cmp A B alt w ↔ uniform cmp {t | ⟨w, t⟩ ∈ A} {t | ⟨w, t⟩ ∈ B} := by
  have hs (t : T) : instTimes (alt ⟨w, t⟩) B = {t' | ⟨w, t'⟩ ∈ B} := by
    rw [h t]
    ext
    simp [instTimes]
  simp only [connective, uniform, hs, Set.mem_ofPred_eq]

-- (49)
theorem connective_alt_inst (h : connective cmp A B alt w) :
    ∃ t, ⟨w, t⟩ ∈ A ∧ ∃ w' ∈ alt ⟨w, t⟩, Inst B w' :=
  let ⟨t, htA, e, ⟨⟨w', hw', hB⟩, _⟩, _⟩ := h
  ⟨t, htA, w', hw', e, hB⟩

/-- A clause respects the historical equivalence of a frame when worlds historically equivalent
at `t` agree on it at all earlier times. -/
def RespectsHistory (F : Temporal.TWFrame W T) (B : Set (Index W T)) : Prop :=
  ∀ ⦃w w' : W⦄ ⦃t t' : T⦄, t' < t → F.sim t w w' → (⟨w, t'⟩ ∈ B ↔ ⟨w', t'⟩ ∈ B)

/-- Beaver and Condoravdi's alternatives for a temporal clause over a frame (p. 50) lie among the
historical alternatives and leave a world instantiating the clause as its own only
alternative. -/
structure Alternatives (F : Temporal.TWFrame W T) (B : Set (Index W T)) where
  /-- The alternatives of a world at a time. -/
  alt : HistoricalAlternatives W T
  /-- The initial branch point condition. -/
  subset_alternatives : ∀ i, alt i ⊆ F.alternatives i
  /-- A world in which the temporal clause is instantiated is its own only alternative. -/
  eq_singleton_of_inst : ∀ ⦃w⦄, Inst B w → ∀ t, alt ⟨w, t⟩ = {w}

variable {F : Temporal.TWFrame W T}

/-- On a temporal clause instantiated in the world, (47) is (45). -/
theorem connective_iff_uniform_of_inst (a : Alternatives F B) (hw : Inst B w) :
    connective cmp A B a.alt w ↔ uniform cmp {t | ⟨w, t⟩ ∈ A} {t | ⟨w, t⟩ ∈ B} :=
  connective_iff_uniform_of_eq_singleton (a.eq_singleton_of_inst hw)

/-- *After* entails its temporal clause (§6). Its earliest time precedes the main-clause time, so
the alternative instantiating it agrees with the world there. -/
theorem after_veridical (a : Alternatives F B) (hB : RespectsHistory F B) :
    after A B a.alt w → Inst B w :=
  fun ⟨_, _, e, ⟨⟨_, hw', hBe⟩, _⟩, het⟩ ↦ ⟨e, (hB het (a.subset_alternatives _ hw')).2 hBe⟩

end Modal

/-! ### The readings of *before* (48)

A context, a set of worlds, is updated with a sentence by keeping the worlds at which it is true
(p. 51). A context updated with *A after B* is always veridical, while one updated with
*A before B* is veridical, counterfactual or non-committal, depending on the context. -/

section Readings

variable {W T : Type*}

/-- The three readings of *before* (48). -/
inductive BeforeReading where
  | veridical
  | counterfactual
  | nonCommittal
  deriving DecidableEq, Repr

/-- The veridical reading has every world of the context instantiate `B`. -/
def Veridical (B : Set (Index W T)) (c : Set W) : Prop := ∀ w ∈ c, Inst B w

/-- The counterfactual reading has no world of the context instantiate `B`. -/
def Counterfactual (B : Set (Index W T)) (c : Set W) : Prop := ∀ w ∈ c, ¬ Inst B w

/-- The non-committal reading has some worlds of the context instantiate `B` and some not. -/
def NonCommittal (B : Set (Index W T)) (c : Set W) : Prop :=
  (∃ w ∈ c, Inst B w) ∧ ∃ w ∈ c, ¬ Inst B w

/-- The property of a context that a reading names. -/
def BeforeReading.Holds (B : Set (Index W T)) (c : Set W) : BeforeReading → Prop
  | .veridical => Veridical B c
  | .counterfactual => Counterfactual B c
  | .nonCommittal => NonCommittal B c

/-- Each nonempty context has exactly one of the readings (48). -/
theorem existsUnique_reading {B : Set (Index W T)} {c : Set W} (hc : c.Nonempty) :
    ∃! r : BeforeReading, r.Holds B c := by
  obtain ⟨w₀, hw₀⟩ := hc
  by_cases hv : Veridical B c
  · refine ⟨.veridical, hv, fun r hr ↦ ?_⟩
    cases r
    exacts [rfl, absurd (hv w₀ hw₀) (hr w₀ hw₀),
      absurd (hv _ hr.2.choose_spec.1) hr.2.choose_spec.2]
  by_cases hcf : Counterfactual B c
  · refine ⟨.counterfactual, hcf, fun r hr ↦ ?_⟩
    cases r
    exacts [absurd (hr w₀ hw₀) (hcf w₀ hw₀), rfl,
      absurd hr.1.choose_spec.2 (hcf _ hr.1.choose_spec.1)]
  have hnc : NonCommittal B c := by
    simp only [Veridical, Counterfactual, not_forall, not_not] at hv hcf
    obtain ⟨w, hw, hn⟩ := hv
    obtain ⟨w', hw', hi⟩ := hcf
    exact ⟨⟨w', hw', hi⟩, w, hw, hn⟩
  refine ⟨.nonCommittal, hnc, fun r hr ↦ ?_⟩
  cases r
  exacts [absurd hr hv, absurd hr hcf, rfl]

variable [LinearOrder T] {A B : Set (Index W T)} {F : Temporal.TWFrame W T}

/-- A context updated with *A after B* is veridical (p. 51). -/
theorem veridical_inter_after (a : Alternatives F B) (hB : RespectsHistory F B) (c : Set W) :
    Veridical B (c ∩ {w | after A B a.alt w}) :=
  fun _ hw ↦ after_veridical a hB hw.2

-- (49)
theorem alt_inst_of_mem_inter_before {alt : HistoricalAlternatives W T} {c : Set W} {w : W}
    (hw : w ∈ c ∩ {w | before A B alt w}) :
    ∃ t, ⟨w, t⟩ ∈ A ∧ ∃ w' ∈ alt ⟨w, t⟩, Inst B w' :=
  connective_alt_inst hw.2

end Readings

/-! ### The Mozart example

In the context in which (40) is uttered, Mozart finishes the Requiem before dying in the `finish`
world, dies first with a normal alternative in which he lives longer and finishes it in the
`early` world, and dies first with a normal alternative in which he lives longer and still does
not finish it in the `idle` world. Updating the context with *Mozart died before he finished the
Requiem* discards the first as false and the third as undefined, leaving a counterfactual context
(p. 51). -/

section Mozart

/-- The worlds of the Mozart example, with the alternatives `later` of `early` and `idleLater` of
`idle`. -/
inductive World where
  | finish | early | later | idle | idleLater
  deriving DecidableEq, Repr

/-- The time at which Mozart dies. -/
def World.death : World → ℕ
  | .finish => 2
  | .early => 1
  | .later => 3
  | .idle => 1
  | .idleLater => 3

/-- The time at which Mozart finishes the Requiem, if he does. -/
def World.completion : World → Option ℕ
  | .finish => some 1
  | .later => some 2
  | _ => none

/-- The world–time pairs at which Mozart dies. -/
def dies : Set (Index World ℕ) := {i | i.world.death = i.time}

/-- The world–time pairs at which Mozart finishes the Requiem. -/
def finishes : Set (Index World ℕ) := {i | i.world.completion = some i.time}

/-- Worlds are historically equivalent at `t` when they agree on Mozart's death and on his
finishing at all earlier times, each fact being settled from the next time on. -/
def frame : Temporal.TWFrame World ℕ :=
  .ofDatedFacts (fun f : ℕ × Bool ↦ f.1 + 1)
    fun w f ↦ if f.2 then w.death = f.1 else w.completion = some f.1

theorem respectsHistory_finishes : RespectsHistory frame finishes :=
  fun _ _ _ t' ht h ↦ by simpa [finishes] using h (t', false) ht

theorem mem_alternatives_of_le_one {t : ℕ} (ht : t ≤ 1) (w v : World) :
    v ∈ frame.alternatives ⟨w, t⟩ := by
  have hd (u : World) : u.death ≠ 0 := by cases u <;> decide
  have hc (u : World) : u.completion ≠ some 0 := by cases u <;> decide
  rintro ⟨n, b⟩ hn
  obtain rfl : n = 0 := by simp at hn; omega
  cases b <;> simp [hd, hc]

/-- The alternatives of the context, a world being its own only alternative except at the times
up to Mozart's death in `early` and `idle`, where the world in which he lives longer is
normal. -/
def alt : HistoricalAlternatives World ℕ
  | ⟨.early, t⟩ => if t ≤ 1 then {.early, .later} else {.early}
  | ⟨.idle, t⟩ => if t ≤ 1 then {.idle, .idleLater} else {.idle}
  | ⟨w, _⟩ => {w}

/-- The alternatives of the Mozart example meet the conditions of p. 50. -/
def alternatives : Alternatives frame finishes where
  alt := alt
  subset_alternatives := by
    rintro ⟨w, t⟩ v hv
    by_cases ht : t ≤ 1
    · exact mem_alternatives_of_le_one ht w v
    · cases w <;> simp [alt, ht] at hv <;> subst hv <;> exact (frame.sim t).iseqv.refl _
  eq_singleton_of_inst := by
    rintro w ⟨t, ht⟩ t'
    cases w <;> simp_all [finishes, World.completion, alt]

/-- The context in which (40) is uttered, one world of each kind. -/
def context : Set World := {.finish, .early, .idle}

/-- Updating the context with *Mozart died before he finished the Requiem* keeps exactly the
`early` world (p. 51). -/
theorem mozart_update : context ∩ {w | before dies finishes alt w} = {.early} := by
  ext w
  simp only [context, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨rfl | rfl | rfl, t, ht, e, ⟨⟨v, hv, hve⟩, he⟩, hlt⟩
    · simp only [dies, World.death, Set.mem_ofPred_eq] at ht
      subst ht
      simp only [alt, Set.mem_singleton_iff] at hv
      subst hv
      simp [finishes, World.completion] at hve
      omega
    · rfl
    · simp only [dies, World.death, Set.mem_ofPred_eq] at ht
      subst ht
      simp only [alt, le_refl, ite_true, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl <;> simp [finishes, World.completion] at hve
  · rintro rfl
    refine ⟨Or.inr (Or.inl rfl), 1, rfl, 2, ⟨⟨.later, by simp [alt], rfl⟩, ?_⟩, by decide⟩
    rintro t ⟨v, hv, hvt⟩
    simp only [alt, le_refl, ite_true, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl <;> simp_all [finishes, World.completion]

theorem counterfactual_mozart :
    Counterfactual finishes (context ∩ {w | before dies finishes alt w}) := by
  rw [mozart_update]
  rintro w rfl ⟨t, ht⟩
  simp [finishes, World.completion] at ht

end Mozart

/-! ### The examples -/

/-- The reading a row reports. -/
def readingOf : String → Option BeforeReading
  | "veridical" => some .veridical
  | "counterfactual" => some .counterfactual
  | "non-committal" => some .nonCommittal
  | _ => none

theorem rows_nonVeridical_before :
    ∀ e ∈ Examples.all, ∀ r ∈ (e.feature? "reading" >>= readingOf).toList, r ≠ .veridical →
      e.feature? "connective" = some "before" := by
  decide +kernel

end BeaverCondoravdi2003
