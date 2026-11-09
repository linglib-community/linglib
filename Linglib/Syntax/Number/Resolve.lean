/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Number.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.UpperLower.Basic

/-!
# Number resolution

A system's values partition the positive cardinalities: a referent of `n` individuals takes the
determinate value of `n` if the system has one and the plural otherwise. A target agreeing with
conjoined noun phrases takes the value of the group they form, whose cardinality is the sum of
theirs: in Slovene the dual for two singulars and the plural otherwise. The group's value is a
function of the conjuncts' values [exactly when the determinate values are an initial
segment](##Number.determinateInitial_iff_factorsThrough) of singular, dual and trial, [exactly
when the cells are intervals](##Number.determinateInitial_iff_ordConnected), and [`resolve` is
that function](##Number.resolve_ofCard). A target's value is a function of its controller's
[exactly when the controller's system has every determinate value of the
target's](##Number.factorsThrough_ofCard_iff), as a Modern Hebrew verb takes the plural with a
dual noun.

## Implementation notes

Number is indifferent to which individuals a referent comprises, so a system's partition of
referents factors through their cardinality, and the cardinality of a sum of distinct individuals
is the sum of theirs. Conjuncts sharing a referent, as in *my friend and colleague*, fall outside
resolution by values.

`ofCard` is a system's partition only when its values other than the plural are determinate. An
approximative value has no boundary fixed by the system (the Bayso paucal is for two to about
six), and the minimal and augmented are relative to person, so neither is a class the labels cut
out. `resolve` and `coarsen` send them, as they send the plural, to the plural; no theorem here
reaches them. In Harbour's settings an approximative value rules resolution out
(`Studies/Harbour2014.lean`).

## TODO

* Minimal–augmented systems, where the speaker and the addressee, each minimal, sum to the
  minimal inclusive, want person and number resolved together.

## References

* [corbett-1991] §9.1.2, pp. 263–264
* [corbett-2000] §6.1, pp. 180–181; §6.5.2, pp. 198–199
* [corbett-2006] §8.2, pp. 242–243; §8.5.4, p. 257
* [link-1983]
* [heycock-zamparelli-2005]
-/

@[expose] public section

namespace Number

variable (s : Finset Number)

/-- `ofCard s n` is the value the system `s` gives a referent of `n` individuals, the
determinate value of `n` if `s` has it and the plural otherwise. -/
def ofCard (n : ℕ+) : Number :=
  match fromCard? n with
  | some v => if v ∈ s then v else .plural
  | none => .plural

/-- `resolve s a b` is the resolved number of two conjuncts, the value of the sum of their
cardinalities; a conjunct with no fixed cardinality makes it plural. -/
def resolve (a b : Number) : Number :=
  (Option.map₂ (· + ·) a.exactCard b.exactCard).elim .plural (ofCard s)

/-- `coarsen s v` is the value the system `s` gives the referent of a value `v` of another
system, the value of its cardinality if `v` has one and the plural otherwise. -/
def coarsen (v : Number) : Number :=
  v.exactCard.elim .plural (ofCard s)

variable {s} {n : ℕ+} {v : Number}

private theorem not_isDeterminate_plural : ¬ Number.plural.IsDeterminate := by decide

/-! ### The value of a cardinality -/

/-- A system uses a determinate value for its cardinality alone. -/
theorem ofCard_eq_iff (hv : v.IsDeterminate) :
    ofCard s n = v ↔ v ∈ s ∧ v.exactCard = some n := by
  rw [← fromCard?_eq_some_iff]
  unfold ofCard
  rcases fromCard? n with _ | w
  · exact ⟨fun (h : Number.plural = v) ↦ absurd (h ▸ hv) not_isDeterminate_plural,
      fun ⟨_, h⟩ ↦ nomatch h⟩
  · by_cases hw : w ∈ s
    · simp only [hw, ↓reduceIte, Option.some.injEq]
      exact ⟨fun h ↦ h ▸ ⟨hw, rfl⟩, fun ⟨_, h⟩ ↦ h⟩
    · simp only [hw, ↓reduceIte, Option.some.injEq]
      exact ⟨fun h ↦ absurd (h ▸ hv) not_isDeterminate_plural, fun ⟨h, e⟩ ↦ absurd (e ▸ h) hw⟩

theorem isDeterminate_ofCard : (ofCard s n).IsDeterminate ↔ ∃ v ∈ s, v.exactCard = some n :=
  ⟨fun h ↦ ⟨_, (ofCard_eq_iff h).1 rfl⟩, fun ⟨_, hv, hn⟩ ↦
    (ofCard_eq_iff (Option.isSome_iff_exists.2 ⟨n, hn⟩)).2 ⟨hv, hn⟩ ▸
      Option.isSome_iff_exists.2 ⟨n, hn⟩⟩

theorem exactCard_ofCard (h : (ofCard s n).IsDeterminate) : (ofCard s n).exactCard = some n :=
  ((ofCard_eq_iff h).1 rfl).2

/-- Every value a system gives is determinate or the plural. -/
theorem ofCard_eq_plural_iff : ofCard s n = .plural ↔ ¬ (ofCard s n).IsDeterminate := by
  refine ⟨fun h hd ↦ not_isDeterminate_plural (h ▸ hd), fun h ↦ ?_⟩
  unfold ofCard at h ⊢
  rcases hf : fromCard? n with _ | w
  · rfl
  · by_cases hw : w ∈ s
    · simp only [hf, hw, ↓reduceIte] at h
      exact absurd (Option.isSome_iff_exists.2 ⟨n, fromCard?_eq_some_iff.1 hf⟩) h
    · simp [hw]

/-- A system uses the plural for the cardinalities none of its values is fixed to. -/
theorem ofCard_eq_plural_iff_forall : ofCard s n = .plural ↔ ∀ v ∈ s, v.exactCard ≠ some n := by
  rw [ofCard_eq_plural_iff, isDeterminate_ofCard]
  push Not
  rfl

theorem ofCard_of_three_lt (h : 3 < n) : ofCard s n = .plural := by
  simp [ofCard, fromCard?_eq_none_iff.2 h]

/-! ### The cells of a system -/

/-- The determinate values of a system are an initial segment exactly when the cardinalities it
gives a determinate value are. -/
theorem determinateInitial_iff_isLowerSet :
    DeterminateInitial s ↔ IsLowerSet {n | (ofCard s n).IsDeterminate} := by
  simp only [IsLowerSet, Set.mem_ofPred_eq, isDeterminate_ofCard]
  refine ⟨fun h n m hmn ⟨v, hv, hn⟩ ↦ ?_, fun h v hv n hn m hm w hw ↦ ?_⟩
  · obtain ⟨w, hw⟩ := exists_fromCard?_eq_some (hmn.trans (le_three_of_exactCard_eq_some hn))
    exact ⟨w, h v hv n hn m (Finset.mem_Icc.2 ⟨one_le, hmn⟩) w hw, fromCard?_eq_some_iff.1 hw⟩
  · obtain ⟨w', hw', hm'⟩ := h (Finset.mem_Icc.1 hm).2 ⟨v, hv, hn⟩
    rwa [Option.some_injective _ ((fromCard?_eq_some_iff.2 hm').symm.trans hw)] at hw'

/-- The determinate values of a system are an initial segment exactly when its cells are
intervals of cardinalities. -/
theorem determinateInitial_iff_ordConnected :
    DeterminateInitial s ↔ ∀ v, (ofCard s ⁻¹' {v}).OrdConnected := by
  rw [determinateInitial_iff_isLowerSet]
  have hpl : ofCard s ⁻¹' {.plural} = {n | (ofCard s n).IsDeterminate}ᶜ :=
    Set.ext fun _ ↦ ofCard_eq_plural_iff
  refine ⟨fun h v ↦ ?_, fun h n m hmn hn ↦ ?_⟩
  · by_cases hv : v.IsDeterminate
    · have hs : (ofCard s ⁻¹' {v}).Subsingleton := fun x hx y hy ↦ by
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hx hy
        have ex := exactCard_ofCard (hx ▸ hv)
        rwa [hx, ← hy, exactCard_ofCard (hy ▸ hv), Option.some_inj, eq_comm] at ex
      rcases hs.eq_empty_or_singleton with h' | ⟨c, h'⟩ <;> rw [h']
      exacts [Set.ordConnected_empty, Set.ordConnected_singleton]
    · by_cases hp : v = .plural
      · rw [hp, hpl]
        exact (isUpperSet_compl.2 h).ordConnected
      · convert Set.ordConnected_empty
        refine Set.eq_empty_of_forall_notMem fun x hx ↦ hp ?_
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
        exact hx ▸ ofCard_eq_plural_iff.2 (hx ▸ hv)
  · by_contra hm
    have h4 : ofCard s 4 = .plural := ofCard_of_three_lt (by decide)
    exact ofCard_eq_plural_iff.1 ((h .plural).out (ofCard_eq_plural_iff.2 hm) h4
      ⟨hmn, (le_three_of_exactCard_eq_some (exactCard_ofCard hn)).trans (by decide)⟩) hn

/-! ### Resolution -/

theorem resolve_comm (a b : Number) : resolve s a b = resolve s b a := by
  unfold resolve
  rw [Option.map₂_comm (g := (· + ·)) fun a b ↦ add_comm a b]

theorem resolve_of_not_isDeterminate_left {a : Number} (ha : ¬ a.IsDeterminate) (b : Number) :
    resolve s a b = .plural := by
  simp [resolve, Option.not_isSome_iff_eq_none.1 ha]

theorem resolve_of_not_isDeterminate_right (a : Number) {b : Number} (hb : ¬ b.IsDeterminate) :
    resolve s a b = .plural := by
  rw [resolve_comm, resolve_of_not_isDeterminate_left hb]

@[simp] theorem resolve_plural_left (b : Number) : resolve s .plural b = .plural :=
  resolve_of_not_isDeterminate_left not_isDeterminate_plural b

@[simp] theorem resolve_plural_right (a : Number) : resolve s a .plural = .plural :=
  resolve_of_not_isDeterminate_right a not_isDeterminate_plural

/-- In a system whose determinate values are an initial segment of singular, dual and trial,
conjuncts of `m` and `n` individuals resolve to the value of `m + n`. -/
theorem resolve_ofCard (h : DeterminateInitial s) (m n : ℕ+) :
    resolve s (ofCard s m) (ofCard s n) = ofCard s (m + n) := by
  by_cases hd : (ofCard s m).IsDeterminate ∧ (ofCard s n).IsDeterminate
  · simp [resolve, exactCard_ofCard hd.1, exactCard_ofCard hd.2]
  have hp : resolve s (ofCard s m) (ofCard s n) = .plural := by
    rcases not_and_or.1 hd with hd | hd
    · exact resolve_of_not_isDeterminate_left hd _
    · exact resolve_of_not_isDeterminate_right _ hd
  rw [hp, eq_comm, ofCard_eq_plural_iff]
  have h := determinateInitial_iff_isLowerSet.1 h
  exact fun hmn ↦ hd ⟨h (PNat.lt_add_right m n).le hmn, h (PNat.lt_add_left n m).le hmn⟩

/-- A system gives a coordination a value its conjuncts' values determine, and that agrees with
the values of cardinalities, exactly when its determinate values are an initial segment of
singular, dual and trial. A system with a dual and no singular fails: it gives one individual and
four alike the plural, but one more makes two, which is dual, and five, which is plural. -/
theorem determinateInitial_iff_factorsThrough : DeterminateInitial s ↔
    (fun p : ℕ+ × ℕ+ ↦ ofCard s (p.1 + p.2)).FactorsThrough (Prod.map (ofCard s) (ofCard s)) := by
  refine ⟨fun h ⟨a, b⟩ ⟨c, d⟩ hp ↦ ?_, fun H ↦ ?_⟩
  · simp only [Prod.map, Prod.mk.injEq] at hp
    simp only [← resolve_ofCard h, hp.1, hp.2]
  rw [determinateInitial_iff_isLowerSet]
  intro n m hmn hn
  by_contra hm
  have hlt : m < n := lt_of_le_of_ne hmn fun e ↦ hm (e ▸ hn)
  have e := H (a := (m, n - m)) (b := (4, n - m)) (by
    simp [ofCard_eq_plural_iff.2 hm, ofCard_of_three_lt (n := 4) (by decide)])
  simp only [PNat.add_sub_of_lt hlt] at e
  exact ofCard_eq_plural_iff.1 (e.trans (ofCard_of_three_lt
    (lt_of_lt_of_le (by decide) (PNat.lt_add_right 4 (n - m)).le))) hn

/-- Any number of conjuncts, resolved in order, give the value of the sum of their
cardinalities. -/
theorem foldl_resolve_ofCard (h : DeterminateInitial s) (m : ℕ+) (ms : List ℕ+) :
    (ms.map (ofCard s)).foldl (resolve s) (ofCard s m) = ofCard s (ms.foldl (· + ·) m) := by
  induction ms generalizing m with
  | nil => rfl
  | cons x xs ih => simp [resolve_ofCard h, ih]

/-! ### Coarsening -/

theorem coarsen_of_not_isDeterminate (hv : ¬ v.IsDeterminate) : coarsen s v = .plural := by
  simp [coarsen, Option.not_isSome_iff_eq_none.1 hv]

variable {src tgt : Finset Number}

private theorem ofCard_eq_plural_of_subset (h : ∀ v ∈ tgt, v.IsDeterminate → v ∈ src)
    (hn : ¬ (ofCard src n).IsDeterminate) : ofCard tgt n = .plural :=
  ofCard_eq_plural_iff.2 fun htd ↦ hn <| ((ofCard_eq_iff htd).2
    ⟨h _ ((ofCard_eq_iff htd).1 rfl).1 htd, exactCard_ofCard htd⟩).symm ▸ htd

/-- A target's value is a function of its controller's exactly when the controller's system has
every determinate value of the target's. -/
theorem factorsThrough_ofCard_iff :
    (ofCard tgt).FactorsThrough (ofCard src) ↔ ∀ v ∈ tgt, v.IsDeterminate → v ∈ src := by
  refine ⟨fun H v hv hd ↦ ?_, fun h a b hab ↦ ?_⟩
  · by_contra hs
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hd
    have hsrc : ofCard src c = ofCard src 4 := by
      rw [ofCard_of_three_lt (n := 4) (by decide), ofCard_eq_plural_iff]
      intro hd'
      have hv' : ofCard src c = v := Option.some_injective _ <|
        (fromCard?_eq_some_iff.2 (exactCard_ofCard hd')).symm.trans (fromCard?_eq_some_iff.2 hc)
      exact hs (hv' ▸ ((ofCard_eq_iff hd').1 rfl).1)
    have e := H hsrc
    rw [(ofCard_eq_iff hd).2 ⟨hv, hc⟩, ofCard_of_three_lt (n := 4) (by decide)] at e
    exact not_isDeterminate_plural (e ▸ hd)
  · by_cases hd : (ofCard src a).IsDeterminate
    · have ex := exactCard_ofCard hd
      rw [hab, exactCard_ofCard (hab ▸ hd), Option.some_inj] at ex
      rw [ex]
    · rw [ofCard_eq_plural_of_subset h hd, ofCard_eq_plural_of_subset h (hab ▸ hd)]

/-- A target shows the value of its controller's referent when the controller's system has
every determinate value of the target's. -/
theorem coarsen_ofCard (h : ∀ v ∈ tgt, v.IsDeterminate → v ∈ src) (n : ℕ+) :
    coarsen tgt (ofCard src n) = ofCard tgt n := by
  by_cases hd : (ofCard src n).IsDeterminate
  · simp [coarsen, exactCard_ofCard hd]
  · rw [coarsen_of_not_isDeterminate hd, ofCard_eq_plural_of_subset h hd]

end Number
