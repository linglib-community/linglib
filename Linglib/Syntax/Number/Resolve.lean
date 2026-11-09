/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.PNat.Congruence
public import Linglib.Syntax.Number.Basic
public import Mathlib.Order.UpperLower.Basic

/-!
# Number resolution

A system's values partition the positive cardinalities: a referent of `n` individuals takes the
determinate value of `n` if the system has one and the plural otherwise. A target agreeing with
conjoined noun phrases takes the value of the group they form, whose cardinality is the sum of
theirs: in Slovene the dual for two singulars and the plural otherwise. The group's value is a
function of the conjuncts' values [exactly when the determinate values are an initial
segment](##Number.System.determinateInitial_iff_factorsThrough) of singular, dual and trial,
[exactly when the cells are intervals](##Number.System.determinateInitial_iff_ordConnected), and
[`resolve` is that function](##Number.System.resolve_ofCard). Of the partitions into intervals,
only those into single cardinalities up to some bound and one cell above admit such a function
(`PNat.factorsThrough_add_iff`), so a bounded cell of several cardinalities precludes it. A
target's value is a function of its controller's [exactly when the controller's system has every
determinate value of the target's](##Number.System.factorsThrough_ofCard_iff), as a Modern Hebrew
verb takes the plural with a dual noun.

## Implementation notes

Number is indifferent to which individuals a referent comprises, so a system's partition of
referents factors through their cardinality, and the cardinality of a sum of distinct individuals
is the sum of theirs. Conjuncts sharing a referent, as in *my friend and colleague*, fall outside
resolution by values.

`ofCard` is a system's partition only when its values other than the plural are determinate. An
approximative value has no boundary fixed by the system (the Bayso paucal is for two to about
six), and the minimal and augmented are relative to person, so neither is a class the labels cut
out. `resolve` and `coarsen` send them, as they send the plural, to the plural; no theorem here
reaches them.

## TODO

* Minimal–augmented systems, where the speaker and the addressee, each minimal, sum to the
  minimal inclusive, want person and number resolved together.
* Resolution in systems with an approximative value, where no function of the conjuncts' values
  gives the group's.

## References

* [corbett-1991] §9.1.2, pp. 263–264
* [corbett-2000] §6.1, pp. 180–181; §6.5.2, pp. 198–199
* [corbett-2006] §8.2, pp. 242–243; §8.5.4, p. 257
* [link-1983]
* [heycock-zamparelli-2005]
-/

@[expose] public section

namespace Number.System

variable (ns : System)

/-- `ns.ofCard n` is the value a system gives a referent of `n` individuals, the determinate
value of that cardinality if the system has it and the plural otherwise. -/
def ofCard (n : ℕ+) : Number :=
  if fromCard n ∈ ns.values then fromCard n else .plural

/-- `ns.resolve a b` is the resolved number of two conjuncts, the value of the sum of their
cardinalities; a conjunct with no fixed cardinality makes it plural. -/
def resolve (a b : Number) : Number :=
  match a.exactCard, b.exactCard with
  | some m, some n => ns.ofCard (m + n)
  | _, _ => .plural

/-- `ns.coarsen v` is the value a system gives the referent of a value `v` of another system,
the value of its cardinality if `v` has one and the plural otherwise. -/
def coarsen (v : Number) : Number :=
  match v.exactCard with
  | some n => ns.ofCard n
  | none => .plural

variable {ns} {n : ℕ+} {v : Number}

/-! ### The value of a cardinality -/

theorem ofCard_of_mem (h : fromCard n ∈ ns.values) : ns.ofCard n = fromCard n := ite_eq_left h

theorem ofCard_of_notMem (h : fromCard n ∉ ns.values) : ns.ofCard n = .plural := ite_eq_right h

theorem isDeterminate_ofCard :
    (ns.ofCard n).IsDeterminate ↔ n ≤ 3 ∧ fromCard n ∈ ns.values := by
  by_cases h : fromCard n ∈ ns.values
  · simpa [ofCard_of_mem h, h] using isDeterminate_fromCard
  · simp [ofCard_of_notMem h, h, IsDeterminate]

theorem exactCard_ofCard (h : (ns.ofCard n).IsDeterminate) :
    (ns.ofCard n).exactCard = some n := by
  obtain ⟨hn, hv⟩ := isDeterminate_ofCard.1 h
  rw [ofCard_of_mem hv, exactCard_eq_some_iff]
  exact ⟨hn, rfl⟩

/-- A system uses a determinate value for its cardinality alone. -/
theorem ofCard_eq_iff (hv : v.IsDeterminate) :
    ns.ofCard n = v ↔ v ∈ ns.values ∧ v.exactCard = some n := by
  rw [exactCard_eq_some_iff]
  refine ⟨fun h ↦ ?_, fun ⟨hv, hn, h⟩ ↦ h ▸ ofCard_of_mem (h ▸ hv)⟩
  subst h
  obtain ⟨hn, hv⟩ := isDeterminate_ofCard.1 hv
  exact ⟨ofCard_of_mem hv ▸ hv, hn, (ofCard_of_mem hv).symm⟩

/-- Every value a system gives is determinate or the plural. -/
theorem ofCard_eq_plural_iff : ns.ofCard n = .plural ↔ ¬ (ns.ofCard n).IsDeterminate := by
  refine ⟨fun h hd ↦ by rw [h] at hd; exact hd, fun h ↦ ?_⟩
  by_cases hv : fromCard n ∈ ns.values
  · rw [ofCard_of_mem hv]
    exact fromCard_of_three_lt (not_le.1 fun h3 ↦ h (isDeterminate_ofCard.2 ⟨h3, hv⟩))
  · exact ofCard_of_notMem hv

/-- A system uses the plural for the cardinalities none of its values is fixed to. -/
theorem ofCard_eq_plural_iff_forall :
    ns.ofCard n = .plural ↔ ∀ v ∈ ns.values, v.exactCard ≠ some n := by
  refine ⟨fun h v hv hn ↦ ?_, fun h ↦ ofCard_eq_plural_iff.2 fun hd ↦
    h _ ((ofCard_eq_iff hd).1 rfl).1 (exactCard_ofCard hd)⟩
  have hd := isDeterminate_of_exactCard_eq_some hn
  rw [(ofCard_eq_iff hd).2 ⟨hv, hn⟩] at h
  subst h
  exact hd

theorem ofCard_of_three_lt (h : 3 < n) : ns.ofCard n = .plural :=
  ofCard_eq_plural_iff.2 fun hd ↦ (isDeterminate_ofCard.1 hd).1.not_gt h

/-! ### The cells of a system -/

/-- The determinate values of a system are an initial segment exactly when the cardinalities it
gives a determinate value are. -/
theorem determinateInitial_iff_isLowerSet :
    ns.DeterminateInitial ↔ IsLowerSet {n | (ns.ofCard n).IsDeterminate} := by
  simp only [IsLowerSet, Set.mem_ofPred_eq, isDeterminate_ofCard]
  refine ⟨fun h n m hmn ⟨hn, hv⟩ ↦ ⟨hmn.trans hn, h _ hv n (exactCard_eq_some_iff.2 ⟨hn, rfl⟩)
    m (Finset.mem_Icc.2 ⟨one_le, hmn⟩)⟩, fun h v hv n hn m hm ↦ ?_⟩
  obtain ⟨hn3, rfl⟩ := exactCard_eq_some_iff.1 hn
  exact (h (Finset.mem_Icc.1 hm).2 ⟨hn3, hv⟩).2

/-- The determinate values of a system are an initial segment exactly when its cells are
intervals of cardinalities. -/
theorem determinateInitial_iff_ordConnected :
    ns.DeterminateInitial ↔ ∀ v, (ns.ofCard ⁻¹' {v}).OrdConnected := by
  rw [determinateInitial_iff_isLowerSet]
  have hpl : ns.ofCard ⁻¹' {.plural} = {n | (ns.ofCard n).IsDeterminate}ᶜ :=
    Set.ext fun _ ↦ ofCard_eq_plural_iff
  refine ⟨fun h v ↦ ?_, fun h n m hmn hn ↦ ?_⟩
  · by_cases hv : v.IsDeterminate
    · have hs : (ns.ofCard ⁻¹' {v}).Subsingleton := fun x hx y hy ↦ by
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
    have h4 : ns.ofCard 4 = .plural := ofCard_of_three_lt (by decide)
    exact ofCard_eq_plural_iff.1 ((h .plural).out (ofCard_eq_plural_iff.2 hm) h4
      ⟨hmn, (isDeterminate_ofCard.1 hn).1.trans (by decide)⟩) hn

/-! ### Resolution -/

theorem resolve_comm (a b : Number) : ns.resolve a b = ns.resolve b a := by
  unfold resolve
  cases a.exactCard <;> cases b.exactCard <;> simp [add_comm]

theorem resolve_of_not_isDeterminate_left {a : Number} (ha : ¬ a.IsDeterminate) (b : Number) :
    ns.resolve a b = .plural := by
  simp [resolve, exactCard_eq_none_iff.2 ha]

theorem resolve_of_not_isDeterminate_right (a : Number) {b : Number} (hb : ¬ b.IsDeterminate) :
    ns.resolve a b = .plural := by
  rw [resolve_comm, resolve_of_not_isDeterminate_left hb]

@[simp] theorem resolve_plural_left (b : Number) : ns.resolve .plural b = .plural :=
  resolve_of_not_isDeterminate_left id b

@[simp] theorem resolve_plural_right (a : Number) : ns.resolve a .plural = .plural :=
  resolve_of_not_isDeterminate_right a id

/-- In a system whose determinate values are an initial segment of singular, dual and trial,
conjuncts of `m` and `n` individuals resolve to the value of `m + n`. -/
theorem resolve_ofCard (h : ns.DeterminateInitial) (m n : ℕ+) :
    ns.resolve (ns.ofCard m) (ns.ofCard n) = ns.ofCard (m + n) := by
  by_cases hd : (ns.ofCard m).IsDeterminate ∧ (ns.ofCard n).IsDeterminate
  · rw [resolve, exactCard_ofCard hd.1, exactCard_ofCard hd.2]
  have hp : ns.resolve (ns.ofCard m) (ns.ofCard n) = .plural := by
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
theorem determinateInitial_iff_factorsThrough : ns.DeterminateInitial ↔
    (fun p : ℕ+ × ℕ+ ↦ ns.ofCard (p.1 + p.2)).FactorsThrough (Prod.map ns.ofCard ns.ofCard) := by
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

/-- In a system whose determinate values are an initial segment, the cardinalities up to some
`k` have cells of their own and those above share one. -/
theorem exists_ofCard_eq_ofCard_iff (h : ns.DeterminateInitial) :
    ∃ k : ℕ, ∀ m n, ns.ofCard m = ns.ofCard n ↔ m = n ∨ k < m ∧ k < n :=
  (PNat.factorsThrough_add_iff (determinateInitial_iff_ordConnected.1 h)).1
    (determinateInitial_iff_factorsThrough.1 h)

/-- Any number of conjuncts, resolved in order, give the value of the sum of their
cardinalities. -/
theorem foldl_resolve_ofCard (h : ns.DeterminateInitial) (m : ℕ+) (ms : List ℕ+) :
    (ms.map ns.ofCard).foldl ns.resolve (ns.ofCard m) = ns.ofCard (ms.foldl (· + ·) m) := by
  induction ms generalizing m with
  | nil => rfl
  | cons x xs ih => simp [resolve_ofCard h, ih]

/-! ### Coarsening -/

theorem coarsen_of_not_isDeterminate (hv : ¬ v.IsDeterminate) : ns.coarsen v = .plural := by
  simp [coarsen, exactCard_eq_none_iff.2 hv]

private theorem ofCard_eq_plural_of_subset {src tgt : System}
    (h : ∀ v ∈ tgt.values, v.IsDeterminate → v ∈ src.values)
    (hn : ¬ (src.ofCard n).IsDeterminate) : tgt.ofCard n = .plural :=
  ofCard_eq_plural_iff.2 fun htd ↦ hn <| ((ofCard_eq_iff htd).2
    ⟨h _ ((ofCard_eq_iff htd).1 rfl).1 htd, exactCard_ofCard htd⟩).symm ▸ htd

/-- A target's value is a function of its controller's exactly when the controller's system has
every determinate value of the target's. -/
theorem factorsThrough_ofCard_iff {src tgt : System} :
    tgt.ofCard.FactorsThrough src.ofCard ↔ ∀ v ∈ tgt.values, v.IsDeterminate → v ∈ src.values := by
  refine ⟨fun H v hv hd ↦ ?_, fun h a b hab ↦ ?_⟩
  · by_contra hs
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 (exactCard_eq_none_iff.not.2 (not_not.2 hd))
    have hsrc : src.ofCard c = src.ofCard 4 := by
      rw [ofCard_of_three_lt (n := 4) (by decide), ofCard_eq_plural_iff]
      intro hd'
      have hv' : src.ofCard c = v :=
        (exactCard_eq_some_iff.1 (exactCard_ofCard hd')).2.symm.trans (exactCard_eq_some_iff.1 hc).2
      exact hs (hv' ▸ ((ofCard_eq_iff hd').1 rfl).1)
    have e := H hsrc
    rw [(ofCard_eq_iff hd).2 ⟨hv, hc⟩, ofCard_of_three_lt (n := 4) (by decide)] at e
    subst e
    exact hd
  · by_cases hd : (src.ofCard a).IsDeterminate
    · have ex := exactCard_ofCard hd
      rw [hab, exactCard_ofCard (hab ▸ hd), Option.some_inj] at ex
      rw [ex]
    · rw [ofCard_eq_plural_of_subset h hd, ofCard_eq_plural_of_subset h (hab ▸ hd)]

/-- A target shows the value of its controller's referent when the controller's system has
every determinate value of the target's. -/
theorem coarsen_ofCard {src tgt : System}
    (h : ∀ v ∈ tgt.values, v.IsDeterminate → v ∈ src.values) (n : ℕ+) :
    tgt.coarsen (src.ofCard n) = tgt.ofCard n := by
  by_cases hd : (src.ofCard n).IsDeterminate
  · rw [coarsen, exactCard_ofCard hd]
  · rw [coarsen_of_not_isDeterminate hd, ofCard_eq_plural_of_subset h hd]

end Number.System
