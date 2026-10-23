/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Combinatorics.SimpleGraph.Acyclic
public import Linglib.Core.Order.IntervalOrder
public import Linglib.Phonology.Autosegmental.Basic

/-!
# Representations in time

Read in time, the order of each tier is precedence and an association line is overlap. A
representation has an interval order when some interval order on its positions extends the
order of each tier and leaves associated positions incomparable. The `2 + 2` condition of an
interval order is the No-Crossing Constraint between two tiers, and when lines join only tiers
adjacent in a forest, every non-crossing representation has an interval order. Around a cycle
of three tiers, lines that cross none pairwise can chain into a precedence that no interval
order admits.

## Main definitions

* `AR.HasIntervalOrder`: the representation has an interval order.

## Main results

* `IsNonCrossing.of_intervals`: overlaps of intervals placed in tier order are non-crossing.
* `AR.HasIntervalOrder.noCrossing`: a representation with an interval order obeys the NCC.
* `AR.noCrossing_iff_hasIntervalOrder_of_isAcyclic`: on a forest of tiers the converse holds,
  and `AR.noCrossing_iff_hasIntervalOrder` on two tiers in particular.
* `AR.exists_noCrossing_not_hasIntervalOrder`: on a cycle of three tiers it fails.

## Implementation notes

A representation fixes precedence only within tiers, so a floating tone and a toneless timing
slot can be ordered either way: a representation has interval orders, generally many, and is
not one. The least precedence it forces is not an interval order in general, since two tiers
without lines form a `2 + 2`. The intervals for a forest of tiers are built one leaf tier at a
time, each step passing to the lexicographic product of the previous line of time with `ℕ`.

## References

* [sagey-1988]
* [bird-klein-1990]
* [fishburn-1970]
-/

@[expose] public section

namespace Autosegmental

open NonemptyInterval

/-! ### Relations between two tiers -/

section Intervals

variable {ι κ T : Type*} [Preorder ι] [LinearOrder κ] [LinearOrder T] {R : SetRel ι κ}

/-- A relation whose pairs are overlaps of intervals placed in tier order is non-crossing
([sagey-1988]'s derivation of the No-Crossing Constraint). -/
theorem IsNonCrossing.of_intervals {I : ι → NonemptyInterval T} {J : κ → NonemptyInterval T}
    (hI : ∀ ⦃a b⦄, a < b → (I a).Precedes (I b)) (hJ : ∀ ⦃a b⦄, a < b → (J a).Precedes (J b))
    (hR : ∀ x ∈ R, (I x.1).Overlaps (J x.2)) : IsNonCrossing R := by
  intro x hx y hy hlt
  by_contra! hgt
  rcases IsIntervalOrder.two_plus_two (hI hlt) (hJ hgt) with h | h
  exacts [precedes_not_overlaps h (hR x hx), precedes_not_overlaps h (overlaps_symm (hR y hy))]

end Intervals

/-! ### Representations -/

namespace AR

variable {ι : Type*} {τ : ι → Type*}

variable (X : AR τ) in
/-- `X` has an interval order: an interval order on its positions that extends the order of
each tier and leaves associated positions incomparable. -/
def HasIntervalOrder : Prop :=
  ∃ r : X.Pos → X.Pos → Prop, IsIntervalOrder X.Pos r ∧
    (∀ i ⦃p q : Fin (X.word i).length⦄, p < q → r ⟨i, p⟩ ⟨i, q⟩) ∧
      ∀ ⦃v w⦄, X.assoc.Adj v w → ¬ r v w

variable {X : AR τ}

theorem hasIntervalOrder_of_intervals {T : Type*} [LinearOrder T] (I : X.Pos → NonemptyInterval T)
    (hI : ∀ i ⦃p q : Fin (X.word i).length⦄, p < q → (I ⟨i, p⟩).Precedes (I ⟨i, q⟩))
    (hA : ∀ ⦃v w⦄, X.assoc.Adj v w → (I v).Overlaps (I w)) : X.HasIntervalOrder :=
  ⟨InvImage Precedes I, isIntervalOrder_precedes.invImage I, hI,
    fun _ _ h hp ↦ precedes_not_overlaps hp (hA h)⟩

/-- A representation with an interval order obeys the No-Crossing Constraint: two crossing
lines would make the order of their tiers a `2 + 2`. -/
theorem HasIntervalOrder.noCrossing (h : X.HasIntervalOrder) : X.NoCrossing := by
  obtain ⟨r, hr, htier, hadj⟩ := h
  refine fun i j ↦ isNonCrossing_lines_iff.2 fun p q p' q' ⟨hp, hq, h₁⟩ ⟨hp', hq', h₂⟩ hlt ↦ ?_
  by_contra! hgt
  rcases hr.two_plus_two (htier i (show (⟨p, hp⟩ : Fin _) < ⟨p', hp'⟩ from hlt))
    (htier j (show (⟨q', hq'⟩ : Fin _) < ⟨q, hq⟩ from hgt)) with h | h
  exacts [hadj h₁ h, hadj h₂.symm h]

/-- Intervals place the tiers of `s`: in order along each tier, with the lines among them
overlaps. -/
private def Placed (X : AR τ) (s : Set ι) : Prop :=
  ∃ (T : Type) (_ : LinearOrder T) (I : X.Pos → NonemptyInterval T),
    (∀ i ∈ s, ∀ ⦃p q : Fin (X.word i).length⦄, p < q → (I ⟨i, p⟩).Precedes (I ⟨i, q⟩)) ∧
      ∀ ⦃v w⦄, v.1 ∈ s → w.1 ∈ s → X.assoc.Adj v w → (I v).Overlaps (I w)

private theorem Placed.insert [Fintype ι] {G : SimpleGraph ι} (hX : X.assoc ≤ G.comap Sigma.fst)
    (hNC : X.NoCrossing) {s : Set ι} {ℓ : ι}
    (hℓ : ∀ ⦃i j⦄, i ∈ s → j ∈ s → G.Adj ℓ i → G.Adj ℓ j → i = j) (h : Placed X s) :
    Placed X (insert ℓ s) := by
  classical
  obtain ⟨T, _, I, hI, hA⟩ := h
  let M (k : ℕ) : WithBot T := (Finset.univ.filter fun v : X.Pos ↦ v.1 ∈ s ∧
    ∃ p : Fin (X.word ℓ).length, (p : ℕ) < k ∧ X.assoc.Adj ⟨ℓ, p⟩ v).sup fun v ↦ ↑(I v).fst
  have le_M {p : Fin (X.word ℓ).length} {v : X.Pos} {k : ℕ} (hv : v.1 ∈ s) (hp : (p : ℕ) < k)
      (hpv : X.assoc.Adj ⟨ℓ, p⟩ v) : ((I v).fst : WithBot T) ≤ M k :=
    Finset.le_sup (f := fun v ↦ ((I v).fst : WithBot T))
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hv, p, hp, hpv⟩)
  have M_mono : Monotone M := fun k k' hk ↦ Finset.sup_le fun v hv ↦ by
    obtain ⟨-, hv, p, hp, hpv⟩ := Finset.mem_filter.1 hv
    exact le_M hv (hp.trans_le hk) hpv
  have lex_le {a b : WithBot T} {m n : ℕ} (h₁ : a ≤ b) (h₂ : m ≤ n) : toLex (a, m) ≤ toLex (b, n) :=
    Prod.Lex.toLex_mono (Prod.mk_le_mk.2 ⟨h₁, h₂⟩)
  let J (v : X.Pos) : NonemptyInterval (WithBot T ×ₗ ℕ) :=
    if v.1 = ℓ then ⟨(toLex (M v.2, v.2), toLex (M (v.2 + 1), v.2)),
      lex_le (M_mono (Nat.le_succ _)) le_rfl⟩
    else ⟨(toLex ((I v).fst, 0), toLex ((I v).snd, (X.word ℓ).length)),
      lex_le (WithBot.coe_le_coe.2 (I v).fst_le_snd) (Nat.zero_le _)⟩
  have hJ {q : Fin (X.word ℓ).length} {v : X.Pos} (hv : v.1 ∈ s) (hqv : X.assoc.Adj ⟨ℓ, q⟩ v) :
      (J ⟨ℓ, q⟩).Overlaps (J v) := by
    have hM : M q ≤ (I v).fst := Finset.sup_le fun w hw ↦ by
      obtain ⟨-, hw, p, hp, hpw⟩ := Finset.mem_filter.1 hw
      obtain ⟨j, r⟩ := w; obtain ⟨_, r'⟩ := v
      obtain rfl : j = _ := hℓ hw hv (hX hpw) (hX hqv)
      obtain hlt | rfl := (show r ≤ r' from @hNC ℓ j (p, r) hpw (q, r') hqv hp).lt_or_eq
      exacts [WithBot.coe_le_coe.2 ((I _).fst_le_snd.trans_lt (hI j hw hlt)).le, le_rfl]
    simp only [J, (fst_ne_of_adj hqv).symm, ↓reduceIte]
    exact ⟨lex_le (hM.trans (WithBot.coe_le_coe.2 (I v).fst_le_snd)) q.2.le,
      lex_le (le_M hv (Nat.lt_succ_self _) hqv) (Nat.zero_le _)⟩
  refine ⟨WithBot T ×ₗ ℕ, inferInstance, J, fun i hi p q hpq ↦ ?_, ?_⟩
  · obtain rfl | h := eq_or_ne ℓ i
    · simp only [J, ↓reduceIte]
      exact Prod.Lex.toLex_strictMono (Prod.mk_lt_mk.2
        (.inr ⟨M_mono (show (p : ℕ) + 1 ≤ q from hpq), hpq⟩))
    · simp only [J, h.symm, ↓reduceIte]
      exact Prod.Lex.toLex_lt_toLex.2 <| .inl <| WithBot.coe_lt_coe.2 <|
        hI i (hi.resolve_left h.symm) hpq
  · rintro ⟨i, p⟩ ⟨j, q⟩ hi hj h
    obtain rfl | hi' := eq_or_ne ℓ i
    · exact hJ (hj.resolve_left fun hj ↦ fst_ne_of_adj h hj.symm) h
    obtain rfl | hj' := eq_or_ne ℓ j
    · exact overlaps_symm (hJ (hi.resolve_left hi'.symm) h.symm)
    obtain ⟨h₁, h₂⟩ := hA (hi.resolve_left hi'.symm) (hj.resolve_left hj'.symm) h
    simp only [J, hi'.symm, hj'.symm, ↓reduceIte]
    exact ⟨lex_le (WithBot.coe_le_coe.2 h₁) (Nat.zero_le _),
      lex_le (WithBot.coe_le_coe.2 h₂) (Nat.zero_le _)⟩

/-- If lines join only tiers adjacent in a forest, a representation obeys the No-Crossing
Constraint iff it has an interval order. The tiers are placed one leaf at a time. -/
theorem noCrossing_iff_hasIntervalOrder_of_isAcyclic [Finite ι] {G : SimpleGraph ι}
    (hG : G.IsAcyclic) (hX : X.assoc ≤ G.comap Sigma.fst) :
    X.NoCrossing ↔ X.HasIntervalOrder := by
  classical
  refine ⟨fun h ↦ ?_, HasIntervalOrder.noCrossing⟩
  have := Fintype.ofFinite ι
  suffices ∀ s : Finset ι, Placed X s by
    obtain ⟨T, _, I, hI, hA⟩ := this .univ
    exact hasIntervalOrder_of_intervals I (fun i ↦ hI i (by simp)) fun _ _ ↦ hA (by simp) (by simp)
  intro s
  induction s using Finset.strongInduction with | H s ih => ?_
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact ⟨ℕ, inferInstance, fun _ ↦ .pure 0, by simp, by simp⟩
  have : Nonempty (s : Set ι) := hs.to_set.to_subtype
  obtain ⟨⟨ℓ, hℓ⟩, hleaf⟩ := (hG.induce s).exists_neighborSet_subsingleton
  have := (ih (s.erase ℓ) (Finset.erase_ssubset hℓ)).insert hX h (ℓ := ℓ) fun i j hi hj hi' hj' ↦
    congrArg Subtype.val <|
      @hleaf ⟨i, Finset.mem_of_mem_erase hi⟩ hi' ⟨j, Finset.mem_of_mem_erase hj⟩ hj'
  rwa [Finset.coe_erase, Set.insert_sdiff_singleton, Set.insert_eq_of_mem hℓ] at this

/-- On two tiers, which always form a forest, a representation obeys the No-Crossing
Constraint iff it has an interval order. -/
theorem noCrossing_iff_hasIntervalOrder {τ : Bool → Type*} {X : AR τ} :
    X.NoCrossing ↔ X.HasIntervalOrder :=
  noCrossing_iff_hasIntervalOrder_of_isAcyclic (G := ⊤) (.of_card_le_two (by simp))
    fun _ _ ↦ fst_ne_of_adj

/-- On a cycle of three tiers the converse fails: with each tier's first position linked to the
next tier's second, no two lines cross, yet the precedences chain from the last tier's first
position to the first tier's second, to which it is linked. -/
theorem exists_noCrossing_not_hasIntervalOrder :
    ∃ X : AR fun _ : Fin 3 ↦ Unit, X.NoCrossing ∧ ¬ X.HasIntervalOrder := by
  refine ⟨fromRel (fun _ ↦ [(), ()]) fun i j p q ↦ p = 0 ∧ q = 1 ∧ j = i + 1, by decide, ?_⟩
  rintro ⟨r, hr, htier, hadj⟩
  have h₀ := htier 0 (show (⟨0, by decide⟩ : Fin 2) < ⟨1, by decide⟩ by decide)
  have h₁ := htier 1 (show (⟨0, by decide⟩ : Fin 2) < ⟨1, by decide⟩ by decide)
  have h₂ := htier 2 (show (⟨0, by decide⟩ : Fin 2) < ⟨1, by decide⟩ by decide)
  rcases hr.two_plus_two h₂ h₁ with h | h
  · rcases hr.two_plus_two h h₀ with h' | h'
    · exact hadj (by decide) h'
    · exact hadj (by decide) h'
  · exact hadj (by decide) h

end AR

end Autosegmental
