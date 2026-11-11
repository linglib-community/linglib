/-
Copyright (c) 2026 The Linglib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Linglib contributors
-/
module

public import Linglib.Core.ModelTheory.QuantifierRank
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fintype.Pi
public import Mathlib.ModelTheory.Bundled

/-!
# Ehrenfeucht–Fraïssé games and finite-rank elementary equivalence

`[UPSTREAM]` candidate. Two structures are `n`-equivalent when they satisfy the same sentences of
quantifier rank `≤ n`, and elementarily equivalent when they are `n`-equivalent for every `n`.
Duplicator wins the `k`-round Ehrenfeucht–Fraïssé game from a pair of tuples when she can answer
every move for `k` rounds, back and forth, keeping the tuples alike. Such tuples satisfy the
same formulas of quantifier rank `≤ k`, and over a finite relational signature the converse
holds, witnessed by Hintikka formulas. This is the rank-bounded counterpart of mathlib's
`IsExtensionPair`.

## Main definitions

* `FirstOrder.Language.ElementarilyEquivalentUpTo`: `n`-equivalence of structures.
* `FirstOrder.Language.FODefinable`: definability of a class of structures within a class.
* `FirstOrder.Language.DuplicatorWins`: duplicator wins the `k`-round game from a pair of tuples.
* `FirstOrder.Language.gameNormal`, `FirstOrder.Language.hintikkaSet`: the game-normal formulas
  of each rank, finitely many over a finite relational signature.
* `FirstOrder.Language.hintikka`: the rank-`k` Hintikka formula of a tuple.

## Main results

* `FirstOrder.Language.not_foDefinable_of_elementarilyEquivalentUpTo`: the Ehrenfeucht–Fraïssé
  method for undefinability.
* `FirstOrder.Language.DuplicatorWins.realize_iff`: a winning position agrees on formulas of
  quantifier rank `≤ k`.
* `FirstOrder.Language.duplicatorWins_iff_realize_iff`,
  `FirstOrder.Language.elementarilyEquivalentUpTo_iff_duplicatorWins`: the converse over a finite
  relational signature.
* `FirstOrder.Language.foDefinable_iff_exists_elementarilyEquivalentUpTo`: over a finite relational
  signature, a class is definable within `K` iff it is closed under `n`-equivalence within `K` for
  some `n`.

## Implementation notes

Tuples are the bound variables of `L.BoundedFormula Empty n`, so the `Fin.snoc` in `realize_all`
is a round of the game and sentences are the case `n = 0`. As in Hodges's back-and-forth systems,
the atomic condition holds at every rank; Libkin states it at rank `0` only, which agrees on
nonempty structures (`duplicatorWins_succ_iff_of_nonempty`) but makes soundness fail on empty
ones, where a nullary relation symbol can tell two structures apart with no move to play. For the
same reason a game-normal formula of positive rank carries an atomic type, which Hodges's omit.

## References

* [libkin-2004]
* [hodges-1993]
-/

@[expose] public section

universe u v w w' w''

namespace FirstOrder.Language

open BoundedFormula CategoryTheory
open scoped FirstOrder

variable (L : Language.{u, v}) {M : Type w} {N : Type w'} {P : Type w''}
  [L.Structure M] [L.Structure N] [L.Structure P]

/-! ### `n`-equivalence and definability -/

/-- Two structures are elementarily equivalent up to `n`, or `n`-equivalent, when they satisfy the
same sentences of quantifier rank `≤ n`. -/
def ElementarilyEquivalentUpTo (n : ℕ) (M : Type w) (N : Type w') [L.Structure M]
    [L.Structure N] : Prop :=
  ∀ φ : L.Sentence, φ.quantifierRank ≤ n → (M ⊨ φ ↔ N ⊨ φ)

@[inherit_doc FirstOrder.Language.ElementarilyEquivalentUpTo]
scoped[FirstOrder] notation:25 A " ≅[" L ", " n "] " B:50 =>
  FirstOrder.Language.ElementarilyEquivalentUpTo L n A B

/-- A class `P` of structures is *first-order definable within* `K` when some sentence holds of
exactly the members of `P` among the structures in `K`. -/
def FODefinable (K P : Set (Bundled.{w} L.Structure)) : Prop :=
  ∃ φ : L.Sentence, ∀ M ∈ K, M ∈ P ↔ M ⊨ φ

variable {L} {k l n : ℕ}

namespace ElementarilyEquivalentUpTo

variable (L) in
@[refl] theorem refl (n : ℕ) (M : Type w) [L.Structure M] : M ≅[L, n] M := fun _ _ ↦ Iff.rfl

@[symm] theorem symm (h : M ≅[L, n] N) : N ≅[L, n] M := fun φ hφ ↦ (h φ hφ).symm

@[trans] theorem trans (h₁ : M ≅[L, n] N) (h₂ : N ≅[L, n] P) : M ≅[L, n] P :=
  fun φ hφ ↦ (h₁ φ hφ).trans (h₂ φ hφ)

theorem mono (hkn : k ≤ n) (h : M ≅[L, n] N) : M ≅[L, k] N :=
  fun φ hφ ↦ h φ (hφ.trans hkn)

end ElementarilyEquivalentUpTo

theorem elementarilyEquivalent_iff_forall_elementarilyEquivalentUpTo :
    M ≅[L] N ↔ ∀ n, M ≅[L, n] N :=
  ⟨fun h _ φ _ ↦ h.realize_sentence φ,
    fun h ↦ elementarilyEquivalent_iff.2 fun φ ↦ h φ.quantifierRank φ le_rfl⟩

/-- **The Ehrenfeucht–Fraïssé method.** If for every rank `n` some structure in `K` with
property `P` is `n`-equivalent to one in `K` without it, then `P` is not definable within `K`,
since a defining sentence would be fooled at its own quantifier rank. -/
theorem not_foDefinable_of_elementarilyEquivalentUpTo {K P : Set (Bundled.{w} L.Structure)}
    (h : ∀ n, ∃ M ∈ K, ∃ N ∈ K, (M ≅[L, n] N) ∧ M ∈ P ∧ N ∉ P) : ¬ L.FODefinable K P := by
  rintro ⟨φ, hφ⟩
  obtain ⟨M, hM, N, hN, hMN, hP, hnP⟩ := h φ.quantifierRank
  exact hnP ((hφ N hN).2 ((hMN φ le_rfl).1 ((hφ M hM).1 hP)))

/-! ### The Ehrenfeucht–Fraïssé game -/

variable (L) in
/-- Duplicator wins the `k`-round Ehrenfeucht–Fraïssé game from an `n`-tuple `v` of `M` and an
`n`-tuple `w` of `N` when the tuples satisfy the same atomic formulas and, with `k + 1` rounds
left, every element of either structure (*forth*, *back*) has an answer in the other extending
them to a position she wins with `k` rounds left. -/
def DuplicatorWins : ℕ → ∀ {n : ℕ}, (Fin n → M) → (Fin n → N) → Prop
  | 0, _, v, w => ∀ φ : L.BoundedFormula Empty _, φ.IsAtomic →
      (φ.Realize default v ↔ φ.Realize default w)
  | k + 1, _, v, w => (∀ φ : L.BoundedFormula Empty _, φ.IsAtomic →
      (φ.Realize default v ↔ φ.Realize default w)) ∧
      (∀ a, ∃ b, DuplicatorWins k (Fin.snoc v a) (Fin.snoc w b)) ∧
      ∀ b, ∃ a, DuplicatorWins k (Fin.snoc v a) (Fin.snoc w b)

variable {v : Fin n → M} {w : Fin n → N}

theorem duplicatorWins_zero_iff : L.DuplicatorWins 0 v w ↔
    ∀ φ : L.BoundedFormula Empty n, φ.IsAtomic → (φ.Realize default v ↔ φ.Realize default w) :=
  .rfl

theorem duplicatorWins_succ_iff : L.DuplicatorWins (k + 1) v w ↔ L.DuplicatorWins 0 v w ∧
    (∀ a, ∃ b, L.DuplicatorWins k (Fin.snoc v a) (Fin.snoc w b)) ∧
      ∀ b, ∃ a, L.DuplicatorWins k (Fin.snoc v a) (Fin.snoc w b) :=
  .rfl

namespace DuplicatorWins

theorem zero : ∀ {k n} {v : Fin n → M} {w : Fin n → N},
    L.DuplicatorWins k v w → L.DuplicatorWins 0 v w
  | 0, _, _, _, h => h
  | _ + 1, _, _, _, h => (duplicatorWins_succ_iff.1 h).1

theorem realize_iff_of_isAtomic (h : L.DuplicatorWins k v w) {φ : L.BoundedFormula Empty n}
    (hφ : φ.IsAtomic) : φ.Realize default v ↔ φ.Realize default w :=
  duplicatorWins_zero_iff.1 h.zero φ hφ

theorem forth (h : L.DuplicatorWins (k + 1) v w) (a : M) :
    ∃ b, L.DuplicatorWins k (Fin.snoc v a) (Fin.snoc w b) :=
  (duplicatorWins_succ_iff.1 h).2.1 a

theorem back (h : L.DuplicatorWins (k + 1) v w) (b : N) :
    ∃ a, L.DuplicatorWins k (Fin.snoc v a) (Fin.snoc w b) :=
  (duplicatorWins_succ_iff.1 h).2.2 b

theorem of_succ : ∀ {k n} {v : Fin n → M} {w : Fin n → N},
    L.DuplicatorWins (k + 1) v w → L.DuplicatorWins k v w
  | 0, _, _, _, h => h.zero
  | _ + 1, _, _, _, h => duplicatorWins_succ_iff.2 ⟨h.zero,
      fun a ↦ (h.forth a).imp fun _ ↦ of_succ, fun b ↦ (h.back b).imp fun _ ↦ of_succ⟩

theorem antitone (v : Fin n → M) (w : Fin n → N) : Antitone (L.DuplicatorWins · v w) :=
  antitone_nat_of_succ_le fun _ ↦ of_succ

theorem mono (hkl : k ≤ l) (h : L.DuplicatorWins l v w) : L.DuplicatorWins k v w :=
  DuplicatorWins.antitone v w hkl h

/-- Tuples from which duplicator wins `k` rounds satisfy the same formulas of quantifier rank
`≤ k`. Atomic formulas agree by the atomic condition, and quantified ones by the *back* and
*forth* moves. -/
theorem realize_iff : ∀ {n} {φ : L.BoundedFormula Empty n} {k} {v : Fin n → M} {w : Fin n → N},
    L.DuplicatorWins k v w → φ.quantifierRank ≤ k → (φ.Realize default v ↔ φ.Realize default w)
  | _, .falsum, _, _, _, _, _ => Iff.rfl
  | _, .equal _ _, _, _, _, h, _ => h.realize_iff_of_isAtomic (.equal _ _)
  | _, .rel _ _, _, _, _, h, _ => h.realize_iff_of_isAtomic (.rel _ _)
  | _, .imp _ _, _, _, _, h, hφ => by
      rw [quantifierRank_imp, max_le_iff] at hφ
      exact imp_congr (realize_iff h hφ.1) (realize_iff h hφ.2)
  | _, .all _, _ + 1, _, _, h, hφ => by
      rw [quantifierRank_all, Nat.add_le_add_iff_right] at hφ
      simp only [realize_all]
      exact ⟨fun hv b ↦ (h.back b).elim fun a hab ↦ (realize_iff hab hφ).1 (hv a),
        fun hw a ↦ (h.forth a).elim fun b hab ↦ (realize_iff hab hφ).2 (hw b)⟩

theorem elementarilyEquivalentUpTo
    (h : L.DuplicatorWins k (default : Fin 0 → M) (default : Fin 0 → N)) :
    M ≅[L, k] N :=
  fun _ hφ ↦ h.realize_iff hφ

theorem symm : ∀ {k n} {v : Fin n → M} {w : Fin n → N},
    L.DuplicatorWins k v w → L.DuplicatorWins k w v
  | 0, _, _, _, h => fun φ hφ ↦ (h.realize_iff_of_isAtomic hφ).symm
  | _ + 1, _, _, _, h => duplicatorWins_succ_iff.2 ⟨h.zero.symm,
      fun b ↦ (h.back b).imp fun _ ↦ symm, fun a ↦ (h.forth a).imp fun _ ↦ symm⟩

theorem trans : ∀ {k n} {u : Fin n → M} {v : Fin n → N} {w : Fin n → P},
    L.DuplicatorWins k u v → L.DuplicatorWins k v w → L.DuplicatorWins k u w
  | 0, _, _, _, _, h₁, h₂ => fun φ hφ ↦
      (h₁.realize_iff_of_isAtomic hφ).trans (h₂.realize_iff_of_isAtomic hφ)
  | _ + 1, _, _, _, _, h₁, h₂ => duplicatorWins_succ_iff.2 ⟨h₁.zero.trans h₂.zero,
      fun a ↦ let ⟨_, hb⟩ := h₁.forth a; let ⟨c, hc⟩ := h₂.forth _; ⟨c, hb.trans hc⟩,
      fun c ↦ let ⟨_, hb⟩ := h₂.back c; let ⟨a, ha⟩ := h₁.back _; ⟨a, ha.trans hb⟩⟩

end DuplicatorWins

theorem Equiv.duplicatorWins (f : M ≃[L] N) :
    ∀ (k : ℕ) {n} (v : Fin n → M), L.DuplicatorWins k v (f ∘ v)
  | 0, _, v => fun φ _ ↦ by
      rw [← StrongHomClass.realize_boundedFormula f φ (v := default) (xs := v),
        Subsingleton.elim (f ∘ default) default]
  | k + 1, _, v => duplicatorWins_succ_iff.2 ⟨f.duplicatorWins 0 v,
      fun a ↦ ⟨f a, by simpa [Fin.comp_snoc] using f.duplicatorWins k (Fin.snoc v a)⟩,
      fun b ↦ ⟨f.symm b, by
        simpa [Fin.comp_snoc] using f.duplicatorWins k (Fin.snoc v (f.symm b))⟩⟩

theorem DuplicatorWins.refl (k : ℕ) (v : Fin n → M) : L.DuplicatorWins k v v :=
  (Equiv.refl L M).duplicatorWins k v

/-- On a nonempty structure the back-and-forth condition alone characterizes [libkin-2004]'s `≃ₖ₊₁`
(p. 36; [hodges-1993] Lemma 3.3.1). -/
theorem duplicatorWins_succ_iff_of_nonempty [Nonempty M] :
    L.DuplicatorWins (k + 1) v w ↔
      (∀ a, ∃ b, L.DuplicatorWins k (Fin.snoc v a) (Fin.snoc w b)) ∧
        ∀ b, ∃ a, L.DuplicatorWins k (Fin.snoc v a) (Fin.snoc w b) := by
  refine ⟨fun h ↦ (duplicatorWins_succ_iff.1 h).2,
    fun h ↦ duplicatorWins_succ_iff.2 ⟨fun φ hφ ↦ ?_, h⟩⟩
  obtain ⟨b, hb⟩ := h.1 (Classical.arbitrary M)
  simpa [realize_liftAt_one_self, Fin.snoc_comp_castSucc] using
    hb.realize_iff_of_isAtomic (hφ.liftAt (k := 1) (m := n))

/-! ### Hintikka formulas and completeness -/

theorem Term.exists_eq_var [L.IsRelational] {α : Type*} [IsEmpty α] (t : L.Term (α ⊕ Fin n)) :
    ∃ i, t = &i := by
  rcases t with (x | i) | ⟨f, _⟩
  exacts [isEmptyElim x, ⟨i, rfl⟩, isEmptyElim f]

section Hintikka

variable (L)

/-- `AtomIndex n` indexes the atomic formulas in `n` bound variables of a relational language,
the equalities of two variables and the relation symbols applied to variables. -/
abbrev AtomIndex (n : ℕ) : Type _ :=
  (Fin n × Fin n) ⊕ (Σ R : (Σ l, L.Relations l), Fin R.1 → Fin n)

/-- The atomic formula with the given index. -/
def atom : L.AtomIndex n → L.BoundedFormula Empty n
  | .inl (i, j) => (&i).bdEqual &j
  | .inr ⟨⟨_, R⟩, f⟩ => R.boundedFormula fun i ↦ &(f i)

instance [Finite L.Symbols] : Finite (Σ l, L.Relations l) :=
  Finite.of_injective (Sum.inr : _ → L.Symbols) Sum.inr_injective

variable {L} in
theorem atom_isAtomic (i : L.AtomIndex n) : (L.atom i).IsAtomic := by
  cases i with
  | inl p => exact .equal _ _
  | inr p => exact .rel _ _

variable {L} in
theorem BoundedFormula.IsAtomic.exists_eq_atom [L.IsRelational] {φ : L.BoundedFormula Empty n}
    (hφ : φ.IsAtomic) : ∃ i, φ = L.atom i := by
  cases hφ with
  | equal t₁ t₂ =>
    obtain ⟨i, rfl⟩ := t₁.exists_eq_var
    obtain ⟨j, rfl⟩ := t₂.exists_eq_var
    exact ⟨.inl (i, j), rfl⟩
  | @rel l R ts =>
    choose f hf using fun i ↦ (ts i).exists_eq_var
    exact ⟨.inr ⟨⟨l, R⟩, f⟩, by simp [atom, Relations.boundedFormula, funext hf]⟩

variable [Finite L.Symbols]

open Classical in
/-- The atomic type `S` is the conjunction of the atoms in `S` and the negations of the others. -/
noncomputable def atomicType (S : Set (L.AtomIndex n)) : L.BoundedFormula Empty n :=
  iInf fun i ↦ if i ∈ S then L.atom i else (L.atom i).not

/-- The game-normal formula built from `θ₀` and a set `X` of formulas in one more variable says
that `θ₀` holds, each member of `X` is realized by some extension of the tuple, and every extension
realizes some member of `X` ([hodges-1993] (3.7), there without `θ₀`). -/
noncomputable def gameNormal (θ₀ : L.BoundedFormula Empty n)
    (X : Finset (L.BoundedFormula Empty (n + 1))) : L.BoundedFormula Empty n :=
  θ₀ ⊓ (iInf fun θ : X ↦ θ.1.ex) ⊓ (iSup fun θ : X ↦ θ.1).all

open Classical in
/-- `hintikkaSet k n` is the finite set of game-normal formulas of rank `k` in `n` variables: the
atomic types at rank `0`, and at rank `k + 1` the game-normal formulas built from an atomic type
and a set of game-normal formulas of rank `k` in `n + 1` variables. -/
noncomputable def hintikkaSet : (k n : ℕ) → Finset (L.BoundedFormula Empty n)
  | 0, n =>
      letI := Fintype.ofFinite (Set (L.AtomIndex n))
      Finset.univ.image L.atomicType
  | k + 1, n =>
      letI := Fintype.ofFinite (Set (L.AtomIndex n))
      (Finset.univ ×ˢ (hintikkaSet k (n + 1)).powerset).image fun p ↦
        L.gameNormal (L.atomicType p.1) p.2

open Classical in
/-- The game-normal formulas of rank `k` realized by the extensions of `v` by one element. -/
noncomputable def hintikkaExtensions (k : ℕ) (v : Fin n → M) :
    Finset (L.BoundedFormula Empty (n + 1)) :=
  (L.hintikkaSet k (n + 1)).filter fun θ ↦ ∃ a, θ.Realize default (Fin.snoc v a)

/-- The rank-`k` Hintikka formula of `v` is the game-normal formula of rank `k` it satisfies: its
atomic type, joined at rank `k + 1` to the game-normal formulas of rank `k` of its extensions. -/
noncomputable def hintikka : (k : ℕ) → {n : ℕ} → (Fin n → M) → L.BoundedFormula Empty n
  | 0, _, v => L.atomicType {i | (L.atom i).Realize default v}
  | k + 1, _, v => L.gameNormal (L.atomicType {i | (L.atom i).Realize default v})
      (L.hintikkaExtensions k v)

variable {L} {S : Set (L.AtomIndex n)} {θ θ₀ : L.BoundedFormula Empty n}
  {X : Finset (L.BoundedFormula Empty (n + 1))}

theorem realize_atomicType : (L.atomicType S).Realize default w ↔
    {i | (L.atom i).Realize default w} = S := by
  classical
  simp only [atomicType, realize_iInf, Set.ext_iff, Set.mem_ofPred_eq]
  refine forall_congr' fun i ↦ ?_
  split_ifs with hi <;> simp [hi]

theorem realize_atomicType_iff_duplicatorWins [L.IsRelational] (v : Fin n → M) (w : Fin n → N) :
    (L.atomicType {i | (L.atom i).Realize default v}).Realize default w ↔
      L.DuplicatorWins 0 v w := by
  rw [realize_atomicType, Set.ext_iff]
  exact ⟨fun h φ hφ ↦ by obtain ⟨i, rfl⟩ := hφ.exists_eq_atom; exact (h i).symm,
    fun h i ↦ (h _ (atom_isAtomic i)).symm⟩

theorem quantifierRank_atomicType (S : Set (L.AtomIndex n)) :
    (L.atomicType S).quantifierRank = 0 :=
  Nat.le_zero.1 <| quantifierRank_iInf_le fun i ↦ by
    split_ifs <;> simp [(atom_isAtomic i).quantifierRank_eq_zero]

omit [Finite L.Symbols] in
theorem realize_gameNormal : (L.gameNormal θ₀ X).Realize default w ↔ θ₀.Realize default w ∧
    (∀ θ ∈ X, ∃ b, θ.Realize default (Fin.snoc w b)) ∧
      ∀ b, ∃ θ ∈ X, θ.Realize default (Fin.snoc w b) := by
  simp only [gameNormal, realize_inf, realize_iInf, realize_iSup, realize_all, realize_ex,
    Subtype.forall, Subtype.exists, and_assoc, exists_prop]

omit [Finite L.Symbols] in
theorem quantifierRank_gameNormal_le (h₀ : θ₀.quantifierRank ≤ k + 1)
    (hX : ∀ θ ∈ X, θ.quantifierRank ≤ k) : (L.gameNormal θ₀ X).quantifierRank ≤ k + 1 := by
  simp only [gameNormal, quantifierRank_inf, quantifierRank_all, max_le_iff]
  exact ⟨⟨h₀, quantifierRank_iInf_le fun θ ↦ by
      rw [quantifierRank_ex]; exact Nat.succ_le_succ (hX _ θ.2)⟩,
    Nat.succ_le_succ (quantifierRank_iSup_le fun θ ↦ hX _ θ.2)⟩

theorem mem_hintikkaSet_zero : θ ∈ L.hintikkaSet 0 n ↔ ∃ S, L.atomicType S = θ := by
  simp [hintikkaSet]

theorem mem_hintikkaSet_succ : θ ∈ L.hintikkaSet (k + 1) n ↔
    ∃ S, ∃ X ⊆ L.hintikkaSet k (n + 1), L.gameNormal (L.atomicType S) X = θ := by
  simp [hintikkaSet]

theorem mem_hintikkaExtensions {θ : L.BoundedFormula Empty (n + 1)} :
    θ ∈ L.hintikkaExtensions k v ↔
      θ ∈ L.hintikkaSet k (n + 1) ∧ ∃ a, θ.Realize default (Fin.snoc v a) := by
  classical exact Finset.mem_filter

theorem quantifierRank_le_of_mem_hintikkaSet :
    ∀ {k n} {θ : L.BoundedFormula Empty n}, θ ∈ L.hintikkaSet k n → θ.quantifierRank ≤ k
  | 0, _, _, hθ => by
      obtain ⟨S, rfl⟩ := mem_hintikkaSet_zero.1 hθ
      exact (quantifierRank_atomicType S).le
  | k + 1, _, _, hθ => by
      obtain ⟨S, X, hX, rfl⟩ := mem_hintikkaSet_succ.1 hθ
      exact quantifierRank_gameNormal_le ((quantifierRank_atomicType S).le.trans (Nat.zero_le _))
        fun θ hθ ↦ quantifierRank_le_of_mem_hintikkaSet (hX hθ)

theorem hintikka_mem : ∀ (k : ℕ) {n} (v : Fin n → M), L.hintikka k v ∈ L.hintikkaSet k n
  | 0, _, _ => mem_hintikkaSet_zero.2 ⟨_, rfl⟩
  | _ + 1, _, _ =>
      mem_hintikkaSet_succ.2 ⟨_, _, fun _ h ↦ (mem_hintikkaExtensions.1 h).1, rfl⟩

theorem quantifierRank_hintikka_le (k : ℕ) (v : Fin n → M) : (L.hintikka k v).quantifierRank ≤ k :=
  quantifierRank_le_of_mem_hintikkaSet (hintikka_mem k v)

theorem realize_hintikka_self : ∀ (k : ℕ) {n} (v : Fin n → M), (L.hintikka k v).Realize default v
  | 0, _, _ => realize_atomicType.2 rfl
  | k + 1, _, v => realize_gameNormal.2 ⟨realize_hintikka_self 0 v,
      fun _ hθ ↦ (mem_hintikkaExtensions.1 hθ).2, fun a ↦ ⟨_, mem_hintikkaExtensions.2
        ⟨hintikka_mem k _, a, realize_hintikka_self k _⟩, realize_hintikka_self k _⟩⟩

/-- A tuple satisfies exactly one game-normal formula of each rank, its Hintikka formula
([hodges-1993] Theorem 3.3.2 (a)). -/
theorem eq_hintikka_of_realize : ∀ {k n} {θ : L.BoundedFormula Empty n} (u : Fin n → M),
    θ ∈ L.hintikkaSet k n → θ.Realize default u → θ = L.hintikka k u
  | 0, _, _, _, hθ, h => by
      obtain ⟨S, rfl⟩ := mem_hintikkaSet_zero.1 hθ
      exact congrArg _ (realize_atomicType.1 h).symm
  | k + 1, n, _, u, hθ, h => by
      obtain ⟨S, X, hX, rfl⟩ := mem_hintikkaSet_succ.1 hθ
      obtain ⟨h₀, h₁, h₂⟩ := realize_gameNormal.1 h
      obtain rfl := realize_atomicType.1 h₀
      change L.gameNormal _ X = L.gameNormal _ _
      congr 1
      ext θ'
      rw [mem_hintikkaExtensions]
      refine ⟨fun hθ' ↦ ⟨hX hθ', h₁ θ' hθ'⟩, fun ⟨hθ', a, ha⟩ ↦ ?_⟩
      obtain ⟨θ'', hθ'', ha''⟩ := h₂ a
      rwa [eq_hintikka_of_realize _ hθ' ha, ← eq_hintikka_of_realize _ (hX hθ'') ha'']

variable [L.IsRelational]

/-- The Hintikka formula of `v` holds of `w` iff duplicator wins `k` rounds from the tuples
([hodges-1993] Theorem 3.3.2 (b)). -/
theorem realize_hintikka_iff : ∀ {k n} (v : Fin n → M) (w : Fin n → N),
    (L.hintikka k v).Realize default w ↔ L.DuplicatorWins k v w
  | 0, _, v, w => realize_atomicType_iff_duplicatorWins v w
  | k + 1, n, v, w => by
      change (L.gameNormal _ _).Realize default w ↔ _
      rw [realize_gameNormal, realize_atomicType_iff_duplicatorWins]
      rw [duplicatorWins_succ_iff]
      refine ⟨fun ⟨h₀, h₁, h₂⟩ ↦ ⟨h₀, fun a ↦ ?_, fun b ↦ ?_⟩,
        fun ⟨h₀, hf, hb⟩ ↦ ⟨h₀, fun θ hθ ↦ ?_, fun b ↦ ?_⟩⟩
      · obtain ⟨b, hb⟩ := h₁ _ (mem_hintikkaExtensions.2
          ⟨hintikka_mem k _, a, realize_hintikka_self k _⟩)
        exact ⟨b, (realize_hintikka_iff _ _).1 hb⟩
      · obtain ⟨θ, hθ, hb⟩ := h₂ b
        obtain ⟨hθ, a, ha⟩ := mem_hintikkaExtensions.1 hθ
        exact ⟨a, (realize_hintikka_iff _ _).1 (by rwa [← eq_hintikka_of_realize _ hθ ha])⟩
      · obtain ⟨hθ, a, ha⟩ := mem_hintikkaExtensions.1 hθ
        obtain ⟨b, hb⟩ := hf a
        exact ⟨b, eq_hintikka_of_realize _ hθ ha ▸ (realize_hintikka_iff _ _).2 hb⟩
      · obtain ⟨a, ha⟩ := hb b
        exact ⟨_, mem_hintikkaExtensions.2 ⟨hintikka_mem k _, a, realize_hintikka_self k _⟩,
          (realize_hintikka_iff _ _).2 ha⟩
termination_by k _ => k
decreasing_by all_goals omega

/-- Duplicator wins `k` rounds from two tuples iff they satisfy the same formulas of quantifier rank
at most `k` ([libkin-2004] Theorem 3.18). -/
theorem duplicatorWins_iff_realize_iff (v : Fin n → M) (w : Fin n → N) :
    L.DuplicatorWins k v w ↔
      ∀ φ : L.BoundedFormula Empty n, φ.quantifierRank ≤ k →
        (φ.Realize default v ↔ φ.Realize default w) :=
  ⟨fun h _ hφ ↦ h.realize_iff hφ, fun h ↦ (realize_hintikka_iff v w).1
    ((h _ (quantifierRank_hintikka_le k v)).1 (realize_hintikka_self k v))⟩

theorem elementarilyEquivalentUpTo_iff_duplicatorWins :
    (M ≅[L, k] N) ↔ L.DuplicatorWins k (default : Fin 0 → M) (default : Fin 0 → N) :=
  ⟨fun h ↦ (duplicatorWins_iff_realize_iff _ _).2 fun φ hφ ↦ h φ hφ,
    DuplicatorWins.elementarilyEquivalentUpTo⟩

/-- A class is first-order definable within `K` iff it is closed under `k`-equivalence within `K`
for some `k` ([libkin-2004] Corollary 3.17). -/
theorem foDefinable_iff_exists_elementarilyEquivalentUpTo {K P : Set (Bundled.{w} L.Structure)} :
    L.FODefinable K P ↔ ∃ k, ∀ M ∈ K, ∀ N ∈ K, (M ≅[L, k] N) → M ∈ P → N ∈ P := by
  classical
  refine ⟨fun ⟨φ, hφ⟩ ↦ ⟨φ.quantifierRank, fun M hM N hN h hP ↦ (hφ N hN).2 ((h φ le_rfl).1
    ((hφ M hM).1 hP))⟩, fun ⟨k, hk⟩ ↦ ⟨iSup fun θ : (L.hintikkaSet k 0).filter
      (fun θ ↦ ∃ N ∈ K, N ∈ P ∧ θ.Realize (default : Empty → N) default) ↦ θ.1,
        fun M hM ↦ ?_⟩⟩
  simp only [Sentence.Realize, Formula.Realize, realize_iSup, Subtype.exists, Finset.mem_filter]
  refine ⟨fun hP ↦ ⟨_, ⟨hintikka_mem k default, M, hM, hP, realize_hintikka_self k _⟩,
    realize_hintikka_self k _⟩, fun ⟨θ, ⟨hθ, N, hN, hP, hNθ⟩, hMθ⟩ ↦ ?_⟩
  obtain rfl := eq_hintikka_of_realize _ hθ hNθ
  exact hk N hN M hM ((realize_hintikka_iff _ _).1 hMθ).elementarilyEquivalentUpTo hP

end Hintikka

end FirstOrder.Language
