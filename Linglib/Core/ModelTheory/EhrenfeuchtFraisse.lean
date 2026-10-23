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
nonempty structures (`duplicatorWins_succ_iff`) but makes soundness fail on empty ones.

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
  ∀ φ : L.Sentence, φ.qr ≤ n → (M ⊨ φ ↔ N ⊨ φ)

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
@[refl] theorem refl (n : ℕ) (M : Type w) [L.Structure M] : M ≅[L, n] M := fun _ _ => Iff.rfl

@[symm] theorem symm (h : M ≅[L, n] N) : N ≅[L, n] M := fun φ hφ => (h φ hφ).symm

@[trans] theorem trans (h₁ : M ≅[L, n] N) (h₂ : N ≅[L, n] P) : M ≅[L, n] P :=
  fun φ hφ => (h₁ φ hφ).trans (h₂ φ hφ)

theorem mono (hkn : k ≤ n) (h : M ≅[L, n] N) : M ≅[L, k] N :=
  fun φ hφ => h φ (hφ.trans hkn)

end ElementarilyEquivalentUpTo

theorem elementarilyEquivalent_iff_forall_elementarilyEquivalentUpTo :
    M ≅[L] N ↔ ∀ n, M ≅[L, n] N :=
  ⟨fun h _ φ _ => h.realize_sentence φ,
    fun h => elementarilyEquivalent_iff.2 fun φ => h φ.qr φ le_rfl⟩

theorem not_foDefinable_of_elementarilyEquivalentUpTo {K P : Set (Bundled.{w} L.Structure)}
    (h : ∀ n, ∃ M ∈ K, ∃ N ∈ K, (M ≅[L, n] N) ∧ M ∈ P ∧ N ∉ P) : ¬ L.FODefinable K P := by
  rintro ⟨φ, hφ⟩
  obtain ⟨M, hM, N, hN, hMN, hP, hnP⟩ := h φ.qr
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

namespace DuplicatorWins

theorem zero : ∀ {k n} {v : Fin n → M} {w : Fin n → N},
    L.DuplicatorWins k v w → L.DuplicatorWins 0 v w
  | 0, _, _, _, h => h
  | _ + 1, _, _, _, h => h.1

theorem realize_iff_of_isAtomic (h : L.DuplicatorWins k v w) {φ : L.BoundedFormula Empty n}
    (hφ : φ.IsAtomic) : φ.Realize default v ↔ φ.Realize default w :=
  h.zero φ hφ

theorem forth (h : L.DuplicatorWins (k + 1) v w) (a : M) :
    ∃ b, L.DuplicatorWins k (Fin.snoc v a) (Fin.snoc w b) := h.2.1 a

theorem back (h : L.DuplicatorWins (k + 1) v w) (b : N) :
    ∃ a, L.DuplicatorWins k (Fin.snoc v a) (Fin.snoc w b) := h.2.2 b

theorem of_succ : ∀ {k n} {v : Fin n → M} {w : Fin n → N},
    L.DuplicatorWins (k + 1) v w → L.DuplicatorWins k v w
  | 0, _, _, _, h => h.1
  | _ + 1, _, _, _, h => ⟨h.1, fun a => (h.forth a).imp fun _ => of_succ,
      fun b => (h.back b).imp fun _ => of_succ⟩

theorem antitone (v : Fin n → M) (w : Fin n → N) : Antitone (L.DuplicatorWins · v w) :=
  antitone_nat_of_succ_le fun _ => of_succ

theorem mono (hkl : k ≤ l) (h : L.DuplicatorWins l v w) : L.DuplicatorWins k v w :=
  DuplicatorWins.antitone v w hkl h

theorem realize_iff : ∀ {n} {φ : L.BoundedFormula Empty n} {k} {v : Fin n → M} {w : Fin n → N},
    L.DuplicatorWins k v w → φ.qr ≤ k → (φ.Realize default v ↔ φ.Realize default w)
  | _, .falsum, _, _, _, _, _ => Iff.rfl
  | _, .equal _ _, _, _, _, h, _ => h.realize_iff_of_isAtomic (.equal _ _)
  | _, .rel _ _, _, _, _, h, _ => h.realize_iff_of_isAtomic (.rel _ _)
  | _, .imp _ _, _, _, _, h, hφ => by
      rw [qr_imp, max_le_iff] at hφ
      exact imp_congr (realize_iff h hφ.1) (realize_iff h hφ.2)
  | _, .all _, _ + 1, _, _, h, hφ => by
      rw [qr_all, Nat.add_le_add_iff_right] at hφ
      simp only [realize_all]
      exact ⟨fun hv b => (h.back b).elim fun a hab => (realize_iff hab hφ).1 (hv a),
        fun hw a => (h.forth a).elim fun b hab => (realize_iff hab hφ).2 (hw b)⟩

theorem elementarilyEquivalentUpTo
    (h : L.DuplicatorWins k (default : Fin 0 → M) (default : Fin 0 → N)) :
    M ≅[L, k] N :=
  fun _ hφ => h.realize_iff hφ

theorem symm : ∀ {k n} {v : Fin n → M} {w : Fin n → N},
    L.DuplicatorWins k v w → L.DuplicatorWins k w v
  | 0, _, _, _, h => fun φ hφ => (h φ hφ).symm
  | _ + 1, _, _, _, h => ⟨fun φ hφ => (h.1 φ hφ).symm, fun b => (h.back b).imp fun _ => symm,
      fun a => (h.forth a).imp fun _ => symm⟩

theorem trans : ∀ {k n} {u : Fin n → M} {v : Fin n → N} {w : Fin n → P},
    L.DuplicatorWins k u v → L.DuplicatorWins k v w → L.DuplicatorWins k u w
  | 0, _, _, _, _, h₁, h₂ => fun φ hφ => (h₁ φ hφ).trans (h₂ φ hφ)
  | _ + 1, _, _, _, _, h₁, h₂ => ⟨fun φ hφ => (h₁.1 φ hφ).trans (h₂.1 φ hφ),
      fun a => let ⟨_, hb⟩ := h₁.forth a; let ⟨c, hc⟩ := h₂.forth _; ⟨c, hb.trans hc⟩,
      fun c => let ⟨_, hb⟩ := h₂.back c; let ⟨a, ha⟩ := h₁.back _; ⟨a, ha.trans hb⟩⟩

end DuplicatorWins

theorem Equiv.duplicatorWins (f : M ≃[L] N) :
    ∀ (k : ℕ) {n} (v : Fin n → M), L.DuplicatorWins k v (f ∘ v)
  | 0, _, v => fun φ _ => by
      rw [← StrongHomClass.realize_boundedFormula f φ (v := default) (xs := v),
        Subsingleton.elim (f ∘ default) default]
  | k + 1, _, v => ⟨f.duplicatorWins 0 v,
      fun a => ⟨f a, by simpa [Fin.comp_snoc] using f.duplicatorWins k (Fin.snoc v a)⟩,
      fun b => ⟨f.symm b, by
        simpa [Fin.comp_snoc] using f.duplicatorWins k (Fin.snoc v (f.symm b))⟩⟩

theorem DuplicatorWins.refl (k : ℕ) (v : Fin n → M) : L.DuplicatorWins k v v :=
  (Equiv.refl L M).duplicatorWins k v

/-- On a nonempty structure the atomic condition at rank `k + 1` follows from *forth*, so the
relation is [libkin-2004]'s `≃ₖ₊₁` (p. 36) and [hodges-1993] Lemma 3.3.1. -/
theorem duplicatorWins_succ_iff [Nonempty M] :
    L.DuplicatorWins (k + 1) v w ↔
      (∀ a, ∃ b, L.DuplicatorWins k (Fin.snoc v a) (Fin.snoc w b)) ∧
        ∀ b, ∃ a, L.DuplicatorWins k (Fin.snoc v a) (Fin.snoc w b) := by
  refine ⟨fun h => h.2, fun h => ⟨fun φ hφ => ?_, h.1, h.2⟩⟩
  obtain ⟨b, hb⟩ := h.1 (Classical.arbitrary M)
  simpa [realize_liftAt_one_self, Fin.snoc_comp_castSucc] using
    hb.realize_iff_of_isAtomic (hφ.liftAt (k := 1) (m := n))

/-! ### Hintikka formulas and completeness -/

section Hintikka

variable (L)

/-- `AtomIndex n` indexes the atomic formulas in `n` bound variables of a relational language,
the equalities of two variables and the relation symbols applied to variables. -/
abbrev AtomIndex (n : ℕ) : Type _ :=
  (Fin n × Fin n) ⊕ (Σ R : (Σ l, L.Relations l), Fin R.1 → Fin n)

/-- The atomic formula with the given index. -/
def atom : L.AtomIndex n → L.BoundedFormula Empty n
  | .inl (i, j) => (&i).bdEqual &j
  | .inr ⟨⟨_, R⟩, f⟩ => R.boundedFormula fun i => &(f i)

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
  have hvar : ∀ t : L.Term (Empty ⊕ Fin n), ∃ i, t = &i := by
    rintro (⟨x | i⟩ | ⟨f, _⟩)
    exacts [x.elim, ⟨i, rfl⟩, isEmptyElim f]
  cases hφ with
  | equal t₁ t₂ =>
    obtain ⟨i, rfl⟩ := hvar t₁
    obtain ⟨j, rfl⟩ := hvar t₂
    exact ⟨.inl (i, j), rfl⟩
  | @rel l R ts =>
    choose f hf using fun i => hvar (ts i)
    exact ⟨.inr ⟨⟨l, R⟩, f⟩, by simp [atom, Relations.boundedFormula, funext hf]⟩

variable [Finite L.Symbols]

open Classical in
/-- The atomic type of a tuple is the conjunction of the atoms it satisfies and the negations of
the others. -/
noncomputable def atomicType (v : Fin n → M) : L.BoundedFormula Empty n :=
  iInf fun i : L.AtomIndex n => if (L.atom i).Realize default v then L.atom i else (L.atom i).not

open Classical in
/-- `hintikkaSet k n` is the finite set of game-normal formulas of rank `k` in `n` variables. At
rank `0` they are the atomic types. At rank `k + 1` each joins an atomic type to a set `X` of
rank-`k` formulas in `n + 1` variables, saying that each member of `X` is realized by some
extension and every extension realizes some member of `X`. -/
noncomputable def hintikkaSet : (k n : ℕ) → Finset (L.BoundedFormula Empty n)
  | 0, n =>
      letI := Fintype.ofFinite (L.AtomIndex n → Bool)
      Finset.univ.image fun s : L.AtomIndex n → Bool =>
        iInf fun i => if s i then L.atom i else (L.atom i).not
  | k + 1, n =>
      (hintikkaSet 0 n ×ˢ (hintikkaSet k (n + 1)).powerset).image fun p =>
        p.1 ⊓ (iInf fun θ : p.2 => θ.1.ex) ⊓ (iSup fun θ : p.2 => θ.1).all

open Classical in
/-- The rank-`k` Hintikka formula of `v` is the game-normal formula of rank `k` it satisfies. -/
noncomputable def hintikka : (k : ℕ) → {n : ℕ} → (Fin n → M) →
    L.BoundedFormula Empty n
  | 0, _, v => L.atomicType v
  | k + 1, n, v =>
      L.atomicType v ⊓
        (iInf fun θ : (L.hintikkaSet k (n + 1)).filter
            (fun θ => ∃ a, θ.Realize default (Fin.snoc v a)) => θ.1.ex) ⊓
        (iSup fun θ : (L.hintikkaSet k (n + 1)).filter
            (fun θ => ∃ a, θ.Realize default (Fin.snoc v a)) => θ.1).all

variable {L}

theorem realize_atomicType_iff [L.IsRelational] (v : Fin n → M) (w : Fin n → N) :
    (L.atomicType v).Realize default w ↔ L.DuplicatorWins 0 v w := by
  classical
  simp only [atomicType, realize_iInf]
  refine ⟨fun h φ hφ => ?_, fun h i => ?_⟩
  · obtain ⟨i, rfl⟩ := hφ.exists_eq_atom
    have := h i
    split_ifs at this with hi
    exacts [iff_of_true hi this, iff_of_false hi (realize_not.1 this)]
  · split_ifs with hi
    exacts [(h _ (atom_isAtomic i)).1 hi, realize_not.2 fun hw => hi ((h _ (atom_isAtomic i)).2 hw)]

theorem qr_atomicType (v : Fin n → M) : (L.atomicType v).qr = 0 :=
  Nat.le_zero.1 <| qr_iInf_le fun i => by split_ifs <;> simp [(atom_isAtomic i).qr_eq_zero]

theorem qr_le_of_mem_hintikkaSet :
    ∀ {k n} {θ : L.BoundedFormula Empty n}, θ ∈ L.hintikkaSet k n → θ.qr ≤ k
  | 0, n, θ, hθ => by
      classical
      unfold hintikkaSet at hθ
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hθ
      exact qr_iInf_le fun i => by split_ifs <;> simp [(atom_isAtomic i).qr_eq_zero]
  | k + 1, n, θ, hθ => by
      classical
      unfold hintikkaSet at hθ
      obtain ⟨⟨θ₀, X⟩, hp, rfl⟩ := Finset.mem_image.1 hθ
      rw [Finset.mem_product, Finset.mem_powerset] at hp
      simp only [qr_inf, qr_all, max_le_iff]
      refine ⟨⟨(qr_le_of_mem_hintikkaSet hp.1).trans k.succ.zero_le, qr_iInf_le fun θ' => ?_⟩,
        Nat.succ_le_succ (qr_iSup_le fun θ' => qr_le_of_mem_hintikkaSet (hp.2 θ'.2))⟩
      rw [qr_ex]
      exact Nat.succ_le_succ (qr_le_of_mem_hintikkaSet (hp.2 θ'.2))

theorem hintikka_mem : ∀ (k : ℕ) {n} (v : Fin n → M), L.hintikka k v ∈ L.hintikkaSet k n
  | 0, n, v => by
      classical
      unfold hintikkaSet hintikka atomicType
      let _ := Fintype.ofFinite (L.AtomIndex n → Bool)
      refine Finset.mem_image.2 ⟨fun i => decide ((L.atom i).Realize default v),
        Finset.mem_univ _, congrArg _ (funext fun i => ?_)⟩
      simp only [decide_eq_true_eq]
  | k + 1, n, v => by
      classical
      unfold hintikkaSet hintikka
      exact Finset.mem_image.2 ⟨(L.atomicType v, _), Finset.mem_product.2
        ⟨hintikka_mem 0 v, Finset.mem_powerset.2 (Finset.filter_subset _ _)⟩, rfl⟩

theorem qr_hintikka_le (k : ℕ) (v : Fin n → M) : (L.hintikka k v).qr ≤ k :=
  qr_le_of_mem_hintikkaSet (hintikka_mem k v)

/-- A tuple satisfies exactly one game-normal formula of each rank ([hodges-1993]
Theorem 3.3.2 (a)), so any member of `hintikkaSet k n` it satisfies is its Hintikka formula. -/
theorem eq_hintikka_of_realize : ∀ {k n} {θ : L.BoundedFormula Empty n} (u : Fin n → M),
    θ ∈ L.hintikkaSet k n → θ.Realize default u → θ = L.hintikka k u
  | 0, n, θ, u, hθ, h => by
      classical
      unfold hintikkaSet at hθ
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hθ
      simp only [realize_iInf] at h
      refine congrArg _ (funext fun i => ?_)
      have hi := h i
      cases hs : s i <;>
        simp only [hs, Bool.false_eq_true, ite_true, ite_false, realize_not] at hi ⊢ <;> simp [hi]
  | k + 1, n, θ, u, hθ, h => by
      classical
      unfold hintikkaSet at hθ
      obtain ⟨⟨θ₀, X⟩, hp, rfl⟩ := Finset.mem_image.1 hθ
      rw [Finset.mem_product, Finset.mem_powerset] at hp
      simp only [realize_inf, realize_iInf, realize_iSup, realize_all, realize_ex,
        Subtype.forall, Subtype.exists] at h
      obtain ⟨⟨h₀, h₁⟩, h₂⟩ := h
      obtain rfl := eq_hintikka_of_realize u hp.1 h₀
      have hX : X = (L.hintikkaSet k (n + 1)).filter
          (fun θ => ∃ a, θ.Realize default (Fin.snoc u a)) := by
        ext θ'
        rw [Finset.mem_filter]
        refine ⟨fun hX => ⟨hp.2 hX, h₁ θ' hX⟩, fun ⟨hθ', a, ha⟩ => ?_⟩
        obtain ⟨θ'', hθ'', ha''⟩ := h₂ a
        rw [eq_hintikka_of_realize _ hθ' ha, ← eq_hintikka_of_realize _ (hp.2 hθ'') ha'']
        exact hθ''
      subst hX
      rfl

variable [L.IsRelational]

theorem realize_hintikka_self : ∀ (k : ℕ) {n} (v : Fin n → M), (L.hintikka k v).Realize default v
  | 0, _, v => (realize_atomicType_iff v v).2 (DuplicatorWins.refl 0 v)
  | k + 1, n, v => by
      classical
      simp only [hintikka, realize_inf, realize_iInf, realize_iSup, realize_all, realize_ex,
        Subtype.forall, Subtype.exists, Finset.mem_filter]
      exact ⟨⟨realize_hintikka_self 0 v, fun θ ⟨_, a, ha⟩ => ⟨a, ha⟩⟩,
        fun a => ⟨_, ⟨hintikka_mem k _, a, realize_hintikka_self k _⟩, realize_hintikka_self k _⟩⟩

/-- The Hintikka formula of `v` holds of `w` iff duplicator wins `k` rounds from the tuples
([hodges-1993] Theorem 3.3.2 (b)). -/
theorem realize_hintikka_iff : ∀ {k n} (v : Fin n → M) (w : Fin n → N),
    (L.hintikka k v).Realize default w ↔ L.DuplicatorWins k v w
  | 0, _, v, w => realize_atomicType_iff v w
  | k + 1, n, v, w => by
      classical
      simp only [hintikka, realize_inf, realize_atomicType_iff, realize_iInf, realize_iSup,
        realize_all, realize_ex, Subtype.forall, Subtype.exists, Finset.mem_filter, DuplicatorWins,
        and_assoc]
      refine and_congr_right fun _ => ⟨fun ⟨h₁, h₂⟩ => ⟨fun a => ?_, fun b => ?_⟩,
        fun ⟨h₁, h₂⟩ => ⟨fun θ ⟨hθ, a, ha⟩ => ?_, fun b => ?_⟩⟩
      · obtain ⟨b, hb⟩ := h₁ _ ⟨hintikka_mem k _, a, realize_hintikka_self k _⟩
        exact ⟨b, (realize_hintikka_iff _ _).1 hb⟩
      · obtain ⟨θ, ⟨hθ, a, ha⟩, hb⟩ := h₂ b
        refine ⟨a, (realize_hintikka_iff _ _).1 ?_⟩
        rwa [← eq_hintikka_of_realize _ hθ ha]
      · obtain ⟨b, hb⟩ := h₁ a
        exact ⟨b, eq_hintikka_of_realize _ hθ ha ▸ (realize_hintikka_iff _ _).2 hb⟩
      · obtain ⟨a, ha⟩ := h₂ b
        exact ⟨_, ⟨hintikka_mem k _, a, realize_hintikka_self k _⟩,
          (realize_hintikka_iff _ _).2 ha⟩
termination_by k _ => k
decreasing_by all_goals omega

/-- Over a finite relational signature, duplicator wins `k` rounds from two tuples iff they
satisfy the same formulas of quantifier rank `≤ k` ([libkin-2004] Theorem 3.18). -/
theorem duplicatorWins_iff_realize_iff (v : Fin n → M) (w : Fin n → N) :
    L.DuplicatorWins k v w ↔
      ∀ φ : L.BoundedFormula Empty n, φ.qr ≤ k → (φ.Realize default v ↔ φ.Realize default w) :=
  ⟨fun h _ hφ => h.realize_iff hφ, fun h => (realize_hintikka_iff v w).1
    ((h _ (qr_hintikka_le k v)).1 (realize_hintikka_self k v))⟩

theorem elementarilyEquivalentUpTo_iff_duplicatorWins :
    (M ≅[L, k] N) ↔ L.DuplicatorWins k (default : Fin 0 → M) (default : Fin 0 → N) :=
  ⟨fun h => (duplicatorWins_iff_realize_iff _ _).2 fun φ hφ => h φ hφ,
    DuplicatorWins.elementarilyEquivalentUpTo⟩

/-- Over a finite relational signature, a class is first-order definable within `K` iff, for some
`k`, it is closed under `k`-equivalence within `K` ([libkin-2004] Corollary 3.17). The defining
sentence is the disjunction of the rank-`k` Hintikka sentences of its members. -/
theorem foDefinable_iff_exists_elementarilyEquivalentUpTo {K P : Set (Bundled.{w} L.Structure)} :
    L.FODefinable K P ↔ ∃ k, ∀ M ∈ K, ∀ N ∈ K, (M ≅[L, k] N) → M ∈ P → N ∈ P := by
  classical
  refine ⟨fun ⟨φ, hφ⟩ => ⟨φ.qr, fun M hM N hN h hP => (hφ N hN).2 ((h φ le_rfl).1
    ((hφ M hM).1 hP))⟩, fun ⟨k, hk⟩ => ⟨iSup fun θ : (L.hintikkaSet k 0).filter
      (fun θ => ∃ N ∈ K, N ∈ P ∧ θ.Realize (default : Empty → N) default) => θ.1,
        fun M hM => ?_⟩⟩
  simp only [Sentence.Realize, Formula.Realize, realize_iSup, Subtype.exists, Finset.mem_filter]
  refine ⟨fun hP => ⟨_, ⟨hintikka_mem k default, M, hM, hP, realize_hintikka_self k _⟩,
    realize_hintikka_self k _⟩, fun ⟨θ, ⟨hθ, N, hN, hP, hNθ⟩, hMθ⟩ => ?_⟩
  obtain rfl := eq_hintikka_of_realize _ hθ hNθ
  exact hk N hN M hM ((realize_hintikka_iff _ _).1 hMθ).elementarilyEquivalentUpTo hP

end Hintikka

end FirstOrder.Language
