module

public import Linglib.Core.ModelTheory.EhrenfeuchtFraisse
public import Linglib.Core.ModelTheory.Graph
public import Linglib.Core.ModelTheory.Lindstrom
public import Linglib.Core.ModelTheory.Monadic
public import Mathlib.Algebra.Order.Group.Abs

/-!
# First-order logic with monadic quantifiers and the bijective game

`[UPSTREAM]` candidate. This file defines `FO(Mon)`, first-order logic with every monadic
Lindström quantifier, and Hella's bijective Ehrenfeucht–Fraïssé game for it. A quantifier `Q` over
`m` predicates binds one variable in `m` formulas, and holds when the domain, with the predicates
interpreted as the extensions of the formulas, belongs to `Q`. In each round of the game,
duplicator chooses a bijection between the domains, spoiler chooses an element, and its image is
the answer. If duplicator wins `k` rounds, the two positions satisfy the same `FO(Mon)` formulas
of quantifier rank `≤ k`.

## Main definitions

* `FirstOrder.Language.MonFormula L n`: formulas of `FO(Mon)` with `n` free variables, with
  satisfaction `MonFormula.Realize` and quantifier rank `MonFormula.qr`.
* `FirstOrder.Language.MonDefinable K P`: some sentence of `FO(Mon)` defines `P` within `K`.
* `FirstOrder.Language.DuplicatorWinsBijective`: duplicator wins the `k`-round bijective game.

## Main results

* `FirstOrder.Language.DuplicatorWinsBijective.realize_iff`: a winning position agrees on the
  `FO(Mon)` formulas of quantifier rank `≤ k`.
* `FirstOrder.Language.not_monDefinable_of_duplicatorWinsBijective`: the game method for
  undefinability in `FO(Mon)`.
* `FirstOrder.Language.duplicatorWinsBijective_successor`: the successor graphs of two
  permutations of equinumerous finite sets with all cycles of length at least `2 ^ r` are not
  told apart in `r` rounds.

## References

* [peters-westerstahl-2006]
-/

@[expose] public section

universe u v w

namespace FirstOrder.Language

open CategoryTheory
open scoped FirstOrder

variable (L : Language.{u, v})

/-- Formulas of first-order logic with all monadic quantifiers, `FO(Mon)`, with `n` free
variables. Besides equations and relations between terms, falsity and implication, a monadic
quantifier `Q` over `m` predicates binds a new variable in `m` formulas. -/
inductive MonFormula : ℕ → Type (max u v (w + 1))
  | equal {n : ℕ} (t₁ t₂ : L.Term (Empty ⊕ Fin n)) : MonFormula n
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (Empty ⊕ Fin n)) : MonFormula n
  | falsum {n : ℕ} : MonFormula n
  | imp {n : ℕ} (φ ψ : MonFormula n) : MonFormula n
  | quant {n m : ℕ} (Q : LindstromQuantifier.{0, 0, w} (Language.monadic (Fin m)))
      (ψ : Fin m → MonFormula (n + 1)) : MonFormula n

variable {L}

namespace MonFormula

variable {M : Type w} [L.Structure M]

/-- Satisfaction of a formula of `FO(Mon)` under an assignment of its free variables. A monadic
quantifier holds when the domain, with each predicate interpreted as the extension of the
corresponding formula in the bound variable, belongs to the quantifier. -/
def Realize : ∀ {n}, L.MonFormula n → (Fin n → M) → Prop
  | _, equal t₁ t₂, v => t₁.realize (Sum.elim default v) = t₂.realize (Sum.elim default v)
  | _, rel R ts, v => Structure.RelMap R fun i ↦ (ts i).realize (Sum.elim default v)
  | _, falsum, _ => False
  | _, imp φ ψ, v => φ.Realize v → ψ.Realize v
  | _, quant Q ψ, v => (⟨M, monadicStructure M fun i a ↦ (ψ i).Realize (Fin.snoc v a)⟩ :
      Bundled.{w} (Language.monadic (Fin _)).Structure) ∈ Q.holds

/-- The quantifier rank of a formula of `FO(Mon)`, the greatest nesting depth of quantifiers. -/
def qr : ∀ {n}, L.MonFormula n → ℕ
  | _, equal _ _ => 0
  | _, rel _ _ => 0
  | _, falsum => 0
  | _, imp φ ψ => max φ.qr ψ.qr
  | _, quant _ ψ => (Finset.univ.sup fun i ↦ (ψ i).qr) + 1

end MonFormula

variable (L) in
/-- A class `P` of structures is definable in `FO(Mon)` within `K` when some sentence of
`FO(Mon)` holds of exactly the members of `P` among the structures in `K`. -/
def MonDefinable (K P : Set (Bundled.{w} L.Structure)) : Prop :=
  ∃ φ : L.MonFormula.{u, v, w} 0, ∀ M ∈ K, M ∈ P ↔ φ.Realize (default : Fin 0 → M)

/-! ### The bijective game -/

variable {M N : Type w} [L.Structure M] [L.Structure N] {k n : ℕ}

variable (L) in
/-- Duplicator wins the `k`-round bijective game from an `n`-tuple `v` of `M` and an `n`-tuple
`w` of `N`. The tuples must satisfy the same atomic formulas; with `k + 1` rounds left, she must
also have a bijection `g : M ≃ N` such that she wins with `k` rounds left from `v` extended by `a`
and `w` extended by `g a`, for every `a`. -/
def DuplicatorWinsBijective : ℕ → ∀ {n : ℕ}, (Fin n → M) → (Fin n → N) → Prop
  | 0, _, v, w => L.DuplicatorWins 0 v w
  | k + 1, _, v, w => L.DuplicatorWins 0 v w ∧
      ∃ g : M ≃ N, ∀ a, DuplicatorWinsBijective k (Fin.snoc v a) (Fin.snoc w (g a))

namespace DuplicatorWinsBijective

theorem duplicatorWins_zero : ∀ {k n} {v : Fin n → M} {w : Fin n → N},
    L.DuplicatorWinsBijective k v w → L.DuplicatorWins 0 v w
  | 0, _, _, _, h => h
  | _ + 1, _, _, _, h => h.1

/-- A position from which duplicator wins `k` rounds of the bijective game satisfies the same
formulas of `FO(Mon)` of quantifier rank `≤ k`. -/
theorem realize_iff : ∀ {n} {φ : L.MonFormula n} {k} {v : Fin n → M} {w : Fin n → N},
    L.DuplicatorWinsBijective k v w → φ.qr ≤ k → (φ.Realize v ↔ φ.Realize w)
  | _, .equal t₁ t₂, _, _, _, h, _ => h.duplicatorWins_zero.realize_iff_of_isAtomic (.equal t₁ t₂)
  | _, .rel R ts, _, _, _, h, _ => h.duplicatorWins_zero.realize_iff_of_isAtomic (.rel R ts)
  | _, .falsum, _, _, _, _, _ => Iff.rfl
  | _, .imp _ _, _, _, _, h, hφ =>
    imp_congr (realize_iff h (le_of_max_le_left hφ)) (realize_iff h (le_of_max_le_right hφ))
  | _, .quant _ _, 0, _, _, _, hφ => absurd hφ (by simp [MonFormula.qr])
  | _, .quant Q ψ, _ + 1, v, w, h, hφ => by
    obtain ⟨-, g, hg⟩ := h
    have hψ (i) : (ψ i).qr ≤ _ :=
      (Finset.le_sup (f := fun i ↦ (ψ i).qr) (Finset.mem_univ i)).trans
        (Nat.le_of_succ_le_succ hφ)
    refine Q.iso_inv ⟨monadicStructureEquiv (P := fun i a ↦ (ψ i).Realize (Fin.snoc v a))
      (Q := fun i b ↦ (ψ i).Realize (Fin.snoc w b)) g fun i a ↦ ?_⟩
    exact (realize_iff (hg a) (hψ i)).symm

end DuplicatorWinsBijective

/-- The bijective game method for undefinability in `FO(Mon)`. If for every number of rounds
duplicator wins the bijective game between some structure in `K` with property `P` and one in
`K` without it, then `P` is not definable in `FO(Mon)` within `K`. -/
theorem not_monDefinable_of_duplicatorWinsBijective {K P : Set (Bundled.{w} L.Structure)}
    (h : ∀ k, ∃ M ∈ K, ∃ N ∈ K, L.DuplicatorWinsBijective k (default : Fin 0 → M)
      (default : Fin 0 → N) ∧ M ∈ P ∧ N ∉ P) : ¬ L.MonDefinable K P := by
  rintro ⟨φ, hφ⟩
  obtain ⟨M, hM, N, hN, hMN, hP, hnP⟩ := h φ.qr
  exact hnP ((hφ N hN).2 ((hMN.realize_iff le_rfl).1 ((hφ M hM).1 hP)))

/-! ### Successor graphs of permutations

The successor graph of a permutation `σ` joins each element `x` to `σ x`. Duplicator wins `r`
rounds of the bijective game between the successor graphs of two permutations of equinumerous
finite sets whose cycles all have length at least `2 ^ r`. With `k` rounds left she keeps the
chosen points matched for every displacement up to `2 ^ k`: the `j`-th point lies `d` steps along
`σ` from the `i`-th exactly when the same holds along `τ`. In each round she maps the points near
the chosen ones by translating along `τ`, and matches the remaining points by counting. -/

section Permutation

open _root_.Equiv (Perm)

variable {M N : Type w} (σ : Perm M) (τ : Perm N)

/-- The `j`-th point of `v` lies `d` steps along `σ` from the `i`-th exactly when the `j`-th point
of `w` lies `d` steps along `τ` from the `i`-th, for every displacement `|d| ≤ t`. -/
private def DisplacementMatch (t : ℕ) {n : ℕ} (v : Fin n → M) (w : Fin n → N) : Prop :=
  ∀ i j (d : ℤ), |d| ≤ t → (v j = (σ ^ d) (v i) ↔ w j = (τ ^ d) (w i))

private theorem zpow_apply_eq_zpow_apply_iff (π : Perm M) (a b : M) (e e' : ℤ) :
    (π ^ e) a = (π ^ e') b ↔ b = (π ^ (e - e')) a := by
  rw [sub_eq_neg_add, zpow_add, Perm.mul_apply, zpow_neg, Perm.eq_inv_iff_eq, eq_comm]

private theorem eq_zpow_apply_iff (π : Perm M) (a b : M) (d : ℤ) :
    b = (π ^ d) a ↔ a = (π ^ (-d)) b := by
  rw [zpow_neg, Perm.eq_inv_iff_eq, eq_comm]

private theorem abs_sub_le_two_mul {e e' : ℤ} {t : ℕ} (he : |e| ≤ t) (he' : |e'| ≤ t) :
    |e - e'| ≤ ((2 * t : ℕ) : ℤ) := by
  have := abs_le.1 he
  have := abs_le.1 he'
  exact abs_le.2 ⟨by push_cast; omega, by push_cast; omega⟩

variable {σ τ}

private theorem DisplacementMatch.mono {t t' : ℕ} {n : ℕ} {v : Fin n → M} {w : Fin n → N}
    (h : DisplacementMatch σ τ t' v w) (htt' : t ≤ t') : DisplacementMatch σ τ t v w :=
  fun i j d hd ↦ h i j d (hd.trans (by exact_mod_cast htt'))

private theorem DisplacementMatch.duplicatorWins_zero {n : ℕ} {v : Fin n → M} {w : Fin n → N}
    (h : DisplacementMatch σ τ 1 v w) :
    @DuplicatorWins Language.graph M N (graphStructure fun x y ↦ y = σ x)
      (graphStructure fun x y ↦ y = τ x) 0 n v w := by
  let := graphStructure fun x y : M ↦ y = σ x
  let := graphStructure fun x y : N ↦ y = τ x
  intro φ hφ
  obtain ⟨i, rfl⟩ := hφ.exists_eq_atom
  rcases i with ⟨i, j⟩ | ⟨⟨l, R⟩, f⟩
  · have := h i j 0 (by simp)
    simp only [zpow_zero, Perm.one_apply] at this
    simp only [atom, BoundedFormula.realize_bdEqual, Function.comp_apply, Term.realize_var,
      Sum.elim_inr]
    exact eq_comm.trans (this.trans eq_comm)
  · cases R
    have := h (f 0) (f 1) 1 (by decide)
    simp only [zpow_one] at this
    exact this

private theorem DisplacementMatch.exists_equiv [Fintype M] [Fintype N]
    (hcard : Fintype.card M = Fintype.card N) {t : ℕ}
    (hσ : ∀ x (d : ℤ), |d| ≤ t → (σ ^ d) x = x → d = 0)
    (hτ : ∀ x (d : ℤ), |d| ≤ t → (τ ^ d) x = x → d = 0)
    {n : ℕ} {v : Fin n → M} {w : Fin n → N} (h : DisplacementMatch σ τ (2 * t) v w) :
    ∃ g : M ≃ N, ∀ a, DisplacementMatch σ τ t (Fin.snoc v a) (Fin.snoc w (g a)) := by
  classical
  -- Two translates of chosen points agree in `M` exactly when their partners agree in `N`.
  have key {i i' : Fin n} {e e' : ℤ} (he : |e| ≤ t) (he' : |e'| ≤ t) :
      (σ ^ e) (v i) = (σ ^ e') (v i') ↔ (τ ^ e) (w i) = (τ ^ e') (w i') := by
    rw [zpow_apply_eq_zpow_apply_iff, zpow_apply_eq_zpow_apply_iff]
    exact h i i' (e - e') (abs_sub_le_two_mul he he')
  let U : Set M := {a | ∃ i, ∃ e : ℤ, |e| ≤ t ∧ a = (σ ^ e) (v i)}
  let U' : Set N := {b | ∃ i, ∃ e : ℤ, |e| ≤ t ∧ b = (τ ^ e) (w i)}
  let f : U → U' := fun a ↦ ⟨(τ ^ a.2.choose_spec.choose) (w a.2.choose),
    a.2.choose, a.2.choose_spec.choose, a.2.choose_spec.choose_spec.1, rfl⟩
  have hf (a : U) {i : Fin n} {e : ℤ} (he : |e| ≤ t) (ha : (a : M) = (σ ^ e) (v i)) :
      (f a : N) = (τ ^ e) (w i) :=
    (key a.2.choose_spec.choose_spec.1 he).1 (a.2.choose_spec.choose_spec.2.symm.trans ha)
  have hfb : Function.Bijective f := by
    refine ⟨fun a a' haa' ↦ ?_, fun b ↦ ?_⟩
    · obtain ⟨i, e, he, ha⟩ := a.2
      have := (hf a he ha).symm.trans (congrArg Subtype.val haa')
      exact Subtype.ext (ha.trans ((key he a'.2.choose_spec.choose_spec.1).2
        (this.trans (hf a' a'.2.choose_spec.choose_spec.1
          a'.2.choose_spec.choose_spec.2).symm).symm.symm |>.trans
          a'.2.choose_spec.choose_spec.2.symm))
    · obtain ⟨i, e, he, hb⟩ := b.2
      exact ⟨⟨(σ ^ e) (v i), i, e, he, rfl⟩, Subtype.ext ((hf _ he rfl).trans hb.symm)⟩
  have hcard' : Fintype.card {a // a ∉ U} = Fintype.card {b // b ∉ U'} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hcard,
      Fintype.card_congr (_root_.Equiv.ofBijective f hfb)]
  let g : M ≃ N := ((_root_.Equiv.sumCompl (· ∈ U)).symm.trans
    ((_root_.Equiv.ofBijective f hfb).sumCongr (Fintype.equivOfCardEq hcard'))).trans
      (_root_.Equiv.sumCompl (· ∈ U'))
  have hgU {a} (ha : a ∈ U) : g a = f ⟨a, ha⟩ := by
    simp [g, _root_.Equiv.sumCompl_symm_apply_of_pos ha]
  have hgU' {a} (ha : a ∉ U) : g a ∉ U' := by
    simp only [g, _root_.Equiv.trans_apply, _root_.Equiv.sumCompl_symm_apply_of_neg ha,
      _root_.Equiv.sumCongr_apply,
      Sum.map_inr, _root_.Equiv.sumCompl_apply_inr]
    exact ((Fintype.equivOfCardEq hcard') ⟨a, ha⟩).2
  -- A new point lies `d` steps from an old one exactly when its image does from its partner.
  have hnew (a : M) (i : Fin n) {d : ℤ} (hd : |d| ≤ t) :
      a = (σ ^ d) (v i) ↔ g a = (τ ^ d) (w i) := by
    by_cases ha : a ∈ U
    · obtain ⟨i₀, e₀, he₀, ha₀⟩ := ha
      rw [hgU ⟨i₀, e₀, he₀, ha₀⟩, hf _ he₀ ha₀, ha₀]
      exact key he₀ hd
    · refine iff_of_false (fun h ↦ ha ⟨i, d, hd, h⟩) fun h ↦ hgU' ha ⟨i, d, hd, h⟩
  refine ⟨g, fun a i j d hd ↦ ?_⟩
  have hd' : |d| ≤ ((2 * t : ℕ) : ℤ) :=
    hd.trans (by exact_mod_cast Nat.le_mul_of_pos_left t two_pos)
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · rw [hσ a d hd h.symm, zpow_zero, Perm.one_apply]
      · rw [hτ (g a) d hd h.symm, zpow_zero, Perm.one_apply]
    | cast j =>
      simp only [Fin.snoc_last, Fin.snoc_castSucc]
      rw [eq_zpow_apply_iff σ a (v j), eq_zpow_apply_iff τ (g a) (w j)]
      exact hnew a j (by rwa [abs_neg])
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last, Fin.snoc_castSucc]
      exact hnew a i hd
    | cast j =>
      simp only [Fin.snoc_castSucc]
      exact h i j d hd'

private theorem DisplacementMatch.duplicatorWinsBijective [Fintype M] [Fintype N]
    (hcard : Fintype.card M = Fintype.card N) {r : ℕ}
    (hσ : ∀ x (d : ℤ), |d| < 2 ^ r → (σ ^ d) x = x → d = 0)
    (hτ : ∀ x (d : ℤ), |d| < 2 ^ r → (τ ^ d) x = x → d = 0) :
    ∀ k ≤ r, ∀ {n : ℕ} {v : Fin n → M} {w : Fin n → N}, DisplacementMatch σ τ (2 ^ k) v w →
      @DuplicatorWinsBijective Language.graph M N (graphStructure fun x y ↦ y = σ x)
        (graphStructure fun x y ↦ y = τ x) k n v w
  | 0, _, _, _, _, h => h.duplicatorWins_zero
  | k + 1, hk, _, _, _, h => by
    have h2k : 2 ^ k < 2 ^ r := Nat.pow_lt_pow_right (by omega) (by omega)
    obtain ⟨g, hg⟩ := DisplacementMatch.exists_equiv hcard
      (fun x d hd ↦ hσ x d (hd.trans_lt (by exact_mod_cast h2k)))
      (fun x d hd ↦ hτ x d (hd.trans_lt (by exact_mod_cast h2k)))
      (h.mono (by rw [pow_succ']))
    exact ⟨(h.mono (Nat.one_le_two_pow)).duplicatorWins_zero, g, fun a ↦
      DisplacementMatch.duplicatorWinsBijective hcard hσ hτ k (by omega) (hg a)⟩

/-- Duplicator wins `r` rounds of the bijective game between the successor graphs of two
permutations of equinumerous finite sets whose cycles all have length at least `2 ^ r`. -/
theorem duplicatorWinsBijective_successor [Fintype M] [Fintype N]
    (hcard : Fintype.card M = Fintype.card N) (r : ℕ)
    (hσ : ∀ x (d : ℤ), |d| < 2 ^ r → (σ ^ d) x = x → d = 0)
    (hτ : ∀ x (d : ℤ), |d| < 2 ^ r → (τ ^ d) x = x → d = 0) :
    @DuplicatorWinsBijective Language.graph M N (graphStructure fun x y ↦ y = σ x)
      (graphStructure fun x y ↦ y = τ x) r 0 default default :=
  DisplacementMatch.duplicatorWinsBijective hcard hσ hτ r le_rfl fun i ↦ i.elim0

end Permutation

end FirstOrder.Language
