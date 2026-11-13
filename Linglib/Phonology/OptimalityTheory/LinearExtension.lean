module

public import Linglib.Phonology.OptimalityTheory.Ranking
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Prod.Basic
public import Mathlib.Order.Extension.Linear
public import Mathlib.Order.RelIso.Basic

/-!
# Linear extensions of a ranking relation

A partial ranking of the constraints is a relation `r` on them, and the total rankings compatible
with it are its linear extensions. Every partial order has one, by Szpilrajn's theorem, and a
permutation of the constraints that preserves `r` permutes its linear extensions. In a stratified
relation the constraints fall into strata ranked one above the other, and a transposition within
a freely ranked stratum preserves it.

## Implementation notes

A relation is an unbundled `r : Fin n → Fin n → Prop` with `[IsPartialOrder (Fin n) r]` where
needed, never a `PartialOrder (Fin n)` value, since a class-typed binder would become a local
instance and capture the `≤` and `<` notation that must keep meaning the positional order of
`Fin n`. This is mathlib's idiom for orders treated as data, as in `extend_partialOrder`. A
permutation `g` of the constraints is an automorphism of `r` when `g ⁻¹'o r = r`.

## References

* [A. Anttila, *Deriving Variation from Grammar* (1997)][anttila-1997]
* [B. Tesar and P. Smolensky, *The Learnability of Optimality Theory* (1995)][tesar-smolensky-1995]
* [N. Merchant and J. Riggle, *OT grammars, beyond partial orders: ERC sets and antimatroids*
  (2016)][merchant-riggle-2016]
-/

@[expose] public section

namespace OptimalityTheory

open Finset

variable {n : ℕ}

/-! ### Linear extensions -/

/-- Equality is the discrete partial order. As a grammar it imposes no ranking, and every ranking
is a linear extension of it. -/
instance {α : Type*} : IsPartialOrder α (· = ·) where
  refl _ := rfl
  trans _ _ _ := Eq.trans
  antisymm _ _ h _ := h

namespace Ranking

variable {r : Fin n → Fin n → Prop} {g σ : Ranking (Fin n) n}

/-- The ranking `σ` is a *linear extension* of the relation `r` when it ranks `a` at least as high
as `b` whenever `r a b`. -/
def IsLinearExtension (σ : Ranking (Fin n) n) (r : Fin n → Fin n → Prop) : Prop :=
  r ≤ σ.toRel

instance (σ : Ranking (Fin n) n) (r : Fin n → Fin n → Prop) [DecidableRel r] :
    Decidable (σ.IsLinearExtension r) :=
  decidable_of_iff (∀ a b, r a b → σ.symm a ≤ σ.symm b) Iff.rfl

/-- The linear extensions of a grammar: Anttila's tableaux, the total rankings among which the
grammar chooses at each evaluation. -/
def linearExtensions (r : Fin n → Fin n → Prop) [DecidableRel r] : Finset (Ranking (Fin n) n) :=
  {σ | σ.IsLinearExtension r}

@[simp]
theorem mem_linearExtensions [DecidableRel r] :
    σ ∈ linearExtensions r ↔ σ.IsLinearExtension r := by
  simp [linearExtensions]

theorem isLinearExtension_toRel (σ : Ranking (Fin n) n) : σ.IsLinearExtension σ.toRel :=
  le_refl σ.toRel

/-- A ranking is the only linear extension of its own order. -/
@[simp]
theorem linearExtensions_toRel (σ : Ranking (Fin n) n) : linearExtensions σ.toRel = {σ} := by
  ext τ
  rw [mem_linearExtensions, mem_singleton, IsLinearExtension, Ranking.toRel_le_toRel_iff, eq_comm]

/-- Every ranking is a linear extension of the discrete grammar. -/
@[simp]
theorem linearExtensions_eq (n : ℕ) :
    linearExtensions (· = · : Fin n → Fin n → Prop) = univ :=
  eq_univ_of_forall fun _ ↦ mem_linearExtensions.2 fun _ _ h ↦ h ▸ le_refl _

/-- Composing with a permutation `g` of the constraints turns the linear extensions of the
pullback of `r` along `g` into those of `r`. -/
theorem isLinearExtension_mul_iff :
    (g * σ).IsLinearExtension r ↔ σ.IsLinearExtension (g ⁻¹'o r) :=
  ⟨fun h a b hab ↦ by simpa using h (g a) (g b) hab,
   fun h a b hab ↦ by simpa using h (g⁻¹ a) (g⁻¹ b) (by simpa [Order.Preimage] using hab)⟩

/-- The linear extensions of a grammar are closed under the permutations of the constraints that
preserve it. -/
theorem IsLinearExtension.mul (hg : g ⁻¹'o r = r) (hσ : σ.IsLinearExtension r) :
    (g * σ).IsLinearExtension r :=
  isLinearExtension_mul_iff.2 (hg.symm ▸ hσ)

/-- Every grammar has a linear extension, by Szpilrajn's theorem. -/
theorem exists_isLinearExtension (r : Fin n → Fin n → Prop) [IsPartialOrder (Fin n) r] :
    ∃ σ : Ranking (Fin n) n, σ.IsLinearExtension r := by
  obtain ⟨s, hs, hsub⟩ := extend_partialOrder r
  obtain ⟨σ, rfl⟩ := Ranking.exists_toRel_eq (n := n) s
  exact ⟨σ, hsub⟩

theorem linearExtensions_nonempty (r : Fin n → Fin n → Prop) [IsPartialOrder (Fin n) r]
    [DecidableRel r] : (linearExtensions r).Nonempty :=
  (exists_isLinearExtension r).imp fun _ ↦ mem_linearExtensions.2

end Ranking

/-! ### Stratified grammars

In a stratified grammar every constraint of an earlier stratum dominates every constraint of a
later one, and an inner order applies within each stratum. With the discrete inner order this is
the stratified domination hierarchy of [tesar-smolensky-1995], whose strata are freely ranked. -/

section Stratified

variable {s : ℕ} {stratumOf : Fin n → Fin s} {inner : Fin n → Fin n → Prop} {k : Fin s}
  {d d' : Fin n}

/-- The stratified grammar of a stratum assignment and an inner order: the lexicographic order
`Prod.Lex` pulled back along `a ↦ (stratumOf a, a)`, so that strata compare strictly and `inner`
applies within a stratum. -/
def stratified (stratumOf : Fin n → Fin s) (inner : Fin n → Fin n → Prop) :
    Fin n → Fin n → Prop :=
  fun a b ↦ Prod.Lex (· < ·) inner (stratumOf a, a) (stratumOf b, b)

theorem stratified_iff {a b : Fin n} :
    stratified stratumOf inner a b ↔
      stratumOf a < stratumOf b ∨ stratumOf a = stratumOf b ∧ inner a b :=
  Prod.lex_iff

instance [IsPartialOrder (Fin n) inner] : IsPartialOrder (Fin n) (stratified stratumOf inner) where
  refl a := Prod.Lex.right _ (refl_of inner a)
  trans _ _ _ := Prod.Lex.trans
  antisymm _ _ hab hba := congrArg Prod.snd (antisymm hab hba)

instance [DecidableRel inner] : DecidableRel (stratified stratumOf inner) :=
  fun _ _ ↦ decidable_of_iff _ stratified_iff.symm

/-- A stratified grammar is invariant under the transposition of two constraints of a stratum on
which the inner order is discrete. -/
theorem swap_preimage_stratified [Std.Refl inner]
    (h_triv : ∀ a b, stratumOf a = k → stratumOf b = k → inner a b → a = b)
    (hd : stratumOf d = k) (hd' : stratumOf d' = k) :
    Equiv.swap d d' ⁻¹'o stratified stratumOf inner = stratified stratumOf inner := by
  have h_str (x : Fin n) : stratumOf (Equiv.swap d d' x) = stratumOf x := by
    rcases eq_or_ne x d with rfl | hxd
    · rw [Equiv.swap_apply_left, hd', hd]
    rcases eq_or_ne x d' with rfl | hxd'
    · rw [Equiv.swap_apply_right, hd, hd']
    · rw [Equiv.swap_apply_of_ne_of_ne hxd hxd']
  ext a b
  rw [Order.Preimage, stratified_iff, stratified_iff, h_str a, h_str b]
  refine or_congr_right (and_congr_right fun heq ↦ ?_)
  rcases eq_or_ne (stratumOf a) k with hk | hk
  · refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain rfl : a = b := (Equiv.swap d d').injective
        (h_triv _ _ ((h_str a).trans hk) ((h_str b).trans (heq ▸ hk)) h)
      exact refl_of inner a
    · obtain rfl : a = b := h_triv a b hk (heq ▸ hk) h
      exact refl_of inner _
  · have hne {x c : Fin n} (hx : stratumOf x ≠ k) (hc : stratumOf c = k) : x ≠ c :=
      fun h ↦ hx (h ▸ hc)
    rw [Equiv.swap_apply_of_ne_of_ne (hne hk hd) (hne hk hd'),
      Equiv.swap_apply_of_ne_of_ne (hne (heq ▸ hk) hd) (hne (heq ▸ hk) hd')]

end Stratified

end OptimalityTheory
