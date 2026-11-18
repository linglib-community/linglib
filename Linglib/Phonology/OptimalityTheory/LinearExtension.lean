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

A relation is an unbundled `r : ι → ι → Prop` on the constraints `ι` with `[IsPartialOrder ι r]`
where needed, never a `PartialOrder ι` value, since a class-typed binder would become a local
instance and capture the `≤` and `<` notation. This is mathlib's idiom for orders treated as
data, as in `extend_partialOrder`. A permutation `g` of the constraints is an automorphism of `r`
when `g ⁻¹'o r = r`, and acts on a ranking `σ` by `σ.trans g`.

A stratified relation is used here through its linear extensions, each a total ranking, as
[anttila-1997] uses a partial ranking. [tesar-smolensky-1995] evaluate a stratified hierarchy
by pooling the marks of a stratum, a property of evaluation rather than of the relation, which
is not formalized here.

## References

* [A. Anttila, *Deriving Variation from Grammar* (1997)][anttila-1997]
* [B. Tesar and P. Smolensky, *The Learnability of Optimality Theory* (1995)][tesar-smolensky-1995]
* [N. Merchant and J. Riggle, *OT grammars, beyond partial orders: ERC sets and antimatroids*
  (2016)][merchant-riggle-2016]
-/

@[expose] public section

namespace OptimalityTheory

open Finset

variable {ι : Type*} {n : ℕ}

/-! ### Linear extensions -/

/-- Equality is the discrete partial order. As a grammar it imposes no ranking, and every ranking
is a linear extension of it. -/
instance {α : Type*} : IsPartialOrder α (· = ·) where
  refl _ := rfl
  trans _ _ _ := Eq.trans
  antisymm _ _ h _ := h

namespace Ranking.Enumeration

variable {r : ι → ι → Prop} {σ : Ranking.Enumeration ι n} {g : Equiv.Perm ι}

/-- The ranking `σ` is a *linear extension* of the relation `r` when it ranks `a` at least as high
as `b` whenever `r a b`. -/
def IsLinearExtension (σ : Ranking.Enumeration ι n) (r : ι → ι → Prop) : Prop :=
  r ≤ σ.toRel

instance [Fintype ι] (σ : Ranking.Enumeration ι n) (r : ι → ι → Prop) [DecidableRel r] :
    Decidable (σ.IsLinearExtension r) :=
  decidable_of_iff (∀ a b, r a b → σ.symm a ≤ σ.symm b) Iff.rfl

/-- A linear extension strictly ranks distinct related constraints. -/
theorem IsLinearExtension.dominates (hσ : σ.IsLinearExtension r) {a b : ι} (hab : r a b)
    (hne : a ≠ b) : σ.Dominates a b :=
  (toRel_iff_dominates σ hne).1 (hσ a b hab)

/-- A linear extension strictly ranks the distinct pairs of the relation. -/
theorem IsLinearExtension.le_dominates (hσ : σ.IsLinearExtension r) :
    (fun a b ↦ r a b ∧ a ≠ b) ≤ σ.Dominates :=
  fun _ _ h ↦ hσ.dominates h.1 h.2

/-- Two relations with a common linear extension order no two distinct constraints in opposite
ways. -/
theorem IsLinearExtension.eq_of_rel_of_rel {s : ι → ι → Prop} (hσ : σ.IsLinearExtension r)
    (hσ' : σ.IsLinearExtension s) {a b : ι} (hab : r a b) (hba : s b a) : a = b :=
  antisymm_of σ.toRel (hσ a b hab) (hσ' b a hba)

/-- A ranking that extends a relation extends its transitive closure, so a diagram may be given
by its edges. -/
theorem IsLinearExtension.transGen (hσ : σ.IsLinearExtension r) :
    σ.IsLinearExtension (Relation.TransGen r) := fun a b h ↦ by
  induction h with
  | single h => exact hσ _ _ h
  | tail _ h ih => exact le_trans ih (hσ _ _ h)

theorem isLinearExtension_toRel (σ : Ranking.Enumeration ι n) : σ.IsLinearExtension σ.toRel :=
  le_refl σ.toRel

/-- Composing with a permutation `g` of the constraints turns the linear extensions of the
pullback of `r` along `g` into those of `r`. -/
theorem isLinearExtension_trans_iff :
    IsLinearExtension (σ.trans g) r ↔ σ.IsLinearExtension (g ⁻¹'o r) :=
  ⟨fun h a b hab ↦ by simpa [toRel] using h (g a) (g b) hab,
   fun h a b hab ↦ h (g.symm a) (g.symm b) (by simpa [Order.Preimage] using hab)⟩

/-- The linear extensions of a grammar are closed under the permutations of the constraints that
preserve it. -/
theorem IsLinearExtension.trans_of_preimage_eq (hg : g ⁻¹'o r = r)
    (hσ : σ.IsLinearExtension r) : IsLinearExtension (σ.trans g) r :=
  isLinearExtension_trans_iff.2 (hg.symm ▸ hσ)

section Fintype

variable [Fintype ι]

/-- Every grammar has a linear extension, by Szpilrajn's theorem. -/
theorem exists_isLinearExtension (r : ι → ι → Prop) [IsPartialOrder ι r]
    (hn : Fintype.card ι =
        n := by simp) : ∃ σ : Ranking.Enumeration ι n, σ.IsLinearExtension r := by
  obtain ⟨s, hs, hsub⟩ := extend_partialOrder r
  obtain ⟨σ, rfl⟩ := Ranking.Enumeration.exists_toRel_eq s hn
  exact ⟨σ, hsub⟩

variable [DecidableEq ι]

/-- The linear extensions of a grammar: Anttila's tableaux, the total rankings among which the
grammar chooses at each evaluation. -/
def linearExtensions (r : ι → ι → Prop) [DecidableRel r] : Finset (Ranking.Enumeration ι n) :=
  {σ | σ.IsLinearExtension r}

@[simp]
theorem mem_linearExtensions [DecidableRel r] :
    σ ∈ linearExtensions r ↔ σ.IsLinearExtension r := by
  simp [linearExtensions]

/-- A ranking is the only linear extension of its own order. -/
@[simp]
theorem linearExtensions_toRel (σ : Ranking.Enumeration ι n) : linearExtensions σ.toRel = {σ} := by
  ext τ
  rw [mem_linearExtensions, mem_singleton, IsLinearExtension,
    Ranking.Enumeration.toRel_le_toRel_iff, eq_comm]

/-- Every ranking is a linear extension of the discrete grammar. -/
@[simp]
theorem linearExtensions_eq (ι : Type*) [Fintype ι] [DecidableEq ι] (n : ℕ) :
    linearExtensions (· = · : ι → ι → Prop) = (univ : Finset (Ranking.Enumeration ι n)) :=
  eq_univ_of_forall fun _ ↦ mem_linearExtensions.2 fun _ _ h ↦ h ▸ le_refl _

theorem linearExtensions_nonempty (r : ι → ι → Prop) [IsPartialOrder ι r]
    [DecidableRel r] (hn : Fintype.card ι = n := by simp) :
    (linearExtensions (n := n) r).Nonempty :=
  (exists_isLinearExtension r hn).imp fun _ ↦ mem_linearExtensions.2

end Fintype

end Ranking.Enumeration

/-! ### Stratified grammars

In a stratified grammar every constraint of an earlier stratum dominates every constraint of a
later one, and an inner order applies within each stratum. With the discrete inner order the
linear extensions rank each stratum's constraints freely, as [anttila-1997] ranks a partial
order's. -/

section Stratified

variable {s : ℕ} {stratumOf : ι → Fin s} {inner : ι → ι → Prop} {k : Fin s}
  {d d' : ι}

/-- The stratified grammar of a stratum assignment and an inner order: the lexicographic order
`Prod.Lex` pulled back along `a ↦ (stratumOf a, a)`, so that strata compare strictly and `inner`
applies within a stratum. -/
def stratified (stratumOf : ι → Fin s) (inner : ι → ι → Prop) : ι → ι → Prop :=
  fun a b ↦ Prod.Lex (· < ·) inner (stratumOf a, a) (stratumOf b, b)

theorem stratified_iff {a b : ι} :
    stratified stratumOf inner a b ↔
      stratumOf a < stratumOf b ∨ stratumOf a = stratumOf b ∧ inner a b :=
  Prod.lex_iff

instance [IsPartialOrder ι inner] : IsPartialOrder ι (stratified stratumOf inner) where
  refl a := Prod.Lex.right _ (refl_of inner a)
  trans _ _ _ := Prod.Lex.trans
  antisymm _ _ hab hba := congrArg Prod.snd (antisymm hab hba)

instance [DecidableRel inner] : DecidableRel (stratified stratumOf inner) :=
  fun _ _ ↦ decidable_of_iff _ stratified_iff.symm

/-- A stratified grammar is invariant under the transposition of two constraints of a stratum on
which the inner order is discrete. -/
theorem swap_preimage_stratified [DecidableEq ι] [Std.Refl inner]
    (h_triv : ∀ a b, stratumOf a = k → stratumOf b = k → inner a b → a = b)
    (hd : stratumOf d = k) (hd' : stratumOf d' = k) :
    Equiv.swap d d' ⁻¹'o stratified stratumOf inner = stratified stratumOf inner := by
  have h_str (x : ι) : stratumOf (Equiv.swap d d' x) = stratumOf x := by
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
  · have hne {x c : ι} (hx : stratumOf x ≠ k) (hc : stratumOf c = k) : x ≠ c :=
      fun h ↦ hx (h ▸ hc)
    rw [Equiv.swap_apply_of_ne_of_ne (hne hk hd) (hne hk hd'),
      Equiv.swap_apply_of_ne_of_ne (hne (heq ▸ hk) hd) (hne (heq ▸ hk) hd')]

end Stratified

end OptimalityTheory
