module

public import Linglib.Phonology.OptimalityTheory.ElementaryRankingCondition
public import Linglib.Phonology.OptimalityTheory.Antimatroid
public import Linglib.Phonology.OptimalityTheory.Grammar
public import Linglib.Phonology.OptimalityTheory.Typology
public import Linglib.Core.GroupTheory.Perm.MinOn
public import Linglib.Core.Probability.UniformOn
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Prod.Basic
public import Mathlib.Order.Extension.Linear
public import Mathlib.Order.Preorder.Finite

/-!
# Partially ordered constraints

This file defines the partially ordered constraints (POC) model of variation of Kiparsky and
Anttila. A POC grammar is a partial order on the constraint set, and each evaluation samples a
total order consistent with it, a linear extension, whose OT optimum is the output. A single
grammar therefore induces a distribution over outputs: Anttila's quantitative interpretation
is the uniform measure `uniformOn` on the grammar's linear extensions, and the probability of an
output is that measure at the rankings picking it. The central identities are division-free
cardinality equations, which the rate theorems restate as values of the measure.

## Main definitions

* `stratified stratumOf inner`: Tesar and Smolensky's stratified domination hierarchies, pulled
  back from mathlib's `Prod.Lex` along `a ↦ (stratumOf a, a)`. Equality is the discrete grammar,
  with no ranking imposed.
* `IsConsistent r σ`: the ranking `σ` is a linear extension of `r`, that is, `r ≤ σ.toRel`.
* `consistentTotalOrders r`: the `Finset` of linear extensions of `r`, nonempty by Szpilrajn.
* `toGrammar`, `orderIdealAntimatroid`: a POC grammar as a `Grammar`, and its order-ideal
  antimatroid.
* `PicksAt S σ i o`: `o` alone is the language of `σ` at input `i`.
* `active con i o o'`, `favoring con i o o'`: the non-neutral and the winner-preferring constraints
  of the winner–loser ERC of a candidate pair.

## Main results

* `consistentTotalOrders_eq_linearExtensions`: the linear extensions of a POC grammar are those
  of its simple ERC encoding `toERCs`.
* `sum_measure_setOf_picksAt`: under any probability measure on rankings, POC's uniform one or
  stochastic OT's, the outputs' probabilities sum to one, which produces intermediate
  frequencies, such as Coetzee and Pater's t/d-deletion rates, that no single ranking reproduces.
* `picksAt_binary_iff_exists_favoring_isMinOn`: a binary competition is decided by its
  σ-earliest active constraint.
* `ERC.uniformOn_real_satisfiedBy`: a uniformly random ranking satisfies an ERC with a
  non-neutral constraint at rate `|W| / |W ∪ L|`.
* `uniformOn_real_picksAt_discrete_binary`, `uniformOn_real_picksAt_stratified_binary`: `chosen`
  wins at rate `|favoring| / |active|`, restricted to the deciding stratum in the stratified
  case.
* `uniformOn_picksAt_stratified_eq_one`: a candidate that dominates every rival at the deciding
  stratum is the categorical output.

## Implementation notes

Grammars are unbundled relations `r : Fin n → Fin n → Prop` with `[IsPartialOrder (Fin n) r]`,
never `PartialOrder (Fin n)` values, since a class-typed binder would become a local instance and
capture the `≤` and `<` notation that must keep meaning the positional order of `Fin n`. This is
mathlib's own idiom for orders treated as data (Szpilrajn's `extend_partialOrder`).

## References

* [P. Kiparsky, *An OT Perspective on Phonological Variation* (1993)][kiparsky-1993b]
* [A. Anttila, *Deriving Variation from Grammar* (1997)][anttila-1997]
* [B. Tesar and P. Smolensky, *The Learnability of Optimality Theory* (1995)][tesar-smolensky-1995]
* [A. Prince, *Entailed Ranking Arguments* (2002)][prince-2002]
* [N. Merchant and J. Riggle, *OT grammars, beyond partial orders: ERC sets and antimatroids*
  (2016)][merchant-riggle-2016]
* [R. P. Dilworth, *Lattices with unique irreducible decompositions* (1940)][dilworth-1940]
* [A. W. Coetzee and J. Pater, *The Place of Variation in Phonological Theory*
  (2011)][coetzee-pater-2011]
-/

@[expose] public section

namespace OptimalityTheory

open Finset MeasureTheory ProbabilityTheory

variable {n : ℕ}

/-! ### Grammars and their linear extensions -/

/-- Equality is the discrete partial order, relating nothing beyond reflexivity. As a POC
    grammar it is [anttila-1997]'s "no ranking imposed" baseline, of which every permutation is
    a consistent linear extension. -/
instance {α : Type*} : IsPartialOrder α (· = ·) where
  refl _ := rfl
  trans _ _ _ := Eq.trans
  antisymm _ _ h _ := h

/-- A permutation σ is **consistent** with grammar `r` when `r` is contained
    in the total order σ induces (`Ranking.toRel`) — σ is a linear extension
    of `r`. Unfolds to `∀ a b, r a b → σ.symm a ≤ σ.symm b`. -/
def IsConsistent (r : Fin n → Fin n → Prop) (σ : Ranking (Fin n) n) : Prop :=
  r ≤ σ.toRel

instance (r : Fin n → Fin n → Prop) [DecidableRel r] (σ : Ranking (Fin n) n) :
    Decidable (IsConsistent r σ) :=
  decidable_of_iff (∀ a b, r a b → σ.symm a ≤ σ.symm b) Iff.rfl

/-- `consistentTotalOrders r` is the finite set of linear extensions of `r`. -/
def consistentTotalOrders (r : Fin n → Fin n → Prop) [DecidableRel r] :
    Finset (Ranking (Fin n) n) :=
  Finset.univ.filter (IsConsistent r)

@[simp]
theorem mem_consistentTotalOrders {r : Fin n → Fin n → Prop} [DecidableRel r]
    {σ : Ranking (Fin n) n} :
    σ ∈ consistentTotalOrders r ↔ IsConsistent r σ := by
  simp [consistentTotalOrders]

theorem isConsistent_mul_iff {r : Fin n → Fin n → Prop} {g σ : Ranking (Fin n) n} :
    IsConsistent r (g * σ) ↔ IsConsistent (fun a b => r (g a) (g b)) σ :=
  ⟨fun h a b hab => by simpa using h (g a) (g b) hab,
   fun h a b hab => by simpa using h (g⁻¹ a) (g⁻¹ b) (by simpa using hab)⟩

theorem IsConsistent.mul {r : Fin n → Fin n → Prop} {g σ : Ranking (Fin n) n}
    (hg : ∀ a b, r (g a) (g b) ↔ r a b) (hσ : IsConsistent r σ) :
    IsConsistent r (g * σ) :=
  isConsistent_mul_iff.mpr fun a b hab => hσ a b ((hg a b).mp hab)

theorem consistentTotalOrders_discrete (n : ℕ) :
    consistentTotalOrders (· = · : Fin n → Fin n → Prop) = Finset.univ :=
  Finset.eq_univ_of_forall fun _ =>
    mem_consistentTotalOrders.mpr fun _ _ h => h ▸ le_refl _

theorem isConsistent_toRel (σ : Ranking (Fin n) n) : IsConsistent σ.toRel σ :=
  le_refl σ.toRel

@[simp]
theorem consistentTotalOrders_toRel (σ : Ranking (Fin n) n) :
    consistentTotalOrders σ.toRel = {σ} := by
  ext τ
  rw [mem_consistentTotalOrders, Finset.mem_singleton]
  refine ⟨fun hτ => (Ranking.toRel_le_toRel_iff.mp hτ).symm, fun hτ => ?_⟩
  rw [hτ]
  exact isConsistent_toRel σ

/-! ### Szpilrajn — every grammar has a consistent linear extension -/

theorem exists_isConsistent (r : Fin n → Fin n → Prop)
    [IsPartialOrder (Fin n) r] :
    ∃ σ : Ranking (Fin n) n, IsConsistent r σ := by
  obtain ⟨s, hs, hsub⟩ := extend_partialOrder r
  have := hs
  obtain ⟨σ, rfl⟩ := Ranking.exists_toRel_eq (n := n) s
  exact ⟨σ, hsub⟩

theorem consistentTotalOrders_nonempty (r : Fin n → Fin n → Prop)
    [IsPartialOrder (Fin n) r] [DecidableRel r] :
    (consistentTotalOrders r).Nonempty :=
  let ⟨σ, hσ⟩ := exists_isConsistent r
  ⟨σ, mem_consistentTotalOrders.mpr hσ⟩

theorem consistentTotalOrders_card_pos (r : Fin n → Fin n → Prop)
    [IsPartialOrder (Fin n) r] [DecidableRel r] :
    0 < (consistentTotalOrders r).card :=
  (consistentTotalOrders_nonempty r).card_pos

/-! ### Stratified grammars

Earlier strata dominate later ones wholesale, and within a stratum an inner
order applies. With the discrete inner order this is the freely-ranked stratum
grammar of [anttila-1997] eq. (50) — the Stratified Domination Hierarchy of
[tesar-smolensky-1995] that constraint-demotion learning produces. -/

variable {s : ℕ}

section Stratified

/-- The stratified grammar induced by `stratumOf` and an inner order `inner` —
    mathlib's lexicographic order (`Prod.Lex`) pulled back along
    `a ↦ (stratumOf a, a)`: strata compare strictly, ties defer to `inner`.
    The plain characterization is `stratified_iff`; cross-stratum `inner`
    edges are ignored. -/
def stratified (stratumOf : Fin n → Fin s) (inner : Fin n → Fin n → Prop) :
    Fin n → Fin n → Prop :=
  fun a b => Prod.Lex (· < ·) inner (stratumOf a, a) (stratumOf b, b)

variable {stratumOf : Fin n → Fin s} {inner : Fin n → Fin n → Prop} {k : Fin s}
  {d d' : Fin n} {σ : Ranking (Fin n) n}

theorem stratified_iff {a b : Fin n} :
    stratified stratumOf inner a b ↔
      stratumOf a < stratumOf b ∨ stratumOf a = stratumOf b ∧ inner a b :=
  Prod.lex_iff

instance [IsPartialOrder (Fin n) inner] :
    IsPartialOrder (Fin n) (stratified stratumOf inner) where
  refl a := Prod.Lex.right _ (refl_of inner a)
  trans _ _ _ := Prod.Lex.trans
  antisymm _ _ hab hba := congrArg Prod.snd (antisymm hab hba)

instance [DecidableRel inner] : DecidableRel (stratified stratumOf inner) :=
  fun _ _ => decidable_of_iff _ stratified_iff.symm

theorem IsConsistent.symm_lt_of_stratum_lt
    (hσ : IsConsistent (stratified stratumOf inner) σ) {a b : Fin n}
    (h : stratumOf a < stratumOf b) : σ.symm a < σ.symm b :=
  lt_of_le_of_ne (hσ a b (stratified_iff.mpr (Or.inl h)))
    (fun heq => absurd (σ.symm.injective heq ▸ h) (lt_irrefl _))

theorem stratified_swap_apply_iff [Std.Refl inner]
    (h_triv : ∀ a b, stratumOf a = k → stratumOf b = k → inner a b → a = b)
    (hd : stratumOf d = k) (hd' : stratumOf d' = k) (a b : Fin n) :
    stratified stratumOf inner (Equiv.swap d d' a) (Equiv.swap d d' b) ↔
      stratified stratumOf inner a b := by
  have h_str : ∀ x, stratumOf (Equiv.swap d d' x) = stratumOf x := by
    intro x
    rcases eq_or_ne x d with rfl | hxd
    · rw [Equiv.swap_apply_left, hd', hd]
    rcases eq_or_ne x d' with rfl | hxd'
    · rw [Equiv.swap_apply_right, hd, hd']
    · rw [Equiv.swap_apply_of_ne_of_ne hxd hxd']
  rw [stratified_iff, stratified_iff, h_str a, h_str b]
  refine or_congr Iff.rfl (and_congr_right fun heq => ?_)
  rcases eq_or_ne (stratumOf a) k with hk | hk
  · constructor
    · intro h
      obtain h' : a = b := (Equiv.swap d d').injective
        (h_triv _ _ ((h_str a).trans hk) ((h_str b).trans (heq ▸ hk)) h)
      exact h' ▸ refl_of inner a
    · intro h
      obtain rfl : a = b := h_triv a b hk (heq ▸ hk) h
      exact refl_of inner _
  · rw [Equiv.swap_apply_of_ne_of_ne (fun h => hk (by rw [h]; exact hd))
        (fun h => hk (by rw [h]; exact hd')),
      Equiv.swap_apply_of_ne_of_ne (fun h => (heq ▸ hk) (by rw [h]; exact hd))
        (fun h => (heq ▸ hk) (by rw [h]; exact hd'))]

theorem isConsistent_swap_mul [Std.Refl inner]
    (h_triv : ∀ a b, stratumOf a = k → stratumOf b = k → inner a b → a = b)
    (hd : stratumOf d = k) (hd' : stratumOf d' = k)
    (hσ : IsConsistent (stratified stratumOf inner) σ) :
    IsConsistent (stratified stratumOf inner) (Equiv.swap d d' * σ) :=
  hσ.mul (stratified_swap_apply_iff h_triv hd hd')

end Stratified

/-! ### Grounding in the ERC lex API

A partial order is a set of dominance requirements — each related pair is a
simple ERC `a ≫ b` ([merchant-riggle-2016]), and under this encoding the
consistent total orders are exactly `ERC.linearExtensions` ([prince-2002]). -/

/-- The simple-ERC encoding of a grammar, with one ERC `a ≫ b`
(`simpleERC a b`) for each related pair — diagonal pairs give trivial ERCs,
matching `toRel`'s reflexivity. Transitively-implied pairs are entailed by the
covering pairs, so the encoding has the same linear extensions as the
Hasse-edge one. -/
def toERCs (r : Fin n → Fin n → Prop) [DecidableRel r] : Finset (ERC (Fin n)) :=
  (Finset.univ.filter fun p : Fin n × Fin n => r p.1 p.2).image
    fun p => simpleERC p.1 p.2

theorem mem_toERCs {r : Fin n → Fin n → Prop} [DecidableRel r] {α : ERC (Fin n)} :
    α ∈ toERCs r ↔ ∃ a b, r a b ∧ simpleERC a b = α := by
  simp [toERCs, Prod.exists]

theorem satisfiedBy_toERCs {r : Fin n → Fin n → Prop} [DecidableRel r]
    {σ : Ranking (Fin n) n} :
    (∀ α ∈ toERCs r, ERC.SatisfiedBy σ α) ↔ IsConsistent r σ := by
  constructor
  · intro h a b hrel
    exact (simpleERC_satisfiedBy_toRel_iff a b σ).mp
      (h _ (mem_toERCs.mpr ⟨a, b, hrel, rfl⟩))
  · intro hcons α hα
    obtain ⟨a, b, hrel, rfl⟩ := mem_toERCs.mp hα
    exact (simpleERC_satisfiedBy_toRel_iff a b σ).mpr (hcons a b hrel)

/-- The consistent total orders of a grammar are exactly the linear extensions
of its simple-ERC encoding ([merchant-riggle-2016]; [prince-2002]). -/
theorem consistentTotalOrders_eq_linearExtensions (r : Fin n → Fin n → Prop)
    [DecidableRel r] :
    consistentTotalOrders r = ERC.linearExtensions (toERCs r) := by
  ext σ
  rw [mem_consistentTotalOrders, ERC.mem_linearExtensions, satisfiedBy_toERCs]

/-! ### The order-ideal antimatroid of a POC

A grammar's Hasse-edge encoding is a consistent set of simple ERCs, so it has
a Birkhoff antimatroid whose feasible sets are exactly the order ideals of `r`
([dilworth-1940]; [merchant-riggle-2016]). -/

variable (r : Fin n → Fin n → Prop) [IsPartialOrder (Fin n) r] [DecidableRel r]

omit [IsPartialOrder (Fin n) r] in
theorem toERCs_isSimple_or_isTrivial :
    ∀ α ∈ toERCs r, α.IsSimple ∨ α.IsTrivial := by
  intro α hα
  obtain ⟨a, b, _, rfl⟩ := mem_toERCs.mp hα
  exact simpleERC_isSimple_or_isTrivial a b

theorem toERCs_consistent : (ERC.linearExtensions (toERCs r)).Nonempty := by
  obtain ⟨σ, hσ⟩ := exists_isConsistent r
  exact ⟨σ, ERC.mem_linearExtensions.mpr (satisfiedBy_toERCs.mpr hσ)⟩

/-- The order-ideal antimatroid of a partial order is the antimatroid of its encoding as simple
ERCs, whose feasible sets are its order ideals (`orderIdealAntimatroid_isFeasible_iff`). -/
def orderIdealAntimatroid : Antimatroid (Fin n) :=
  ERC.toAntimatroid _ ((ERC.linearExtensions_nonempty_iff _).mp (toERCs_consistent r))

theorem forall_isFeasible_toERCs_iff {S : Finset (Fin n)} :
    (∀ α ∈ toERCs r, ERC.IsFeasible {α} (S : Set (Fin n))) ↔ ∀ a b, r a b → b ∈ S → a ∈ S := by
  obtain ⟨σ, hσ⟩ := toERCs_consistent r
  have hsat : ∀ α ∈ toERCs r, ∃ σ : Ranking (Fin n) n, ERC.SatisfiedBy σ α :=
    fun α hα ↦ ⟨σ, ERC.mem_linearExtensions.mp hσ α hα⟩
  refine ⟨fun h a b hrel hbS ↦ ?_, fun h α hα ↦ ?_⟩
  · rcases eq_or_ne a b with rfl | hab
    · exact hbS
    · have hα := mem_toERCs.mpr ⟨a, b, hrel, rfl⟩
      obtain ⟨w, hwS, hwW⟩ := (ERC.isFeasible_singleton_iff (hsat _ hα) S).mp (h _ hα)
        ⟨b, hbS, simpleERC_apply_L hab⟩
      rwa [(simpleERC_eq_W_iff w).mp hwW] at hwS
  · rw [ERC.isFeasible_singleton_iff (hsat α hα)]
    obtain ⟨a, b, hrel, rfl⟩ := mem_toERCs.mp hα
    rintro ⟨l, hlS, hlL⟩
    have hab : a ≠ b := by rintro rfl; exact simpleERC_self_isTrivial a l hlL
    rw [(simpleERC_eq_L_iff hab l).mp hlL] at hlS
    exact ⟨a, h a b hrel hlS, simpleERC_apply_W⟩

@[simp] theorem orderIdealAntimatroid_isFeasible_iff {S : Finset (Fin n)} :
    (orderIdealAntimatroid r).IsFeasible (↑S : Set (Fin n)) ↔
      ∀ a b, r a b → b ∈ S → a ∈ S := by
  rw [orderIdealAntimatroid, ERC.toAntimatroid_isFeasible,
    ERC.isFeasible_iff_forall_singleton_of_simple
      ((ERC.linearExtensions_nonempty_iff _).mp (toERCs_consistent r))
      (toERCs_isSimple_or_isTrivial r)]
  exact forall_isFeasible_toERCs_iff r

variable {r}

/-! ### Bridge to the `Grammar` hub

A partial order on constraints is the simple-ERC fragment of an OT grammar —
its consistent total orders are exactly the legs of
`Grammar.ofERCs (toERCs r)` ([merchant-riggle-2016]). -/

/-- The `Grammar` whose legs are `r`'s consistent total orders. -/
def toGrammar (r : Fin n → Fin n → Prop) [IsPartialOrder (Fin n) r]
    [DecidableRel r] : Grammar n :=
  Grammar.ofERCs (toERCs r) (toERCs_consistent r)

@[simp] theorem toGrammar_legs (r : Fin n → Fin n → Prop) [IsPartialOrder (Fin n) r]
    [DecidableRel r] :
    (toGrammar r).legs = consistentTotalOrders r := by
  show (Grammar.ofERCs (toERCs r) (toERCs_consistent r)).legs = consistentTotalOrders r
  rw [Grammar.legs_ofERCs, consistentTotalOrders_eq_linearExtensions]

/-! ### The quantitative interpretation

A POC grammar draws one of its linear extensions uniformly at each evaluation
([anttila-1997]), so it is the probability measure `uniformOn ↑(consistentTotalOrders r)` on
rankings, and the probability that it selects `o` for input `i` is that measure at
`{σ | PicksAt S σ i o}`: the fraction of linear extensions picking `o`. -/

instance (r : Fin n → Fin n → Prop) [IsPartialOrder (Fin n) r] [DecidableRel r] :
    IsProbabilityMeasure (uniformOn (consistentTotalOrders r : Set (Ranking (Fin n) n))) :=
  isProbabilityMeasure_uniformOn (Set.toFinite _) (consistentTotalOrders_nonempty r)

variable {Input Output : Type*}
variable {S : ConstraintSystem Input Output (Fin n)} {con : ConstraintSet (Input × Output) (Fin n)}
  {r : Fin n → Fin n → Prop} {σ : Ranking (Fin n) n} {i : Input} {o o' chosen other : Output}

/-- The constraints **active** on the candidate pair `o, o'` at input `i` are the non-neutral
    constraints of the winner–loser ERC of `o` against `o'`, those assigning the two candidates
    different violation counts ([anttila-1997]'s decisive constraints). Inactive constraints
    cannot affect the competition. -/
def active (con : ConstraintSet (Input × Output) (Fin n)) (i : Input) (o o' : Output) :
    Finset (Fin n) :=
  {c | ercOfProfiles (con · (i, o)) (con · (i, o')) c ≠ .e}

/-- The constraints **favoring** `o` over `o'` at input `i` are the winner-preferring constraints
    of the winner–loser ERC of `o` against `o'`, those assigning `o` strictly fewer
    violations. -/
def favoring (con : ConstraintSet (Input × Output) (Fin n)) (i : Input) (o o' : Output) :
    Finset (Fin n) :=
  {c | ercOfProfiles (con · (i, o)) (con · (i, o')) c = .W}

@[simp] theorem mem_active {c : Fin n} :
    c ∈ active con i o o' ↔ con c (i, o) ≠ con c (i, o') := by
  rw [active, mem_filter, ne_eq, ercOfProfiles_eq_e_iff]
  exact and_iff_right (mem_univ c)

@[simp] theorem mem_favoring {c : Fin n} :
    c ∈ favoring con i o o' ↔ con c (i, o) < con c (i, o') := by
  rw [favoring, mem_filter, ercOfProfiles_eq_W_iff]
  exact and_iff_right (mem_univ c)

theorem favoring_subset_active : favoring con i o o' ⊆ active con i o o' :=
  fun _ hc => mem_active.mpr (Nat.ne_of_lt (mem_favoring.mp hc))

/-- σ **picks** output `o` for input `i` when `o` alone is the language of `σ` at `i`, the sole
    winner of the input's tableau. -/
def PicksAt {ι : Type*} (S : ConstraintSystem Input Output ι) (σ : Ranking ι n) (i : Input)
    (o : Output) : Prop :=
  S.language σ i = {o}

theorem picksAt_iff {ι : Type*} {S : ConstraintSystem Input Output ι} {σ : Ranking ι n} :
    PicksAt S σ i o ↔ o ∈ S.gen i ∧ ∀ o' ∈ S.gen i, o' ≠ o →
      toLex (fun k ↦ S.con (σ k) (i, o)) < toLex (fun k ↦ S.con (σ k) (i, o')) :=
  ConstraintSystem.language_eq_singleton_iff

theorem picksAt_unique {ι : Type*} {S : ConstraintSystem Input Output ι} {σ : Ranking ι n}
    (h : PicksAt S σ i o) (h' : PicksAt S σ i o') : o = o' :=
  Finset.singleton_injective (h.symm.trans h')

theorem exists_picksAt (h_ne : (S.gen i).Nonempty)
    (h_inj : Set.InjOn (fun o ↦ (S.con · (i, o))) (S.gen i)) (σ : Ranking (Fin n) n) :
    ∃ o ∈ S.gen i, PicksAt S σ i o := by
  obtain ⟨o, ho⟩ := ConstraintSystem.language_nonempty (r := σ) h_ne
  have hoc := Tableau.optimal_subset ho
  refine ⟨o, hoc, Finset.eq_singleton_iff_unique_mem.2 ⟨ho, fun o' ho' ↦ ?_⟩⟩
  have hoc' := Tableau.optimal_subset ho'
  have heq := (Tableau.le_of_mem_optimal ho' hoc).antisymm (Tableau.le_of_mem_optimal ho hoc')
  refine h_inj hoc' hoc (funext fun c ↦ ?_)
  simpa using show S.con (σ (σ.symm c)) (i, o') = S.con (σ (σ.symm c)) (i, o) from
    congrFun heq (σ.symm c)

variable [DecidableEq Output]

/-- Picking is decided by comparing the candidate with each rival (`picksAt_iff`), not by
computing the winner set. -/
instance {ι : Type*} (S : ConstraintSystem Input Output ι) (σ : Ranking ι n) (i : Input)
    (o : Output) : Decidable (PicksAt S σ i o) :=
  decidable_of_iff _ picksAt_iff.symm

theorem sum_card_filter_picksAt [DecidableRel r]
    (h_ne : (S.gen i).Nonempty) (h_inj : Set.InjOn (fun o ↦ (S.con · (i, o))) (S.gen i)) :
    ∑ o ∈ S.gen i, ((consistentTotalOrders r).filter
      (fun σ => PicksAt S σ i o)).card = (consistentTotalOrders r).card := by
  classical
  have h_disjoint : (↑(S.gen i) : Set Output).PairwiseDisjoint
      (fun o => (consistentTotalOrders r).filter (fun σ => PicksAt S σ i o)) := by
    intro o _ o' _ hne'
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
    rintro σ ⟨_, h₁⟩ ⟨_, h₂⟩
    exact hne' (picksAt_unique h₁ h₂)
  have h_union : (S.gen i).biUnion (fun o => (consistentTotalOrders r).filter
      (fun σ => PicksAt S σ i o)) = consistentTotalOrders r := by
    ext σ
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨o, _, hσ, _⟩; exact hσ
    · intro hσ
      obtain ⟨o, ho, hpick⟩ := exists_picksAt h_ne h_inj σ
      exact ⟨o, ho, hσ, hpick⟩
  calc ∑ o ∈ S.gen i, ((consistentTotalOrders r).filter
        (fun σ => PicksAt S σ i o)).card
      = ((S.gen i).biUnion (fun o => (consistentTotalOrders r).filter
          (fun σ => PicksAt S σ i o))).card :=
        (Finset.card_biUnion h_disjoint).symm
    _ = (consistentTotalOrders r).card := by rw [h_union]

theorem card_filter_picksAt_binary_add [DecidableRel r]
    {o₁ o₂ : Output} (h_two : S.gen i = {o₁, o₂}) (h_ne : o₁ ≠ o₂)
    (h_vp : (S.con · (i, o₁)) ≠ (S.con · (i, o₂))) :
    ((consistentTotalOrders r).filter (fun σ => PicksAt S σ i o₁)).card +
      ((consistentTotalOrders r).filter (fun σ => PicksAt S σ i o₂)).card =
    (consistentTotalOrders r).card := by
  have h_inj : Set.InjOn (fun o ↦ (S.con · (i, o))) (S.gen i) := by
    intro o ho o' ho' hvv
    rw [h_two] at ho ho'
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at ho ho'
    rcases ho with rfl | rfl <;> rcases ho' with rfl | rfl <;>
      first | rfl | exact absurd hvv h_vp | exact absurd hvv.symm h_vp
  have h := sum_card_filter_picksAt (r := r)
    (by rw [h_two]; exact Finset.insert_nonempty _ _) h_inj
  rwa [h_two, Finset.sum_pair h_ne] at h

omit [DecidableEq Output] in
/-- With pairwise-distinct violation profiles every ranking picks exactly one candidate, so under
any probability measure on rankings, a POC grammar's or stochastic OT's, the candidates'
probabilities sum to one. -/
theorem sum_measure_setOf_picksAt (μ : Measure (Ranking (Fin n) n)) [IsProbabilityMeasure μ]
    (h_ne : (S.gen i).Nonempty) (h_inj : Set.InjOn (fun o ↦ (S.con · (i, o))) (S.gen i)) :
    ∑ o ∈ S.gen i, μ {σ | PicksAt S σ i o} = 1 := by
  rw [← measure_biUnion_finset (f := fun o ↦ {σ | PicksAt S σ i o})
      (fun _ _ _ _ hne ↦ Set.disjoint_left.mpr fun _ h h' ↦ hne (picksAt_unique h h'))
      fun _ _ ↦ .of_discrete, ← measure_univ (μ := μ)]
  congr 1
  refine Set.eq_univ_of_forall fun σ ↦ ?_
  obtain ⟨o, ho, h⟩ := exists_picksAt h_ne h_inj σ
  exact Set.mem_biUnion ho h

/-! ### Binary competitions are decided by the earliest active constraint

For binary candidate sets `S.gen i = {chosen, other}`, `PicksAt σ i chosen` reduces to lex
domination of the permuted profile of `chosen`, which is decided at the first position where the
profiles differ. So `chosen` wins exactly when the σ-earliest constraint of
`active S.con i chosen other`, the one at which `σ.symm` is least, lies in
`favoring S.con i chosen other`. Counting rankings by their σ-earliest active constraint
(`Equiv.Perm.card_filter_isMinOn_symm_mul_card`) then gives closed-form rates for binary POC
competitions without enumerating rankings. -/

omit [DecidableEq Output] in
theorem lex_lt_iff_exists_favoring_isMinOn (σ : Ranking (Fin n) n) :
    toLex (fun k : Fin n => con (σ k) (i, o)) < toLex (fun k : Fin n => con (σ k) (i, o')) ↔
    ∃ x ∈ favoring con i o o' ∩ active con i o o', IsMinOn σ.symm (active con i o o') x := by
  have hle := satisfiedBy_ercOfProfiles_iff_le σ (con · (i, o)) (con · (i, o'))
  constructor
  · intro hlt
    have hne : ∃ k, ercOfProfiles (con · (i, o)) (con · (i, o')) k ≠ .e := by
      by_contra! h
      exact hlt.ne (congrArg toLex (funext fun k ↦ (ercOfProfiles_eq_e_iff _ _ _).1 (h (σ k))))
    obtain ⟨x, hx, hmin⟩ := (ERC.satisfiedBy_iff_exists_isMinOn hne).1 (hle.2 hlt.le)
    have hxf : x ∈ favoring con i o o' := mem_filter.2 ⟨mem_univ x, hx⟩
    exact ⟨x, mem_inter.2 ⟨hxf, favoring_subset_active hxf⟩, hmin⟩
  · rintro ⟨x, hx, hmin⟩
    obtain ⟨hxf, hxa⟩ := mem_inter.1 hx
    refine lt_of_le_of_ne (hle.1 ((ERC.satisfiedBy_iff_exists_isMinOn
      ⟨x, (mem_filter.1 hxa).2⟩).2 ⟨x, (mem_filter.1 hxf).2, hmin⟩)) fun heq ↦ mem_active.1 hxa ?_
    simpa using show con (σ (σ.symm x)) (i, o) = con (σ (σ.symm x)) (i, o') from
      congrFun heq (σ.symm x)

/-- For binary candidate sets, `PicksAt σ i chosen` holds exactly when the σ-earliest active
constraint favors `chosen`. -/
theorem picksAt_binary_iff_exists_favoring_isMinOn
    (h_two : S.gen i = {chosen, other}) (h_ne : chosen ≠ other) (σ : Ranking (Fin n) n) :
    PicksAt S σ i chosen ↔
    ∃ x ∈ favoring S.con i chosen other ∩ active S.con i chosen other,
      IsMinOn σ.symm (active S.con i chosen other) x :=
  (Tableau.optimal_eq_singleton_iff_pair h_two h_ne).trans (lex_lt_iff_exists_favoring_isMinOn σ)

/-! ### Closed-form rate for binary candidates

A binary competition is won exactly by the rankings satisfying the winner–loser ERC of the pair,
whose winner-preferring and non-neutral constraints are `favoring` and `active`, and a uniformly
random ranking satisfies an ERC with a non-neutral constraint at rate `|W| / |W ∪ L|`
(`ERC.card_filter_satisfiedBy_mul_card`). -/

/-- A uniformly random ranking satisfies an ERC with a non-neutral constraint at rate
`|W| / |W ∪ L|`. -/
theorem ERC.uniformOn_real_satisfiedBy (α : ERC (Fin n)) (h : ∃ k, α k ≠ .e) :
    (uniformOn (Set.univ : Set (Ranking (Fin n) n))).real {σ | α.SatisfiedBy σ} =
      (#{k | α k = .W} : ℝ) / #{k | α k ≠ .e} := by
  obtain ⟨k, hk⟩ := h
  rw [← Finset.coe_univ, uniformOn_finset_real_setOf, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, div_eq_div_iff (by positivity)
      (by exact_mod_cast (Finset.card_pos.2 ⟨k, mem_filter.2 ⟨mem_univ k, hk⟩⟩).ne')]
  exact_mod_cast α.card_filter_satisfiedBy_mul_card.trans (Nat.mul_comm _ _)

/-- Under the discrete grammar, with every ranking a linear extension, the uniform measure on
rankings picks `chosen` at rate `|favoring| / |active|`. -/
theorem uniformOn_real_picksAt_discrete_binary
    (h_two : S.gen i = {chosen, other}) (h_ne : chosen ≠ other) :
    (uniformOn (Set.univ : Set (Ranking (Fin n) n))).real {σ | PicksAt S σ i chosen} =
      ((favoring S.con i chosen other).card : ℝ) / (active S.con i chosen other).card := by
  rcases (active S.con i chosen other).eq_empty_or_nonempty with h | ⟨k, hk⟩
  · -- no constraint distinguishes the pair, so no ranking picks `chosen`
    have : {σ : Ranking (Fin n) n | PicksAt S σ i chosen} = ∅ :=
      Set.eq_empty_of_forall_notMem fun σ hσ ↦ by
        obtain ⟨x, hx, -⟩ := (picksAt_binary_iff_exists_favoring_isMinOn h_two h_ne σ).1 hσ
        simp [h] at hx
    rw [this, h, card_empty, Nat.cast_zero, div_zero, measureReal_empty]
  · convert (ercOfProfiles (S.con · (i, chosen)) (S.con · (i, other))).uniformOn_real_satisfiedBy
      ⟨k, (mem_filter.1 hk).2⟩ using 3 <;> try rfl
    ext σ
    refine (picksAt_binary_iff_exists_favoring_isMinOn h_two h_ne σ).trans
      ((exists_congr fun x ↦ ?_).trans
        (ERC.satisfiedBy_iff_exists_isMinOn ⟨k, (mem_filter.1 hk).2⟩).symm)
    rw [mem_inter, and_iff_left_of_imp (favoring_subset_active ·)]
    exact and_congr (mem_filter.trans (and_iff_right (mem_univ x))) Iff.rfl

/-! ### Deciding-stratum rate for stratified grammars

A binary competition whose variants tie on every stratum before `k` is decided within stratum
`k`, and later strata, including any inner rankings among them, are provably irrelevant. This is
[anttila-1997]'s tableau-count shortcut stated against the full grammar rather than a per-stratum
sub-grammar. -/

omit [DecidableEq Output] in
theorem isMinOn_active_iff_isMinOn_filter_stratum
    {stratumOf : Fin n → Fin s} {inner : Fin n → Fin n → Prop} {k : Fin s}
    (hσ : IsConsistent (stratified stratumOf inner) σ)
    (h_tie : ∀ c, stratumOf c < k → S.con c (i, chosen) = S.con c (i, other))
    (h_dec : ((active S.con i chosen other).filter (stratumOf · = k)).Nonempty) {x : Fin n} :
    x ∈ active S.con i chosen other ∧ IsMinOn σ.symm (active S.con i chosen other) x ↔
      x ∈ (active S.con i chosen other).filter (stratumOf · = k) ∧
        IsMinOn σ.symm ((active S.con i chosen other).filter (stratumOf · = k)) x := by
  refine ⟨fun ⟨hx, hmin⟩ => ⟨mem_filter.2 ⟨hx, ?_⟩, hmin.of_subset (filter_subset _ _)⟩,
    fun ⟨hx, hmin⟩ => ⟨(mem_filter.1 hx).1, isMinOn_iff.2 fun y hy => ?_⟩⟩
  · obtain ⟨z, hz⟩ := h_dec
    rcases lt_trichotomy (stratumOf x) k with hlt | heq | hgt
    · exact absurd (h_tie x hlt) (mem_active.1 hx)
    · exact heq
    · exact absurd (isMinOn_iff.1 hmin z (mem_filter.1 hz).1)
        (not_le.2 (hσ.symm_lt_of_stratum_lt (by rw [(mem_filter.1 hz).2]; exact hgt)))
  · rcases lt_trichotomy (stratumOf y) k with hlt | heq | hgt
    · exact absurd (h_tie y hlt) (mem_active.1 hy)
    · exact isMinOn_iff.1 hmin y (mem_filter.2 ⟨hy, heq⟩)
    · exact (hσ.symm_lt_of_stratum_lt (by rw [(mem_filter.1 hx).2]; exact hgt)).le

theorem card_filter_picksAt_stratified_binary
    {stratumOf : Fin n → Fin s} {inner : Fin n → Fin n → Prop}
    [IsPartialOrder (Fin n) inner] [DecidableRel inner] {k : Fin s}
    (h_two : S.gen i = {chosen, other}) (h_ne : chosen ≠ other)
    (h_triv : ∀ a b, stratumOf a = k → stratumOf b = k → inner a b → a = b)
    (h_tie : ∀ c, stratumOf c < k → S.con c (i, chosen) = S.con c (i, other))
    (h_dec : ((active S.con i chosen other).filter (stratumOf · = k)).Nonempty) :
    ((consistentTotalOrders (stratified stratumOf inner)).filter
        (fun σ => PicksAt S σ i chosen)).card *
        ((active S.con i chosen other).filter (stratumOf · = k)).card =
      (consistentTotalOrders (stratified stratumOf inner)).card *
        (favoring S.con i chosen other ∩
          (active S.con i chosen other).filter (stratumOf · = k)).card := by
  classical
  set D := (active S.con i chosen other).filter (stratumOf · = k)
  have key (σ) (hσ : σ ∈ consistentTotalOrders (stratified stratumOf inner)) :
      PicksAt S σ i chosen ↔ ∃ x ∈ favoring S.con i chosen other ∩ D, IsMinOn σ.symm D x := by
    have h := fun x => isMinOn_active_iff_isMinOn_filter_stratum (x := x)
      (mem_consistentTotalOrders.mp hσ) h_tie h_dec
    rw [picksAt_binary_iff_exists_favoring_isMinOn h_two h_ne σ]
    constructor
    · rintro ⟨x, hx, hmin⟩
      obtain ⟨hxD, hminD⟩ := (h x).1 ⟨(mem_inter.1 hx).2, hmin⟩
      exact ⟨x, mem_inter.2 ⟨(mem_inter.1 hx).1, hxD⟩, hminD⟩
    · rintro ⟨x, hx, hmin⟩
      obtain ⟨hxA, hminA⟩ := (h x).2 ⟨(mem_inter.1 hx).2, hmin⟩
      exact ⟨x, mem_inter.2 ⟨(mem_inter.1 hx).1, hxA⟩, hminA⟩
  rw [Finset.filter_congr key]
  convert Equiv.Perm.card_filter_isMinOn_symm_mul_card _ D _
    fun y₁ h₁ y₂ h₂ σ hσ => mem_consistentTotalOrders.mpr
      (isConsistent_swap_mul h_triv (Finset.mem_filter.mp h₁).2 (Finset.mem_filter.mp h₂).2
        (mem_consistentTotalOrders.mp hσ))

/-- Under a stratified grammar, the uniform measure on its linear extensions picks `chosen` at
the deciding-stratum rate `|favoring ∩ Dₖ| / |Dₖ|`. -/
theorem uniformOn_real_picksAt_stratified_binary
    {stratumOf : Fin n → Fin s} {inner : Fin n → Fin n → Prop}
    [IsPartialOrder (Fin n) inner] [DecidableRel inner] {k : Fin s}
    (h_two : S.gen i = {chosen, other}) (h_ne : chosen ≠ other)
    (h_triv : ∀ a b, stratumOf a = k → stratumOf b = k → inner a b → a = b)
    (h_tie : ∀ c, stratumOf c < k → S.con c (i, chosen) = S.con c (i, other))
    (h_dec : ((active S.con i chosen other).filter (stratumOf · = k)).Nonempty) :
    (uniformOn (consistentTotalOrders (stratified stratumOf inner) : Set (Ranking (Fin n) n))).real
        {σ | PicksAt S σ i chosen} =
      ((favoring S.con i chosen other ∩
          (active S.con i chosen other).filter (stratumOf · = k)).card : ℝ) /
        ((active S.con i chosen other).filter (stratumOf · = k)).card := by
  rw [uniformOn_finset_real_setOf, div_eq_div_iff
    (by exact_mod_cast (consistentTotalOrders_card_pos _).ne')
    (by exact_mod_cast h_dec.card_pos.ne')]
  exact_mod_cast (card_filter_picksAt_stratified_binary h_two h_ne h_triv h_tie h_dec).trans
    (Nat.mul_comm _ _)

/-! ### Categorical outcomes under stratified grammars -/

omit [DecidableEq Output] in
theorem picksAt_stratified_of_dominates
    {stratumOf : Fin n → Fin s} {inner : Fin n → Fin n → Prop}
    (hσ : IsConsistent (stratified stratumOf inner) σ) (ho : o ∈ S.gen i)
    (h : ∀ o' ∈ S.gen i, o' ≠ o → ∃ k : Fin s,
      (∀ c, stratumOf c < k → S.con c (i, o) = S.con c (i, o')) ∧
      ((active S.con i o o').filter (stratumOf · = k)).Nonempty ∧
      (active S.con i o o').filter (stratumOf · = k) ⊆ favoring S.con i o o') :
    PicksAt S σ i o := by
  refine picksAt_iff.2 ⟨ho, fun o' ho' hne => ?_⟩
  obtain ⟨k, h_tie, h_dec, h_sub⟩ := h o' ho' hne
  obtain ⟨x, hx, hmin⟩ := Equiv.Perm.exists_isMinOn_symm h_dec σ
  obtain ⟨hxA, hminA⟩ := (isMinOn_active_iff_isMinOn_filter_stratum hσ h_tie h_dec).2 ⟨hx, hmin⟩
  exact (lex_lt_iff_exists_favoring_isMinOn σ).2 ⟨x, mem_inter.2 ⟨h_sub hx, hxA⟩, hminA⟩

omit [DecidableEq Output] in
/-- A candidate dominating every rival at the deciding stratum wins with probability one. -/
theorem uniformOn_picksAt_stratified_eq_one
    {stratumOf : Fin n → Fin s} {inner : Fin n → Fin n → Prop}
    [IsPartialOrder (Fin n) inner] [DecidableRel inner] (ho : o ∈ S.gen i)
    (h : ∀ o' ∈ S.gen i, o' ≠ o → ∃ k : Fin s,
      (∀ c, stratumOf c < k → S.con c (i, o) = S.con c (i, o')) ∧
      ((active S.con i o o').filter (stratumOf · = k)).Nonempty ∧
      (active S.con i o o').filter (stratumOf · = k) ⊆ favoring S.con i o o') :
    uniformOn (consistentTotalOrders (stratified stratumOf inner) : Set (Ranking (Fin n) n))
      {σ | PicksAt S σ i o} = 1 :=
  uniformOn_eq_one_of (Set.toFinite _) (consistentTotalOrders_nonempty _) fun _ hσ ↦
    picksAt_stratified_of_dominates (mem_consistentTotalOrders.mp (Finset.mem_coe.mp hσ)) ho h

end OptimalityTheory
