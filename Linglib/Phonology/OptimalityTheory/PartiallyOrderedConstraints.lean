module

public import Linglib.Phonology.OptimalityTheory.ElementaryRankingCondition
public import Linglib.Phonology.OptimalityTheory.Grammar
public import Linglib.Phonology.OptimalityTheory.Typology
public import Linglib.Core.GroupTheory.Perm.MinOn
public import Linglib.Core.Probability.UniformOn
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Order.Preorder.Finite

/-!
# Partially ordered constraints

This file defines the partially ordered constraints model of variation of Kiparsky and Anttila. A
grammar is a partial order `r` on the constraints, and each evaluation uses one of its linear
extensions, a total ranking, whose sole winner is the output. Anttila reads the grammar
quantitatively: a candidate that wins under $n$ of the $t$ linear extensions has probability
$n/t$, so the grammar is the uniform measure on its linear extensions and the
[probabilities of the candidates sum to one](##sum_measure_setOf_picksAt). The same measure is
defined on any `Grammar.Enumeration`, where a candidate's probability is the
[share of the grammar's rankings](##OptimalityTheory.Grammar.Enumeration.uniformOn_extent_picksAt)
that satisfy the candidate's ERCs.

A ranking satisfies an ERC strictly when its earliest non-neutral constraint is winner-preferring.
When the grammar ranks a set `D` of the non-neutral constraints above the others and its
automorphisms act transitively on `D`, each member of `D` comes first equally often, and the ERC
holds at the rate [$|W ∩ D| / |D|$](##OptimalityTheory.ERC.uniformOn_real_lex_pos). A competition
between two candidates is [strict satisfaction of their ERC](##picksAt_binary_iff_lex_pos), so
this is the rate at which a candidate wins. Free ranking of all the constraints and Tesar and
Smolensky's stratified hierarchies are the two cases used in practice.

## Implementation notes

Sole winners need strict satisfaction of an ERC, `toLex 0 < toLex (α ∘ σ)`, where
`ERC.SatisfiedBy` is the weak inequality. The rate theorems are stated for the strict form, which
needs no side condition that some constraint be non-neutral.

## References

* [P. Kiparsky, *An OT Perspective on Phonological Variation* (1993)][kiparsky-1993b]
* [A. Anttila, *Deriving Variation from Grammar* (1997)][anttila-1997]
* [B. Tesar and P. Smolensky, *The Learnability of Optimality Theory* (1995)][tesar-smolensky-1995]
* [A. Prince, *Entailed Ranking Arguments* (2002)][prince-2002]
* [N. Merchant and J. Riggle, *OT grammars, beyond partial orders: ERC sets and antimatroids*
  (2016)][merchant-riggle-2016]
* [J. Riggle, *Sampling Rankings* (2010)][riggle-2010]
-/

@[expose] public section

namespace OptimalityTheory

open Finset MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-! ### The quantitative interpretation

A grammar draws one of its linear extensions uniformly at each evaluation ([anttila-1997]), so it
is the probability measure `uniformOn ↑(Ranking.Enumeration.linearExtensions r)` on rankings, and
the
probability that it selects `o` for the input `i` is that measure at `{σ | S.PicksAt σ i o}`: the
fraction of the linear extensions that pick `o`. -/

instance (r : ι → ι → Prop) [IsPartialOrder ι r] [DecidableRel r] [h : Nonempty
    (Ranking.Enumeration ι n)] :
    IsProbabilityMeasure
      (uniformOn ((Ranking.Enumeration.linearExtensions r : Finset
          (Ranking.Enumeration ι n)) : Set (Ranking.Enumeration ι n))) :=
  isProbabilityMeasure_uniformOn (Set.toFinite _)
    (Ranking.Enumeration.linearExtensions_nonempty r h.some.card_eq)

variable {Input Output : Type*}
variable {S : ConstraintSystem Input Output ι} {con : ConstraintSet (Input × Output) ι}
  {r : ι → ι → Prop} {σ : Ranking.Enumeration ι n} {i : Input} {o o' chosen other : Output}

omit [Fintype ι] [DecidableEq ι] in
/-- With pairwise distinct violation profiles every ranking picks exactly one candidate, so under
any probability measure on rankings, a partially ordered grammar's or stochastic OT's, the
candidates' probabilities sum to one. -/
theorem sum_measure_setOf_picksAt (μ : Measure (Ranking.Enumeration ι n)) [IsProbabilityMeasure μ]
    (h_ne : (S.gen i).Nonempty) (h_inj : Set.InjOn (fun o ↦ (S.marks i o)) (S.gen i)) :
    ∑ o ∈ S.gen i, μ {σ | S.PicksAt σ i o} = 1 := by
  rw [← measure_biUnion_finset (f := fun o ↦ {σ | S.PicksAt σ i o})
      (fun _ _ _ _ hne ↦ Set.disjoint_left.mpr fun _ h h' ↦ hne (h.unique h'))
      fun _ _ ↦ .of_discrete, ← measure_univ (μ := μ)]
  congr 1
  refine Set.eq_univ_of_forall fun σ ↦ ?_
  obtain ⟨o, ho, h⟩ := ConstraintSystem.exists_picksAt h_ne h_inj σ
  exact Set.mem_biUnion ho h

/-- The linear extensions of a grammar are partitioned by the candidate they pick. -/
theorem sum_card_filter_picksAt [DecidableEq Output] [DecidableRel r] (h_ne : (S.gen i).Nonempty)
    (h_inj : Set.InjOn (fun o ↦ (S.marks i o)) (S.gen i)) :
    ∑ o ∈ S.gen i, #{σ ∈ Ranking.Enumeration.linearExtensions (n := n) r | S.PicksAt σ i o} =
      #(Ranking.Enumeration.linearExtensions (n := n) r) := by
  classical
  rw [← card_biUnion fun o _ o' _ hne ↦ disjoint_left.2 fun σ h h' ↦
    hne ((mem_filter.1 h).2.unique (mem_filter.1 h').2)]
  congr 1
  ext σ
  simp only [mem_biUnion, mem_filter]
  refine ⟨fun ⟨_, _, hσ, _⟩ ↦ hσ, fun hσ ↦ ?_⟩
  obtain ⟨o, ho, h⟩ := ConstraintSystem.exists_picksAt h_ne h_inj σ
  exact ⟨o, ho, hσ, h⟩

theorem card_filter_picksAt_binary_add [DecidableEq Output] [DecidableRel r] {o₁ o₂ : Output}
    (h_two : S.gen i = {o₁, o₂}) (h_ne : o₁ ≠ o₂)
    (h_vp : (S.marks i o₁) ≠ (S.marks i o₂)) :
    #{σ ∈ Ranking.Enumeration.linearExtensions (n := n) r | S.PicksAt σ i o₁} +
        #{σ ∈ Ranking.Enumeration.linearExtensions (n := n) r | S.PicksAt σ i o₂} =
      #(Ranking.Enumeration.linearExtensions (n := n) r) := by
  have h_inj : Set.InjOn (fun o ↦ (S.marks i o)) (S.gen i) := by
    intro o ho o' ho' hvv
    rw [h_two] at ho ho'
    simp only [coe_insert, Set.mem_insert_iff, coe_singleton, Set.mem_singleton_iff] at ho ho'
    rcases ho with rfl | rfl <;> rcases ho' with rfl | rfl <;>
      first | rfl | exact absurd hvv h_vp | exact absurd hvv.symm h_vp
  have h := sum_card_filter_picksAt (n := n) (r := r) (h_two ▸ insert_nonempty _ _) h_inj
  rwa [h_two, sum_pair h_ne] at h

/-! ### The measure of a grammar

The uniform measure is defined on the rankings of any grammar. With pairwise distinct violation
profiles a candidate is picked exactly by the rankings that satisfy its ERC against each rival, so
its probability is the number of rankings of the grammar that satisfy those ERCs over the number
of all its rankings, the two counts that [riggle-2010] calls r-volumes. -/

section Grammar.Enumeration

open scoped ENNReal

omit [Fintype ι] [DecidableEq ι] in
theorem Grammar.Enumeration.isProbabilityMeasure_uniformOn (G : Grammar.Enumeration ι n)
    (h : G.extent.Nonempty) :
    IsProbabilityMeasure (uniformOn G.extent) :=
  ProbabilityTheory.isProbabilityMeasure_uniformOn G.extent.toFinite h

omit [Fintype ι] [DecidableEq ι] in
/-- The uniform measure on the rankings of a grammar gives another grammar the share of the
rankings that the two have in common. -/
theorem Grammar.Enumeration.uniformOn_extent (G H : Grammar.Enumeration ι n) :
    uniformOn G.extent H.extent = ((G ⊓ H).extent.ncard : ℝ≥0∞) / G.extent.ncard := by
  rw [uniformOn_apply_of_finite G.extent.toFinite, Concept.extent_inf]

omit [Fintype ι] [DecidableEq ι] in
/-- The probability of a candidate under a grammar is the share of the grammar's rankings that
satisfy the candidate's ERCs: Anttila's $n/t$ as a ratio of r-volumes. -/
theorem Grammar.Enumeration.uniformOn_extent_picksAt (G : Grammar.Enumeration ι n)
    (ho : o ∈ S.gen i)
    (hvp : ∀ o' ∈ S.gen i, o' ≠ o → (S.marks i o) ≠ (S.marks i o')) :
    uniformOn G.extent {σ | S.PicksAt σ i o} =
      ((G ⊓ .ofERCs (S.ercs i o)).extent.ncard : ℝ≥0∞) / G.extent.ncard := by
  rw [← Grammar.Enumeration.uniformOn_extent]
  congr 1
  ext σ
  exact ConstraintSystem.picksAt_iff_forall_ercs_satisfiedBy ho hvp

omit [Fintype ι] [DecidableEq ι] in
/-- A grammar predicts a candidate, giving it nonzero probability, iff the candidate wins under
one of its rankings ([anttila-1997]). -/
theorem Grammar.Enumeration.uniformOn_extent_picksAt_ne_zero_iff (G : Grammar.Enumeration ι n) :
    uniformOn G.extent {σ | S.PicksAt σ i o} ≠ 0 ↔ ∃ σ ∈ G.extent, S.PicksAt σ i o :=
  uniformOn_ne_zero_iff G.extent.toFinite

end Grammar.Enumeration

/-! ### Categorical outcomes -/

omit [Fintype ι] [DecidableEq ι] in
/-- A candidate is picked by every linear extension of a grammar if, against each rival, some
constraint that favors it is ranked by the grammar above every constraint that favors the
rival. -/
theorem Ranking.Enumeration.IsLinearExtension.picksAt (hσ : σ.IsLinearExtension r)
    (ho : o ∈ S.gen i)
    (h : ∀ o' ∈ S.gen i, o' ≠ o → ∃ w, S.marks i o w < S.marks i o' w ∧
      ∀ l, S.marks i o' l < S.marks i o l → r w l) :
    S.PicksAt σ i o :=
  Ranking.Enumeration.optimal_eq_singleton_iff.2 ⟨ho, fun o' ho' hne ↦
    (h o' ho' hne).imp fun w ⟨hw, hl⟩ ↦ ⟨hw, fun l hlt ↦ lt_of_le_of_ne (hσ w l (hl l hlt))
      fun heq ↦ lt_asymm hw (σ.symm.injective heq ▸ hlt)⟩⟩

/-! ### The rate of an ERC

A ranking satisfies an ERC strictly when its earliest non-neutral constraint is winner-preferring
(`ERC.lex_pos_iff_exists_isMinOn`). Suppose a grammar ranks a set `D` of the non-neutral
constraints above the remaining ones, and its automorphisms that preserve `D` act transitively on
`D`, as when `D` is freely ranked. Then every linear extension decides the ERC at its earliest
member of `D`, and the linear extensions put each member of `D` earliest equally often
(`Equiv.card_filter_isMinOn_symm_mul_card`), so the ERC holds in the fraction
`|W ∩ D| / |D|` of them. -/

section Rate

variable {α : ERC ι} {D : Finset ι}

/-- The linear extensions of a grammar that strictly satisfy an ERC, counted against all of them,
when the grammar ranks a set `D` of non-neutral constraints above the other non-neutral ones and
its automorphisms preserving `D` act transitively on `D`: their number times `|D|` is the number
of linear extensions times `|W ∩ D|`. -/
theorem ERC.card_filter_lex_pos_mul_card [DecidableRel r] (hD : D ⊆ α.support)
    (h_lead : ∀ a ∈ α.support, a ∉ D → ∃ d ∈ D, r d a)
    (h_aut : ∀ d ∈ D, ∀ d' ∈ D, ∃ g : Equiv.Perm ι,
      g d = d' ∧ (∀ z, g z ∈ D ↔ z ∈ D) ∧ g ⁻¹'o r = r) :
    #((Ranking.Enumeration.linearExtensions r).filter
        fun σ : Ranking.Enumeration ι n ↦ toLex 0 < toLex (α ∘ σ)) * #D =
      #(Ranking.Enumeration.linearExtensions (n := n) r) * #(α.W ∩ D) := by
  classical
  have key (σ : Ranking.Enumeration ι n) (hσ : σ ∈ Ranking.Enumeration.linearExtensions r) :
      toLex 0 < toLex (α ∘ σ) ↔ ∃ x ∈ α.W ∩ D, IsMinOn σ.symm D x := by
    rw [Ranking.Enumeration.mem_linearExtensions] at hσ
    rw [ERC.lex_pos_iff_exists_isMinOn]
    refine ⟨fun ⟨x, hx, hmin⟩ ↦ ?_, fun ⟨x, hx, hmin⟩ ↦ ?_⟩
    · have hxD : x ∈ D := by
        by_contra hxD
        obtain ⟨d, hd, hdx⟩ := h_lead x (ERC.W_subset_support hx) hxD
        exact hxD (σ.symm.injective ((hσ d x hdx).antisymm (isMinOn_iff.1 hmin d (hD hd))) ▸ hd)
      exact ⟨x, mem_inter.2 ⟨hx, hxD⟩, hmin.of_subset (coe_subset.2 hD)⟩
    · refine ⟨x, (mem_inter.1 hx).1, isMinOn_iff.2 fun a ha ↦ ?_⟩
      by_cases haD : a ∈ D
      · exact isMinOn_iff.1 hmin a haD
      · obtain ⟨d, hd, hda⟩ := h_lead a ha haD
        exact (isMinOn_iff.1 hmin d hd).trans (hσ d a hda)
  have hS : ∀ d ∈ D, ∀ d' ∈ D, ∃ g : Equiv.Perm ι, g d = d' ∧ (∀ z, g z ∈ D ↔ z ∈ D) ∧
      ∀ σ : Ranking.Enumeration ι n, σ.trans g ∈ Ranking.Enumeration.linearExtensions r ↔
        σ ∈ Ranking.Enumeration.linearExtensions r :=
      fun d hd d' hd' ↦ by
    obtain ⟨g, hgd, hgD, hg⟩ := h_aut d hd d' hd'
    exact ⟨g, hgd, hgD, fun σ ↦ by
      rw [Ranking.Enumeration.mem_linearExtensions, Ranking.Enumeration.mem_linearExtensions,
        Ranking.Enumeration.isLinearExtension_trans_iff, hg]⟩
  rw [filter_congr key]
  convert Equiv.card_filter_isMinOn_symm_mul_card _ D _ hS

/-- When a grammar ranks a set `D` of non-neutral constraints above the other non-neutral ones
and its automorphisms preserving `D` act transitively on `D`, the uniform measure on its linear
extensions strictly satisfies the ERC at the rate `|W ∩ D| / |D|`. -/
theorem ERC.uniformOn_real_lex_pos [IsPartialOrder ι r] [DecidableRel r]
    (hD : D ⊆ α.support) (h_lead : ∀ a ∈ α.support, a ∉ D → ∃ d ∈ D, r d a)
    (h_aut : ∀ d ∈ D, ∀ d' ∈ D, ∃ g : Equiv.Perm ι,
      g d = d' ∧ (∀ z, g z ∈ D ↔ z ∈ D) ∧ g ⁻¹'o r = r)
    (hn : Fintype.card ι = n := by simp) :
    (uniformOn ((Ranking.Enumeration.linearExtensions r : Finset (Ranking.Enumeration ι n)) : Set
        (Ranking.Enumeration ι n))).real
        {σ : Ranking.Enumeration ι n | toLex 0 < toLex (α ∘ σ)} = (#(α.W ∩ D) : ℝ) / #D := by
  rw [uniformOn_finset_real_setOf]
  rcases D.eq_empty_or_nonempty with rfl | hne
  · -- every constraint is neutral, so no ranking satisfies the ERC strictly
    have : (Ranking.Enumeration.linearExtensions (n := n) r).filter
        (fun σ : Ranking.Enumeration ι n ↦ toLex 0 < toLex (α ∘ σ)) = ∅ :=
      filter_eq_empty_iff.2 fun σ _ hσ ↦ by
        obtain ⟨x, hx, -⟩ := ERC.lex_pos_iff_exists_isMinOn.1 hσ
        obtain ⟨d, hd, -⟩ := h_lead x (ERC.W_subset_support hx) (notMem_empty x)
        exact notMem_empty d hd
    rw [this, card_empty, inter_empty, card_empty, Nat.cast_zero, zero_div, div_zero]
  · have hpos := (Ranking.Enumeration.linearExtensions_nonempty r hn).card_pos
    rw [div_eq_div_iff (by exact_mod_cast hpos.ne') (by exact_mod_cast hne.card_pos.ne')]
    exact_mod_cast (ERC.card_filter_lex_pos_mul_card hD h_lead h_aut).trans (Nat.mul_comm _ _)

/-- A uniformly random ranking satisfies an ERC with a non-neutral constraint at the rate
`|W| / |W ∪ L|`. -/
theorem ERC.uniformOn_real_satisfiedBy (α : ERC ι) (h : ∃ k, α k ≠ .e)
    (hn : Fintype.card ι = n := by simp) :
    (uniformOn (Set.univ : Set (Ranking.Enumeration ι n))).real {σ | α.SatisfiedBy σ} =
      (#α.W : ℝ) / #α.support := by
  obtain ⟨k, hk⟩ := h
  rw [← Finset.coe_univ, uniformOn_finset_real_setOf, Finset.card_univ,
    Ranking.Enumeration.card_eq_factorial hn, div_eq_div_iff (by positivity)
      (by exact_mod_cast (Finset.card_pos.2 ⟨k, ERC.mem_support.2 hk⟩).ne')]
  exact_mod_cast
      (Ranking.Enumeration.card_eq_factorial hn ▸ α.card_filter_satisfiedBy_mul_card).trans
    (Nat.mul_comm _ _)

end Rate

/-! ### Binary competitions

For a candidate set `{chosen, other}`, picking `chosen` is strict satisfaction of the winner–loser
ERC of `chosen` against `other`. So `chosen` wins exactly when the earliest of the constraints
active on the pair favors it, and the rates of an ERC are the rates at which `chosen` wins. This is
Anttila's observation that the tableaux need not be drawn: the count of the freely ranked
constraints on each side gives the result. -/

/-- The constraints *active* on the candidates `o` and `o'` of the input `i` are those assigning
them different violations, the non-neutral constraints of the winner–loser ERC of `o` against
`o'`. An inactive constraint cannot affect the competition ([anttila-1997]). -/
def active (con : ConstraintSet (Input × Output) ι) (i : Input) (o o' : Output) :
    Finset ι :=
  (ercOfProfiles (con · (i, o)) (con · (i, o'))).support

/-- The constraints *favoring* `o` over `o'` at the input `i` are those assigning `o` strictly
fewer violations, the winner-preferring constraints of the winner–loser ERC of `o` against
`o'`. -/
def favoring (con : ConstraintSet (Input × Output) ι) (i : Input) (o o' : Output) :
    Finset ι :=
  (ercOfProfiles (con · (i, o)) (con · (i, o'))).W

omit [DecidableEq ι] in
@[simp] theorem mem_active {c : ι} :
    c ∈ active con i o o' ↔ con c (i, o) ≠ con c (i, o') :=
  mem_support_ercOfProfiles

omit [DecidableEq ι] in
@[simp] theorem mem_favoring {c : ι} :
    c ∈ favoring con i o o' ↔ con c (i, o) < con c (i, o') :=
  mem_W_ercOfProfiles

omit [DecidableEq ι] in
theorem favoring_subset_active : favoring con i o o' ⊆ active con i o o' :=
  ERC.W_subset_support

variable [DecidableEq Output]

omit [Fintype ι] [DecidableEq ι] in
/-- A ranking picks `chosen` from the candidates `{chosen, other}` exactly when it strictly
satisfies the winner–loser ERC of `chosen` against `other`. -/
theorem picksAt_binary_iff_lex_pos (h_two : S.gen i = {chosen, other}) (h_ne : chosen ≠ other)
    (σ : Ranking.Enumeration ι n) :
    S.PicksAt σ i chosen ↔
      toLex 0 < toLex (ercOfProfiles (S.marks i chosen) (S.marks i other) ∘ σ) :=
  (Ranking.Enumeration.optimal_eq_singleton_iff_pair h_two h_ne).trans
    (lex_pos_ercOfProfiles_iff_lt σ (S.marks i chosen) (S.marks i other)).symm

omit [DecidableEq ι] in
/-- A ranking picks `chosen` from the candidates `{chosen, other}` exactly when the earliest
constraint active on the pair favors `chosen`. -/
theorem picksAt_binary_iff_exists_favoring_isMinOn
    (h_two : S.gen i = {chosen, other}) (h_ne : chosen ≠ other) (σ : Ranking.Enumeration ι n) :
    S.PicksAt σ i chosen ↔
      ∃ x ∈ favoring S.con i chosen other, IsMinOn σ.symm (active S.con i chosen other) x :=
  (picksAt_binary_iff_lex_pos h_two h_ne σ).trans ERC.lex_pos_iff_exists_isMinOn

/-- The linear extensions that pick `chosen`, counted against all of them, when the grammar ranks
a set `D` of active constraints above the other active ones and its automorphisms preserving `D`
act transitively on `D`: their number times `|D|` is the number of linear extensions times
`|favoring ∩ D|`. -/
theorem card_filter_picksAt_mul_card [DecidableRel r] {D : Finset ι}
    (h_two : S.gen i = {chosen, other}) (h_ne : chosen ≠ other)
    (hD : D ⊆ active S.con i chosen other)
    (h_lead : ∀ a ∈ active S.con i chosen other, a ∉ D → ∃ d ∈ D, r d a)
    (h_aut : ∀ d ∈ D, ∀ d' ∈ D, ∃ g : Equiv.Perm ι,
      g d = d' ∧ (∀ z, g z ∈ D ↔ z ∈ D) ∧ g ⁻¹'o r = r) :
    #{σ ∈ Ranking.Enumeration.linearExtensions (n := n) r | S.PicksAt σ i chosen} * #D =
      #(Ranking.Enumeration.linearExtensions
          (n := n) r) * #(favoring S.con i chosen other ∩ D) := by
  rw [filter_congr fun σ _ ↦ picksAt_binary_iff_lex_pos h_two h_ne σ]
  exact ERC.card_filter_lex_pos_mul_card hD h_lead h_aut

/-- Under the same hypotheses, the uniform measure on the linear extensions picks `chosen` at the
rate `|favoring ∩ D| / |D|`. -/
theorem uniformOn_real_picksAt_binary [IsPartialOrder ι r] [DecidableRel r]
    {D : Finset ι} (h_two : S.gen i = {chosen, other}) (h_ne : chosen ≠ other)
    (hD : D ⊆ active S.con i chosen other)
    (h_lead : ∀ a ∈ active S.con i chosen other, a ∉ D → ∃ d ∈ D, r d a)
    (h_aut : ∀ d ∈ D, ∀ d' ∈ D, ∃ g : Equiv.Perm ι,
      g d = d' ∧ (∀ z, g z ∈ D ↔ z ∈ D) ∧ g ⁻¹'o r = r)
    (hn : Fintype.card ι = n := by simp) :
    (uniformOn ((Ranking.Enumeration.linearExtensions r : Finset (Ranking.Enumeration ι n)) : Set
        (Ranking.Enumeration ι n))).real
        {σ | S.PicksAt σ i chosen} =
      (#(favoring S.con i chosen other ∩ D) : ℝ) / #D := by
  have h : {σ | S.PicksAt σ i chosen} =
      {σ : Ranking.Enumeration ι n |
        toLex 0 < toLex (ercOfProfiles (S.marks i chosen) (S.marks i other) ∘ σ)} :=
    Set.ext fun σ ↦ picksAt_binary_iff_lex_pos h_two h_ne σ
  rw [h]
  exact ERC.uniformOn_real_lex_pos hD h_lead h_aut hn

/-- Under the discrete grammar, with every ranking a linear extension, the uniform measure on
rankings picks `chosen` at the rate `|favoring| / |active|`, the r-volume of a candidate of a
pair in [riggle-2010]. -/
theorem uniformOn_real_picksAt_discrete_binary
    (h_two : S.gen i = {chosen, other}) (h_ne : chosen ≠ other)
    (hn : Fintype.card ι = n := by simp) :
    (uniformOn (Set.univ : Set (Ranking.Enumeration ι n))).real {σ | S.PicksAt σ i chosen} =
      (#(favoring S.con i chosen other) : ℝ) / #(active S.con i chosen other) := by
  have h := uniformOn_real_picksAt_binary (r := (· = ·)) (hn := hn) h_two h_ne Subset.rfl
    (fun a ha h ↦ absurd ha h) fun d hd d' hd' ↦
      ⟨Equiv.swap d d', Equiv.swap_apply_left d d', Equiv.Perm.swap_apply_mem_iff hd hd', by
        ext a b
        exact (Equiv.swap d d').injective.eq_iff⟩
  rwa [Ranking.Enumeration.linearExtensions_eq, coe_univ,
    inter_eq_left.2 favoring_subset_active] at h

section Stratified

variable {s : ℕ} {stratumOf : ι → Fin s} {inner : ι → ι → Prop} {k : Fin s}

/-- A binary competition whose candidates tie on every stratum before `k` is decided within
stratum `k`: the linear extensions of a stratified grammar that pick `chosen`, counted `|Dₖ|`
times for `Dₖ` the active constraints of stratum `k`, number `|favoring ∩ Dₖ|` times all of them.
Later strata, and any inner ranking among them, are irrelevant. -/
theorem card_filter_picksAt_stratified_binary [IsPartialOrder ι inner] [DecidableRel inner]
    (h_two : S.gen i = {chosen, other}) (h_ne : chosen ≠ other)
    (h_triv : ∀ a b, stratumOf a = k → stratumOf b = k → inner a b → a = b)
    (h_tie : ∀ c, stratumOf c < k → S.marks i chosen c = S.marks i other c)
    (h_dec : ((active S.con i chosen other).filter (stratumOf · = k)).Nonempty) :
    #{σ ∈ Ranking.Enumeration.linearExtensions (n := n) (stratified stratumOf inner) |
        S.PicksAt σ i chosen} *
        #((active S.con i chosen other).filter (stratumOf · = k)) =
      #(Ranking.Enumeration.linearExtensions (n := n) (stratified stratumOf inner)) *
        #(favoring S.con i chosen other ∩
          (active S.con i chosen other).filter (stratumOf · = k)) := by
  obtain ⟨d, hd⟩ := h_dec
  refine card_filter_picksAt_mul_card h_two h_ne (filter_subset _ _) (fun a ha haD ↦ ?_)
    fun d hd d' hd' ↦ ⟨Equiv.swap d d', Equiv.swap_apply_left d d',
      Equiv.Perm.swap_apply_mem_iff hd hd',
      swap_preimage_stratified h_triv (mem_filter.1 hd).2 (mem_filter.1 hd').2⟩
  refine ⟨d, hd, stratified_iff.2 (.inl ?_)⟩
  rw [(mem_filter.1 hd).2]
  exact lt_of_le_of_ne (not_lt.1 fun hlt ↦ mem_active.1 ha (h_tie a hlt))
    fun hk ↦ haD (mem_filter.2 ⟨ha, hk.symm⟩)

/-- Under a stratified grammar, the uniform measure on its linear extensions picks `chosen` at
the rate `|favoring ∩ Dₖ| / |Dₖ|` of the deciding stratum `k`. -/
theorem uniformOn_real_picksAt_stratified_binary [IsPartialOrder ι inner]
    [DecidableRel inner] (h_two : S.gen i = {chosen, other}) (h_ne : chosen ≠ other)
    (h_triv : ∀ a b, stratumOf a = k → stratumOf b = k → inner a b → a = b)
    (h_tie : ∀ c, stratumOf c < k → S.marks i chosen c = S.marks i other c)
    (h_dec : ((active S.con i chosen other).filter (stratumOf · = k)).Nonempty)
    (hn : Fintype.card ι = n := by simp) :
    (uniformOn ((Ranking.Enumeration.linearExtensions (stratified stratumOf inner) :
      Finset (Ranking.Enumeration ι n)) : Set (Ranking.Enumeration ι n))).real
        {σ | S.PicksAt σ i chosen} =
      (#(favoring S.con i chosen other ∩
          (active S.con i chosen other).filter (stratumOf · = k)) : ℝ) /
        #((active S.con i chosen other).filter (stratumOf · = k)) := by
  rw [uniformOn_finset_real_setOf, div_eq_div_iff
    (by exact_mod_cast (Ranking.Enumeration.linearExtensions_nonempty _ hn).card_pos.ne')
    (by exact_mod_cast h_dec.card_pos.ne')]
  exact_mod_cast (card_filter_picksAt_stratified_binary h_two h_ne h_triv h_tie h_dec).trans
    (Nat.mul_comm _ _)

omit [DecidableEq Output] [DecidableEq ι] in
/-- Under a stratified grammar a candidate is picked if, against each rival, the two tie on every
stratum before some stratum whose active constraints all favor it. -/
theorem picksAt_stratified_of_dominates
    (hσ : σ.IsLinearExtension (stratified stratumOf inner)) (ho : o ∈ S.gen i)
    (h : ∀ o' ∈ S.gen i, o' ≠ o → ∃ k : Fin s,
      (∀ c, stratumOf c < k → S.marks i o c = S.marks i o' c) ∧
      ((active S.con i o o').filter (stratumOf · = k)).Nonempty ∧
      (active S.con i o o').filter (stratumOf · = k) ⊆ favoring S.con i o o') :
    S.PicksAt σ i o :=
  hσ.picksAt ho fun o' ho' hne ↦ by
    obtain ⟨k, h_tie, ⟨x, hx⟩, h_sub⟩ := h o' ho' hne
    refine ⟨x, mem_favoring.1 (h_sub hx), fun l hl ↦ stratified_iff.2 (.inl ?_)⟩
    rw [(mem_filter.1 hx).2]
    exact lt_of_le_of_ne (not_lt.1 fun hlt ↦ hl.ne' (h_tie l hlt)) fun hk ↦
      lt_asymm hl (mem_favoring.1 (h_sub (mem_filter.2 ⟨mem_active.2 hl.ne', hk.symm⟩)))

omit [DecidableEq Output] in
/-- A candidate that dominates every rival at the deciding stratum wins with probability one. -/
theorem uniformOn_picksAt_stratified_eq_one [IsPartialOrder ι inner] [DecidableRel inner]
    (ho : o ∈ S.gen i)
    (h : ∀ o' ∈ S.gen i, o' ≠ o → ∃ k : Fin s,
      (∀ c, stratumOf c < k → S.marks i o c = S.marks i o' c) ∧
      ((active S.con i o o').filter (stratumOf · = k)).Nonempty ∧
      (active S.con i o o').filter (stratumOf · = k) ⊆ favoring S.con i o o')
    (hn : Fintype.card ι = n := by simp) :
    uniformOn ((Ranking.Enumeration.linearExtensions (stratified stratumOf inner) : Finset
        (Ranking.Enumeration ι n)) :
      Set (Ranking.Enumeration ι n)) {σ | S.PicksAt σ i o} = 1 :=
  uniformOn_eq_one_of (Set.toFinite _)
      (Ranking.Enumeration.linearExtensions_nonempty _ hn) fun _ hσ ↦
    picksAt_stratified_of_dominates (Ranking.Enumeration.mem_linearExtensions.1 (mem_coe.1 hσ)) ho h

end Stratified

end OptimalityTheory
