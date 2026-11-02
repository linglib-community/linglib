module

public import Linglib.Logic.Team.QBSML.FreeChoice
public import Linglib.Semantics.Degree.Comparison
public import Linglib.Data.Examples.AloniVanOrmondt2023
public import Mathlib.Tactic.DeriveFintype

/-!
# Aloni and van Ormondt (2023): modified numerals and split disjunction

Superlative modifiers (*at least n*, *at most n*) convey that the speaker does not know the amount,
where comparative modifiers (*more than n*, *fewer than n*) with the same truth conditions do not.
Following Büring, a superlative is the split disjunction of the bare numeral and a comparative,
*at least n* as *n or more*, and Aloni's neglect-zero enrichment, raised to the first-order logic
QBSML, derives the difference. A numeral predicate is a set of amounts. The split [keeps the truth
conditions](##support_translate_iff), but the enriched superlative [leaves the amount
open](##exists_eq_and_exists_gt_of_support_enrich), so [a speaker who knows the amount can assert
only the comparative](##support_enrich_translate_iff_of_settled). Negated, the superlative [says
what the comparative says](##support_enrich_neg_translate_ge), and under a universal quantifier its
disjuncts split over individuals, [obviating the ignorance](##obviation).

## Implementation notes

* The amount of an individual at a world is a function `μ`. A world of the obviation model is the
  amount of each of its two objects, so `w_{PaQb}` is the world where `a` has three and `b` four.
* The free-choice, distribution and negation facts hold for any `NE`-free disjuncts and are the
  theorems of `Logic/Team/QBSML/FreeChoice.lean`; with a state-based accessibility relation,
  `QBSML.ignorance` turns the open amount into the possibilities of exactly `n` and more.

## Errata

* After Fact 3 the paper says the ignorance fact generalises to arbitrary disjuncts. It fails for
  disjuncts with a free variable, which Definition 4.12 admits: the universal extension in the
  proof of Fact 4 is state-based and [supports `[three(x) ∨ more(x)]⁺` but not
  `◇three(x)`](##not_ignorance_fig15).
* On p. 542 example (4a) is repeated as "(3-b)", and on p. 546 the blocked (41) is called "(42)".

## References

* [aloni-vanormondt-2023]
* [aloni-2022]
-/

@[expose] public section

namespace AloniVanOrmondt2023

open QBSML Degree

inductive Var
  | x
  deriving DecidableEq, Repr, Fintype

variable {W Domain Const : Type*} [DecidableEq W] [DecidableEq Domain] [Fintype Domain]

/-! ### Numerals as sets of amounts -/

/-- The model in which a set of amounts holds of an individual at a world when it contains the
individual's amount `μ w d` there, the cardinality `|P ∩ Q|` of the paper's numeral denotations. -/
def amountModel (R : W → Finset W) (κ : W → Const → Domain) (μ : W → Domain → ℕ) :
    Model W Domain Const (Set ℕ) :=
  .ofMonadic R κ fun w A d ↦ μ w d ∈ A

/-- The paper's translation of a numeral modified by `c`, said of `k`: a superlative is the split
disjunction of the bare numeral and the strict comparative, *at least n* as *n or more* and *at most
n* as *n or less*, and a bare or comparative numeral is atomic. -/
def translate (c : Comparison) (n : ℕ) (k : Const) : Formula Var Const (Set ℕ) :=
  match c with
  | .ge => .disj (.predc (Comparison.eq.interval n) k) (.predc (Comparison.gt.interval n) k)
  | .le => .disj (.predc (Comparison.eq.interval n) k) (.predc (Comparison.lt.interval n) k)
  | c => .predc (c.interval n) k

variable {R : W → Finset W} {κ : W → Const → Domain} {μ : W → Domain → ℕ}
  {s : Finset (Index W Var Domain)} {A B : Set ℕ} {k : Const} {c : Comparison} {n m : ℕ}

@[simp] theorem support_predc_amountModel :
    support (amountModel R κ μ) (.predc A k) s ↔ ∀ i ∈ s, μ i.world (κ i.world k) ∈ A :=
  Iff.rfl

@[simp] theorem antiSupport_predc_amountModel :
    antiSupport (amountModel R κ μ) (.predc A k) s ↔ ∀ i ∈ s, μ i.world (κ i.world k) ∉ A :=
  Iff.rfl

theorem support_enrich_predc_amountModel :
    support (amountModel R κ μ) (Formula.predc A k).enrich s ↔
      (∀ i ∈ s, μ i.world (κ i.world k) ∈ A) ∧ s.Nonempty :=
  Iff.rfl

theorem support_disj_predc_amountModel :
    support (amountModel R κ μ) (.disj (.predc A k) (.predc B k)) s ↔
      support (amountModel R κ μ) (.predc (A ∪ B) k) s :=
  Team.mem_tensor_flat

/-- The translation of a modified numeral is supported exactly where the comparison holds of the
amount, so splitting a superlative keeps its truth conditions ((8), (14), (16)). -/
theorem support_translate_iff :
    support (amountModel R κ μ) (translate c n k) s ↔
      ∀ i ∈ s, μ i.world (κ i.world k) ∈ c.interval n := by
  cases c with
  | ge =>
    rw [translate, support_disj_predc_amountModel, Comparison.interval_eq, Comparison.interval_gt,
      Set.singleton_union, Set.Ioi_insert]
    rfl
  | le =>
    rw [translate, support_disj_predc_amountModel, Comparison.interval_eq, Comparison.interval_lt,
      Set.singleton_union, Set.Iio_insert]
    rfl
  | _ => rfl

/-! ### Ignorance -/

private theorem exists_mem_of_support_enrich_disj
    (h : support (amountModel R κ μ) (Formula.disj (.predc A k) (.predc B k)).enrich s) :
    (∃ i ∈ s, μ i.world (κ i.world k) ∈ A) ∧ ∃ i ∈ s, μ i.world (κ i.world k) ∈ B :=
  have ⟨⟨_, hts, ⟨i, hi⟩, ht⟩, _, hus, ⟨j, hj⟩, hu⟩ :=
    witnesses_of_enrich_disj _ (.predc A k) (.predc B k) h
  ⟨⟨i, hts hi, ht i hi⟩, j, hus hj, hu j hj⟩

/-- A state supporting the enriched *at least n* has an index where the amount is exactly `n` and
one where it exceeds `n`: the speaker does not know how many ((2a), (19), (56)). -/
theorem exists_eq_and_exists_gt_of_support_enrich
    (h : support (amountModel R κ μ) (translate .ge n k).enrich s) :
    (∃ i ∈ s, μ i.world (κ i.world k) = n) ∧ ∃ i ∈ s, n < μ i.world (κ i.world k) :=
  exists_mem_of_support_enrich_disj h

/-- At a non-empty state where the amount is known to be `m`, the enriched translation of a modified
numeral is supported exactly when the modifier is not a superlative and `m` satisfies it ((2)). -/
theorem support_enrich_translate_iff_of_settled (hne : s.Nonempty)
    (hs : ∀ i ∈ s, μ i.world (κ i.world k) = m) :
    support (amountModel R κ μ) (translate c n k).enrich s ↔
      (c ≠ .ge ∧ c ≠ .le) ∧ m ∈ c.interval n := by
  have hsettled {A : Set ℕ} : (∀ i ∈ s, μ i.world (κ i.world k) ∈ A) ↔ m ∈ A :=
    ⟨fun h ↦ have ⟨i, hi⟩ := hne; hs i hi ▸ h i hi, fun h i hi ↦ hs i hi ▸ h⟩
  cases c with
  | ge | le =>
    refine iff_of_false (fun h ↦ ?_) (by simp)
    obtain ⟨⟨i, hi, h₁⟩, j, hj, h₂⟩ := exists_mem_of_support_enrich_disj h
    rw [hs i hi] at h₁
    rw [hs j hj] at h₂
    simp_all
  | _ =>
    dsimp only [translate]
    rw [support_enrich_predc_amountModel, hsettled, and_iff_left hne]
    exact ⟨fun h ↦ ⟨⟨by decide, by decide⟩, h⟩, And.right⟩

/-- The modified numerals of (3) and (4), each with its comparison and number. -/
def knownAmountRows : List (Datum × Comparison × ℕ) :=
  [(Examples.ex_3a, .ge, 3), (Examples.ex_3b, .gt, 2), (Examples.ex_4a, .le, 10),
    (Examples.ex_4b, .lt, 11)]

-- (3), (4)
theorem knownAmountRows_judgment (hne : s.Nonempty) (hs : ∀ i ∈ s, μ i.world (κ i.world k) = m) :
    ∀ r ∈ knownAmountRows, m ∈ r.2.1.interval r.2.2 →
      (support (amountModel R κ μ) (translate r.2.1 r.2.2 k).enrich s ↔
        r.1.judgment = .acceptable) := by
  simp only [knownAmountRows, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl) hm <;> simp at hm <;>
    simp [support_enrich_translate_iff_of_settled hne hs, hm, Examples.ex_3a, Examples.ex_3b,
      Examples.ex_4a, Examples.ex_4b]

example : support (amountModel (fun _ ↦ ∅) (fun _ _ ↦ ()) fun w _ ↦ w) (translate .ge 3 ()).enrich
    (State.modalLift {3, 4} fun (_ : Var) ↦ (none : Option Unit)) :=
  ⟨⟨State.modalLift {3} fun _ ↦ none, ⟨by simp, (Finset.singleton_nonempty _).image _⟩,
    State.modalLift {4} fun _ ↦ none, ⟨by simp, (Finset.singleton_nonempty _).image _⟩, by decide⟩,
    (Finset.insert_nonempty _ _).image _⟩

/-! ### Negation -/

private theorem support_enrich_neg_disj_predc :
    support (amountModel R κ μ) (Formula.neg (.disj (.predc A k) (.predc B k))).enrich s ↔
      support (amountModel R κ μ) (Formula.predc (A ∪ B)ᶜ k).enrich s := by
  refine and_congr_left fun _ ↦ ?_
  change antiSupport _ (.conj (.disj (.conj _ .ne) (.conj _ .ne)) .ne) s ↔ _
  rw [antiSupport_conj_ne]
  change antiSupport _ (.conj _ .ne) s ∧ antiSupport _ (.conj _ .ne) s ↔ _
  simp only [antiSupport_conj_ne, antiSupport_predc_amountModel, support_predc_amountModel,
    ← forall₂_and, Set.mem_compl_iff, Set.mem_union, not_or]

/-- Enriched, *not at least n* is equivalent to *fewer than n*, which blocks it ((41), (42)). -/
theorem support_enrich_neg_translate_ge :
    support (amountModel R κ μ) (Formula.neg (translate .ge n k)).enrich s ↔
      support (amountModel R κ μ) (translate .lt n k).enrich s :=
  support_enrich_neg_disj_predc.trans <| by
    rw [Comparison.interval_eq, Comparison.interval_gt, Set.singleton_union, Set.Ioi_insert,
      Set.compl_Ici]
    rfl

-- (41), (42)
theorem support_enrich_neg_translate_le :
    support (amountModel R κ μ) (Formula.neg (translate .le n k)).enrich s ↔
      support (amountModel R κ μ) (translate .gt n k).enrich s :=
  support_enrich_neg_disj_predc.trans <| by
    rw [Comparison.interval_eq, Comparison.interval_lt, Set.singleton_union, Set.Iio_insert,
      Set.compl_Iic]
    rfl

/-! ### Obviation

The model of Fig. 14 has one index, at the world `w_{PaQb}` with the empty assignment, and that
world alone sees itself. Its universal extension is the state of Fig. 15. -/

/-- `Entity` is the Fig. 14 domain of two objects, each its own individual constant. -/
inductive Entity
  | a
  | b
  deriving DecidableEq, Repr, Fintype

/-- `three` and `more`, said of `x`, are the disjuncts of *at least three*. -/
def three : Formula Var Entity (Set ℕ) := .pred (Comparison.eq.interval 3) .x

@[inherit_doc three]
def more : Formula Var Entity (Set ℕ) := .pred (Comparison.gt.interval 3) .x

/-- `wPaQb` is the world `w_{PaQb}`, where `a` has three (the figure's `P`) and `b` has four
(`Q`). -/
def wPaQb : Entity → ℕ
  | .a => 3
  | .b => 4

def fig14Model : Model (Entity → ℕ) Entity Entity (Set ℕ) :=
  amountModel (fun w ↦ if w = wPaQb then {wPaQb} else ∅) (fun _ ↦ id) id

def fig14Index : Index (Entity → ℕ) Var Entity := (wPaQb, fun _ ↦ none)

def fig14State : Finset (Index (Entity → ℕ) Var Entity) := {fig14Index}

def fig15State : Finset (Index (Entity → ℕ) Var Entity) := State.extendUniversal fig14State .x

-- Fig. 14
theorem fig14_stateBased : Team.IsStateBased fig14Model.access (State.worldProj fig14State) := by
  decide

-- Fig. 15
theorem fig15_stateBased : Team.IsStateBased fig14Model.access (State.worldProj fig15State) := by
  decide

-- Fig. 15
theorem support_enrich_fig15 : support fig14Model (Formula.disj three more).enrich fig15State := by
  refine ⟨⟨{fig14Index.update .x .a}, ⟨?_, Finset.singleton_nonempty _⟩,
    {fig14Index.update .x .b}, ⟨?_, Finset.singleton_nonempty _⟩, by decide⟩,
    ⟨_, (by decide : fig14Index.update .x .a ∈ fig15State)⟩⟩ <;>
  · intro j hj
    obtain rfl := Finset.mem_singleton.mp hj
    exact ⟨_, rfl, by simp [fig14Model, amountModel, fig14Index, Index.world, wPaQb]⟩

-- Fig. 16
theorem not_support_poss_three_fig15 : ¬ support fig14Model (.poss three) fig15State := by
  intro h
  obtain ⟨X, hX, hne, hsupp⟩ :=
    support_poss_iff.mp h (fig14Index.update .x .b) (by decide)
  obtain rfl : X = {wPaQb} := hne.subset_singleton_iff.mp <| by
    simpa [fig14Model, amountModel, Model.ofMonadic, fig14Index] using hX
  obtain ⟨d, hd, hP⟩ := hsupp _ (State.mem_modalLift.mpr ⟨Finset.mem_singleton_self _, rfl⟩)
  obtain rfl := Option.some.inj hd
  simp [fig14Model, amountModel, fig14Index, Index.world, wPaQb] at hP

-- Fact 3, Fig. 15
theorem not_ignorance_fig15 :
    Team.IsStateBased fig14Model.access (State.worldProj fig15State) ∧
      support fig14Model (Formula.disj three more).enrich fig15State ∧
        ¬ support fig14Model (.poss three) fig15State :=
  ⟨fig15_stateBased, support_enrich_fig15, not_support_poss_three_fig15⟩

/-- Under a universal quantifier the enriched *at least three* conveys no ignorance: a speaker who
knows how many each individual has can assert it, though no individual has both amounts possible
((20), (57), Fact 4). -/
theorem obviation :
    ∃ (M : Model (Entity → ℕ) Entity Entity (Set ℕ)) (s : Finset (Index (Entity → ℕ) Var Entity)),
      Team.IsStateBased M.access (State.worldProj s) ∧
        support M (Formula.univ .x (.disj three more)).enrich s ∧
        ¬ support M (.univ .x (.conj (.poss three) (.poss more))) s :=
  ⟨fig14Model, fig14State, fig14_stateBased, ⟨support_enrich_fig15, Finset.singleton_nonempty _⟩,
    fun h ↦ not_support_poss_three_fig15 h.1⟩

end AloniVanOrmondt2023
