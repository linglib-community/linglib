module

public import Studies.Kamp1975
public import Studies.Sassoon2013
public import Linglib.Logic.Trivalent.Supervaluation
public import Linglib.Semantics.Aggregation.Arrow
public import Linglib.Semantics.Aggregation.Rules
public import Linglib.Semantics.Quantification.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# D'Ambrosio and Hedden (2024): Multidimensional Adjectives

A context admits a set of aggregation rules, each sending a profile of dimensional values to an
ordering of objects, and a sentence is determinately true, determinately false or neither as all,
none or only some of them make it true. Where two admissible rules sort a pair oppositely against
the standard, [the delineation comparative leaves the pair incomparable while this one is
determinately complete and indeterminate](##incompRel_delineation); over the positive weightings,
[a comparison is indeterminate exactly where the Pareto rule is
incomplete](##supervaluationOn_utilitarian_eq_undefined_iff). Arrow's conditions admit no rule
(`Aggregation.arrow`), while without weak-ordering outputs [majority rule and the Pareto rule both
qualify](##nontrivial_ordinal_weakPareto_independent_nonDictatorial) and with cardinal unit
comparability [every positive weighting does](##nontrivial_arrovian_cardinalUnit), so the
comparative is vague.

## Implementation notes

* The verdict on a sentence is `Trivalent.supervaluationOn` over the admissible rules; the paper
  takes this vocabulary without identifying truth with determinate truth. Rules form a complete
  lattice, in which *determinately at least as F* is the infimum of the admissible rules.
* The delineation comparative takes the admissible rules, with the standard fixed, as its
  precisifications, so it is `Kamp1975.kampPreorder`.
* Sassoon's comparatives bind the dimensions by the determiners of her binding types
  (`Sassoon2013.DimensionBindingType.dets`). The paper restates her comparative, which she gives
  for the strict *-er* (`Sassoon2013.comparative`), for *at least as*, and reads mixed adjectives
  as counting dimensions, after Sassoon 2015, where her 2013 article lets context choose *every*
  or *some*.
* `Acyclic` is the paper's three-term condition, not Sen's acyclicity, which forbids strict cycles
  of every length; the Condorcet cycle violates both.

## TODO

* The sharp branch, May's and Weymark's characterizations of majority rule and the Pareto rule.
* The Cobb–Douglas route to vagueness, which needs weak Pareto on non-negative profiles only.

## References

* [J. D'Ambrosio and B. Hedden, *Multidimensional adjectives* (2024)][dambrosio-hedden-2024]
* [K. J. Arrow, *A difficulty in the concept of social welfare* (1951)][arrow-1950]
* [H. Kamp, *Two theories about adjectives* (1975)][kamp-1975]
* [G. W. Sassoon, *A typology of multidimensional adjectives* (2013)][sassoon-2013]
* [A. Sen, *Collective choice and social welfare* (1970)][sen-1970]
* [K. O. May, *A set of independent necessary and sufficient conditions for simple majority
  decision* (1952)][may-1952]
* [J. A. Weymark, *Arrow's theorem with social quasi-orderings* (1984)][weymark-1984]
-/

@[expose] public section

namespace DAmbrosioHedden2024

open Aggregation Finset Quantifier Sassoon2013 Trivalent

variable {ι O K : Type*}

/-! ### Determinacy -/

section Determinacy

variable {A : Set (Rule ι O K)} {v : Profile ι O K} {x y : O}

-- p. 260: determinately at least as F is the infimum of the admissible rules
theorem supervaluationOn_eq_true_iff_sInf :
    supervaluationOn A (· v x y) = .true ↔ sInf A v x y := by
  simp [supervaluationOn_eq_true_iff, sInf_apply, iInf_apply]

theorem supervaluationOn_eq_false_iff_sSup :
    supervaluationOn A (· v x y) = .false ↔ A.Nonempty ∧ ¬ sSup A v x y := by
  simp [supervaluationOn_eq_false_iff, sSup_apply, iSup_apply]

end Determinacy

/-! ### The delineation comparative -/

/-- The delineation comparative of §2.1 takes the admissible rules `A` as precisifications with the
standard `d` fixed, so that `x` is at least as F as `y` iff every admissible rule that makes `y` F,
ranking it at least as high as `d`, makes `x` F. -/
abbrev delineation (A : Set (Rule ι O K)) (d : O) (v : Profile ι O K) : Preorder O :=
  Kamp1975.kampPreorder (fun (a : Rule ι O K) x ↦ a v x d) A

/-- Where two admissible rules with weak-ordering outputs sort `x` and `y` oppositely against the
standard, the delineation comparative leaves them incomparable, while it is determinately true that
one is at least as F as the other and indeterminate which (p. 256). -/
theorem incompRel_delineation {A : Set (Rule ι O K)} {d : O} {v : Profile ι O K} {x y : O}
    {a b : Rule ι O K} (hW : ∀ a ∈ A, WeakOrderValued a) (ha : a ∈ A) (hb : b ∈ A)
    (hax : a v x d) (hay : ¬ a v y d) (hby : b v y d) (hbx : ¬ b v x d) :
    IncompRel (delineation A d v).le x y ∧
      supervaluationOn A (fun a ↦ a v x y ∨ a v y x) = .true ∧
      supervaluationOn A (· v x y) = .undefined := by
  refine ⟨⟨fun h ↦ hbx (h b hb hby), fun h ↦ hay (h a ha hax)⟩,
    supervaluationOn_eq_true_iff.2 fun a ha ↦ ((hW a ha).complete v).total x y,
    supervaluationOn_eq_undefined_iff.2 ⟨⟨a, ha, ?_⟩, b, hb, fun h ↦ ?_⟩⟩
  · have := (hW a ha).transitive v
    exact (((hW a ha).complete v).total x y).resolve_right fun h ↦ hay (_root_.trans h hax)
  · have := (hW b hb).transitive v
    exact hbx (_root_.trans h hby)

/-! ### The sorites on Suzy's health -/

/-- The dimensions of *healthy* in the sorites of §2.1. -/
inductive Health
  | musculoskeletal
  | cardiovascular
  deriving DecidableEq, Fintype

/-- Bill and a variant of Suzy. -/
inductive Patient
  | suzy
  | bill
  deriving DecidableEq

/-- In the sorites profile Suzy's musculoskeletal health `mS` sits below Bill's `mB`, and her
cardiovascular health `t` varies against Bill's `cB`. -/
def health (mS mB cB t : K) : Profile Health Patient K
  | .suzy, .musculoskeletal => mS
  | .suzy, .cardiovascular => t
  | .bill, .musculoskeletal => mB
  | .bill, .cardiovascular => cB

private theorem sum_health [AddCommMonoid K] (f : Health → K) :
    ∑ i, f i = f .musculoskeletal + f .cardiovascular := by
  rw [show (univ : Finset Health) = {.musculoskeletal, .cardiovascular} from by decide,
    sum_pair (by decide)]

variable {A : Set (Rule Health Patient K)} {w w' : Health → K} {mS mB cB t : K}

-- p. 257: the first Suzy is not at least as healthy as Bill
theorem supervaluationOn_health_eq_false [Preorder K] (hne : A.Nonempty)
    (hP : ∀ a ∈ A, WeakPareto a) (hm : mS < mB) (ht : t < cB) :
    supervaluationOn A (· (health mS mB cB t) .suzy .bill) = .false :=
  supervaluationOn_eq_false_iff.2 ⟨hne, fun a ha ↦
    (hP a ha _ .bill .suzy fun i ↦ by cases i <;> [exact hm; exact ht]).2⟩

section Sorites

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The cardiovascular health at which Suzy draws level with Bill under the weighting `w`. -/
def cutoff (w : Health → K) (mS mB cB : K) : K :=
  cB + w .musculoskeletal / w .cardiovascular * (mB - mS)

theorem health_utilitarian_iff (hw : 0 < w .cardiovascular) :
    utilitarian w (health mS mB cB t) .suzy .bill ↔ cutoff w mS mB cB ≤ t := by
  rw [cutoff, ← mul_le_mul_iff_of_pos_right hw, add_mul, div_mul_eq_mul_div,
    div_mul_cancel₀ _ hw.ne']
  simp only [utilitarian_apply, dotProduct, sum_health, health]
  constructor <;> intro h <;> linarith

-- p. 257: the Suzys between two weightings' cut-offs are borderline
theorem supervaluationOn_health_eq_undefined (hw : utilitarian w ∈ A)
    (hw' : utilitarian w' ∈ A) (hc : 0 < w .cardiovascular) (hc' : 0 < w' .cardiovascular)
    (ht : cutoff w mS mB cB ≤ t) (ht' : t < cutoff w' mS mB cB) :
    supervaluationOn A (· (health mS mB cB t) .suzy .bill) = .undefined :=
  supervaluationOn_eq_undefined_iff.2 ⟨⟨_, hw, (health_utilitarian_iff hc).2 ht⟩, _, hw',
    fun h ↦ ((health_utilitarian_iff hc').1 h).not_gt ht'⟩

end Sorites

-- p. 261: it can be indeterminate whether the comparative is complete
theorem supervaluationOn_completeValued_eq_undefined [Fintype ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Nontrivial ι] [Nontrivial O] {A : Set (Rule ι O K)} {w : ι → K}
    (hu : utilitarian w ∈ A) (hp : paretoRule ∈ A) :
    supervaluationOn A CompleteValued = .undefined :=
  supervaluationOn_eq_undefined_iff.2
    ⟨⟨_, hu, (utilitarian_weakOrderValued w).complete⟩, _, hp, not_completeValued_paretoRule⟩

/-! ### Giving up weak-ordering outputs -/

/-- Without weak-ordering outputs, Arrow's other conditions admit majority rule, complete but not
transitive, and the Pareto rule, transitive but not complete, so an adjective they govern is vague
(p. 265). -/
theorem nontrivial_ordinal_weakPareto_independent_nonDictatorial [Fintype ι] [LinearOrder K]
    [Nontrivial ι] [Nontrivial O] [Nontrivial K] :
    Set.Nontrivial
      {a : Rule ι O K | Invariant ordinal a ∧ WeakPareto a ∧ Independent a ∧ NonDictatorial a} :=
  Set.nontrivial_of_mem_mem_ne
    ⟨majority_ordinalInvariant, majority_weakPareto, majority_independent, majority_nonDictatorial⟩
    ⟨paretoRule_ordinalInvariant, paretoRule_strongPareto.weakPareto, paretoRule_independent,
      paretoRule_nonDictatorial⟩
    fun e ↦ not_completeValued_paretoRule (e ▸ majority_completeValued)

/-- A relation is acyclic, as the paper states it, when two strict steps yield a weak step. -/
def Acyclic (r : O → O → Prop) : Prop := ∀ x y z, AsymmRel r x y → AsymmRel r y z → r x z

/-- Condorcet's profile has three dimensions ranking three objects cyclically. -/
def condorcet : Profile (Fin 3) (Fin 3) ℕ := ![![2, 0, 1], ![1, 2, 0], ![0, 1, 2]]

-- p. 266
theorem majority_condorcet :
    AsymmRel (majority condorcet) 0 1 ∧ AsymmRel (majority condorcet) 1 2 ∧
      AsymmRel (majority condorcet) 2 0 := by
  decide

theorem not_acyclic_majority_condorcet : ¬ Acyclic (majority condorcet) :=
  fun h ↦ majority_condorcet.2.2.2 (h 0 1 2 majority_condorcet.1 majority_condorcet.2.1)

/-! ### Weighting the dimensions -/

section Weighted

variable [Fintype ι] [Field K] [LinearOrder K] [IsStrictOrderedRing K] {v : Profile ι O K}
  {x y : O}

/-- Over the positive weightings of the dimensions, it is indeterminate whether `x` is at least as
F as `y` exactly when the Pareto rule leaves them incomparable (p. 256, p. 268). -/
theorem supervaluationOn_utilitarian_eq_undefined_iff :
    supervaluationOn (utilitarian '' {c | ∀ i, 0 < c i}) (· v x y) = .undefined ↔
      IncompRel (paretoRule v) x y := by
  rw [eq_undefined_iff, Ne, Ne, supervaluationOn_eq_true_iff_sInf,
    supervaluationOn_eq_false_iff_sSup, sInf_image, sSup_image]
  simp only [Set.mem_ofPred_eq]
  rw [← paretoRule_eq_iInf_utilitarian, ← paretoExtension_eq_iSup_utilitarian]
  simp only [Set.image_nonempty, show {c : ι → K | ∀ i, 0 < c i}.Nonempty from ⟨1, fun _ ↦ one_pos⟩,
    true_and, not_not, paretoExtension_apply, paretoRule_apply]
  exact and_congr_right fun h ↦ not_congr (lt_iff_le_not_ge.trans (and_iff_left h))

/-- With cardinal unit comparability in place of ordinal non-comparability, Arrow's conditions
admit every positively weighted utilitarian rule, so an adjective they govern is vague
(p. 268). -/
theorem nontrivial_arrovian_cardinalUnit [Nontrivial ι] [Nontrivial O] :
    {a : Rule ι O K | Arrovian cardinalUnit a}.Nontrivial := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne O
  obtain ⟨v, -, hv⟩ := exists_incompRel_paretoRule (K := K) hxy (Classical.arbitrary ι)
  refine (nontrivial_of_supervaluationOn_eq_undefined
    (supervaluationOn_utilitarian_eq_undefined_iff.2 hv)).mono ?_
  rintro _ ⟨w, hw, rfl⟩
  exact utilitarian_arrovian_cardinalUnit w hw

end Weighted

/-! ### Sassoon's comparatives -/

/-- Sassoon's comparative for an adjective that binds its dimensions by the quantifier `Q`: `x` is
at least as F as `y` when `Q` holds of the dimensions on which `x` ranks at least as high. -/
def sassoon [LE K] (Q : Quantifier ι) : Rule ι O K := ofRel fun p q ↦ Q {i | q i ≤ p i}

/-- Sassoon's comparative for an adjective that counts its dimensions ranks objects by the number
of dimensions on which they meet the thresholds `θ`. -/
def sassoonCounting [Fintype ι] [LE K] [DecidableLE K] (θ : ι → K) : Rule ι O K :=
  ofRel ((fun p ↦ #{i | θ i ≤ p i}) ⁻¹'o (· ≥ ·))

-- p. 270: binding every dimension makes the comparative the Pareto rule
theorem sassoon_every [Preorder K] : (sassoon (Det.every .univ) : Rule ι O K) = paretoRule :=
  funext fun _ ↦ funext₂ fun _ _ ↦ by
    simp [sassoon, paretoRule, Det.every, Pi.le_def, Set.eq_univ_iff_forall]

section Linear

variable [LinearOrder K]

theorem not_completeValued_sassoon_of_mem_conjunctive [Nontrivial ι] [Nontrivial O] [Nontrivial K]
    {d : Det ι} (hd : d ∈ DimensionBindingType.conjunctive.dets) :
    ¬ CompleteValued (sassoon (d .univ) : Rule ι O K) := by
  obtain rfl : d = Det.every := hd
  exact sassoon_every (ι := ι) (O := O) (K := K) ▸ not_completeValued_paretoRule

theorem not_strongPareto_sassoon_of_mem_disjunctive [Nontrivial ι] [Nontrivial O] [Nontrivial K]
    {d : Det ι} (hd : d ∈ DimensionBindingType.disjunctive.dets) :
    ¬ StrongPareto (sassoon (d .univ) : Rule ι O K) := by
  obtain rfl : d = Det.some := hd
  intro h
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  obtain ⟨x, y, hxy⟩ := exists_pair_ne O
  obtain ⟨k, k', hk⟩ := exists_pair_lt K
  classical
  let v : Profile ι O K := fun z l ↦ if z = y ∧ l ≠ i then k' else k
  have hle : v x ≤ v y := fun l ↦ by
    simp only [v, hxy, false_and, ite_false]
    split_ifs <;> simp [hk.le]
  have hlt : ∃ l, v x l < v y l := ⟨j, by simp [v, hxy, hij.symm, hk]⟩
  have hxy' : sassoon (Det.some .univ) v x y := ⟨i, trivial, by simp [v, hxy]⟩
  exact ((h v y x).2 (Pi.lt_def.2 ⟨hle, hlt⟩)).2 hxy'

theorem not_weakPareto_sassoonCounting [Fintype ι] [Nonempty ι] [Nontrivial O] [NoMaxOrder K]
    (θ : ι → K) : ¬ WeakPareto (sassoonCounting θ : Rule ι O K) := by
  rw [sassoonCounting, weakPareto_ofRel_iff]
  obtain ⟨k, hk⟩ := exists_gt (univ.sup' univ_nonempty θ)
  obtain ⟨k', hk'⟩ := exists_gt k
  have hθ (i : ι) : θ i ≤ k := (le_sup' θ (mem_univ i)).trans hk.le
  intro h
  have := (h (fun _ ↦ k') (fun _ ↦ k) fun _ ↦ hk').2
  simp [Order.Preimage, hθ, fun i ↦ (hθ i).trans hk'.le] at this

end Linear

end DAmbrosioHedden2024
