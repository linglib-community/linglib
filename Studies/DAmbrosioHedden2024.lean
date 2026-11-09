module

public import Studies.Kamp1975
public import Studies.Sassoon2013
public import Linglib.Logic.Trivalent.Supervaluation
public import Linglib.Semantics.Aggregation.Arrow
public import Linglib.Semantics.Aggregation.Rules
public import Mathlib.Tactic.DeriveFintype

/-!
# D'Ambrosio and Hedden (2024): Multidimensional Adjectives

A context admits a set of aggregation rules, each sending a profile of dimensional values to an
ordering of objects, and a sentence is determinately true, determinately false or neither as every,
no or only some admissible rule makes it true. Where two admissible rules sort a pair oppositely
against the standard, [the delineation comparative leaves the pair incomparable while this one is
determinately complete and indeterminate](##Context.incompRel_delineation); over the positive
weightings of the dimensions, [a comparison is indeterminate exactly where the Pareto rule is
incomplete](##supervaluationOn_utilitarian_eq_undefined_iff). Arrow's conditions [admit no
rule](##Context.incoherent_of_arrovian), while without weak-ordering outputs [majority rule and the
Pareto rule both qualify](##Context.vague_of_ordinal) and with cardinal unit comparability [every
positive weighting does](##Context.vague_of_arrovian_cardinalUnit), so the comparative is vague.

## Implementation notes

* The verdict on a sentence is `Trivalent.supervaluationOn` over the admissible rules; the paper
  takes this vocabulary without identifying truth with determinate truth.
* The delineation comparative takes the admissible rules, with the standard fixed, as its
  precisifications, so it is `Kamp1975.kampPreorder`.
* `Acyclic` is the paper's three-term condition, not Sen's acyclicity, which forbids strict cycles
  of every length; the Condorcet cycle violates both.

## Errata

* The paper offers utilitarian aggregation with non-negative weights as meeting Arrow's conditions
  under cardinal unit comparability, but zero weights fail weak Pareto
  (`Aggregation.not_weakPareto_utilitarian_zero`) and one positive weight makes a dictator
  (`Aggregation.isDictator_utilitarian_single`).
* The quantificational comparative cited to Sassoon's 2013 book is on p. 368 of
  [sassoon-2013], the paper's Sassoon 2013b.

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

open Aggregation Finset Trivalent

variable {ι O K : Type*}

/-! ### Contexts -/

/-- A context supplies a multidimensional adjective with its admissible aggregation rules and a
standard object. Relative to an admissible rule `a` and a profile `v`, *x is at least as F as y* is
`a v x y`, *x is F-er than y* is `AsymmRel (a v) x y`, *x and y are equally F* is
`AntisymmRel (a v) x y`, and *x is F* is `a v x c.standard`. A sentence true relative to `a`
exactly when `P a` has the verdict `supervaluationOn c.adm P`. -/
structure Context (ι O K : Type*) where
  /-- The aggregation rules the context does not rule out. -/
  adm : Set (Rule ι O K)
  /-- The object that sets the standard for the positive form. -/
  standard : O

namespace Context

variable (c : Context ι O K)

/-- An adjective is incoherent when no rule is admissible. -/
def Incoherent : Prop := c.adm = ∅

/-- The comparative is sharp when exactly one rule is admissible. -/
def Sharp : Prop := ∃ a, c.adm = {a}

/-- The comparative is vague when more than one rule is admissible. -/
def Vague : Prop := c.adm.Nontrivial

variable {c}

-- §4, p. 263
theorem incoherent_or_sharp_or_vague : c.Incoherent ∨ c.Sharp ∨ c.Vague :=
  (Set.subsingleton_or_nontrivial c.adm).elim
    (fun h ↦ h.eq_empty_or_singleton.imp id Or.inl) (fun h ↦ Or.inr (Or.inr h))

/-! ### The delineation comparative -/

/-- The delineation comparative of §2.1, with the admissible rules as precisifications and the
standard fixed, makes `x` at least as F as `y` iff every admissible rule that makes `y` F makes
`x` F. -/
abbrev delineation (c : Context ι O K) (v : Profile ι O K) : Preorder O :=
  Kamp1975.kampPreorder (fun (a : Rule ι O K) x ↦ a v x c.standard) c.adm

/-- Where two admissible rules with weak-ordering outputs sort `x` and `y` oppositely against the
standard, the delineation comparative leaves them incomparable, while it is determinately true that
one is at least as F as the other and indeterminate which (p. 256). -/
theorem incompRel_delineation {v : Profile ι O K} {x y : O} {a b : Rule ι O K}
    (hW : ∀ a ∈ c.adm, WeakOrderValued a) (ha : a ∈ c.adm) (hb : b ∈ c.adm)
    (hax : a v x c.standard) (hay : ¬ a v y c.standard) (hby : b v y c.standard)
    (hbx : ¬ b v x c.standard) :
    IncompRel (c.delineation v).le x y ∧
      supervaluationOn c.adm (fun a ↦ a v x y ∨ a v y x) = .true ∧
      supervaluationOn c.adm (fun a ↦ a v x y) = .undefined := by
  refine ⟨⟨fun h ↦ hbx (h b hb hby), fun h ↦ hay (h a ha hax)⟩,
    supervaluationOn_eq_true_iff.2 fun a ha ↦ ((hW a ha).complete v).total x y,
    supervaluationOn_eq_undefined_iff.2 ⟨⟨a, ha, ?_⟩, b, hb, fun h ↦ ?_⟩⟩
  · have := (hW a ha).transitive v
    exact (((hW a ha).complete v).total x y).resolve_right fun h ↦ hay (_root_.trans h hax)
  · have := (hW b hb).transitive v
    exact hbx (_root_.trans h hby)

end Context

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

variable {c : Context Health Patient K} {w w' : Health → K} {mS mB cB t : K}

-- p. 257: the first Suzy is not at least as healthy as Bill
theorem supervaluationOn_health_eq_false [Preorder K] (hne : c.adm.Nonempty)
    (hP : ∀ a ∈ c.adm, WeakPareto a) (hm : mS < mB) (ht : t < cB) :
    supervaluationOn c.adm (fun a ↦ a (health mS mB cB t) .suzy .bill) = .false :=
  supervaluationOn_eq_false_iff.2 ⟨hne, fun a ha ↦
    (hP a ha _ .bill .suzy fun i ↦ by cases i <;> [exact hm; exact ht]).2⟩

section Sorites

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem health_utilitarian_iff (hw : 0 < w .cardiovascular) :
    utilitarian w (health mS mB cB t) .suzy .bill ↔
      cB + w .musculoskeletal / w .cardiovascular * (mB - mS) ≤ t := by
  rw [← mul_le_mul_iff_of_pos_right hw, add_mul, div_mul_eq_mul_div, div_mul_cancel₀ _ hw.ne']
  simp only [utilitarian_apply, dotProduct, sum_health, health]
  constructor <;> intro h <;> linarith

-- p. 257: the Suzys between two weightings' cut-offs are borderline
theorem supervaluationOn_health_eq_undefined (hw : utilitarian w ∈ c.adm)
    (hw' : utilitarian w' ∈ c.adm) (hc : 0 < w .cardiovascular) (hc' : 0 < w' .cardiovascular)
    (ht : cB + w .musculoskeletal / w .cardiovascular * (mB - mS) ≤ t)
    (ht' : t < cB + w' .musculoskeletal / w' .cardiovascular * (mB - mS)) :
    supervaluationOn c.adm (fun a ↦ a (health mS mB cB t) .suzy .bill) = .undefined :=
  supervaluationOn_eq_undefined_iff.2 ⟨⟨_, hw, (health_utilitarian_iff hc).2 ht⟩, _, hw',
    fun h ↦ ((health_utilitarian_iff hc').1 h).not_gt ht'⟩

-- p. 261, (a): vague and determinately complete and transitive
theorem vague_and_weakOrderValued (hadm : c.adm = {utilitarian w, utilitarian w'})
    (hc : 0 < w .cardiovascular) (hc' : 0 < w' .cardiovascular)
    (h : cB + w .musculoskeletal / w .cardiovascular * (mB - mS) <
      cB + w' .musculoskeletal / w' .cardiovascular * (mB - mS)) :
    c.Vague ∧ supervaluationOn c.adm WeakOrderValued = .true := by
  refine ⟨nontrivial_of_supervaluationOn_eq_undefined
    (supervaluationOn_health_eq_undefined (by simp [hadm]) (by simp [hadm]) hc hc' le_rfl h),
    supervaluationOn_eq_true_iff.2 fun a ha ↦ ?_⟩
  rw [hadm] at ha
  rcases ha with rfl | rfl <;> exact utilitarian_weakOrderValued _

end Sorites

-- p. 261: it can be indeterminate whether the comparative is complete
theorem supervaluationOn_complete_eq_undefined [Fintype ι] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Nontrivial ι] [Nontrivial O] {c : Context ι O K} {w : ι → K}
    (hu : utilitarian w ∈ c.adm) (hp : paretoRule ∈ c.adm) :
    supervaluationOn c.adm Complete = .undefined :=
  supervaluationOn_eq_undefined_iff.2
    ⟨⟨_, hu, (utilitarian_weakOrderValued w).complete⟩, _, hp, not_complete_paretoRule⟩

/-! ### Arrow's conditions and incoherence -/

/-- An adjective whose admissible rules all meet Arrow's conditions, with three or more objects in
its domain, is incoherent (p. 264). -/
theorem Context.incoherent_of_arrovian [Fintype ι] [Fintype O] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (h₃ : 3 ≤ Fintype.card O) (c : Context ι O K)
    (h : ∀ a ∈ c.adm, Arrovian ordinal a) : c.Incoherent :=
  Set.eq_empty_of_forall_notMem fun a ha ↦ arrow h₃ a (h a ha)

/-! ### Giving up weak-ordering outputs -/

/-- Without weak-ordering outputs, Arrow's other conditions admit majority rule, complete but not
transitive, and the Pareto rule, transitive but not complete, so an adjective admitting every rule
that meets them is vague (p. 265). -/
theorem Context.vague_of_ordinal [Fintype ι] [LinearOrder K] [Nontrivial ι] [Nontrivial O]
    [Nontrivial K] (c : Context ι O K)
    (h : ∀ a, Invariant ordinal a → WeakPareto a → Independent a → NonDictatorial a → a ∈ c.adm) :
    c.Vague :=
  Set.nontrivial_of_mem_mem_ne
    (h _ majority_ordinalInvariant majority_weakPareto majority_independent
      majority_nonDictatorial)
    (h _ paretoRule_ordinalInvariant paretoRule_strongPareto.weakPareto paretoRule_independent
      paretoRule_nonDictatorial)
    fun e ↦ not_complete_paretoRule (e ▸ majority_complete)

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

theorem supervaluationOn_utilitarian_eq_true_iff :
    supervaluationOn (utilitarian '' {w | ∀ i, 0 < w i}) (fun a ↦ a v x y) = .true ↔
      paretoRule v x y := by
  rw [supervaluationOn_image, supervaluationOn_eq_true_iff]
  exact paretoRule_iff_forall_utilitarian.symm

theorem supervaluationOn_utilitarian_eq_false_iff :
    supervaluationOn (utilitarian '' {w | ∀ i, 0 < w i}) (fun a ↦ a v x y) = .false ↔
      AsymmRel (paretoRule v) y x := by
  rw [supervaluationOn_image, supervaluationOn_eq_false_iff,
    asymmRel_paretoRule_iff_forall_utilitarian]
  simp only [AsymmRel, Function.comp_apply, Set.mem_ofPred_eq, utilitarian_apply, not_le]
  exact ⟨fun h c hc ↦ ⟨(h.2 c hc).le, h.2 c hc⟩,
    fun h ↦ ⟨⟨1, fun _ ↦ one_pos⟩, fun c hc ↦ (h c hc).2⟩⟩

/-- Over the positive weightings of the dimensions, it is indeterminate whether `x` is at least as
F as `y` exactly when the Pareto rule leaves them incomparable (p. 256, p. 268). -/
theorem supervaluationOn_utilitarian_eq_undefined_iff :
    supervaluationOn (utilitarian '' {w | ∀ i, 0 < w i}) (fun a ↦ a v x y) = .undefined ↔
      IncompRel (paretoRule v) x y := by
  have key (t : Trivalent) : t = .undefined ↔ t ≠ .true ∧ t ≠ .false := by cases t <;> simp
  rw [key, Ne, Ne, supervaluationOn_utilitarian_eq_true_iff,
    supervaluationOn_utilitarian_eq_false_iff]
  exact and_congr_right fun h ↦ not_congr (and_iff_left h)

/-- With cardinal unit comparability in place of ordinal non-comparability, Arrow's conditions
admit every positively weighted utilitarian rule, so an adjective admitting every rule that meets
them is vague (p. 268). -/
theorem Context.vague_of_arrovian_cardinalUnit [Nontrivial ι] [Nontrivial O] (c : Context ι O K)
    (h : ∀ a, Arrovian cardinalUnit a → a ∈ c.adm) : c.Vague := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne O
  obtain ⟨v, -, hv⟩ := exists_incompRel_paretoRule (K := K) hxy (Classical.arbitrary ι)
  refine (nontrivial_of_supervaluationOn_eq_undefined
    (supervaluationOn_utilitarian_eq_undefined_iff.2 hv)).mono ?_
  rintro _ ⟨w, hw, rfl⟩
  exact h _ (utilitarian_arrovian_cardinalUnit w hw)

end Weighted

/-! ### Sassoon's comparatives -/

section Sassoon

variable [Fintype ι] [LinearOrder K] (θ : ι → K)

/-- The comparative the paper attributes to Sassoon for each binding type is universal
quantification over the dimensions for conjunctive adjectives (*healthy*), existential for
disjunctive ones (*sick*), and for mixed ones (*intelligent*) counting the dimensions on which
the thresholds `θ` are met. -/
def sassoon : Sassoon2013.DimensionBindingType → Rule ι O K
  | .conjunctive => fun v x y ↦ ∀ i, v y i ≤ v x i
  | .disjunctive => fun v x y ↦ ∃ i, v y i ≤ v x i
  | .mixed => fun v x y ↦ #{i | θ i ≤ v y i} ≤ #{i | θ i ≤ v x i}

-- p. 270: the conjunctive comparative is the Pareto rule, so incomplete
theorem not_complete_sassoon_conjunctive [Nontrivial ι] [Nontrivial O] [Nontrivial K] :
    ¬ Complete (sassoon θ .conjunctive : Rule ι O K) :=
  not_complete_paretoRule

theorem not_strongPareto_sassoon_disjunctive [Nontrivial ι] [Nontrivial O] [Nontrivial K] :
    ¬ StrongPareto (sassoon θ .disjunctive : Rule ι O K) := by
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
  have hxy' : sassoon θ .disjunctive v x y := ⟨i, by simp [v, hxy]⟩
  exact ((h v y x).2 (Pi.lt_def.2 ⟨hle, hlt⟩)).2 hxy'

theorem not_weakPareto_sassoon_mixed [Nonempty ι] [Nontrivial O] [NoMaxOrder K] :
    ¬ WeakPareto (sassoon θ .mixed : Rule ι O K) := by
  intro h
  obtain ⟨x, y, hxy⟩ := exists_pair_ne O
  obtain ⟨k, hk⟩ := exists_gt (univ.sup' univ_nonempty θ)
  obtain ⟨k', hk'⟩ := exists_gt k
  classical
  let v : Profile ι O K := fun z _ ↦ if z = x then k' else k
  have hθ : ∀ z i, θ i ≤ v z i := fun z i ↦ by
    have := (le_sup' θ (mem_univ i)).trans hk.le
    simp only [v]
    split_ifs <;> [exact this.trans hk'.le; exact this]
  have := h v x y fun i ↦ by simp [v, hxy.symm, hk']
  simp only [AsymmRel, sassoon, filter_true_of_mem (fun i _ ↦ hθ _ i), le_refl, not_true,
    and_false] at this

end Sassoon

end DAmbrosioHedden2024
