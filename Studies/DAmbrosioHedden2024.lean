module

public import Linglib.Semantics.Degree.Adjective
public import Linglib.Core.SocialChoice.Arrow
public import Linglib.Core.SocialChoice.Rules
public import Studies.Kamp1975
public import Mathlib.Tactic.DeriveFintype

/-!
# D'Ambrosio and Hedden, multidimensional adjectives (2024)

An adjective is multidimensional when whether it applies to an object, and whether it applies
to one object more than to another, depend on how the objects stand on several underlying
dimensions. The paper gives such adjectives a semantics with explicit aggregation: a context
supplies a profile of dimensional orderings, represented by value functions, a set of
admissible aggregation rules from profiles to an overall ordering, and a standard object. *x
is at least as F as y* holds relative to an admissible rule when it ranks x weakly above y, *x
is F* when it ranks x weakly above the standard, and a sentence is determinately true when it
is true relative to every admissible rule. The comparative is vague when more than one rule is
admissible, and its vagueness is independent of the completeness and transitivity of the
orderings the rules output, which the delineation approach conflates by turning disagreement
between precisifications into incomparability. Transposed to social choice, Arrow's theorem
makes an adjective governed by all of Arrow's conditions incoherent; giving up weak-ordering
outputs admits majority rule or the Pareto rule, and giving up ordinal non-comparability admits
utilitarian and Cobb–Douglas aggregation, whose free weights make the comparative vague.
Sassoon's quantificational comparatives are the Pareto rule for conjunctive adjectives, a rule
violating strong Pareto for disjunctive ones, and a rule violating weak Pareto for
dimension-counting ones.

The framework is stated over the social welfare functionals of `SocialChoice`, with the
dimensions as its individuals and the objects as its alternatives. This file states the sorites
on Suzy's cardiovascular health under utilitarian weightings and the three verdicts on Sassoon's
comparatives.

## Implementation notes

* The precisifications of the delineation comparative are the admissible rules with the
  standard fixed, so that comparative is `Kamp1975.kampPreorder`.
* Weighting the dimensions of *healthy*, as the paper's sorites does, is utilitarian
  aggregation; the cut-off on Suzy's cardiovascular health is where her weighted sum reaches
  Bill's.

## References

* [J. D'Ambrosio and B. Hedden, *Multidimensional adjectives* (2024)][dambrosio-hedden-2024]
* [K. J. Arrow, *A difficulty in the concept of social welfare* (1951)][arrow-1950]
* [H. Kamp, *Two theories about adjectives* (1975)][kamp-1975]
* [G. W. Sassoon, *A typology of multidimensional adjectives* (2013)][sassoon-2013]
-/

@[expose] public section

namespace DAmbrosioHedden2024

open SocialChoice Finset

variable {ι O K : Type*}

/-! ### Contexts and determinacy -/

/-- A context supplies a multidimensional adjective with its admissible aggregation rules and a
standard object. Relative to an admissible rule `a` and a profile `v`, *x is at least
as F as y* is `a v x y`, *x is F-er than y* is `AsymmRel (a v) x y`, *x and y are equally F* is
`AntisymmRel (a v) x y`, and *x is F* is `a v x c.standard`. -/
structure Context (ι O K : Type*) where
  /-- The aggregation rules the context does not rule out. -/
  adm : Set (Rule ι O K)
  /-- The object that sets the standard for the positive form. -/
  standard : O

namespace Context

variable (c : Context ι O K) (P : Rule ι O K → Prop)

/-- A statement is determinately true when it is true relative to every admissible rule. -/
def Determinately : Prop := ∀ a ∈ c.adm, P a

/-- A statement is determinately false when it is false relative to every admissible rule. -/
def DeterminatelyNot : Prop := ∀ a ∈ c.adm, ¬ P a

/-- Neither determinately true nor determinately false. -/
def Indeterminate : Prop := ¬ c.Determinately P ∧ ¬ c.DeterminatelyNot P

/-- An adjective is incoherent when no rule is admissible. -/
def Incoherent : Prop := c.adm = ∅

/-- The comparative is sharp when exactly one rule is admissible. -/
def Sharp : Prop := ∃ a, c.adm = {a}

/-- The comparative is vague when more than one rule is admissible. -/
def Vague : Prop := c.adm.Nontrivial

variable {c P}

/-- The three cases of §4. -/
theorem incoherent_or_sharp_or_vague : c.Incoherent ∨ c.Sharp ∨ c.Vague :=
  (Set.subsingleton_or_nontrivial c.adm).elim
    (fun h ↦ h.eq_empty_or_singleton.imp id Or.inl) (fun h ↦ Or.inr (Or.inr h))

theorem Sharp.determinately_or (h : c.Sharp) (P : Rule ι O K → Prop) :
    c.Determinately P ∨ c.DeterminatelyNot P := by
  obtain ⟨a, ha⟩ := h
  simp only [Determinately, DeterminatelyNot, ha, Set.mem_singleton_iff, forall_eq]
  exact em (P a)

theorem indeterminate_of_disagree {a b : Rule ι O K} (ha : a ∈ c.adm) (hb : b ∈ c.adm)
    (hPa : P a) (hPb : ¬ P b) : c.Indeterminate P :=
  ⟨fun h ↦ hPb (h b hb), fun h ↦ h a ha hPa⟩

theorem Indeterminate.vague (h : c.Indeterminate P) : c.Vague := by
  obtain ⟨h₁, h₂⟩ := h
  simp only [Determinately, DeterminatelyNot, not_forall, not_not, exists_prop] at h₁ h₂
  obtain ⟨a, ha, hPa⟩ := h₁
  obtain ⟨b, hb, hPb⟩ := h₂
  exact ⟨b, hb, a, ha, fun e ↦ hPa (e ▸ hPb)⟩

theorem determinately_or_of_complete (h : c.Determinately Complete) (v : Profile ι O K)
    (x y : O) : c.Determinately fun a ↦ a v x y ∨ a v y x :=
  fun a ha ↦ (h a ha v).total x y

/-! ### The delineation comparative -/

/-- The delineation comparative of §2, with the admissible rules as precisifications and the
standard fixed, makes `x` at least as F as `y` iff every admissible rule that makes `y` F makes
`x` F. -/
abbrev delineation (c : Context ι O K) (v : Profile ι O K) : Preorder O :=
  Kamp1975.kampPreorder (fun (a : Rule ι O K) x ↦ a v x c.standard) c.adm

theorem delineation_incomparable (c : Context ι O K) {v : Profile ι O K} {x y : O}
    {a b : Rule ι O K} (ha : a ∈ c.adm) (hb : b ∈ c.adm) (hax : a v x c.standard)
    (hay : ¬ a v y c.standard) (hby : b v y c.standard) (hbx : ¬ b v x c.standard) :
    ¬ (c.delineation v).le x y ∧ ¬ (c.delineation v).le y x :=
  ⟨fun h ↦ hbx (h b hb hby), fun h ↦ hay (h a ha hax)⟩

end Context

/-! ### The sorites on Suzy's health -/

/-- The dimensions of *healthy* in the sorites of §2. -/
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

section Sorites

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] {w w' : Health → K} {mS mB cB t t' : K}

theorem health_utilitarian_iff (hw : 0 < w .cardiovascular) :
    utilitarian w (health mS mB cB t) .suzy .bill ↔
      cB + w .musculoskeletal / w .cardiovascular * (mB - mS) ≤ t := by
  rw [← mul_le_mul_iff_of_pos_right hw, add_mul, div_mul_eq_mul_div, div_mul_cancel₀ _ hw.ne']
  simp only [utilitarian, dotProduct, sum_health, health]
  constructor <;> intro h <;> linarith

theorem health_mono (hw : 0 ≤ w .cardiovascular) (h : t ≤ t') :
    utilitarian w (health mS mB cB t) .suzy .bill →
      utilitarian w (health mS mB cB t') .suzy .bill := by
  simp only [utilitarian, dotProduct, sum_health, health]
  intro h'
  linarith [mul_le_mul_of_nonneg_left h hw]

theorem not_health_of_lt (hm : mS < mB) (ht : t < cB) (hw : ∀ i, 0 ≤ w i)
    (hpos : ∃ i, 0 < w i) : ¬ utilitarian w (health mS mB cB t) .suzy .bill :=
  (utilitarian_weakPareto w hw hpos (health mS mB cB t) Patient.bill Patient.suzy fun i ↦ by
    cases i <;> [exact hm; exact ht]).2

theorem health_indeterminate (c : Context Health Patient K) (hw : utilitarian w ∈ c.adm)
    (hw' : utilitarian w' ∈ c.adm) (hc : 0 < w .cardiovascular) (hc' : 0 < w' .cardiovascular)
    (ht : cB + w .musculoskeletal / w .cardiovascular * (mB - mS) ≤ t)
    (ht' : t < cB + w' .musculoskeletal / w' .cardiovascular * (mB - mS)) :
    c.Indeterminate fun a ↦ a (health mS mB cB t) .suzy .bill :=
  c.indeterminate_of_disagree hw hw' ((health_utilitarian_iff hc).2 ht)
    fun h ↦ ((health_utilitarian_iff hc').1 h).not_gt ht'

theorem vague_of_cutoff_lt (c : Context Health Patient K) (hw : utilitarian w ∈ c.adm)
    (hw' : utilitarian w' ∈ c.adm) (hc : 0 < w .cardiovascular) (hc' : 0 < w' .cardiovascular)
    (h : cB + w .musculoskeletal / w .cardiovascular * (mB - mS) <
      cB + w' .musculoskeletal / w' .cardiovascular * (mB - mS)) : c.Vague :=
  (health_indeterminate (t := cB + w .musculoskeletal / w .cardiovascular * (mB - mS)) c hw hw'
    hc hc' le_rfl h).vague

/-! ### Vagueness against structure -/

theorem vague_determinately_weakOrderValued (c : Context Health Patient K)
    (hadm : c.adm = {utilitarian w, utilitarian w'}) (hc : 0 < w .cardiovascular)
    (hc' : 0 < w' .cardiovascular)
    (h : cB + w .musculoskeletal / w .cardiovascular * (mB - mS) <
      cB + w' .musculoskeletal / w' .cardiovascular * (mB - mS)) :
    c.Vague ∧ c.Determinately WeakOrderValued := by
  refine ⟨vague_of_cutoff_lt c (by simp [hadm]) (by simp [hadm]) hc hc' h, fun a ha ↦ ?_⟩
  rw [hadm] at ha
  rcases ha with rfl | rfl <;> exact utilitarian_weakOrderValued _

omit [IsStrictOrderedRing K] in
theorem indeterminate_complete (c : Context Health Patient K) (hu : utilitarian w ∈ c.adm)
    (hp : paretoRule ∈ c.adm) (hm : mS < mB) (ht : cB < t) : c.Indeterminate Complete :=
  c.indeterminate_of_disagree hu hp (utilitarian_weakOrderValued w).2 fun h ↦
    ((h (health mS mB cB t)).total .suzy .bill).elim
      (paretoRule_incomparable (i := Health.cardiovascular) (j := .musculoskeletal) ht hm).1
      (paretoRule_incomparable (i := Health.cardiovascular) (j := .musculoskeletal) ht hm).2

end Sorites

/-! ### Arrow's theorem and incoherence -/

/-- Arrow's conditions, transposed to dimensional aggregation. -/
def Arrovian [Preorder K] (a : Rule ι O K) : Prop :=
  Invariant ordinal a ∧ WeakOrderValued a ∧ WeakPareto a ∧ Independent a ∧ NonDictatorial a

theorem arrow [Fintype ι] [Fintype O] (h₃ : 3 ≤ Fintype.card O) (a : Rule ι O ℝ) :
    ¬ Arrovian a :=
  SocialChoice.arrow h₃ a

theorem Context.incoherent_of_arrovian [Fintype ι] [Fintype O] (h₃ : 3 ≤ Fintype.card O)
    (c : Context ι O ℝ) (h : c.Determinately Arrovian) : c.Incoherent :=
  Set.eq_empty_iff_forall_notMem.2 fun a ha ↦ arrow h₃ a (h a ha)

/-! ### Escaping Arrow by weakening the outputs -/

/-- A relation is acyclic, as the paper states it, when two strict steps yield a weak step. -/
def Acyclic (r : O → O → Prop) : Prop := ∀ x y z, AsymmRel r x y → AsymmRel r y z → r x z

/-- Condorcet's profile has three dimensions ranking three objects cyclically. -/
def condorcet : Profile (Fin 3) (Fin 3) ℕ := ![![2, 0, 1], ![1, 2, 0], ![0, 1, 2]]

theorem majority_condorcet :
    AsymmRel (majority condorcet) 0 1 ∧ AsymmRel (majority condorcet) 1 2 ∧
      AsymmRel (majority condorcet) 2 0 := by
  decide

theorem not_acyclic_majority_condorcet : ¬ Acyclic (majority condorcet) :=
  fun h ↦ majority_condorcet.2.2.2 (h 0 1 2 majority_condorcet.1 majority_condorcet.2.1)

/-! ### Sassoon's comparatives -/

section Sassoon

variable [Fintype ι] [LinearOrder K] (θ : ι → K)

/-- The comparative the paper attributes to Sassoon for each binding type is universal
quantification over the dimensions for conjunctive adjectives (*healthy*), existential for
disjunctive ones (*sick*), and for mixed ones (*intelligent*) counting the dimensions on which
the thresholds `θ` are met. -/
def sassoon : Degree.DimensionBindingType → Rule ι O K
  | .conjunctive => fun v x y ↦ ∀ i, v y i ≤ v x i
  | .disjunctive => fun v x y ↦ ∃ i, v y i ≤ v x i
  | .mixed => fun v x y ↦ #{i | θ i ≤ v y i} ≤ #{i | θ i ≤ v x i}

theorem sassoon_conjunctive : sassoon θ .conjunctive = (paretoRule : Rule ι O K) := rfl

theorem not_strongPareto_sassoon_disjunctive [Nontrivial ι] [Nontrivial O] [Nontrivial K] :
    ¬ StrongPareto (sassoon θ .disjunctive : Rule ι O K) := by
  intro h
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  obtain ⟨x, y, hxy⟩ := exists_pair_ne O
  obtain ⟨k, k', hk⟩ : ∃ k k' : K, k < k' := by
    obtain ⟨k, k', h⟩ := exists_pair_ne K
    exact h.lt_or_gt.elim (fun h ↦ ⟨k, k', h⟩) (fun h ↦ ⟨k', k, h⟩)
  classical
  let v : Profile ι O K := fun z l ↦ if z = y ∧ l ≠ i then k' else k
  have hle : v x ≤ v y := fun l ↦ by
    simp only [v, hxy, false_and, ite_false]
    split_ifs <;> simp [hk.le]
  have hlt : ∃ l, v x l < v y l := ⟨j, by simp [v, hxy, hij.symm, hk]⟩
  have hxy' : sassoon θ .disjunctive v x y := ⟨i, by simp [v, hxy]⟩
  exact ((h v y x hle).2 hlt).2 hxy'

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
