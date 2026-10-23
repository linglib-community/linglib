module

public import Linglib.Phonology.HarmonicGrammar.MaxEnt
public import Linglib.Phonology.Hiatus
public import Linglib.Phonology.OptimalityTheory.Correspondence.Deletion
public import Linglib.Fragments.Farsi.Phonology

/-!
# Storme (2026): A Method to Evaluate Systemic Constraints in Probabilistic Grammars

This file formalizes [storme-2026]'s method for fitting systemic constraints, those that
score several input-output mappings jointly, in probabilistic constraint-based grammars: a
maximum-entropy distribution is evaluated over the joint tableau of output tuples and the
probability of each mapping is recovered by marginalization. With the systemic weights at
zero the marginal is the classical maximum-entropy probability of the mapping
(`marginal_eq_classical_of_systemic_zero`). The case study is variable hiatus resolution in
spoken Persian ([ariyaee-jurgec-2021]): the suffix vowel of the possessive /hutʃɑ-emun/
usually deletes while that of the definite /hutʃɑ-e/ rarely does, since deleting it would
make the suffixed form homophonous with the bare stem. The paradigm is two junctures over
Persian segments (`definite`, `possessive`), homophony is string identity
(`homophonyAvoidance`, `starHomophony`), and the joint tableau puts \*HOMOPHONY beside the
jointly evaluated classical constraints (`jointCon`), with the mapping probabilities its
marginals (`predicted`).

On this paradigm \*HOMOPHONY coincides with the jointly evaluated REALIZEMORPHEME of
[kurisu-2001] that [ariyaee-jurgec-2021] use, so the marginalized model is their classical
one (`starHomophony_eq_joint_realizeMorpheme`, `predicted_eq_maxEnt`). Whatever the
weights, the suffix-length effect on deletion, in log-odds against faithful hiatus, is
exactly the \*HOMOPHONY weight (`log_odds_deletion_sub`), deletion is less likely for the
monosegmental suffix whenever that weight is positive (`deletion_lt_deletion`), and without
\*HOMOPHONY the two suffixes receive identical distributions (`classical_no_length_effect`).
At the paper's fitted weights the predicted orders are those of its Table 5 (`mono_order`,
`poly_order`).

## Implementation notes

The fitted weights are the paper's posterior means, with MAX fixed at one as in the paper;
the theorems about the suffix-length effect are stated for arbitrary weights and only the
preference orders use the fitted values. The base's single faithful candidate enters the
tableau as the bare stem. The paper's model comparison by deviance information criterion
is not formalized.

## References

* [storme-2026]
* [ariyaee-jurgec-2021]
* [kurisu-2001]
* [casali-2011]
-/

@[expose] public section

namespace Storme2026

open OptimalityTheory HarmonicGrammar Phonology Farsi MeasureTheory Finset Real

/-! ### Systemic constraints, joint evaluation, and marginalization -/

/-- \*HOMOPHONY counts the pairs of distinct inputs that receive identical outputs. It is a
systemic constraint, one that scores a whole output tuple and not a single mapping, so it is a
`Constraint` on `Fin n → O` that does not decompose over the mappings. -/
def homophonyAvoidance {n : ℕ} {O : Type*} [DecidableEq O] : Constraint (Fin n → O) :=
  fun f ↦ #{p : Fin n × Fin n | p.1 < p.2 ∧ f p.1 = f p.2}

section Method

variable {ι I O : Type*} [Fintype ι] [DecidableEq ι] [Fintype O] [MeasurableSpace O]
  [MeasurableSingletonClass O] [Nonempty O] {m k : ℕ}

theorem marginal_eq_classical_of_systemic_zero (inputs : ι → I)
    (scon : ConstraintSet (ι → O) (Fin k))
    (con : ConstraintSet (I × O) (Fin m)) (w : Fin m → ℝ) (i : ι) :
    (maxEnt (ConstraintSet.violations (Fin.append scon (con.joint inputs))) (Fin.append 0 w)).map
        (Function.eval i) =
      maxEnt (con.comap (inputs i, ·)).violations w := by
  rw [maxEnt_congr (T' := fun f ↦ ∑ k, (con.comap (inputs k, ·)).violations (f k)) (w' := w)
    (funext fun f ↦ by
      rw [harmony_sum (fun k ↦ (con.comap (inputs k, ·)).violations)]
      simp [harmonyScore_append, harmonyScore_joint]),
    map_eval_maxEnt_sum]

end Method

/-! ### The Persian paradigm -/

/-- The three candidate realizations of a suffixed input — the
hiatus-resolution typology ([casali-2011]) as restricted by
[ariyaee-jurgec-2021]. -/
inductive Resolution where
  /-- Faithful vowel hiatus, e.g. [hutʃɑe]. -/
  | hiatus
  /-- Glottal-stop epenthesis, e.g. [hutʃɑʔe]. -/
  | epenthesis
  /-- Suffix-vowel deletion, e.g. [hutʃɑ], [hutʃɑmun]. -/
  | deletion
  deriving DecidableEq, Fintype, Inhabited, Repr

instance : MeasurableSpace Resolution := ⊤
instance : MeasurableSingletonClass Resolution := ⟨fun _ ↦ trivial⟩

instance : Nontrivial Resolution := ⟨.hiatus, .deletion, by decide⟩

/-- The definite-suffix juncture /hutʃɑ-e/: a monosegmental suffix. -/
def definite : Hiatus.Juncture :=
  ⟨[h, u, tesh], scriptA, e, [], by decide, by decide⟩

/-- The possessive-suffix juncture /hutʃɑ-emun/: a polysegmental suffix. -/
def possessive : Hiatus.Juncture :=
  ⟨[h, u, tesh], scriptA, e, [m, u, n], by decide, by decide⟩

/-- The inputs of the joint tableau are the definite and the possessive junctures. -/
def inputs : Fin 2 → Hiatus.Juncture := ![definite, possessive]

/-- `resolve o j` is the surface form of the candidate `o` at the juncture `j`, with faithful
hiatus, glottal-stop epenthesis, or elision of the suffix vowel. -/
def resolve : Resolution → Hiatus.Juncture → List Segment
  | .hiatus => Hiatus.Juncture.input
  | .epenthesis => (Hiatus.Juncture.epenthesize · glottalStop)
  | .deletion => Hiatus.Juncture.elideV2

/-! ### The constraints and the joint tableau -/

/-- \*HIATUS counts the adjacent vowel pairs that survive in the surface form. -/
def starHiatus : Constraint (Hiatus.Juncture × Resolution) := fun c ↦
  Hiatus.count (resolve c.2 c.1)

/-- `corr o j` is the correspondence between the unrepaired concatenation and the candidate
`o`, which is the identity for faithful hiatus, the insertion of a glottal stop before the
suffix vowel for epenthesis, and the deletion of the suffix vowel for elision. -/
def corr : Resolution → Hiatus.Juncture → Correspondence BinaryRole Segment
  | .hiatus, j => Correspondence.identity j.input
  | .epenthesis, j =>
    Correspondence.insertIdx j.input ⟨j.v2Idx, j.v2Idx_lt_length_input.trans (by omega)⟩ glottalStop
  | .deletion, j => Correspondence.eraseIdx j.input ⟨j.v2Idx, j.v2Idx_lt_length_input⟩

theorem corr_form_rhs (o : Resolution) (j : Hiatus.Juncture) :
    (corr o j).form .rhs = resolve o j := by
  cases o
  · rfl
  · exact (j.epenthesize_eq_insertIdx glottalStop).symm
  · exact j.elideV2_eq_eraseIdx.symm

/-- DEP counts the output segments that have no correspondent in the input. -/
def depConstraint : Constraint (Hiatus.Juncture × Resolution) := fun c ↦
  (corr c.2 c.1).depViol .lhs .rhs

/-- MAX counts the input segments that have no correspondent in the output. -/
def maxConstraint : Constraint (Hiatus.Juncture × Resolution) := fun c ↦
  (corr c.2 c.1).maxViol .lhs .rhs

theorem depConstraint_eq (j : Hiatus.Juncture) (o : Resolution) :
    depConstraint (j, o) = if o = .epenthesis then 1 else 0 := by
  cases o
  · exact Correspondence.depViol_identity _
  · exact Correspondence.depViol_insertIdx
  · exact Correspondence.depViol_eraseIdx

theorem maxConstraint_eq (j : Hiatus.Juncture) (o : Resolution) :
    maxConstraint (j, o) = if o = .deletion then 1 else 0 := by
  cases o
  · exact Correspondence.maxViol_identity _
  · exact Correspondence.maxViol_insertIdx
  · exact Correspondence.maxViol_eraseIdx

theorem starHiatus_eq (k : Fin 2) (o : Resolution) :
    starHiatus (inputs k, o) = if o = .hiatus then 1 else 0 := by
  revert k o; decide

/-- The classical constraint set consists of DEP, \*HIATUS and MAX. -/
def classicalCon : ConstraintSet (Hiatus.Juncture × Resolution) (Fin 3) :=
  ![depConstraint, starHiatus, maxConstraint]

/-- The fitted classical weights, posterior means with MAX fixed at one. -/
noncomputable def classicalW : Fin 3 → ℝ := ![2.47, 1.89, 1]

@[simp] theorem classicalW_zero : classicalW 0 = 2.47 := rfl
@[simp] theorem classicalW_one : classicalW 1 = 1.89 := rfl
@[simp] theorem classicalW_two : classicalW 2 = 1 := rfl

/-- \*HOMOPHONY over the paradigm counts the collisions among the surface forms of the base,
which is realized faithfully as the bare stem, its only candidate, and of the two suffixed
inputs. Two outputs collide when they are the same string. -/
def starHomophony : Constraint (Fin 2 → Resolution) := fun f ↦
  homophonyAvoidance (Fin.cons definite.stem fun k ↦ resolve (f k) (inputs k))

/-- The fitted \*HOMOPHONY weight, a posterior mean. -/
noncomputable def homophonyWeight : ℝ := 2.27

/-- The constraint set of the joint tableau puts \*HOMOPHONY beside the jointly evaluated
classical constraints. These are the columns of the paper's Table 4, over its nine output
tuples. -/
def jointCon : ConstraintSet (Fin 2 → Resolution) (Fin 4) :=
  Fin.append ![starHomophony] (classicalCon.joint inputs)

/-- The weights of the joint tableau are `wh` for \*HOMOPHONY and `w` for the classical
constraints. -/
def jointW (wh : ℝ) (w : Fin 3 → ℝ) : Fin 4 → ℝ := Fin.append ![wh] w

/-- `predicted wh w k` is the distribution of input `k`'s realizations, the marginal of the
joint MaxEnt distribution by the paper's marginalization equation, which gives its Table 5 at the
fitted weights. -/
noncomputable def predicted (wh : ℝ) (w : Fin 3 → ℝ) (k : Fin 2) : Measure Resolution :=
  (maxEnt jointCon.violations (jointW wh w)).map (Function.eval k)

/-! ### \*HOMOPHONY against REALIZEMORPHEME

[ariyaee-jurgec-2021] analyse the same data with a per-mapping constraint
penalizing a null realization of the suffix ([kurisu-2001]'s
REALIZEMORPHEME) in place of \*HOMOPHONY. [storme-2026] notes that the two
coincide here, and that only the systemic constraint extends to homophony
avoidance not involving a null morpheme. -/

/-- REALIZEMORPHEME is violated when the suffix has a null realization, the suffixed form
surfacing as its bare stem. -/
def realizeMorpheme : Constraint (Hiatus.Juncture × Resolution) :=
  Constraint.binary fun c ↦ resolve c.2 c.1 = c.1.stem

theorem realizeMorpheme_eq (j : Hiatus.Juncture) (o : Resolution) :
    realizeMorpheme (j, o) = if o = .deletion ∧ j.suffixBody = [] then 1 else 0 := by
  cases o <;> simp [realizeMorpheme, resolve, j.input_ne_stem, j.epenthesize_ne_stem]

theorem starHomophony_eq_joint_realizeMorpheme :
    starHomophony = realizeMorpheme.joint inputs := by
  funext f; revert f; decide

/-- [ariyaee-jurgec-2021]'s classical constraint set, REALIZEMORPHEME beside DEP, \*HIATUS
and MAX. -/
def ajCon : ConstraintSet (Hiatus.Juncture × Resolution) (Fin 4) :=
  Matrix.vecCons realizeMorpheme classicalCon

/-- The weights of `ajCon`, REALIZEMORPHEME at the \*HOMOPHONY weight. -/
def ajW (wh : ℝ) (w : Fin 3 → ℝ) : Fin 4 → ℝ := Matrix.vecCons wh w

theorem harmonyScore_jointCon (wh : ℝ) (w : Fin 3 → ℝ) (f : Fin 2 → Resolution) :
    harmonyScore jointCon (jointW wh w) f = ∑ k, harmonyScore ajCon (ajW wh w) (inputs k, f k) := by
  rw [jointCon, jointW, harmonyScore_append]
  simp [ajCon, ajW, harmonyScore_joint, starHomophony_eq_joint_realizeMorpheme, Fin.sum_univ_two]
  ring

theorem predicted_eq_maxEnt (wh : ℝ) (w : Fin 3 → ℝ) (k : Fin 2) :
    predicted wh w k = maxEnt (ajCon.comap (inputs k, ·)).violations (ajW wh w) := by
  rw [predicted, maxEnt_congr
    (T' := fun f ↦ ∑ k, (ajCon.comap (inputs k, ·)).violations (f k)) (w' := ajW wh w)
    (funext fun f ↦ by
      rw [harmony_sum (fun k ↦ (ajCon.comap (inputs k, ·)).violations)]
      simp [harmonyScore_jointCon]), map_eval_maxEnt_sum]

theorem ajScore_eq (wh : ℝ) (w : Fin 3 → ℝ) (k : Fin 2) (o : Resolution) :
    harmonyScore ajCon (ajW wh w) (inputs k, o) = -(match o with
      | .hiatus => w 1
      | .epenthesis => w 0
      | .deletion => w 2 + if k = 0 then wh else 0) := by
  fin_cases k <;> cases o <;>
    simp [harmonyScore, dotProduct, Fin.sum_univ_four, ajCon, ajW, classicalCon,
      realizeMorpheme_eq, depConstraint_eq, starHiatus_eq, maxConstraint_eq]
  simp [inputs, definite, possessive]
  ring

/-! ### Predictions with the fitted weights -/

/-- At the fitted weights the monosegmental suffix prefers hiatus over epenthesis over
deletion, which would merge the suffixed form with the bare stem. -/
theorem mono_order :
    (predicted homophonyWeight classicalW 0).real {.deletion} <
        (predicted homophonyWeight classicalW 0).real {.epenthesis} ∧
      (predicted homophonyWeight classicalW 0).real {.epenthesis} <
        (predicted homophonyWeight classicalW 0).real {.hiatus} := by
  simp only [predicted_eq_maxEnt, maxEnt_real_singleton_lt_iff, harmony_violations,
    harmonyScore_comap]
  exact ⟨by norm_num [ajScore_eq, homophonyWeight], by norm_num [ajScore_eq, homophonyWeight]⟩

/-- At the fitted weights the polysegmental suffix prefers deletion over hiatus over
epenthesis: the suffix stays recoverable, so \*HOMOPHONY is silent. -/
theorem poly_order :
    (predicted homophonyWeight classicalW 1).real {.epenthesis} <
        (predicted homophonyWeight classicalW 1).real {.hiatus} ∧
      (predicted homophonyWeight classicalW 1).real {.hiatus} <
        (predicted homophonyWeight classicalW 1).real {.deletion} := by
  simp only [predicted_eq_maxEnt, maxEnt_real_singleton_lt_iff, harmony_violations,
    harmonyScore_comap]
  exact ⟨by norm_num [ajScore_eq, homophonyWeight], by norm_num [ajScore_eq, homophonyWeight]⟩

theorem deletion_lt_deletion {wh : ℝ} (hwh : 0 < wh) (w : Fin 3 → ℝ) :
    (predicted wh w 0).real {.deletion} < (predicted wh w 1).real {.deletion} := by
  simp only [predicted_eq_maxEnt, maxEnt_real_singleton, harmony_violations]
  refine softmax_lt_softmax_of_single_lt ?_ fun o ho ↦ ?_
  · simp only [harmonyScore_comap, ajScore_eq]; simp; linarith
  · cases o <;> simp_all [ajScore_eq]

theorem log_odds_deletion_sub (wh : ℝ) (w : Fin 3 → ℝ) :
    log ((predicted wh w 1).real {.deletion} / (predicted wh w 1).real {.hiatus}) -
      log ((predicted wh w 0).real {.deletion} / (predicted wh w 0).real {.hiatus}) = wh := by
  simp only [predicted_eq_maxEnt, log_maxEnt_real_singleton_div, harmony_violations,
    harmonyScore_comap, ajScore_eq]
  simp

theorem harmonyScore_classicalCon_inputs (w : Fin 3 → ℝ) (k k' : Fin 2) (o : Resolution) :
    harmonyScore classicalCon w (inputs k, o) = harmonyScore classicalCon w (inputs k', o) :=
  harmonyScore_congr fun j ↦ by
    fin_cases j <;> simp [classicalCon, depConstraint_eq, starHiatus_eq, maxConstraint_eq]

theorem classical_no_length_effect (w : Fin 3 → ℝ) :
    maxEnt (classicalCon.comap (inputs 0, ·)).violations w =
      maxEnt (classicalCon.comap (inputs 1, ·)).violations w :=
  maxEnt_congr (funext fun o ↦ harmonyScore_classicalCon_inputs w 0 1 o)

end Storme2026
