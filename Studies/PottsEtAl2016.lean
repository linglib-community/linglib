module

public import Linglib.Pragmatics.RSA.Uniform
public import Linglib.Logic.Aristotelian.Square

/-!
# Potts, Lassiter, Levy and Frank (2016): Embedded Implicatures as Pragmatic Inferences under Compositional Lexical Uncertainty

Potts, Lassiter, Levy and Frank model embedded implicatures as pragmatic inference under
compositional lexical uncertainty, in the context of their experiment (§6). Three players each
hit none, some but not all, or all of their shots, a vertex of `Aristotelian.Triangle`, and a
state is the multiset of outcomes (16). A message composes a quantifier over players with a
quantifier over shots, the null message added (18), and the lexica are the neo-Gricean
refinement set of *some*, itself or *some but not all* (14), (19d). The literal listener `L0`,
the speaker `S1` and the uncertainty listener `L1`, which inverts the speaker jointly over states
and lexica (13), are compared with the fixed-lexicon listener `L1fixed` of (19b). Every ordering
below holds at every rationality and every cost of the null message.

## Main results

* `one_some_local`, `no_some_local`: under *exactly one* and *no* the uncertainty listener gives
  mass to the locally enriched states, which the fixed-lexicon model excludes, the low but
  non-negligible enrichment under a negative quantifier that Chemla and Spector report.
* `one_some_literal_first`, `no_some_literal_first`: the literal construals NNS and NNN still
  rank first.
* `every_some_ordering`, `every_some_fixed`: for *every player hit some of his shots* the
  uncertainty listener mirrors the human ordering, SSS first and AAA last among the true states,
  where the fixed-lexicon listener puts SAA first.

## Implementation notes

The state and lexicon priors are flat (18). The null message is true at every state, so its
cost adds the same weight to every row of the speaker, and the share of a statement is its
informativity weight over the sum of the weights of the statements true at the state plus that
constant; each ordering is an inequality between such fractions in the weights `4^{-α}`,
`3^{-α}`, `2^{-α}`, `1`. The unconstrained refinement model (19c), whose lexica are the nonempty
subsets of the denotation of *some* over sets of shots, and the fit to the response data are not
formalized.

## References

* [potts-etal-2016]
* [chemla-spector-2011]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA Aristotelian
open scoped ENNReal NNReal

namespace PottsEtAl2016

/-! ### The context (§6, (16) and (18)) -/

/-- The states (16) are the multisets of three outcomes, each named by its outcomes. -/
inductive World where
  | NNN
  | NNS
  | NNA
  | NSS
  | NSA
  | NAA
  | SSS
  | SSA
  | SAA
  | AAA
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace World := ⊤

/-- The outcomes of a state. -/
def World.outcomes : World → Multiset Triangle
  | .NNN => {.E, .E, .E}
  | .NNS => {.E, .E, .IO}
  | .NNA => {.E, .E, .A}
  | .NSS => {.E, .IO, .IO}
  | .NSA => {.E, .IO, .A}
  | .NAA => {.E, .A, .A}
  | .SSS => {.IO, .IO, .IO}
  | .SSA => {.IO, .IO, .A}
  | .SAA => {.IO, .A, .A}
  | .AAA => {.A, .A, .A}

/-- The quantifiers over a player's shots are *every*, *no* and *some*. -/
inductive ShotQ where
  | every
  | no
  | some_
  deriving DecidableEq, Fintype

/-- The quantifiers over the players are *every*, *exactly one* and *no*. -/
inductive PlayerQ where
  | every
  | exactlyOne
  | no
  deriving DecidableEq, Fintype

/-- The lexica of the neo-Gricean refinement set (14), (19d) read *some* as itself or as *some
but not all*. -/
inductive Lex where
  | weak
  | strong
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace Lex := ⊤

/-- Under a lexicon *some* covers the outcomes with any hit, or those with some but not all. -/
def Lex.someDen : Lex → Finset Triangle
  | .weak => {.IO, .A}
  | .strong => {.IO}

/-- The refinement condition (11) holds, each lexicon reading *some* as a nonempty part of its
base denotation, which the base lexicon is. -/
theorem lex_refines : ∀ l : Lex, l.someDen.Nonempty ∧ l.someDen ⊆ Lex.weak.someDen := by
  decide

/-- Whether an outcome satisfies the quantifier over shots under a lexicon. -/
def ShotQ.Holds (l : Lex) : ShotQ → Triangle → Prop
  | .every, o => o = ⊤
  | .no, o => o = ⊥
  | .some_, o => o ∈ l.someDen

instance (l : Lex) (s : ShotQ) : DecidablePred (s.Holds l) := fun o ↦ by
  cases s <;> unfold ShotQ.Holds <;> infer_instance

/-- Whether a number of players satisfies the quantifier over players. -/
def PlayerQ.Holds : PlayerQ → ℕ → Prop
  | .every, n => n = 3
  | .exactlyOne, n => n = 1
  | .no, n => n = 0

instance (q : PlayerQ) : DecidablePred q.Holds := fun n ↦ by
  cases q <;> unfold PlayerQ.Holds <;> infer_instance

/-- A statement (18c) applies a quantifier over players to a quantifier over shots. -/
abbrev Stmt := PlayerQ × ShotQ

/-- A statement is true at a state under a lexicon when its quantifier over players holds of
the number of players whose outcome satisfies its quantifier over shots. -/
def Stmt.Truth (l : Lex) (s : Stmt) (w : World) : Prop :=
  s.1.Holds (w.outcomes.countP (s.2.Holds l))

instance (l : Lex) (s : Stmt) : DecidablePred (s.Truth l) := fun w ↦
  inferInstanceAs (Decidable (s.1.Holds (w.outcomes.countP (s.2.Holds l))))

/-- The extension of a statement under a lexicon. -/
def stmtSem (l : Lex) (s : Stmt) : Finset World := Finset.univ.filter (s.Truth l)

/-- The messages (18c) are the statements and the null message of (12a). -/
abbrev Msg := Option Stmt

instance : MeasurableSpace Msg := ⊤

/-- The extension of a message under a lexicon, the null message true at every state. -/
def sem (l : Lex) (m : Msg) : Finset World := m.elim Finset.univ (stmtSem l)

/-- *Every player hit some of his shots*. -/
abbrev everySome : Stmt := (.every, .some_)

/-- *Exactly one player hit some of his shots*. -/
abbrev oneSome : Stmt := (.exactlyOne, .some_)

/-- *No player hit some of his shots*. -/
abbrev noSome : Stmt := (.no, .some_)

theorem refinement_facts :
    (∀ q : PlayerQ, stmtSem .weak (q, .every) = stmtSem .strong (q, .every) ∧
      stmtSem .weak (q, .no) = stmtSem .strong (q, .no)) ∧
    stmtSem .strong everySome ⊂ stmtSem .weak everySome ∧
    stmtSem .weak noSome ⊂ stmtSem .strong noSome ∧
    stmtSem .weak oneSome = {.NNS, .NNA} ∧ stmtSem .strong oneSome = {.NNS, .NSA, .SAA} := by
  decide

/-! ### The model (13), (18), (19) -/

section Tower

variable (α k : ℝ)

/-- The cost (18d) is `k` for the null message and 0 for every statement. -/
def cost (m : Msg) : ℝ := m.elim k fun _ ↦ 0

/-- The literal listener (13a) conditions a flat prior on the message's extension. -/
noncomputable def L0 (l : Lex) : Kernel Msg World :=
  listener (uniformOn Set.univ) (truthful fun m ↦ (sem l m : Set World))

instance (l : Lex) : IsFiniteKernel (L0 l) := inferInstanceAs (IsFiniteKernel (listener _ _))

/-- The speaker (13b). -/
noncomputable def S1 (l : Lex) : Kernel World Msg := speaker α (cost k) (L0 l) Measure.dirac

instance (l : Lex) : IsFiniteKernel (S1 α k l) := inferInstanceAs (IsFiniteKernel (speaker _ _ _ _))

/-- The uncertainty listener (13c) inverts the lexicon-indexed speaker against flat priors over
states and lexica; its state marginal is the paper's listener. -/
noncomputable def L1 : Kernel Msg (World × Lex) :=
  listener (uniformOn Set.univ) fun p ↦ S1 α k p.2 p.1

/-- The fixed-lexicon pragmatic listener (19b) inverts the base lexicon's speaker at a flat
prior. -/
noncomputable def L1fixed : Kernel Msg World :=
  listener (uniformOn Set.univ) (S1 α k .weak)

end Tower

/-- State preference of the uncertainty listener is the pooled speaker preference. -/
theorem L1_fst_real_lt_iff {α k : ℝ} (m : Msg) (w₁ w₂ : World) :
    (L1 α k m).fst.real {w₁} < (L1 α k m).fst.real {w₂} ↔
      ∑ l, (S1 α k l w₁).real {m} < ∑ l, (S1 α k l w₂).real {m} := by
  rw [L1, listener_fst_real_lt_iff_of_forall_eq _ _ uniformOn_univ_singleton_eq
    uniformOn_univ_singleton_ne_zero]

/-- State preference of the fixed-lexicon listener is the base-lexicon speaker's preference. -/
theorem L1fixed_real_lt_iff {α k : ℝ} (m : Msg) (w₁ w₂ : World) :
    (L1fixed α k m).real {w₁} < (L1fixed α k m).real {w₂} ↔
      (S1 α k .weak w₁).real {m} < (S1 α k .weak w₂).real {m} :=
  listener_uniformOn_real_lt_iff _ m w₁ w₂

section Model

variable {α : ℝ} (hα : 0 < α) {k : ℝ}
include hα

/-! ### Support: local enrichment (§6.3) -/

theorem L1_fst_ne_zero_iff (m : Msg) (w : World) :
    (L1 α k m).fst {w} ≠ 0 ↔ ∃ l, w ∈ sem l m := by
  rw [L1, listener_fst_apply_singleton_ne_zero_iff]
  exact exists_congr fun l ↦ (and_iff_right (uniformOn_univ_singleton_ne_zero _)).trans
    (speaker_uniformOn_dirac_apply_singleton_ne_zero_iff (sem l) hα (cost k) w m)

theorem L1fixed_ne_zero_iff (m : Msg) (w : World) :
    L1fixed α k m {w} ≠ 0 ↔ w ∈ sem .weak m := by
  rw [L1fixed, listener_apply_singleton_ne_zero_iff,
    and_iff_right (uniformOn_univ_singleton_ne_zero w)]
  exact speaker_uniformOn_dirac_apply_singleton_ne_zero_iff (sem .weak) hα (cost k) w m

/-- Hearing *exactly one player hit some of his shots*, the uncertainty listener gives mass to
the locally enriched states NSA and SAA, false on the literal construal, and the fixed-lexicon
listener none. -/
theorem one_some_local :
    ∀ w ∈ ({.NSA, .SAA} : Finset World),
      (L1 α k (some oneSome)).fst {w} ≠ 0 ∧ L1fixed α k (some oneSome) {w} = 0 := by
  intro w hw
  rw [L1_fst_ne_zero_iff hα, ← not_ne_iff, (L1fixed_ne_zero_iff hα _ w).not]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl <;> decide

/-- Hearing *no player hit some of his shots*, the uncertainty listener gives mass to the locally
enriched states NNA, NAA and AAA, and the fixed-lexicon listener none. -/
theorem no_some_local :
    ∀ w ∈ ({.NNA, .NAA, .AAA} : Finset World),
      (L1 α k (some noSome)).fst {w} ≠ 0 ∧ L1fixed α k (some noSome) {w} = 0 := by
  intro w hw
  rw [L1_fst_ne_zero_iff hα, ← not_ne_iff, (L1fixed_ne_zero_iff hα _ w).not]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl <;> decide

/-! ### Preference orderings (§6.2, §6.3) -/

theorem S1_real (l : Lex) (w : World) (s : Stmt) :
    (S1 α k l w).real {some s}
      = (if w ∈ stmtSem l s then (((stmtSem l s).card : ℝ))⁻¹ ^ α else 0)
        / ((∑ s', if w ∈ stmtSem l s' then (((stmtSem l s').card : ℝ))⁻¹ ^ α else 0)
            + Real.exp (-(α * k)) * (10 : ℝ)⁻¹ ^ α) := by
  rw [S1, speaker_dirac_real_singleton hα.le, Fintype.sum_option]
  simp only [L0, listener_uniformOn_truthful_apply_singleton, sem, cost, Option.elim_some,
    Option.elim_none,
    Finset.mem_univ, ↓reduceIte, Finset.card_univ, (by decide : Fintype.card World = 10),
    mul_zero, neg_zero, Real.exp_zero, mul_one, apply_ite (· ^ α),
    ENNReal.zero_rpow_of_pos hα, apply_ite ENNReal.toReal, ENNReal.toReal_zero,
    ← ENNReal.toReal_rpow, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_ofNat,
    Nat.cast_ofNat]
  rw [add_comm, mul_comm]

end Model

/-! #### The weights and the sums -/

/-- The two lexica as `Fin 2`, for sums over the family. -/
def Lex.equivFin : Lex ≃ Fin 2 where
  toFun | .weak => 0 | .strong => 1
  invFun | 0 => .weak | 1 => .strong
  left_inv l := by cases l <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The quantifiers over players as `Fin 3`. -/
def PlayerQ.equivFin : PlayerQ ≃ Fin 3 where
  toFun | .every => 0 | .exactlyOne => 1 | .no => 2
  invFun | 0 => .every | 1 => .exactlyOne | 2 => .no
  left_inv q := by cases q <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The quantifiers over shots as `Fin 3`. -/
def ShotQ.equivFin : ShotQ ≃ Fin 3 where
  toFun | .every => 0 | .no => 1 | .some_ => 2
  invFun | 0 => .every | 1 => .no | 2 => .some_
  left_inv s := by cases s <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem Lex.sum_univ {M : Type*} [AddCommMonoid M] (f : Lex → M) :
    ∑ l, f l = f .weak + f .strong := by
  rw [Fintype.sum_equiv Lex.equivFin f (f ∘ Lex.equivFin.symm) fun l ↦ by simp,
    Fin.sum_univ_two]
  rfl

theorem PlayerQ.sum_univ {M : Type*} [AddCommMonoid M] (f : PlayerQ → M) :
    ∑ q, f q = f .every + f .exactlyOne + f .no := by
  rw [Fintype.sum_equiv PlayerQ.equivFin f (f ∘ PlayerQ.equivFin.symm) fun q ↦ by simp,
    Fin.sum_univ_three]
  rfl

theorem ShotQ.sum_univ {M : Type*} [AddCommMonoid M] (f : ShotQ → M) :
    ∑ s, f s = f .every + f .no + f .some_ := by
  rw [Fintype.sum_equiv ShotQ.equivFin f (f ∘ ShotQ.equivFin.symm) fun s ↦ by simp,
    Fin.sum_univ_three]
  rfl

private theorem cards :
    (stmtSem .weak (.every, .every)).card = 1 ∧ (stmtSem .strong (.every, .every)).card = 1 ∧
    (stmtSem .weak (.every, .no)).card = 1 ∧ (stmtSem .strong (.every, .no)).card = 1 ∧
    (stmtSem .weak everySome).card = 4 ∧ (stmtSem .strong everySome).card = 1 ∧
    (stmtSem .weak (.exactlyOne, .every)).card = 3 ∧
    (stmtSem .strong (.exactlyOne, .every)).card = 3 ∧
    (stmtSem .weak (.exactlyOne, .no)).card = 3 ∧ (stmtSem .strong (.exactlyOne, .no)).card = 3 ∧
    (stmtSem .weak oneSome).card = 2 ∧ (stmtSem .strong oneSome).card = 3 ∧
    (stmtSem .weak (.no, .every)).card = 4 ∧ (stmtSem .strong (.no, .every)).card = 4 ∧
    (stmtSem .weak (.no, .no)).card = 4 ∧ (stmtSem .strong (.no, .no)).card = 4 ∧
    (stmtSem .weak noSome).card = 1 ∧ (stmtSem .strong noSome).card = 4 := by
  decide

section Findings

variable {α : ℝ} (hα : 0 < α) {k : ℝ}
include hα

private theorem weights :
    0 < (4 : ℝ)⁻¹ ^ α ∧ (4 : ℝ)⁻¹ ^ α < (3 : ℝ)⁻¹ ^ α ∧ (3 : ℝ)⁻¹ ^ α < (2 : ℝ)⁻¹ ^ α ∧
      (2 : ℝ)⁻¹ ^ α < 1 ∧ 0 ≤ Real.exp (-(α * k)) * (10 : ℝ)⁻¹ ^ α :=
  ⟨Real.rpow_pos_of_pos (by norm_num) α, Real.rpow_lt_rpow (by norm_num) (by norm_num) hα,
    Real.rpow_lt_rpow (by norm_num) (by norm_num) hα,
    Real.rpow_lt_one (by norm_num) (by norm_num) hα, by positivity⟩

/-- Hearing *every player hit some of his shots*, the uncertainty listener ranks the locally
enriched SSS above the other true states and AAA below the two remaining ones, the ordering of
the human responses. -/
theorem every_some_ordering :
    (L1 α k (some everySome)).fst.real {.SSA} < (L1 α k (some everySome)).fst.real {.SSS} ∧
    (L1 α k (some everySome)).fst.real {.SAA} < (L1 α k (some everySome)).fst.real {.SSS} ∧
    (L1 α k (some everySome)).fst.real {.AAA} < (L1 α k (some everySome)).fst.real {.SSA} ∧
    (L1 α k (some everySome)).fst.real {.AAA} < (L1 α k (some everySome)).fst.real {.SAA} := by
  obtain ⟨ha, hab, hbc, hc1, ht⟩ := weights hα (k := k)
  have ha1 : (4 : ℝ)⁻¹ ^ α < 1 := hab.trans (hbc.trans hc1)
  obtain ⟨c1, c2, -, -, c5, c6, c7, c8, -, -, -, c12, c13, c14, c15, c16, -, c18⟩ := cards
  simp +decide only [L1_fst_real_lt_iff, Lex.sum_univ, S1_real hα, Fintype.sum_prod_type,
    PlayerQ.sum_univ, ShotQ.sum_univ, c1, c2, c5, c6, c7, c8, c12, c13, c14, c15, c16, c18,
    Nat.cast_ofNat, Nat.cast_one, inv_one, Real.one_rpow, ↓reduceIte, add_zero, zero_add,
    zero_div]
  refine ⟨(div_lt_div_of_pos_left ha (by positivity) (by linarith)).trans_le
    (le_add_of_nonneg_right (by positivity)), ?_,
    div_lt_div_of_pos_left ha (by positivity) (by linarith),
    div_lt_div_of_pos_left ha (by positivity) (by linarith)⟩
  rw [div_add_div _ _ (by positivity) (by positivity), div_lt_div_iff₀ (by positivity)
    (by positivity)]
  nlinarith [mul_pos ha ha, mul_pos (mul_pos ha ha) (sub_pos.2 ha1), mul_nonneg ha.le ht,
    mul_nonneg (mul_nonneg ha.le ht) (sub_pos.2 ha1).le, mul_nonneg ht ht]

/-- The fixed-lexicon listener instead puts SAA above SSS. -/
theorem every_some_fixed :
    (L1fixed α k (some everySome)).real {.SSS} < (L1fixed α k (some everySome)).real {.SAA} := by
  obtain ⟨ha, -, -, -, -⟩ := weights hα (k := k)
  obtain ⟨-, -, -, -, c5, -, -, -, -, -, -, -, c13, -, c15, -, -, -⟩ := cards
  simp +decide only [L1fixed_real_lt_iff, S1_real hα, Fintype.sum_prod_type,
    PlayerQ.sum_univ, ShotQ.sum_univ, c5, c13, c15, Nat.cast_ofNat, ↓reduceIte, add_zero,
    zero_add]
  exact div_lt_div_of_pos_left ha (by positivity) (by linarith)

/-- Hearing *exactly one player hit some of his shots*, the uncertainty listener still prefers the
literal construal NNS most, above NNA and above the locally enriched NSA and SAA. -/
theorem one_some_literal_first :
    (L1 α k (some oneSome)).fst.real {.NNA} < (L1 α k (some oneSome)).fst.real {.NNS} ∧
    (L1 α k (some oneSome)).fst.real {.NSA} < (L1 α k (some oneSome)).fst.real {.NNS} ∧
    (L1 α k (some oneSome)).fst.real {.SAA} < (L1 α k (some oneSome)).fst.real {.NNS} := by
  obtain ⟨ha, hab, hbc, -, -⟩ := weights hα (k := k)
  obtain ⟨-, -, -, -, c5, -, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, -, c18⟩ := cards
  simp +decide only [L1_fst_real_lt_iff, Lex.sum_univ, S1_real hα, Fintype.sum_prod_type,
    PlayerQ.sum_univ, ShotQ.sum_univ, c5, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c18,
    Nat.cast_ofNat, ↓reduceIte, add_zero, zero_add, zero_div]
  exact ⟨(div_lt_div_of_pos_left (ha.trans (hab.trans hbc)) (by positivity) (by linarith)).trans_le
      (le_add_of_nonneg_right (by positivity)),
    (div_lt_div_of_pos_left (ha.trans hab) (by positivity) (by linarith)).trans_le
      (le_add_of_nonneg_left (by positivity)),
    lt_add_of_pos_left _ (by positivity)⟩

/-- Hearing *no player hit some of his shots*, the uncertainty listener still prefers the literal
construal NNN most, above the locally enriched NNA, NAA and AAA. -/
theorem no_some_literal_first :
    (L1 α k (some noSome)).fst.real {.NNA} < (L1 α k (some noSome)).fst.real {.NNN} ∧
    (L1 α k (some noSome)).fst.real {.NAA} < (L1 α k (some noSome)).fst.real {.NNN} ∧
    (L1 α k (some noSome)).fst.real {.AAA} < (L1 α k (some noSome)).fst.real {.NNN} := by
  obtain ⟨ha, hab, -, -, ht⟩ := weights hα (k := k)
  obtain ⟨c1, c2, c3, c4, c5, -, c7, c8, c9, c10, c11, -, c13, c14, c15, c16, c17, c18⟩ := cards
  simp +decide only [L1_fst_real_lt_iff, Lex.sum_univ, S1_real hα, Fintype.sum_prod_type,
    PlayerQ.sum_univ, ShotQ.sum_univ, c1, c2, c3, c4, c5, c7, c8, c9, c10, c11, c13, c14, c15,
    c16, c17, c18, Nat.cast_ofNat, Nat.cast_one, inv_one, Real.one_rpow, ↓reduceIte, add_zero,
    zero_add, zero_div]
  have hab' : 0 < (3 : ℝ)⁻¹ ^ α - (4 : ℝ)⁻¹ ^ α := sub_pos.2 hab
  have key : (4 : ℝ)⁻¹ ^ α / ((3 : ℝ)⁻¹ ^ α + (4 : ℝ)⁻¹ ^ α + Real.exp (-(α * k)) * (10 : ℝ)⁻¹ ^ α)
      < 1 / (1 + ((4 : ℝ)⁻¹ ^ α + 1) + Real.exp (-(α * k)) * (10 : ℝ)⁻¹ ^ α)
        + (4 : ℝ)⁻¹ ^ α /
          (1 + ((4 : ℝ)⁻¹ ^ α + (4 : ℝ)⁻¹ ^ α) + Real.exp (-(α * k)) * (10 : ℝ)⁻¹ ^ α) := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_lt_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith [mul_pos ha ha, mul_pos (mul_pos ha ha) hab', mul_nonneg ha.le ht,
      mul_nonneg (mul_nonneg ha.le ht) hab'.le, mul_pos ha hab', mul_nonneg ht ht,
      mul_nonneg hab'.le ht]
  exact ⟨key, key, lt_add_of_pos_left _ (by positivity)⟩

end Findings

end PottsEtAl2016
