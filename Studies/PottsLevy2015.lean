module

public import Linglib.Core.Probability.Kernel.Module
public import Linglib.Pragmatics.RSA.Uniform

/-!
# Potts and Levy (2015): Negotiating Lexical Uncertainty and Speaker Expertise with Disjunction

This file formalizes the lexical-uncertainty model of Potts and Levy and its Hurfordian context.
Disjunctions *A or X* whose disjunct *X* covers *A* violate the generalization of Hurford yet are
used, and the listener who hears one infers both that the speaker is uncertain between the disjuncts
and that her lexicon keeps them apart. The model is a rational-speech-acts tower over states,
messages, and lexica (§3). A literal listener conditions a flat prior on a message's extension under
a lexicon (10), a speaker chooses messages by the listener's mass at the state under a rationality
and a cost (11), and a pragmatic listener inverts the speaker (12) (`L0`, `S1`, `l1`); the
lexical-uncertainty listener infers state and lexicon jointly (14) (`L1`), the expertise speaker
weighs the world information and the lexicon information a message carries (15) (`S2`), the next
listener inverts her (`L2`), and marginalization recovers simple signaling (16), (17) (`S2exp`). The
state space is closed under joins so that a disjunction can convey uncertainty, a join state
satisfying a message when all its atoms do (§4, Figure 6), and the lexica refine the unknown term
*X* (13) (`World`, `Msg`, `Lex`, `sem`).

In the Hurfordian context of §5.2, three atoms, the terms *A*, *B*, *X* with their
disjunctions, and the lexica reading *X* as the general term, its exclusivization, or the
synonym of *A*, at the paper's rationality α = 2 and lexicon weight β = 1, with the disjunction
cost free: the level-one listener hearing *A or X* ranks the uncertain state first
and the exclusivized lexicon first (`l1_uncertainty`, `l1_lexicon`), the exclusivizing speaker
uses the disjunction exactly when uncertain (`s1_disjunction_iff_uncertain`), the disjunction
signals exclusivization where the bare disjunct does not (`AorX_signals_excl`), and the
expertise speaker who is uncertain and exclusivizes prefers the disjunction to every other
message, the paper's production claim for this context (`s2_prefers_disjunction`,
`s2exp_uncertain`). Each ordering is stated on a range of disjunction costs containing the
paper's 1.

## Implementation notes

The agents are kernels of `Pragmatics/RSA`, the speakers power-weight kernels and the
listeners Bayesian inverses against uniform priors; the expertise speaker is a weight kernel
built from the fixed-lexicon listener and the lexicon posterior. The paper's speakers subtract
the cost outside the rationality, so it enters the substrate speaker divided by α. Listener
preferences reduce to speaker preferences (`l1_real_lt_iff`, `L1_fst_real_lt_iff`,
`S2_real_lt_iff`), and a speaker's share is a rational function of the cost factor `exp (−c)`,
so each ordering is a polynomial inequality in it certified by its Bernstein coefficients on the
stated range. The definitional
regime of §5.1, which needs β > α, and the parameter exploration of §5.4 are not formalized.

## TODO

The level-two readings of Figure 10, the listener `L2` hearing *A or X* ranking the uncertain
state and the exclusivized lexicon first, and the marginal speaker `S2exp` preferring the bare
*A* when certain of the first atom, are rational inequalities in the cost factor of very high degree
whose symbolic certificates are out of reach; the paper reports them numerically at cost 1.

## References

* [potts-levy-2015]
* [hurford-1974]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal NNReal

namespace PottsLevy2015

/-! ### The domain (§4, §5) -/

/-- The three atomic states of the context. -/
inductive Atom where
  | w₁
  | w₂
  | w₃
  deriving DecidableEq, Fintype

/-- The states are the nonempty joins of the atoms (Figure 6). -/
inductive World where
  | w₁
  | w₂
  | w₃
  | w₁₂
  | w₁₃
  | w₂₃
  | w₁₂₃
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace World := ⊤

/-- The atoms a state joins. -/
def World.atoms : World → Finset Atom
  | .w₁ => {.w₁}
  | .w₂ => {.w₂}
  | .w₃ => {.w₃}
  | .w₁₂ => {.w₁, .w₂}
  | .w₁₃ => {.w₁, .w₃}
  | .w₂₃ => {.w₂, .w₃}
  | .w₁₂₃ => {.w₁, .w₂, .w₃}

/-- The messages are the basic terms, their disjunctions, and the null message. -/
inductive Msg where
  | A
  | B
  | X
  | AorB
  | AorX
  | BorX
  | AorBorX
  | null
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace Msg := ⊤

/-- Whether a message is a disjunction, the messages that carry a cost. -/
def Msg.IsDisjunction : Msg → Prop
  | .AorB | .AorX | .BorX | .AorBorX => True
  | _ => False

instance : DecidablePred Msg.IsDisjunction := fun m => by
  cases m <;> unfold Msg.IsDisjunction <;> infer_instance

/-- The lexica (13) are the base lexicon reading *X* as the general term over the first two
atoms, its exclusivization to the second atom, and the synonym of *A*. -/
inductive Lex where
  | base
  | excl
  | syn
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace Lex := ⊤

/-- The atoms *X* denotes under a lexicon. -/
def Lex.x : Lex → Finset Atom
  | .base => {.w₁, .w₂}
  | .excl => {.w₂}
  | .syn => {.w₁}

/-- Under a lexicon *A* denotes the first atom, *B* the second, a disjunction the union, and the
null message every atom. -/
def atomDen (l : Lex) : Msg → Finset Atom
  | .A => {.w₁}
  | .B => {.w₂}
  | .X => l.x
  | .AorB => {.w₁, .w₂}
  | .AorX => {.w₁} ∪ l.x
  | .BorX => {.w₂} ∪ l.x
  | .AorBorX => {.w₁, .w₂} ∪ l.x
  | .null => Finset.univ

/-- In the join-closed state space, a message is true of the states all of whose atoms it
denotes. -/
def sem (l : Lex) (m : Msg) : Finset World :=
  Finset.univ.filter fun w => w.atoms ⊆ atomDen l m

theorem lexica_facts :
    Disjoint (atomDen .excl .A) (atomDen .excl .X) ∧ atomDen .syn .AorX = atomDen .syn .A ∧
      (∀ m, World.w₁₂ ∈ sem .excl m ↔ m = .AorX ∨ m = .AorB ∨ m = .AorBorX ∨ m = .null) := by
  decide

theorem sem_nonempty (l : Lex) (m : Msg) : ∃ w, w ∈ sem l m := by
  revert l m; decide

/-- The null message is true of seven states, a message denoting two atoms of three, and any
other message of one. -/
def semCard : Lex → Msg → ℕ
  | _, .null => 7
  | _, .AorB | _, .AorBorX | .base, .X | .base, .AorX | .base, .BorX | .excl, .AorX
  | .syn, .BorX => 3
  | _, _ => 1

theorem card_sem (l : Lex) (m : Msg) : (sem l m).card = semCard l m := by
  revert l m; decide

/-! ### The tower (§3) -/

section Tower

variable (α β c : ℝ)

/-- A disjunction costs `c` and any other message nothing (9). -/
def cost (m : Msg) : ℝ := if m.IsDisjunction then c else 0

/-- The literal listener (10) conditions a flat prior on the message's extension. -/
noncomputable def L0 (l : Lex) : Kernel Msg World :=
  listener (uniformOn Set.univ) (truthful fun m ↦ (sem l m : Set World))

instance (l : Lex) : IsFiniteKernel (L0 l) := inferInstanceAs (IsFiniteKernel (listener _ _))

/-- The speaker (11) is the substrate's speaker, with the cost divided by the rationality
since the paper subtracts it outside. -/
noncomputable def S1 (l : Lex) : Kernel World Msg := speaker α (cost c · / α) (L0 l) Measure.dirac

instance (l : Lex) : IsFiniteKernel (S1 α c l) := inferInstanceAs (IsFiniteKernel (speaker _ _ _ _))

/-- The fixed-lexicon pragmatic listener (12) inverts the speaker against a flat prior. -/
noncomputable def l1 (l : Lex) : Kernel Msg World :=
  listener (uniformOn Set.univ) (S1 α c l)

instance (l : Lex) : IsFiniteKernel (l1 α c l) := inferInstanceAs (IsFiniteKernel (listener _ _))

/-- The lexical-uncertainty listener (14) at k = 1 inverts the lexicon-indexed speaker against a
flat prior over states and lexica. -/
noncomputable def L1 : Kernel Msg (World × Lex) :=
  listener (uniformOn Set.univ) fun p ↦ S1 α c p.2 p.1

instance : IsFiniteKernel (L1 α c) := inferInstanceAs (IsFiniteKernel (listener _ _))

/-- The expertise speaker (15) at k = 2 weighs the fixed-lexicon listener's mass at the state
to the rationality, the lexicon posterior to the lexicon weight, and the cost. -/
noncomputable def S2 : Kernel (World × Lex) Msg :=
  Kernel.ofWeights fun p m => l1 α c p.2 m {p.1} ^ α * (L1 α c m).snd {p.2} ^ β *
    ENNReal.ofReal (Real.exp (-cost c m))

instance : IsFiniteKernel (S2 α β c) := inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

/-- The lexical-uncertainty listener (14) at k = 2. -/
noncomputable def L2 : Kernel Msg (World × Lex) := listener (uniformOn Set.univ) (S2 α β c)

/-- The marginal expertise speaker (17) at a flat lexicon prior. -/
noncomputable def S2exp : Kernel World Msg :=
  ∑ l, uniformOn Set.univ {l} • (S2 α β c).comap (·, l) (measurable_of_countable _)

end Tower

/-! ### Support and preference reductions -/

section Listener

variable {α c : ℝ}

/-- State preference of the fixed-lexicon listener is the speaker's preference. -/
theorem l1_real_lt_iff (l : Lex) (m : Msg) (v v' : World) :
    (l1 α c l m).real {v} < (l1 α c l m).real {v'} ↔
      (S1 α c l v).real {m} < (S1 α c l v').real {m} :=
  listener_uniformOn_real_lt_iff _ m v v'

theorem l1_real (l : Lex) (m : Msg) (w : World) :
    (l1 α c l m).real {w} = (S1 α c l w).real {m} / ∑ w', (S1 α c l w').real {m} := by
  simpa [l1] using listener_uniformOn_univ_real_finset (S1 α c l) m {w}

/-- State preference of the joint listener is the pooled speaker preference. -/
theorem L1_fst_real_lt_iff (m : Msg) (v v' : World) :
    (L1 α c m).fst.real {v} < (L1 α c m).fst.real {v'} ↔
      ∑ l, (S1 α c l v).real {m} < ∑ l, (S1 α c l v').real {m} := by
  rw [L1, listener_fst_real_lt_iff_of_forall_eq _ _ uniformOn_univ_singleton_eq
    uniformOn_univ_singleton_ne_zero]

/-- Lexicon preference of the joint listener is the speaker preference pooled over states. -/
theorem L1_snd_real_lt_iff (m : Msg) (l₁ l₂ : Lex) :
    (L1 α c m).snd.real {l₁} < (L1 α c m).snd.real {l₂} ↔
      ∑ w, (S1 α c l₁ w).real {m} < ∑ w, (S1 α c l₂ w).real {m} := by
  rw [L1, listener_snd_real_lt_iff_of_forall_eq _ _ uniformOn_univ_singleton_eq
    uniformOn_univ_singleton_ne_zero]

theorem L1_snd_real (m : Msg) (l : Lex) :
    (L1 α c m).snd.real {l}
      = (∑ w, (S1 α c l w).real {m}) / ∑ p : World × Lex, (S1 α c p.2 p.1).real {m} := by
  rw [L1, listener_snd_real_singleton]
  simp only [uniformOn_univ_real_singleton]
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_div_mul_left _ _ (by positivity)]

end Listener

section Model

variable {α : ℝ} (hα : 0 < α) {c : ℝ}
include hα

theorem S1_ne_zero_iff (l : Lex) (w : World) (m : Msg) : S1 α c l w {m} ≠ 0 ↔ w ∈ sem l m :=
  speaker_uniformOn_dirac_apply_singleton_ne_zero_iff (sem l) hα _ w m

theorem l1_ne_zero_iff (l : Lex) (m : Msg) (w : World) : l1 α c l m {w} ≠ 0 ↔ w ∈ sem l m := by
  rw [l1, listener_apply_singleton_ne_zero_iff, and_iff_right (uniformOn_univ_singleton_ne_zero w)]
  exact S1_ne_zero_iff hα l w m

theorem L1_ne_zero_iff (m : Msg) (p : World × Lex) : L1 α c m {p} ≠ 0 ↔ p.1 ∈ sem p.2 m := by
  rw [L1, listener_apply_singleton_ne_zero_iff, and_iff_right (uniformOn_univ_singleton_ne_zero p)]
  exact S1_ne_zero_iff hα p.2 p.1 m

theorem L1_snd_ne_zero (m : Msg) (l : Lex) : (L1 α c m).snd {l} ≠ 0 := by
  obtain ⟨w₀, h₀⟩ := sem_nonempty l m
  rw [Measure.snd_apply_singleton]
  exact fun h => (L1_ne_zero_iff hα m (w₀, l)).2 h₀
    (Finset.sum_eq_zero_iff.1 h w₀ (Finset.mem_univ _))

end Model

/-- The factor a message's cost puts on its weight. -/
noncomputable def costFactor (c : ℝ) (m : Msg) : ℝ := Real.exp (-cost c m)

/-- The literal listener's mass at a state on reals. -/
noncomputable def l0r (l : Lex) (m : Msg) (w : World) : ℝ :=
  if w ∈ sem l m then ((sem l m).card : ℝ)⁻¹ else 0

theorem L0_rpow_toReal {α : ℝ} (hα : 0 < α) (l : Lex) (m : Msg) (w : World) :
    (L0 l m {w} ^ α).toReal = l0r l m w ^ α := by
  rw [L0, listener_uniformOn_truthful_apply_singleton, l0r]
  split_ifs
  · rw [← ENNReal.toReal_rpow, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  · rw [ENNReal.zero_rpow_of_pos hα, ENNReal.toReal_zero, Real.zero_rpow hα.ne']

theorem S1_real {α : ℝ} (hα : 0 < α) (c : ℝ) (l : Lex) (w : World) (m : Msg) :
    (S1 α c l w).real {m}
      = l0r l m w ^ α * costFactor c m / ∑ m', l0r l m' w ^ α * costFactor c m' := by
  have h : ∀ m, α * (cost c m / α) = cost c m := fun m => mul_div_cancel₀ _ hα.ne'
  rw [S1, speaker_dirac_real_singleton hα.le]
  simp only [L0_rpow_toReal hα, h, costFactor]

section Expertise

variable {α β : ℝ} (hα : 0 < α) {c : ℝ}
include hα

private theorem S2_weight_ne_zero {p : World × Lex} {m : Msg} (hm : p.1 ∈ sem p.2 m) :
    l1 α c p.2 m {p.1} ^ α * (L1 α c m).snd {p.2} ^ β * ENNReal.ofReal (Real.exp (-cost c m)) ≠
      0 :=
  mul_ne_zero (mul_ne_zero
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 ((l1_ne_zero_iff hα p.2 m p.1).2 hm))
      (measure_ne_top _ _)).ne'
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 (L1_snd_ne_zero hα m p.2)) (measure_ne_top _ _)).ne')
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'

theorem S2_apply_eq_zero {p : World × Lex} {m : Msg} (hm : p.1 ∉ sem p.2 m) : S2 α β c p {m} = 0 :=
  Kernel.ofWeights_apply_singleton_eq_zero (by
    rw [not_ne_iff.1 (mt (l1_ne_zero_iff hα p.2 m p.1).1 hm), ENNReal.zero_rpow_of_pos hα,
      zero_mul, zero_mul])

variable (hβ : 0 ≤ β)
include hβ

private theorem S2_weight_ne_top (p : World × Lex) (m : Msg) :
    l1 α c p.2 m {p.1} ^ α * (L1 α c m).snd {p.2} ^ β * ENNReal.ofReal (Real.exp (-cost c m)) ≠
      ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hα.le (measure_ne_top _ _))
    (ENNReal.rpow_ne_top_of_nonneg hβ (measure_ne_top _ _))) ENNReal.ofReal_ne_top

/-- Message preference of the expertise speaker is weight preference on reals. -/
theorem S2_real_lt_iff (p : World × Lex) (m₁ m₂ : Msg) :
    (S2 α β c p).real {m₁} < (S2 α β c p).real {m₂} ↔
      (l1 α c p.2 m₁).real {p.1} ^ α * (L1 α c m₁).snd.real {p.2} ^ β * costFactor c m₁
        < (l1 α c p.2 m₂).real {p.1} ^ α * (L1 α c m₂).snd.real {p.2} ^ β * costFactor c m₂ := by
  have hnull : ∀ p : World × Lex, p.1 ∈ sem p.2 .null := by decide
  have h0 : ∑ m, l1 α c p.2 m {p.1} ^ α * (L1 α c m).snd {p.2} ^ β *
      ENNReal.ofReal (Real.exp (-cost c m)) ≠ 0 := fun h =>
    S2_weight_ne_zero hα (hnull p) (Finset.sum_eq_zero_iff.1 h .null (Finset.mem_univ _))
  rw [S2, Kernel.ofWeights_real_singleton_lt_iff _ h0
    (ENNReal.sum_ne_top.2 fun m _ => S2_weight_ne_top hα hβ p m),
    ← ENNReal.toReal_lt_toReal (S2_weight_ne_top hα hβ p m₁) (S2_weight_ne_top hα hβ p m₂)]
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, measureReal_def,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, costFactor]

end Expertise

/-! ### The sums -/

/-- The states as `Fin 7`. -/
def World.equivFin : World ≃ Fin 7 where
  toFun | .w₁ => 0 | .w₂ => 1 | .w₃ => 2 | .w₁₂ => 3 | .w₁₃ => 4 | .w₂₃ => 5 | .w₁₂₃ => 6
  invFun | 0 => .w₁ | 1 => .w₂ | 2 => .w₃ | 3 => .w₁₂ | 4 => .w₁₃ | 5 => .w₂₃ | 6 => .w₁₂₃
  left_inv w := by cases w <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The messages as `Fin 8`. -/
def Msg.equivFin : Msg ≃ Fin 8 where
  toFun
    | .A => 0 | .B => 1 | .X => 2 | .AorB => 3 | .AorX => 4 | .BorX => 5 | .AorBorX => 6
    | .null => 7
  invFun
    | 0 => .A | 1 => .B | 2 => .X | 3 => .AorB | 4 => .AorX | 5 => .BorX | 6 => .AorBorX
    | 7 => .null
  left_inv m := by cases m <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The lexica as `Fin 3`. -/
def Lex.equivFin : Lex ≃ Fin 3 where
  toFun | .base => 0 | .excl => 1 | .syn => 2
  invFun | 0 => .base | 1 => .excl | 2 => .syn
  left_inv l := by cases l <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem World.sum_univ {M : Type*} [AddCommMonoid M] (f : World → M) :
    ∑ w, f w = f .w₁ + f .w₂ + f .w₃ + f .w₁₂ + f .w₁₃ + f .w₂₃ + f .w₁₂₃ := by
  rw [Fintype.sum_equiv World.equivFin f (f ∘ World.equivFin.symm) fun w => by simp,
    Fin.sum_univ_seven]
  rfl

theorem Msg.sum_univ {M : Type*} [AddCommMonoid M] (f : Msg → M) :
    ∑ m, f m = f .A + f .B + f .X + f .AorB + f .AorX + f .BorX + f .AorBorX + f .null := by
  rw [Fintype.sum_equiv Msg.equivFin f (f ∘ Msg.equivFin.symm) fun m => by simp,
    Fin.sum_univ_eight]
  rfl

theorem Lex.sum_univ {M : Type*} [AddCommMonoid M] (f : Lex → M) :
    ∑ l, f l = f .base + f .excl + f .syn := by
  rw [Fintype.sum_equiv Lex.equivFin f (f ∘ Lex.equivFin.symm) fun l => by simp,
    Fin.sum_univ_three]
  rfl

/-! ### The Hurfordian context (§5.2, Figure 10) -/

private theorem bern {x a b : ℝ} (ha : a ≤ x) (hb : x ≤ b) (i j : ℕ) :
    0 ≤ (x - a) ^ i * (b - x) ^ j :=
  mul_nonneg (pow_nonneg (sub_nonneg.2 ha) i) (pow_nonneg (sub_nonneg.2 hb) j)

section Findings

variable {c : ℝ}

theorem l1_uncertainty (hc : 0 ≤ c) :
    (L1 2 c .AorX).fst.real {.w₂} < (L1 2 c .AorX).fst.real {.w₁} ∧
      (L1 2 c .AorX).fst.real {.w₁} < (L1 2 c .AorX).fst.real {.w₁₂} := by
  have hκ' := Real.exp_pos (-c)
  have hκ1' : Real.exp (-c) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 hc)
  simp +decide only [L1_fst_real_lt_iff, Lex.sum_univ, S1_real two_pos,
    Msg.sum_univ, l0r, costFactor, cost, neg_zero, Real.exp_zero, card_sem, semCard, ↓reduceIte,
    Real.rpow_two, Nat.cast_ofNat, Nat.cast_one, inv_one, one_pow, mul_one, zero_pow, zero_mul,
    add_zero, zero_add, zero_div]
  generalize Real.exp (-c) = κ at hκ' hκ1' ⊢
  constructor <;> field_simp <;> ring_nf
  · linarith [pow_pos hκ' 2, pow_pos hκ' 3]
  · linarith [bern hκ'.le hκ1' 4 0, bern hκ'.le hκ1' 3 1, bern hκ'.le hκ1' 2 2,
      bern hκ'.le hκ1' 1 3, bern hκ'.le hκ1' 0 4]

theorem l1_lexicon (hc : 0 ≤ c) :
    (L1 2 c .AorX).snd.real {.syn} < (L1 2 c .AorX).snd.real {.base} ∧
      (L1 2 c .AorX).snd.real {.base} < (L1 2 c .AorX).snd.real {.excl} := by
  have hκ' := Real.exp_pos (-c)
  have hκ1' : Real.exp (-c) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 hc)
  simp +decide only [L1_snd_real_lt_iff, World.sum_univ, S1_real two_pos,
    Msg.sum_univ, l0r, costFactor, cost, neg_zero, Real.exp_zero, card_sem, semCard, ↓reduceIte,
    Real.rpow_two, Nat.cast_ofNat, Nat.cast_one, inv_one, one_pow, mul_one, zero_pow, zero_mul,
    add_zero, zero_add, zero_div]
  generalize Real.exp (-c) = κ at hκ' hκ1' ⊢
  constructor <;> field_simp <;> ring_nf
  · linarith [bern hκ'.le hκ1' 3 0, bern hκ'.le hκ1' 2 1, bern hκ'.le hκ1' 1 2,
      bern hκ'.le hκ1' 0 3]
  · linarith [pow_pos hκ' 2, pow_pos hκ' 3]

theorem s1_disjunction_iff_uncertain (hc : 0 ≤ c) :
    (S1 2 c .excl .w₁₂).real {.A} < (S1 2 c .excl .w₁₂).real {.AorX} ∧
      (S1 2 c .excl .w₁₂).real {.X} < (S1 2 c .excl .w₁₂).real {.AorX} ∧
      (S1 2 c .excl .w₁).real {.AorX} < (S1 2 c .excl .w₁).real {.A} := by
  have hκ' := Real.exp_pos (-c)
  have hκ1' : Real.exp (-c) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 hc)
  simp +decide only [S1_real two_pos, Msg.sum_univ, l0r, costFactor, cost, neg_zero,
    Real.exp_zero, card_sem, semCard, ↓reduceIte, Real.rpow_two, Nat.cast_ofNat, Nat.cast_one,
    inv_one, one_pow, mul_one, zero_pow, zero_mul, add_zero, zero_add, zero_div]
  refine ⟨by positivity, by positivity, ?_⟩
  generalize Real.exp (-c) = κ at hκ' hκ1' ⊢
  field_simp
  ring_nf
  linarith

theorem AorX_signals_excl (hc : Real.log 2 ≤ c) :
    (L1 2 c .A).snd.real {.excl} < (L1 2 c .AorX).snd.real {.excl} := by
  have hκ' := Real.exp_pos (-c)
  have hκ2' : Real.exp (-c) ≤ 1 / 2 :=
    (Real.exp_le_exp.2 (neg_le_neg hc)).trans_eq
      (by rw [Real.exp_neg, Real.exp_log two_pos, one_div])
  simp +decide only [L1_snd_real, Fintype.sum_prod_type, World.sum_univ,
    Lex.sum_univ, S1_real two_pos, Msg.sum_univ, l0r, costFactor, cost, neg_zero, Real.exp_zero,
    card_sem, semCard, ↓reduceIte, Real.rpow_two, Nat.cast_ofNat, Nat.cast_one, inv_one, one_pow,
    mul_one, zero_pow, zero_mul, add_zero, zero_add, zero_div]
  generalize Real.exp (-c) = κ at hκ' hκ2' ⊢
  field_simp
  ring_nf
  linarith [bern hκ'.le hκ2' 6 0, bern hκ'.le hκ2' 5 1, bern hκ'.le hκ2' 4 2, bern hκ'.le hκ2' 3 3,
    bern hκ'.le hκ2' 2 4, bern hκ'.le hκ2' 1 5, bern hκ'.le hκ2' 0 6]

/-- At a disjunction cost between 0 and `log 10`, the expertise speaker who observes the
uncertain state with the exclusivized lexicon prefers *A or X* to every other message, the
paper's production claim for the context. -/
theorem s2_prefers_disjunction (hc0 : 0 ≤ c) (hc10 : c ≤ Real.log 10) (m : Msg) (hm : m ≠ .AorX) :
    (S2 2 1 c (.w₁₂, .excl)).real {m} < (S2 2 1 c (.w₁₂, .excl)).real {.AorX} := by
  have hκ' := Real.exp_pos (-c)
  have hκ10' : 1 / 10 ≤ Real.exp (-c) :=
    (Real.exp_le_exp.2 (neg_le_neg hc10)).trans_eq'
      (by rw [Real.exp_neg, Real.exp_log (by norm_num), one_div])
  have hκ1' : Real.exp (-c) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 hc0)
  rw [S2_real_lt_iff two_pos zero_le_one]
  cases m
  case AorX => exact absurd rfl hm
  all_goals
    simp +decide only [l1_real, L1_snd_real, Fintype.sum_prod_type,
      World.sum_univ, Lex.sum_univ, Real.rpow_one, S1_real two_pos, Msg.sum_univ, l0r,
      costFactor, cost, neg_zero, Real.exp_zero, card_sem, semCard, ↓reduceIte, Real.rpow_two,
      Nat.cast_ofNat, Nat.cast_one, inv_one, one_pow, mul_one, zero_pow, zero_mul, add_zero,
      zero_add, zero_div]
  case A => positivity
  case B => positivity
  case X => positivity
  case BorX => positivity
  case AorB =>
    generalize Real.exp (-c) = κ at hκ' hκ10' hκ1' ⊢
    field_simp
    ring_nf
    linarith [bern hκ10' hκ1' 5 0, bern hκ10' hκ1' 4 1, bern hκ10' hκ1' 3 2, bern hκ10' hκ1' 2 3,
      bern hκ10' hκ1' 1 4, bern hκ10' hκ1' 0 5]
  case AorBorX =>
    generalize Real.exp (-c) = κ at hκ' hκ10' hκ1' ⊢
    field_simp
    ring_nf
    linarith [bern hκ10' hκ1' 5 0, bern hκ10' hκ1' 4 1, bern hκ10' hκ1' 3 2, bern hκ10' hκ1' 2 3,
      bern hκ10' hκ1' 1 4, bern hκ10' hκ1' 0 5]
  case null =>
    generalize Real.exp (-c) = κ at hκ' hκ10' hκ1' ⊢
    field_simp
    ring_nf
    linarith [bern hκ10' hκ1' 10 0, bern hκ10' hκ1' 9 1, bern hκ10' hκ1' 8 2, bern hκ10' hκ1' 7 3,
      bern hκ10' hκ1' 6 4, bern hκ10' hκ1' 5 5, bern hκ10' hκ1' 4 6, bern hκ10' hκ1' 3 7,
      bern hκ10' hκ1' 2 8, bern hκ10' hκ1' 1 9, bern hκ10' hκ1' 0 10]

theorem s2exp_uncertain : S2exp 2 1 c .w₁₂ {.A} = 0 ∧ S2exp 2 1 c .w₁₂ {.AorX} ≠ 0 := by
  refine ⟨?_, ?_⟩
  · simp only [S2exp, sum_apply, smul_apply, Measure.finsetSum_apply, Measure.smul_apply,
      smul_eq_mul]
    exact Finset.sum_eq_zero fun l _ => by
      rw [Kernel.comap_apply', S2_apply_eq_zero two_pos (by cases l <;> decide), mul_zero]
  · simp only [S2exp, sum_apply, smul_apply, Measure.finsetSum_apply, Measure.smul_apply,
      smul_eq_mul, ne_eq, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies, mul_eq_zero,
      not_forall, not_or]
    exact ⟨.excl, uniformOn_univ_singleton_ne_zero _, by
      rw [Kernel.comap_apply']
      exact Kernel.ofWeights_apply_singleton_ne_zero
        (S2_weight_ne_zero two_pos (by decide))
        (S2_weight_ne_top two_pos zero_le_one _)⟩

end Findings

end PottsLevy2015
