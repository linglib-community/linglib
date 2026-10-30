module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Linglib.Core.Order.Argmax
public import Linglib.Core.Probability.Decision.Admissible
public import Linglib.Data.Examples.Jaeger2014
public import Studies.Franke2011
public import Linglib.Data.Examples.Readers

/-!
# Jäger (2014): Rationalizable Signaling

Jäger models pragmatic interpretation in a semantic game, a signaling game whose signals have
literal meanings and whose players may be unsure of each other's preferences. Starting from the
credulous receiver, each player in turn plays a best response to some belief that gives every
strategy the other might currently play positive weight, an unexpected signal being read as
true; the strategies that recur arbitrarily late are pragmatically rationalizable, the notion
Jäger and Ebert also develop, and they are rationalizable in the classical sense
(`prs_rationalizable`). Worked examples derive the scalar implicature of "some", Horn's division
of pragmatic labor, the context-dependent precision of round numbers and the breakdown of
communication under opposed interests, and contrast the model with Franke's iterated best
response.

## Implementation notes

* Beliefs are points of mathlib's `Convexity.StdSimplex`; the paper's distributions over a set
  `P` of strategies, all of them or only those positive on all of `P`, are the beliefs whose
  support is contained in, respectively equal to, `P`.
* The iterated cautious response sequence is an iterate of `receiverStep` and the pragmatically
  rationalizable strategies are its limit superior; `mem_prsR_iff` is the paper's definition,
  which prints `s` for `r` in its receiver half.
* A signal or an action that some alternative weakly dominates against every strategy the other
  player might play is never a cautious response (`senderCR_subset`, `receiverCR_subset`). This is
  the sound half of the note on computing the sequence, which goes on to compute cautious responses
  separately at each context and world. Since one belief serves all of them, that computation can
  overcount: with one context, receivers `f ↦ a₁, f' ↦ a₂` and `f ↦ a₂, f' ↦ a₁`, the sender wanting
  `a₁` in `w₁` and `a₂` in `w₂`, and `f'` costing `0.2`, sending `f'` is optimal in `w₁` only if the
  first receiver has weight at most `0.4` and in `w₂` only if it has weight at least `0.6`. The
  stages displayed for Example 5 overcount in this way. With one context, a sender strategy that no
  mixture weakly dominates in ex-ante payoff is a cautious response
  (`mem_senderCR_of_not_weaklyDominated`), by Pearce's lemma.
* The examples are set in `Fin n`, the `k`-th world, signal or action of the paper being
  `k - 1`; each example's docstring names its signals.
* Section 3 asserts that under the right panel of Table 4 alone Sally would use "some but not
  all" when not all is true and never use "some", so that the implicature needs the other
  context. Under the definitions the unused "some" may be read as not-all after a belief revision,
  and two rounds later it carries the implicature
  (`NoImplicatureContext.some_still_implicates_not_all`). Table 8 swaps Table 4's context labels.
* The recurrence sets displayed for Example 2 are products, which by the paper's convention for
  such tables contain every strategy; the sequence cycles through two stages and the pragmatically
  rationalizable strategies are their union (`Opposed.prs_eq`).
* The stages displayed for Example 8 move away from the credulous ones, but the receiver's belief
  about the sender's context has full support, so "100 m" stays read as `100 m` and the sequence
  never moves; "exactly 100 m" is never used (`Precision.exactly_never_used`). The paper's verbal
  conclusions hold.
* Table 14 labels the last sender set of its left panel `S₀`; it is `S₁`.
* Example 10's "some but not all" costs a parameter `c` with `0 < c < 1`, the paper saying only
  that the cost is small. Franke's iterated best response is his costless light system
  (`Franke2011.receiverChain`), which agrees with the paper's costly variant when `c < 1/2`.

## TODO

* Examples 1, 3, 5 and 7, the uniform-prior variant of Example 6 in Section 6, and the notions of
  credibility of Section 7. Example 7 contrasts the model with weak bidirectional optimality,
  which the library has in `Pragmatics/Bidirectional.lean`.

## References

* [jaeger-2014]
* [jaeger-ebert-2009]
* [pearce-1984]
* [horn-1984]
* [franke-2011]
-/

@[expose] public section

namespace Jaeger2014

open Filter Convexity Function

noncomputable section

/-! ### Beliefs -/

section Beliefs

variable {M : Type*} [Fintype M] {ρ : StdSimplex ℝ M} {X Y : M → ℝ}

private theorem sum_weights_mul_le (h : ∀ x ∈ ρ.weights.support, X x ≤ Y x) :
    ∑ x, ρ.weights x * X x ≤ ∑ x, ρ.weights x * Y x := by
  refine Finset.sum_le_sum fun x _ ↦ ?_
  by_cases hx : x ∈ ρ.weights.support
  · exact mul_le_mul_of_nonneg_left (h x hx) (ρ.weights_nonneg x)
  · simp [Finsupp.notMem_support_iff.1 hx]

private theorem sum_weights_mul_lt (h : ∀ x ∈ ρ.weights.support, X x ≤ Y x)
    (hlt : ∃ x ∈ ρ.weights.support, X x < Y x) :
    ∑ x, ρ.weights x * X x < ∑ x, ρ.weights x * Y x := by
  obtain ⟨x₀, hx₀, hlt⟩ := hlt
  refine Finset.sum_lt_sum (fun x _ ↦ ?_) ⟨x₀, Finset.mem_univ _, ?_⟩
  · by_cases hx : x ∈ ρ.weights.support
    · exact mul_le_mul_of_nonneg_left (h x hx) (ρ.weights_nonneg x)
    · simp [Finsupp.notMem_support_iff.1 hx]
  · exact mul_lt_mul_of_pos_left hlt
      (lt_of_le_of_ne (ρ.weights_nonneg x₀) (Ne.symm (Finsupp.mem_support_iff.1 hx₀)))

private theorem sum_weights_mul_const (a : ℝ) : ∑ x, ρ.weights x * a = a := by
  rw [← Finset.sum_mul, ρ.total_of_fintype, one_mul]

private theorem exists_weights_eq {p : M → ℝ} (h0 : ∀ x, 0 ≤ p x) (h1 : ∑ x, p x = 1) :
    ∃ ρ : StdSimplex ℝ M, ⇑ρ.weights = p := by
  have : p ∈ Set.range fun t : StdSimplex ℝ M ↦ ⇑t.weights := by
    rw [StdSimplex.range_toFun_comp_weights]; exact ⟨Set.mem_iInter.2 h0, h1⟩
  exact this

private theorem exists_coe_support_eq {P : Set M} (hP : P.Nonempty) :
    ∃ ρ : StdSimplex ℝ M, ↑ρ.weights.support = P := by
  classical
  set s := Finset.univ.filter (· ∈ P)
  have hs : 0 < (s.card : ℝ) := by
    obtain ⟨x, hx⟩ := hP
    exact Nat.cast_pos.2 (Finset.card_pos.2 ⟨x, by simpa [s] using hx⟩)
  obtain ⟨ρ, hρ⟩ := exists_weights_eq (p := fun x ↦ if x ∈ P then 1 / s.card else 0)
    (fun x ↦ by split_ifs <;> positivity)
    (by rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]; exact mul_one_div_cancel hs.ne')
  refine ⟨ρ, Set.ext fun x ↦ ?_⟩
  rw [Finset.mem_coe, Finsupp.mem_support_iff, hρ]
  simp [hs.ne']

variable {a b : M}

omit [Fintype M] in
private theorem coe_support_eq_singleton :
    (ρ.weights.support : Set M) = {a} ↔ ρ = .single a := by
  rw [Finset.coe_eq_singleton, StdSimplex.support_weights_eq_singleton]

omit [Fintype M] in
private theorem coe_support_duple (hab : a ≠ b) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (h : s + t = 1) : ((StdSimplex.duple a b hs.le ht.le h).weights.support : Set M) = {a, b} := by
  ext x
  by_cases hxa : x = a
  · subst hxa; simp [hab, hs.ne']
  · by_cases hxb : x = b
    · subst hxb; simp [Ne.symm hab, ht.ne']
    · simp [hxa, hxb]

omit [Fintype M] in
private theorem weights_pos_of_coe_support_eq_pair (hρ : (ρ.weights.support : Set M) = {a, b}) :
    0 < ρ.weights a ∧ 0 < ρ.weights b := by
  have h := fun x (hx : x ∈ ({a, b} : Set M)) ↦
    lt_of_le_of_ne (ρ.weights_nonneg x) (Ne.symm (Finsupp.mem_support_iff.1 (by
      rw [← Finset.mem_coe, hρ]; exact hx)))
  exact ⟨h a (by simp), h b (by simp)⟩

private theorem sum_map_weights_mul {N : Type*} [Fintype N] (μ : StdSimplex ℝ M) (e : M → N)
    (X : N → ℝ) : ∑ y, (μ.map e).weights y * X y = ∑ x, μ.weights x * X (e x) := by
  rw [← Finsupp.sum_fintype _ (fun y m ↦ m * X y) (by simp),
    ← Finsupp.sum_fintype _ (fun x m ↦ m * X (e x)) (by simp)]
  exact Finsupp.sum_mapDomain_index (by simp) fun _ _ _ ↦ add_mul _ _ _

omit [Fintype M] in
private theorem coe_support_map {N : Type*} [DecidableEq N] {e : M → N} (he : Injective e)
    (μ : StdSimplex ℝ M) : ↑(μ.map e).weights.support = e '' ↑μ.weights.support := by
  rw [show (μ.map e).weights = μ.weights.mapDomain e from rfl,
    Finsupp.mapDomain_support_of_injective he, Finset.coe_image]

variable [DecidableEq M]

private theorem sum_single_mul (X : M → ℝ) :
    ∑ x, (StdSimplex.single a : StdSimplex ℝ M).weights x * X x = X a := by
  simp [Finsupp.single_apply]

private theorem sum_duple_mul {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (X : M → ℝ) :
    ∑ x, (StdSimplex.duple a b hs ht h).weights x * X x = s * X a + t * X b := by
  simp [add_mul, Finset.sum_add_distrib, Finsupp.single_apply]

private theorem sum_mul_of_coe_support_eq_pair (hab : a ≠ b)
    (hρ : (ρ.weights.support : Set M) = {a, b}) (X : M → ℝ) :
    ∑ x, ρ.weights x * X x = ρ.weights a * X a + ρ.weights b * X b := by
  rw [← Finset.sum_subset (Finset.subset_univ {a, b}) fun x _ hx ↦ ?_, Finset.sum_pair hab]
  rw [Finsupp.notMem_support_iff.1 fun h ↦ hx (by simpa using (Set.ext_iff.1 hρ x).1 h), zero_mul]

private theorem weights_add_of_coe_support_eq_pair (hab : a ≠ b)
    (hρ : (ρ.weights.support : Set M) = {a, b}) : ρ.weights a + ρ.weights b = 1 := by
  simpa using (sum_mul_of_coe_support_eq_pair hab hρ fun _ ↦ 1).symm.trans
    (sum_weights_mul_const 1)

end Beliefs

/-! ### Recurrence in a periodic sequence of sets -/

section Periodic

variable {α : Type*} {u : ℕ → Set α} {n p : ℕ}

private theorem add_mul_of_periodic (h : ∀ m ≥ n, u (m + p) = u m) {m : ℕ} (hm : n ≤ m)
    (k : ℕ) : u (m + p * k) = u m := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← add_assoc, h _ (by omega), ih]

private theorem frequently_mem_of_periodic (hp : 0 < p) (h : ∀ m ≥ n, u (m + p) = u m)
    {m : ℕ} (hm : n ≤ m) {x : α} (hx : x ∈ u m) : ∃ᶠ k in atTop, x ∈ u k :=
  frequently_atTop.2 fun N ↦ ⟨m + p * N, by nlinarith, (add_mul_of_periodic h hm N).symm ▸ hx⟩

private theorem limsup_eq_iUnion_of_periodic (hp : 0 < p) (h : ∀ m ≥ n, u (m + p) = u m) :
    limsup u atTop = ⋃ i < p, u (i + n) := by
  ext x
  rw [mem_limsup_iff_frequently_mem, Set.mem_iUnion₂]
  constructor
  · intro hx
    obtain ⟨k, hk, hxk⟩ := frequently_atTop.1 hx n
    refine ⟨(k - n) % p, Nat.mod_lt _ hp, ?_⟩
    have := add_mul_of_periodic h (m := (k - n) % p + n) (by omega) ((k - n) / p)
    rwa [← this, show (k - n) % p + n + p * ((k - n) / p) = k by
      have := Nat.mod_add_div (k - n) p; omega]
  · rintro ⟨i, -, hi⟩
    exact frequently_mem_of_periodic hp h (by omega) hi

end Periodic

/-! ### Semantic games -/

/-- A semantic game has contexts `C`, which carry each player's uncertainty about the other's
preferences, worlds `W`, signals `F` and actions `A`. It has a full-support prior over worlds, a
literal meaning for each signal, receiver utilities, and sender utilities that subtract a signal
cost from an outcome utility. -/
structure SemanticGame (C W F A : Type*) [Fintype W] where
  /-- The receiver's prior over worlds. -/
  prior : StdSimplex ℝ W
  /-- Every world has positive prior probability. -/
  prior_support : prior.weights.support = Finset.univ
  /-- Whether signal `f` is literally true at world `w`. -/
  meaning : F → W → Prop
  /-- The sender's utility of an outcome, by her context, the world and the receiver's action. -/
  vS : C → W → A → ℝ
  /-- The cost of sending a signal. -/
  cost : F → ℝ
  /-- The receiver's utility, by his context, the world and his action. -/
  uR : C → W → A → ℝ
  [meaningDecidable : ∀ f, DecidablePred (meaning f)]

attribute [instance] SemanticGame.meaningDecidable

namespace SemanticGame

variable {C W F A : Type*} [Fintype C] [Fintype W] [Fintype F] [Fintype A]
  [DecidableEq C] [DecidableEq W] [DecidableEq F] (g : SemanticGame C W F A)

/-- The sender's utility, the outcome utility less the signal's cost. -/
def uS (c : C) (w : W) (f : F) (a : A) : ℝ := g.vS c w a - g.cost f

/-- The worlds at which a signal is literally true. -/
def extension (f : F) : Finset W := Finset.univ.filter (g.meaning f)

/-- The actions optimal for the receiver in context `c` when he updates the belief `p` with the
proposition `φ` (Definition 1). -/
def optimalActions (c : C) (φ : Finset W) (p : StdSimplex ℝ W) : Finset A :=
  Finset.univ.argmax fun a ↦ ∑ w ∈ φ, p.weights w * g.uR c w a

/-! ### Best responses and cautious responses

A sender strategy maps a context and a world to a signal, a receiver strategy a context and a
signal to an action. A player's belief combines a belief about the other's strategy with one
about the other's context. -/

/-- The receiver's best responses to a belief about the sender's strategy and context maximize
expected utility under the prior in each of his contexts (Definition 2). -/
def receiverBR (σ : StdSimplex ℝ (C → W → F)) (q : StdSimplex ℝ C) : Set (C → F → A) :=
  {r' | ∀ c, r' ∈ Finset.univ.argmax fun r : C → F → A ↦
    ∑ s, σ.weights s * ∑ c', q.weights c' * ∑ w, g.prior.weights w * g.uR c w (r c (s c' w))}

/-- The sender's best responses to a belief about the receiver's strategy and context maximize
expected utility in each context and world (Definition 2). -/
def senderBR (ρ : StdSimplex ℝ (C → F → A)) (q : StdSimplex ℝ C) : Set (C → W → F) :=
  {s' | ∀ c w, s' ∈ Finset.univ.argmax fun s : C → W → F ↦
    ∑ r, ρ.weights r * ∑ c', q.weights c' * g.uS c w (s c w) (r c' (s c w))}

/-- The sender's cautious responses to a set of receiver strategies, the best responses to a
belief whose support is exactly that set, with every receiver context possible
(Definition 3). -/
def senderCR (R : Set (C → F → A)) : Set (C → W → F) :=
  {s | ∃ ρ q, ↑ρ.weights.support = R ∧ q.weights.support = Finset.univ ∧ s ∈ g.senderBR ρ q}

/-- The receiver's cautious responses to a set of sender strategies (Definition 3). -/
def receiverCR (S : Set (C → W → F)) : Set (C → F → A) :=
  {r | ∃ σ q, ↑σ.weights.support = S ∧ q.weights.support = Finset.univ ∧ r ∈ g.receiverBR σ q}

/-! ### The iterated cautious response sequence -/

omit [Fintype C] [Fintype W] [Fintype F] [DecidableEq C] [DecidableEq W] [DecidableEq F] in
/-- A signal is unexpected under a set of sender strategies if none of them ever sends it. -/
def Unexpected (S : Set (C → W → F)) (f : F) : Prop :=
  f ∉ ⋃ s ∈ S, Set.range (uncurry s)

omit [Fintype C] [Fintype W] [Fintype F] [DecidableEq C] [DecidableEq W] [DecidableEq F] in
theorem unexpected_iff {S : Set (C → W → F)} {f : F} :
    Unexpected S f ↔ ∀ s ∈ S, ∀ c w, s c w ≠ f := by
  simp [Unexpected]

/-- The credulous receiver strategies, optimal under the prior updated with each signal's
literal meaning. -/
def credulous : Set (C → F → A) :=
  {r | ∀ c f, r c f ∈ g.optimalActions c (g.extension f) g.prior}

/-- One step of the sequence keeps the receiver's cautious responses to the sender's cautious
responses to `R` that read every unexpected signal as literally true under some full-support
revised belief. -/
def receiverStep (R : Set (C → F → A)) : Set (C → F → A) :=
  {r ∈ g.receiverCR (g.senderCR R) | ∀ f, Unexpected (g.senderCR R) f →
    ∀ c, ∃ p : StdSimplex ℝ W, p.weights.support = Finset.univ ∧
      r c f ∈ g.optimalActions c (g.extension f) p}

/-- The receiver stages of the iterated cautious response sequence (Definition 4). -/
def icrR (n : ℕ) : Set (C → F → A) := g.receiverStep^[n] g.credulous

/-- The sender stages, the cautious responses to the receiver stages (Definition 4). -/
def icrS (n : ℕ) : Set (C → W → F) := g.senderCR (g.icrR n)

theorem icrR_succ (n : ℕ) : g.icrR (n + 1) = g.receiverStep (g.icrR n) :=
  iterate_succ_apply' _ _ _

/-- The pragmatically rationalizable sender strategies, those recurring arbitrarily late in the
sequence (Definition 5). -/
def prsS : Set (C → W → F) := limsup g.icrS atTop

/-- The pragmatically rationalizable receiver strategies (Definition 5). -/
def prsR : Set (C → F → A) := limsup g.icrR atTop

theorem mem_prsS_iff {s : C → W → F} : s ∈ g.prsS ↔ ∀ n, ∃ m > n, s ∈ g.icrS m := by
  rw [prsS, mem_limsup_iff_frequently_mem, frequently_atTop']

theorem mem_prsR_iff {r : C → F → A} : r ∈ g.prsR ↔ ∀ n, ∃ m > n, r ∈ g.icrR m := by
  rw [prsR, mem_limsup_iff_frequently_mem, frequently_atTop']

private theorem icrR_add_of_isPeriodicPt {n p : ℕ}
    (h : IsPeriodicPt g.receiverStep p (g.icrR n)) {m : ℕ} (hm : n ≤ m) :
    g.icrR (m + p) = g.icrR m := by
  have := congrArg (g.receiverStep^[m - n]) h.eq
  simp only [icrR, ← iterate_add_apply] at this
  rwa [show m - n + (p + n) = m + p by omega, Nat.sub_add_cancel hm] at this

theorem prsR_eq_of_isPeriodicPt {n p : ℕ} (hp : 0 < p)
    (h : IsPeriodicPt g.receiverStep p (g.icrR n)) : g.prsR = ⋃ i < p, g.icrR (i + n) :=
  limsup_eq_iUnion_of_periodic hp fun _ hm ↦ g.icrR_add_of_isPeriodicPt h hm

theorem prsS_eq_of_isPeriodicPt {n p : ℕ} (hp : 0 < p)
    (h : IsPeriodicPt g.receiverStep p (g.icrR n)) : g.prsS = ⋃ i < p, g.icrS (i + n) :=
  limsup_eq_iUnion_of_periodic hp fun _ hm ↦ by rw [icrS, g.icrR_add_of_isPeriodicPt h hm, icrS]

theorem prsR_eq_of_isFixedPt {n : ℕ} (h : IsFixedPt g.receiverStep (g.icrR n)) :
    g.prsR = g.icrR n := by
  simpa using g.prsR_eq_of_isPeriodicPt one_pos h

theorem prsS_eq_of_isFixedPt {n : ℕ} (h : IsFixedPt g.receiverStep (g.icrR n)) :
    g.prsS = g.icrS n := by
  simpa using g.prsS_eq_of_isPeriodicPt one_pos h

/-! ### Rationalizability -/

/-- A strategy pair is rationalizable if it lies in a pair of sets each of whose members is a best
response to some belief supported inside the other set (Definition 6, after Osborne). -/
def IsRationalizable (s : C → W → F) (r : C → F → A) : Prop :=
  ∃ (S : Set (C → W → F)) (R : Set (C → F → A)),
    (∀ s' ∈ S, ∃ ρ q, ↑ρ.weights.support ⊆ R ∧ s' ∈ g.senderBR ρ q) ∧
    (∀ r' ∈ R, ∃ σ q, ↑σ.weights.support ⊆ S ∧ r' ∈ g.receiverBR σ q) ∧
    s ∈ S ∧ r ∈ R

/-- Pragmatically rationalizable strategy pairs are rationalizable (Theorem 1). -/
theorem prs_rationalizable {s : C → W → F} {r : C → F → A}
    (hs : s ∈ g.prsS) (hr : r ∈ g.prsR) : g.IsRationalizable s r := by
  obtain ⟨a, b, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite g.icrR
  wlog hab : a < b generalizing a b
  · exact this b a hne.symm heq.symm (by omega)
  have hper : IsPeriodicPt g.receiverStep (b - a) (g.icrR a) := by
    simp only [IsPeriodicPt, IsFixedPt, icrR, ← iterate_add_apply]
    rw [Nat.sub_add_cancel hab.le]; exact heq.symm
  have hp : 0 < b - a := by omega
  have hR : ∀ m ≥ a, g.icrR m ⊆ g.prsR := fun m hm _ hx ↦ mem_limsup_iff_frequently_mem.2 <|
    frequently_mem_of_periodic hp (fun _ hk ↦ g.icrR_add_of_isPeriodicPt hper hk) hm hx
  have hS : ∀ m ≥ a, g.icrS m ⊆ g.prsS := fun m hm _ hx ↦ mem_limsup_iff_frequently_mem.2 <|
    frequently_mem_of_periodic hp (fun _ hk ↦ by
      rw [icrS, g.icrR_add_of_isPeriodicPt hper hk, icrS]) hm hx
  refine ⟨g.prsS, g.prsR, fun s' hs' ↦ ?_, fun r' hr' ↦ ?_, hs, hr⟩
  · obtain ⟨m, hm, ρ, q, hρ, -, hBR⟩ := (g.mem_prsS_iff.1 hs') a
    exact ⟨ρ, q, hρ ▸ hR m hm.le, hBR⟩
  · obtain ⟨m, hm, hr'm⟩ := (g.mem_prsR_iff.1 hr') a
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [icrR_succ] at hr'm
    obtain ⟨⟨σ, q, hσ, -, hBR⟩, -⟩ := hr'm
    exact ⟨σ, q, hσ ▸ hS k (by omega), hBR⟩

/-! ### Best responses, pointwise

Definition 2 maximizes over whole strategies, but the objectives separate: the sender's at a
context and world depends only on the signal sent there, and the receiver's is a sum over
signals. -/

variable {ρ : StdSimplex ℝ (C → F → A)} {σ : StdSimplex ℝ (C → W → F)} {q : StdSimplex ℝ C}

/-- The sender's expected utility of a signal in a context and world. -/
def senderEU (ρ : StdSimplex ℝ (C → F → A)) (q : StdSimplex ℝ C) (c : C) (w : W) (f : F) : ℝ :=
  ∑ r, ρ.weights r * ∑ c', q.weights c' * g.uS c w f (r c' f)

/-- The receiver's expected utility of an action on a signal, counting the occasions on which the
signal is sent. -/
def receiverEU (σ : StdSimplex ℝ (C → W → F)) (q : StdSimplex ℝ C) (c : C) (f : F) (a : A) : ℝ :=
  ∑ s, σ.weights s * ∑ c', q.weights c' *
    ∑ w, g.prior.weights w * if s c' w = f then g.uR c w a else 0

theorem mem_senderBR_iff {s : C → W → F} :
    s ∈ g.senderBR ρ q ↔ ∀ c w, s c w ∈ Finset.univ.argmax (g.senderEU ρ q c w) :=
  forall₂_congr fun c w ↦ Finset.mem_argmax_comp_surjective (e := fun s : C → W → F ↦ s c w)
    (fun f₀ ↦ ⟨fun _ _ ↦ f₀, rfl⟩) (g.senderEU ρ q c w)

omit [Fintype A] in
private theorem receiverBR_objective_eq (c : C) (r : C → F → A) :
    (∑ s, σ.weights s * ∑ c', q.weights c' * ∑ w, g.prior.weights w * g.uR c w (r c (s c' w))) =
      ∑ f, g.receiverEU σ q c f (r c f) := by
  unfold receiverEU
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  conv_rhs => rw [← Finset.mul_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ ↦ ?_
  conv_rhs => rw [← Finset.mul_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  conv_rhs => rw [← Finset.mul_sum]
  simp

theorem mem_receiverBR_iff {r : C → F → A} :
    r ∈ g.receiverBR σ q ↔ ∀ c f, r c f ∈ Finset.univ.argmax (g.receiverEU σ q c f) := by
  refine forall_congr' fun c ↦ ?_
  have : (fun r : C → F → A ↦ ∑ s, σ.weights s * ∑ c', q.weights c' *
      ∑ w, g.prior.weights w * g.uR c w (r c (s c' w))) =
      (fun ρ : F → A ↦ ∑ f, g.receiverEU σ q c f (ρ f)) ∘ fun r ↦ r c :=
    funext (g.receiverBR_objective_eq c)
  rw [this, Finset.mem_argmax_comp_surjective (fun ρ₀ ↦ ⟨fun _ ↦ ρ₀, rfl⟩),
    Finset.mem_argmax_pi_sum]

theorem mem_senderCR_iff {R : Set (C → F → A)} {s : C → W → F} :
    s ∈ g.senderCR R ↔ ∃ ρ q, ↑ρ.weights.support = R ∧ q.weights.support = Finset.univ ∧
      ∀ c w, s c w ∈ Finset.univ.argmax (g.senderEU ρ q c w) := by
  simp only [senderCR, Set.mem_ofPred_eq, mem_senderBR_iff]

theorem mem_receiverCR_iff {S : Set (C → W → F)} {r : C → F → A} :
    r ∈ g.receiverCR S ↔ ∃ σ q, ↑σ.weights.support = S ∧ q.weights.support = Finset.univ ∧
      ∀ c f, r c f ∈ Finset.univ.argmax (g.receiverEU σ q c f) := by
  simp only [receiverCR, Set.mem_ofPred_eq, mem_receiverBR_iff]

omit [DecidableEq W] in
theorem senderEU_single [DecidableEq A] (r₀ : C → F → A) (q : StdSimplex ℝ C) (c : C) (w : W)
    (f : F) : g.senderEU (.single r₀) q c w f = ∑ c', q.weights c' * g.uS c w f (r₀ c' f) :=
  sum_single_mul _

omit [Fintype A] in
theorem receiverEU_single (s₀ : C → W → F) (q : StdSimplex ℝ C) (c : C) (f : F) (a : A) :
    g.receiverEU (.single s₀) q c f a =
      ∑ c', q.weights c' * ∑ w, g.prior.weights w * if s₀ c' w = f then g.uR c w a else 0 :=
  sum_single_mul _

/-! ### Dominance

A signal that an alternative weakly dominates against every receiver strategy and context the
sender considers possible, strictly against one, earns less under every full-support belief, so
it is never a cautious response; symmetrically for the receiver's actions, compared at the
worlds where the signal is sent. -/

omit [DecidableEq W] in
theorem senderEU_le {c : C} {w : W} {f f' : F}
    (h : ∀ r ∈ ρ.weights.support, ∀ c' ∈ q.weights.support,
      g.uS c w f' (r c' f') ≤ g.uS c w f (r c' f)) :
    g.senderEU ρ q c w f' ≤ g.senderEU ρ q c w f :=
  sum_weights_mul_le fun r hr ↦ sum_weights_mul_le (h r hr)

omit [DecidableEq W] in
theorem senderEU_lt {c : C} {w : W} {f f' : F}
    (h : ∀ r ∈ ρ.weights.support, ∀ c' ∈ q.weights.support,
      g.uS c w f' (r c' f') ≤ g.uS c w f (r c' f))
    (hlt : ∃ r ∈ ρ.weights.support, ∃ c' ∈ q.weights.support,
      g.uS c w f' (r c' f') < g.uS c w f (r c' f)) :
    g.senderEU ρ q c w f' < g.senderEU ρ q c w f :=
  sum_weights_mul_lt (fun r hr ↦ sum_weights_mul_le (h r hr))
    (hlt.imp fun _ ⟨hr, hc⟩ ↦ ⟨hr, sum_weights_mul_lt (h _ hr) hc⟩)

omit [Fintype A] in
theorem receiverEU_le {c : C} {f : F} {a a' : A}
    (h : ∀ s ∈ σ.weights.support, ∀ c' ∈ q.weights.support, ∀ w, s c' w = f →
      g.uR c w a' ≤ g.uR c w a) :
    g.receiverEU σ q c f a' ≤ g.receiverEU σ q c f a :=
  sum_weights_mul_le fun s hs ↦ sum_weights_mul_le fun c' hc ↦ sum_weights_mul_le fun w _ ↦ by
    split_ifs with hw
    exacts [h s hs c' hc w hw, le_rfl]

omit [Fintype A] in
theorem receiverEU_lt {c : C} {f : F} {a a' : A}
    (h : ∀ s ∈ σ.weights.support, ∀ c' ∈ q.weights.support, ∀ w, s c' w = f →
      g.uR c w a' ≤ g.uR c w a)
    (hlt : ∃ s ∈ σ.weights.support, ∃ c' ∈ q.weights.support, ∃ w, s c' w = f ∧
      g.uR c w a' < g.uR c w a) :
    g.receiverEU σ q c f a' < g.receiverEU σ q c f a := by
  have hle : ∀ s ∈ σ.weights.support, ∀ c' ∈ q.weights.support, ∀ w,
      (if s c' w = f then g.uR c w a' else 0) ≤ if s c' w = f then g.uR c w a else 0 :=
    fun s hs c' hc w ↦ by split_ifs with hw; exacts [h s hs c' hc w hw, le_rfl]
  obtain ⟨s, hs, c', hc, w, hw, hlt⟩ := hlt
  refine sum_weights_mul_lt (fun s hs ↦ sum_weights_mul_le fun c' hc ↦
    sum_weights_mul_le fun w _ ↦ hle s hs c' hc w) ⟨s, hs, sum_weights_mul_lt
      (fun c' hc ↦ sum_weights_mul_le fun w _ ↦ hle s hs c' hc w) ⟨c', hc, ?_⟩⟩
  exact sum_weights_mul_lt (fun w _ ↦ hle s hs c' hc w)
    ⟨w, g.prior_support ▸ Finset.mem_univ w, by simpa [hw] using hlt⟩

theorem senderCR_subset {R : Set (C → F → A)} {T : C → W → Set F}
    (h : ∀ c w, ∀ f' ∉ T c w, ∃ f, (∀ r ∈ R, ∀ c', g.uS c w f' (r c' f') ≤ g.uS c w f (r c' f)) ∧
      ∃ r ∈ R, ∃ c', g.uS c w f' (r c' f') < g.uS c w f (r c' f)) :
    g.senderCR R ⊆ {s | ∀ c w, s c w ∈ T c w} := by
  rintro s ⟨ρ, q, hρ, hq, hBR⟩ c w
  by_contra hs
  obtain ⟨f, hle, r, hr, c', hlt⟩ := h c w _ hs
  have hρ' : ∀ r, r ∈ ρ.weights.support ↔ r ∈ R := fun r ↦ by rw [← hρ]; rfl
  have := (Finset.mem_argmax.1 ((g.mem_senderBR_iff.1 hBR) c w)).2 f (Finset.mem_univ _)
  exact absurd this (not_le.2 (g.senderEU_lt (fun r hr c' _ ↦ hle r ((hρ' r).1 hr) c')
    ⟨r, (hρ' r).2 hr, c', hq ▸ Finset.mem_univ _, hlt⟩))

theorem mem_senderCR [Nonempty C] {R : Set (C → F → A)} (hR : R.Nonempty) {s : C → W → F}
    (h : ∀ c w f', ∀ r ∈ R, ∀ c', g.uS c w f' (r c' f') ≤ g.uS c w (s c w) (r c' (s c w))) :
    s ∈ g.senderCR R := by
  obtain ⟨ρ, hρ⟩ := exists_coe_support_eq hR
  obtain ⟨q, hq⟩ := exists_coe_support_eq (Set.univ_nonempty (α := C))
  refine ⟨ρ, q, hρ, by simpa using hq, g.mem_senderBR_iff.2 fun c w ↦ Finset.mem_argmax.2
    ⟨Finset.mem_univ _, fun f' _ ↦ g.senderEU_le fun r hr c' _ ↦ h c w f' r ?_ c'⟩⟩
  rw [← hρ]; exact hr

/-- The ex-ante payoff of a sender strategy against a receiver strategy in a context is the
sender's utility at each world, weighted by the prior. -/
def senderPayoff (c : C) (s : C → W → F) (r : C → F → A) : ℝ :=
  ∑ w, g.prior.weights w * g.uS c w (s c w) (r c (s c w))

open MeasureTheory ProbabilityTheory in
theorem mem_senderCR_of_not_weaklyDominated [Unique C] {R : Set (C → F → A)} (hR : R.Nonempty)
    {s : C → W → F}
    (h : ∀ μ : StdSimplex ℝ (C → W → F),
      (∀ r ∈ R, g.senderPayoff default s r ≤ ∑ s', μ.weights s' * g.senderPayoff default s' r) →
        ∀ r ∈ R, ∑ s', μ.weights s' * g.senderPayoff default s' r = g.senderPayoff default s r) :
    s ∈ g.senderCR R := by
  classical
  let : MeasurableSpace (C → W → F) := ⊤
  let : MeasurableSpace R := ⊤
  have : Nonempty R := hR.to_subtype
  let U : (C → W → F) → R → ℝ := fun s' r ↦ g.senderPayoff default s' r
  have hdirac (x : C → W → F) (r : R) : mixedPayoff U (Measure.dirac x) r = U x r := by
    simp [mixedPayoff]
  have hnd : ¬ IsWeaklyPayoffDominated U (Measure.dirac s) := by
    rintro ⟨ν, hν, hle, r₀, hlt⟩
    obtain ⟨μ, hμ⟩ := exists_weights_eq (p := fun x ↦ ν.real {x}) (fun _ ↦ measureReal_nonneg)
      (sum_measureReal_singleton_eq_one ν)
    have hmix (r : R) : mixedPayoff U ν r = ∑ x, μ.weights x * g.senderPayoff default x r := by
      rw [mixedPayoff_eq_sum, hμ]
    have heq := h μ (fun r hr ↦ by simpa only [hdirac, hmix] using hle ⟨r, hr⟩) r₀ r₀.2
    rw [hdirac, hmix] at hlt
    exact absurd heq (ne_of_gt hlt)
  obtain ⟨P, hP, hP0, hmax⟩ :=
    (not_isWeaklyPayoffDominated_iff_exists_maximizesPayoff U (Measure.dirac s)).1 hnd
  have hsum (X : (C → F → A) → ℝ) :
      ∑ r, (if hr : r ∈ R then P.real {⟨r, hr⟩} else 0) * X r = ∑ r : R, P.real {r} * X r := by
    rw [← Fintype.sum_subtype_add_sum_subtype (· ∈ R)]
    simp [fun x : {r // r ∉ R} ↦ x.2]
  obtain ⟨ρ, hρ⟩ := exists_weights_eq (p := fun r ↦ if hr : r ∈ R then P.real {⟨r, hr⟩} else 0)
    (fun r ↦ by split_ifs <;> simp [measureReal_nonneg]) (by
      have := hsum fun _ ↦ 1
      simp only [mul_one] at this
      rw [this, sum_measureReal_singleton_eq_one])
  refine ⟨ρ, .single default, Set.ext fun r ↦ ?_, ?_, g.mem_senderBR_iff.2 fun c w ↦ ?_⟩
  · rw [Finset.mem_coe, Finsupp.mem_support_iff, hρ]
    by_cases hr : r ∈ R
    · simp only [hr, dite_true, ne_eq, iff_true]
      exact (ENNReal.toReal_pos (hP0 _) (measure_ne_top _ _)).ne'
    · simp [hr]
  · ext c; simp [Unique.eq_default c]
  obtain rfl : c = default := Unique.eq_default c
  refine Finset.mem_argmax.2 ⟨Finset.mem_univ _, fun f _ ↦ ?_⟩
  by_contra hlt
  have hEU (f' : F) : g.senderEU ρ (.single default) default w f' =
      ∑ r : R, P.real {r} * g.uS default w f' ((r : C → F → A) default f') := by
    simp only [senderEU, sum_single_mul, hρ]
    exact hsum _
  have hle := hmax (Measure.dirac (Function.update s default (Function.update (s default) w f)))
    inferInstance
  rw [expectedPayoff_eq_sum, expectedPayoff_eq_sum] at hle
  have hupd (r : C → F → A) :
      g.senderPayoff default (Function.update s default (Function.update (s default) w f)) r =
        g.senderPayoff default s r + g.prior.weights w * (g.uS default w f (r default f) -
          g.uS default w (s default w) (r default (s default w))) := by
    simp only [senderPayoff, Function.update_self]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ w), Function.update_self,
      Finset.sum_congr rfl fun w' hw' ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hw')]]
    ring
  simp only [hdirac, U, hupd, mul_add, Finset.sum_add_distrib] at hle
  have hpos : 0 < g.prior.weights w :=
    lt_of_le_of_ne (g.prior.weights_nonneg w) (Ne.symm (Finsupp.mem_support_iff.1
      (g.prior_support ▸ Finset.mem_univ w)))
  have key : ∑ r : R, P.real {r} * (g.prior.weights w *
      (g.uS default w f ((r : C → F → A) default f) -
        g.uS default w (s default w) ((r : C → F → A) default (s default w)))) =
      g.prior.weights w * (g.senderEU ρ (.single default) default w f -
        g.senderEU ρ (.single default) default w (s default w)) := by
    rw [hEU, hEU, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ ↦ by ring
  rw [key] at hle
  have := mul_pos hpos (sub_pos.2 (not_le.1 hlt))
  linarith

theorem receiverCR_subset {S : Set (C → W → F)} {T : C → F → Set A}
    (h : ∀ c f, ∀ a' ∉ T c f, ∃ a, (∀ s ∈ S, ∀ c' w, s c' w = f → g.uR c w a' ≤ g.uR c w a) ∧
      ∃ s ∈ S, ∃ c' w, s c' w = f ∧ g.uR c w a' < g.uR c w a) :
    g.receiverCR S ⊆ {r | ∀ c f, r c f ∈ T c f} := by
  rintro r ⟨σ, q, hσ, hq, hBR⟩ c f
  by_contra hr
  obtain ⟨a, hle, s, hs, c', w, hw, hlt⟩ := h c f _ hr
  have hσ' : ∀ s, s ∈ σ.weights.support ↔ s ∈ S := fun s ↦ by rw [← hσ]; rfl
  have := (Finset.mem_argmax.1 ((g.mem_receiverBR_iff.1 hBR) c f)).2 a (Finset.mem_univ _)
  exact absurd this (not_le.2 (g.receiverEU_lt (fun s hs c' _ w ↦ hle s ((hσ' s).1 hs) c' w)
    ⟨s, (hσ' s).2 hs, c', hq ▸ Finset.mem_univ _, w, hw, hlt⟩))

theorem mem_receiverCR [Nonempty C] {S : Set (C → W → F)} (hS : S.Nonempty) {r : C → F → A}
    (h : ∀ c f a', ∀ s ∈ S, ∀ c' w, s c' w = f → g.uR c w a' ≤ g.uR c w (r c f)) :
    r ∈ g.receiverCR S := by
  obtain ⟨σ, hσ⟩ := exists_coe_support_eq hS
  obtain ⟨q, hq⟩ := exists_coe_support_eq (Set.univ_nonempty (α := C))
  refine ⟨σ, q, hσ, by simpa using hq, g.mem_receiverBR_iff.2 fun c f ↦ Finset.mem_argmax.2
    ⟨Finset.mem_univ _, fun a' _ ↦ g.receiverEU_le fun s hs c' _ w hw ↦ h c f a' s ?_ c' w hw⟩⟩
  rw [← hσ]; exact hs

theorem senderCR_eq [Nonempty C] {R : Set (C → F → A)} (hR : R.Nonempty) {T : C → W → Set F}
    (hle : ∀ c w, ∀ f ∈ T c w, ∀ f', ∀ r ∈ R, ∀ c',
      g.uS c w f' (r c' f') ≤ g.uS c w f (r c' f))
    (hlt : ∀ c w, ∀ f' ∉ T c w, ∃ f ∈ T c w, ∃ r ∈ R, ∃ c',
      g.uS c w f' (r c' f') < g.uS c w f (r c' f)) :
    g.senderCR R = {s | ∀ c w, s c w ∈ T c w} :=
  Set.Subset.antisymm (g.senderCR_subset fun c w f' hf' ↦
      (hlt c w f' hf').imp fun f ⟨hf, hr⟩ ↦ ⟨hle c w f hf f', hr⟩)
    fun _ hs ↦ g.mem_senderCR hR fun c w f' ↦ hle c w _ (hs c w) f'

theorem receiverCR_eq [Nonempty C] {S : Set (C → W → F)} (hS : S.Nonempty) {T : C → F → Set A}
    (hle : ∀ c f, ∀ a ∈ T c f, ∀ a', ∀ s ∈ S, ∀ c' w, s c' w = f → g.uR c w a' ≤ g.uR c w a)
    (hlt : ∀ c f, ∀ a' ∉ T c f, ∃ a ∈ T c f, ∃ s ∈ S, ∃ c' w, s c' w = f ∧
      g.uR c w a' < g.uR c w a) :
    g.receiverCR S = {r | ∀ c f, r c f ∈ T c f} :=
  Set.Subset.antisymm (g.receiverCR_subset fun c f a' ha' ↦
      (hlt c f a' ha').imp fun a ⟨ha, hs⟩ ↦ ⟨hle c f a ha a', hs⟩)
    fun _ hr ↦ g.mem_receiverCR hS fun c f a' ↦ hle c f _ (hr c f) a'

omit [Fintype C] [Fintype F] [DecidableEq C] [DecidableEq W] [DecidableEq F] in
theorem optimalActions_eq_of_extension_eq_singleton {f : F} {w : W} (hf : g.extension f = {w})
    (c : C) {p : StdSimplex ℝ W} (hp : p.weights.support = Finset.univ) :
    g.optimalActions c (g.extension f) p = Finset.univ.argmax (g.uR c w) := by
  have hw : 0 < p.weights w := lt_of_le_of_ne (p.weights_nonneg w)
    (Ne.symm (Finsupp.mem_support_iff.1 (hp ▸ Finset.mem_univ w)))
  simp only [optimalActions, hf, Finset.sum_singleton]
  exact Finset.argmax_comp_strictMono (s := Finset.univ) (f := g.uR c w)
    (strictMono_mul_left_of_pos hw)

end SemanticGame

/-! ### Examples -/

private theorem sum_unit_weights_mul (q : StdSimplex ℝ Unit) (X : Unit → ℝ) :
    ∑ c, q.weights c * X c = X () := by
  simp

private theorem coe_support_duple_eq_univ {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    (StdSimplex.duple (0 : Fin 2) 1 h0.le (sub_pos.2 h1).le (add_sub_cancel x 1)).weights.support
      = Finset.univ := by
  rw [← Finset.coe_inj, coe_support_duple (by decide) h0 (sub_pos.2 h1)]
  ext w; fin_cases w <;> simp

/-- The data rows annotated with a signal and a world of a model, as pairs of the model's
indices, looked up by the paper's names. -/
def annotations {n m : ℕ} (signals : List (String × Fin n)) (worlds : List (String × Fin m)) :
    List (Fin n × Fin m) :=
  Examples.all.filterMap fun e ↦ do
    let f ← signals.lookup (← e.feature? "signal")
    let w ← worlds.lookup (← e.feature? "world")
    pure (f, w)

/-- The literal meanings of the paper's three signals over two worlds, `f₁` (`0`) true at `w₁`
(`0`), `f₂` (`1`) at `w₂` (`1`) and `f₁₂` (`2`) at both. -/
def literalMeaning (f : Fin 3) (w : Fin 2) : Prop := f = 2 ∨ f.val = w.val

instance (f : Fin 3) : DecidablePred (literalMeaning f) := fun _ ↦ by
  unfold literalMeaning; infer_instance

/-- The uniform prior over two worlds. -/
def uniform : StdSimplex ℝ (Fin 2) :=
  .duple 0 1 (s := 1/2) (t := 1/2) (by norm_num) (by norm_num) (by norm_num)

theorem uniform_support : uniform.weights.support = Finset.univ := by
  rw [← Finset.coe_inj, uniform, coe_support_duple (by decide) (by norm_num) (by norm_num)]
  ext w; fin_cases w <;> simp


/-! ### The scalar games of Section 3 and Example 4 -/

/-- In the scalar games of Section 3 the speaker says "all" (`0`), "some but not all" (`1`, which
costs `2`) or "some" (`2`), in the world where all is true (`0`) or the other (`1`), and the
hearer acts on either world or hedges (`2`), which pays `hedge c` in context `c`. Both players
have the same payoffs. -/
def scalarGame {C : Type*} (hedge : C → ℝ) : SemanticGame C (Fin 2) (Fin 3) (Fin 3) where
  prior := uniform
  prior_support := uniform_support
  meaning := literalMeaning
  vS c w a := if a = 2 then hedge c else if a.val = w.val then 10 else 0
  cost f := if f = 1 then 2 else 0
  uR c w a := if a = 2 then hedge c else if a.val = w.val then 10 else 0


/-! ### Example 2: opposed interests -/

namespace Opposed

/-- Example 2 pairs the opposed utilities of Table 6 with Example 1's signals `f₁`, `f₂`, `f₁₂`. -/
def game : SemanticGame Unit (Fin 2) (Fin 3) (Fin 2) where
  prior := uniform
  prior_support := uniform_support
  meaning := literalMeaning
  vS _ w a := if w = a then 1 else -1
  cost _ := 0
  uR _ w a := if w = a then -1 else 1

attribute [local simp] literalMeaning uniform
  Finsupp.single_apply Fin.sum_univ_two Finset.sum_filter

/-- The two stages of the cycle are the credulous reading `f₁ ↦ a₂`, `f₂ ↦ a₁` and its inverse,
with `f₁₂` read either way. -/
private def Stage (b : Fin 2) : Set (Unit → Fin 3 → Fin 2) := {r | r () 0 = b + 1 ∧ r () 1 = b}

private def liar (b : Fin 2) : Unit → Fin 2 → Fin 3 := fun _ w ↦ if w = b then 1 else 0

private theorem optimalActions_eq (u : Unit) (p : StdSimplex ℝ (Fin 2))
    (hp : p.weights.support = Finset.univ) (f : Fin 3) (hf : f ≠ 2) :
    game.optimalActions u (game.extension f) p = {if f = 0 then 1 else 0} := by
  have hext : game.extension f = {if f = 0 then 0 else 1} := by
    ext w; fin_cases f <;> fin_cases w <;> simp_all [SemanticGame.extension, game]
  rw [game.optimalActions_eq_of_extension_eq_singleton hext u hp, Finset.argmax_eq_singleton_iff]
  refine ⟨Finset.mem_univ _, fun b _ hb ↦ ?_⟩
  fin_cases f <;> fin_cases b <;> simp_all [game]

private theorem icrR_zero : game.icrR 0 = Stage 0 := by
  ext r
  simp only [SemanticGame.icrR, iterate_zero, id, SemanticGame.credulous, Set.mem_ofPred_eq,
    Stage]
  constructor
  · intro h
    exact ⟨by simpa [optimalActions_eq () _ game.prior_support 0 (by decide)] using h () 0,
      by simpa [optimalActions_eq () _ game.prior_support 1 (by decide)] using h () 1⟩
  · rintro ⟨h0, h1⟩ u f
    cases u
    by_cases hf : f = 2
    · subst hf
      exact Finset.mem_argmax.2 ⟨Finset.mem_univ _, fun b _ ↦ by
        fin_cases b <;> generalize r () 2 = a <;> fin_cases a <;>
          simp [SemanticGame.extension, game]⟩
    · rw [optimalActions_eq () _ game.prior_support f hf]
      fin_cases f <;> simp_all

private theorem stage_nonempty (b : Fin 2) : (Stage b).Nonempty :=
  ⟨fun _ f ↦ if f = 0 then b + 1 else b, by simp [Stage]⟩

private theorem senderCR_stage (b : Fin 2) : game.senderCR (Stage b) = {liar b} := by
  rw [game.senderCR_eq (stage_nonempty b) (T := fun u w ↦ {liar b u w})]
  · ext s; simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun h ↦ funext fun u ↦ funext (h u), fun h u w ↦ h ▸ rfl⟩
  · rintro u w f rfl f' r ⟨h0, h1⟩ c'
    cases c'
    fin_cases b <;> fin_cases w <;> fin_cases f' <;> simp_all [game, SemanticGame.uS, liar] <;>
      generalize r () 2 = a <;> fin_cases a <;> simp
  · intro u w f' hf'
    refine ⟨liar b u w, rfl, fun _ f ↦ if f = 0 then b + 1 else if f = 1 then b else w + 1, by
      simp [Stage], (), ?_⟩
    fin_cases b <;> fin_cases w <;> fin_cases f' <;> simp_all [game, SemanticGame.uS, liar]

private theorem f₁₂_witness (a : Fin 2) : ∃ p : StdSimplex ℝ (Fin 2),
    p.weights.support = Finset.univ ∧ a ∈ game.optimalActions () (game.extension 2) p := by
  have key : ∀ x : ℝ, ∀ (h0 : 0 < x) (h1 : x < 1),
      (StdSimplex.duple (0 : Fin 2) 1 h0.le (sub_pos.2 h1).le (add_sub_cancel x 1)).weights.support
        = Finset.univ := fun x h0 h1 ↦ by
    rw [← Finset.coe_inj, coe_support_duple (by decide) h0 (sub_pos.2 h1)]
    ext w; fin_cases w <;> simp
  fin_cases a
  · refine ⟨_, key (1/3) (by norm_num) (by norm_num), ?_⟩
    simp [SemanticGame.optimalActions, SemanticGame.extension, game, Fin.forall_fin_two]; norm_num
  · refine ⟨_, key (2/3) (by norm_num) (by norm_num), ?_⟩
    simp [SemanticGame.optimalActions, SemanticGame.extension, game, Fin.forall_fin_two]; norm_num

private theorem receiverStep_stage (b : Fin 2) : game.receiverStep (Stage b) = Stage (b + 1) := by
  rw [SemanticGame.receiverStep, senderCR_stage,
    game.receiverCR_eq (Set.singleton_nonempty _)
      (T := fun u f ↦ if f = 2 then Set.univ else {if f = 0 then b else b + 1})]
  · ext r
    simp only [Set.mem_ofPred_eq, SemanticGame.unexpected_iff, Stage]
    constructor
    · rintro ⟨h, -⟩
      have h0 := h () 0
      have h1 := h () 1
      fin_cases b <;> exact ⟨by simpa using h0, by simpa using h1⟩
    · rintro ⟨h0, h1⟩
      refine ⟨fun u f ↦ ?_, fun f hf u ↦ ?_⟩
      · cases u; fin_cases b <;> fin_cases f <;> simp_all
      · by_cases hf2 : f = 2
        · subst hf2; cases u; exact f₁₂_witness _
        · exact absurd (hf (liar b) rfl () (if f = 0 then b + 1 else b) (by
            fin_cases b <;> fin_cases f <;> simp_all [liar])) (by simp)
  · intro u f a ha a' s hs u' w hw
    rw [Set.mem_singleton_iff.1 hs] at hw
    by_cases hf2 : f = 2
    · subst hf2; fin_cases b <;> fin_cases w <;> simp [liar] at hw
    · simp only [hf2, ite_false, Set.mem_singleton_iff] at ha
      subst ha
      fin_cases b <;> fin_cases w <;> fin_cases f <;> fin_cases a' <;> simp_all [game, liar]
  · intro u f a' ha'
    by_cases hf2 : f = 2
    · simp [hf2] at ha'
    · simp only [hf2, ite_false, Set.mem_singleton_iff] at ha'
      refine ⟨if f = 0 then b else b + 1, by simp [hf2], liar b, rfl, (),
        if f = 0 then b + 1 else b, by fin_cases b <;> fin_cases f <;> simp_all [liar], ?_⟩
      fin_cases b <;> fin_cases f <;> fin_cases a' <;> simp_all [game]

/-- With opposed interests (Example 2), the pragmatically rationalizable senders are the liar and
truth-teller, and the receivers those reading `f₁` and `f₂` differently. -/
theorem prs_eq : game.prsS = {fun _ w ↦ if w = 0 then 1 else 0, fun _ w ↦ if w = 1 then 1 else 0} ∧
    game.prsR = {r | r () 0 ≠ r () 1} := by
  have h2 : IsPeriodicPt game.receiverStep 2 (game.icrR 0) := by
    simp only [IsPeriodicPt, IsFixedPt, iterate_succ, iterate_zero, 
      Function.comp_apply, icrR_zero, receiverStep_stage]
    rfl
  have h1 : game.icrR 1 = Stage 1 := by
    rw [SemanticGame.icrR_succ, icrR_zero, receiverStep_stage]; rfl
  have hi : ∀ {α : Type} (X : ℕ → Set α), (⋃ i < 2, X (i + 0)) = X 0 ∪ X 1 := fun X ↦ by
    ext x
    simp only [Set.mem_iUnion₂, Set.mem_union, exists_prop, add_zero]
    constructor
    · rintro ⟨i, hi, hx⟩
      obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      exacts [Or.inl hx, Or.inr hx]
    · rintro (hx | hx)
      exacts [⟨0, by norm_num, hx⟩, ⟨1, by norm_num, hx⟩]
  refine ⟨?_, ?_⟩
  · rw [game.prsS_eq_of_isPeriodicPt two_pos h2, hi, SemanticGame.icrS, SemanticGame.icrS,
      icrR_zero, h1, senderCR_stage, senderCR_stage]
    rfl
  · rw [game.prsR_eq_of_isPeriodicPt two_pos h2, hi, icrR_zero, h1]
    ext r
    simp only [Stage, Set.mem_union, Set.mem_ofPred_eq]
    generalize r () 0 = x
    generalize r () 1 = y
    fin_cases x <;> fin_cases y <;> decide

end Opposed


/-! ### Section 3: the no-implicature context alone -/

namespace NoImplicatureContext

/-- The right panel of Table 4 on its own, where the hedge pays `6`. -/
def game : SemanticGame Unit (Fin 2) (Fin 3) (Fin 3) := scalarGame fun _ ↦ 6

attribute [local simp] scalarGame literalMeaning uniform SemanticGame.uS
  Finsupp.single_apply Fin.sum_univ_two Finset.sum_filter

private theorem optimalActions_prior (c : Unit) (f : Fin 3) :
    game.optimalActions c (game.extension f) game.prior = {f} := by
  rw [SemanticGame.optimalActions, Finset.argmax_eq_singleton_iff]
  refine ⟨Finset.mem_univ _, fun b _ hb ↦ ?_⟩
  fin_cases f <;> fin_cases b <;>
    simp_all [SemanticGame.extension, game] <;> norm_num

private theorem icrR_zero : game.icrR 0 = {fun _ f ↦ f} := by
  ext r
  simp only [SemanticGame.icrR, iterate_zero, id, SemanticGame.credulous, Set.mem_ofPred_eq,
    Set.mem_singleton_iff, optimalActions_prior, Finset.mem_singleton]
  exact ⟨fun hr ↦ funext fun c ↦ funext (hr c), fun hr c f ↦ by subst hr; rfl⟩

private theorem icrS_zero : game.icrS 0 = {fun _ w ↦ Fin.castSucc w} := by
  rw [SemanticGame.icrS, icrR_zero]
  apply Set.Subset.antisymm
  · intro s hs
    have h := game.senderCR_subset (R := {fun _ f ↦ f}) (T := fun _ w ↦ {Fin.castSucc w})
      (fun c w f' hf' ↦ ⟨Fin.castSucc w, fun r hr c' ↦ by
        rw [Set.mem_singleton_iff.1 hr]
        fin_cases w <;> fin_cases f' <;> simp [game] <;> norm_num,
        fun _ f ↦ f, rfl, (), by
          fin_cases w <;> fin_cases f' <;> simp_all [game] <;> norm_num⟩) hs
    exact funext fun c ↦ funext fun w ↦ h c w
  · rintro s rfl
    refine game.mem_senderCR (Set.singleton_nonempty _) fun c w f' r hr c' ↦ ?_
    rw [Set.mem_singleton_iff.1 hr]
    fin_cases w <;> fin_cases f' <;> simp [game] <;> norm_num

private theorem icrS_zero' : game.senderCR {fun _ f ↦ f} = {fun _ w ↦ Fin.castSucc w} :=
  icrR_zero ▸ icrS_zero

/-- The receivers reading "all" and "some but not all" literally and "some" as `a`. -/
private def reading (a : Fin 3) : Unit → Fin 3 → Fin 3 := fun _ f ↦ if f = 2 then a else f

private theorem reading_injective : Injective reading := fun a b h ↦ by
  simpa [reading] using congrFun (congrFun h ()) 2

private theorem range_reading : Set.range reading = {r | r () 0 = 0 ∧ r () 1 = 1} := by
  ext r
  constructor
  · rintro ⟨a, rfl⟩; simp [reading]
  · rintro ⟨h0, h1⟩
    refine ⟨r () 2, funext fun c ↦ funext fun f ↦ ?_⟩
    cases c; fin_cases f <;> simp [reading, h0, h1]

private theorem coe_support_duple_eq_univ {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    (StdSimplex.duple (0 : Fin 2) 1 h0.le (sub_pos.2 h1).le (add_sub_cancel x 1)).weights.support
      = Finset.univ := by
  rw [← Finset.coe_inj, coe_support_duple (by decide) h0 (sub_pos.2 h1)]
  ext w; fin_cases w <;> simp

private theorem some_witness (a : Fin 3) : ∃ p : StdSimplex ℝ (Fin 2),
    p.weights.support = Finset.univ ∧ a ∈ game.optimalActions () (game.extension 2) p := by
  obtain ⟨x, h0, h1, hx⟩ : ∃ x : ℝ, ∃ (h0 : 0 < x) (h1 : x < 1),
      a ∈ game.optimalActions () (game.extension 2)
        (.duple 0 1 h0.le (sub_pos.2 h1).le (add_sub_cancel x 1)) := by
    fin_cases a
    · exact ⟨7/10, by norm_num, by norm_num, by
        simp [SemanticGame.optimalActions, SemanticGame.extension, game,
          Fin.forall_fin_succ]; norm_num⟩
    · exact ⟨3/10, by norm_num, by norm_num, by
        simp [SemanticGame.optimalActions, SemanticGame.extension, game,
          Fin.forall_fin_succ]; norm_num⟩
    · exact ⟨1/2, by norm_num, by norm_num, by
        simp [SemanticGame.optimalActions, SemanticGame.extension, game,
          Fin.forall_fin_succ]; norm_num⟩
  exact ⟨_, coe_support_duple_eq_univ h0 h1, hx⟩

private theorem icrR_one : game.icrR 1 = Set.range reading := by
  rw [SemanticGame.icrR_succ, icrR_zero, SemanticGame.receiverStep, icrS_zero', range_reading]
  ext r
  constructor
  · rintro ⟨hr, -⟩
    have h := game.receiverCR_subset (S := {fun _ w ↦ Fin.castSucc w})
      (T := fun _ f ↦ if f = 2 then Set.univ else {f}) (fun c f a' ha' ↦ ⟨f, fun s hs c' w hw ↦ by
        rw [Set.mem_singleton_iff.1 hs] at hw
        subst hw; fin_cases w <;> fin_cases a' <;> simp [game] <;> norm_num, by
        refine ⟨_, rfl, (), ?_⟩
        fin_cases f <;> simp at ha'
        · exact ⟨0, rfl, by fin_cases a' <;> simp_all [game]; norm_num⟩
        · exact ⟨1, rfl, by fin_cases a' <;> simp_all [game]; norm_num⟩⟩) hr
    exact ⟨by simpa using h () 0, by simpa using h () 1⟩
  · rintro ⟨h0, h1⟩
    refine ⟨game.mem_receiverCR (Set.singleton_nonempty _) fun c f a' s hs c' w hw ↦ ?_,
      fun f hf c ↦ ?_⟩
    · rw [Set.mem_singleton_iff.1 hs] at hw
      subst hw; cases c
      fin_cases w <;> fin_cases a' <;> simp [game, h0, h1] <;> norm_num
    · fin_cases f
      · exact (SemanticGame.unexpected_iff.1 hf _ rfl () 0 rfl).elim
      · exact (SemanticGame.unexpected_iff.1 hf _ rfl () 1 rfl).elim
      · cases c; exact some_witness _

private theorem exists_reading_belief {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 1) : ∃ ρ : StdSimplex ℝ (Unit → Fin 3 → Fin 3),
      ↑ρ.weights.support = Set.range reading ∧
      ∀ X : (Unit → Fin 3 → Fin 3) → ℝ,
        ∑ r, ρ.weights r * X r = x * X (reading 0) + y * X (reading 1) + z * X (reading 2) := by
  obtain ⟨μ, hμ⟩ := exists_weights_eq (p := ![x, y, z]) (fun a ↦ by
    fin_cases a <;> simp [hx.le, hy.le, hz.le]) (by simp [Fin.sum_univ_three, h])
  refine ⟨μ.map reading, ?_, fun X ↦ ?_⟩
  · rw [coe_support_map reading_injective, ← Set.image_univ]
    congr 1
    ext a; fin_cases a <;> simp [Finsupp.mem_support_iff, hμ, hx.ne', hy.ne', hz.ne']
  · rw [sum_map_weights_mul, Fin.sum_univ_three, hμ]; rfl

private theorem icrS_one : game.icrS 1 = {s | s () 0 = 0 ∧ s () 1 ≠ 0} := by
  rw [SemanticGame.icrS, icrR_one]
  ext s
  constructor
  · intro hs
    have h := game.senderCR_subset (R := Set.range reading)
      (T := fun _ w ↦ if w = 0 then {0} else {1, 2}) (fun c w f' hf' ↦ by
        fin_cases w
        · refine ⟨0, ?_, reading 1, ⟨1, rfl⟩, (), ?_⟩
          · rintro r ⟨a, rfl⟩ c'
            fin_cases f' <;> fin_cases a <;> simp [game, reading] <;> norm_num
          · fin_cases f' <;> simp_all [game, reading]; norm_num
        · refine ⟨1, ?_, reading 1, ⟨1, rfl⟩, (), ?_⟩
          · rintro r ⟨a, rfl⟩ c'
            fin_cases f' <;> simp_all [game, reading]; norm_num
          · fin_cases f' <;> simp_all [game, reading]; norm_num) hs
    refine ⟨by simpa using h () 0, fun h1 ↦ ?_⟩
    simpa [h1] using h () 1
  · rintro ⟨h0, h1⟩
    obtain ⟨x, y, z, hx, hy, hz, hsum, hpick⟩ : ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧
        x + y + z = 1 ∧ (s () 1 = 1 → y * 10 + z * 6 ≤ 8) ∧ (s () 1 = 2 → 8 ≤ y * 10 + z * 6) := by
      rcases (by omega : s () 1 = 1 ∨ s () 1 = 2) with h | h
      · exact ⟨1/3, 1/3, 1/3, by norm_num, by norm_num, by norm_num, by norm_num,
          fun _ ↦ by norm_num, fun h' ↦ absurd (h.symm.trans h') (by decide)⟩
      · exact ⟨1/10, 8/10, 1/10, by norm_num, by norm_num, by norm_num, by norm_num,
          fun h' ↦ absurd (h.symm.trans h') (by decide), fun _ ↦ by norm_num⟩
    obtain ⟨ρ, hρ, hsum'⟩ := exists_reading_belief hx hy hz hsum
    refine game.mem_senderCR_iff.2 ⟨ρ, .single (), hρ, by simp, fun c w ↦ ?_⟩
    cases c
    simp only [Finset.mem_argmax, Finset.mem_univ, true_and, SemanticGame.senderEU, hsum',
      sum_unit_weights_mul]
    intro f'
    fin_cases w <;> fin_cases f' <;> rcases (by omega : s () 1 = 1 ∨ s () 1 = 2) with h | h <;>
      simp_all [game, reading] <;> nlinarith

private theorem icrS_one' : game.senderCR (Set.range reading) = {s | s () 0 = 0 ∧ s () 1 ≠ 0} :=
  icrR_one ▸ icrS_one

private theorem icrR_two : game.icrR 2 = {reading 1} := by
  rw [SemanticGame.icrR_succ, icrR_one, SemanticGame.receiverStep, icrS_one']
  have hsa : (fun _ w ↦ Fin.castSucc w : Unit → Fin 2 → Fin 3) ∈
      {s : Unit → Fin 2 → Fin 3 | s () 0 = 0 ∧ s () 1 ≠ 0} := ⟨rfl, by decide⟩
  have hsb : (fun _ w ↦ if w = 0 then 0 else 2 : Unit → Fin 2 → Fin 3) ∈
      {s : Unit → Fin 2 → Fin 3 | s () 0 = 0 ∧ s () 1 ≠ 0} := ⟨rfl, by decide⟩
  ext r
  constructor
  · rintro ⟨hr, -⟩
    have h := game.receiverCR_subset (T := fun _ f ↦ {reading 1 () f}) (fun c f a' ha' ↦ by
      refine ⟨reading 1 () f, fun s hs c' w hw ↦ ?_, ?_⟩
      · obtain ⟨h0, h1⟩ := hs
        cases c'
        fin_cases w <;> fin_cases f <;> fin_cases a' <;> simp_all [game, reading] <;> norm_num
      · fin_cases f
        · exact ⟨_, hsa, (), 0, rfl, by fin_cases a' <;> simp_all [game, reading]; norm_num⟩
        · exact ⟨_, hsa, (), 1, rfl, by fin_cases a' <;> simp_all [game, reading]; norm_num⟩
        · exact ⟨_, hsb, (), 1, rfl, by fin_cases a' <;> simp_all [game, reading]; norm_num⟩) hr
    exact Set.mem_singleton_iff.2 (funext fun c ↦ funext fun f ↦ by simpa using h c f)
  · rintro rfl
    refine ⟨game.mem_receiverCR ⟨_, hsa⟩ fun c f a' s hs c' w hw ↦ ?_, fun f hf ↦ ?_⟩
    · obtain ⟨h0, h1⟩ := hs
      cases c'
      fin_cases w <;> fin_cases f <;> fin_cases a' <;> simp_all [game, reading] <;> norm_num
    · rw [SemanticGame.unexpected_iff] at hf
      fin_cases f
      · exact (hf _ hsa () 0 rfl).elim
      · exact (hf _ hsa () 1 rfl).elim
      · exact (hf _ hsb () 1 rfl).elim

private theorem icrS_two : game.icrS 2 = {fun _ w ↦ if w = 0 then 0 else 2} := by
  rw [SemanticGame.icrS, icrR_two]
  apply Set.Subset.antisymm
  · intro s hs
    have h := game.senderCR_subset (R := {reading 1})
      (T := fun _ w ↦ {if w = 0 then 0 else 2}) (fun c w f' hf' ↦ ⟨if w = 0 then 0 else 2,
        fun r hr c' ↦ by
          rw [Set.mem_singleton_iff.1 hr]
          fin_cases w <;> fin_cases f' <;> simp [game, reading]; norm_num,
        reading 1, rfl, (), by
          fin_cases w <;> fin_cases f' <;> simp_all [game, reading];
            norm_num⟩) hs
    exact funext fun c ↦ funext fun w ↦ h c w
  · rintro s rfl
    refine game.mem_senderCR (Set.singleton_nonempty _) fun c w f' r hr c' ↦ ?_
    rw [Set.mem_singleton_iff.1 hr]
    fin_cases w <;> fin_cases f' <;> simp [game, reading]; norm_num

private theorem icrS_two' :
    game.senderCR {reading 1} = {fun _ w ↦ if w = 0 then 0 else 2} :=
  icrR_two ▸ icrS_two

private theorem icrR_three : game.icrR 3 = game.icrR 2 := by
  rw [SemanticGame.icrR_succ, icrR_two, SemanticGame.receiverStep, icrS_two']
  have hs : (fun _ w ↦ if w = 0 then 0 else 2 : Unit → Fin 2 → Fin 3) ∈
      ({fun _ w ↦ if w = 0 then 0 else 2} : Set (Unit → Fin 2 → Fin 3)) := rfl
  ext r
  constructor
  · rintro ⟨hr, hsur⟩
    have h := game.receiverCR_subset (T := fun _ f ↦ if f = 1 then Set.univ else {reading 1 () f})
      (fun c f a' ha' ↦ by
        refine ⟨reading 1 () f, fun s hs c' w hw ↦ ?_, ?_⟩
        · rw [Set.mem_singleton_iff.1 hs] at hw
          cases c'
          fin_cases w <;> fin_cases f <;> fin_cases a' <;> simp_all [game, reading] <;> norm_num
        · fin_cases f
          · exact ⟨_, hs, (), 0, rfl, by fin_cases a' <;> simp_all [game, reading]; norm_num⟩
          · simp at ha'
          · exact ⟨_, hs, (), 1, rfl, by fin_cases a' <;> simp_all [game, reading]; norm_num⟩) hr
    obtain ⟨p, hp, hr1⟩ := hsur 1 (SemanticGame.unexpected_iff.2 fun s hs c w ↦ by
      rw [Set.mem_singleton_iff.1 hs]; fin_cases w <;> simp) ()
    have hp1 : 0 < p.weights 1 := lt_of_le_of_ne (p.weights_nonneg 1)
      (Ne.symm (Finsupp.mem_support_iff.1 (hp ▸ Finset.mem_univ 1)))
    have h1 : r () 1 = 1 := by
      have hmax := (Finset.mem_argmax.1 hr1).2 1 (Finset.mem_univ _)
      revert hmax
      generalize r () 1 = a
      intro hmax
      fin_cases a <;> simp_all [SemanticGame.extension, game] <;> nlinarith
    refine Set.mem_singleton_iff.2 (funext fun c ↦ funext fun f ↦ ?_)
    cases c
    fin_cases f
    · simpa using h () 0
    · simpa [reading] using h1
    · simpa using h () 2
  · rintro rfl
    refine ⟨game.mem_receiverCR ⟨_, hs⟩ fun c f a' s hs c' w hw ↦ ?_, fun f hf c ↦ ?_⟩
    · rw [Set.mem_singleton_iff.1 hs] at hw
      cases c'
      fin_cases w <;> fin_cases f <;> fin_cases a' <;> simp_all [game, reading] <;> norm_num
    · refine ⟨game.prior, game.prior_support, ?_⟩
      rw [SemanticGame.unexpected_iff] at hf
      fin_cases f
      · exact (hf _ hs () 0 rfl).elim
      · simp [SemanticGame.optimalActions, SemanticGame.extension, game, reading,
          Fin.forall_fin_succ]
        norm_num
      · exact (hf _ hs () 1 rfl).elim

/-- Contrary to p. 683, the no-implicature utilities yield the scalar implicature, the sender using
*some* exactly when not all holds. -/
theorem some_still_implicates_not_all :
    game.prsS = {fun _ w ↦ if w = 0 then 0 else 2} ∧
      game.prsR = {fun _ f ↦ if f = 2 then 1 else f} := by
  have h : IsFixedPt game.receiverStep (game.icrR 2) := by
    rw [IsFixedPt, ← SemanticGame.icrR_succ]; exact icrR_three
  exact ⟨(game.prsS_eq_of_isFixedPt h).trans icrS_two, (game.prsR_eq_of_isFixedPt h).trans icrR_two⟩

end NoImplicatureContext


/-! ### Example 4: the scalar implicature across two contexts -/

namespace Scalar

/-- Example 4 has two contexts, the hedge paying `6` in `0` and `9` in `1` (Table 8). -/
def game : SemanticGame (Fin 2) (Fin 2) (Fin 3) (Fin 3) :=
  scalarGame fun c ↦ if c = 0 then 6 else 9

attribute [local simp] scalarGame literalMeaning uniform SemanticGame.uS
  Finsupp.single_apply Fin.sum_univ_two Finset.sum_filter

private def s₀ : Fin 2 → Fin 2 → Fin 3 := fun c w ↦ if w = 0 then 0 else if c = 0 then 1 else 2
private def r₁ : Fin 2 → Fin 3 → Fin 3 := fun _ f ↦ if f = 0 then 0 else 1
private def s₁ : Fin 2 → Fin 2 → Fin 3 := fun _ w ↦ if w = 0 then 0 else 2

private theorem optimalActions_prior (c : Fin 2) (f : Fin 3) :
    game.optimalActions c (game.extension f) game.prior = {f} := by
  rw [SemanticGame.optimalActions, Finset.argmax_eq_singleton_iff]
  refine ⟨Finset.mem_univ _, fun b _ hb ↦ ?_⟩
  fin_cases c <;> fin_cases f <;> fin_cases b <;>
    simp_all [SemanticGame.extension, game] <;> norm_num

private theorem icrR_zero : game.icrR 0 = {fun _ f ↦ f} := by
  ext r
  simp only [SemanticGame.icrR, iterate_zero, id, SemanticGame.credulous, Set.mem_ofPred_eq,
    Set.mem_singleton_iff, optimalActions_prior, Finset.mem_singleton]
  exact ⟨fun hr ↦ funext fun c ↦ funext (hr c), fun hr c f ↦ by subst hr; rfl⟩

private theorem icrS_zero : game.senderCR {fun _ f ↦ f} = {s₀} := by
  rw [game.senderCR_eq (Set.singleton_nonempty _) (T := fun c w ↦ {s₀ c w})]
  · ext s; simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun h ↦ funext fun c ↦ funext (h c), fun h c w ↦ h ▸ rfl⟩
  · rintro c w f rfl f' r rfl c'
    fin_cases c <;> fin_cases w <;> fin_cases f' <;>
      simp [game, s₀] <;> norm_num
  · intro c w f' hf'
    refine ⟨s₀ c w, rfl, _, rfl, c, ?_⟩
    fin_cases c <;> fin_cases w <;> fin_cases f' <;>
      simp_all [game, s₀] <;> norm_num

private theorem receiverStep_zero : game.receiverStep {fun _ f ↦ f} = {r₁} := by
  rw [SemanticGame.receiverStep, icrS_zero,
    game.receiverCR_eq (Set.singleton_nonempty _) (T := fun c f ↦ {r₁ c f})]
  · ext r
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, SemanticGame.unexpected_iff]
    constructor
    · exact fun ⟨h, _⟩ ↦ funext fun c ↦ funext (h c)
    · rintro rfl
      refine ⟨fun c f ↦ rfl, fun f hf ↦ ?_⟩
      fin_cases f
      · exact (hf s₀ rfl 0 0 rfl).elim
      · exact (hf s₀ rfl 0 1 rfl).elim
      · exact (hf s₀ rfl 1 1 rfl).elim
  · rintro c f a rfl a' s rfl c' w hw
    fin_cases c <;> fin_cases c' <;> fin_cases w <;> fin_cases f <;> fin_cases a' <;>
      simp_all [game, r₁, s₀] <;> norm_num
  · intro c f a' ha'
    refine ⟨r₁ c f, rfl, s₀, rfl, ?_⟩
    fin_cases f
    · exact ⟨0, 0, rfl, by fin_cases c <;> fin_cases a' <;> simp_all [game, r₁] <;> norm_num⟩
    · exact ⟨0, 1, rfl, by fin_cases c <;> fin_cases a' <;> simp_all [game, r₁] <;> norm_num⟩
    · exact ⟨1, 1, rfl, by fin_cases c <;> fin_cases a' <;> simp_all [game, r₁] <;> norm_num⟩

private theorem icrS_one : game.senderCR {r₁} = {s₁} := by
  rw [game.senderCR_eq (Set.singleton_nonempty _) (T := fun c w ↦ {s₁ c w})]
  · ext s; simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun h ↦ funext fun c ↦ funext (h c), fun h c w ↦ h ▸ rfl⟩
  · rintro c w f rfl f' r rfl c'
    fin_cases c <;> fin_cases w <;> fin_cases f' <;>
      simp [game, s₁, r₁] <;> norm_num
  · intro c w f' hf'
    refine ⟨s₁ c w, rfl, _, rfl, c, ?_⟩
    fin_cases c <;> fin_cases w <;> fin_cases f' <;>
      simp_all [game, s₁, r₁] <;> norm_num

private theorem argmax_uR_one (c : Fin 2) : Finset.univ.argmax (game.uR c 1) = {1} := by
  rw [Finset.argmax_eq_singleton_iff]
  refine ⟨Finset.mem_univ _, fun b _ hb ↦ ?_⟩
  fin_cases c <;> fin_cases b <;> simp_all [game] <;> norm_num

private theorem receiverStep_one : game.receiverStep {r₁} = {r₁} := by
  rw [SemanticGame.receiverStep, icrS_one,
    game.receiverCR_eq (Set.singleton_nonempty _)
      (T := fun c f ↦ if f = 1 then Set.univ else {r₁ c f})]
  · have hext : game.extension 1 = {1} := by decide
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, SemanticGame.unexpected_iff]
    constructor
    · rintro ⟨h, hsur⟩
      refine funext fun c ↦ funext fun f ↦ ?_
      by_cases hf1 : f = 1
      · subst hf1
        obtain ⟨p, hp, hr⟩ := hsur 1 (fun s hs c' w ↦ by
          rw [hs]; fin_cases w <;> simp [s₁]) c
        rw [game.optimalActions_eq_of_extension_eq_singleton hext c hp, argmax_uR_one,
          Finset.mem_singleton] at hr
        simpa [r₁] using hr
      · simpa [hf1] using h c f
    · rintro rfl
      refine ⟨fun c f ↦ by split_ifs <;> simp, fun f hf c ↦ ⟨game.prior, game.prior_support, ?_⟩⟩
      fin_cases f
      · exact (hf s₁ rfl 0 0 rfl).elim
      · change r₁ c 1 ∈ game.optimalActions c (game.extension 1) game.prior
        rw [game.optimalActions_eq_of_extension_eq_singleton hext c game.prior_support,
          argmax_uR_one]
        simp [r₁]
      · exact (hf s₁ rfl 0 1 rfl).elim
  · intro c f a ha a' s hs c' w hw
    rw [Set.mem_singleton_iff.1 hs] at hw
    fin_cases f
    · simp only [r₁] at ha; subst ha
      fin_cases c <;> fin_cases w <;> fin_cases a' <;> simp_all [game, s₁] <;> norm_num
    · fin_cases c' <;> fin_cases w <;> simp [s₁] at hw
    · simp only [r₁] at ha; subst ha
      fin_cases c <;> fin_cases w <;> fin_cases a' <;> simp_all [game, s₁] <;> norm_num
  · intro c f a' ha'
    fin_cases f <;> simp at ha'
    · exact ⟨_, rfl, s₁, rfl, 0, 0, rfl, by
        fin_cases c <;> fin_cases a' <;> simp_all [game, r₁] <;> norm_num⟩
    · exact ⟨_, rfl, s₁, rfl, 0, 1, rfl, by
        fin_cases c <;> fin_cases a' <;> simp_all [game, r₁] <;> norm_num⟩

-- Example 4
theorem some_implicates_not_all : game.prsS = {fun _ w ↦ if w = 0 then 0 else 2} ∧
    game.prsR = {fun _ f ↦ if f = 0 then 0 else 1} := by
  have h1 : game.icrR 1 = {r₁} := by rw [SemanticGame.icrR_succ, icrR_zero, receiverStep_zero]
  have h : IsFixedPt game.receiverStep (game.icrR 1) := by
    rw [IsFixedPt, h1, receiverStep_one]
  refine ⟨(game.prsS_eq_of_isFixedPt h).trans ?_, (game.prsR_eq_of_isFixedPt h).trans h1⟩
  rw [SemanticGame.icrS, h1, icrS_one]; rfl

theorem some_boys_read_as_not_all :
    ∀ x ∈ annotations [("f1", 0), ("f2", 1), ("f12", 2)] [("w1", 0), ("w2", 1)],
      ∀ r ∈ game.prsR, ∀ c, r c x.1 = x.2 := by
  rw [some_implicates_not_all.2]
  rintro x hx r rfl c
  revert x c; decide

example :
    (annotations (n := 3) (m := 2) [("f1", 0), ("f2", 1), ("f12", 2)] [("w1", 0), ("w2", 1)])
      = [(2, 1)] := by decide

end Scalar


/-! ### Example 6: Horn's division of pragmatic labor -/

namespace Horn

def game : SemanticGame Unit (Fin 2) (Fin 2) (Fin 2) where
  prior := .duple 0 1 (s := 3/4) (t := 1/4) (by norm_num) (by norm_num) (by norm_num)
  prior_support := by ext w; fin_cases w <;> simp
  meaning _ _ := True
  vS _ w a := if w = a then 5 else 0
  cost f := if f = 0 then 0 else 1
  uR _ w a := if w = a then 5 else 0

attribute [local simp] SemanticGame.uS
  Finsupp.single_apply Fin.sum_univ_two Finset.sum_filter

private theorem zero_ne_id : (fun _ _ ↦ 0 : Unit → Fin 2 → Fin 2) ≠ fun _ x ↦ x := fun h ↦
  absurd (congrFun (congrFun h ()) 1) (by decide)

private theorem pair_eq :
    {h : Unit → Fin 2 → Fin 2 | h () 0 = 0} = {(fun _ _ ↦ 0), (fun _ x ↦ x)} := by
  ext h
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h0
    rcases (by omega : h () 1 = 0 ∨ h () 1 = 1) with h1 | h1
    · left; funext c x; cases c; fin_cases x <;> assumption
    · right; funext c x; cases c; fin_cases x <;> simp_all
  · rintro (rfl | rfl) <;> rfl

private theorem argmax_fin2_zero {V : Fin 2 → ℝ} (h : V 1 < V 0) :
    Finset.univ.argmax V = {0} := by
  ext x; fin_cases x <;> simp [Finset.mem_argmax, Fin.forall_fin_two] <;> linarith

private theorem argmax_fin2_one {V : Fin 2 → ℝ} (h : V 0 < V 1) :
    Finset.univ.argmax V = {1} := by
  ext x; fin_cases x <;> simp [Finset.mem_argmax, Fin.forall_fin_two] <;> linarith

private theorem argmax_fin2_univ {V : Fin 2 → ℝ} (h : V 0 = V 1) :
    Finset.univ.argmax V = Finset.univ := by
  ext x; fin_cases x <;> simp [Finset.mem_argmax, Fin.forall_fin_two, h.le, h.ge]

private theorem extension_eq (f : Fin 2) : game.extension f = Finset.univ := by
  simp [SemanticGame.extension, game]

private theorem icrR_zero : game.icrR 0 = {fun _ _ ↦ 0} := by
  have h : ∀ (c : Unit) (f : Fin 2),
      game.optimalActions c (game.extension f) game.prior = {0} := fun c f ↦ by
    rw [SemanticGame.optimalActions, extension_eq]
    exact argmax_fin2_zero (by simp [game]; norm_num)
  ext r
  simp only [SemanticGame.icrR, iterate_zero, id, SemanticGame.credulous, Set.mem_ofPred_eq,
    Set.mem_singleton_iff, h, Finset.mem_singleton]
  exact ⟨fun hr ↦ funext fun c ↦ funext (hr c), fun hr c f ↦ by subst hr; rfl⟩

private theorem icrS_zero : game.icrS 0 = {fun _ _ ↦ 0} := by
  have e : ∀ q w, Finset.univ.argmax (game.senderEU (.single fun _ _ ↦ 0) q () w) = {0} :=
    fun q w ↦ argmax_fin2_zero (by
      fin_cases w <;> simp [SemanticGame.senderEU_single, game])
  ext s
  rw [SemanticGame.icrS, icrR_zero, SemanticGame.mem_senderCR_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨ρ, q, hρ, -, hBR⟩
    rw [coe_support_eq_singleton] at hρ
    subst hρ
    funext c w; cases c
    simpa [e] using hBR () w
  · rintro rfl
    exact ⟨.single _, .single (), coe_support_eq_singleton.2 rfl, by simp,
      fun c w ↦ by cases c; simp [e]⟩

private theorem optimalActions_witness (x : Fin 2) :
    ∃ p : StdSimplex ℝ (Fin 2), p.weights.support = Finset.univ ∧
      x ∈ game.optimalActions () Finset.univ p := by
  have key : ∀ y : ℝ, ∀ (h0 : 0 < y) (h1 : y < 1),
      (StdSimplex.duple (0 : Fin 2) 1 h0.le (sub_pos.2 h1).le (add_sub_cancel y 1)).weights.support
        = Finset.univ := fun y h0 h1 ↦ by
    rw [← Finset.coe_inj, coe_support_duple (by decide) h0 (sub_pos.2 h1)]
    ext w; fin_cases w <;> simp
  fin_cases x
  · refine ⟨_, key (2/3) (by norm_num) (by norm_num), ?_⟩
    rw [SemanticGame.optimalActions, argmax_fin2_zero (by simp [game]; norm_num)]
    simp
  · refine ⟨_, key (1/3) (by norm_num) (by norm_num), ?_⟩
    rw [SemanticGame.optimalActions, argmax_fin2_one (by simp [game]; norm_num)]
    simp

private theorem icrR_one : game.icrR 1 = {r | r () 0 = 0} := by
  have e0 : ∀ q, Finset.univ.argmax
      (game.receiverEU (.single fun _ _ ↦ 0) q () 0) = {0} := fun q ↦
    argmax_fin2_zero (by simp [SemanticGame.receiverEU_single, game]; norm_num)
  have e1 : ∀ q, Finset.univ.argmax
      (game.receiverEU (.single fun _ _ ↦ 0) q () 1) = Finset.univ := fun q ↦
    argmax_fin2_univ (by simp [SemanticGame.receiverEU_single, game])
  ext r
  rw [SemanticGame.icrR_succ, icrR_zero, SemanticGame.receiverStep,
    show game.senderCR {fun _ _ ↦ 0} = {fun _ _ ↦ 0} from icrR_zero ▸ icrS_zero,
    Set.mem_ofPred_eq, Set.mem_ofPred_eq, SemanticGame.mem_receiverCR_iff]
  constructor
  · rintro ⟨⟨σ, q, hσ, -, hBR⟩, -⟩
    rw [coe_support_eq_singleton] at hσ
    subst hσ
    simpa [e0] using hBR () 0
  · intro hr
    refine ⟨⟨.single _, .single (), coe_support_eq_singleton.2 rfl, by simp, fun c ↦ ?_⟩,
      fun f _ c ↦ ?_⟩
    · cases c; rw [Fin.forall_fin_two]
      exact ⟨by rw [e0]; simp [hr], by rw [e1]; simp⟩
    · cases c; rw [extension_eq]; exact optimalActions_witness _

private theorem coe_support_mix {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    ↑(StdSimplex.duple (fun _ _ ↦ 0 : Unit → Fin 2 → Fin 2) (fun _ x ↦ x) h0.le
      (sub_pos.2 h1).le (add_sub_cancel t 1)).weights.support =
      {h : Unit → Fin 2 → Fin 2 | h () 0 = 0} :=
  (coe_support_duple zero_ne_id h0 (sub_pos.2 h1) _).trans pair_eq.symm

private theorem icrS_one : game.icrS 1 = {s | s () 0 = 0} := by
  rw [SemanticGame.icrS, icrR_one]
  ext s
  constructor
  · intro hs
    have h := game.senderCR_subset (R := {r | r () 0 = 0})
      (T := fun _ w ↦ if w = 0 then {0} else Set.univ) (fun c w f' hf' ↦ by
        fin_cases w
        · refine ⟨0, fun r hr c' ↦ ?_, fun _ x ↦ x, rfl, (), ?_⟩
          · simp only [Set.mem_ofPred_eq] at hr
            fin_cases f' <;> simp [game, hr];
              generalize r c' 1 = a; fin_cases a <;> simp; norm_num
          · fin_cases f' <;> simp_all [game]; norm_num
        · simp at hf') hs
    simpa using h () 0
  · intro hs
    obtain ⟨t, ht0, ht1, hpick⟩ : ∃ t : ℝ, 0 < t ∧ t < 1 ∧
        ((s () 1 = 0 → 4 - 5 * t ≤ 0) ∧ (s () 1 = 1 → 0 ≤ 4 - 5 * t)) := by
      rcases (by omega : s () 1 = 0 ∨ s () 1 = 1) with h | h
      · exact ⟨9/10, by norm_num, by norm_num, fun _ ↦ by norm_num,
          fun h' ↦ absurd (h.symm.trans h') (by decide)⟩
      · exact ⟨1/2, by norm_num, by norm_num, fun h' ↦ absurd (h.symm.trans h') (by decide),
          fun _ ↦ by norm_num⟩
    refine game.mem_senderCR_iff.2 ⟨_, .single (), coe_support_mix ht0 ht1, by simp,
      fun c w ↦ ?_⟩
    cases c
    simp only [Finset.mem_argmax, Finset.mem_univ, true_and, SemanticGame.senderEU,
      sum_duple_mul, sum_unit_weights_mul]
    intro f'
    simp only [Set.mem_ofPred_eq] at hs
    fin_cases w <;> fin_cases f' <;> rcases (by omega : s () 1 = 0 ∨ s () 1 = 1) with h | h <;>
      simp_all [game] <;> nlinarith

private theorem icrR_two : game.icrR 2 = {fun _ f ↦ f} := by
  have hS : game.senderCR (game.icrR 1) = {(fun _ _ ↦ 0), (fun _ x ↦ x)} := icrS_one.trans pair_eq
  ext r
  rw [SemanticGame.icrR_succ, SemanticGame.receiverStep, hS, Set.mem_ofPred_eq,
    SemanticGame.mem_receiverCR_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨σ, q, hσ, -, hBR⟩, -⟩
    have hpos := weights_pos_of_coe_support_eq_pair hσ
    have hsum := weights_add_of_coe_support_eq_pair zero_ne_id hσ
    have e : ∀ f a, game.receiverEU σ q () f a =
        σ.weights (fun _ _ ↦ 0) * ∑ w, game.prior.weights w *
          (if (0 : Fin 2) = f then game.uR () w a else 0) +
        σ.weights (fun _ x ↦ x) * ∑ w, game.prior.weights w *
          (if w = f then game.uR () w a else 0) := fun f a ↦ by
      rw [SemanticGame.receiverEU, sum_mul_of_coe_support_eq_pair zero_ne_id hσ]
      simp
    funext c f; cases c
    have h := Finset.mem_argmax.1 ((hBR ()) f)
    by_contra hne
    have := h.2 f (Finset.mem_univ _)
    revert this hne; generalize r () f = a; intro hne this
    fin_cases f <;> fin_cases a <;> simp_all [game] <;>
      nlinarith
  · rintro rfl
    obtain ⟨t, ht0, ht1⟩ : ∃ t : ℝ, 0 < t ∧ t < 1 := ⟨1/2, by norm_num, by norm_num⟩
    refine ⟨⟨_, .single (), (coe_support_duple zero_ne_id ht0 (sub_pos.2 ht1)
      (add_sub_cancel t 1)), by simp, fun c f ↦ ?_⟩, fun f hf c ↦ ?_⟩
    · cases c
      refine Finset.mem_argmax.2 ⟨Finset.mem_univ _, fun a _ ↦ ?_⟩
      simp only [SemanticGame.receiverEU, sum_duple_mul, sum_unit_weights_mul]
      fin_cases f <;> fin_cases a <;> simp [game] <;>
        nlinarith
    · exact absurd rfl (SemanticGame.unexpected_iff.1 hf (fun _ x ↦ x) (by simp) () f)

private theorem icrS_two : game.icrS 2 = {fun _ w ↦ w} := by
  rw [SemanticGame.icrS, icrR_two, game.senderCR_eq (Set.singleton_nonempty _)
    (T := fun _ w ↦ {w})]
  · ext s; simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun h ↦ funext fun c ↦ funext (h c), fun h c w ↦ h ▸ rfl⟩
  · intro c w f hf f' r hr c'
    rw [Set.mem_singleton_iff.1 hf, Set.mem_singleton_iff.1 hr]
    fin_cases w <;> fin_cases f' <;> simp [game]; norm_num
  · intro c w f' hf'
    refine ⟨w, rfl, _, rfl, (), ?_⟩
    fin_cases w <;> fin_cases f' <;> simp_all [game]; norm_num

private theorem icrR_three : game.icrR 3 = game.icrR 2 := by
  have hS : game.senderCR (game.icrR 2) = {fun _ w ↦ w} := icrS_two
  have hs : (fun _ w ↦ w : Unit → Fin 2 → Fin 2) ∈ ({fun _ w ↦ w} : Set _) := rfl
  rw [SemanticGame.icrR_succ, SemanticGame.receiverStep, hS, icrR_two,
    game.receiverCR_eq ⟨_, hs⟩ (T := fun _ f ↦ {f})]
  · ext r
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, SemanticGame.unexpected_iff]
    constructor
    · exact fun ⟨h, _⟩ ↦ funext fun c ↦ funext (h c)
    · rintro rfl
      exact ⟨fun _ _ ↦ rfl, fun f hf ↦ (hf _ rfl () f rfl).elim⟩
  · intro c f a ha a' s hs c' w hw
    rw [Set.mem_singleton_iff.1 hs] at hw
    rw [Set.mem_singleton_iff.1 ha]
    simp only at hw
    subst hw
    fin_cases w <;> fin_cases a' <;> simp [game]
  · intro c f a' ha'
    have : f ≠ a' := fun h ↦ ha' (h ▸ rfl)
    exact ⟨f, rfl, _, hs, (), f, rfl, by simp [game, this]⟩

-- Example 6
theorem division_of_pragmatic_labor :
    game.prsS = {fun _ w ↦ w} ∧ game.prsR = {fun _ f ↦ f} := by
  have h : IsFixedPt game.receiverStep (game.icrR 2) := by
    rw [IsFixedPt, ← SemanticGame.icrR_succ]; exact icrR_three
  exact ⟨(game.prsS_eq_of_isFixedPt h).trans icrS_two, (game.prsR_eq_of_isFixedPt h).trans icrR_two⟩

theorem stop_sentences_read_as_reported :
    ∀ x ∈ annotations [("f", 0), ("f'", 1)] [("w1", 0), ("w2", 1)],
      ∀ r ∈ game.prsR, r () x.1 = x.2 := by
  rw [division_of_pragmatic_labor.2]
  rintro x hx r rfl
  revert x; decide

example : (annotations (n := 2) (m := 2) [("f", 0), ("f'", 1)] [("w1", 0), ("w2", 1)]).length = 2 :=
  by decide

end Horn

/-! ### Example 8: precision of number words -/

namespace Precision

/-- In Example 8 the distance is `100 m` in `w₁` (`0`) and `101 m` in `w₂` (`1`). The signals are
"100 m" (`0`), "exactly 100 m" (`1`) and "101 m" (`2`), the last two costing `9/2`, and each
action suits one world, paying `10` when precision matters (context `0`) and `4` otherwise
(Table 12). -/
def game : SemanticGame (Fin 2) (Fin 2) (Fin 3) (Fin 2) where
  prior := uniform
  prior_support := uniform_support
  meaning f w := (f = 2 ∧ w = 1) ∨ (f ≠ 2 ∧ w = 0)
  vS c w a := if w = a then (if c = 0 then 10 else 4) else 0
  cost f := if f = 0 then 0 else 9 / 2
  uR c w a := if w = a then (if c = 0 then 10 else 4) else 0

attribute [local simp] uniform SemanticGame.uS
  Finsupp.single_apply Fin.sum_univ_two Finset.sum_filter

private def r₀ : Fin 2 → Fin 3 → Fin 2 := fun _ f ↦ if f = 2 then 1 else 0
private def s₀ : Fin 2 → Fin 2 → Fin 3 := fun c w ↦ if c = 0 ∧ w = 1 then 2 else 0

private theorem extension_eq (f : Fin 3) : game.extension f = {if f = 2 then 1 else 0} := by
  ext w; fin_cases f <;> fin_cases w <;> simp [SemanticGame.extension, game]

private theorem argmax_uR (c w : Fin 2) : Finset.univ.argmax (game.uR c w) = {w} := by
  rw [Finset.argmax_eq_singleton_iff]
  refine ⟨Finset.mem_univ _, fun b _ hb ↦ ?_⟩
  fin_cases c <;> fin_cases w <;> fin_cases b <;> simp_all [game]

private theorem optimalActions_eq (c : Fin 2) (f : Fin 3) {p : StdSimplex ℝ (Fin 2)}
    (hp : p.weights.support = Finset.univ) :
    game.optimalActions c (game.extension f) p = {if f = 2 then 1 else 0} := by
  rw [game.optimalActions_eq_of_extension_eq_singleton (extension_eq f) c hp, argmax_uR]

private theorem icrR_zero : game.icrR 0 = {r₀} := by
  ext r
  simp only [SemanticGame.icrR, iterate_zero, id, SemanticGame.credulous, Set.mem_ofPred_eq,
    Set.mem_singleton_iff, optimalActions_eq _ _ game.prior_support, Finset.mem_singleton]
  exact ⟨fun hr ↦ funext fun c ↦ funext (hr c), fun hr c f ↦ by subst hr; rfl⟩

private theorem icrS_zero : game.senderCR {r₀} = {s₀} := by
  rw [game.senderCR_eq (Set.singleton_nonempty _) (T := fun c w ↦ {s₀ c w})]
  · ext s; simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun h ↦ funext fun c ↦ funext (h c), fun h c w ↦ h ▸ rfl⟩
  · intro c w f hf f' r hr c'
    rw [Set.mem_singleton_iff.1 hf, Set.mem_singleton_iff.1 hr]
    fin_cases c <;> fin_cases w <;> fin_cases f' <;> simp [game, s₀, r₀] <;>
      norm_num
  · intro c w f' hf'
    refine ⟨s₀ c w, rfl, _, rfl, c, ?_⟩
    fin_cases c <;> fin_cases w <;> fin_cases f' <;>
      simp_all [game, s₀, r₀] <;> norm_num

private theorem receiverEU_zero (q : StdSimplex ℝ (Fin 2)) (c : Fin 2) (a : Fin 2) :
    game.receiverEU (.single s₀) q c 0 a =
      (q.weights 0 + q.weights 1) / 2 * game.uR c 0 a + q.weights 1 / 2 * game.uR c 1 a := by
  rw [SemanticGame.receiverEU_single]
  have := q.total_fin_two
  fin_cases c <;> fin_cases a <;> simp [game, s₀] <;>
    linarith

private theorem receiverEU_zero_lt {q : StdSimplex ℝ (Fin 2)} (hq0 : 0 < q.weights 0) (c : Fin 2) :
    game.receiverEU (.single s₀) q c 0 1 < game.receiverEU (.single s₀) q c 0 0 := by
  have := q.total_fin_two
  rw [receiverEU_zero, receiverEU_zero]
  fin_cases c <;> simp [game] <;> linarith

private theorem receiverEU_two_lt {q : StdSimplex ℝ (Fin 2)} (hq0 : 0 < q.weights 0) (c : Fin 2) :
    game.receiverEU (.single s₀) q c 2 0 < game.receiverEU (.single s₀) q c 2 1 := by
  rw [SemanticGame.receiverEU_single, SemanticGame.receiverEU_single]
  fin_cases c <;> simp [game, s₀] <;> linarith

private theorem receiverStep_zero : game.receiverStep {r₀} = {r₀} := by
  rw [SemanticGame.receiverStep, icrS_zero]
  ext r
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, SemanticGame.mem_receiverCR_iff,
    coe_support_eq_singleton]
  constructor
  · rintro ⟨⟨σ, q, rfl, hq, hBR⟩, hsur⟩
    have hq0 : 0 < q.weights 0 := lt_of_le_of_ne (q.weights_nonneg 0)
      (Ne.symm (Finsupp.mem_support_iff.1 (hq ▸ Finset.mem_univ 0)))
    have hsum := q.total_fin_two
    refine funext fun c ↦ funext fun f ↦ ?_
    obtain rfl | rfl | rfl : f = 0 ∨ f = 1 ∨ f = 2 := by omega
    · by_contra hne
      have h1 : r c 0 = 1 := by revert hne; generalize r c 0 = a; fin_cases a <;> simp [r₀]
      exact absurd ((Finset.mem_argmax.1 (hBR c 0)).2 0 (Finset.mem_univ _))
        (not_le.2 (h1 ▸ receiverEU_zero_lt hq0 c))
    · obtain ⟨p, hp, hr⟩ := hsur 1 (SemanticGame.unexpected_iff.2 fun s hs c' w ↦ by
        rw [Set.mem_singleton_iff.1 hs]; fin_cases c' <;> fin_cases w <;> simp [s₀]) c
      simpa [optimalActions_eq c 1 hp, r₀] using hr
    · by_contra hne
      have h0 : r c 2 = 0 := by revert hne; generalize r c 2 = a; fin_cases a <;> simp [r₀]
      exact absurd ((Finset.mem_argmax.1 (hBR c 2)).2 1 (Finset.mem_univ _))
        (not_le.2 (h0 ▸ receiverEU_two_lt hq0 c))
  · rintro rfl
    refine ⟨⟨.single s₀, uniform, rfl, uniform_support, fun c f ↦ ?_⟩, fun f hf c ↦
      ⟨game.prior, game.prior_support, by simp [optimalActions_eq c f game.prior_support, r₀]⟩⟩
    have hu : (0 : ℝ) < uniform.weights 0 := by simp
    refine Finset.mem_argmax.2 ⟨Finset.mem_univ _, fun a _ ↦ ?_⟩
    obtain rfl | rfl | rfl : f = 0 ∨ f = 1 ∨ f = 2 := by omega
    · fin_cases a
      · exact le_rfl
      · exact (receiverEU_zero_lt hu c).le
    · rw [SemanticGame.receiverEU_single, SemanticGame.receiverEU_single]
      simp [s₀, r₀]
    · fin_cases a
      · exact (receiverEU_two_lt hu c).le
      · exact le_rfl

/-- In Example 8, the pragmatically rationalizable sender says *101 m* only when precision matters,
and the receiver reads every signal literally. -/
theorem prs_eq : game.prsS = {fun c w ↦ if c = 0 ∧ w = 1 then 2 else 0} ∧
    game.prsR = {fun _ f ↦ if f = 2 then 1 else 0} := by
  have h : IsFixedPt game.receiverStep (game.icrR 0) := by
    rw [IsFixedPt, icrR_zero, receiverStep_zero]
  refine ⟨(game.prsS_eq_of_isFixedPt h).trans ?_, (game.prsR_eq_of_isFixedPt h).trans icrR_zero⟩
  rw [SemanticGame.icrS, icrR_zero, icrS_zero]; rfl

theorem round_number_ambiguous : ∀ s ∈ game.prsS, s 0 1 ≠ 0 ∧ s 1 1 = 0 := by
  rw [prs_eq.1]; rintro s rfl; decide

/-- Contrary to the stages displayed for Example 8, "exactly 100 m" is never used. -/
theorem exactly_never_used : ∀ s ∈ game.prsS, ∀ c w, s c w ≠ 1 := by
  rw [prs_eq.1]; rintro s rfl c w; fin_cases c <;> fin_cases w <;> decide

end Precision

/-! ### Example 10 and Section 6: cautious against best response -/

namespace SomeAll

/-- In Example 10 "some" (`0`) is true in both worlds, "all" (`1`) in the world `0` where all is
true and "some but not all" (`2`) in the other world `1`. -/
def meaning (f : Fin 3) (w : Fin 2) : Prop := f = 0 ∨ f.val = w.val + 1

instance (f : Fin 3) : DecidablePred (meaning f) := fun _ ↦ by unfold meaning; infer_instance

/-- Example 10's game (Table 13), with "some but not all" costing `c`. -/
def game (c : ℝ) : SemanticGame Unit (Fin 2) (Fin 3) (Fin 2) where
  prior := uniform
  prior_support := uniform_support
  meaning := meaning
  vS _ w a := if w = a then 1 else 0
  cost f := if f = 2 then c else 0
  uR _ w a := if w = a then 1 else 0

attribute [local simp] meaning uniform SemanticGame.uS
  Finsupp.single_apply Fin.sum_univ_two Finset.sum_filter

/-- The denotations of the signals, which are the literal receiver of the iterated best
response of [franke-2011]. -/
def denotation (f : Fin 3) : Finset (Fin 2) := Finset.univ.filter (meaning f)

theorem ibr_some_ambiguous :
    Function.IsFixedPt (Franke2011.receiverStep denotation ∘ Franke2011.senderStep denotation)
        denotation ∧
      Franke2011.inverse (Franke2011.senderStep denotation denotation) 0 = ∅ ∧
      denotation 0 = Finset.univ := by
  decide

variable {c : ℝ}

private def rA : Unit → Fin 3 → Fin 2 := fun _ f ↦ if f = 2 then 1 else 0
private def rB : Unit → Fin 3 → Fin 2 := fun _ f ↦ if f = 1 then 0 else 1
private def sA : Unit → Fin 2 → Fin 3 := fun _ w ↦ if w = 0 then 1 else 0
private def sB : Unit → Fin 2 → Fin 3 := fun _ w ↦ if w = 0 then 1 else 2

private theorem rA_ne_rB : rA ≠ rB := fun h ↦ by
  simpa [rA, rB] using congrFun (congrFun h ()) 0

private theorem mem_pair {r : Unit → Fin 3 → Fin 2} :
    r ∈ ({rA, rB} : Set _) ↔ r () 1 = 0 ∧ r () 2 = 1 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl) <;> simp [rA, rB]
  · rintro ⟨h1, h2⟩
    rcases (by omega : r () 0 = 0 ∨ r () 0 = 1) with h0 | h0
    · left; funext u f; cases u; fin_cases f <;> simp_all [rA]
    · right; funext u f; cases u; fin_cases f <;> simp_all [rB]

private theorem optimalActions_prior (u : Unit) (f : Fin 3) :
    (game c).optimalActions u ((game c).extension f) (game c).prior =
      if f = 0 then Finset.univ else {if f = 1 then 0 else 1} := by
  rw [SemanticGame.optimalActions]
  split_ifs with h0 h1
  · subst h0
    exact Finset.argmax_eq_self_of_forall_le fun a _ b _ ↦ by
      fin_cases a <;> fin_cases b <;> simp [SemanticGame.extension, game]
  all_goals
    rw [Finset.argmax_eq_singleton_iff]
    refine ⟨Finset.mem_univ _, fun b _ hb ↦ ?_⟩
    fin_cases f <;> fin_cases b <;> simp_all [SemanticGame.extension, game]

private theorem icrR_zero : (game c).icrR 0 = {rA, rB} := by
  ext r
  rw [mem_pair]
  simp only [SemanticGame.icrR, iterate_zero, id, SemanticGame.credulous, Set.mem_ofPred_eq,
    optimalActions_prior]
  constructor
  · intro h
    exact ⟨by simpa using h () 1, by simpa using h () 2⟩
  · rintro ⟨h1, h2⟩ u f
    cases u
    fin_cases f <;> simp [h1, h2]

private theorem mem_pair_s {s : Unit → Fin 2 → Fin 3} :
    s ∈ ({sA, sB} : Set _) ↔ s () 0 = 1 ∧ s () 1 ≠ 1 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl) <;> simp [sA, sB]
  · rintro ⟨h0, h1⟩
    rcases (by omega : s () 1 = 0 ∨ s () 1 = 2) with h | h
    · left; funext u w; cases u; fin_cases w <;> simp_all [sA]
    · right; funext u w; cases u; fin_cases w <;> simp_all [sB]

private theorem icrS_zero (hc0 : 0 < c) (hc1 : c < 1) : (game c).senderCR {rA, rB} = {sA, sB} := by
  ext s
  rw [mem_pair_s]
  constructor
  · intro hs
    have h := (game c).senderCR_subset (R := {rA, rB})
      (T := fun _ w ↦ if w = 0 then {1} else {0, 2}) (fun u w f' hf' ↦ by
        fin_cases w
        · refine ⟨1, fun r hr c' ↦ ?_, rB, by simp, (), ?_⟩
          · rw [mem_pair] at hr
            fin_cases f' <;> simp [game, hr.1, hr.2] <;>
              [skip; linarith]
            generalize r c' 0 = a; fin_cases a <;> simp
          · fin_cases f' <;> simp_all [game, rB]; linarith
        · refine ⟨2, fun r hr c' ↦ ?_, rB, by simp, (), ?_⟩
          · rw [mem_pair] at hr
            fin_cases f' <;> simp_all [game]; linarith
          · fin_cases f' <;> simp_all [game, rB]) hs
    refine ⟨by simpa using h () 0, fun h1 ↦ ?_⟩
    simpa [h1] using h () 1
  · rintro ⟨h0, h1⟩
    obtain ⟨t, ht0, ht1, hpick⟩ : ∃ t : ℝ, 0 < t ∧ t < 1 ∧
        ((s () 1 = 0 → 1 - c ≤ 1 - t) ∧ (s () 1 = 2 → 1 - t ≤ 1 - c)) := by
      rcases (by omega : s () 1 = 0 ∨ s () 1 = 2) with h | h
      · exact ⟨c / 2, by linarith, by linarith, fun _ ↦ by linarith,
          fun h' ↦ absurd (h.symm.trans h') (by decide)⟩
      · exact ⟨(1 + c) / 2, by linarith, by linarith,
          fun h' ↦ absurd (h.symm.trans h') (by decide), fun _ ↦ by linarith⟩
    refine (game c).mem_senderCR_iff.2 ⟨.duple rA rB ht0.le (sub_pos.2 ht1).le
      (add_sub_cancel t 1), .single (), coe_support_duple rA_ne_rB ht0 (sub_pos.2 ht1) _,
      by simp, fun u w ↦ ?_⟩
    cases u
    simp only [Finset.mem_argmax, Finset.mem_univ, true_and, SemanticGame.senderEU,
      sum_duple_mul, sum_unit_weights_mul]
    intro f'
    fin_cases w <;> fin_cases f' <;> rcases (by omega : s () 1 = 0 ∨ s () 1 = 2) with h | h <;>
      simp_all [game, rA, rB] <;> nlinarith

private theorem receiverStep_zero (hc0 : 0 < c) (hc1 : c < 1) :
    (game c).receiverStep {rA, rB} = {rB} := by
  have hsA : sA ∈ ({sA, sB} : Set _) := by simp
  have hsB : sB ∈ ({sA, sB} : Set _) := by simp
  rw [SemanticGame.receiverStep, icrS_zero hc0 hc1,
    (game c).receiverCR_eq ⟨_, hsA⟩ (T := fun u f ↦ {rB u f})]
  · ext r
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, SemanticGame.unexpected_iff]
    constructor
    · exact fun ⟨h, _⟩ ↦ funext fun u ↦ funext (h u)
    · rintro rfl
      refine ⟨fun u f ↦ rfl, fun f hf ↦ ?_⟩
      fin_cases f
      · exact (hf sA hsA () 1 rfl).elim
      · exact (hf sA hsA () 0 rfl).elim
      · exact (hf sB hsB () 1 rfl).elim
  · rintro u f a rfl a' s hs u' w hw
    rw [mem_pair_s] at hs
    fin_cases w <;> fin_cases f <;> fin_cases a' <;> simp_all [game, rB]
  · intro u f a' ha'
    refine ⟨rB u f, rfl, ?_⟩
    fin_cases f
    · exact ⟨sA, hsA, (), 1, rfl, by fin_cases a' <;> simp_all [game, rB]⟩
    · exact ⟨sA, hsA, (), 0, rfl, by fin_cases a' <;> simp_all [game, rB]⟩
    · exact ⟨sB, hsB, (), 1, rfl, by fin_cases a' <;> simp_all [game, rB]⟩

private theorem icrS_one (hc0 : 0 < c) : (game c).senderCR {rB} = {sA} := by
  rw [(game c).senderCR_eq (Set.singleton_nonempty _) (T := fun u w ↦ {sA u w})]
  · ext s; simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun h ↦ funext fun u ↦ funext (h u), fun h u w ↦ h ▸ rfl⟩
  · rintro u w f rfl f' r rfl c'
    fin_cases w <;> fin_cases f' <;> simp [game, sA, rB] <;> linarith
  · intro u w f' hf'
    refine ⟨sA u w, rfl, _, rfl, (), ?_⟩
    fin_cases w <;> fin_cases f' <;> simp_all [game, sA, rB]; linarith

private theorem receiverStep_one (hc0 : 0 < c) : (game c).receiverStep {rB} = {rB} := by
  have hext : (game c).extension 2 = {1} := by
    ext w; fin_cases w <;> simp [SemanticGame.extension, game]
  have hsA : sA ∈ ({sA} : Set _) := rfl
  rw [SemanticGame.receiverStep, icrS_one hc0,
    (game c).receiverCR_eq ⟨_, hsA⟩ (T := fun u f ↦ if f = 2 then Set.univ else {rB u f})]
  · ext r
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, SemanticGame.unexpected_iff]
    constructor
    · rintro ⟨h, hsur⟩
      refine funext fun u ↦ funext fun f ↦ ?_
      by_cases hf2 : f = 2
      · subst hf2
        obtain ⟨p, hp, hr⟩ := hsur 2 (fun s hs u' w ↦ by
          rw [hs]; fin_cases w <;> simp [sA]) u
        rw [(game c).optimalActions_eq_of_extension_eq_singleton hext u hp] at hr
        have := (Finset.mem_argmax.1 hr).2 1 (Finset.mem_univ _)
        revert this; generalize r u 2 = a; intro this
        fin_cases a <;> simp_all [game, rB]; linarith
      · simpa [hf2] using h u f
    · rintro rfl
      refine ⟨fun u f ↦ by split_ifs <;> simp, fun f hf u ↦
        ⟨(game c).prior, (game c).prior_support, ?_⟩⟩
      fin_cases f
      · exact (hf sA rfl () 1 rfl).elim
      · exact (hf sA rfl () 0 rfl).elim
      · change rB u 2 ∈ (game c).optimalActions u ((game c).extension 2) (game c).prior
        rw [(game c).optimalActions_eq_of_extension_eq_singleton hext u (game c).prior_support]
        simp [game, rB, Fin.forall_fin_two]
  · intro u f a ha a' s hs u' w hw
    rw [Set.mem_singleton_iff.1 hs] at hw
    fin_cases f
    · simp only [rB] at ha; subst ha
      fin_cases w <;> fin_cases a' <;> simp_all [game, sA]
    · simp only [rB] at ha; subst ha
      fin_cases w <;> fin_cases a' <;> simp_all [game, sA]
    · fin_cases w <;> simp [sA] at hw
  · intro u f a' ha'
    fin_cases f <;> simp at ha'
    · exact ⟨_, rfl, sA, rfl, (), 1, rfl, by fin_cases a' <;> simp_all [game, rB]⟩
    · exact ⟨_, rfl, sA, rfl, (), 0, rfl, by fin_cases a' <;> simp_all [game, rB]⟩

-- Example 10
theorem icr_some_implicates_not_all (hc0 : 0 < c) (hc1 : c < 1) :
    (game c).prsS = {fun _ w ↦ if w = 0 then 1 else 0} ∧
      (game c).prsR = {fun _ f ↦ if f = 1 then 0 else 1} := by
  have h1 : (game c).icrR 1 = {rB} := by
    rw [SemanticGame.icrR_succ, icrR_zero, receiverStep_zero hc0 hc1]
  have h : IsFixedPt (game c).receiverStep ((game c).icrR 1) := by
    rw [IsFixedPt, h1, receiverStep_one hc0]
  refine ⟨((game c).prsS_eq_of_isFixedPt h).trans ?_, ((game c).prsR_eq_of_isFixedPt h).trans h1⟩
  rw [SemanticGame.icrS, h1, icrS_one hc0]; rfl

end SomeAll

end

end Jaeger2014
