module

public import Mathlib.Data.Finset.Interval
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Modality.Necessity

/-!
# Boylan (2023): Putting oughts together

Consistent Agglomeration, from ⌜ought φ⌝ and ⌜ought ψ⌝ to ⌜ought (φ ∧ ψ)⌝ for consistent φ
and ψ, is valid for deontic *ought* and fails for epistemic *ought* ([boylan-2023]): in The Office
each worker should be in today though not everyone should be. The semantics makes *ought* an
existential quantifier over the propositionally best partial answers to a contextual relevance
question, restricted to the background information, and presupposes those best answers
pairwise consistent. The split then follows from the orderings. A deontic ordering places a
partial answer between the best and the worst complete answer inside it, so exactly one
complete answer is best (Fact 2), *ought* reduces to universal quantification over it
(Fact 3) and agglomerates (Fact 4); an epistemic ordering can rank a disjunction above each
disjunct, as a threshold on probability does, and The Office falsifies Agglomeration (Fact 5).
Inheritance holds and no choice of parameters verifies a dilemma, against the conflict
account, which reads The Office as one and agglomerates its premises.

## Implementation notes

The background information is a finite set of worlds and the relevance question restricted to
it a `Finpartition`, whose partial answers are the unions of complete answers; an ordering is a
relation on finite propositions at a world. Definedness and truth are separate predicates, so
the presupposition of (71a) is a hypothesis of the theorems that need it. Assumption 2 enters
through its lower half, that some complete answer inside a partial answer is at least as good
as it, which is what Fact 2 uses. The Office has two workers absent independently with
probability one third, worlds weighted by counts rather than probabilities; Dessert orders by
worst outcome and asks the two questions of §8.2.

## References

* [boylan-2023]
* [karttunen-1977]
* [von-fintel-2012]
* [horty-2012]
-/

@[expose] public section

namespace Boylan2023

open Finset

variable {W : Type*} [DecidableEq W]

/-! ### Questions and partial answers (§4.2) -/

section Question

variable {acc : Finset W} (Q : Finpartition acc)

/-- The partial answers to the relevance question restricted to the background information,
`Q|f(w)`: the unions of nonempty sets of complete answers. -/
def partialAnswers : Finset (Finset W) := (Ioc ∅ Q.parts).image (·.sup id)

variable {Q}

theorem mem_partialAnswers {p : Finset W} :
    p ∈ partialAnswers Q ↔ ∃ s, s ≠ ∅ ∧ s ⊆ Q.parts ∧ s.sup id = p := by
  simp [partialAnswers, and_assoc, nonempty_iff_ne_empty]

theorem parts_subset_partialAnswers : Q.parts ⊆ partialAnswers Q := λ q hq =>
  mem_partialAnswers.2 ⟨{q}, singleton_ne_empty q, singleton_subset_iff.2 hq, sup_singleton⟩

theorem subset_of_mem_partialAnswers {p : Finset W} (hp : p ∈ partialAnswers Q) : p ⊆ acc := by
  obtain ⟨s, -, hs, rfl⟩ := mem_partialAnswers.1 hp
  exact Finset.sup_le λ q hq => Q.le (hs hq)

theorem nonempty_of_mem_partialAnswers {p : Finset W} (hp : p ∈ partialAnswers Q) :
    p.Nonempty := by
  obtain ⟨s, hne, hs, rfl⟩ := mem_partialAnswers.1 hp
  obtain ⟨q, hq⟩ := nonempty_iff_ne_empty.2 hne
  exact (nonempty_iff_ne_empty.2 (Q.ne_bot (hs hq))).mono (le_sup (f := id) hq)

/-- Fact 1: a complete answer lies inside a partial answer or is disjoint from it. -/
theorem fact1 {p q : Finset W} (hp : p ∈ partialAnswers Q) (hq : q ∈ Q.parts) :
    q ⊆ p ∨ Disjoint q p := by
  obtain ⟨s, -, hs, rfl⟩ := mem_partialAnswers.1 hp
  by_cases h : q ∈ s
  · exact .inl (le_sup (f := id) h)
  · exact .inr (Finset.disjoint_sup_right.2 λ r hr => Q.disjoint hq (hs hr) λ e => h (e ▸ hr))

end Question

/-! ### Orderings and the best answers (§4) -/

/-- An ordering of propositions at a world, `ord w p q` for `p ≾ q`, `p` at least as good as
`q`; context supplies it, from value for a deontic and from probability or normality for an
epistemic *ought*. -/
abbrev PropOrdering (W : Type*) := W → Finset W → Finset W → Prop

section Ordering

variable (ord : PropOrdering W) [∀ w, DecidableRel (ord w)] (w : W)

/-- `q ≺ p`: `q` is strictly better than `p`. -/
def Better (q p : Finset W) : Prop := ord w q p ∧ ¬ ord w p q

instance (q p : Finset W) : Decidable (Better ord w q p) :=
  inferInstanceAs (Decidable (ord w q p ∧ ¬ ord w p q))

variable {acc : Finset W} (Q : Finpartition acc)

/-- (70): the propositionally best partial answers, those no partial answer strictly betters. -/
def PBEST : Finset (Finset W) :=
  (partialAnswers Q).filter λ p => ∀ q ∈ partialAnswers Q, ¬ Better ord w q p

/-- (71a): *ought* is defined only if the best answers are pairwise consistent with the
background information. -/
def Defined : Prop := ∀ p ∈ PBEST ord w Q, ∀ q ∈ PBEST ord w Q, (p ∩ q).Nonempty

/-- (71b): ⌜ought φ⌝, some best answer entails φ. -/
def Ought (φ : W → Prop) : Prop := ∃ p ∈ PBEST ord w Q, ∀ v ∈ p, φ v

/-- Assumption 2, the half Fact 2 uses: inside every partial answer some complete answer is
at least as good as it. -/
def IsDeontic : Prop := ∀ p ∈ partialAnswers Q, ∃ q ∈ Q.parts, q ⊆ p ∧ ord w q p

instance : Decidable (Defined ord w Q) :=
  inferInstanceAs (Decidable (∀ p ∈ PBEST ord w Q, ∀ q ∈ PBEST ord w Q, (p ∩ q).Nonempty))

instance (φ : W → Prop) [DecidablePred φ] : Decidable (Ought ord w Q φ) :=
  inferInstanceAs (Decidable (∃ p ∈ PBEST ord w Q, ∀ v ∈ p, φ v))

instance : Decidable (IsDeontic ord w Q) :=
  inferInstanceAs (Decidable (∀ p ∈ partialAnswers Q, ∃ q ∈ Q.parts, q ⊆ p ∧ ord w q p))

variable {ord w Q}

theorem mem_PBEST {p : Finset W} :
    p ∈ PBEST ord w Q ↔
      p ∈ partialAnswers Q ∧ ∀ q ∈ partialAnswers Q, ¬ Better ord w q p :=
  mem_filter

/-! ### Inheritance and dilemmas (§3.3, §8.1, §10) -/

theorem inheritance {φ ψ : W → Prop} (h : ∀ v, φ v → ψ v) (hφ : Ought ord w Q φ) :
    Ought ord w Q ψ :=
  let ⟨p, hp, hpφ⟩ := hφ
  ⟨p, hp, λ v hv => h v (hpφ v hv)⟩

theorem no_dilemma {φ : W → Prop} (hdef : Defined ord w Q) (h₁ : Ought ord w Q φ)
    (h₂ : Ought ord w Q (¬ φ ·)) : False :=
  let ⟨p, hp, hpφ⟩ := h₁
  let ⟨q, hq, hqφ⟩ := h₂
  let ⟨v, hv⟩ := hdef p hp q hq
  hqφ v (mem_inter.1 hv).2 (hpφ v (mem_inter.1 hv).1)

/-! ### Deontic *ought* is a box (Facts 2–4) -/

omit [∀ w, DecidableRel (ord w)] in
theorem not_better_of_le [IsTrans (Finset W) (ord w)] {p q : Finset W}
    (hp : ∀ r ∈ partialAnswers Q, ¬ Better ord w r p) (hqp : ord w q p) :
    ∀ r ∈ partialAnswers Q, ¬ Better ord w r q :=
  λ r hr ⟨hrq, hqr⟩ =>
    hp r hr ⟨IsTrans.trans _ _ _ hrq hqp, λ hpr => hqr (IsTrans.trans _ _ _ hqp hpr)⟩

/-- Fact 2: under a deontic transitive ordering whose *ought* is defined, exactly one
complete answer is best. -/
theorem fact2 [IsTrans (Finset W) (ord w)] (hdeon : IsDeontic ord w Q)
    (hdef : Defined ord w Q) (hne : (PBEST ord w Q).Nonempty) :
    ∃ q ∈ Q.parts, q ∈ PBEST ord w Q ∧
      ∀ q' ∈ Q.parts, q' ∈ PBEST ord w Q → q' = q := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨hpa, hund⟩ := mem_PBEST.1 hp
  obtain ⟨q, hq, -, hqp⟩ := hdeon p hpa
  have hqb : q ∈ PBEST ord w Q :=
    mem_PBEST.2 ⟨parts_subset_partialAnswers hq, not_better_of_le hund hqp⟩
  refine ⟨q, hq, hqb, λ q' hq' hq'b => by_contra λ hne => ?_⟩
  obtain ⟨v, hv⟩ := hdef q' hq'b q hqb
  exact Finset.disjoint_left.1 (Q.disjoint hq' hq hne) (mem_inter.1 hv).1 (mem_inter.1 hv).2

/-- Fact 3: with a best complete answer `q` and *ought* defined, ⌜ought φ⌝ holds exactly when
φ holds throughout `q`, the classic entry (59) relativized to `q`. -/
theorem fact3 {q : Finset W} (hq : q ∈ Q.parts) (hqb : q ∈ PBEST ord w Q)
    (hdef : Defined ord w Q) (φ : W → Prop) : Ought ord w Q φ ↔ ∀ v ∈ q, φ v := by
  refine ⟨λ ⟨p, hp, hpφ⟩ v hv => ?_, λ h => ⟨q, hqb, h⟩⟩
  rcases fact1 (mem_PBEST.1 hp).1 hq with hsub | hdisj
  · exact hpφ v (hsub hv)
  · obtain ⟨u, hu⟩ := hdef q hqb p hp
    exact absurd (mem_inter.1 hu) (Finset.disjoint_left.1 hdisj (mem_inter.1 hu).1 ·.2)

/-- Fact 4: deontic *ought*s agglomerate. -/
theorem fact4 [IsTrans (Finset W) (ord w)] (hdeon : IsDeontic ord w Q)
    (hdef : Defined ord w Q) (hne : (PBEST ord w Q).Nonempty) {φ ψ : W → Prop}
    (hφ : Ought ord w Q φ) (hψ : Ought ord w Q ψ) : Ought ord w Q (λ v => φ v ∧ ψ v) := by
  obtain ⟨q, hq, hqb, -⟩ := fact2 hdeon hdef hne
  rw [fact3 hq hqb hdef] at hφ hψ ⊢
  exact λ v hv => ⟨hφ v hv, hψ v hv⟩

end Ordering

/-! ### Epistemic orderings from a threshold (§8.1) -/

section Threshold

variable (μ : W → ℕ) (T : ℕ)

/-- The epistemic ordering of §8.1: `p ≾ q` when `p` passes the threshold, or is at least as
likely as `q`. Worlds carry weights and the threshold is half the information's weight. -/
def threshold : PropOrdering W := λ _ p q => T < 2 * p.sum μ ∨ q.sum μ ≤ p.sum μ

instance (w : W) : DecidableRel (threshold μ T w) :=
  λ p q => inferInstanceAs (Decidable (T < 2 * p.sum μ ∨ q.sum μ ≤ p.sum μ))

variable {μ T}

theorem inter_nonempty_of_half_lt {acc p q : Finset W} (hp : p ⊆ acc) (hq : q ⊆ acc)
    (h₁ : acc.sum μ < 2 * p.sum μ) (h₂ : acc.sum μ < 2 * q.sum μ) : (p ∩ q).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at h
  have h₃ : p.sum μ + q.sum μ ≤ acc.sum μ :=
    (sum_union h).symm.le.trans (sum_le_sum_of_subset (union_subset hp hq))
  omega

variable {acc : Finset W} {Q : Finpartition acc} {w : W}

theorem mem_PBEST_threshold (hex : ∃ q ∈ partialAnswers Q, T < 2 * q.sum μ)
    {p : Finset W} :
    p ∈ PBEST (threshold μ T) w Q ↔ p ∈ partialAnswers Q ∧ T < 2 * p.sum μ := by
  rw [mem_PBEST]
  refine ⟨λ ⟨hp, hund⟩ => ⟨hp, by_contra λ h => ?_⟩,
    λ ⟨hp, hT⟩ => ⟨hp, λ q _ hqp => ?_⟩⟩
  · obtain ⟨q, hq, hqT⟩ := hex
    exact hund q hq ⟨.inl hqT, λ hpq => hpq.elim h λ hle => h (by omega)⟩
  · exact hqp.2 (.inl hT)

theorem defined_threshold (hT : acc.sum μ = T)
    (hex : ∃ q ∈ partialAnswers Q, T < 2 * q.sum μ) :
    Defined (threshold μ T) w Q := λ _ hp _ hq =>
  have hp' := (mem_PBEST_threshold hex).1 hp
  have hq' := (mem_PBEST_threshold hex).1 hq
  inter_nonempty_of_half_lt (subset_of_mem_partialAnswers hp'.1)
    (subset_of_mem_partialAnswers hq'.1) (hT ▸ hp'.2) (hT ▸ hq'.2)

end Threshold

/-! ### The conflict account (61) -/

section Conflict

variable [Fintype W]

/-- The maximal contextually consistent subsets of a set of propositions, `D(f(w), g(w))`
with the whole space as information (fn. 16). -/
def MaxConsistent (props S : Finset (Finset W)) : Prop :=
  S ⊆ props ∧ (S.inf id).Nonempty ∧ ∀ S' ⊆ props, S ⊂ S' → ¬ (S'.inf id).Nonempty

instance (props S : Finset (Finset W)) : Decidable (MaxConsistent props S) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∀ S' ⊆ props, S ⊂ S' → ¬ (S'.inf id).Nonempty))

/-- (61): the conflict account ([von-fintel-2012], [horty-2012]), ⌜ought φ⌝ iff some
maximal consistent subset of the best propositions entails φ. -/
def ConflictOught (props : Finset (Finset W)) (φ : W → Prop) : Prop :=
  ∃ S ∈ props.powerset, MaxConsistent props S ∧ ∀ v ∈ S.inf id, φ v

instance (props : Finset (Finset W)) (φ : W → Prop) [DecidablePred φ] :
    Decidable (ConflictOught props φ) :=
  inferInstanceAs
    (Decidable (∃ S ∈ props.powerset, MaxConsistent props S ∧ ∀ v ∈ S.inf id, φ v))

end Conflict

/-! ### The classic semantics (59) -/

omit [DecidableEq W] in
open Modality ModalLogic in
/-- The classic entry (59), Kratzer necessity over the best worlds, agglomerates
unconditionally, so it cannot fit The Office for any modal base and ordering source. -/
theorem classic_agglomerates {f g : Background W} {φ ψ : W → Prop} {w : W}
    (hφ : necessity f g φ w) (hψ : necessity f g ψ w) : necessity f g (φ ⊓ ψ) w := by
  rw [necessity, box_inf]; exact ⟨hφ, hψ⟩

/-! ### The Office (§8.1) -/

namespace Office

/-- A world of The Office with two workers: whether Alice and whether Bob are in. -/
abbrev World := Bool × Bool

/-- Each worker is in with probability two thirds, independently: a world weighs `2` for each
worker in and `1` for each out, out of `9`. -/
def weight (w : World) : ℕ := (if w.1 then 2 else 1) * (if w.2 then 2 else 1)

instance : DecidableRel ⇑(Setoid.ker (id : World → World)) :=
  λ a b => inferInstanceAs (Decidable (id a = id b))

/-- The relevance question *which workers are in?*, every world its own complete answer. -/
def question : Finpartition (univ : Finset World) := Finpartition.ofSetoid (Setoid.ker id)

/-- The epistemic ordering: best above the threshold of one half. -/
def ordering : PropOrdering World := threshold weight 9

instance (w : World) : DecidableRel (ordering w) :=
  inferInstanceAs (DecidableRel (threshold weight 9 w))

def aliceIn (w : World) : Prop := w.1 = true
def bobIn (w : World) : Prop := w.2 = true

instance : DecidablePred aliceIn := λ w => inferInstanceAs (Decidable (w.1 = true))
instance : DecidablePred bobIn := λ w => inferInstanceAs (Decidable (w.2 = true))

/-- *ought* is defined in The Office: the best answers are pairwise consistent. -/
theorem defined : Defined ordering (true, true) question := by decide +kernel

/-- (2): Alice should be in the office today. -/
theorem alice_should_be_in : Ought ordering (true, true) question aliceIn := by decide +kernel

/-- (3): Bob should be in the office today. -/
theorem bob_should_be_in : Ought ordering (true, true) question bobIn := by decide +kernel

/-- (6) is false: no best answer entails that everyone is in. -/
theorem not_everyone_should_be_in :
    ¬ Ought ordering (true, true) question (λ v => aliceIn v ∧ bobIn v) := by decide +kernel

/-- (66) is false: no best answer entails that Alice is absent. -/
theorem not_alice_should_be_out :
    ¬ Ought ordering (true, true) question (¬ aliceIn ·) := by decide +kernel

theorem not_isDeontic : ¬ IsDeontic ordering (true, true) question := by decide +kernel

/-- Fact 5: parameters on which two *ought*s are true and their conjunction false. -/
theorem fact5 :
    ∃ (ord : PropOrdering World) (_ : ∀ w, DecidableRel (ord w)) (w : World)
      (Q : Finpartition (univ : Finset World)) (φ ψ : World → Prop),
      Defined ord w Q ∧ Ought ord w Q φ ∧ Ought ord w Q ψ ∧
        ¬ Ought ord w Q (λ v => φ v ∧ ψ v) :=
  ⟨ordering, inferInstance, (true, true), question, aliceIn, bobIn, defined, alice_should_be_in,
    bob_should_be_in, not_everyone_should_be_in⟩

/-- The conflict account's best propositions for The Office: each worker in, and not
everyone in. -/
def conflictBest : Finset (Finset World) :=
  {univ.filter aliceIn, univ.filter bobIn, univ.filter (λ v => ¬ (aliceIn v ∧ bobIn v))}

/-- On the conflict account (6) comes out true: the set of everyone in is maximal consistent. -/
theorem conflict_everyone_in : ConflictOught conflictBest (λ v => aliceIn v ∧ bobIn v) := by
  decide +kernel

/-- (67): the conflict account makes (2) and (66) both true, a dilemma The Office does not
involve. -/
theorem conflict_dilemma :
    ConflictOught conflictBest aliceIn ∧ ConflictOught conflictBest (¬ aliceIn ·) := by
  decide +kernel

end Office

/-! ### Dessert (§8.2) -/

namespace Dessert

/-- The outcomes: one of the three desserts, or illness from more than one. -/
inductive World
  | pie | cannoli | cake | ill
  deriving DecidableEq, Fintype, Repr

/-- Pie and cannoli are tastiest, cheesecake less so, illness worst. -/
def value : World → ℕ
  | .pie => 3
  | .cannoli => 3
  | .cake => 2
  | .ill => 0

/-- The worst outcome a proposition allows. -/
def worst (p : Finset World) : WithTop ℕ := p.inf λ v => (value v : WithTop ℕ)

/-- The deontic ordering: a proposition is at least as good as another when its worst outcome
is. -/
def ordering : PropOrdering World := λ _ p q => worst q ≤ worst p

instance (w : World) : DecidableRel (ordering w) :=
  λ p q => inferInstanceAs (Decidable (worst q ≤ worst p))

instance : DecidableRel ⇑(Setoid.ker (id : World → World)) :=
  λ a b => inferInstanceAs (Decidable (id a = id b))

instance : DecidableRel ⇑(Setoid.ker value) :=
  λ a b => inferInstanceAs (Decidable (value a = value b))

/-- The relevance question *what will I do?*, every outcome its own complete answer. -/
def what : Finpartition (univ : Finset World) := Finpartition.ofSetoid (Setoid.ker id)

/-- The relevance question *how good will the action I perform be?*, outcomes of equal value
lumped together. -/
def howGood : Finpartition (univ : Finset World) := Finpartition.ofSetoid (Setoid.ker value)

theorem isDeontic : IsDeontic ordering .pie what ∧ IsDeontic ordering .pie howGood := by
  decide +kernel

theorem what_undefined : ¬ Defined ordering .pie what := by decide +kernel

theorem howGood_defined : Defined ordering .pie howGood := by decide +kernel

theorem indifference :
    Ought ordering .pie howGood (λ v => v = .pie ∨ v = .cannoli) ∧
      ¬ Ought ordering .pie howGood (· = .pie) ∧
        ¬ Ought ordering .pie howGood (· = .cannoli) := by
  decide +kernel

/-- Deontic *ought* is a box: under *how good?* the unique best complete answer is *pie or
cannoli*, and ⌜ought φ⌝ holds exactly when φ does throughout it (Fact 3). -/
theorem ought_iff (φ : World → Prop) :
    Ought ordering .pie howGood φ ↔ ∀ v ∈ ({.pie, .cannoli} : Finset World), φ v :=
  fact3 (by decide +kernel) (by decide +kernel) howGood_defined φ

end Dessert

end Boylan2023
