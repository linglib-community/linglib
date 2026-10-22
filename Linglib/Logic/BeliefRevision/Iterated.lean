module

public import Mathlib.Order.Antisymmetrization
public import Linglib.Logic.RankingFunction

/-!
# Iterated belief revision

This file defines revision operators on epistemic states, the postulates of Alchourrón,
Gärdenfors and Makinson in the form Katsuno and Mendelzon gave them, and the iterated-revision
postulates of Darwiche and Pearl. An operator satisfies the first postulates iff a faithful
assignment of total preorders to states represents it, and the assignment is unique. Each
iterated-revision postulate is equivalent to a condition relating the preorder of a state to that
of its revision, and Spohn's conditionalisation of rankings meets the postulates.

## Main statements

* `BeliefRevision.Revision.isAGM_iff`, `BeliefRevision.Revision.Faithful.unique`: the
  representation theorem (Theorem 2).
* `BeliefRevision.Revision.IsAGM.isRational_accepts`: the conditional beliefs of a state form a
  rational consequence relation, whose preorder is the one representing the operator.
* `BeliefRevision.Revision.Faithful.c1_iff` to `c6_iff`, `cb_iff`: the postulates as conditions
  on preorders (Theorems 3, 4 and 7).
* `BeliefRevision.Revision.Faithful.cb_iff_c1_c2_c3_c4_c5_c6`: Boutilier's postulate is (C1)–(C6)
  together.
* `BeliefRevision.spohnRevision_faithful`, `BeliefRevision.spohnRevision_c1` to `c4`: Spohn's
  revision meets the postulates (Theorem 5).

## Implementation notes

* Rankings are bare functions `W → ℕ`, as the paper relaxes normalisation so that revision by an
  unsatisfiable proposition yields an unsatisfiable belief set. Their ranks and parts are those of
  `RankingFunction`, which are defined for any such function.
* A faithful assignment sends each state to a preorder given as a term. Its preorders are total
  and well-founded, as total preorders on the finitely many worlds of a propositional language
  are; well-foundedness supplies the least worlds that consistency needs.
* The preorder an AGM operator induces ranks `w` below `v` when `w` survives revision by
  `{w, v}`. The paper's construction adds the disjunct that `w` is believed, which expansion makes
  redundant.
* Lemma 1 needs its premise satisfiable, which the paper leaves implicit.
* The postulate of syntax-irrelevance holds by construction: propositions are sets of worlds and
  revision is a function of the state.

## References

* [A. Darwiche and J. Pearl, *On the Logic of Iterated Belief Revision*
  (1997)][darwiche-pearl-1997]
* [C. E. Alchourrón, P. Gärdenfors and D. Makinson, *On the Logic of Theory Change: Partial
  Meet Contraction and Revision Functions* (1985)][alchouron-gardenfors-makinson-1985]
* [H. Katsuno and A. O. Mendelzon, *Propositional Knowledge Base Revision and Minimal Change*
  (1991)][katsuno-mendelzon-1991]
* [C. Boutilier, *Iterated Revision and Minimal Change of Conditional Beliefs*
  (1996)][boutilier-1996]
* [P. Gärdenfors and D. Makinson, *Nonmonotonic Inference Based on Expectations*
  (1994)][gardenfors-makinson-1994]
* [W. Spohn, *Ordinal Conditional Functions: A Dynamic Theory of Epistemic States*
  (1988)][spohn-1988]
-/

@[expose] public section

namespace BeliefRevision

variable {S W : Type*}

/-- A revision operator on epistemic states over the worlds `W` assigns each state the worlds
its belief set admits and revises a state by a proposition. -/
structure Revision (S W : Type*) where
  /-- The worlds admitted by the state's belief set. -/
  bel : S → Set W
  /-- Revision of a state by a proposition. -/
  revise : S → Set W → S

/-- Two preorders agree on `d`. -/
def AgreesOn (p q : Preorder W) (d : Set W) : Prop :=
  ∀ w ∈ d, ∀ v ∈ d, (p.le w v ↔ q.le w v)

/-- An `A`-world strictly below a `B`-world in `p` stays strictly below in `q`. -/
def PreservesLt (p q : Preorder W) (A B : Set W) : Prop :=
  ∀ w ∈ A, ∀ v ∈ B, p.lt w v → q.lt w v

/-- An `A`-world weakly below a `B`-world in `p` stays weakly below in `q`. -/
def PreservesLe (p q : Preorder W) (A B : Set W) : Prop :=
  ∀ w ∈ A, ∀ v ∈ B, p.le w v → q.le w v

section Decidable

variable [Fintype W] {p q : Preorder W} [DecidableRel p.le] [DecidableRel q.le]
  [DecidableRel p.lt] [DecidableRel q.lt] {A B : Set W} [DecidablePred (· ∈ A)]
  [DecidablePred (· ∈ B)]

instance : Decidable (AgreesOn p q A) := by unfold AgreesOn; infer_instance

instance : Decidable (PreservesLt p q A B) := by unfold PreservesLt; infer_instance

instance : Decidable (PreservesLe p q A B) := by unfold PreservesLe; infer_instance

end Decidable

theorem AgreesOn.lt_iff {p q : Preorder W} {d : Set W} (h : AgreesOn p q d) {w v : W}
    (hw : w ∈ d) (hv : v ∈ d) : p.lt w v ↔ q.lt w v := by
  rw [p.lt_iff_le_not_ge, q.lt_iff_le_not_ge, h w hw v hv, h v hv w hw]

namespace Revision

variable (r : Revision S W)

/-- A revision operator satisfies the AGM postulates on epistemic states when it has success,
expansion when the evidence is consistent with the beliefs, consistency, superexpansion and
subexpansion. -/
structure IsAGM : Prop where
  success : ∀ Ψ μ, r.bel (r.revise Ψ μ) ⊆ μ
  expansion : ∀ Ψ μ, (r.bel Ψ ∩ μ).Nonempty → r.bel (r.revise Ψ μ) = r.bel Ψ ∩ μ
  consistency : ∀ Ψ μ, μ.Nonempty → (r.bel (r.revise Ψ μ)).Nonempty
  superexpansion : ∀ Ψ μ φ, r.bel (r.revise Ψ μ) ∩ φ ⊆ r.bel (r.revise Ψ (μ ∩ φ))
  subexpansion : ∀ Ψ μ φ, (r.bel (r.revise Ψ μ) ∩ φ).Nonempty →
    r.bel (r.revise Ψ (μ ∩ φ)) ⊆ r.bel (r.revise Ψ μ) ∩ φ

/-- An assignment of well-founded total preorders to states is faithful and represents `r` when
the belief worlds of a state are equally plausible and strictly more plausible than the others,
and revision selects the least worlds of the evidence. -/
structure Faithful (ord : S → Preorder W) : Prop where
  total : ∀ Ψ, Std.Total (ord Ψ).le
  wellFounded : ∀ Ψ, WellFounded (ord Ψ).lt
  equiv_of_mem : ∀ Ψ w v, w ∈ r.bel Ψ → v ∈ r.bel Ψ → AntisymmRel (ord Ψ).le w v
  lt_of_mem : ∀ Ψ w v, w ∈ r.bel Ψ → v ∉ r.bel Ψ → (ord Ψ).lt w v
  bel_revise : ∀ Ψ μ, r.bel (r.revise Ψ μ) = (ord Ψ).minimals μ

/-- Postulate (C1) says that evidence entailed by later evidence is redundant. -/
def C1 : Prop :=
  ∀ Ψ μ α, α ⊆ μ → r.bel (r.revise (r.revise Ψ μ) α) = r.bel (r.revise Ψ α)

/-- Postulate (C2) says that evidence contradicted by later evidence is overridden. -/
def C2 : Prop :=
  ∀ Ψ μ α, α ⊆ μᶜ → r.bel (r.revise (r.revise Ψ μ) α) = r.bel (r.revise Ψ α)

/-- Postulate (C3) says that evidence implied by later evidence given the state is retained. -/
def C3 : Prop :=
  ∀ Ψ μ α, r.bel (r.revise Ψ α) ⊆ μ → r.bel (r.revise (r.revise Ψ μ) α) ⊆ μ

/-- Postulate (C4) says that evidence not contradicted by later evidence stays
uncontradicted. -/
def C4 : Prop :=
  ∀ Ψ μ α, ¬ r.bel (r.revise Ψ α) ⊆ μᶜ → ¬ r.bel (r.revise (r.revise Ψ μ) α) ⊆ μᶜ

/-- Postulate (C5) says that the conditional belief `μ ∣ α` is not acquired on accommodating
evidence `μ` that rules out the premise `α`. -/
def C5 : Prop :=
  ∀ Ψ μ α, r.bel (r.revise Ψ μ) ⊆ αᶜ → ¬ r.bel (r.revise Ψ α) ⊆ μ →
    ¬ r.bel (r.revise (r.revise Ψ μ) α) ⊆ μ

/-- Postulate (C6) says that the conditional belief `μᶜ ∣ α` is not given up on accommodating
evidence `μ` that rules out the premise `α`. -/
def C6 : Prop :=
  ∀ Ψ μ α, r.bel (r.revise Ψ μ) ⊆ αᶜ → r.bel (r.revise Ψ α) ⊆ μᶜ →
    r.bel (r.revise (r.revise Ψ μ) α) ⊆ μᶜ

/-- Boutilier's postulate (CB) says that evidence contradicted by later evidence is forgotten. -/
def CB : Prop :=
  ∀ Ψ μ α, r.bel (r.revise Ψ μ) ⊆ αᶜ → r.bel (r.revise (r.revise Ψ μ) α) = r.bel (r.revise Ψ α)

/-- Revising by a conjunction is conditioning the revision by the first conjunct on the
second, when that leaves something. -/
theorem IsAGM.revise_inter {r : Revision S W} (h : r.IsAGM) {Ψ : S} {μ φ : Set W}
    (hne : (r.bel (r.revise Ψ μ) ∩ φ).Nonempty) :
    r.bel (r.revise Ψ (μ ∩ φ)) = r.bel (r.revise Ψ μ) ∩ φ :=
  (h.subexpansion Ψ μ φ hne).antisymm (h.superexpansion Ψ μ φ)

/-- The state `Ψ` accepts `β` given `α`, and `β ∣ α` is a conditional belief of `Ψ`, when the
belief set of the revision of `Ψ` by `α` entails `β`. -/
def Accepts (Ψ : S) (α β : Set W) : Prop := r.bel (r.revise Ψ α) ⊆ β

/-- Postulate (C1) holds iff accommodating `μ` perturbs no conditional belief whose premise
entails `μ`. -/
theorem c1_iff_accepts : r.C1 ↔
    ∀ Ψ μ α β, α ⊆ μ → (r.Accepts (r.revise Ψ μ) α β ↔ r.Accepts Ψ α β) :=
  ⟨fun h Ψ μ α β hα ↦ by rw [Accepts, Accepts, h Ψ μ α hα], fun h Ψ μ α hα ↦
    ((h Ψ μ α _ hα).2 subset_rfl).antisymm ((h Ψ μ α _ hα).1 subset_rfl)⟩

/-- Postulate (C2) holds iff accommodating `μ` perturbs no conditional belief whose premise
contradicts `μ`. -/
theorem c2_iff_accepts : r.C2 ↔
    ∀ Ψ μ α β, α ⊆ μᶜ → (r.Accepts (r.revise Ψ μ) α β ↔ r.Accepts Ψ α β) :=
  ⟨fun h Ψ μ α β hα ↦ by rw [Accepts, Accepts, h Ψ μ α hα], fun h Ψ μ α hα ↦
    ((h Ψ μ α _ hα).2 subset_rfl).antisymm ((h Ψ μ α _ hα).1 subset_rfl)⟩

/-- Postulate (C3) holds iff the conditional belief `μ ∣ α` is never given up on accommodating
`μ`. -/
theorem c3_iff_accepts : r.C3 ↔ ∀ Ψ μ α, r.Accepts Ψ α μ → r.Accepts (r.revise Ψ μ) α μ :=
  Iff.rfl

/-- Postulate (C4) holds iff the conditional belief `μᶜ ∣ α` is never acquired on accommodating
`μ`. -/
theorem c4_iff_accepts : r.C4 ↔
    ∀ Ψ μ α, ¬ r.Accepts Ψ α μᶜ → ¬ r.Accepts (r.revise Ψ μ) α μᶜ :=
  Iff.rfl

variable {r}

/-- The conditional beliefs of a state of an AGM operator form a rational consequence relation.
Superexpansion gives Or, and subexpansion gives cautious and rational monotonicity. -/
theorem IsAGM.isRational_accepts (h : r.IsAGM) (Ψ : S) : Nonmonotonic.IsRational (r.Accepts Ψ) where
  refl α := h.success Ψ α
  rightWeakening hβ hβγ := hβ.trans hβγ
  and hβ hγ := Set.subset_inter hβ hγ
  or := by
    rintro α β γ hα hβ w hw
    rcases h.success Ψ _ hw with hwα | hwβ
    · exact hα (by
        simpa only [Set.union_inter_cancel_left] using h.superexpansion Ψ (α ∪ β) α ⟨hw, hwα⟩)
    · exact hβ (by
        simpa only [Set.union_inter_cancel_right] using h.superexpansion Ψ (α ∪ β) β ⟨hw, hwβ⟩)
  cautiousMonotonicity := by
    intro α β γ hβ hγ
    rcases (r.bel (r.revise Ψ α)).eq_empty_or_nonempty with he | ⟨w, hw⟩
    · have hα : α = ∅ := Set.not_nonempty_iff_eq_empty.1 fun hne ↦
        (h.consistency Ψ α hne).ne_empty he
      exact fun w hw ↦ absurd (h.success Ψ _ hw).1 (by simp [hα])
    · exact ((h.subexpansion Ψ α β ⟨w, hw, hβ hw⟩).trans Set.inter_subset_left).trans hγ
  rationalMonotonicity := by
    intro α β γ hγ hβ
    obtain ⟨w, hw, hwβ⟩ := Set.not_subset.1 hβ
    exact ((h.subexpansion Ψ α β ⟨w, hw, not_not.1 hwβ⟩).trans Set.inter_subset_left).trans hγ

/-- A state of an AGM operator accepts the contradiction only given the contradiction
(consistency preservation). -/
theorem IsAGM.accepts_empty_iff (h : r.IsAGM) {Ψ : S} {α : Set W} :
    r.Accepts Ψ α ∅ ↔ α = ∅ :=
  ⟨fun hα ↦ Set.not_nonempty_iff_eq_empty.1 fun hne ↦
      (h.consistency Ψ α hne).ne_empty (Set.subset_empty_iff.1 hα),
    fun hα ↦ hα ▸ h.success Ψ ∅⟩

/-! ### The representation theorem -/

/-- The preorder of a state of an AGM operator is that of its conditional beliefs, under which `w`
is at least as plausible as `v` when `w` survives revision by `{w, v}`. -/
@[reducible] def IsAGM.ord (h : r.IsAGM) (Ψ : S) : Preorder W :=
  Nonmonotonic.IsRational.preorder (C := fun μ ↦ r.bel (r.revise Ψ μ)) (h.isRational_accepts Ψ)
    fun _ ↦ h.accepts_empty_iff.1

theorem IsAGM.ord_le_iff (h : r.IsAGM) {Ψ : S} {w v : W} :
    (h.ord Ψ).le w v ↔ w ∈ r.bel (r.revise Ψ {w, v}) :=
  Iff.rfl

/-- The preorders of an AGM operator are a faithful assignment representing it. -/
theorem IsAGM.faithful (h : r.IsAGM) : r.Faithful h.ord where
  total _ := Nonmonotonic.IsRational.total_preorder _ _
  wellFounded _ := Nonmonotonic.IsRational.wellFounded_preorder_lt _ _
  equiv_of_mem Ψ w v hw hv := by
    rw [AntisymmRel, h.ord_le_iff, h.ord_le_iff, h.expansion Ψ _ ⟨w, hw, by simp⟩,
      h.expansion Ψ _ ⟨v, hv, by simp⟩]
    exact ⟨⟨hw, by simp⟩, ⟨hv, by simp⟩⟩
  lt_of_mem Ψ w v hw hv := by
    rw [(h.ord Ψ).lt_iff_le_not_ge, h.ord_le_iff, h.ord_le_iff, h.expansion Ψ _ ⟨w, hw, by simp⟩,
      h.expansion Ψ _ ⟨w, hw, by simp⟩]
    exact ⟨⟨hw, by simp⟩, fun hv' ↦ hv hv'.1⟩
  bel_revise Ψ μ :=
    (Nonmonotonic.IsRational.minimals_preorder (C := fun μ ↦ r.bel (r.revise Ψ μ)) _ _ μ).symm

/-- Under a faithful assignment the revised belief worlds are the least worlds of the
evidence. -/
theorem Faithful.mem_bel_revise {ord : S → Preorder W} (h : r.Faithful ord) {Ψ : S} {μ : Set W}
    {w : W} : w ∈ r.bel (r.revise Ψ μ) ↔ w ∈ μ ∧ ∀ y ∈ μ, (ord Ψ).le w y := by
  rw [h.bel_revise, Preorder.mem_minimals_iff_forall_le (h.total Ψ)]

theorem Faithful.le_of_mem {ord : S → Preorder W} (h : r.Faithful ord) {Ψ : S} {w v : W}
    (hw : w ∈ r.bel Ψ) (hv : v ∉ r.bel Ψ) : (ord Ψ).le w v :=
  (((ord Ψ).lt_iff_le_not_ge _ _).1 (h.lt_of_mem Ψ w v hw hv)).1

theorem Faithful.not_le_of_mem {ord : S → Preorder W} (h : r.Faithful ord) {Ψ : S} {w v : W}
    (hw : w ∈ r.bel Ψ) (hv : v ∉ r.bel Ψ) : ¬ (ord Ψ).le v w :=
  (((ord Ψ).lt_iff_le_not_ge _ _).1 (h.lt_of_mem Ψ w v hw hv)).2

/-- Under a faithful assignment `w` survives revision by the pair `{w, v}` exactly when it is
at least as plausible as `v`. -/
theorem Faithful.mem_bel_revise_pair {ord : S → Preorder W} (h : r.Faithful ord) {Ψ : S}
    {w v : W} : w ∈ r.bel (r.revise Ψ {w, v}) ↔ (ord Ψ).le w v := by
  rw [h.bel_revise, Preorder.mem_minimals_pair (h.total Ψ)]

/-- At most one faithful assignment represents an operator. -/
theorem Faithful.unique {o₁ o₂ : S → Preorder W} (h₁ : r.Faithful o₁) (h₂ : r.Faithful o₂) :
    o₁ = o₂ :=
  funext fun Ψ ↦ Preorder.eq_of_minimals_eq (h₁.total Ψ) (h₂.total Ψ) <|
    funext fun μ ↦ (h₁.bel_revise Ψ μ).symm.trans (h₂.bel_revise Ψ μ)

/-- A faithfully represented operator satisfies the postulates. -/
theorem Faithful.isAGM {ord : S → Preorder W} (h : r.Faithful ord) : r.IsAGM where
  success Ψ μ := by rw [h.bel_revise]; exact (ord Ψ).minimals_subset μ
  expansion Ψ μ hne := by
    obtain ⟨u, hu, huμ⟩ := hne
    ext w
    rw [h.mem_bel_revise]
    constructor
    · rintro ⟨hwμ, hw⟩
      exact ⟨by_contra fun hwΨ ↦ h.not_le_of_mem hu hwΨ (hw u huμ), hwμ⟩
    · rintro ⟨hwΨ, hwμ⟩
      refine ⟨hwμ, fun y hy ↦ ?_⟩
      by_cases hyΨ : y ∈ r.bel Ψ
      · exact (h.equiv_of_mem Ψ w y hwΨ hyΨ).1
      · exact h.le_of_mem hwΨ hyΨ
  consistency Ψ μ := fun ⟨_, hw⟩ ↦ by
    obtain ⟨v, hv, -⟩ := Preorder.exists_le_mem_minimals (h.wellFounded Ψ) hw
    exact ⟨v, h.bel_revise Ψ μ ▸ hv⟩
  superexpansion Ψ μ φ := by
    simp only [h.bel_revise]
    rcases ((ord Ψ).minimals μ ∩ φ).eq_empty_or_nonempty with he | hne
    · exact he ▸ Set.empty_subset _
    · exact (Preorder.minimals_inter_eq (h.total Ψ) hne).ge
  subexpansion Ψ μ φ hne := by
    simp only [h.bel_revise] at hne ⊢
    exact (Preorder.minimals_inter_eq (h.total Ψ) hne).le

/-- An operator satisfies the postulates iff a faithful assignment represents it (Theorem 2). -/
theorem isAGM_iff : r.IsAGM ↔ ∃ ord, r.Faithful ord :=
  ⟨fun h ↦ ⟨_, h.faithful⟩, fun ⟨_, h⟩ ↦ h.isAGM⟩

/-- The preorder of a state encodes its conditional beliefs, since `β` is accepted given `α`
exactly when the least `α`-worlds are `β`-worlds. -/
theorem Faithful.accepts_iff {ord : S → Preorder W} (h : r.Faithful ord) {Ψ : S}
    {α β : Set W} : r.Accepts Ψ α β ↔ Nonmonotonic.Entails (ord Ψ) α β := by
  rw [Accepts, h.bel_revise, Nonmonotonic.Entails]

/-- A state accepts `β` given a satisfiable `α` iff some `α ∩ β`-world is strictly more plausible
than every `α \ β`-world (Lemma 1). -/
theorem Faithful.accepts_iff_exists_lt {ord : S → Preorder W} (h : r.Faithful ord) {Ψ : S}
    {α β : Set W} (hα : α.Nonempty) :
    r.Accepts Ψ α β ↔ ∃ w ∈ α ∩ β, ∀ v ∈ α \ β, (ord Ψ).lt w v := by
  constructor
  · intro hαβ
    obtain ⟨w, hw⟩ := h.isAGM.consistency Ψ α hα
    refine ⟨w, ⟨(h.mem_bel_revise.1 hw).1, hαβ hw⟩, fun v hv ↦ (ord Ψ).lt_iff_le_not_ge _ _ |>.2
      ⟨(h.mem_bel_revise.1 hw).2 v hv.1, fun hvw ↦ hv.2 (hαβ (h.mem_bel_revise.2
        ⟨hv.1, fun y hy ↦ (ord Ψ).le_trans _ _ _ hvw ((h.mem_bel_revise.1 hw).2 y hy)⟩))⟩⟩
  · rintro ⟨w, ⟨hwα, -⟩, hlt⟩ x hx
    by_contra hxβ
    exact ((ord Ψ).lt_iff_le_not_ge _ _).1 (hlt x ⟨(h.mem_bel_revise.1 hx).1, hxβ⟩) |>.2
      ((h.mem_bel_revise.1 hx).2 w hwα)

/-! ### The iterated-revision postulates -/

/-- Revising by `μ` before `α ⊆ D Ψ μ` leaves the beliefs of revising by `α` alone iff the
preorders of a state and of its revision agree on `D Ψ μ`. -/
theorem Faithful.agreesAfter_iff {ord : S → Preorder W} (h : r.Faithful ord)
    (D : S → Set W → Set W) :
    (∀ Ψ μ α, α ⊆ D Ψ μ → r.bel (r.revise (r.revise Ψ μ) α) = r.bel (r.revise Ψ α)) ↔
      ∀ Ψ μ, AgreesOn (ord Ψ) (ord (r.revise Ψ μ)) (D Ψ μ) := by
  constructor
  · intro hC Ψ μ w hw v hv
    have e := hC Ψ μ {w, v} (Set.pair_subset hw hv)
    rw [← h.mem_bel_revise_pair (Ψ := Ψ), ← h.mem_bel_revise_pair (Ψ := r.revise Ψ μ), e]
  · intro hCR Ψ μ α hα
    rw [h.bel_revise, h.bel_revise,
      Preorder.minimals_congr fun a ha b hb ↦ hCR Ψ μ a (hα ha) b (hα hb)]

/-- Postulate (C1) holds iff the preorders of a state and of its revision by `μ` agree on the
`μ`-worlds, which is condition (CR1) of Theorem 4. -/
theorem Faithful.c1_iff {ord : S → Preorder W} (h : r.Faithful ord) :
    r.C1 ↔ ∀ Ψ μ, AgreesOn (ord Ψ) (ord (r.revise Ψ μ)) μ :=
  h.agreesAfter_iff fun _ μ ↦ μ

/-- Postulate (C2) holds iff the preorders of a state and of its revision by `μ` agree on the
non-`μ`-worlds, which is condition (CR2) of Theorem 4. -/
theorem Faithful.c2_iff {ord : S → Preorder W} (h : r.Faithful ord) :
    r.C2 ↔ ∀ Ψ μ, AgreesOn (ord Ψ) (ord (r.revise Ψ μ)) μᶜ :=
  h.agreesAfter_iff fun _ μ ↦ μᶜ

/-- Postulate (CB) holds iff the preorders of a state and of its revision agree outside the
revised belief set, which is condition (CBR) of Theorem 3. -/
theorem Faithful.cb_iff {ord : S → Preorder W} (h : r.Faithful ord) :
    r.CB ↔ ∀ Ψ μ, AgreesOn (ord Ψ) (ord (r.revise Ψ μ)) (r.bel (r.revise Ψ μ))ᶜ := by
  rw [← h.agreesAfter_iff fun Ψ μ ↦ (r.bel (r.revise Ψ μ))ᶜ]
  exact forall₃_congr fun _ _ _ ↦ imp_congr_left Set.subset_compl_comm

/-- Postulate (C3) holds iff revision by `μ` preserves each strict ranking of a `μ`-world below a
non-`μ`-world, which is condition (CR3) of Theorem 4. -/
theorem Faithful.c3_iff {ord : S → Preorder W} (h : r.Faithful ord) :
    r.C3 ↔ ∀ Ψ μ, PreservesLt (ord Ψ) (ord (r.revise Ψ μ)) μ μᶜ := by
  constructor
  · intro hC Ψ μ w hw v hv hlt
    have hlt' := ((ord Ψ).lt_iff_le_not_ge _ _).1 hlt
    have h₁ : r.bel (r.revise Ψ {w, v}) ⊆ μ := by
      intro x hx
      rcases Set.mem_insert_iff.1 (h.mem_bel_revise.1 hx).1 with rfl | hxv
      · exact hw
      · rw [Set.mem_singleton_iff] at hxv
        subst hxv
        exact absurd ((h.mem_bel_revise.1 hx).2 w (by simp)) hlt'.2
    have h₂ := hC Ψ μ {w, v} h₁
    have hnvw : ¬ (ord (r.revise Ψ μ)).le v w := fun hvw ↦
      hv (h₂ (by rw [Set.pair_comm]; exact h.mem_bel_revise_pair.2 hvw))
    exact ((ord _).lt_iff_le_not_ge _ _).2
      ⟨((h.total _).total w v).resolve_right hnvw, hnvw⟩
  · intro hCR Ψ μ α hα w hw
    by_contra hwμ
    have hw' := h.mem_bel_revise.1 hw
    obtain ⟨u, hu⟩ := h.isAGM.consistency Ψ α ⟨w, hw'.1⟩
    have hu' := h.mem_bel_revise.1 hu
    have hlt : (ord Ψ).lt u w := ((ord Ψ).lt_iff_le_not_ge _ _).2
      ⟨hu'.2 w hw'.1, fun hwu ↦ hwμ (hα (h.mem_bel_revise.2
        ⟨hw'.1, fun y hy ↦ (ord Ψ).le_trans _ _ _ hwu (hu'.2 y hy)⟩))⟩
    exact (((ord _).lt_iff_le_not_ge _ _).1 (hCR Ψ μ u (hα hu) w hwμ hlt)).2 (hw'.2 u hu'.1)

/-- Postulate (C4) holds iff revision by `μ` preserves each weak ranking of a `μ`-world below a
non-`μ`-world, which is condition (CR4) of Theorem 4. -/
theorem Faithful.c4_iff {ord : S → Preorder W} (h : r.Faithful ord) :
    r.C4 ↔ ∀ Ψ μ, PreservesLe (ord Ψ) (ord (r.revise Ψ μ)) μ μᶜ := by
  constructor
  · intro hC Ψ μ w hw v hv hle
    have h₁ : ¬ r.bel (r.revise Ψ {w, v}) ⊆ μᶜ :=
      Set.not_subset.2 ⟨w, h.mem_bel_revise_pair.2 hle, fun hwc ↦ hwc hw⟩
    obtain ⟨x, hx, hxμ⟩ := Set.not_subset.1 (hC Ψ μ {w, v} h₁)
    rw [Set.mem_compl_iff, not_not] at hxμ
    rcases Set.mem_insert_iff.1 (h.mem_bel_revise.1 hx).1 with rfl | hx'
    · exact h.mem_bel_revise_pair.1 hx
    · rw [Set.mem_singleton_iff] at hx'
      subst hx'
      exact absurd hxμ hv
  · intro hCR Ψ μ α hα
    obtain ⟨u, hu, huμ⟩ := Set.not_subset.1 hα
    rw [Set.mem_compl_iff, not_not] at huμ
    have hu' := h.mem_bel_revise.1 hu
    obtain ⟨w, hw⟩ := h.isAGM.consistency (r.revise Ψ μ) α ⟨u, hu'.1⟩
    have hw' := h.mem_bel_revise.1 hw
    refine Set.not_subset.2 ?_
    by_cases hwμ : w ∈ μ
    · exact ⟨w, hw, fun hwc ↦ hwc hwμ⟩
    · exact ⟨u, h.mem_bel_revise.2 ⟨hu'.1, fun y hy ↦ (ord _).le_trans _ _ _
        (hCR Ψ μ u huμ w hwμ (hu'.2 w hw'.1)) (hw'.2 y hy)⟩, fun huc ↦ huc huμ⟩

/-- Postulate (C5) holds iff revision by `μ` preserves each weak ranking of a non-`μ`-world below
a `μ`-world outside the revised belief set, which is condition (CR5) of Theorem 7, its world `ω₃`
witnessing that `ω₁` is not among the least `μ`-worlds. -/
theorem Faithful.c5_iff {ord : S → Preorder W} (h : r.Faithful ord) :
    r.C5 ↔ ∀ Ψ μ, PreservesLe (ord Ψ) (ord (r.revise Ψ μ)) μᶜ (μ \ r.bel (r.revise Ψ μ)) := by
  constructor
  · intro hC Ψ μ w hw v hv hle
    have hα : r.bel (r.revise Ψ μ) ⊆ ({w, v} : Set W)ᶜ := by
      rintro x hx (rfl | rfl)
      exacts [hw (h.isAGM.success Ψ μ hx), hv.2 hx]
    obtain ⟨x, hx, hxμ⟩ := Set.not_subset.1 (hC Ψ μ {w, v} hα fun hsub ↦
      hw (hsub (h.mem_bel_revise_pair.2 hle)))
    rcases (h.mem_bel_revise.1 hx).1 with rfl | rfl
    · exact h.mem_bel_revise_pair.1 hx
    · exact absurd hv.1 hxμ
  · intro hCR Ψ μ α hα hαμ hsub
    obtain ⟨u, hu, huμ⟩ := Set.not_subset.1 hαμ
    have hu' := h.mem_bel_revise.1 hu
    obtain ⟨x, hx⟩ := h.isAGM.consistency (r.revise Ψ μ) α ⟨u, hu'.1⟩
    have hx' := h.mem_bel_revise.1 hx
    have hux := hCR Ψ μ u huμ x ⟨hsub hx, fun hxB ↦ hα hxB hx'.1⟩ (hu'.2 x hx'.1)
    exact huμ (hsub (h.mem_bel_revise.2
      ⟨hu'.1, fun y hy ↦ (ord _).le_trans _ _ _ hux (hx'.2 y hy)⟩))

/-- Postulate (C6) holds iff revision by `μ` preserves each strict ranking of a non-`μ`-world
below a `μ`-world outside the revised belief set, which is condition (CR6) of Theorem 7. -/
theorem Faithful.c6_iff {ord : S → Preorder W} (h : r.Faithful ord) :
    r.C6 ↔ ∀ Ψ μ, PreservesLt (ord Ψ) (ord (r.revise Ψ μ)) μᶜ (μ \ r.bel (r.revise Ψ μ)) := by
  constructor
  · intro hC Ψ μ w hw v hv hlt
    have hα : r.bel (r.revise Ψ μ) ⊆ ({w, v} : Set W)ᶜ := by
      rintro x hx (rfl | rfl)
      exacts [hw (h.isAGM.success Ψ μ hx), hv.2 hx]
    have hαμ : r.bel (r.revise Ψ {w, v}) ⊆ μᶜ := by
      intro x hx
      rcases (h.mem_bel_revise.1 hx).1 with rfl | rfl
      · exact hw
      · exact absurd ((h.mem_bel_revise.1 hx).2 w (by simp))
          (((ord Ψ).lt_iff_le_not_ge _ _).1 hlt).2
    have hnvw : ¬ (ord (r.revise Ψ μ)).le v w := fun hvw ↦
      hC Ψ μ {w, v} hα hαμ (by rw [Set.pair_comm]; exact h.mem_bel_revise_pair.2 hvw) hv.1
    exact ((ord _).lt_iff_le_not_ge _ _).2 ⟨((h.total _).total w v).resolve_right hnvw, hnvw⟩
  · intro hCR Ψ μ α hα hαμ x hx hxμ
    have hx' := h.mem_bel_revise.1 hx
    obtain ⟨u, hu⟩ := h.isAGM.consistency Ψ α ⟨x, hx'.1⟩
    have hu' := h.mem_bel_revise.1 hu
    have hlt : (ord Ψ).lt u x := ((ord Ψ).lt_iff_le_not_ge _ _).2
      ⟨hu'.2 x hx'.1, fun hxu ↦ hαμ (h.mem_bel_revise.2
        ⟨hx'.1, fun y hy ↦ (ord Ψ).le_trans _ _ _ hxu (hu'.2 y hy)⟩) hxμ⟩
    exact (((ord _).lt_iff_le_not_ge _ _).1
      (hCR Ψ μ u (hαμ hu) x ⟨hxμ, fun hxB ↦ hα hxB hx'.1⟩ hlt)).2 (hx'.2 u hu'.1)

/-- Boutilier's postulate (CB) is postulates (C1)–(C6) together, the absolute minimisation of
change in conditional beliefs of Section 7. -/
theorem Faithful.cb_iff_c1_c2_c3_c4_c5_c6 {ord : S → Preorder W} (h : r.Faithful ord) :
    r.CB ↔ r.C1 ∧ r.C2 ∧ r.C3 ∧ r.C4 ∧ r.C5 ∧ r.C6 := by
  simp only [h.cb_iff, h.c1_iff, h.c2_iff, h.c3_iff, h.c4_iff, h.c5_iff, h.c6_iff, ← forall_and]
  refine forall₂_congr fun Ψ μ ↦ ?_
  have hB {w} : w ∈ r.bel (r.revise Ψ μ) ↔ w ∈ μ ∧ ∀ y ∈ μ, (ord Ψ).le w y := h.mem_bel_revise
  have hBμ {w} (hw : w ∈ r.bel (r.revise Ψ μ)) : w ∈ μ := (hB.1 hw).1
  have hlt {p : Preorder W} (hp : Std.Total p.le) {w v : W} (hwv : ¬ p.le w v) : p.lt v w :=
    (p.lt_iff_le_not_ge _ _).2 ⟨(hp.total v w).resolve_right hwv, hwv⟩
  constructor
  · intro hA
    refine ⟨fun w hw v hv ↦ ?_, fun w hw v hv ↦ hA w (mt hBμ hw) v (mt hBμ hv),
      fun w hw v hv hwv ↦ ?_, fun w hw v hv hwv ↦ ?_, fun w hw v hv ↦
        (hA w (mt hBμ hw) v hv.2).1, fun w hw v hv ↦ (hA.lt_iff (mt hBμ hw) hv.2).1⟩
    · by_cases hwB : w ∈ r.bel (r.revise Ψ μ)
      · refine iff_of_true ((hB.1 hwB).2 v hv) ?_
        by_cases hvB : v ∈ r.bel (r.revise Ψ μ)
        exacts [(h.equiv_of_mem _ w v hwB hvB).1, h.le_of_mem hwB hvB]
      by_cases hvB : v ∈ r.bel (r.revise Ψ μ)
      · exact iff_of_false (fun hwv ↦ hwB (hB.2 ⟨hw, fun y hy ↦
          (ord Ψ).le_trans _ _ _ hwv ((hB.1 hvB).2 y hy)⟩)) (h.not_le_of_mem hvB hwB)
      · exact hA w hwB v hvB
    · by_cases hwB : w ∈ r.bel (r.revise Ψ μ)
      · exact h.lt_of_mem _ w v hwB (mt hBμ hv)
      · exact (hA.lt_iff hwB (mt hBμ hv)).1 hwv
    · by_cases hwB : w ∈ r.bel (r.revise Ψ μ)
      · exact h.le_of_mem hwB (mt hBμ hv)
      · exact (hA w hwB v (mt hBμ hv)).1 hwv
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩ w hw v hv
    by_cases hwμ : w ∈ μ <;> by_cases hvμ : v ∈ μ
    · exact h1 w hwμ v hvμ
    · exact ⟨h4 w hwμ v hvμ, fun hq ↦ by_contra fun hp ↦ (((ord _).lt_iff_le_not_ge _ _).1
        (h6 v hvμ w ⟨hwμ, hw⟩ (hlt (h.total Ψ) hp))).2 hq⟩
    · exact ⟨h5 w hwμ v ⟨hvμ, hv⟩, fun hq ↦ by_contra fun hp ↦ (((ord _).lt_iff_le_not_ge _ _).1
        (h3 v hvμ w hwμ (hlt (h.total Ψ) hp))).2 hq⟩
    · exact h2 w hwμ v hvμ

end Revision

/-! ### Spohn's revision of rankings -/

section Spohn

open RankingFunction

variable (κ : W → ℕ) (μ : Set W)

open Classical in
/-- Spohn's revision shifts the `μ`-worlds down so that the best reach rank `0` and the others
up by one, which makes the evidence one degree more plausible than it was implausible. -/
noncomputable def spohn : W → ℕ := fun w ↦ if w ∈ μ then aPart κ μ w else κ w + 1

/-- Spohn's revision is an operator on rankings whose belief sets are the rank-`0` worlds. -/
noncomputable def spohnRevision (W : Type*) : Revision (W → ℕ) W where
  bel κ := {w | κ w = 0}
  revise := spohn

/-- A revision of rankings that takes the `μ`-worlds to their `μ`-part and leaves the rest
disbelieved is represented by the rankings' own orderings. -/
theorem faithful_lift {f : (W → ℕ) → Set W → W → ℕ}
    (hμ : ∀ κ μ, ∀ w ∈ μ, f κ μ w = aPart κ μ w) (hν : ∀ κ μ, ∀ w ∉ μ, 0 < f κ μ w) :
    Revision.Faithful ⟨fun κ ↦ {w | κ w = 0}, f⟩ (fun κ ↦ Preorder.lift κ) where
  total κ := Preorder.total_lift κ
  wellFounded κ := Preorder.wellFounded_lt_lift κ
  equiv_of_mem κ w v hw hv := by
    simp only [Set.mem_ofPred_eq] at hw hv
    exact ⟨by simp [hw, hv], by simp [hw, hv]⟩
  lt_of_mem κ w v hw hv := by
    simp only [Set.mem_ofPred_eq] at hw hv
    exact (Preorder.lift_lt_iff κ).2 (by omega)
  bel_revise κ μ := by
    ext w
    simp only [Set.mem_ofPred_eq, Preorder.mem_minimals_lift]
    by_cases hw : w ∈ μ
    · rw [hμ κ μ w hw, aPart]
      constructor
      · intro h
        exact ⟨hw, fun y hy ↦ (Nat.sub_eq_zero_iff_le.1 h).trans (toNat_rank_le κ hy)⟩
      · rintro ⟨-, h⟩
        obtain ⟨u, hu, e⟩ := exists_apply_eq_rank κ ⟨w, hw⟩
        exact Nat.sub_eq_zero_iff_le.2 (by rw [← e, ENat.toNat_natCast]; exact h u hu)
    · exact ⟨fun h ↦ absurd h (hν κ μ w hw).ne', fun h ↦ absurd h.1 hw⟩

/-- Taking the `μ`-worlds to their `μ`-part preserves their ordering. -/
theorem agreesOn_lift {f : (W → ℕ) → Set W → W → ℕ}
    (hμ : ∀ κ μ, ∀ w ∈ μ, f κ μ w = aPart κ μ w) :
    AgreesOn (Preorder.lift κ) (Preorder.lift (f κ μ)) μ := fun w hw v hv ↦ by
  simp only [Preorder.lift_le_iff, hμ κ μ w hw, hμ κ μ v hv, aPart]
  have h₁ := toNat_rank_le κ hw
  have h₂ := toNat_rank_le κ hv
  constructor <;> intro <;> omega

theorem spohn_of_mem {w : W} (hw : w ∈ μ) : spohn κ μ w = aPart κ μ w := by
  simp [spohn, hw]

theorem spohn_of_notMem {w : W} (hw : w ∉ μ) : spohn κ μ w = κ w + 1 := by
  simp [spohn, hw]

/-- The rankings' orderings faithfully represent Spohn's revision (Lemma 2). -/
theorem spohnRevision_faithful :
    (spohnRevision W).Faithful (fun κ ↦ Preorder.lift κ) :=
  faithful_lift (fun κ μ _ hw ↦ spohn_of_mem κ μ hw)
    (fun κ μ _ hw ↦ by rw [spohn_of_notMem κ μ hw]; exact Nat.succ_pos _)

/-- Spohn's revision satisfies condition (CR1), the first part of Lemma 3. -/
theorem spohn_agreesOn : AgreesOn (Preorder.lift κ) (Preorder.lift (spohn κ μ)) μ :=
  agreesOn_lift κ μ fun κ μ _ hw ↦ spohn_of_mem κ μ hw

/-- Spohn's revision satisfies condition (CR2), the second part of Lemma 3. -/
theorem spohn_agreesOn_compl :
    AgreesOn (Preorder.lift κ) (Preorder.lift (spohn κ μ)) μᶜ := fun w hw v hv ↦ by
  simp only [Preorder.lift_le_iff, spohn_of_notMem κ μ hw, spohn_of_notMem κ μ hv]
  omega

/-- Spohn's revision satisfies condition (CR3), the third part of Lemma 3. -/
theorem spohn_preservesLt :
    PreservesLt (Preorder.lift κ) (Preorder.lift (spohn κ μ)) μ μᶜ := fun w hw v hv h ↦ by
  rw [Preorder.lift_lt_iff] at h ⊢
  rw [spohn_of_mem κ μ hw, spohn_of_notMem κ μ hv, aPart]
  omega

/-- Spohn's revision satisfies condition (CR4), the fourth part of Lemma 3. -/
theorem spohn_preservesLe :
    PreservesLe (Preorder.lift κ) (Preorder.lift (spohn κ μ)) μ μᶜ := fun w hw v hv h ↦ by
  rw [Preorder.lift_le_iff] at h ⊢
  rw [spohn_of_mem κ μ hw, spohn_of_notMem κ μ hv, aPart]
  omega

/-- Spohn's revision satisfies the AGM postulates (Theorem 5). -/
theorem spohnRevision_isAGM : (spohnRevision W).IsAGM :=
  spohnRevision_faithful.isAGM

/-- Spohn's revision satisfies (C1) (Theorem 5). -/
theorem spohnRevision_c1 : (spohnRevision W).C1 :=
  spohnRevision_faithful.c1_iff.2 spohn_agreesOn

/-- Spohn's revision satisfies (C2) (Theorem 5). -/
theorem spohnRevision_c2 : (spohnRevision W).C2 :=
  spohnRevision_faithful.c2_iff.2 spohn_agreesOn_compl

/-- Spohn's revision satisfies (C3) (Theorem 5). -/
theorem spohnRevision_c3 : (spohnRevision W).C3 :=
  spohnRevision_faithful.c3_iff.2 spohn_preservesLt

/-- Spohn's revision satisfies (C4) (Theorem 5). -/
theorem spohnRevision_c4 : (spohnRevision W).C4 :=
  spohnRevision_faithful.c4_iff.2 spohn_preservesLe

/-- On a ranking function, Spohn's revision by `A` is conditionalization on `A` at the firmness
`κ(Aᶜ) + 1`. -/
theorem spohn_eq_conditionα (κ : RankingFunction W) {A : Set W} (hA : A.Nonempty) :
    spohn κ A = κ.conditionα A hA ((rank κ Aᶜ).toNat + 1) := by
  funext w
  by_cases hw : w ∈ A
  · rw [κ.conditionα_of_mem _ _ hw, spohn_of_mem κ A hw]
  · have := toNat_rank_le κ (A := Aᶜ) hw
    rw [κ.conditionα_of_notMem _ _ hw, spohn_of_notMem κ A hw, aPart]
    omega

/-- The conditional beliefs of a ranking function under Spohn's revision are the consequences
of its ranked model. -/
theorem _root_.RankingFunction.accepts_spohnRevision_iff (κ : RankingFunction W) {A B : Set W} :
    (spohnRevision W).Accepts κ A B ↔ κ.Entails A B :=
  spohnRevision_faithful.accepts_iff

end Spohn

end BeliefRevision
