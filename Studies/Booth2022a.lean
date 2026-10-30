module

public import Linglib.Semantics.Modality.MinimalCovering
public import Linglib.Logic.Modal.Defs
public import Studies.Simons2005

/-!
# Booth (2022a): Independent alternatives: Ross's puzzle and free choice

[booth-2022a] explains Ross's puzzle and free choice permission by the Independence inferences:
accepting `□(p ∨ q)` or `◇(p ∨ q)` commits a speaker to `◇(p ∧ ¬q)` and `◇(q ∧ ¬p)`, each disjunct
an option independently of the other. These are strictly stronger than the Diversity inferences
`◇p`, `◇q` of the standard analyses (§4), and they amount to the disjuncts' truth sets forming a
minimal cover of the relevant worlds, where the Diversity inferences need only a super cover (§5):
`◇(p ∨ q)` is true [exactly where both Independence inferences are](##truth_diamond_disj_eq_inter),
and `□(p ∨ q)` is [the orthodox `□!(p ∨ q)` together with `◇(p ∨ q)`](##truth_box_disj_eq_inter).
The minimal covering semantics of §6 validates them for inquisitive propositions; §7 notes that
its unilateral version loses the duality of the modals and the distribution of negated modals over
disjunction, and recovers both with bilateral propositions; §8 shows the truth-value gaps this
creates are well placed. The semantics is the theory-layer `MinimalCovering`.

The super covers of [simons-2005] validate the Diversity inferences without the Independence
inferences (fn. 22). Among the pragmatic strengthenings of the super cover that Simons considers,
the Alternativeness constraint [is the minimal cover](##isMinCover_iff_alternativeness), so
Booth's semantics makes Alternativeness part of the truth conditions: the cases where some of
Simons's informants judge a modal disjunction false although her truth conditions make it true
[are not true here](##not_mem_truth_disj_of_inter_subset).

* Facts 1–7 of the appendix: `box_independence_left`, …, `diamond_independence_right` (Fact 1);
  `box_conditional_left`, …, `diamond_conditional_right` (Fact 2); `Figures.ross_invalid` (Fact 3);
  `free_choice` (Fact 4); `box_eq_neg_diamond_neg`, `diamond_eq_neg_box_neg` (Fact 5);
  `impossibility_distribution_left`, `impossibility_distribution_right` (Fact 6);
  `unnecessity_distribution_left`, `unnecessity_distribution_right` (Fact 7).
* §8: `isCompl_truth_falsity` (the modal-free fragment is classical), `ross_gap`,
  `free_choice_gap`, `independence_gap` and the card example `CardGame.gap`;
  `Figures.not_contraposition`: entailment is not closed under contraposition, the formal content
  of the "diplomatic resolution".

## Implementation notes

* Validity over the admissible models of Def 1 is universal quantification over worlds,
  accessibility and valuation, with the hypothesis `IncompRel (· ⊆ ·) (V p) (V q)` for the two
  atoms each fact mentions. Def 1 as printed quantifies over all `p, q ∈ At`, which no model
  satisfies for `p = q`; it is read here for the pair at hand.
* The appendix prints `[!φ] = (℘(info([φ]⁺)), ℘(info([ψ]⁻)))`, with `ψ` in the negative
  coordinate; this is a typo for `φ`, the only reading on which `!φ` is a bilateral proposition,
  and `MinimalCovering.bang` follows it.
* Fact 3 is non-validity: some admissible model has `□p` true and `□(p ∨ q)` not. The stronger
  pointwise claim of §8, that `□p` makes `□(p ∨ q)` neither true nor false, is `ross_gap`.

## References

* [booth-2022a]
* [simons-2005]
* [ciardelli-groenendijk-roelofsen-2018]
* [kratzer-1991]
-/

@[expose] public section

namespace Booth2022a

open MinimalCovering Question

variable {W At : Type*} (V : At → Set W) (R : W → Set W) {p q : At}

/-! ### Minimal covers and the Independence inferences (§§4–6) -/

/-- The target truth conditions of `□(p ∨ q)` (§5): the truth sets of the disjuncts minimally
cover the relevant worlds. -/
theorem truth_box_disj (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    truth (Formula.eval V R (.box (.disj (.atom p) (.atom q)))) =
      {w | IsMinCover {V p, V q} (R w)} := by
  change truth (necessity R (atom (V p) ⊔ atom (V q))) = _
  rw [truth_necessity, alt_sup_atom h]

/-- The target truth conditions of `◇(p ∨ q)` (§5): the truth sets of the disjuncts minimally
cover a nonempty set of relevant worlds. -/
theorem truth_diamond_disj (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    truth (Formula.eval V R (.diamond (.disj (.atom p) (.atom q)))) =
      {w | ∃ R' ⊆ R w, R'.Nonempty ∧ IsMinCover {V p, V q} R'} := by
  change truth (possibility R (atom (V p) ⊔ atom (V q))) = _
  rw [truth_possibility, alt_sup_atom h]

theorem truth_box_atom (p : At) :
    truth (Formula.eval V R (.box (.atom p))) = {w | (R w).Nonempty ∧ R w ⊆ V p} :=
  truth_necessity_of_alt_eq_singleton R _ (alt_atom_pro _)

theorem truth_diamond_atom (p : At) :
    truth (Formula.eval V R (.diamond (.atom p))) = {w | (R w ∩ V p).Nonempty} :=
  truth_possibility_of_alt_eq_singleton R _ (alt_atom_pro _)

theorem truth_diamond_conj_neg (p q : At) :
    truth (Formula.eval V R (.diamond (.conj (.atom p) (.neg (.atom q))))) =
      {w | (R w ∩ (V p \ V q)).Nonempty} :=
  truth_possibility_of_alt_eq_singleton R _ (alt_inf_compl_atom _ _)

/-- `◇(p ∨ q)` is true exactly where both Independence inferences are (§5): some relevant world is
a `p`-without-`q` world and some is a `q`-without-`p` world. -/
theorem truth_diamond_disj_eq_inter (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    truth (Formula.eval V R (.diamond (.disj (.atom p) (.atom q)))) =
      truth (Formula.eval V R (.diamond (.conj (.atom p) (.neg (.atom q))))) ∩
        truth (Formula.eval V R (.diamond (.conj (.atom q) (.neg (.atom p))))) := by
  rw [truth_diamond_disj V R h, truth_diamond_conj_neg, truth_diamond_conj_neg]
  ext w
  simp [exists_isMinCover_iff, Set.pair_sdiff_left h.ne, Set.pair_sdiff_right h.ne]

/-- `□(p ∨ q)` is the orthodox necessity `□!(p ∨ q)` together with `◇(p ∨ q)` (§5): every relevant
world is a `p ∨ q`-world, and the disjuncts are independent alternatives among them. -/
theorem truth_box_disj_eq_inter (p q : At) :
    truth (Formula.eval V R (.box (.disj (.atom p) (.atom q)))) =
      truth (Formula.eval V R (.box (.bang (.disj (.atom p) (.atom q))))) ∩
        truth (Formula.eval V R (.diamond (.disj (.atom p) (.atom q)))) :=
  truth_necessity_eq_inter R _ ((isNormal_ofSet (V p)).sup (isNormal_ofSet (V q)))

/-- The meta-linguistic Diversity inferences follow (§4): the relevant worlds meet both truth
sets. -/
theorem box_diversity (h : IncompRel (· ⊆ ·) (V p) (V q)) {w : W}
    (hw : w ∈ truth (Formula.eval V R (.box (.disj (.atom p) (.atom q))))) :
    (R w ∩ V p).Nonempty ∧ (R w ∩ V q).Nonempty := by
  rw [truth_box_disj_eq_inter V R p q, truth_diamond_disj_eq_inter V R h, truth_diamond_conj_neg,
    truth_diamond_conj_neg] at hw
  exact ⟨hw.2.1.mono (Set.inter_subset_inter_right _ Set.sdiff_subset),
    hw.2.2.mono (Set.inter_subset_inter_right _ Set.sdiff_subset)⟩

/-- `◇(p ∧ ¬q)` entails `◇p`, so the Independence inferences are at least as strong as the
Diversity inferences (§4); `Figures.diversity_without_independence` shows they are stronger. -/
theorem truth_diamond_conj_neg_subset (p q : At) :
    truth (Formula.eval V R (.diamond (.conj (.atom p) (.neg (.atom q))))) ⊆
      truth (Formula.eval V R (.diamond (.atom p))) := by
  rw [truth_diamond_conj_neg, truth_diamond_atom]
  exact fun _ hw ↦ hw.mono (Set.inter_subset_inter_right _ Set.sdiff_subset)

/-- Over `!φ`, necessity is the universal modal over the relevant worlds when they are nonempty
([kratzer-1991]; §6, fn. 13). -/
theorem truth_necessity_bang (φ : Kalman (Question W)) :
    truth (necessity R (bang φ)) =
      {w | (R w).Nonempty ∧ ModalLogic.Box (.ofSuccessors R) (· ∈ truth φ) w} :=
  truth_necessity_of_alt_eq_singleton R _ (alt_bang_pro φ)

/-- Over `!φ`, possibility is the orthodox existential modal over the relevant worlds (§6). -/
theorem truth_possibility_bang (φ : Kalman (Question W)) :
    truth (possibility R (bang φ)) =
      {w | ModalLogic.Diamond (.ofSuccessors R) (· ∈ truth φ) w} := by
  rw [truth_possibility_of_alt_eq_singleton R _ (alt_bang_pro φ)]
  rfl

/-- Flexibility (§6, (16)–(17)): `□p` entails `□!(p ∨ q)`, in every model. -/
theorem box_bang_disj (p q : At) :
    truth (Formula.eval V R (.box (.atom p))) ⊆
      truth (Formula.eval V R (.box (.bang (.disj (.atom p) (.atom q))))) := by
  rw [truth_box_atom]
  change _ ⊆ truth (necessity R (bang (atom (V p) ⊔ atom (V q))))
  rw [truth_necessity_of_alt_eq_singleton R _ (alt_bang_pro _)]
  refine fun _ ⟨hne, hsub⟩ ↦ ⟨hne, fun _ hv ↦ ?_⟩
  rw [truth_sup, truth_atom, truth_atom]
  exact .inl (hsub hv)

/-! ### The unilateral semantics loses duality and distribution (§7)

In the unilateral semantics of §6 a sentence denotes one inquisitive proposition, negation is the
pseudocomplement `ᶜ` of `Question W` (the states disjoint from the informative content), and the
modals are `box` and `diamond`. Booth's scenario: in all relevant worlds Alicia burns the letter.
Then `¬◇(M ∨ B)` is true, since there is no relevant mailing-without-burning world, yet `◇B` is true
and `□¬(M ∨ B)` is not. The worlds record whether Alicia mails (`M`) and whether she burns (`B`)
the letter; the relevant worlds are the two burning worlds, one of them a mailing world. -/

namespace Unilateral

/-- Alicia mails the letter. -/
def vM : Set (Bool × Bool) := {w | w.1 = true}

/-- Alicia burns the letter. -/
def vB : Set (Bool × Bool) := {w | w.2 = true}

/-- The relevant worlds are the burning worlds. -/
def rB : Bool × Bool → Set (Bool × Bool) := fun _ ↦ vB

theorem vM_ne_vB : vM ≠ vB := fun h ↦ by simpa [vM, vB] using Set.ext_iff.1 h (true, false)

theorem alt_disj : alt (ofSet vM ⊔ ofSet vB) = {vM, vB} :=
  alt_ofSet_sup_ofSet (fun h ↦ by simpa [vB] using h (show (true, false) ∈ vM from rfl))
    (fun h ↦ by simpa [vM] using h (show (false, true) ∈ vB from rfl))

/-- `¬◇(M ∨ B)` is true: no nonempty set of burning worlds contains a mailing-without-burning
world, as a minimal cover by `{M, B}` would need. -/
theorem not_dia_disj (w : Bool × Bool) : w ∈ (diamond rB (ofSet vM ⊔ ofSet vB))ᶜ.info := by
  rw [info_compl, info_diamond, alt_disj]
  rintro ⟨R', hR', -, hmc⟩
  obtain ⟨-, ⟨v, hv, -, hvB⟩, -⟩ := (isMinCover_pair_iff_inter_sdiff vM_ne_vB).1 hmc
  exact hvB (hR' hv)

/-- `¬◇B` is not true: some relevant world is a burning world. Impossibility Distribution (19)
fails. -/
theorem dia_right (w : Bool × Bool) : w ∉ (diamond rB (ofSet vB))ᶜ.info := by
  rw [info_compl, info_diamond, alt_ofSet, Set.notMem_compl_iff]
  have hB : vB.Nonempty := ⟨(true, true), rfl⟩
  exact ⟨vB, subset_rfl, hB, isMinCover_singleton_iff.2 ⟨hB, subset_rfl⟩⟩

/-- `□¬(M ∨ B)` is not true while `¬◇(M ∨ B)` is: duality (21) fails. -/
theorem box_neg_disj (w : Bool × Bool) : w ∉ (box rB (ofSet vM ⊔ ofSet vB)ᶜ).info := by
  rw [info_box, compl_eq, alt_ofSet, Set.mem_ofPred_eq,
    isMinCover_singleton_iff, info_sup, info_ofSet, info_ofSet]
  intro h
  exact h.2 (show (true, true) ∈ rB w from rfl) (Or.inr rfl)

/-- `¬□(M ∨ B)` is true: the burning worlds hold no mailing-without-burning world. -/
theorem not_box_disj (w : Bool × Bool) : w ∈ (box rB (ofSet vM ⊔ ofSet vB))ᶜ.info := by
  rw [info_compl, info_box, alt_disj]
  intro hmc
  obtain ⟨-, ⟨v, hv, -, hvB⟩, -⟩ := (isMinCover_pair_iff_inter_sdiff vM_ne_vB).1 hmc
  exact hvB hv

/-- `¬□B` is not true: all relevant worlds are burning worlds. Unnecessity Distribution (20)
fails. -/
theorem box_right (w : Bool × Bool) : w ∉ (box rB (ofSet vB))ᶜ.info := by
  rw [info_compl, info_box, alt_ofSet, Set.notMem_compl_iff]
  exact isMinCover_singleton_iff.2 ⟨⟨(true, true), rfl⟩, subset_rfl⟩

theorem bilateral_not_neg_diamond_disj (w : Bool × Bool) :
    w ∉ truth (possibility rB (atom vM ⊔ atom vB))ᶜ := by
  rw [truth_compl, falsity_possibility, alt_sup_atom_con, Set.mem_ofPred_eq,
    isMinCover_singleton_iff]
  intro h
  exact (h.2 (show (true, true) ∈ rB w from rfl)).2 rfl

end Unilateral

/-! ### The facts of the appendix -/

section Facts

variable {V R}

/-- **Fact 1**, `□(p ∨ q) ⊨ ◇(p ∧ ¬q)`. -/
theorem box_independence_left (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    truth (Formula.eval V R (.box (.disj (.atom p) (.atom q)))) ⊆
      truth (Formula.eval V R (.diamond (.conj (.atom p) (.neg (.atom q))))) :=
  (truth_box_disj_eq_inter V R p q).le.trans
    (Set.inter_subset_right.trans
      ((truth_diamond_disj_eq_inter V R h).le.trans Set.inter_subset_left))

-- Fact 1
theorem box_independence_right (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    truth (Formula.eval V R (.box (.disj (.atom p) (.atom q)))) ⊆
      truth (Formula.eval V R (.diamond (.conj (.atom q) (.neg (.atom p))))) :=
  (truth_box_disj_eq_inter V R p q).le.trans
    (Set.inter_subset_right.trans
      ((truth_diamond_disj_eq_inter V R h).le.trans Set.inter_subset_right))

-- Fact 1
theorem diamond_independence_left (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    truth (Formula.eval V R (.diamond (.disj (.atom p) (.atom q)))) ⊆
      truth (Formula.eval V R (.diamond (.conj (.atom p) (.neg (.atom q))))) :=
  (truth_diamond_disj_eq_inter V R h).le.trans Set.inter_subset_left

/-- **Fact 1**, `◇(p ∨ q) ⊨ ◇(q ∧ ¬p)`. -/
theorem diamond_independence_right (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    truth (Formula.eval V R (.diamond (.disj (.atom p) (.atom q)))) ⊆
      truth (Formula.eval V R (.diamond (.conj (.atom q) (.neg (.atom p))))) :=
  (truth_diamond_disj_eq_inter V R h).le.trans Set.inter_subset_right

theorem updateAccess_neg_atom (p : At) (w : W) :
    updateAccess R (Formula.eval V R (.neg (.atom p))) w = R w \ V p := by
  change R w ∩ truth (atom (V p))ᶜ = _
  rw [truth_compl, falsity_atom]
  rfl

/-- **Fact 2**, `□(p ∨ q) ⊨ ¬p → □q`. -/
theorem box_conditional_left (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    truth (Formula.eval V R (.box (.disj (.atom p) (.atom q)))) ⊆
      truth (Formula.eval V R (.cond (.neg (.atom p)) (.box (.atom q)))) := by
  intro w hw
  have hmc := hw
  rw [truth_box_disj V R h, Set.mem_ofPred_eq,
    isMinCover_pair_iff_inter_sdiff h.ne] at hmc
  change w ∈ truth (Formula.eval V (updateAccess R (Formula.eval V R (.neg (.atom p))))
    (.box (.atom q)))
  rw [truth_box_atom, Set.mem_ofPred_eq, updateAccess_neg_atom]
  obtain ⟨v, hvR, -, hvp⟩ := hmc.2.2
  exact ⟨⟨v, hvR, hvp⟩, fun u hu ↦ (hmc.1 hu.1).resolve_left hu.2⟩

-- Fact 2
theorem box_conditional_right (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    truth (Formula.eval V R (.box (.disj (.atom p) (.atom q)))) ⊆
      truth (Formula.eval V R (.cond (.neg (.atom q)) (.box (.atom p)))) := by
  intro w hw
  rw [truth_box_disj V R h, Set.mem_ofPred_eq,
    isMinCover_pair_iff_inter_sdiff h.ne] at hw
  change w ∈ truth (Formula.eval V (updateAccess R (Formula.eval V R (.neg (.atom q))))
    (.box (.atom p)))
  rw [truth_box_atom, Set.mem_ofPred_eq, updateAccess_neg_atom]
  obtain ⟨v, hvR, -, hvq⟩ := hw.2.1
  exact ⟨⟨v, hvR, hvq⟩, fun u hu ↦ (hw.1 hu.1).resolve_right hu.2⟩

-- Fact 2
theorem diamond_conditional_left (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    truth (Formula.eval V R (.diamond (.disj (.atom p) (.atom q)))) ⊆
      truth (Formula.eval V R (.cond (.neg (.atom p)) (.diamond (.atom q)))) := by
  intro w hw
  change w ∈ truth (Formula.eval V (updateAccess R (Formula.eval V R (.neg (.atom p))))
    (.diamond (.atom q)))
  rw [truth_diamond_atom, Set.mem_ofPred_eq, updateAccess_neg_atom]
  have hind := diamond_independence_right h hw
  rw [truth_diamond_conj_neg] at hind
  obtain ⟨v, hvR, hvq, hvp⟩ := hind
  exact ⟨v, ⟨hvR, hvp⟩, hvq⟩

/-- **Fact 2**, `◇(p ∨ q) ⊨ ¬q → ◇p`. -/
theorem diamond_conditional_right (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    truth (Formula.eval V R (.diamond (.disj (.atom p) (.atom q)))) ⊆
      truth (Formula.eval V R (.cond (.neg (.atom q)) (.diamond (.atom p)))) := by
  intro w hw
  change w ∈ truth (Formula.eval V (updateAccess R (Formula.eval V R (.neg (.atom q))))
    (.diamond (.atom p)))
  rw [truth_diamond_atom, Set.mem_ofPred_eq, updateAccess_neg_atom]
  have hind := diamond_independence_left h hw
  rw [truth_diamond_conj_neg] at hind
  obtain ⟨v, hvR, hvp, hvq⟩ := hind
  exact ⟨v, ⟨hvR, hvq⟩, hvp⟩

/-- **Fact 4**, Free Choice: `◇(p ∨ q) ⊨ ◇p`. -/
theorem free_choice (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    truth (Formula.eval V R (.diamond (.disj (.atom p) (.atom q)))) ⊆
      truth (Formula.eval V R (.diamond (.atom p))) :=
  (diamond_independence_left h).trans (truth_diamond_conj_neg_subset V R p q)

theorem free_choice_right (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    truth (Formula.eval V R (.diamond (.disj (.atom p) (.atom q)))) ⊆
      truth (Formula.eval V R (.diamond (.atom q))) :=
  (diamond_independence_right h).trans (truth_diamond_conj_neg_subset V R q p)

variable (V R)

/-- **Fact 5**, modal duality: `[□φ] = [¬◇¬φ]`. -/
theorem box_eq_neg_diamond_neg (φ : Formula At) :
    Formula.eval V R (.box φ) = Formula.eval V R (.neg (.diamond (.neg φ))) :=
  rfl

/-- **Fact 5**, modal duality: `[◇φ] = [¬□¬φ]`. -/
theorem diamond_eq_neg_box_neg (φ : Formula At) :
    Formula.eval V R (.diamond φ) = Formula.eval V R (.neg (.box (.neg φ))) :=
  rfl

/-- **Fact 6**, Impossibility Distribution: `¬◇(p ∨ q) ⊨ ¬◇p`. -/
theorem impossibility_distribution_left (p q : At) :
    truth (Formula.eval V R (.neg (.diamond (.disj (.atom p) (.atom q))))) ⊆
      truth (Formula.eval V R (.neg (.diamond (.atom p)))) := by
  change falsity (possibility R (atom (V p) ⊔ atom (V q))) ⊆ falsity (possibility R (atom (V p)))
  rw [falsity_possibility_of_alt_eq_singleton R _ (alt_sup_atom_con _ _),
    falsity_possibility_of_alt_eq_singleton R _ (alt_atom_con _)]
  exact fun _ ⟨hne, hsub⟩ ↦ ⟨hne, hsub.trans Set.inter_subset_left⟩

/-- **Fact 6**, Impossibility Distribution: `¬◇(p ∨ q) ⊨ ¬◇q`. -/
theorem impossibility_distribution_right (p q : At) :
    truth (Formula.eval V R (.neg (.diamond (.disj (.atom p) (.atom q))))) ⊆
      truth (Formula.eval V R (.neg (.diamond (.atom q)))) := by
  change falsity (possibility R (atom (V p) ⊔ atom (V q))) ⊆ falsity (possibility R (atom (V q)))
  rw [falsity_possibility_of_alt_eq_singleton R _ (alt_sup_atom_con _ _),
    falsity_possibility_of_alt_eq_singleton R _ (alt_atom_con _)]
  exact fun _ ⟨hne, hsub⟩ ↦ ⟨hne, hsub.trans Set.inter_subset_right⟩

/-- **Fact 7**, Unnecessity Distribution: `¬□(p ∨ q) ⊨ ¬□p`. -/
theorem unnecessity_distribution_left (p q : At) :
    truth (Formula.eval V R (.neg (.box (.disj (.atom p) (.atom q))))) ⊆
      truth (Formula.eval V R (.neg (.box (.atom p)))) := by
  change falsity (necessity R (atom (V p) ⊔ atom (V q))) ⊆ falsity (necessity R (atom (V p)))
  rw [falsity_necessity_of_alt_eq_singleton R _ (alt_sup_atom_con _ _),
    falsity_necessity_of_alt_eq_singleton R _ (alt_atom_con _)]
  exact fun _ hw ↦ hw.mono (Set.inter_subset_inter_right _ Set.inter_subset_left)

/-- **Fact 7**, Unnecessity Distribution: `¬□(p ∨ q) ⊨ ¬□q`. -/
theorem unnecessity_distribution_right (p q : At) :
    truth (Formula.eval V R (.neg (.box (.disj (.atom p) (.atom q))))) ⊆
      truth (Formula.eval V R (.neg (.box (.atom q)))) := by
  change falsity (necessity R (atom (V p) ⊔ atom (V q))) ⊆ falsity (necessity R (atom (V q)))
  rw [falsity_necessity_of_alt_eq_singleton R _ (alt_sup_atom_con _ _),
    falsity_necessity_of_alt_eq_singleton R _ (alt_atom_con _)]
  exact fun _ hw ↦ hw.mono (Set.inter_subset_inter_right _ Set.inter_subset_right)

variable {V R}

/-- Dual Free Choice `¬□(p ∧ q) ⊨ ◇¬p` holds for incomparable atoms (fn. 32). -/
theorem dual_free_choice (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    truth (Formula.eval V R (.neg (.box (.conj (.atom p) (.atom q))))) ⊆
      truth (Formula.eval V R (.diamond (.neg (.atom p)))) := by
  have key : Formula.eval V R (.neg (.box (.conj (.atom p) (.atom q)))) =
      Formula.eval (fun a ↦ (V a)ᶜ) R (.diamond (.disj (.atom p) (.atom q))) := by
    change (necessity R (atom (V p) ⊓ atom (V q)))ᶜ = possibility R (atom (V p)ᶜ ⊔ atom (V q)ᶜ)
    rw [necessity_eq_compl_possibility_compl, InvolutiveCompl.compl_compl,
      InvolutiveCompl.compl_inf, compl_atom, compl_atom]
  have hc : IncompRel (· ⊆ ·) (V p)ᶜ (V q)ᶜ :=
    ⟨fun hs ↦ h.2 (Set.compl_subset_compl.1 hs), fun hs ↦ h.1 (Set.compl_subset_compl.1 hs)⟩
  rw [key]
  refine (free_choice (V := fun a ↦ (V a)ᶜ) (R := R) hc).trans_eq ?_
  change truth (possibility R (atom (V p)ᶜ)) = truth (possibility R (atom (V p))ᶜ)
  rw [compl_atom]

end Facts

/-! ### Truth-value gaps (§8) -/

/-- The modal-free sentences: those without `□` or `◇`. -/
def IsModalFree : Formula At → Prop
  | .atom _ => True
  | .neg φ => IsModalFree φ
  | .conj φ ψ => IsModalFree φ ∧ IsModalFree ψ
  | .disj φ ψ => IsModalFree φ ∧ IsModalFree ψ
  | .bang φ => IsModalFree φ
  | .cond φ ψ => IsModalFree φ ∧ IsModalFree ψ
  | .box _ => False
  | .diamond _ => False

/-- A modal-free sentence is false exactly where it is not true (§8). -/
theorem isCompl_truth_falsity (φ : Formula At) (hφ : IsModalFree φ) :
    IsCompl (truth (Formula.eval V R φ)) (falsity (Formula.eval V R φ)) := by
  induction φ generalizing R with
  | atom p =>
    simp only [Formula.eval, truth_atom, falsity_atom]
    exact isCompl_compl
  | neg φ ih => exact (ih R hφ).symm
  | conj φ ψ ihφ ihψ =>
    simp only [Formula.eval, truth_inf, falsity_inf]
    exact (ihφ R hφ.1).inf_sup (ihψ R hφ.2)
  | disj φ ψ ihφ ihψ =>
    simp only [Formula.eval, truth_sup, falsity_sup]
    exact (ihφ R hφ.1).sup_inf (ihψ R hφ.2)
  | bang φ ih =>
    simp only [Formula.eval, truth_bang, falsity_bang]
    exact ih R hφ
  | cond φ ψ _ ihψ => exact ihψ _ hφ.2
  | box φ _ => exact hφ.elim
  | diamond φ _ => exact hφ.elim

variable {V R}

/-- **The Ross gap** (§8, fn. 35): if `□p` is true, `□(p ∨ q)` is neither true nor false. -/
theorem ross_gap (h : IncompRel (· ⊆ ·) (V p) (V q)) {w : W}
    (hw : w ∈ truth (Formula.eval V R (.box (.atom p)))) :
    w ∉ truth (Formula.eval V R (.box (.disj (.atom p) (.atom q)))) ∧
      w ∉ falsity (Formula.eval V R (.box (.disj (.atom p) (.atom q)))) := by
  rw [truth_box_atom, Set.mem_ofPred_eq] at hw
  refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
  · rw [truth_box_disj V R h, Set.mem_ofPred_eq, isMinCover_pair_iff h.ne] at h'
    exact h'.2.1 hw.2
  · change w ∈ falsity (necessity R (atom (V p) ⊔ atom (V q))) at h'
    rw [falsity_necessity_of_alt_eq_singleton R _ (alt_sup_atom_con _ _)] at h'
    obtain ⟨v, hvR, hvp, -⟩ := h'
    exact hvp (hw.2 hvR)

/-- If `p` is possible and `q` is not, `◇(p ∨ q)` is neither true nor false (§8). -/
theorem free_choice_gap (h : IncompRel (· ⊆ ·) (V p) (V q)) {w : W}
    (hp : w ∈ truth (Formula.eval V R (.diamond (.atom p))))
    (hq : w ∉ truth (Formula.eval V R (.diamond (.atom q)))) :
    w ∉ truth (Formula.eval V R (.diamond (.disj (.atom p) (.atom q)))) ∧
      w ∉ falsity (Formula.eval V R (.diamond (.disj (.atom p) (.atom q)))) :=
  ⟨fun h' ↦ hq (free_choice_right h h'), fun h' ↦ Set.disjoint_left.1
    (disjoint_truth_falsity (Formula.eval V R (.diamond (.atom p)))) hp
    (impossibility_distribution_left V R p q h')⟩

/-- If `p` is possible but not independently of `q`, `◇(p ∨ q)` is neither true nor false (§8). -/
theorem independence_gap (h : IncompRel (· ⊆ ·) (V p) (V q)) {w : W}
    (hp : w ∈ truth (Formula.eval V R (.diamond (.atom p))))
    (hind : w ∉ truth (Formula.eval V R (.diamond (.conj (.atom p) (.neg (.atom q)))))) :
    w ∉ truth (Formula.eval V R (.diamond (.disj (.atom p) (.atom q)))) ∧
      w ∉ falsity (Formula.eval V R (.diamond (.disj (.atom p) (.atom q)))) :=
  ⟨fun h' ↦ hind (diamond_independence_left h h'), fun h' ↦ Set.disjoint_left.1
    (disjoint_truth_falsity (Formula.eval V R (.diamond (.atom p)))) hp
    (impossibility_distribution_left V R p q h')⟩

/-! #### The card game of (12)

The only permitted option is to take the ace and the ten of diamonds together. "You may take the
ace or the ten" (12) and its negation (12′) are both untrue. -/

namespace CardGame

/-- Whether the ace, and whether the ten, is taken. -/
def val : Bool → Set (Bool × Bool)
  | true => {w | w.1 = true}
  | false => {w | w.2 = true}

/-- The only permitted option: take both. -/
def acc : Bool × Bool → Set (Bool × Bool) := fun _ ↦ {(true, true)}

theorem incomp : IncompRel (· ⊆ ·) (val true) (val false) :=
  ⟨fun h ↦ by simpa [val] using h (show (true, false) ∈ val true from rfl),
    fun h ↦ by simpa [val] using h (show (false, true) ∈ val false from rfl)⟩

/-- (12) is neither true nor false. -/
theorem gap (w : Bool × Bool) :
    w ∉ truth (Formula.eval val acc (.diamond (.disj (.atom true) (.atom false)))) ∧
      w ∉ falsity (Formula.eval val acc (.diamond (.disj (.atom true) (.atom false)))) := by
  refine independence_gap incomp ?_ ?_
  · rw [truth_diamond_atom]
    exact ⟨(true, true), rfl, rfl⟩
  · rw [truth_diamond_conj_neg]
    rintro ⟨v, hvR, -, hv⟩
    rw [Set.mem_singleton_iff.1 hvR] at hv
    exact hv rfl

end CardGame

/-! ### Figures 1 and 2

Four worlds, the valuations of `p` and `q`. Where the relevant worlds are the three
`p ∨ q`-worlds, `{⟦p⟧, ⟦q⟧}` minimally covers them (Figure 2, Independence). Where they are the
two `p`-worlds, the pair is a super cover but not a minimal one (Figure 1): the Diversity
inferences hold without the Independence inferences, and the premises `□M`, `◇P` of the extended
Ross argument (8) are true while its conclusion is not. -/

namespace Figures

/-- Worlds: the truth values of `p` and `q`. -/
abbrev W4 := Bool × Bool

/-- `p` is true at the worlds whose first coordinate is `true`. -/
def vp : Set W4 := {w | w.1 = true}

/-- `q` is true at the worlds whose second coordinate is `true`. -/
def vq : Set W4 := {w | w.2 = true}

/-- The valuation: `true` is `p`, `false` is `q`. -/
def val : Bool → Set W4
  | true => vp
  | false => vq

/-- The relevant worlds are the three `p ∨ q`-worlds (Figure 2). -/
def r₃ : W4 → Set W4 := fun _ ↦ vp ∪ vq

/-- The relevant worlds are the two `p`-worlds (Figure 1). -/
def rP : W4 → Set W4 := fun _ ↦ vp

theorem incomp : IncompRel (· ⊆ ·) vp vq :=
  ⟨fun h ↦ absurd (h (show (true, false) ∈ vp from rfl)) (by simp [vq]),
    fun h ↦ absurd (h (show (false, true) ∈ vq from rfl)) (by simp [vp])⟩

theorem incomp_val : IncompRel (· ⊆ ·) (val true) (val false) := incomp

-- Figure 2
theorem isMinCover_r₃ : IsMinCover {vp, vq} (r₃ (true, true)) := by
  rw [isMinCover_pair_iff incomp.ne]
  refine ⟨subset_rfl, fun h ↦ ?_, fun h ↦ ?_⟩
  · exact absurd (h (show (false, true) ∈ r₃ (true, true) from .inr rfl)) (by simp [vp])
  · exact absurd (h (show (true, false) ∈ r₃ (true, true) from .inl rfl)) (by simp [vq])

/-- Figure 1: on the two `p`-worlds `{⟦p⟧, ⟦q⟧}` is a super cover but not a minimal one. -/
theorem diversity_without_independence :
    IsSuperCover {vp, vq} (rP (true, true)) ∧ ¬ IsMinCover {vp, vq} (rP (true, true)) :=
  ⟨isSuperCover_pair_iff.2 ⟨⟨(true, true), rfl, rfl⟩, ⟨(true, true), rfl, rfl⟩,
    Set.subset_union_left⟩,
    fun h ↦ ((isMinCover_pair_iff incomp.ne).1 h).2.1 subset_rfl⟩

-- Figure 2
theorem box_pOrQ :
    (true, true) ∈ truth (Formula.eval val r₃ (.box (.disj (.atom true) (.atom false)))) := by
  rw [truth_box_disj val r₃ incomp_val]
  exact isMinCover_r₃

-- Figure 1
theorem box_p : (true, true) ∈ truth (Formula.eval val rP (.box (.atom true))) := by
  rw [truth_box_atom]
  exact ⟨⟨(true, true), rfl⟩, subset_rfl⟩

-- Figure 1
theorem diamond_q : (true, true) ∈ truth (Formula.eval val rP (.diamond (.atom false))) := by
  rw [truth_diamond_atom]
  exact ⟨(true, true), rfl, rfl⟩

-- Figure 1
theorem not_diamond_qAndNotP :
    (true, true) ∉
      truth (Formula.eval val rP (.diamond (.conj (.atom false) (.neg (.atom true))))) := by
  rw [truth_diamond_conj_neg]
  rintro ⟨v, hvR, -, hv⟩
  exact hv hvR

-- (8), Figure 1
theorem extended_ross :
    (true, true) ∈ truth (Formula.eval val rP (.box (.atom true))) ∩
        truth (Formula.eval val rP (.diamond (.atom false))) ∧
      (true, true) ∉ truth (Formula.eval val rP (.box (.disj (.atom true) (.atom false)))) :=
  ⟨⟨box_p, diamond_q⟩, (ross_gap incomp_val box_p).1⟩

/-- **Fact 3**: the Ross inference `□p ⊭ □(p ∨ q)` is not valid over the admissible models; the
model of Figure 1 refutes it. -/
theorem ross_invalid :
    ¬ ∀ (W : Type) (r : W → Set W) (v : Bool → Set W), IncompRel (· ⊆ ·) (v true) (v false) →
      truth (Formula.eval v r (.box (.atom true))) ⊆
        truth (Formula.eval v r (.box (.disj (.atom true) (.atom false)))) :=
  fun hall ↦ (ross_gap incomp_val box_p).1 (hall W4 rP val incomp_val box_p)

/-- Entailment is not closed under contraposition, as `¬□(p ∨ q) ⊨ ¬□p` (Fact 7) but `□p ⊭ □(p ∨ q)`
(Fact 3) (§8). -/
theorem not_contraposition :
    truth (Formula.eval val rP (.neg (.box (.disj (.atom true) (.atom false))))) ⊆
        truth (Formula.eval val rP (.neg (.box (.atom true)))) ∧
      ¬ truth (Formula.eval val rP (.box (.atom true))) ⊆
        truth (Formula.eval val rP (.box (.disj (.atom true) (.atom false)))) :=
  ⟨unnecessity_distribution_left val rP true false,
    fun h ↦ (ross_gap incomp_val box_p).1 (h box_p)⟩

end Figures

/-! ### Simons's super covers (fn. 22)

[simons-2005] requires the disjuncts under a modal to super cover its domain, each meeting it,
and considers strengthening the super cover by an Alternativeness constraint as a pragmatic
add-on. Booth's minimal covers are that strengthening made part of the truth conditions. -/

/-- Simons's super cover enhanced by the Alternativeness constraint is exactly a minimal cover:
the requirement fn. 22 says resembles the minimal covering relation is that relation. -/
theorem isMinCover_iff_alternativeness {C : Set (Set W)} {S : Set W} :
    IsMinCover C S ↔
      S ⊆ ⋃₀ C ∧ (∀ X ∈ C, (X ∩ S).Nonempty) ∧ Simons2005.Alternativeness C S := by
  rw [isMinCover_iff_inter_sdiff]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ ⟨fun X hX ↦ (h X hX).mono fun _ hv ↦ ⟨hv.2.1, hv.1⟩,
    fun X hX ↦ ?_⟩, fun ⟨_, h⟩ X hX ↦ ?_⟩
  · obtain ⟨x, hxS, hxX, hx⟩ := h X hX
    exact ⟨x, ⟨hxX, hxS⟩, fun Y hY hYX hxY ↦ hx ⟨Y, ⟨hY, hYX⟩, hxY⟩⟩
  · obtain ⟨x, ⟨hxX, hxS⟩, hx⟩ := h X hX
    exact ⟨x, hxS, hxX, fun ⟨Y, ⟨hY, hYX⟩, hxY⟩ ↦ hx Y hY hYX hxY⟩

/-- `□(p ∨ q)` entails Simons's necessity over the disjuncts, and with it the Diversity
inferences (fn. 22). -/
theorem truth_box_disj_subset_must (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    truth (Formula.eval V R (.box (.disj (.atom p) (.atom q)))) ⊆
      Simons2005.must R {V p, V q} := by
  rw [truth_box_disj V R h]
  exact fun _ hw ↦ hw.isSuperCover (hw.nonempty (Set.insert_nonempty _ _))

/-- Simons's necessity validates the Diversity inferences without the Independence inferences
(fn. 22): on the model of Figure 1 the disjuncts super cover the relevant worlds, yet `◇(q ∧ ¬p)`
is not true. -/
theorem Figures.must_not_independence :
    (true, true) ∈ Simons2005.must Figures.rP {Figures.vp, Figures.vq} ∧
      (true, true) ∉ truth (Formula.eval Figures.val Figures.rP
        (.diamond (.conj (.atom false) (.neg (.atom true))))) :=
  ⟨Figures.diversity_without_independence.1, Figures.not_diamond_qAndNotP⟩

/-- Where every relevant `p`-world is a `q`-world, neither `◇(p ∨ q)` nor `□(p ∨ q)` is true. These
are the cases of §6.2 of [simons-2005], *Jane may eat chocolate or brush her teeth* when eating
chocolate requires brushing, on which some speakers judge the sentences false and Simons's own
truth conditions hold. -/
theorem not_mem_truth_disj_of_inter_subset (h : IncompRel (· ⊆ ·) (V p) (V q)) {w : W}
    (hpq : R w ∩ V p ⊆ V q) :
    w ∉ truth (Formula.eval V R (.diamond (.disj (.atom p) (.atom q)))) ∧
      w ∉ truth (Formula.eval V R (.box (.disj (.atom p) (.atom q)))) := by
  have hind : w ∉ truth (Formula.eval V R (.diamond (.conj (.atom p) (.neg (.atom q))))) := by
    rw [truth_diamond_conj_neg]
    rintro ⟨v, hvR, hvp, hvq⟩
    exact hvq (hpq ⟨hvR, hvp⟩)
  exact ⟨fun hw ↦ hind (diamond_independence_left h hw),
    fun hw ↦ hind (box_independence_left h hw)⟩

end Booth2022a
