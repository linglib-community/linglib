module

public import Linglib.Semantics.Modality.MinimalCovering
public import Linglib.Logic.Modal.Defs
public import Studies.Simons2005

/-!
# Booth (2022a): Independent alternatives: Ross's puzzle and free choice

[booth-2022a] explains Ross's puzzle and free choice permission by the Independence inferences:
accepting `□(p ∨ q)` or `◇(p ∨ q)` commits a speaker to `◇(p ∧ ¬q)` and `◇(q ∧ ¬p)`, each disjunct
an option independently of the other, which is strictly stronger than the Diversity inferences
`◇p`, `◇q` of the standard analyses. In Booth's bilateral minimal covering semantics, the
theory-layer `MinimalCovering`, `◇(p ∨ q)` is true [exactly where both Independence inferences
are](##truth_diamond_disj_eq_inter), and `□(p ∨ q)` is [the orthodox `□!(p ∨ q)` together with
`◇(p ∨ q)`](##truth_box_disj_eq_inter). Free choice [follows](##free_choice), and the Ross inference
fails in the strongest way: where `□p` is true, `□(p ∨ q)` is [neither true nor false](##ross_gap).

The super covers of [simons-2005] validate the Diversity inferences without the Independence
inferences. The Alternativeness constraint that Simons considers adding to them as a pragmatic
requirement [is the minimal cover](##isMinCover_iff_alternativeness), so Booth's semantics makes
Alternativeness part of the truth conditions, and the cases where some of Simons's informants judge
a modal disjunction false although her truth conditions make it true
[are not true here](##not_mem_truth_disj_of_inter_subset).

## Implementation notes

* Sentences use the notation of `MinimalCovering`: `□`, `◇`, `∼`, `⋏`, `⋎`, `⇒` for the restrictor
  conditional, and `φ ⊨[V, R] ψ` for the appendix's entailment in the model `⟨W, R, V⟩`.
* Validity over the admissible models is universal quantification over worlds, accessibility and
  valuation, with the hypothesis `IncompRel (· ⊆ ·) (V p) (V q)` for the two atoms each fact
  mentions.
* The appendix's Ross fact is non-validity: some admissible model has `□p` true and `□(p ∨ q)`
  not (`Figures.ross_invalid`). The stronger pointwise claim, that `□p` makes `□(p ∨ q)` neither
  true nor false, is `ross_gap`.

## Errata

* The admissibility of a model is printed as a condition on all atoms `p, q`, which no model
  satisfies for `p = q`; it is read here for the pair at hand.
* The appendix prints `[!φ] = (℘(info([φ]⁺)), ℘(info([ψ]⁻)))`, with `ψ` in the negative
  coordinate. This is a typo for `φ`, the only reading on which `!φ` is a bilateral proposition,
  and `MinimalCovering.bang` follows it.
* The paraphrase of Simons's super cover drops its requirement that the family be nonempty, under
  which the claim that every minimal cover is a super cover fails for the empty family covering
  the empty set. It holds for every nonempty set (`MinimalCovering.IsMinCover.isSuperCover`).

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

-- §5
theorem truth_box_disj (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    truth (Formula.eval V R (□(.atom p ⋎ .atom q))) =
      {w | IsMinCover {V p, V q} (R w)} := by
  change truth (necessity R (atom (V p) ⊔ atom (V q))) = _
  rw [truth_necessity, alt_sup_atom h]

-- §5
theorem truth_diamond_disj (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    truth (Formula.eval V R (◇(.atom p ⋎ .atom q))) =
      {w | ∃ R' ⊆ R w, R'.Nonempty ∧ IsMinCover {V p, V q} R'} := by
  change truth (possibility R (atom (V p) ⊔ atom (V q))) = _
  rw [truth_possibility, alt_sup_atom h]

theorem truth_box_atom (p : At) :
    truth (Formula.eval V R (□.atom p)) = {w | (R w).Nonempty ∧ R w ⊆ V p} :=
  truth_necessity_of_alt_eq_singleton R _ (alt_atom_pro _)

theorem truth_diamond_atom (p : At) :
    truth (Formula.eval V R (◇.atom p)) = {w | (R w ∩ V p).Nonempty} :=
  truth_possibility_of_alt_eq_singleton R _ (alt_atom_pro _)

theorem truth_diamond_conj_neg (p q : At) :
    truth (Formula.eval V R (◇(.atom p ⋏ ∼.atom q))) =
      {w | (R w ∩ (V p \ V q)).Nonempty} :=
  truth_possibility_of_alt_eq_singleton R _ (alt_inf_compl_atom _ _)

/-- `◇(p ∨ q)` is true exactly where both Independence inferences are (§5): some relevant world is
a `p`-without-`q` world and some is a `q`-without-`p` world. -/
theorem truth_diamond_disj_eq_inter (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    truth (Formula.eval V R (◇(.atom p ⋎ .atom q))) =
      truth (Formula.eval V R (◇(.atom p ⋏ ∼.atom q))) ∩
        truth (Formula.eval V R (◇(.atom q ⋏ ∼.atom p))) := by
  rw [truth_diamond_disj V R h, truth_diamond_conj_neg, truth_diamond_conj_neg]
  ext w
  simp [exists_isMinCover_iff, Set.pair_sdiff_left h.ne, Set.pair_sdiff_right h.ne]

/-- `□(p ∨ q)` is the orthodox necessity `□!(p ∨ q)` together with `◇(p ∨ q)` (§5): every relevant
world is a `p ∨ q`-world, and the disjuncts are independent alternatives among them. -/
theorem truth_box_disj_eq_inter (p q : At) :
    truth (Formula.eval V R (□(.atom p ⋎ .atom q))) =
      truth (Formula.eval V R (□.bang (.atom p ⋎ .atom q))) ∩
        truth (Formula.eval V R (◇(.atom p ⋎ .atom q))) :=
  truth_necessity_eq_inter R _ ((isNormal_ofSet (V p)).sup (isNormal_ofSet (V q)))

-- §4
theorem box_diversity (h : IncompRel (· ⊆ ·) (V p) (V q)) {w : W}
    (hw : w ∈ truth (Formula.eval V R (□(.atom p ⋎ .atom q)))) :
    (R w ∩ V p).Nonempty ∧ (R w ∩ V q).Nonempty := by
  rw [truth_box_disj_eq_inter V R p q, truth_diamond_disj_eq_inter V R h, truth_diamond_conj_neg,
    truth_diamond_conj_neg] at hw
  exact ⟨hw.2.1.mono (Set.inter_subset_inter_right _ Set.sdiff_subset),
    hw.2.2.mono (Set.inter_subset_inter_right _ Set.sdiff_subset)⟩

-- §4
theorem truth_diamond_conj_neg_subset (p q : At) :
    ◇(.atom p ⋏ ∼.atom q) ⊨[V, R] ◇.atom p := by
  rw [truth_diamond_conj_neg, truth_diamond_atom]
  exact fun _ hw ↦ hw.mono (Set.inter_subset_inter_right _ Set.sdiff_subset)

-- §6, fn. 13 [kratzer-1991]
theorem truth_necessity_bang (φ : Kalman (Question W)) :
    truth (necessity R (bang φ)) =
      {w | (R w).Nonempty ∧ ModalLogic.Box (.ofSuccessors R) (· ∈ truth φ) w} :=
  truth_necessity_of_alt_eq_singleton R _ (alt_bang_pro φ)

-- §6
theorem truth_possibility_bang (φ : Kalman (Question W)) :
    truth (possibility R (bang φ)) =
      {w | ModalLogic.Diamond (.ofSuccessors R) (· ∈ truth φ) w} := by
  rw [truth_possibility_of_alt_eq_singleton R _ (alt_bang_pro φ)]
  rfl

-- §6, (16), (17)
theorem box_bang_disj (p q : At) :
    □.atom p ⊨[V, R] □.bang (.atom p ⋎ .atom q) := by
  rw [truth_box_atom]
  change _ ⊆ truth (necessity R (bang (atom (V p) ⊔ atom (V q))))
  rw [truth_necessity_of_alt_eq_singleton R _ (alt_bang_pro _)]
  exact fun _ ⟨hne, hsub⟩ ↦ ⟨hne, fun v hv ↦ by simpa using Or.inl (hsub hv)⟩

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

theorem not_diamond_disj (w : Bool × Bool) : w ∈ (diamond rB (ofSet vM ⊔ ofSet vB))ᶜ.info := by
  rw [info_compl, info_diamond, alt_disj]
  rintro ⟨R', hR', -, hmc⟩
  obtain ⟨-, ⟨v, hv, -, hvB⟩, -⟩ := (isMinCover_pair_iff_inter_sdiff vM_ne_vB).1 hmc
  exact hvB (hR' hv)

-- (19)
theorem diamond_right (w : Bool × Bool) : w ∉ (diamond rB (ofSet vB))ᶜ.info := by
  rw [info_compl, info_diamond, alt_ofSet, Set.notMem_compl_iff]
  have hB : vB.Nonempty := ⟨(true, true), rfl⟩
  exact ⟨vB, subset_rfl, hB, isMinCover_singleton_iff.2 ⟨hB, subset_rfl⟩⟩

-- (21)
theorem box_neg_disj (w : Bool × Bool) : w ∉ (box rB (ofSet vM ⊔ ofSet vB)ᶜ).info := by
  rw [info_box, compl_eq, alt_ofSet, Set.mem_ofPred_eq,
    isMinCover_singleton_iff, info_sup, info_ofSet, info_ofSet]
  intro h
  exact h.2 (show (true, true) ∈ rB w from rfl) (Or.inr rfl)

theorem not_box_disj (w : Bool × Bool) : w ∈ (box rB (ofSet vM ⊔ ofSet vB))ᶜ.info := by
  rw [info_compl, info_box, alt_disj]
  intro hmc
  obtain ⟨-, ⟨v, hv, -, hvB⟩, -⟩ := (isMinCover_pair_iff_inter_sdiff vM_ne_vB).1 hmc
  exact hvB hv

-- (20)
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

-- Fact 1
theorem box_independence_left (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    □(.atom p ⋎ .atom q) ⊨[V, R] ◇(.atom p ⋏ ∼.atom q) :=
  (truth_box_disj_eq_inter V R p q).le.trans
    (Set.inter_subset_right.trans
      ((truth_diamond_disj_eq_inter V R h).le.trans Set.inter_subset_left))

-- Fact 1
theorem box_independence_right (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    □(.atom p ⋎ .atom q) ⊨[V, R] ◇(.atom q ⋏ ∼.atom p) :=
  (truth_box_disj_eq_inter V R p q).le.trans
    (Set.inter_subset_right.trans
      ((truth_diamond_disj_eq_inter V R h).le.trans Set.inter_subset_right))

-- Fact 1
theorem diamond_independence_left (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    ◇(.atom p ⋎ .atom q) ⊨[V, R] ◇(.atom p ⋏ ∼.atom q) :=
  (truth_diamond_disj_eq_inter V R h).le.trans Set.inter_subset_left

-- Fact 1
theorem diamond_independence_right (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    ◇(.atom p ⋎ .atom q) ⊨[V, R] ◇(.atom q ⋏ ∼.atom p) :=
  (truth_diamond_disj_eq_inter V R h).le.trans Set.inter_subset_right

theorem updateAccess_neg_atom (p : At) (w : W) :
    updateAccess R (Formula.eval V R (∼.atom p)) w = R w \ V p := by
  change R w ∩ truth (atom (V p))ᶜ = _
  rw [truth_compl, falsity_atom]
  rfl

theorem truth_cond_neg_atom (p : At) (ψ : Formula At) :
    truth (Formula.eval V R (∼.atom p ⇒ ψ)) = truth (Formula.eval V (fun w ↦ R w \ V p) ψ) :=
  congrArg (fun R' ↦ truth (Formula.eval V R' ψ)) (funext (updateAccess_neg_atom p))

-- Fact 2
theorem box_conditional_left (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    □(.atom p ⋎ .atom q) ⊨[V, R] ∼.atom p ⇒ □.atom q := by
  intro w hw
  rw [truth_box_disj V R h, Set.mem_ofPred_eq,
    isMinCover_pair_iff_inter_sdiff h.ne] at hw
  rw [truth_cond_neg_atom, truth_box_atom, Set.mem_ofPred_eq]
  obtain ⟨v, hvR, -, hvp⟩ := hw.2.2
  exact ⟨⟨v, hvR, hvp⟩, fun u hu ↦ (hw.1 hu.1).resolve_left hu.2⟩

-- Fact 2
theorem box_conditional_right (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    □(.atom p ⋎ .atom q) ⊨[V, R] ∼.atom q ⇒ □.atom p := by
  intro w hw
  rw [truth_box_disj V R h, Set.mem_ofPred_eq,
    isMinCover_pair_iff_inter_sdiff h.ne] at hw
  rw [truth_cond_neg_atom, truth_box_atom, Set.mem_ofPred_eq]
  obtain ⟨v, hvR, -, hvq⟩ := hw.2.1
  exact ⟨⟨v, hvR, hvq⟩, fun u hu ↦ (hw.1 hu.1).resolve_right hu.2⟩

-- Fact 2
theorem diamond_conditional_left (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    ◇(.atom p ⋎ .atom q) ⊨[V, R] ∼.atom p ⇒ ◇.atom q := by
  intro w hw
  rw [truth_cond_neg_atom, truth_diamond_atom, Set.mem_ofPred_eq]
  have hind := diamond_independence_right h hw
  rw [truth_diamond_conj_neg] at hind
  obtain ⟨v, hvR, hvq, hvp⟩ := hind
  exact ⟨v, ⟨hvR, hvp⟩, hvq⟩

-- Fact 2
theorem diamond_conditional_right (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    ◇(.atom p ⋎ .atom q) ⊨[V, R] ∼.atom q ⇒ ◇.atom p := by
  intro w hw
  rw [truth_cond_neg_atom, truth_diamond_atom, Set.mem_ofPred_eq]
  have hind := diamond_independence_left h hw
  rw [truth_diamond_conj_neg] at hind
  obtain ⟨v, hvR, hvp, hvq⟩ := hind
  exact ⟨v, ⟨hvR, hvq⟩, hvp⟩

/-- **Fact 4**, Free Choice: `◇(p ∨ q) ⊨ ◇p`. -/
theorem free_choice (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    ◇(.atom p ⋎ .atom q) ⊨[V, R] ◇.atom p :=
  (diamond_independence_left h).trans (truth_diamond_conj_neg_subset V R p q)

theorem free_choice_right (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    ◇(.atom p ⋎ .atom q) ⊨[V, R] ◇.atom q :=
  (diamond_independence_right h).trans (truth_diamond_conj_neg_subset V R q p)

variable (V R)

-- Fact 5
theorem box_eq_neg_diamond_neg (φ : Formula At) :
    Formula.eval V R (□φ) = Formula.eval V R (∼◇∼φ) :=
  rfl

-- Fact 5
theorem diamond_eq_neg_box_neg (φ : Formula At) :
    Formula.eval V R (◇φ) = Formula.eval V R (∼□∼φ) :=
  rfl

-- Fact 6
theorem impossibility_distribution_left (p q : At) :
    ∼◇(.atom p ⋎ .atom q) ⊨[V, R] ∼◇.atom p := by
  change falsity (possibility R (atom (V p) ⊔ atom (V q))) ⊆ falsity (possibility R (atom (V p)))
  rw [falsity_possibility_of_alt_eq_singleton R _ (alt_sup_atom_con _ _),
    falsity_possibility_of_alt_eq_singleton R _ (alt_atom_con _)]
  exact fun _ ⟨hne, hsub⟩ ↦ ⟨hne, hsub.trans Set.inter_subset_left⟩

-- Fact 6
theorem impossibility_distribution_right (p q : At) :
    ∼◇(.atom p ⋎ .atom q) ⊨[V, R] ∼◇.atom q := by
  change falsity (possibility R (atom (V p) ⊔ atom (V q))) ⊆ falsity (possibility R (atom (V q)))
  rw [falsity_possibility_of_alt_eq_singleton R _ (alt_sup_atom_con _ _),
    falsity_possibility_of_alt_eq_singleton R _ (alt_atom_con _)]
  exact fun _ ⟨hne, hsub⟩ ↦ ⟨hne, hsub.trans Set.inter_subset_right⟩

-- Fact 7
theorem unnecessity_distribution_left (p q : At) :
    ∼□(.atom p ⋎ .atom q) ⊨[V, R] ∼□.atom p := by
  change falsity (necessity R (atom (V p) ⊔ atom (V q))) ⊆ falsity (necessity R (atom (V p)))
  rw [falsity_necessity_of_alt_eq_singleton R _ (alt_sup_atom_con _ _),
    falsity_necessity_of_alt_eq_singleton R _ (alt_atom_con _)]
  exact fun _ hw ↦ hw.mono (Set.inter_subset_inter_right _ Set.inter_subset_left)

-- Fact 7
theorem unnecessity_distribution_right (p q : At) :
    ∼□(.atom p ⋎ .atom q) ⊨[V, R] ∼□.atom q := by
  change falsity (necessity R (atom (V p) ⊔ atom (V q))) ⊆ falsity (necessity R (atom (V q)))
  rw [falsity_necessity_of_alt_eq_singleton R _ (alt_sup_atom_con _ _),
    falsity_necessity_of_alt_eq_singleton R _ (alt_atom_con _)]
  exact fun _ hw ↦ hw.mono (Set.inter_subset_inter_right _ Set.inter_subset_right)

variable {V R}

-- fn. 32
theorem dual_free_choice (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    ∼□(.atom p ⋏ .atom q) ⊨[V, R] ◇∼.atom p := by
  have key : Formula.eval V R (∼□(.atom p ⋏ .atom q)) =
      Formula.eval (fun a ↦ (V a)ᶜ) R (◇(.atom p ⋎ .atom q)) := by
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

-- §8
theorem isCompl_truth_falsity (φ : Formula At) (hφ : IsModalFree φ) :
    IsCompl (truth (Formula.eval V R φ)) (falsity (Formula.eval V R φ)) := by
  induction φ generalizing R with
  | atom p => simpa [Formula.eval] using isCompl_compl (x := V p)
  | neg φ ih => exact (ih R hφ).symm
  | conj φ ψ ihφ ihψ => simpa [Formula.eval] using (ihφ R hφ.1).inf_sup (ihψ R hφ.2)
  | disj φ ψ ihφ ihψ => simpa [Formula.eval] using (ihφ R hφ.1).sup_inf (ihψ R hφ.2)
  | bang φ ih => simpa [Formula.eval] using ih R hφ
  | cond φ ψ _ ihψ => exact ihψ _ hφ.2
  | box φ _ => exact hφ.elim
  | diamond φ _ => exact hφ.elim

variable {V R}

/-- **The Ross gap** (§8, fn. 35): if `□p` is true, `□(p ∨ q)` is neither true nor false. -/
theorem ross_gap (h : IncompRel (· ⊆ ·) (V p) (V q)) {w : W}
    (hw : w ∈ truth (Formula.eval V R (□.atom p))) :
    w ∉ truth (Formula.eval V R (□(.atom p ⋎ .atom q))) ∧
      w ∉ falsity (Formula.eval V R (□(.atom p ⋎ .atom q))) := by
  rw [truth_box_atom, Set.mem_ofPred_eq] at hw
  refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
  · rw [truth_box_disj V R h, Set.mem_ofPred_eq, isMinCover_pair_iff h.ne] at h'
    exact h'.2.1 hw.2
  · change w ∈ falsity (necessity R (atom (V p) ⊔ atom (V q))) at h'
    rw [falsity_necessity_of_alt_eq_singleton R _ (alt_sup_atom_con _ _)] at h'
    obtain ⟨v, hvR, hvp, -⟩ := h'
    exact hvp (hw.2 hvR)

-- §8
theorem free_choice_gap (h : IncompRel (· ⊆ ·) (V p) (V q)) {w : W}
    (hp : w ∈ truth (Formula.eval V R (◇.atom p)))
    (hq : w ∉ truth (Formula.eval V R (◇.atom q))) :
    w ∉ truth (Formula.eval V R (◇(.atom p ⋎ .atom q))) ∧
      w ∉ falsity (Formula.eval V R (◇(.atom p ⋎ .atom q))) :=
  ⟨fun h' ↦ hq (free_choice_right h h'), fun h' ↦ Set.disjoint_left.1
    (disjoint_truth_falsity (Formula.eval V R (◇.atom p))) hp
    (impossibility_distribution_left V R p q h')⟩

-- §8
theorem independence_gap (h : IncompRel (· ⊆ ·) (V p) (V q)) {w : W}
    (hp : w ∈ truth (Formula.eval V R (◇.atom p)))
    (hind : w ∉ truth (Formula.eval V R (◇(.atom p ⋏ ∼.atom q)))) :
    w ∉ truth (Formula.eval V R (◇(.atom p ⋎ .atom q))) ∧
      w ∉ falsity (Formula.eval V R (◇(.atom p ⋎ .atom q))) :=
  ⟨fun h' ↦ hind (diamond_independence_left h h'), fun h' ↦ Set.disjoint_left.1
    (disjoint_truth_falsity (Formula.eval V R (◇.atom p))) hp
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

-- (12)
theorem gap (w : Bool × Bool) :
    w ∉ truth (Formula.eval val acc (◇(.atom true ⋎ .atom false))) ∧
      w ∉ falsity (Formula.eval val acc (◇(.atom true ⋎ .atom false))) := by
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

-- Figure 1
theorem diversity_without_independence :
    IsSuperCover {vp, vq} (rP (true, true)) ∧ ¬ IsMinCover {vp, vq} (rP (true, true)) :=
  ⟨isSuperCover_pair_iff.2 ⟨⟨(true, true), rfl, rfl⟩, ⟨(true, true), rfl, rfl⟩,
    Set.subset_union_left⟩,
    fun h ↦ ((isMinCover_pair_iff incomp.ne).1 h).2.1 subset_rfl⟩

-- Figure 2
theorem box_pOrQ :
    (true, true) ∈ truth (Formula.eval val r₃ (□(.atom true ⋎ .atom false))) := by
  rw [truth_box_disj val r₃ incomp_val]
  exact isMinCover_r₃

-- Figure 1
theorem box_p : (true, true) ∈ truth (Formula.eval val rP (□.atom true)) := by
  rw [truth_box_atom]
  exact ⟨⟨(true, true), rfl⟩, subset_rfl⟩

-- Figure 1
theorem diamond_q : (true, true) ∈ truth (Formula.eval val rP (◇.atom false)) := by
  rw [truth_diamond_atom]
  exact ⟨(true, true), rfl, rfl⟩

-- Figure 1
theorem not_diamond_qAndNotP :
    (true, true) ∉
      truth (Formula.eval val rP (◇(.atom false ⋏ ∼.atom true))) := by
  rw [truth_diamond_conj_neg]
  rintro ⟨v, hvR, -, hv⟩
  exact hv hvR

-- (8), Figure 1
theorem extended_ross :
    (true, true) ∈ truth (Formula.eval val rP (□.atom true)) ∩
        truth (Formula.eval val rP (◇.atom false)) ∧
      (true, true) ∉ truth (Formula.eval val rP (□(.atom true ⋎ .atom false))) :=
  ⟨⟨box_p, diamond_q⟩, (ross_gap incomp_val box_p).1⟩

-- Fact 3, Figure 1
theorem ross_invalid :
    ¬ ∀ (W : Type) (r : W → Set W) (v : Bool → Set W), IncompRel (· ⊆ ·) (v true) (v false) →
      □.atom true ⊨[v, r] □(.atom true ⋎ .atom false) :=
  fun hall ↦ (ross_gap incomp_val box_p).1 (hall W4 rP val incomp_val box_p)

-- Fact 7, Fact 3, §8
theorem not_contraposition :
    ∼□(.atom true ⋎ .atom false) ⊨[val, rP] ∼□.atom true ∧
      ¬ □.atom true ⊨[val, rP] □(.atom true ⋎ .atom false) :=
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

-- fn. 22
theorem truth_box_disj_subset_must (h : IncompRel (· ⊆ ·) (V p) (V q)) :
    truth (Formula.eval V R (□(.atom p ⋎ .atom q))) ⊆
      Simons2005.must R {V p, V q} := by
  rw [truth_box_disj V R h]
  exact fun _ hw ↦ hw.isSuperCover (hw.nonempty (Set.insert_nonempty _ _))

-- fn. 22, Figure 1
theorem Figures.must_not_independence :
    (true, true) ∈ Simons2005.must Figures.rP {Figures.vp, Figures.vq} ∧
      (true, true) ∉ truth (Formula.eval Figures.val Figures.rP (◇(.atom false ⋏ ∼.atom true))) :=
  ⟨Figures.diversity_without_independence.1, Figures.not_diamond_qAndNotP⟩

-- §6.2 [simons-2005]
theorem not_mem_truth_disj_of_inter_subset (h : IncompRel (· ⊆ ·) (V p) (V q)) {w : W}
    (hpq : R w ∩ V p ⊆ V q) :
    w ∉ truth (Formula.eval V R (◇(.atom p ⋎ .atom q))) ∧
      w ∉ truth (Formula.eval V R (□(.atom p ⋎ .atom q))) := by
  have hind : w ∉ truth (Formula.eval V R (◇(.atom p ⋏ ∼.atom q))) := by
    rw [truth_diamond_conj_neg]
    rintro ⟨v, hvR, hvp, hvq⟩
    exact hvq (hpq ⟨hvR, hvp⟩)
  exact ⟨fun hw ↦ hind (diamond_independence_left h hw),
    fun hw ↦ hind (box_independence_left h hw)⟩

end Booth2022a
