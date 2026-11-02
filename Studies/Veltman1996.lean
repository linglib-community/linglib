module

public import Linglib.Semantics.Dynamic.OrderedInformationState
public import Mathlib.Data.Fintype.Powerset

/-!
# Veltman (1996): Defaults in Update Semantics

This file formalizes the paper of Veltman, which treats *normally φ* as an update of an agent's
expectations rather than a sentence about them. The framework of section 1, acceptance as a fixed
point of the update, the three notions of validity and additivity, with Propositions 1.2 and 1.3,
is `Semantics/Dynamic/Consequence.lean`.

Section 2 studies *might* on sets of worlds, whose updates of Definition 2.3 are `CCP.up`,
`CCP.neg` and `CCP.might`. The test *might φ* satisfies Strengthening, Idempotence and Monotony,
Lemma 2.8, `might_le`, `might_idem` and `might_monotone`, but not Persistence, so the system is
not additive, `not_isLowerSet_might` and `not_isAdditive_might`. Examples 2.7 show that
consistency depends on the order of the text, `consistent_might_neg` and
`not_consistent_up_might_neg`, and that validity₁ is neither right nor left monotone. On the
fragment without *might* validity is classical, `valid₁_up_iff`.

A state of section 3 pairs an expectation pattern, a preorder on worlds, with the agent's knowledge
of the facts; *normally φ* refines the pattern in favour of the `φ`-worlds and *presumably φ* tests
whether `φ` holds in the optimal worlds. That system is `DynamicSemantics.OrderedInformationState`,
and Examples 3.10 are stated here as verdicts of validity₁ on the paper's four worlds, together with
the rain-or-snow contrast by which *normally (p ∨ q)* is stronger than *normally p*, `rain_or_snow`
and `normally_not_normally_or`. Rules and facts are additive, so a rule that follows under validity₁
follows under validity₃ as well, `ex310_rule_persists_valid₃`, while the default inference *normally
p ⊩ presumably p* is valid₁ but neither valid₂ nor valid₃, `not_valid₂_presumably` and
`not_valid₃_presumably`, which is why Veltman concentrates on validity₁.

Section 4 adds the restricted rules *if φ, then normally ψ*. An expectation frame assigns a pattern
to every domain of worlds, Definition 4.2, `Frame`; a world is normal in a domain when it is
top-ranked in every subdomain containing it, Definition 4.3, `Normal`; a frame is coherent when
every nonempty domain has a normal world, `Coherent`; accepting a rule refines the pattern at the
rule's domain and crashes when the result is incoherent, Definitions 4.5 and 4.6, `rule`; and a set
of defaults applies within the agent's information when every domain extending it has a normal world
complying with them, Definition 4.9, `Applies`. The optimal worlds comply with a maximal applicable
set of defaults, Definition 4.13, `State.optimal`, computed over the accepted rules by Proposition
4.14. Validity is validity₁, `Valid`. Proved in general are the refinement clause of Definition 4.5,
`Frame.ofRules_cons_self` and `Frame.ofRules_cons_of_ne`, Proposition 4.7, coherent acceptance being
applicability of the new rule within its own domain, `coherent_cons_iff`, Conditional Identity and
Conjunction of Consequents, `rule_self` and `conjConsequents`, and the section 5 observation that
Weakening the Consequent never crashes a state, `weakenConsequent_coherent`. Checked on the paper's
eight worlds are Examples 4.8 and 4.11, the Nixon diamond, the student who is presumably an
unemployed adult, Independence, defeasible Modus Tollens, Modus Ponens over Modus Tollens on a
cyclic net, the failure of Hypothetical Syllogism, Contraposition and Strengthening the Antecedent
beside their defeasible versions, and the near-validity of Strengthening with a Consequent and
Disjunction of Antecedents. On the states that general rules build, section 4 agrees with section 3:
a frame is coherent when [its pattern is](##Veltman1996.State.coherent_ofRules_iff), *normally ψ*
[crashes exactly when no normal world is a
`ψ`-world](##Veltman1996.State.IsGeneral.normally_eq_absurd_iff) and otherwise promotes `ψ`, the
optimal worlds are [those of section 3](##Veltman1996.State.IsGeneral.optimal_eq), and *presumably
φ* [passes exactly when it does there](##Veltman1996.State.IsGeneral.presumably_eq_self_iff).

## Implementation notes

The updates of `DynamicSemantics.OrderedInformationState` do not crash, so the crashing system of
section 3 is the system of section 4 restricted to general rules, in which *normally ψ* is the rule
`(ψ ∨ ¬ψ) ⇝ ψ`. The second clause of Example 3.10(i), where the opposite rule crashes the state, is
checked there, `ex310_conflict`, and the remaining examples of section 3, whose texts do not crash,
on the updates of `DynamicSemantics.OrderedInformationState`
(`State.toOrderedInformationState_normally`, `State.toOrderedInformationState_fact`).

Every frame an agent reaches from the minimal state is the total frame refined by the rules it has
accepted, so a frame of section 4 is presented by its list of rules, `Frame.ofRules`, which makes
coherence, normality, applicability and the optimal worlds decidable and lets each verdict be
checked by `decide` over the atoms `p`, `q` and `r`. Acceptance then compares the facts and the
frames of two states rather than their presentations, so `Valid` is
`DynamicSemantics.EntailsFrom ⊤` read up to presentation. The comparison with the default logics
of Asher and Morreau in section 5 is discussed in the paper and not formalized.

## References

* [F. Veltman, *Defaults in Update Semantics* (1996)][veltman-1996]
* [N. Asher and M. Morreau, *Commonsense Entailment: A Modal Theory of Nonmonotonic Reasoning*
  (1991)][asher-morreau-1991]
-/

@[expose] public section

namespace Veltman1996

open DynamicSemantics DynamicSemantics.OrderedInformationState

/-! ### Might (§2) -/

section Might

open Function

variable {W : Type*} {φ : CCP W} {c d : Set W}

/-- The test *might φ* never adds possibilities (Lemma 2.8(i)). -/
theorem might_le (φ : CCP W) (σ : Set W) : CCP.might φ σ ⊆ σ := fun _ h ↦ h.1

/-- The test *might φ* is idempotent (Lemma 2.8(ii)). -/
theorem might_idem (φ : CCP W) (σ : Set W) : IsFixedPt (CCP.might φ) (CCP.might φ σ) := by
  rcases CCP.guard_isTest (fun s ↦ (φ s).Nonempty) σ with h | h
  · exact congrArg (CCP.might φ) h
  · rw [IsFixedPt, show CCP.might φ σ = ∅ from h]
    exact Set.subset_empty_iff.1 (might_le φ ∅)

/-- The test *might φ* is monotone when `φ` is (Lemma 2.8(iii)). -/
theorem might_monotone (hφ : Monotone φ) : Monotone (CCP.might φ) :=
  fun _ _ hst _ ⟨hw, hne⟩ ↦ ⟨hst hw, hne.mono (hφ hst)⟩

/-- A text is consistent when updating some state with it does not yield the absurd state
(Definition 2.4). -/
def Consistent (ψs : List (CCP W)) : Prop := ∃ σ : Set W, (ψs.foldl (fun σ ψ ↦ ψ σ) σ).Nonempty

private theorem neg_up_top_nonempty (hc : cᶜ.Nonempty) : (CCP.neg (CCP.up c) ⊤).Nonempty :=
  let ⟨v, hv⟩ := hc; ⟨v, trivial, fun h ↦ hv h.2⟩

private theorem up_top_nonempty (hc : c.Nonempty) : (CCP.up c ⊤).Nonempty :=
  let ⟨v, hv⟩ := hc; ⟨v, trivial, hv⟩

private theorem might_neg_up_top (hc : cᶜ.Nonempty) :
    CCP.might (CCP.neg (CCP.up c)) ⊤ = ⊤ :=
  CCP.guard_pos (neg_up_top_nonempty hc)

private theorem might_neg_up_up (σ : Set W) :
    CCP.might (CCP.neg (CCP.up c)) (CCP.up c σ) = ∅ :=
  CCP.guard_neg fun ⟨_, hv, hnv⟩ ↦ hnv ⟨hv, hv.2⟩

private theorem might_up_neg_up (σ : Set W) :
    CCP.might (CCP.up c) (CCP.neg (CCP.up c) σ) = ∅ :=
  CCP.guard_neg fun ⟨_, ⟨_, hv⟩, hvc⟩ ↦ hv ⟨‹_›, hvc⟩

/-- *Might ¬p, p* is consistent, but *p, might ¬p* is not (Example 2.7(i)). -/
theorem consistent_might_neg (hc : c.Nonempty) (hc' : cᶜ.Nonempty) :
    Consistent [CCP.might (CCP.neg (CCP.up c)), CCP.up c] :=
  ⟨⊤, by simpa only [List.foldl_cons, List.foldl_nil, might_neg_up_top hc'] using
    up_top_nonempty hc⟩

theorem not_consistent_up_might_neg : ¬Consistent [CCP.up c, CCP.might (CCP.neg (CCP.up c))] :=
  fun ⟨σ, h⟩ ↦ by
    simp only [List.foldl_cons, List.foldl_nil, might_neg_up_up] at h
    exact Set.not_nonempty_empty h

-- Example 2.7
theorem valid₁_might_neg :
    [CCP.might (CCP.neg (CCP.up c))] ⊩₁ CCP.might (CCP.neg (CCP.up c)) :=
  entailsFrom_append_self (ψs := []) (might_idem _)

theorem not_valid₁_might_neg_up (hc : c.Nonempty) (hc' : cᶜ.Nonempty) :
    ¬[CCP.might (CCP.neg (CCP.up c)), CCP.up c] ⊩₁ CCP.might (CCP.neg (CCP.up c)) := by
  intro h
  have h' : CCP.might (CCP.neg (CCP.up c)) (CCP.up c (CCP.might (CCP.neg (CCP.up c)) ⊤)) =
      CCP.up c (CCP.might (CCP.neg (CCP.up c)) ⊤) := h
  rw [might_neg_up_up, might_neg_up_top hc'] at h'
  exact Set.not_nonempty_empty (h' ▸ up_top_nonempty hc)

-- Example 2.7
theorem valid₁_might (hc : c.Nonempty) : [] ⊩₁ CCP.might (CCP.up c) :=
  CCP.guard_pos (up_top_nonempty hc)

theorem not_valid₁_neg_might (hc : cᶜ.Nonempty) :
    ¬[CCP.neg (CCP.up c)] ⊩₁ CCP.might (CCP.up c) := by
  intro h
  have h' : CCP.might (CCP.up c) (CCP.neg (CCP.up c) ⊤) = CCP.neg (CCP.up c) ⊤ := h
  rw [might_up_neg_up] at h'
  exact Set.not_nonempty_empty (h' ▸ neg_up_top_nonempty hc)

/-- *Might p* is not persistent: the minimal state accepts it, but the more informed state that
has learnt *¬p* does not (§2). -/
theorem not_isLowerSet_might (hc : c.Nonempty) (hc' : cᶜ.Nonempty) :
    ¬IsLowerSet (fixedPoints (CCP.might (CCP.up c))) := fun h ↦
  not_valid₁_neg_might hc' <|
    show CCP.neg (CCP.up c) ⊤ ∈ fixedPoints _ from h le_top (valid₁_might hc)

/-- So *might p* is not additive, although it satisfies Strengthening, Idempotence and Monotony
(§2). -/
theorem not_isAdditive_might (hc : c.Nonempty) (hc' : cᶜ.Nonempty) :
    ¬IsAdditive (CCP.might (CCP.up c)) :=
  fun h ↦ not_isLowerSet_might hc hc' (isAdditive_iff.1 h).2.2.2

private theorem mem_text_up {cs : List (Set W)} {σ : Set W} {w : W} :
    w ∈ text (cs.map CCP.up) σ ↔ w ∈ σ ∧ ∀ c ∈ cs, w ∈ c := by
  induction cs generalizing σ with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, text_cons, ih, List.forall_mem_cons]
    exact ⟨fun ⟨⟨hσ, hc⟩, hcs⟩ ↦ ⟨hσ, hc, hcs⟩, fun ⟨hσ, hc, hcs⟩ ↦ ⟨⟨hσ, hc⟩, hcs⟩⟩

/-- On the fragment without *might* validity is classical: the conclusion holds at every world
at which all the premises hold (§2). -/
theorem valid₁_up_iff {cs : List (Set W)} :
    cs.map CCP.up ⊩₁ CCP.up d ↔ ∀ w, (∀ c ∈ cs, w ∈ c) → w ∈ d := by
  rw [EntailsFrom, (CCP.isAdditive_up d).isFixedPt_iff]
  exact ⟨fun h w hw ↦ (h (mem_text_up.2 ⟨trivial, hw⟩)).2,
    fun h w hw ↦ ⟨trivial, h w (mem_text_up.1 hw).2⟩⟩

end Might

/-! ### Rules with exceptions (§3) -/

/-- The four worlds over the atoms `p` and `q` are `w₀ = ∅`, `w₁ = {p}`, `w₂ = {q}` and `w₃ = {p,
q}`. -/
inductive PQWorld where
  | w₀ | w₁ | w₂ | w₃
  deriving DecidableEq

open PQWorld

def atomP : PQWorld → Prop
  | .w₁ | .w₃ => True
  | _ => False

def atomQ : PQWorld → Prop
  | .w₂ | .w₃ => True
  | _ => False

private theorem atomP_w₀ : ¬atomP w₀ := id
private theorem atomP_w₁ : atomP w₁ := trivial
private theorem atomP_w₂ : ¬atomP w₂ := id
private theorem atomP_w₃ : atomP w₃ := trivial
private theorem atomQ_w₀ : ¬atomQ w₀ := id
private theorem atomQ_w₁ : ¬atomQ w₁ := id
private theorem atomQ_w₂ : atomQ w₂ := trivial
private theorem atomQ_w₃ : atomQ w₃ := trivial

/-- The minimal state `0`. -/
def σ₀ : OrderedInformationState PQWorld := ⊤

section Validity

open Function
open OrderedInformationState (promote assert)

-- Examples 3.10(i): a rule can have exceptions
theorem ex310_exception : (σ₀.promote atomP).assert (¬atomP ·) ≠ ⊥ := fun h ↦
  Set.notMem_empty w₀
    (h ▸ ⟨Set.mem_univ _, atomP_w₀⟩ : w₀ ∈ (⊥ : OrderedInformationState PQWorld).info)

theorem ex310_presumably : [(promote · atomP)] ⊩₁ presumablyTest atomP :=
  isFixedPt_presumablyTest_iff.2 fun _ hw ↦
    ((optimal_promote_of_order_eq_top (σ := σ₀) rfl ⟨w₁, Set.mem_univ _, atomP_w₁⟩).subset hw).2

private theorem not_presumably_w₀ :
    ¬IsFixedPt (presumablyTest atomP)
      ((⟨{w₀}, ⊤⟩ : OrderedInformationState PQWorld).promote atomP) :=
  fun h ↦ atomP_w₀ <| isFixedPt_presumablyTest_iff.1 h w₀
    ⟨rfl, fun _ hv _ ↦ by obtain rfl : _ = w₀ := hv; exact ⟨trivial, id⟩⟩

/-- The default inference *normally p ⊩ presumably p* is not valid₂ (§1.3). -/
theorem not_valid₂_presumably : ¬[(promote · atomP)] ⊩₂ presumablyTest atomP :=
  fun h ↦ not_presumably_w₀ (h ⟨{w₀}, ⊤⟩)

theorem not_valid₃_presumably : ¬[(promote · atomP)] ⊩₃ presumablyTest atomP :=
  fun h ↦ not_presumably_w₀ <| h _ fun _ hψ ↦ by
    obtain rfl := List.mem_singleton.1 hψ; exact isFixedPt_promote_iff.2 inf_le_right

private theorem w₀_optimal : w₀ ∈ ((σ₀.promote atomP).assert (¬atomP ·)).optimal :=
  ⟨⟨Set.mem_univ _, atomP_w₀⟩, fun _ ⟨_, hnpv⟩ _ ↦ ⟨trivial, fun hpv ↦ absurd hpv hnpv⟩⟩

theorem ex310_defeat :
    ¬[(promote · atomP), (assert · (¬atomP ·))] ⊩₁ presumablyTest atomP :=
  fun h ↦ atomP_w₀ (isFixedPt_presumablyTest_iff.1 h w₀ w₀_optimal)

theorem ex310_rule_persists :
    [(promote · atomP), (assert · (¬atomP ·))] ⊩₁ (promote · atomP) :=
  isFixedPt_promote_iff.2 inf_le_right

/-- Rules and facts are additive, so the persistence of the rule holds under every notion of
validity (Proposition 1.3), unlike the presumption. -/
theorem ex310_rule_persists_valid₃ :
    [(promote · atomP), (assert · (¬atomP ·))] ⊩₃ (promote · atomP) := by
  refine ((tfae_entails ?_ (OrderedInformationState.isAdditive_promote _)).out 1 3).1
    ex310_rule_persists
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨OrderedInformationState.isAdditive_promote _, OrderedInformationState.isAdditive_assert _⟩

theorem ex310_irrelevant : [(promote · atomP), (assert · atomQ)] ⊩₁ presumablyTest atomP :=
  isFixedPt_presumablyTest_iff.2 fun _ ⟨_, hopt⟩ ↦ by_contra fun hnpw ↦
    hnpw ((hopt ⟨Set.mem_univ _, atomQ_w₃⟩ ⟨trivial, fun _ ↦ atomP_w₃⟩).2 atomP_w₃)

theorem ex310_contrary :
    ¬[(promote · atomP), (assert · atomQ), (assert · (¬atomP ·))] ⊩₁ presumablyTest atomP :=
  fun h ↦ atomP_w₂ <| isFixedPt_presumablyTest_iff.1 h w₂
    ⟨⟨⟨Set.mem_univ _, atomQ_w₂⟩, atomP_w₂⟩, fun _ hv _ ↦ ⟨trivial, fun hp ↦ absurd hp hv.2⟩⟩

theorem ex310_two_rules :
    [(promote · atomP), (promote · atomQ)] ⊩₁ presumablyTest atomP :=
  isFixedPt_presumablyTest_iff.2 fun _ ⟨_, hopt⟩ ↦ by_contra fun hnpw ↦
    hnpw ((hopt (Set.mem_univ w₃) ⟨⟨trivial, fun _ ↦ atomP_w₃⟩, fun _ ↦ atomQ_w₃⟩).1.2 atomP_w₃)

theorem ex310_two_rules_defeat :
    ¬[(promote · atomP), (promote · atomQ), (assert · (¬atomP ·))] ⊩₁ presumablyTest atomP :=
  fun h ↦ atomP_w₂ <| isFixedPt_presumablyTest_iff.1 h w₂
    ⟨⟨Set.mem_univ _, atomP_w₂⟩,
      fun _ hv _ ↦ ⟨⟨trivial, fun hp ↦ absurd hp hv.2⟩, fun _ ↦ atomQ_w₂⟩⟩

theorem ex310_independence :
    [(promote · atomP), (promote · atomQ), (assert · (¬atomP ·))] ⊩₁ presumablyTest atomQ :=
  isFixedPt_presumablyTest_iff.2 fun _ ⟨⟨_, hnpw⟩, hopt⟩ ↦
    by_contra fun hnqw ↦ hnqw ((hopt ⟨Set.mem_univ _, atomP_w₂⟩
      ⟨⟨trivial, fun hpw ↦ absurd hpw hnpw⟩, fun hqw ↦ absurd hqw hnqw⟩).2 atomQ_w₂)

theorem ex310_ambiguity :
    let ψs : List (OrderedInformationState PQWorld → OrderedInformationState PQWorld) :=
      [(promote · atomP), (promote · atomQ), (assert · fun w ↦ ¬(atomP w ∧ atomQ w))]
    ¬ψs ⊩₁ presumablyTest atomP ∧ ¬ψs ⊩₁ presumablyTest atomQ := by
  intro ψs
  refine ⟨fun h ↦ atomP_w₂ (isFixedPt_presumablyTest_iff.1 h w₂
      ⟨⟨Set.mem_univ _, fun ⟨hp, _⟩ ↦ atomP_w₂ hp⟩, ?_⟩),
    fun h ↦ atomQ_w₁ (isFixedPt_presumablyTest_iff.1 h w₁
      ⟨⟨Set.mem_univ _, fun ⟨_, hq⟩ ↦ atomQ_w₁ hq⟩, ?_⟩)⟩
  · rintro v ⟨_, hnpq⟩ ⟨⟨_, _⟩, hqv⟩
    exact ⟨⟨trivial, fun hpv ↦ absurd ⟨hpv, hqv atomQ_w₂⟩ hnpq⟩, fun _ ↦ atomQ_w₂⟩
  · rintro v ⟨_, hnpq⟩ ⟨⟨_, hpv⟩, _⟩
    exact ⟨⟨trivial, fun _ ↦ atomP_w₁⟩, fun hqv ↦ absurd ⟨hpv atomP_w₁, hqv⟩ hnpq⟩

/-- *Normally p; not p; so presumably q* is invalid, while *normally (p ∨ q); not p; so presumably
q* is valid (§3). -/
theorem rain_or_snow :
    ¬[(promote · atomP), (assert · (¬atomP ·))] ⊩₁ presumablyTest atomQ ∧
      [(promote · fun w ↦ atomP w ∨ atomQ w), (assert · (¬atomP ·))] ⊩₁
        (presumablyTest atomQ) := by
  refine ⟨fun h ↦ atomQ_w₀ (isFixedPt_presumablyTest_iff.1 h w₀ w₀_optimal),
    isFixedPt_presumablyTest_iff.2 ?_⟩
  rintro w ⟨⟨_, hnpw⟩, hopt⟩
  by_contra hnqw
  exact ((hopt ⟨Set.mem_univ _, atomP_w₂⟩ ⟨trivial, fun _ ↦ Or.inr atomQ_w₂⟩).2
    (Or.inr atomQ_w₂)).elim hnpw hnqw

theorem normally_not_normally_or :
    ¬[(promote · atomP)] ⊩₁ (promote · fun w ↦ atomP w ∨ atomQ w) := fun h ↦
  ((Preorder.le_ofCriterion_iff.1 (isFixedPt_promote_iff.1 h)) (a := w₀) (b := w₂)
    ⟨trivial, fun hp ↦ absurd hp atomP_w₂⟩ (Or.inr atomQ_w₂)).elim atomP_w₀ atomQ_w₀

end Validity

/-! ### Rules for exceptions (§4) -/

variable {W : Type*}

/-- A restricted rule `φ ⇝ ψ` makes `default` a default in the domain `domain`. -/
structure Rule (W : Type*) where
  domain : Finset W
  default : Finset W
  deriving DecidableEq

/-- An expectation frame assigns to every domain `d` a pattern on `d` (Definition 4.2). -/
abbrev Frame (W : Type*) := (d : Finset W) → Preorder d

/-- The frame presented by a list of rules assigns to `d` the total pattern refined by the defaults
of the rules with domain `d` (Proposition 4.14). -/
@[reducible] def Frame.ofRules (R : List (Rule W)) : Frame W := fun d ↦
  Preorder.ofCriteria (fun (w : d) (r : Rule W) ↦ w.1 ∈ r.default) {r | r ∈ R ∧ r.domain = d}

/-- At the rule's own domain the pattern is the old one refined with `r.default` (Definition
4.5(ii)(b)). -/
theorem Frame.ofRules_cons_self (r : Rule W) (R : List (Rule W)) :
    Frame.ofRules (r :: R) r.domain =
      Frame.ofRules R r.domain ⊓ .ofCriterion (fun w ↦ w.1 ∈ r.default) :=
  Preorder.ext fun w v ↦
    ⟨fun h ↦ ⟨fun c hc ↦ h c ⟨List.mem_cons_of_mem _ hc.1, hc.2⟩, h r ⟨List.mem_cons_self, rfl⟩⟩,
     fun h c hc ↦ by
      rcases List.mem_cons.1 hc.1 with rfl | hc' <;> [exact h.2; exact h.1 c ⟨hc', hc.2⟩]⟩

/-- Other domains are untouched (Definition 4.5(ii)(a)). -/
theorem Frame.ofRules_cons_of_ne (r : Rule W) (R : List (Rule W)) {d : Finset W}
    (h : d ≠ r.domain) : Frame.ofRules (r :: R) d = Frame.ofRules R d :=
  Preorder.ext fun _ _ ↦
    ⟨fun h' c hc ↦ h' c ⟨List.mem_cons_of_mem _ hc.1, hc.2⟩, fun h' c hc ↦ by
      rcases List.mem_cons.1 hc.1 with rfl | hc'
      · exact absurd hc.2 h.symm
      · exact h' c ⟨hc', hc.2⟩⟩

theorem Frame.ofRules_perm {R R' : List (Rule W)} (h : R.Perm R') :
    Frame.ofRules R = Frame.ofRules R' :=
  funext fun d ↦ by simp only [Frame.ofRules, h.mem_iff]

/-- A world `w` is normal in `πd` when `w ∈ d` and `w` is at least as normal as every world of every
subdomain of `d` containing it, under that subdomain's pattern (Definition 4.3(i)). -/
def Normal (π : Frame W) (d : Finset W) (w : W) : Prop :=
  w ∈ d ∧ ∀ d' ⊆ d, ∀ hw : w ∈ d', ∀ v, ∀ hv : v ∈ d', (π d').le ⟨w, hw⟩ ⟨v, hv⟩

theorem normal_ofRules_iff (R : List (Rule W)) (d : Finset W) (w : W) :
    Normal (Frame.ofRules R) d w ↔ w ∈ d ∧ ∀ r ∈ R, r.domain ⊆ d → w ∈ r.domain →
      ∀ v ∈ r.domain, v ∈ r.default → w ∈ r.default :=
  and_congr_right fun _ ↦
    ⟨fun h r hr hsub hw v hv ↦ h r.domain hsub hw v hv r ⟨hr, rfl⟩,
     fun h d' hsub hw v hv r ⟨hr, hd⟩ ↦ by subst hd; exact h r hr hsub hw v hv⟩

theorem Normal.mono {π : Frame W} {d d' : Finset W} {w : W} (h : Normal π d w) (hw : w ∈ d')
    (hd : d' ⊆ d) : Normal π d' w :=
  ⟨hw, fun _ hsub ↦ h.2 _ (hsub.trans hd)⟩

theorem Normal.of_cons {r : Rule W} {R : List (Rule W)} {d : Finset W} {w : W}
    (h : Normal (Frame.ofRules (r :: R)) d w) : Normal (Frame.ofRules R) d w :=
  (normal_ofRules_iff ..).2 ⟨h.1, fun r' hr' ↦
    ((normal_ofRules_iff ..).1 h).2 r' (List.mem_cons_of_mem _ hr')⟩

variable [DecidableEq W]

instance (R : List (Rule W)) (d : Finset W) : DecidableRel (Frame.ofRules R d).le := fun w v ↦
  decidable_of_iff (∀ r ∈ R, r.domain = d → v.1 ∈ r.default → w.1 ∈ r.default)
    ⟨fun h c ⟨hc, hd⟩ ↦ h c hc hd, fun h c hc hd ↦ h c ⟨hc, hd⟩⟩

instance (R : List (Rule W)) (d : Finset W) : DecidablePred (Normal (Frame.ofRules R) d) :=
  fun w ↦ decidable_of_iff _ (normal_ofRules_iff R d w).symm

/-- The normal worlds `nπd` (Definition 4.3(ii)). -/
def normal (π : Frame W) (d : Finset W) [DecidablePred (Normal π d)] : Finset W :=
  d.filter (Normal π d)

/-- `w` complies with the defaults `D` (Definition 4.9(i)). -/
def Complies (w : W) (D : List (Rule W)) : Prop := ∀ r ∈ D, w ∈ r.domain → w ∈ r.default

instance (w : W) (D : List (Rule W)) : Decidable (Complies w D) :=
  inferInstanceAs (Decidable (∀ r ∈ D, w ∈ r.domain → w ∈ r.default))

/-- A proposition `e` is a default in `πd` when `d ∩ e ≠ ∅` and `πd ∘ e = πd`, that is, when the
worlds of `e` form a lower set of `πd` (Definition 4.2(ii)). -/
def IsDefault (π : Frame W) (d e : Finset W) : Prop :=
  (d ∩ e).Nonempty ∧ π d ≤ .ofCriterion (fun w ↦ w.1 ∈ e)

theorem isDefault_of_mem {R : List (Rule W)} {r : Rule W} (hr : r ∈ R)
    (hne : (r.domain ∩ r.default).Nonempty) : IsDefault (Frame.ofRules R) r.domain r.default :=
  ⟨hne, fun _ _ h hv ↦ h r ⟨hr, rfl⟩ hv⟩

theorem conjConsequents {R : List (Rule W)} {φ ψ χ : Finset W}
    (hψ : ⟨φ, ψ⟩ ∈ R) (hχ : ⟨φ, χ⟩ ∈ R) :
    Frame.ofRules (⟨φ, ψ ∩ χ⟩ :: R) = Frame.ofRules R := by
  refine funext fun d ↦ Preorder.ext fun w v ↦
    ⟨fun h c hc ↦ h c ⟨List.mem_cons_of_mem _ hc.1, hc.2⟩, fun h c hc ↦ ?_⟩
  rcases List.mem_cons.1 hc.1 with rfl | hc'
  · exact fun hv ↦ Finset.mem_inter.2
      ⟨h _ ⟨hψ, hc.2⟩ (Finset.mem_inter.1 hv).1, h _ ⟨hχ, hc.2⟩ (Finset.mem_inter.1 hv).2⟩
  · exact h c ⟨hc', hc.2⟩

/-- A frame is coherent when every nonempty domain has a normal world (Definition 4.3(iii)). -/
def Coherent (π : Frame W) [∀ d, DecidablePred (Normal π d)] : Prop :=
  ∀ d : Finset W, d.Nonempty → (normal π d).Nonempty

/-- The defaults `D` jointly apply within `s` when every domain extending `s` has a normal world
complying with them (Definition 4.9(ii)). -/
def Applies (π : Frame W) [∀ d, DecidablePred (Normal π d)] (D : List (Rule W))
    (s : Finset W) : Prop :=
  ∀ d : Finset W, s ⊆ d → ∃ w ∈ normal π d, Complies w D

/-- A coherent frame stays coherent under a rule `r` with `r.domain ∩ r.default ≠ ∅` iff `r` applies
within its own domain (Proposition 4.7). -/
theorem coherent_cons_iff {R : List (Rule W)} (hR : Coherent (Frame.ofRules R)) {r : Rule W}
    (hne : (r.domain ∩ r.default).Nonempty) :
    Coherent (Frame.ofRules (r :: R)) ↔ Applies (Frame.ofRules R) [r] r.domain := by
  obtain ⟨v₀, hv₀⟩ := hne
  rw [Finset.mem_inter] at hv₀
  constructor
  · intro h d hd
    obtain ⟨w, hw⟩ := h d ⟨v₀, hd hv₀.1⟩
    rw [normal, Finset.mem_filter] at hw
    refine ⟨w, Finset.mem_filter.2 ⟨hw.1, hw.2.of_cons⟩, fun _ hr' ↦ ?_⟩
    rcases List.mem_singleton.1 hr' with rfl
    exact fun hwd ↦ ((normal_ofRules_iff ..).1 hw.2).2 _ List.mem_cons_self hd hwd v₀ hv₀.1 hv₀.2
  · intro h d hd
    by_cases hsub : r.domain ⊆ d
    · obtain ⟨w, hw, hc⟩ := h d hsub
      rw [normal, Finset.mem_filter] at hw
      refine ⟨w, Finset.mem_filter.2 ⟨hw.1, (normal_ofRules_iff ..).2 ⟨hw.1, fun r' hr' ↦ ?_⟩⟩⟩
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact fun _ hwd _ _ _ ↦ hc r' (List.mem_singleton_self _) hwd
      · exact ((normal_ofRules_iff ..).1 hw.2).2 r' hr'
    · obtain ⟨w, hw⟩ := hR d hd
      rw [normal, Finset.mem_filter] at hw
      refine ⟨w, Finset.mem_filter.2 ⟨hw.1, (normal_ofRules_iff ..).2 ⟨hw.1, fun r' hr' ↦ ?_⟩⟩⟩
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact fun h ↦ absurd h hsub
      · exact ((normal_ofRules_iff ..).1 hw.2).2 r' hr'

-- §5
theorem weakenConsequent_applies {R : List (Rule W)} (hR : Coherent (Frame.ofRules R))
    {φ ψ χ : Finset W} (hψ : ⟨φ, ψ⟩ ∈ R) (hne : (φ ∩ ψ).Nonempty) :
    Applies (Frame.ofRules R) [⟨φ, ψ ∪ χ⟩] φ := by
  obtain ⟨v₀, hv₀⟩ := hne
  rw [Finset.mem_inter] at hv₀
  intro d hd
  obtain ⟨w, hw⟩ := hR d ⟨v₀, hd hv₀.1⟩
  refine ⟨w, hw, fun _ hr' ↦ ?_⟩
  rcases List.mem_singleton.1 hr' with rfl
  rw [normal, Finset.mem_filter] at hw
  exact fun hwφ ↦ Finset.mem_union_left _
    (((normal_ofRules_iff ..).1 hw.2).2 _ hψ hd hwφ v₀ hv₀.1 hv₀.2)

theorem weakenConsequent_coherent {R : List (Rule W)} (hR : Coherent (Frame.ofRules R))
    {φ ψ χ : Finset W} (hψ : ⟨φ, ψ⟩ ∈ R) (hne : (φ ∩ ψ).Nonempty) :
    Coherent (Frame.ofRules (⟨φ, ψ ∪ χ⟩ :: R)) :=
  (coherent_cons_iff hR (hne.mono (Finset.inter_subset_inter_left Finset.subset_union_left))).2
    (weakenConsequent_applies hR hψ hne)

variable [Fintype W]

instance (R R' : List (Rule W)) : Decidable (Frame.ofRules R = Frame.ofRules R') :=
  decidable_of_iff (∀ d : Finset W, ∀ w v : d, (Frame.ofRules R d).le w v ↔
      (Frame.ofRules R' d).le w v)
    ⟨fun h ↦ funext fun d ↦ Preorder.ext (h d), fun h _ _ _ ↦ h ▸ Iff.rfl⟩

instance (π : Frame W) [∀ d, DecidablePred (Normal π d)] : Decidable (Coherent π) :=
  inferInstanceAs (Decidable (∀ d : Finset W, d.Nonempty → (normal π d).Nonempty))

instance (π : Frame W) [∀ d, DecidablePred (Normal π d)] (D : List (Rule W)) (s : Finset W) :
    Decidable (Applies π D s) :=
  inferInstanceAs (Decidable (∀ d : Finset W, s ⊆ d → ∃ w ∈ normal π d, Complies w D))

/-- A state `(π, s)` consists of the frame, presented by the accepted rules, and the agent's
knowledge of the facts (Definition 4.4). -/
structure State (W : Type*) where
  rules : List (Rule W)
  info : Finset W
  deriving DecidableEq

namespace State

/-- The minimal state `0` has the total frame and every world possible. -/
def init : State W := ⟨[], Finset.univ⟩

/-- The absurd state `1`. -/
def absurd : State W := ⟨[], ∅⟩

variable (σ : State W)

/-- The frame of a state. -/
abbrev frame : Frame W := Frame.ofRules σ.rules

/-- `D` is a maximal applicable set of defaults in `σ` (Definition 4.13(i)), over the
accepted rules (Proposition 4.14). -/
def MaximalApplicable (D : List (Rule W)) : Prop :=
  Applies σ.frame D σ.info ∧ ∀ r ∈ σ.rules, Applies σ.frame (r :: D) σ.info → r ∈ D

instance (D : List (Rule W)) : Decidable (σ.MaximalApplicable D) :=
  inferInstanceAs (Decidable (_ ∧ ∀ r ∈ σ.rules, Applies σ.frame (r :: D) σ.info → r ∈ D))

/-- The optimal worlds `mσ` are the worlds of `s` complying with a maximal applicable set of
defaults (Definition 4.13(ii)). -/
def optimal : Finset W :=
  σ.info.filter fun w ↦ ∃ D ∈ σ.rules.sublists, σ.MaximalApplicable D ∧ Complies w D

/-- The state `σ` accepts `φ`, written `σ ⊩ φ`, when `σ[φ]` has the same facts and the same frame as
`σ`. -/
def Accepts (φ : State W → State W) : Prop := (φ σ).info = σ.info ∧ (φ σ).frame = σ.frame

instance (φ : State W → State W) : Decidable (σ.Accepts φ) :=
  inferInstanceAs (Decidable (_ ∧ Frame.ofRules _ = Frame.ofRules _))

end State

/-- The update `σ[φ ⇝ ψ]` refines the frame at `⟦φ⟧` with `⟦ψ⟧`, and crashes if `⟦φ⟧ ∩ ⟦ψ⟧ = ∅` or
the refined frame is incoherent (Definition 4.6). -/
def rule (φ ψ : Finset W) (σ : State W) : State W :=
  if (φ ∩ ψ).Nonempty ∧ Coherent (Frame.ofRules (⟨φ, ψ⟩ :: σ.rules)) ∧ σ.info.Nonempty
  then ⟨⟨φ, ψ⟩ :: σ.rules, σ.info⟩ else .absurd

/-- *Normally ψ* is `(ψ ∨ ¬ψ) ⇝ ψ` (Definition 4.1). -/
def normally (ψ : Finset W) : State W → State W := rule (ψ ∪ ψᶜ) ψ

/-- The update `σ[φ]` for a factual `φ` eliminates the `¬φ`-worlds, and crashes if none remain. -/
def fact (φ : Finset W) (σ : State W) : State W :=
  if (σ.info ∩ φ).Nonempty then ⟨σ.rules, σ.info ∩ φ⟩ else .absurd

/-- The update `σ[presumably φ]` is a test that passes iff `φ` holds in every optimal world
(Definition 4.13(iii)). -/
def presumably (φ : Finset W) (σ : State W) : State W :=
  if σ.optimal ⊆ φ then σ else .absurd

/-- An argument is valid₁ when the minimal state updated with the premises in order accepts the
conclusion (§1.2). -/
def Valid (prems : List (State W → State W)) (concl : State W → State W) : Prop :=
  (prems.foldl (fun σ φ ↦ φ σ) State.init).Accepts concl

instance (prems : List (State W → State W)) (concl : State W → State W) :
    Decidable (Valid prems concl) :=
  inferInstanceAs (Decidable (State.Accepts _ _))

theorem rule_self {φ : Finset W} (hφ : φ.Nonempty) : Valid [] (rule φ φ) := by
  have hco : Coherent (Frame.ofRules [(⟨φ, φ⟩ : Rule W)]) := fun d ⟨w, hw⟩ ↦
    ⟨w, Finset.mem_filter.2 ⟨hw, (normal_ofRules_iff ..).2 ⟨hw, fun r hr ↦ by
      rcases List.mem_singleton.1 hr with rfl; exact fun _ hw _ _ _ ↦ hw⟩⟩⟩
  have h : rule φ φ ⟨[], Finset.univ⟩ = ⟨[⟨φ, φ⟩], Finset.univ⟩ := by
    rw [rule,
      ite_eq_left ⟨by rwa [Finset.inter_self], hco, hφ.elim fun w _ ↦ ⟨w, Finset.mem_univ w⟩⟩]
  show State.Accepts ⟨[], Finset.univ⟩ (rule φ φ)
  rw [State.Accepts, h]
  refine ⟨rfl, funext fun d ↦ Preorder.ext fun w v ↦ ⟨fun _ c hc ↦ by simp at hc, ?_⟩⟩
  rintro _ c ⟨hc, rfl⟩
  rcases List.mem_singleton.1 hc with rfl
  exact fun _ ↦ w.2

/-! ### General rules

Veltman reintroduces *normally ψ* as the general rule `(ψ ∨ ¬ψ) ⇝ ψ`, whose domain is every world
(Definition 4.1). On the states that general rules build, the frame is a single pattern, the
ordering the defaults of the rules induce as premises, and the optimal worlds of Definition 4.13
are the minimal worlds of Definition 3.4. -/

namespace State

variable {σ : State W} {φ ψ : Finset W}

/-- A state is general when its rules are general rules with nonempty defaults and its frame is
coherent, as every state built from `0` by general rules, facts and presumptions is. -/
structure IsGeneral (σ : State W) : Prop where
  domain_eq : ∀ r ∈ σ.rules, r.domain = Finset.univ
  default_nonempty : ∀ r ∈ σ.rules, r.default.Nonempty
  coherent : Coherent σ.frame

/-- The ordered information state of section 3 that a state presents: its information, ranked by the
ordering that the defaults of its rules induce. -/
def toOrderedInformationState (σ : State W) : OrderedInformationState W :=
  ⟨σ.info, Preorder.ofCriteria (fun w (r : Rule W) ↦ w ∈ r.default) {r | r ∈ σ.rules}⟩

/-- In a general state a set of the rules applies within `s` exactly when some world of `s`
complies with it. -/
theorem IsGeneral.applies_iff (h : σ.IsGeneral) {D : List (Rule W)} (hD : ∀ r ∈ D, r ∈ σ.rules)
    {s : Finset W} : Applies σ.frame D s ↔ ∃ w ∈ s, Complies w D := by
  constructor
  · intro hs
    obtain ⟨w, hw, hc⟩ := hs s subset_rfl
    exact ⟨w, (Finset.mem_filter.1 hw).1, hc⟩
  rintro ⟨w₀, hw₀, hc⟩ d hsd
  by_cases hd : Finset.univ ⊆ d
  · obtain ⟨n, hn⟩ := h.coherent d ⟨w₀, hsd hw₀⟩
    refine ⟨n, hn, fun r hr _ ↦ ?_⟩
    obtain ⟨v, hv⟩ := h.default_nonempty r (hD r hr)
    have hn' := ((normal_ofRules_iff ..).1 (Finset.mem_filter.1 hn).2).2 r (hD r hr)
    rw [h.domain_eq r (hD r hr)] at hn'
    exact hn' hd (Finset.mem_univ n) v (Finset.mem_univ v) hv
  · exact ⟨w₀, Finset.mem_filter.2 ⟨hsd hw₀, (normal_ofRules_iff ..).2 ⟨hsd hw₀,
      fun r hr hsub ↦ (hd (h.domain_eq r hr ▸ hsub)).elim⟩⟩, hc⟩

/-- On a general state the optimal worlds of Definition 4.13 are the minimal worlds of the
information under the pattern of section 3, the optimal worlds of Definition 3.4. -/
theorem IsGeneral.optimal_eq (h : σ.IsGeneral) :
    (σ.optimal : Set W) = σ.toOrderedInformationState.optimal := by
  have hgen r (hr : r ∈ σ.rules) (w : W) : w ∈ r.domain := h.domain_eq r hr ▸ Finset.mem_univ w
  ext w
  rw [Finset.mem_coe, optimal, Finset.mem_filter, OrderedInformationState.optimal,
    Preorder.mem_minimals_iff]
  refine and_congr_right fun hw ↦ ⟨fun ⟨D, hD, hmax, hc⟩ v hv hvw r hr hrv ↦ ?_, fun hmin ↦ ?_⟩
  · have hsub : ∀ r ∈ D, r ∈ σ.rules := fun r hr ↦ (List.mem_sublists.1 hD).subset hr
    refine hc r (hmax.2 r hr ((h.applies_iff fun r' hr' ↦ ?_).2 ⟨v, hv, fun r' hr' _ ↦ ?_⟩))
      (hgen r hr w)
    · exact (List.mem_cons.1 hr').elim (· ▸ hr) (hsub r')
    · rcases List.mem_cons.1 hr' with rfl | hr'
      · exact hrv
      · exact hvw r' (hsub r' hr') (hc r' hr' (hgen r' (hsub r' hr') w))
  · refine ⟨σ.rules.filter (w ∈ ·.default), List.mem_sublists.2 List.filter_sublist,
      ⟨(h.applies_iff fun r hr ↦ (List.mem_filter.1 hr).1).2
        ⟨w, hw, fun r hr _ ↦ of_decide_eq_true (List.mem_filter.1 hr).2⟩, fun r hr hap ↦ ?_⟩,
      fun r hr _ ↦ of_decide_eq_true (List.mem_filter.1 hr).2⟩
    obtain ⟨u, hu, hc⟩ := (h.applies_iff fun r' hr' ↦
      (List.mem_cons.1 hr').elim (· ▸ hr) fun h' ↦ (List.mem_filter.1 h').1).1 hap
    refine List.mem_filter.2 ⟨hr, decide_eq_true (hmin hu (fun r' hr' hwr' ↦ ?_) r hr
      (hc r List.mem_cons_self (hgen r hr u)))⟩
    exact hc r' (List.mem_cons_of_mem _ (List.mem_filter.2 ⟨hr', decide_eq_true hwr'⟩))
      (hgen r' hr' u)

/-- A frame of general rules is coherent exactly when the ordering that their defaults induce has
a world at least as normal as every world, the coherence of a pattern (Definition 3.3). -/
theorem coherent_ofRules_iff [Nonempty W] {R : List (Rule W)}
    (hR : ∀ r ∈ R, r.domain = Finset.univ) :
    Coherent (Frame.ofRules R) ↔
      ∃ w, ∀ v, (Preorder.ofCriteria (fun w (r : Rule W) ↦ w ∈ r.default) {r | r ∈ R}).le w v := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h Finset.univ Finset.univ_nonempty
    refine ⟨n, fun v r hr hv ↦ ?_⟩
    have hn' := ((normal_ofRules_iff ..).1 (Finset.mem_filter.1 hn).2).2 r hr
    rw [hR r hr] at hn'
    exact hn' subset_rfl (Finset.mem_univ n) v (Finset.mem_univ v) hv
  · rintro ⟨w, hw⟩ d ⟨v, hv⟩
    by_cases hd : Finset.univ ⊆ d
    · refine ⟨w, Finset.mem_filter.2 ⟨hd (Finset.mem_univ w), (normal_ofRules_iff ..).2
        ⟨hd (Finset.mem_univ w), fun r hr _ _ u _ hu ↦ hw u r hr hu⟩⟩⟩
    · exact ⟨v, Finset.mem_filter.2 ⟨hv, (normal_ofRules_iff ..).2 ⟨hv,
        fun r hr hsub ↦ (hd (hR r hr ▸ hsub)).elim⟩⟩⟩

theorem isGeneral_of_rules_eq_nil (h : σ.rules = []) : σ.IsGeneral :=
  ⟨by simp [h], by simp [h], fun d ⟨w, hw⟩ ↦
    ⟨w, Finset.mem_filter.2 ⟨hw, (normal_ofRules_iff ..).2 ⟨hw, by simp [h]⟩⟩⟩⟩

theorem IsGeneral.normally (h : σ.IsGeneral) (ψ : Finset W) :
    (Veltman1996.normally ψ σ).IsGeneral := by
  unfold Veltman1996.normally rule
  split_ifs with hc
  · refine ⟨?_, ?_, hc.2.1⟩ <;> simp only [List.mem_cons, forall_eq_or_imp]
    exacts [⟨Finset.union_compl ψ, h.domain_eq⟩,
      ⟨hc.1.mono Finset.inter_subset_right, h.default_nonempty⟩]
  · exact isGeneral_of_rules_eq_nil rfl

theorem IsGeneral.fact (h : σ.IsGeneral) (φ : Finset W) :
    (Veltman1996.fact φ σ).IsGeneral := by
  unfold Veltman1996.fact
  split_ifs
  exacts [⟨h.1, h.2, h.3⟩, isGeneral_of_rules_eq_nil rfl]

omit [DecidableEq W] in
@[simp] theorem toOrderedInformationState_init : (init : State W).toOrderedInformationState = ⊤ :=
  OrderedInformationState.ext (by simp [toOrderedInformationState, init])
    (by simp [toOrderedInformationState, init])

/-- An update with a general rule that does not crash is the promotion of section 3. -/
theorem toOrderedInformationState_normally (h : normally ψ σ ≠ absurd) :
    (normally ψ σ).toOrderedInformationState = σ.toOrderedInformationState.promote (· ∈ ψ) := by
  unfold normally rule at h ⊢
  split_ifs at h ⊢
  · refine OrderedInformationState.ext rfl ?_
    rw [toOrderedInformationState, show {r | r ∈ (⟨ψ ∪ ψᶜ, ψ⟩ : Rule W) :: σ.rules} =
      insert ⟨ψ ∪ ψᶜ, ψ⟩ {r | r ∈ σ.rules} from Set.ext fun _ ↦ List.mem_cons,
      Preorder.ofCriteria_insert]
    rfl
  · exact (h rfl).elim

omit [Fintype W] in
/-- An update with a fact that does not crash is the assertion of section 3. -/
theorem toOrderedInformationState_fact (h : fact φ σ ≠ absurd) :
    (fact φ σ).toOrderedInformationState = σ.toOrderedInformationState.assert (· ∈ φ) := by
  unfold fact at h ⊢
  split_ifs at h ⊢
  · exact OrderedInformationState.ext (Finset.coe_inter _ _) rfl
  · exact (h rfl).elim

/-- On a general state with information, the update with a general rule crashes exactly when no
normal world of the pattern of section 3 is a `ψ`-world, Veltman's condition for *normally ψ* in
section 3 (Definitions 3.3 and 3.9). -/
theorem IsGeneral.normally_eq_absurd_iff (h : σ.IsGeneral) (hσ : σ.info.Nonempty) :
    Veltman1996.normally ψ σ = absurd ↔
      ¬∃ w, (∀ v, σ.toOrderedInformationState.order.le w v) ∧ w ∈ ψ := by
  obtain ⟨w₀, hw₀⟩ := hσ
  have : Nonempty W := ⟨w₀⟩
  have hgen : ∀ r ∈ (⟨ψ ∪ ψᶜ, ψ⟩ : Rule W) :: σ.rules, r.domain = Finset.univ := by
    simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Finset.union_compl ψ, h.domain_eq⟩
  have key : (((ψ ∪ ψᶜ) ∩ ψ).Nonempty ∧ Coherent (Frame.ofRules (⟨ψ ∪ ψᶜ, ψ⟩ :: σ.rules)) ∧
      σ.info.Nonempty) ↔ ∃ w, (∀ v, σ.toOrderedInformationState.order.le w v) ∧ w ∈ ψ := by
    rw [coherent_ofRules_iff hgen, Finset.union_compl, Finset.univ_inter]
    constructor
    · rintro ⟨⟨u, hu⟩, ⟨w, hw⟩, -⟩
      exact ⟨w, fun v r hr ↦ hw v r (List.mem_cons_of_mem _ hr), hw u _ List.mem_cons_self hu⟩
    · rintro ⟨w, hw, hwψ⟩
      refine ⟨⟨w, hwψ⟩, ⟨w, fun v r hr hv ↦ ?_⟩, ⟨w₀, hw₀⟩⟩
      rcases List.mem_cons.1 hr with rfl | hr
      · exact hwψ
      · exact hw v r hr hv
  unfold Veltman1996.normally rule
  split_ifs with hc
  · exact iff_of_false (fun he ↦ List.cons_ne_nil _ _ (congrArg State.rules he))
      (not_not.2 (key.1 hc))
  · exact iff_of_true rfl fun hex ↦ hc (key.2 hex)

/-- On a general state other than the absurd one, *presumably φ* passes exactly when `φ` holds at
the optimal worlds of section 3, so that the presumptions of section 4 extend those of
section 3. -/
theorem IsGeneral.presumably_eq_self_iff (h : σ.IsGeneral) (hσ : σ ≠ absurd) :
    presumably φ σ = σ ↔ σ.toOrderedInformationState.boxLe (· ∈ φ) := by
  rw [OrderedInformationState.boxLe, ← h.optimal_eq, presumably]
  refine ⟨fun he w hw ↦ by_contra fun hφ ↦ hσ ?_, fun hb ↦ ite_eq_left fun w hw ↦ hb w hw⟩
  rw [← he, ite_eq_right fun hs ↦ hφ (hs hw)]

end State

/-! ### Veltman's eight worlds -/

/-- The world `wᵢ` is the set of atoms whose bits are set in `i`, so `w₀ = ∅`, `w₁ = {p}`, `w₂ =
{q}`, `w₃ = {p, q}`, `w₄ = {r}`, …, `w₇ = {p, q, r}`. -/
abbrev World := Fin 8

def p : Finset World := Finset.univ.filter (·.val % 2 = 1)
def q : Finset World := Finset.univ.filter (·.val / 2 % 2 = 1)
def r : Finset World := Finset.univ.filter (·.val / 4 % 2 = 1)

-- Examples 3.10(i): once *normally p* is accepted, the opposite rule crashes the state
theorem ex310_conflict : (State.init |> normally p |> normally pᶜ) = State.absurd := by
  decide +kernel

-- Examples 4.8, (iii)
theorem ex48 :
    (State.init |> normally p |> rule q pᶜ) ≠ State.absurd ∧
      (State.init |> normally p |> rule q pᶜ |> rule qᶜ pᶜ) = State.absurd ∧
      (State.init |> normally p |> rule q pᶜ |> normally q) = State.absurd := by
  decide +kernel

-- Examples 4.11, (iii), §4
theorem ex411_specificity :
    Valid [normally p, rule q pᶜ, fact q] (presumably pᶜ) ∧
      Valid [normally p, rule q pᶜ, fact (q ∩ r)] (presumably pᶜ) ∧
      Valid [normally p, rule q pᶜ, rule (q ∩ r) p, fact (q ∩ r)] (presumably p) := by
  decide +kernel

/-- A restricted rule is not a default of the whole pattern: after *normally p* and *if q, then
normally ¬p*, learning `q` leaves the `p ∧ q`-world out of the optimal worlds (Examples 4.11(i)),
although the ordering that both defaults induce ranks no `q`-world strictly below it. -/
example : (3 : World) ∉ (State.init |> normally p |> rule q pᶜ |> fact q).optimal ∧
    (3 : World) ∈
      (State.init |> normally p |> rule q pᶜ |> fact q).toOrderedInformationState.optimal := by
  have hσ : (State.init |> normally p |> rule q pᶜ |> fact q) =
      ⟨[⟨q, pᶜ⟩, ⟨p ∪ pᶜ, p⟩], Finset.univ ∩ q⟩ := by decide +kernel
  rw [hσ]
  refine ⟨by decide +kernel, (by decide : (3 : World) ∈ Finset.univ ∩ q), fun v _ hv3 r hr hrv ↦ ?_⟩
  have hp3 : (3 : World) ∈ p := by decide
  rcases List.mem_pair.1 hr with rfl | rfl
  · exact absurd (hv3 _ (List.mem_cons_of_mem _ List.mem_cons_self) hp3) (Finset.mem_compl.1 hrv)
  · exact hp3

-- Example 4.11
theorem ex411_iv : Valid [rule p r, rule q (p ∩ rᶜ), fact (p ∩ q)] (presumably rᶜ) := by
  decide +kernel

-- Example 4.11, §5
theorem nixon :
    ¬Valid [rule p r, rule q rᶜ, fact (p ∩ q)] (presumably r) ∧
      ¬Valid [rule p r, rule q rᶜ, fact (p ∩ q)] (presumably rᶜ) := by
  decide +kernel

-- Example 4.11, §5
theorem ex411_vi : Valid [rule q p, rule p r, fact q] (presumably r) := by
  decide +kernel

/-! ### Comparisons (§5) -/

theorem students : Valid [rule p r, rule q rᶜ, rule q p, fact q] (presumably (p ∩ rᶜ)) := by
  decide +kernel

theorem independence : Valid [rule q p, rule q rᶜ, fact q, fact r] (presumably p) := by
  decide +kernel

theorem defeasibleModusTollens : Valid [rule p q, fact qᶜ] (presumably pᶜ) := by
  decide +kernel

theorem modusPonens_over_modusTollens :
    Valid [rule p q, rule q pᶜ, fact p] (presumably q) := by
  decide +kernel

theorem substitution_fails : ¬Valid [rule q p, rule p qᶜ, fact q] (presumably qᶜ) := by
  decide +kernel

theorem hypotheticalSyllogism_fails : ¬Valid [rule q p, rule p r] (rule q r) := by
  decide +kernel

theorem contraposition_fails : ¬Valid [rule p q] (rule qᶜ pᶜ) := by
  decide +kernel

theorem strengthening :
    Valid [rule p q, fact (p ∩ r)] (presumably q) ∧ ¬Valid [rule p q] (rule (p ∩ r) q) := by
  decide +kernel

theorem nearValid :
    (State.init |> rule p q |> rule p r |> rule (p ∩ q) r) ≠ State.absurd ∧
      ¬Valid [rule p q, rule p r] (rule (p ∩ q) r) ∧
      (State.init |> rule p r |> rule q r |> rule (p ∪ q) r) ≠ State.absurd ∧
      ¬Valid [rule p r, rule q r] (rule (p ∪ q) r) := by
  decide +kernel

end Veltman1996
