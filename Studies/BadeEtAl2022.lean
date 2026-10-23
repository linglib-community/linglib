module

public import Studies.Fox2007
public import Linglib.Processing.Reasoning.Erotetic
public import Linglib.Semantics.Exhaustification.ConjunctiveDisjunct
public import Linglib.Semantics.Modality.Necessity
public import Linglib.Logic.Team.Inquisitive
public import Linglib.Data.Examples.BadeEtAl2022
public import Linglib.Data.Experiments.BadeEtAl2022

/-!
# Bade, Picat, Chung and Mascarenhas (2022): Alternatives and attention in language and reasoning

This file formalizes the illusory-inference apparatus of Bade, Picat, Chung and Mascarenhas's
reply to Mascarenhas and Picat, its two routes to the disjunctive fallacy, and the derivations
the paper runs for the epistemic and deontic possibility modals.

From *(a and b) or else c* and *a*, reasoners conclude *b* about 85% of the time though it does
not follow: the disjunction raises the Hamblin alternatives *a and b* and *c*, the first
alternative carries the hint, and selecting it yields the conclusion by conjunction elimination
(`Erotetic.Problem.Illusory` with the `Matches` rule, the §3.2 hallmark). Mascarenhas and Picat
found the same illusion with *might*, whose attentive content is the alternative set `{φ, ⊤}` of
[ciardelli-groenendijk-roelofsen-2009], so *might (a and b)* is the schema's first premise with
`c` the tautology (`Erotetic.mightProblem_eq_disjunction`, by `rfl`); indefinites instantiate it
with one alternative per witness, under the weaker `Overlaps` rule. The second route is
exhaustification ((4), after [spector-2007]): innocent exclusion against the substitution
alternatives strengthens the disjunction to its exclusive reading
(`Exhaustification.exhIE_conjDisjAlternatives`), from which the conclusion follows classically;
posterior-based accounts, by contrast, cannot separate the conclusions *b* and *c* without a
prior asymmetry (`Erotetic.posterior_eq_iff`). The shared apparatus lives in
`Processing.Reasoning.Erotetic`; this file keeps what is specific to the paper. Footnote 6's
excludability asymmetry is derived (`might_not_excludable`, `allowed_excludable`), as is the
fact that the revised flat premise disarms it for both modals (`revised_flat_not_excludable`).

The experiment's printed contrasts live in `Data.Experiments.BadeEtAl2022`, and §3.2's anatomy
of the illusion is read off the paper's verdict rows: *might* satisfies criteria A–C
(`might_anatomy`) while *allowed to* fails the order and dynamics criteria
(`allowed_not_anatomy`), the paper's ground for classifying the deontic fallacies — about 50%,
and structure-insensitive — as the work of another mechanism, with the package deal of
[merin-1992] and [van-rooy-2000] as the candidate ((16), a datum). The relational route (14)
rests on realism of the modal base: a base is realistic exactly when what is actual is possible
(`Modality.isRealistic_iff_id_le_simplePossibility`), the assumption that is standard for
epistemics and absurd for deontics; with an ordering source, reflexivity alone does not make
best-worlds possibility veridical (`exists_not_possibility`).

## Implementation notes

* Alternatives are Hamblin sets `Set (Set W)`: InqB supports are lower sets, so the attentive
  `φ ∨ ⊤` collapses to `⊤` there (`support_inqDisj_top`), exactly what the attentive proposal
  avoids.
* The indefinite instance uses the `Overlaps` selection rule: its match is on the witness,
  which bare propositions cannot see, and the paper gives no criterion beyond "related to".
* (4b) is `Exhaustification.exhIE_conjDisjAlternatives`; the four-member Sauerland set
  provably does not yield it.
* Criteria A–C of the anatomy are derived from the paper's own contrast verdicts, with the
  marginal order contrast counting as a difference, as the paper's classification requires; D
  and the full classification are the paper's marks in the `anatomy` rows.

## References

* [N. Bade, L. Picat, W. Chung and S. Mascarenhas, *Alternatives and attention in language and
  reasoning: A reply to Mascarenhas & Picat 2019* (2022)][bade-picat-chung-mascarenhas-2022]
* [S. Mascarenhas and L. Picat, *'Might' as a generator of alternatives: The view from
  reasoning* (2019)][mascarenhas-picat-2019]
* [I. Ciardelli, J. Groenendijk and F. Roelofsen, *Attention! 'Might' in Inquisitive Semantics*
  (2009)][ciardelli-groenendijk-roelofsen-2009]
* [P. Koralus and S. Mascarenhas, *The erotetic theory of reasoning* (2013)
  ][koralus-mascarenhas-2013]
* [S. Mascarenhas and P. Koralus, *Illusory inferences with quantifiers*
  (2017)][mascarenhas-koralus-2017]
* [P. Koralus and S. Mascarenhas, *Illusory Inferences in a Question-Based Theory of Reasoning*
  (2018)][koralus-mascarenhas-2018]
* [C. Walsh and P. N. Johnson-Laird, *Co-reference and reasoning*
  (2004)][walsh-johnson-laird-2004]
* [D. Fox, *Free choice and the theory of scalar implicatures* (2007)][fox-2007]
* [B. Spector, *Scalar implicatures: exhaustivity and Gricean reasoning* (2007)][spector-2007]
* [A. Kratzer, *Modality* (1991)][kratzer-1991]
* [A. Merin, *Permission Sentences Stand in the Way of Boolean and Other Lattice-Theoretic
  Semantices* (1992)][merin-1992]
* [R. van Rooy, *Permission to Change* (2000)][van-rooy-2000]
-/

@[expose] public section

namespace BadeEtAl2022

open Set Exhaustification Erotetic Modality ModalLogic

variable {W : Type*}

variable {a b : Set W}

/-! ### Footnote 6: the excludability asymmetry -/

section Flat

variable {R : SetRel W W} {ALT : Set (Set W)}

/-- Under a reflexive frame, `a` entails `◇a`, so `◇a` is never innocently excludable from
`a ∧ ◇b`: *not might a* contradicts *a* (fn 6). -/
theorem might_not_excludable (hR : R.IsRefl) (hfin : ALT.Finite)
    (hsat : (a ∩ R.preimage b).Nonempty) :
    ¬ IsInnocentlyExcludable ALT (a ∩ R.preimage b) (R.preimage a) :=
  not_isInnocentlyExcludable_of_phi_subset hfin hsat fun w hw ↦ ⟨w, hw.1, hR.refl w⟩

/-- Over a frame with a world where `a` holds, `◇b` holds and `◇a` fails, `◇a` is innocently
excludable from `a ∧ ◇b`: the implicature *not allowed to a* is available (fn 6). -/
theorem allowed_excludable (hw : ∃ w ∈ a ∩ R.preimage b, w ∉ R.preimage a) :
    IsInnocentlyExcludable {a ∩ R.preimage b, R.preimage a} (a ∩ R.preimage b)
      (R.preimage a) := by
  obtain ⟨w, hw, hwa⟩ := hw
  refine .of_forall_subset_or_notMem (by simp) hw hwa ?_
  rintro q (rfl | rfl)
  exacts [Or.inl subset_rfl, Or.inr hwa]

/-- The revised flat premise `a ∧ ◇(a ∧ b)` entails `◇a` under every frame. -/
theorem revised_flat_subset : a ∩ R.preimage (a ∩ b) ⊆ R.preimage a :=
  fun _ hw ↦ SetRel.preimage_mono inter_subset_left hw.2

/-- So in the experiment's revised flat condition the implicature is unavailable for both
modals, which fn 6's design change implies but does not state. -/
theorem revised_flat_not_excludable (hfin : ALT.Finite)
    (hsat : (a ∩ R.preimage (a ∩ b)).Nonempty) :
    ¬ IsInnocentlyExcludable ALT (a ∩ R.preimage (a ∩ b)) (R.preimage a) :=
  not_isInnocentlyExcludable_of_phi_subset hfin hsat revised_flat_subset

end Flat

/-! ### The relational route (14) and its deontic absurdity -/

section Relational

/-- With an ordering source, actuality entails best-worlds possibility when the actual world
also verifies the ordering source at itself. -/
theorem possibility_of_isRealistic {f g : Background W} {p : W → Prop}
    {w : W} (hf : f.IsRealistic) (hw : ∀ q ∈ g w, q w) (hp : p w) : possibility f g p w :=
  ⟨w, ⟨hf w, fun _ _ _ q hq _ ↦ hw q hq⟩, hp⟩

/-- Realism of the base alone does not make best-worlds possibility veridical, so (14) needs
more than (14b): the actual world must be among the best-ranked. -/
theorem exists_not_possibility :
    ∃ (f g : Background Bool) (p : Bool → Prop) (w : Bool),
      f.IsRealistic ∧ p w ∧ ¬ possibility f g p w :=
  ⟨⊥, fun _ ↦ {(· = true)}, (· = false), false, fun _ ↦ by simp, rfl,
    fun ⟨v, hvb, hv⟩ ↦ by
      obtain ⟨_, hbest⟩ := mem_bestWorlds.1 (mem_bestAccessible.1 hvb)
      have h := hbest true (accessible_bot _ _)
      simp_all [Preorder.ofCriteria_le_iff]⟩

end Relational

/-! ### Why not InqB (§2.1) -/

section InqB

open Inquisitive

variable {Atom : Type*} [DecidableEq W] (M : Model W Atom) (φ : Formula Atom)

/-- In InqB inquisitive disjunction with the tautology is the tautology, so the attentive content of
(7a) is not expressible there. -/
theorem support_inqDisj_top :
    support M (.inqDisj φ Formula.bot.neg) = support M Formula.bot.neg := by
  simp only [support, himp_self, sup_top_eq]

end InqB

/-! ### The experiment and the anatomy of the illusion (§2.3, §3.2) -/

/-- The design crosses modal, structure and conjunct order into twelve conditions (§2.3.1). -/
theorem conditions_card : Fintype.card (Modal × Structure × Order) = 12 := rfl

/-- Criteria A–C of §3.2 are read off the paper's verdicts on its own contrasts: more fallacies
than baseline, an order-of-premises effect, and no fallacy once the question–answer dynamic is
flattened. The marginal epistemic order contrast counts as a difference, as the paper's
classification of *might* requires; criterion D and the paper's full classification are the
`anatomy` rows. -/
structure Anatomy (m : Modal) : Prop where
  fallacy : (contrasts m .canonicalVsBaseline).verdict ≠ .noDifference
  orderOfPremises : (contrasts m .canonicalVsReversed).verdict ≠ .noDifference
  dynamics : (contrasts m .flatVsBaseline).verdict = .noDifference

instance (m : Modal) : Decidable (Anatomy m) :=
  decidable_of_iff (_ ∧ _ ∧ _) ⟨fun ⟨a, b, c⟩ ↦ ⟨a, b, c⟩, fun ⟨a, b, c⟩ ↦ ⟨a, b, c⟩⟩

/-- *might* shows the full signature of illusory inferences from alternatives (§3.2). -/
theorem might_anatomy : Anatomy .epistemic := by decide

/-- *allowed to* does not (§3.2). -/
theorem allowed_not_anatomy : ¬ Anatomy .deontic := by decide

/-- The deontic fallacies fail the order and the dynamics criteria (§2.4). -/
theorem allowed_fails_order_and_dynamics :
    (contrasts .deontic .canonicalVsReversed).verdict = .noDifference ∧
      (contrasts .deontic .flatVsBaseline).verdict ≠ .noDifference := by decide

/-- Deontic targets drew more fallacious endorsements than epistemic ones in every structure
(Table 5). -/
theorem deontic_more_fallacies : ∀ s, (modalContrasts s).verdict = .lower := by decide

/-- The epistemic order contrast is the marginal one (Table 2), the caveat on criterion B. -/
theorem might_order_marginal :
    (contrasts .epistemic .canonicalVsReversed).verdict = .marginallyHigher := rfl

end BadeEtAl2022
