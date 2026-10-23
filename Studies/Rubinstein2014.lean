module

public import Linglib.Semantics.Modality.Directive
public import Linglib.Fragments.English.Auxiliaries
public import Linglib.Data.Examples.Rubinstein2014
public import Mathlib.Data.Fintype.Prod

/-!
# Rubinstein (2014): On Necessity and Comparison

This file formalizes Rubinstein's account of weak necessity as comparison. Following
Sloman (1970), the priorities of Kratzer's ordering source are split by negotiability
((48)–(49)): the priorities every participant is committed to are promoted to the modal base and,
with the circumstances, delimit the favored worlds through Frank's compatibility-restricted
union ((39)–(40)), while the negotiable priorities an opinionated assessor promotes remain an
ordering source. Strong necessity is simple necessity over the favored worlds (41), weak
necessity is human necessity over them under the negotiable ordering (42), and the ordering
source of a weak necessity presupposes negotiability (50). The tax-report dialogue is the shift
from *should* to *have to* as an ideal stops being negotiable ((46), (51)), and neg-raising
follows from the choice between a negotiable ideal and its negation (§3.4.2). Weak necessity
modals form a natural class with the evaluative comparatives *good*, *better*, *preferable* and
*worthwhile*, diagnosed by the strength tests of §2.1 and by neg-raising after Horn (1978), and
Hebrew reaches weak necessity through the comparatives alone.

## Main definitions

* `Backgrounds`, `extensions`, `favoredWorlds`: the circumstances, the promoted priorities and
  the negotiable ordering source; the maximal consistent sets of promoted priorities; and Frank's
  union over them.
* `strongNecessity`, `weakNecessity`: (41) and (42).
* `Negotiable`: (49), a list of ideals some participant is not committed to.

## Main results

* `favoredWorlds_eq_bestWorlds`: Frank's compatibility-restricted union is Kratzer's best worlds
  under the promoted priorities, a best world being one whose verified priorities form a maximal
  consistent set (`verified_mem_extensions`, `mem_bestWorlds_of_extension`), so the two
  necessities are von Fintel and Iatridou's strong and weak necessity with the split ordering
  source (`strongNecessity_iff`, `weakNecessity_iff`); the analyses differ only in the
  negotiability presupposition.
* `tax_shift`: the negotiable ideal makes *should* true and *have to* false, and its endorsement
  leaves it non-negotiable and makes *have to* true.
* `weakNecessity_ideal`, `weakNecessity_neg_of_not`: a choice of ideal is a choice of weak
  necessities, from which the neg-raising inference for the ideal follows.
* `negRaising_iff_comparative`, `carix_negRaises`, `strength_tests`: over the paper's English,
  Hebrew and Spanish rows, neg-raising and the strength tests pick out the weak necessities, with
  *carix* the paper's apparent exception.

## Implementation notes

* Commitment (48) is data, a finite set of ideals per participant, and an ideal list is
  negotiable when some participant is not committed to one of its members. The presupposition
  (50) is stated through the negotiability conjuncts of `tax_shift` rather than as a partial
  operator. Backgrounds are relative to worlds, not to the paper's events.
* The neg-raising rows of Horn (1978) carry Horn's page numbers as their source labels. Narrog's
  survey (Table 1) and the tentative possibility semantics for *preferable* are not formalized.

## References

* [rubinstein-2014]
* [kratzer-1981]
* [frank-1996]
* [sloman-1970]
* [horn-1978]
* [von-fintel-iatridou-2008]
-/

@[expose] public section

namespace Rubinstein2014

open Modality

variable {W : Type*}

/-! ### Favored worlds ((39)–(40)) -/

/-- Modal backgrounds with the ordering source split by negotiability. -/
structure Backgrounds (W : Type*) where
  /-- The circumstances, the modal base proper. -/
  circumstances : Background W
  /-- The non-negotiable priorities, promoted to the modal base. -/
  nonNegotiable : Background W
  /-- The negotiable priorities, which remain an ordering source. -/
  negotiable : Background W

/-- A set of priorities is consistent with the circumstances at `w` when some accessible world
verifies all of them. -/
def ConsistentWith (b : Backgrounds W) (w : W) (X : Set (W → Prop)) : Prop :=
  ∃ v ∈ b.circumstances.accessibleWorlds w, ∀ q ∈ X, q v

/-- The maximal sets of promoted priorities consistent with the circumstances (39), the sets
[frank-1996]'s compatibility-restricted union adds to the circumstances. -/
def extensions (b : Backgrounds W) (w : W) : Set (Set (W → Prop)) :=
  {X | Maximal (fun Y ↦ Y ⊆ {q | q ∈ b.nonNegotiable w} ∧ ConsistentWith b w Y) X}

/-- The favored worlds (40), the accessible worlds verifying some maximal consistent set of
promoted priorities. -/
def favoredWorlds (b : Backgrounds W) (w : W) : Set W :=
  ⋃ X ∈ extensions b w, {u ∈ b.circumstances.accessibleWorlds w | ∀ q ∈ X, q u}

/-- The promoted priorities a world verifies. -/
def verified (b : Backgrounds W) (w u : W) : Set (W → Prop) :=
  Preorder.satisfied (fun v q ↦ q v) {q | q ∈ b.nonNegotiable w} u

variable {b : Backgrounds W} {p : W → Prop} {w : W}

theorem atLeastAsGoodAs_iff_verified_subset {u v : W} :
    (v ≤[b.nonNegotiable w] u) ↔ verified b w u ⊆ verified b w v :=
  (Preorder.satisfied_subset_iff _ _ u v).symm

/-- The priorities a best world verifies form a maximal consistent extension. -/
theorem verified_mem_extensions {u : W} (hu : u ∈ bestWorlds b.circumstances b.nonNegotiable w) :
    verified b w u ∈ extensions b w :=
  ⟨⟨fun _ hq ↦ hq.1, u, hu.1, fun _ hq ↦ hq.2⟩, fun _ ⟨hYh, _, hv, hvY⟩ hXY q hq ↦
    atLeastAsGoodAs_iff_verified_subset.1 (hu.2 hv (atLeastAsGoodAs_iff_verified_subset.2
      fun q' hq' ↦ ⟨hYh (hXY hq'), hvY q' (hXY hq')⟩)) ⟨hYh hq, hvY q hq⟩⟩

/-- A world verifying a maximal consistent extension is best. -/
theorem mem_bestWorlds_of_extension {X : Set (W → Prop)} {u : W} (hX : X ∈ extensions b w)
    (hu : u ∈ b.circumstances.accessibleWorlds w) (huX : ∀ q ∈ X, q u) :
    u ∈ bestWorlds b.circumstances b.nonNegotiable w := by
  have hX' : Maximal (fun Y ↦ Y ⊆ {q | q ∈ b.nonNegotiable w} ∧ ConsistentWith b w Y) X := hX
  refine ⟨hu, fun v hv hvu ↦ atLeastAsGoodAs_iff_verified_subset.2 fun q hq ↦ ⟨hq.1, huX q ?_⟩⟩
  exact hX'.le_of_ge ⟨fun _ hq' ↦ hq'.1, v, hv, fun _ hq' ↦ hq'.2⟩
    (fun q' hq' ↦ atLeastAsGoodAs_iff_verified_subset.1 hvu ⟨hX'.prop.1 hq', huX q' hq'⟩) hq

/-- Frank's union is Kratzer's best worlds under the promoted priorities. -/
theorem favoredWorlds_eq_bestWorlds (b : Backgrounds W) (w : W) :
    favoredWorlds b w = bestWorlds b.circumstances b.nonNegotiable w := by
  ext u
  simp only [favoredWorlds, Set.mem_iUnion, Set.mem_sep_iff, exists_prop]
  exact ⟨fun ⟨X, hX, hu, huX⟩ ↦ mem_bestWorlds_of_extension hX hu huX,
    fun hu ↦ ⟨_, verified_mem_extensions hu, hu.1, fun _ hq ↦ hq.2⟩⟩

/-! ### The two necessities ((41)–(42)) -/

/-- Strong necessity (41) is simple necessity over the favored worlds. -/
def strongNecessity (b : Backgrounds W) (p : W → Prop) (w : W) : Prop :=
  ∀ v ∈ favoredWorlds b w, p v

/-- Weak necessity (42) is human necessity over the favored worlds under the negotiable
ordering source. -/
def weakNecessity (b : Backgrounds W) (p : W → Prop) (w : W) : Prop :=
  ∀ v ∈ (premisePreorder (b.negotiable w)).minimals (favoredWorlds b w), p v

/-- Strong necessity is [von-fintel-iatridou-2008]'s, with the promoted priorities as the
ordering source. -/
theorem strongNecessity_iff :
    strongNecessity b p w ↔
      Modality.Directive.strongNecessity b.circumstances b.nonNegotiable p w := by
  rw [strongNecessity, favoredWorlds_eq_bestWorlds]; rfl

/-- Weak necessity is [von-fintel-iatridou-2008]'s, with the promoted priorities as the primary
and the negotiable ones as the secondary ordering source: the truth conditions of the two analyses
coincide, and only the presupposition (50) separates them. -/
theorem weakNecessity_iff :
    weakNecessity b p w ↔
      Modality.Directive.weakNecessity b.circumstances b.nonNegotiable b.negotiable p w := by
  rw [weakNecessity, favoredWorlds_eq_bestWorlds]; rfl

theorem strong_entails_weak (h : strongNecessity b p w) : weakNecessity b p w :=
  weakNecessity_iff.2
    (Modality.Directive.strong_entails_weak _ _ _ _ _ (strongNecessity_iff.1 h))

theorem weak_not_entails_strong :
    ¬ ∀ (W : Type) (b : Backgrounds W) (p : W → Prop) (w : W),
        weakNecessity b p w → strongNecessity b p w :=
  fun h ↦ Modality.Directive.weak_not_entails_strong fun W f g g' p w hw ↦
    strongNecessity_iff.1 (h W ⟨f, g, g'⟩ p w (weakNecessity_iff.2 hw))

theorem weakNecessity_iff_strongNecessity (hg : b.negotiable w = ∅) :
    weakNecessity b p w ↔ strongNecessity b p w := by
  simp [weakNecessity, strongNecessity, hg]

/-! ### Negotiability ((48)–(50)) -/

/-- A list of ideals is negotiable (49) when some participant is not committed to one of them,
commitment (48) being the ideals a participant is prepared to argue for. -/
def Negotiable {ι κ : Type*} [DecidableEq κ] (commitment : ι → Finset κ) (ideals : List κ) :
    Prop :=
  ∃ a, ∃ i ∈ ideals, i ∉ commitment a

instance {ι κ : Type*} [Fintype ι] [DecidableEq κ] (commitment : ι → Finset κ)
    (ideals : List κ) : Decidable (Negotiable commitment ideals) :=
  inferInstanceAs (Decidable (∃ a, ∃ i ∈ ideals, i ∉ commitment a))

/-- A choice of ideal is a choice of weak necessities (§3.4.2): with `γ` the negotiable ideal
and `γ` live among the favored worlds, *should γ* holds and *should ¬γ* fails. -/
theorem weakNecessity_ideal {γ : W → Prop} (hγ : b.negotiable w = {γ})
    (hlive : ∃ v ∈ favoredWorlds b w, γ v) :
    weakNecessity b γ w ∧ ¬ weakNecessity b (fun v ↦ ¬ γ v) w := by
  obtain ⟨v, hv, hγv⟩ := hlive
  rw [weakNecessity, weakNecessity, hγ, Preorder.minimals_ofCriteria_eq ⟨v, hv, by simpa⟩]
  exact ⟨fun _ h ↦ h.2 γ (Set.mem_singleton _), fun h ↦ h v ⟨hv, by simpa⟩ hγv⟩

/-- The neg-raising inference for the ideal: when the negotiable ideal is `γ` or its negation and
both are live, *not should γ* yields *should ¬γ*. -/
theorem weakNecessity_neg_of_not {γ : W → Prop}
    (hchoice : b.negotiable w = {γ} ∨ b.negotiable w = {fun v ↦ ¬ γ v})
    (hγ : ∃ v ∈ favoredWorlds b w, γ v) (hnγ : ∃ v ∈ favoredWorlds b w, ¬ γ v)
    (h : ¬ weakNecessity b γ w) : weakNecessity b (fun v ↦ ¬ γ v) w := by
  rcases hchoice with hc | hc
  · exact absurd (weakNecessity_ideal hc hγ).1 h
  · exact (weakNecessity_ideal hc hnγ).1

/-! ### The tax report ((45)–(46), (51)) -/

/-- The clauses of the tax law, reporting domestic and reporting international revenue. -/
inductive Ideal
  /-- Report domestic revenue. -/
  | domestic
  /-- Report international revenue. -/
  | international
  deriving DecidableEq, Repr

/-- A world of the scenario records whether domestic and whether international revenue is
reported. -/
abbrev Revenue := Bool × Bool

/-- The content of a clause. -/
def Ideal.holds : Ideal → Revenue → Prop
  | .domestic, v => v.1 = true
  | .international, v => v.2 = true

/-- The participants of the dialogue (46). -/
inductive Participant
  /-- The accountant, who proposes reporting all revenue. -/
  | accountant
  /-- The manager, who endorses it. -/
  | manager
  deriving DecidableEq, Repr, Fintype

/-- Backgrounds with no circumstances, the promoted clauses `h` and the negotiable clauses
`g`. -/
def ofIdeals (h g : List Ideal) : Backgrounds Revenue :=
  ⟨⊥, fun _ ↦ Ideal.holds '' {i | i ∈ h}, fun _ ↦ Ideal.holds '' {i | i ∈ g}⟩

/-- Before the endorsement the manager is committed to the domestic clause only (51a). -/
def commitmentBefore : Participant → Finset Ideal
  | .accountant => {.domestic, .international}
  | .manager => {.domestic}

/-- After the endorsement both participants are committed to both clauses (51b). -/
def commitmentAfter : Participant → Finset Ideal := fun _ ↦ {.domestic, .international}

/-- Reporting all revenue. -/
def reportAll (v : Revenue) : Prop := v.1 = true ∧ v.2 = true

private theorem favoredWorlds_ofIdeals (h g : List Ideal) (w : Revenue) :
    favoredWorlds (ofIdeals h g) w = {v | ∀ i ∈ h, i.holds v} := by
  have hall : (true, true) ∈ (ofIdeals h g).circumstances.accessibleWorlds w := by
    show (true, true) ∈ Background.accessibleWorlds ⊥ w
    rw [Background.accessibleWorlds_bot]; exact Set.mem_univ _
  rw [favoredWorlds_eq_bestWorlds,
    bestWorlds, Preorder.minimals_ofCriteria_eq ⟨(true, true), hall, ?_⟩]
  · ext v
    simp only [ofIdeals, Background.accessibleWorlds_bot, Set.mem_univ, true_and,
      Set.forall_mem_image, Set.mem_ofPred_eq]
  · rintro q ⟨i, -, rfl⟩
    cases i <;> rfl

/-- In (46) and (51), before the endorsement the international clause is negotiable, *we should
report all our revenue* holds and *we have to* does not; after it the clause is no longer
negotiable and *we have to* holds. -/
theorem tax_shift (w : Revenue) :
    (Negotiable commitmentBefore [Ideal.international] ∧
      weakNecessity (ofIdeals [.domestic] [.international]) reportAll w ∧
        ¬ strongNecessity (ofIdeals [.domestic] [.international]) reportAll w) ∧
      (¬ Negotiable commitmentAfter [Ideal.international] ∧
        strongNecessity (ofIdeals [.domestic, .international] []) reportAll w) := by
  refine ⟨⟨by decide, ?_, fun h ↦ ?_⟩, by decide, fun v hv ↦ ?_⟩
  · rw [weakNecessity, favoredWorlds_ofIdeals, Preorder.minimals_ofCriteria_eq ⟨(true, true),
      by simp [Ideal.holds], by simp [ofIdeals, Ideal.holds]⟩]
    rintro v ⟨hd, hi⟩
    exact ⟨hd .domestic (by simp), hi _ ⟨.international, by simp, rfl⟩⟩
  · rw [strongNecessity, favoredWorlds_ofIdeals] at h
    exact Bool.false_ne_true (h (true, false) (by simp [Ideal.holds])).2
  · rw [favoredWorlds_ofIdeals] at hv
    exact ⟨hv .domestic (by simp), hv .international (by simp)⟩

/-! ### The comparative class in the data (§2) -/

/-- The English fragment assigns the modal verb weak necessity. -/
def WeakInFragment (modal : String) : Prop :=
  ∃ a ∈ English.Auxiliaries.modals, a.form = modal ∧ .weakNecessity ∈ a.forces

instance : DecidablePred WeakInFragment := fun _ ↦
  inferInstanceAs (Decidable (∃ a ∈ English.Auxiliaries.modals, _ ∧ _ ∈ _))

/-- An item belongs to the comparative class when it is an evaluative comparative or a modal verb
the fragment marks as weak necessity. -/
def InComparativeClass (e : Datum) : Prop :=
  e.feature? "category" = some "evaluativeComparative" ∨ ∃ m ∈ e.feature? "modal", WeakInFragment m

instance : DecidablePred InComparativeClass := fun _ ↦
  inferInstanceAs (Decidable (_ ∨ ∃ _ ∈ _, _))

/-- The neg-raising stimuli. -/
def negRaisingRows : List Datum :=
  Examples.all.filter fun e ↦ e.feature? "diagnostic" = some "negRaising"

/-- In (30)–(33), the lower-negation reading of a negated attitude is available exactly for the
comparative class, the weak necessity verbs and the evaluative comparatives, and not for the
strong modals, the hybrid *carix* aside. -/
theorem negRaising_iff_comparative :
    ∀ e ∈ negRaisingRows, e.feature? "hybrid" ≠ some "true" →
      (e.readings.lookup "lowerNeg" = some .acceptable ↔ InComparativeClass e) := by
  decide

/-- The hybrid *carix* 'need' (57) neg-raises although it is no comparative, the paper's
apparent exception to the rule. -/
theorem carix_negRaises :
    ∃ e ∈ negRaisingRows, e.feature? "modal" = some "carix" ∧
      e.readings.lookup "lowerNeg" = some .acceptable ∧ ¬ InComparativeClass e := by
  decide

/-- The routes to weak necessity are a dedicated item, a strong modal with weakening morphology,
and evaluative comparative language. -/
inductive Strategy
  /-- A dedicated weak necessity modal, English *ought*. -/
  | lexical
  /-- A strong necessity modal with counterfactual morphology, Spanish *debería*. -/
  | compositional
  /-- An evaluative comparative, Hebrew *yoter tov*. -/
  | evaluativeComparative
  deriving DecidableEq, Repr

/-- The strategy a row exemplifies. -/
def strategy? (e : Datum) : Option Strategy :=
  e.parse? "strategy" [("lexical", Strategy.lexical), ("compositional", .compositional),
    ("evaluativeComparative", .evaluativeComparative)]

/-- The strength tests of (8), (16), (19) and (21), denying strong necessity after the expression
or opposing it to strong necessity with an exclusive, are felicitous exactly for the items that
reach weak necessity by some strategy. -/
theorem strength_tests :
    ∀ e ∈ Examples.all, e.feature? "diagnostic" ∈ [some "test1", some "test2"] →
      (e.judgment = .acceptable ↔ (strategy? e).isSome) := by
  decide

/-- Hebrew has neither a lexical nor a compositional weak necessity (§2.1), its route being the
evaluative comparative. -/
theorem hebrew_comparative_only :
    ∀ e ∈ Examples.all, e.language = "hebr1245" →
      ∀ s ∈ strategy? e, s = .evaluativeComparative := by
  decide

end Rubinstein2014
