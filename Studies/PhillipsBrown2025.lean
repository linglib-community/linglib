module

public import Linglib.Semantics.Questions.Partition.Basic
public import Linglib.Semantics.Attitudes.Preference.BestWorlds
public import Linglib.Semantics.Attitudes.Preference.Conditional
public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Core.Order.OfCriteria
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Powerset

/-!
# Phillips-Brown (2025): Some-Things-Considered Desire

Phillips-Brown gives a question-based semantics for desire ascriptions. Conflicting ascriptions,
*you want to take a nap* and *you don't want to take a nap* both true, falsify the belief-based
semantics of Heim and von Fintel, which evaluate the agent's preferences over her whole belief set
with no context sensitivity, and a context-sensitive preference relation that values whole worlds
overgenerates, predicting *you want to fail the exam* wherever *Nap* is true. The proposal
evaluates an ascription against a contextual question, a partition of the worlds: the answers
compatible with the beliefs are ranked by the desires they entail, *S wants p* holds when every
best answer entails *p* (`Want`), and the ascription is defined only if the question decides *p*,
is diverse, does not stack the deck, and the beliefs are sensitive to it (`Defined`).

## Implementation notes

* A question is a `Setoid`, its answers the cells; the question raised by a list of issues is
  their `Setoid.ofProps`, and *p* is considered relative to a question when the question
  decides it. Answers are ordered by the desires they entail, Kratzer's ordering with
  entailment as satisfaction (`entailed`), and the best answers are the `MaximalFor` elements
  of that valuation.
* The act, its benefit and its cost are the three issues of the nap and lobster cases (nap,
  feeling rested, failing the exam; eating the lobster, the gustatory experience, dying), the
  beliefs tying benefit and cost to the act, and the desires being the benefit and not the
  cost. The Anti-deckstacking Constraint quantifies over all propositions; read so, it admits
  only the finest partition (`antiDeckstacking_univ_singleton`), so it is restricted here to a
  list of salient propositions, the issues of each case.
* Heim's semantics is the conditional one, `Desire.Conditional.Want`, with the similar worlds
  drawn from the belief worlds, as Phillips-Brown presents it. Levinson's expected-value
  comparison, the sufficient-desirability semantics of §2.4, and the Heimian question-based
  semantics of footnote 16 are prose.

## References

* [phillips-brown-2025]
* [heim-1992]
* [von-fintel-1999]
* [villalta-2008]
* [yalcin-2018]
* [kratzer-1981]
-/

@[expose] public section

namespace PhillipsBrown2025

open Desire Presupposition

section Semantics

variable {W : Type*} (G N : List (Finset W)) (s : Setoid W) (bel p : Set W)

/-! ### Question-based desire (§3) -/

/-- An answer, the cell of `w`, compatible with the beliefs. -/
def Live (w : W) : Prop := ∃ v ∈ s.cell w, v ∈ bel

/-- The desires an answer entails, by whose inclusion answers are ordered. -/
abbrev entailed : W → Set (Finset W) := Preorder.satisfied (fun w g ↦ s.cell w ⊆ ↑g) {g | g ∈ G}

/-- `S wants p` holds when every best live answer entails `p`. -/
def Want : Prop := ∀ w, MaximalFor (Live s bel) (entailed G s) w → s.cell w ⊆ p

/-- Some answer entails `p` and some entails `¬p`. -/
def IsDiverse : Prop := (∃ w, s.cell w ⊆ p) ∧ ∃ w, s.cell w ⊆ pᶜ

/-- Every salient proposition in `N` that some answer entails is itself decided. -/
def IsAntiDeckstacking : Prop := ∀ q ∈ N, (∃ w, s.cell w ⊆ ↑q) → s.Decides ↑q

/-- The beliefs discriminate among the answers when some answer is live and some is not. -/
def IsBelSensitive : Prop := (∃ w, Live s bel w) ∧ ∃ w, ¬ Live s bel w

/-- The four metasemantic constraints jointly. -/
def Defined : Prop :=
  s.Decides p ∧ IsDiverse s p ∧ IsAntiDeckstacking N s ∧ IsBelSensitive s bel

open Classical in
/-- Question-based *want* as a trivalent proposition, with its definedness conditions as
presupposition. -/
noncomputable def want : W → SignType :=
  {_w | Defined N s bel p}.indicator fun _ ↦ SignType.ofProp (Want G s bel p)

section Decidable

variable [Fintype W] [DecidableEq W] [DecidableRel s] [DecidablePred (· ∈ bel)]
  [DecidablePred (· ∈ p)]

instance (w : W) : Decidable (Live s bel w) := inferInstanceAs (Decidable (∃ v ∈ s.cell w, _))

instance (w : W) : Decidable (MaximalFor (Live s bel) (entailed G s) w) :=
  inferInstanceAs (Decidable (Live s bel w ∧ ∀ z, Live s bel z → _ → _))

instance : Decidable (Want G s bel p) := inferInstanceAs (Decidable (∀ _, _ → _))

instance : Decidable (IsDiverse s p) := inferInstanceAs (Decidable (_ ∧ _))

instance : Decidable (IsAntiDeckstacking N s) := inferInstanceAs (Decidable (∀ q ∈ N, _ → _))

instance : Decidable (IsBelSensitive s bel) := inferInstanceAs (Decidable (_ ∧ _))

instance : Decidable (Defined N s bel p) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

end Decidable

variable {G N s bel p} {q : Set W}

theorem Want.mono (hpq : p ⊆ q) (h : Want G s bel p) : Want G s bel q :=
  fun w hw ↦ (h w hw).trans hpq

theorem exists_best [Finite W] (h : ∃ w, Live s bel w) :
    ∃ w, MaximalFor (Live s bel) (entailed G s) w :=
  Set.Finite.exists_maximalFor _ {w | Live s bel w} (Set.toFinite _) h

theorem not_want_of_not_exists [Finite W] (hlive : ∃ w, Live s bel w)
    (hp : ¬ ∃ w, s.cell w ⊆ p) : ¬ Want G s bel p := fun hw ↦
  let ⟨w, hb⟩ := exists_best (G := G) hlive
  hp ⟨w, hw w hb⟩

theorem want_of_decides_of_not_exists (hc : s.Decides p) (hnp : ¬ ∃ w, s.cell w ⊆ pᶜ) :
    Want G s bel p := fun w _ ↦
  (Setoid.decides_iff_forall_cell.1 hc w).resolve_right fun h ↦ hnp ⟨w, h⟩

/-- The semantics is Strawson upward monotone, since where both ascriptions are defined,
`want p` entails `want q` for `p ⊆ q`. -/
theorem want_strawsonEntails (hpq : p ⊆ q) :
    strawsonEntails (want G N s bel p) (want G N s bel q) := fun _ hp hq ↦ by
  simp_all [want]
  exact hp.2.mono hpq

/-- On the finest question, question-based *want* is best-worlds *want* (§3.4). -/
theorem want_bot_iff :
    Want G ⊥ bel p ↔ BestWorlds.Want ((fun s w ↦ w ∈ s) '' {s | s ∈ G}) bel p := by
  simp only [Want, BestWorlds.want_iff, Preorder.ofCriteria_le_iff, Set.forall_mem_image,
    MaximalFor, Live,
    entailed, Preorder.satisfied, Setoid.cell_bot, Set.mem_singleton_iff, exists_eq_left,
    Set.singleton_subset_iff, Set.ofPred_subset_ofPred, Finset.mem_coe, and_imp]
  simp +contextual [Set.mem_ofPred_eq]

end Semantics

/-! ### The nap and lobster cases (§2.1, §2.2) -/

/-- A state records whether the act is done, whether its benefit obtains and whether its cost
obtains. -/
structure World where
  act : Bool
  benefit : Bool
  cost : Bool
  deriving DecidableEq

instance : Fintype World :=
  Fintype.ofEquiv (Bool × Bool × Bool)
    ⟨fun t ↦ ⟨t.1, t.2.1, t.2.2⟩, fun w ↦ (w.act, w.benefit, w.cost), fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- The act is napping, or eating the lobster. -/
def act : Finset World := Finset.univ.filter (·.act)

/-- Its benefit is feeling rested, or the gustatory experience. -/
def benefit : Finset World := Finset.univ.filter (·.benefit)

/-- Its cost is failing the exam, or dying of anaphylactic shock. -/
def cost : Finset World := Finset.univ.filter (·.cost)

/-- The beliefs have the benefit and the cost each come exactly with the act. -/
def bel : Set World := {w | w.benefit = w.act ∧ w.cost = w.act}

instance : DecidablePred (· ∈ bel) :=
  fun w ↦ inferInstanceAs (Decidable (w.benefit = w.act ∧ w.cost = w.act))

/-- The desires are the benefit and not the cost. -/
def desires : List (Finset World) := [benefit, costᶜ]

/-- Von Fintel's semantics cannot make *Nap* and *Not-nap* both true, whatever the desires,
since some belief-world is best and it settles the act one way. -/
theorem vonFintel_no_conflict (A : Set (World → Prop)) :
    ¬ (BestWorlds.Want A bel ↑act ∧ BestWorlds.Want A bel (↑act : Set World)ᶜ) :=
  fun ⟨h, h'⟩ ↦ h.not_compl ⟨⟨true, true, true⟩, by decide⟩ h'

/-- Neither can Heim's, under her definedness amendment and antisymmetric desirability. -/
theorem heim_no_conflict (F : Conditional.Frame World) (w : World) [Std.Antisymm (F.pref w)]
    (hd : Desire.IsContingent bel ↑act) :
    ¬ (Conditional.Want F bel bel w ↑act ∧ Conditional.Want F bel bel w (↑act : Set World)ᶜ) :=
  fun ⟨h, h'⟩ ↦ h.not_compl (hd.1.mono Set.inter_subset_left) hd h'

/-- On a belief-based semantics, wanting the act is wanting the cost believed to come with it
(§4.1). -/
theorem closure_under_doxastic_equivalence (A : Set (World → Prop))
    (h : BestWorlds.Want A bel ↑act) : BestWorlds.Want A bel ↑cost :=
  h.mono_on (by decide +kernel)

local instance :
    DecidableRel (Modality.premisePreorder ({(· ∈ benefit)} : Set (World → Prop))).le :=
  fun w z ↦ decidable_of_iff (z ∈ benefit → w ∈ benefit) (by simp [Preorder.ofCriteria_le_iff])

/-- A context-sensitive preference relation overgenerates (§2.2), since the value of feeling
rested makes *Nap* true, and with it *Fail*. -/
theorem cpr_overgenerates :
    BestWorlds.Want {(· ∈ benefit)} bel ↑act ∧ BestWorlds.Want {(· ∈ benefit)} bel ↑cost :=
  ⟨by decide, closure_under_doxastic_equivalence _ (by decide +kernel)⟩

/-! ### Some-things-considered desire (§3) -/

/-- The question considering whether the act is done and whether its benefit obtains
(Figure 3). -/
def qBenefit : Setoid World := Setoid.ofProps {act, benefit}

/-- The question considering whether the act is done and whether its cost obtains
(Figure 5). -/
def qCost : Setoid World := Setoid.ofProps {act, cost}

instance : DecidableRel qBenefit := inferInstanceAs (DecidableRel (Setoid.ofProps _))
instance : DecidableRel qCost := inferInstanceAs (DecidableRel (Setoid.ofProps _))

/-- The salient propositions of the case, the test set of the anti-deckstacking constraint. -/
def issues : List (Finset World) := [act, benefit, cost]

/-- Considering the act and its benefit, *Nap* and *Lobster* are defined and true. -/
theorem act_true : Defined issues qBenefit bel ↑act ∧ Want desires qBenefit bel ↑act := by
  decide +kernel

/-- In that context the cost is ignored, so *Fail* and *Die* are undefined (§3.6), which blocks
the inference from *Nap* to *Fail* (§4.1). -/
theorem cost_undefined : ¬ qBenefit.Decides ↑cost := by decide +kernel

/-- Considering the act and its cost, not doing the act is wanted, *Not-nap* and *Not-lobster*,
and so is avoiding the cost, *Not-die*. -/
theorem not_act_true :
    Defined issues qCost bel (↑act : Set World)ᶜ ∧ Want desires qCost bel (↑act : Set World)ᶜ ∧
      Want desires qCost bel (↑cost : Set World)ᶜ := by
  decide +kernel

/-! ### Deck-stacking (§3.7) -/

/-- A state of Lu's case records whether it rains and whether Lu is happy. -/
structure LuWorld where
  rain : Bool
  happy : Bool
  deriving DecidableEq

instance : Fintype LuWorld :=
  Fintype.ofEquiv (Bool × Bool)
    ⟨fun t ↦ ⟨t.1, t.2⟩, fun w ↦ (w.rain, w.happy), fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- It rains tomorrow. -/
def rain : Finset LuWorld := Finset.univ.filter (·.rain)

/-- Lu is happy tomorrow. -/
def happy : Finset LuWorld := Finset.univ.filter (·.happy)

/-- Lu believes she is happy whatever the weather. -/
def belLu : Set LuWorld := {w | w.happy = true}

instance : DecidablePred (· ∈ belLu) := fun w ↦ inferInstanceAs (Decidable (w.happy = true))

/-- The deck-stacked question (Figure 7) asks whether it rains, and if not, whether Lu is
happy. -/
def qStacked : Setoid LuWorld := Setoid.ker fun w ↦ if w.rain then none else some w.happy

/-- The level playing field (Figure 9). -/
def qFair : Setoid LuWorld := Setoid.ofProps {rain, happy}

instance : DecidableRel qStacked := inferInstanceAs (DecidableRel (Setoid.ker _))
instance : DecidableRel qFair := inferInstanceAs (DecidableRel (Setoid.ofProps _))

/-- Without the constraint the deck-stacked question makes *Lu wants it not to rain* true,
though Lu is indifferent to the weather; the level playing field makes it false. -/
theorem not_rain_deckstacked :
    Want [happy] qStacked belLu (↑rain : Set LuWorld)ᶜ ∧
      ¬ Want [happy] qFair belLu (↑rain : Set LuWorld)ᶜ := by
  decide +kernel

/-- The deck-stacked question violates the constraint at *happy*, which one answer entails and
another leaves open, while the level playing field satisfies it for every proposition. -/
theorem deckstacked_excluded :
    ¬ IsAntiDeckstacking [happy] qStacked ∧
      ∀ q : Finset LuWorld, (∃ w, qFair.cell w ⊆ ↑q) → qFair.Decides ↑q := by
  decide +kernel

theorem antiDeckstacking_univ_singleton {W : Type*} {s : Setoid W}
    (h : ∀ q : Set W, (∃ w, s.cell w ⊆ q) → s.Decides q) {w₁ w₂ w₃ : W} (h₁₂ : s w₁ w₂)
    (h₁₃ : ¬ s w₁ w₃) : w₁ = w₂ := by
  by_contra hne
  have hq := Setoid.decides_iff.1 (h (s.cell w₃ ∪ (s.cell w₁ \ {w₂})) ⟨w₃, Set.subset_union_left⟩)
  rcases (hq w₁ w₂ h₁₂).1 (Or.inr ⟨s.refl' w₁, hne⟩) with h | ⟨_, h⟩
  · exact h₁₃ (s.trans' h₁₂ h)
  · exact h rfl

/-! ### Belief-sensitivity (§4.2) -/

/-- An agent whose beliefs are insensitive to every question that decides `p`, William III and
England avoiding nuclear war with France, has *S wants p* undefined in every context, since
where `p` is decided the beliefs are insensitive, and where they are sensitive `p` is not
decided. -/
theorem undefined_of_insensitive {W : Type*} {bel p : Set W}
    (h : ∀ s : Setoid W, s.Decides p → ¬ IsBelSensitive s bel) (N : List (Finset W))
    (s : Setoid W) : ¬ Defined N s bel p :=
  fun hd ↦ h s hd.1 hd.2.2.2

end PhillipsBrown2025
