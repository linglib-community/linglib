/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Mood.Verbal
public import Linglib.Semantics.Attitudes.Preference.BestWorlds
public import Linglib.Fragments.Romance.French.Verbs
public import Linglib.Fragments.Romance.Spanish.Verbs

/-!
# Portner and Rubinstein (2020): Desire, belief, and semantic composition: variation in mood selection with desire predicates

Spanish *querer* 'want' and *esperar* 'hope' both take the subjunctive, while French *vouloir*
takes it and *espérer* the indicative, though the verbs mean the same in the two languages.
Portner and Rubinstein place the variation in composition. The content of a believing situation
is one modal background and that of a desiring situation a pair of an ordering source and a
modal base; the indicative is simple necessity over one background and the subjunctive local
necessity over a pair, and a mood whose force does not fit the content is uninterpretable.
French moods first simplify the content, unifying a pair whose backgrounds are consistent at
every situation. The desires behind *hope* are consistent with the beliefs and those behind
*want* need not be, so French *hope* takes the indicative, with the truth conditions Spanish
*hope* has with the subjunctive.

## Main results

* `spanish_takes`, `french_takes`: the mood each verb takes in each language, which is the mood
  its fragment entry records (`spanish_fragment`, `french_fragment`).
* `french_hope_eq_spanish_hope`: French *hope* with the indicative means what Spanish *hope*
  with the subjunctive means.
* `want_alice_and_want_sue`, `bestWorlds_want_alice_eq_neg_one`: local necessity lets an agent
  want each of two outcomes their beliefs rule out together, which von Fintel's best-worlds
  *want* forbids.
* `not_hope_both`: no one hopes for each of two outcomes their beliefs rule out together.

## Implementation notes

* Backgrounds are relative to worlds rather than situations, and `Backgrounds` holds those of
  one attitude holder; that the desires of *want* need not be consistent with the beliefs⁺ is
  the assumption that at some world they are not.
* The local necessity of (19) quantifies over `f(s)` where `⋂f(s)` is meant.
* The diversity presuppositions and the similarity-semantics version of the fragment are not
  formalized.

## References

* [portner-rubinstein-2020]
* [portner-2018]
* [kratzer-1981]
* [von-fintel-1999]
* [frank-1996]
-/

@[expose] public section

namespace PortnerRubinstein2020

open Modality Mood

variable {W : Type*}

/-! ### Contents and moods -/

/-- The content of an attitude situation is one modal background or a pair of an ordering source
and a modal base. -/
inductive Content (W : Type*) where
  /-- One modal background. -/
  | single (f : Background W)
  /-- An ordering source `g` ranking the worlds of a modal base `f`. -/
  | pair (g f : Background W)

/-- One background targets the informational component and a pair, whose ordering source ranks
worlds, the preferential one. -/
def Content.target : Content W → Component
  | .single _ => .informational
  | .pair _ _ => .preferential

/-- The mood state a content induces at a world. -/
def Content.state : Content W → W → State W
  | .single f, w => .ofExpState (stateAt f ⊥ w)
  | .pair g f, w => .ofExpState (stateAt f g w)

/-- The Spanish moods relate a clause to a world through the force of the mood applied to the
content. A mood and a content that target different components do not combine. -/
def spanish (m : Grammatical) (c : Content W) : Option ((W → Prop) → W → Prop) :=
  if m.target = c.target then some fun p w ↦ m.interp (c.state w) p else none

@[simp] theorem spanish_indicative_single (f : Background W) :
    spanish .indicative (.single f) = some (simpleNecessity f) := rfl

@[simp] theorem spanish_subjunctive_pair (g f : Background W) :
    spanish .subjunctive (.pair g f) = some fun p w ↦ goodPossibility f g p w := rfl

@[simp] theorem spanish_subjunctive_single (f : Background W) :
    spanish .subjunctive (.single f) = none := rfl

@[simp] theorem spanish_indicative_pair (g f : Background W) :
    spanish .indicative (.pair g f) = none := rfl

open Classical in
/-- Simplification unifies a pair whose backgrounds are consistent at every world into one
background, and leaves any other content alone. -/
noncomputable def spl : Content W → Content W
  | .pair g f => if (f ⊔ g).IsConsistent then .single (f ⊔ g) else .pair g f
  | c => c

/-- The French moods apply the Spanish ones to the simplified content. -/
noncomputable def french (m : Grammatical) (c : Content W) : Option ((W → Prop) → W → Prop) :=
  spanish m (spl c)

/-! ### Believe, want and hope -/

/-- The modal backgrounds of an attitude holder. -/
structure Backgrounds (W : Type*) where
  /-- The beliefs. -/
  dox : Background W
  /-- The beliefs⁺, a background compatible with the beliefs, the modal base of *want*. -/
  doxPlus : Background W
  /-- The desires. -/
  bul : Background W
  /-- The consistent desires, the ordering source of *hope*. -/
  bulc : Background W
  /-- The consistent desires are consistent with the beliefs at every world. -/
  consistent : (dox ⊔ bulc).IsConsistent
  /-- The desires are not consistent with the beliefs⁺ at every world. -/
  inconsistent : ¬ (doxPlus ⊔ bul).IsConsistent

namespace Backgrounds

variable (B : Backgrounds W)

/-- A believing situation has the beliefs as content. -/
def believe : Content W := .single B.dox

/-- A wanting situation ranks the beliefs⁺ by the desires. -/
def want : Content W := .pair B.bul B.doxPlus

/-- A hoping situation ranks the beliefs by the consistent desires. -/
def hope : Content W := .pair B.bulc B.dox

theorem spl_believe : spl B.believe = B.believe := rfl

theorem spl_want : spl B.want = B.want := ite_eq_right B.inconsistent

theorem spl_hope : spl B.hope = .single (B.dox ⊔ B.bulc) := ite_eq_left B.consistent

end Backgrounds

variable (B : Backgrounds W) (m : Grammatical)

/-- In Spanish *believe* takes the indicative and *want* and *hope* the subjunctive. -/
theorem spanish_takes :
    ((spanish m B.believe).isSome ↔ m = .indicative) ∧
      ((spanish m B.want).isSome ↔ m = .subjunctive) ∧
      ((spanish m B.hope).isSome ↔ m = .subjunctive) := by
  cases m <;> simp [Backgrounds.believe, Backgrounds.want, Backgrounds.hope]

/-- In French *believe* and *hope* take the indicative and *want* the subjunctive. -/
theorem french_takes :
    ((french m B.believe).isSome ↔ m = .indicative) ∧
      ((french m B.want).isSome ↔ m = .subjunctive) ∧
      ((french m B.hope).isSome ↔ m = .indicative) := by
  simp only [french, B.spl_believe, B.spl_want, B.spl_hope]
  cases m <;> simp [Backgrounds.believe, Backgrounds.want]

/-- French *hope* with the indicative means what Spanish *hope* with the subjunctive means. -/
theorem french_hope_eq_spanish_hope :
    french .indicative B.hope = spanish .subjunctive B.hope := by
  rw [french, B.spl_hope, spanish_indicative_single, Backgrounds.hope, spanish_subjunctive_pair]
  congr 1
  funext p w
  exact propext (goodPossibility_iff_simpleNecessity_sup (B.consistent w)).symm

/-! ### The fragments -/

/-- The coding of a finite clause in a grammatical mood. -/
def coding : Grammatical → Clause.ComplementType
  | .indicative => .indicative
  | .subjunctive => .subjunctive

/-- A verb selects a mood when one of its frames has a clause in that mood. -/
def Selects (v : Verb) (m : Grammatical) : Prop :=
  ∃ fr ∈ v.valency.frames, coding m ∈ fr.codings

instance (v : Verb) (m : Grammatical) : Decidable (Selects v m) :=
  inferInstanceAs (Decidable (∃ fr ∈ v.valency.frames, coding m ∈ fr.codings))

/-- The Spanish entries record the moods the analysis predicts. -/
theorem spanish_fragment :
    (Selects Spanish.Verbs.creer m ↔ (spanish m B.believe).isSome) ∧
      (Selects Spanish.Verbs.querer m ↔ (spanish m B.want).isSome) ∧
      (Selects Spanish.Verbs.esperar m ↔ (spanish m B.hope).isSome) := by
  rw [(spanish_takes B m).1, (spanish_takes B m).2.1, (spanish_takes B m).2.2]
  cases m <;> decide

/-- The French entries record the moods the analysis predicts. -/
theorem french_fragment :
    (Selects French.Verbs.croire m ↔ (french m B.believe).isSome) ∧
      (Selects French.Verbs.vouloir m ↔ (french m B.want).isSome) ∧
      (Selects French.Verbs.esperer m ↔ (french m B.hope).isSome) := by
  rw [(french_takes B m).1, (french_takes B m).2.1, (french_takes B m).2.2]
  cases m <;> decide

/-! ### Conflicting desires

Desiring to marry Alice and desiring to marry Sue, where the beliefs⁺ rule out marrying both:
the worlds where the speaker marries one of them are incomparable under the desires, so each
marriage holds throughout a branch of the ordering and neither holds at every best world. -/

/-- The outcomes are marrying Alice alone, marrying Sue alone, and marrying neither. -/
inductive Marriage where
  | alice | sue | neither
  deriving DecidableEq

/-- Marrying Alice. -/
def marriesAlice : Marriage → Prop := (· = .alice)

/-- Marrying Sue. -/
def marriesSue : Marriage → Prop := (· = .sue)

/-- The beliefs⁺ leave every outcome open. -/
def doxPlus : Background Marriage := ⊥

/-- The desires are to marry Alice and to marry Sue. -/
def bul : Background Marriage := fun _ ↦ {marriesAlice, marriesSue}

/-- The speaker wants to marry Alice and wants to marry Sue. -/
theorem want_alice_and_want_sue (w : Marriage) :
    goodPossibility doxPlus bul marriesAlice w ∧ goodPossibility doxPlus bul marriesSue w :=
  ⟨⟨.alice, by simp [doxPlus], fun _ _ hv ↦ hv marriesAlice (by simp [bul]) rfl⟩,
    ⟨.sue, by simp [doxPlus], fun _ _ hv ↦ hv marriesSue (by simp [bul]) rfl⟩⟩

/-- On von Fintel's best-worlds *want* it is false that the speaker wants to marry Alice, since
the outcome is contingent on the beliefs⁺ and marrying Sue is a best outcome. -/
theorem bestWorlds_want_alice_eq_neg_one (w : Marriage) :
    Desire.BestWorlds.want doxPlus.accessibleWorlds bul marriesAlice w = -1 := by
  refine Desire.BestWorlds.want_eq_neg_one_iff.2
    ⟨⟨⟨.alice, by simp [doxPlus], rfl⟩, .sue, by simp [doxPlus], nofun⟩, fun h ↦ ?_⟩
  have hbest : Marriage.sue ∈ (premisePreorder (bul w)).minimals (doxPlus.accessibleWorlds w) := by
    refine ⟨by simp [doxPlus], fun v _ hvs ↦ ?_⟩
    have hv : v = .sue := (Preorder.ofCriteria_le_iff _ _ _ _).1 hvs marriesSue (by simp [bul]) rfl
    exact hv ▸ (premisePreorder _).le_refl _
  exact Marriage.noConfusion (h hbest : marriesAlice .sue)

/-- No one hopes for each of two outcomes their beliefs rule out together. -/
theorem not_hope_both {p q : W → Prop} {w : W}
    (hpq : ∀ v ∈ B.dox.accessibleWorlds w, ¬ (p v ∧ q v)) :
    ¬ (goodPossibility B.dox B.bulc p w ∧ goodPossibility B.dox B.bulc q w) := by
  rintro ⟨hp, hq⟩
  obtain ⟨b, hb⟩ := B.consistent w
  have hb' := hb
  rw [Background.accessibleWorlds_sup] at hb'
  exact hpq b hb'.1 ⟨simpleNecessity_sup_of_goodPossibility hp b hb,
    simpleNecessity_sup_of_goodPossibility hq b hb⟩

end PortnerRubinstein2020
