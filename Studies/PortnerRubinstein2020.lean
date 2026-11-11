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

Spanish *querer* 'want' and *esperar* 'hope' take the subjunctive, French *vouloir* the
subjunctive and *espérer* the indicative. Portner and Rubinstein place the variation in
composition. A believing situation has one modal background as content and a desiring situation
a pair of an ordering source and a modal base; the indicative is simple necessity over one
background and the subjunctive local necessity over a pair, and a mood whose force does not fit
the content is uninterpretable. French moods first unify a pair consistent at every situation,
which [changes the mood a content takes and never its meaning](##exists_french_eq_some_iff). The
desires behind *hope* are consistent with the beliefs and those behind *want* need not be, so
*hope* takes [the subjunctive in Spanish](##spanish_takes) and [the indicative in
French](##french_takes); one can [want each of two incompatible
outcomes](##want_alice_and_want_sue) but [not hope for both](##not_hope_both).

## Implementation notes

* Backgrounds are relative to worlds rather than situations, and `Backgrounds` holds those of
  one attitude holder; that the desires of *want* need not be consistent with the beliefs⁺ is
  the assumption that at some world they are not.
* Local necessity is the definition in the text. Appendix B states it through best sets, which
  under the Limit Assumption [says the same](##goodPossibility_iff_exists_mem_bestSets) once the
  best sets are read as classes of best worlds.
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

/-- The ordered information state a content induces at a world. -/
def Content.state : Content W → W → DynamicSemantics.OrderedInformationState W
  | .single f => stateAt f ⊥
  | .pair g f => stateAt f g

/-- The Spanish moods relate a clause to a world through the force of the mood applied to the
content. A mood and a content that target different components do not combine. -/
def spanish (m : Grammatical) (c : Content W) : Option ((W → Prop) → W → Prop) :=
  if m.target = c.target then some fun p w ↦ m.interp (c.state w) p else none

@[simp] theorem spanish_indicative_single (f : Background W) :
    spanish .indicative (.single f) = some fun p w ↦ ∀ᶠ v in simpleNecessity f w, p v := rfl

@[simp] theorem spanish_subjunctive_pair (g f : Background W) :
    spanish .subjunctive (.pair g f) = some fun p w ↦ goodPossibility f g w {v | p v} := rfl

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

-- (49)
theorem goodPossibility_eq_simpleNecessity_sup {f g : Background W}
    (h : (f ⊔ g).IsConsistent) :
    (fun p w ↦ goodPossibility f g w {v | p v}) =
      fun (p : W → Prop) w ↦ ∀ᶠ v in simpleNecessity (f ⊔ g) w, p v :=
  funext₂ fun _ w ↦ propext (goodPossibility_iff_mem_simpleNecessity_sup (h w))

/-- Simplification changes the mood a content is interpreted in and never its meaning: French
moods give a content exactly the meanings Spanish moods give it (p. 366). -/
theorem exists_french_eq_some_iff (c : Content W) (x : (W → Prop) → W → Prop) :
    (∃ m, french m c = some x) ↔ ∃ m, spanish m c = some x := by
  rcases c with f | ⟨g, f⟩
  · exact .rfl
  by_cases h : (f ⊔ g).IsConsistent
  · simp only [french, show spl (.pair g f) = .single (f ⊔ g) from ite_eq_left h]
    refine ⟨fun ⟨m, hm⟩ ↦ ⟨.subjunctive, ?_⟩, fun ⟨m, hm⟩ ↦ ⟨.indicative, ?_⟩⟩ <;> cases m <;>
      simp_all [goodPossibility_eq_simpleNecessity_sup h]
  · simp only [french, show spl (.pair g f) = .pair g f from ite_eq_right h]

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

-- p. 366
theorem french_hope_eq_spanish_hope :
    french .indicative B.hope = spanish .subjunctive B.hope := by
  rw [french, B.spl_hope, spanish_indicative_single, Backgrounds.hope, spanish_subjunctive_pair,
    goodPossibility_eq_simpleNecessity_sup B.consistent]

/-- No one hopes for each of two outcomes their beliefs rule out together. -/
theorem not_hope_both {p q : Set W} {w : W}
    (hpq : ∀ v ∈ B.dox.accessibleWorlds w, ¬ (v ∈ p ∧ v ∈ q)) :
    ¬ (goodPossibility B.dox B.bulc w p ∧ goodPossibility B.dox B.bulc w q) := by
  rintro ⟨hp, hq⟩
  obtain ⟨b, hb⟩ := B.consistent w
  exact hpq b ((Background.accessibleWorlds_sup _ _ w).subset hb).1
    ⟨mem_simpleNecessity_sup_of_goodPossibility hp hb,
      mem_simpleNecessity_sup_of_goodPossibility hq hb⟩

/-! ### The fragments -/

/-- The coding of a finite clause in a grammatical mood. -/
def coding : Grammatical → Clause.ComplementType
  | .indicative => .indicative
  | .subjunctive => .subjunctive

-- The Spanish entries record the moods the analysis predicts.
theorem spanish_fragment :
    (coding m ∈ Spanish.Verbs.creer.codings ↔ (spanish m B.believe).isSome) ∧
      (coding m ∈ Spanish.Verbs.querer.codings ↔ (spanish m B.want).isSome) ∧
      (coding m ∈ Spanish.Verbs.esperar.codings ↔ (spanish m B.hope).isSome) := by
  rw [(spanish_takes B m).1, (spanish_takes B m).2.1, (spanish_takes B m).2.2]
  cases m <;> decide

-- The French entries record the moods the analysis predicts.
theorem french_fragment :
    (coding m ∈ French.Verbs.croire.codings ↔ (french m B.believe).isSome) ∧
      (coding m ∈ French.Verbs.vouloir.codings ↔ (french m B.want).isSome) ∧
      (coding m ∈ French.Verbs.esperer.codings ↔ (french m B.hope).isSome) := by
  rw [(french_takes B m).1, (french_takes B m).2.1, (french_takes B m).2.2]
  cases m <;> decide

/-! ### Marrying Alice and marrying Sue

Under desires to marry Alice and to marry Sue, the worlds where the speaker marries one of them
are incomparable, so where the beliefs⁺ rule out marrying both each marriage holds throughout a
branch of the ordering and neither holds at every best world. -/

/-- A world settles whether the speaker marries Alice and whether the speaker marries Sue. -/
abbrev World := Bool × Bool

/-- The speaker marries Alice. -/
def marriesAlice : Set World := {w | w.1 = true}

/-- The speaker marries Sue. -/
def marriesSue : Set World := {w | w.2 = true}

/-- The beliefs⁺ rule out marrying both. -/
def doxPlus : Background World := fun _ ↦ {(marriesAlice ∩ marriesSue)ᶜ}

/-- The beliefs are that the speaker marries exactly one of them. -/
def dox : Background World :=
  fun _ ↦ {marriesAlice ∪ marriesSue, (marriesAlice ∩ marriesSue)ᶜ}

/-- The desires are to marry Alice and to marry Sue. -/
def bul : Background World := fun _ ↦ {marriesAlice, marriesSue}

theorem bestWorlds_doxPlus_bul (w : World) :
    bestWorlds doxPlus bul w = {(true, false), (false, true)} := by
  ext ⟨a, b⟩
  cases a <;> cases b <;>
    simp [mem_bestWorlds, doxPlus, bul, Preorder.ofCriteria_le_iff, marriesAlice, marriesSue]

/-- An attitude holder who desires to marry Alice and to marry Sue, and whose one consistent
desire is to marry Alice. -/
def marriage : Backgrounds World where
  dox := dox
  doxPlus := doxPlus
  bul := bul
  bulc := fun _ ↦ {marriesAlice}
  consistent _ := ⟨(true, false), by simp [dox, marriesAlice, marriesSue]⟩
  inconsistent h := by
    obtain ⟨⟨a, b⟩, hv⟩ := h (true, true)
    cases a <;> cases b <;> simp [doxPlus, bul, marriesAlice, marriesSue] at hv

/-- The speaker wants to marry Alice and wants to marry Sue. -/
theorem want_alice_and_want_sue (w : World) :
    ∃ φ, spanish .subjunctive marriage.want = some φ ∧ φ marriesAlice w ∧ φ marriesSue w :=
  ⟨fun p w ↦ goodPossibility doxPlus bul w {v | p v}, rfl,
    ⟨(true, false), by simp [doxPlus, marriesAlice, marriesSue],
      fun _ _ hv ↦ hv marriesAlice (by simp [bul]) rfl⟩,
    ⟨(false, true), by simp [doxPlus, marriesAlice, marriesSue],
      fun _ _ hv ↦ hv marriesSue (by simp [bul]) rfl⟩⟩

-- (14), (16): on von Fintel's best-worlds *want* it is false that the speaker wants to marry
-- Alice, since marrying Sue is a best outcome
theorem bestWorlds_want_alice_eq_false (w : World) :
    Desire.BestWorlds.want doxPlus.accessibleWorlds bul marriesAlice w = .false := by
  have hS : ((false, true) : World) ∈ bestWorlds doxPlus bul w := by
    simp [bestWorlds_doxPlus_bul]
  exact Desire.BestWorlds.want_eq_false_iff.2
    ⟨⟨⟨(true, false), by simp [doxPlus, marriesAlice, marriesSue], rfl⟩, (false, true), hS.1,
      nofun⟩, fun h ↦ nomatch (h hS : (false, true) ∈ marriesAlice)⟩

-- fn. 22: the desires are consistent together but not with the beliefs, and local necessity
-- over them makes each marriage hoped for
theorem hope_alice_and_hope_sue (w : World) :
    (bul.accessibleWorlds w).Nonempty ∧
      goodPossibility dox bul w marriesAlice ∧ goodPossibility dox bul w marriesSue :=
  ⟨⟨(true, true), by simp [bul, marriesAlice, marriesSue]⟩,
    ⟨(true, false), by simp [dox, marriesAlice, marriesSue],
      fun _ _ hv ↦ hv marriesAlice (by simp [bul]) rfl⟩,
    ⟨(false, true), by simp [dox, marriesAlice, marriesSue],
      fun _ _ hv ↦ hv marriesSue (by simp [bul]) rfl⟩⟩

/-! ### The best sets of Appendix B -/

/-- The best sets are the classes of best worlds satisfying the same premises of the ordering
source. -/
def bestSets (f g : Background W) (w : W) : Set (Set W) :=
  {X | ∃ b ∈ bestWorlds f g w, X = {v ∈ bestWorlds f g w |
    Preorder.satisfied (· ∈ ·) (g w) v = Preorder.satisfied (· ∈ ·) (g w) b}}

-- Appendix B: under the Limit Assumption local necessity is truth throughout a best set.
theorem goodPossibility_iff_exists_mem_bestSets {f g : Background W} {p : Set W} {w : W}
    (hlim : LimitAssumption f g w) :
    goodPossibility f g w p ↔ ∃ X ∈ bestSets f g w, ∀ v ∈ X, v ∈ p := by
  let o := premisePreorder (g w)
  refine ⟨fun ⟨u, hu, hp⟩ ↦ ?_, fun ⟨_, ⟨b, hb, hX⟩, hp⟩ ↦ ⟨b, hb.1, fun v hv hvb ↦ ?_⟩⟩
  · obtain ⟨b, hb, hbu⟩ := hlim u hu
    exact ⟨_, ⟨b, hb, rfl⟩, fun v ⟨hv, hvb⟩ ↦ hp v hv.1
      (o.le_trans _ _ _ (Preorder.antisymmRel_ofCriteria_iff.2 hvb).1 hbu)⟩
  · exact hp v (hX ▸ ⟨⟨hv, fun ⦃z⦄ hz hzv ↦ o.le_trans _ _ _ hvb
      (hb.2 hz (o.le_trans _ _ _ hzv hvb))⟩,
      Preorder.antisymmRel_ofCriteria_iff.1 ⟨hvb, hb.2 hv hvb⟩⟩)

-- Appendix B as printed: no set holds exactly the pairs of best worlds with the same premises.
theorem not_exists_printed_bestSet (w : World) : ¬ ∃ X : Set World, ∀ u v,
    u ∈ X ∧ v ∈ X ↔ Preorder.satisfied (· ∈ ·) (bul w) u = Preorder.satisfied (· ∈ ·) (bul w) v ∧
      u ∈ bestWorlds doxPlus bul w ∧ v ∈ bestWorlds doxPlus bul w := by
  rintro ⟨X, hX⟩
  have hA : ((true, false) : World) ∈ bestWorlds doxPlus bul w := by simp [bestWorlds_doxPlus_bul]
  have hS : ((false, true) : World) ∈ bestWorlds doxPlus bul w := by simp [bestWorlds_doxPlus_bul]
  have heq := ((hX _ _).1 ⟨((hX _ _).2 ⟨rfl, hA, hA⟩).1, ((hX _ _).2 ⟨rfl, hS, hS⟩).1⟩).1
  have h : marriesAlice ∈ Preorder.satisfied (· ∈ ·) (bul w) ((false, true) : World) :=
    heq ▸ ⟨by simp [bul], rfl⟩
  exact nomatch (h.2 : (false, true) ∈ marriesAlice)

end PortnerRubinstein2020
