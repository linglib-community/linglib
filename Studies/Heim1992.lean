module

public import Linglib.Semantics.Attitudes.Preference.Conditional
public import Linglib.Semantics.Dynamic.Partial
public import Linglib.Logic.Modal.Defs
public import Mathlib.Data.Set.Lattice.Bounded

/-!
# Heim (1992): Presupposition Projection and the Semantics of Attitude Verbs

Heim gives the attitude predicates context change potentials. A belief report [presupposes that its
holder believes the complement's presupposition](##believes_ofTrivalent), and a *know* report,
unlike it, [needs a context that entails it](##believes_admits_not_knows). *Want* compares the most
similar worlds where the complement holds and where it fails. Drawn from all worlds, they [block the
inference](##HealthWorld.want_getWell_not_want_beenSick) from *I want to get well* to *I want to
have been sick*; drawn from the belief worlds, they [make a believed complement and its negation
both wanted](##HealthWorld.want_dox_beenSick), until her amendment [makes wanting `p` exclude
wanting `¬p`](##HealthWorld.want_getWell_not_want_compl).

## Implementation notes

* Heim fixes the closest worlds of her model from each belief world; here similarity is a
  distance on which the two sick worlds are closer to each other than either is to the healthy
  one, which gives those closest worlds.

## TODO

Asher's Concorde case of the same inference, and the accessibility (43) for *intend* that answers
the worry of (41), are not formalized.

## References

* [heim-1992]
* [karttunen-1974-presupposition]
* [asher-1987]
* [stalnaker-1984]
* [stalnaker-1968]
* [lewis-1973b]
-/

@[expose] public section

namespace Heim1992

open DynamicSemantics PartialUpdate CCP.Partial Presupposition Desire.Conditional

/-! ### Belief reports -/

section Belief

variable {W E : Type*} (Dox : E → W → Set W) (a : E) (φ : CCP.Partial W) (p : W → SignType)
  (c : Set W)

/-- By rule (18), `c + a believes φ` is defined iff `Dox_a(w) + φ` is defined for every `w ∈ c`,
and then equals `{w ∈ c | Dox_a(w) + φ = Dox_a(w)}`. -/
def believes : CCP.Partial W :=
  fun c ↦ ⟨∀ w ∈ c, φ.Admits (Dox a w), fun _ ↦ {w ∈ c | Dox a w ∈ φ (Dox a w)}⟩

theorem admits_believes_ofTrivalent :
    (believes Dox a (ofTrivalent p)).Admits c ↔
      ∀ w ∈ c, ModalLogic.Box (.ofSuccessors (Dox a)) (· ∈ Function.support p) w :=
  Iff.rfl

-- (3)
theorem admits_believes_iff :
    (believes Dox a (ofTrivalent p)).Admits c ↔
      (SetRel.ofSuccessors (Dox a)).image c ⊆ Function.support p :=
  (SetRel.image_subset_iff (R := .ofSuccessors (Dox a))).symm

open Classical in
/-- On atomic complements (18) is static, presupposing that `a` believes `φ`'s presupposition and
asserting that `a` believes `φ` (24). -/
theorem believes_ofTrivalent :
    believes Dox a (ofTrivalent p) = ofTrivalent
      ({w | ModalLogic.Box (.ofSuccessors (Dox a)) (· ∈ Function.support p) w}.indicator
        fun w ↦ SignType.ofProp (ModalLogic.Box (.ofSuccessors (Dox a)) (p · = 1) w)) := by
  funext c
  refine Part.ext' ?_ fun h _ ↦ Set.ext fun w ↦ ?_
  · simp [believes, ofTrivalent, Set.subset_def, ModalLogic.Box, admits_ofTrivalent]
  · simp only [believes, mem_ofTrivalent_self, Set.mem_ofPred_eq, ModalLogic.Box,
      SetRel.mem_ofSuccessors, Function.mem_support, ne_eq, ofTrivalent_get,
      Trivalent.indicator_apply_eq_one_iff, SignType.ofProp_eq_one_iff, Set.sep_and,
      Set.mem_inter_iff, iff_and_self, and_imp]
    exact fun hw h1 ↦ ⟨hw, fun v hv ↦ by simp [h1 v hv]⟩

-- (20), (22)
theorem believes_too_admits (m s : Set W) [DecidablePred (· ∈ m)] [DecidablePred (· ∈ s)] :
    (seq (believes Dox a (ofTrivalent fun w ↦ SignType.ofProp (w ∈ m)))
      (believes Dox a (ofTrivalent (m.indicator fun w ↦ SignType.ofProp (w ∈ s))))).Admits c :=
  ⟨fun _ _ _ _ ↦ SignType.ofProp_ne_zero, fun _ hw v hv ↦ by
    simpa [Set.indicator_apply_ne_zero] using (mem_ofTrivalent_self _ _).1 hw.2 v hv⟩

-- (25)
theorem doubt_too_admits_iff (m s : Set W) [DecidablePred (· ∈ m)] [DecidablePred (· ∈ s)] :
    (seq (neg (believes Dox a (ofTrivalent fun w ↦ SignType.ofProp (w ∈ m))))
      (believes Dox a (ofTrivalent (m.indicator fun w ↦ SignType.ofProp (w ∈ s))))).Admits c ↔
      ∀ w ∈ c, Dox a w ⊆ m := by
  refine ⟨fun ⟨_, h⟩ w hw ↦ ?_,
    fun h ↦ ⟨fun _ _ _ _ ↦ SignType.ofProp_ne_zero, fun w hw ↦ (hw.2 ⟨hw.1, ?_⟩).elim⟩⟩
  · by_contra hm
    refine hm ((h w ⟨hw, fun hS ↦ hm fun v hv ↦ ?_⟩).trans Set.support_indicator_subset)
    simpa using (mem_ofTrivalent_self _ _).1 hS.2 v hv
  · exact (mem_ofTrivalent_self _ _).2 fun v hv ↦ by simpa using h w hw.1 hv

/-- By the factive rule of footnote 47, `c + a knows φ` is undefined unless `c + φ = c`, and is
otherwise `c + a believes φ`. -/
def knows : CCP.Partial W := fun c ↦ Part.assert (c ∈ φ c) fun _ ↦ believes Dox a φ c

theorem admits_knows :
    (knows Dox a φ).Admits c ↔ c ∈ φ c ∧ (believes Dox a φ).Admits c :=
  exists_prop

theorem admits_of_admits_knows (h : (knows Dox a (ofTrivalent p)).Admits c) :
    c ⊆ Function.support p :=
  supports.admits h.fst

end Belief

/-! ### The know/believe contrast on Patrick's cello -/

/-- Whether Patrick owns a cello. -/
inductive CelloWorld where
  | owns
  | lacks
  deriving DecidableEq

/-- In Patrick's misconception (2), whatever the facts, he believes he owns a cello. -/
def celloDox (_ : Unit) (_ : CelloWorld) : Set CelloWorld := {.owns}

/-- `Patrick sells his cello` (1) presupposes that he owns one. -/
noncomputable def sellsCello : CelloWorld → SignType := ({.owns} : Set CelloWorld).indicator 1

/-- Where Patrick lacks a cello but believes he owns one, `Patrick believes he is selling his
cello` is admitted and `Patrick knows he is selling his cello` is not, since `celloDox` is not
veridical at `lacks`. -/
theorem believes_admits_not_knows :
    (believes celloDox () (ofTrivalent sellsCello)).Admits {.lacks} ∧
      ¬ (knows celloDox () (ofTrivalent sellsCello)).Admits {.lacks} :=
  ⟨fun _ _ _ h ↦ by simp_all [celloDox, sellsCello],
   fun h ↦ by simpa [sellsCello] using admits_of_admits_knows _ _ _ _ h rfl⟩

/-! ### Desire reports

Stalnaker's counterexample to the inference that the Hintikka-style rule (27) validates: I am
sick and want to get well, getting well entails having been sick, and I do not want to have been
sick. Heim's model has three worlds: in `w1` I am healthy all the time, in `w2` I am sick and
then get well, and in `w3` I am sick and stay sick; `w1` is better than `w2`, which is better than
`w3`, and I believe that I have been sick. -/

/-- The three kinds of worlds of Stalnaker's example. -/
inductive HealthWorld where
  /-- I am healthy all the time. -/
  | w1
  /-- I am sick first and then get well. -/
  | w2
  /-- I am sick and stay sick. -/
  | w3
  deriving DecidableEq, Fintype

namespace HealthWorld

/-- The worlds where I get well. -/
def getWell : Set HealthWorld := {w | w = w2}

/-- The worlds where I have been sick. -/
def beenSick : Set HealthWorld := {w | w ≠ w1}

/-- My belief worlds: I believe that I have been sick. -/
def dox : Set HealthWorld := beenSick

instance : DecidablePred (· ∈ getWell) := fun w ↦ inferInstanceAs (Decidable (w = w2))

instance : DecidablePred (· ∈ beenSick) := fun w ↦ inferInstanceAs (Decidable (w ≠ w1))

instance : DecidablePred (· ∈ dox) := inferInstanceAs (DecidablePred (· ∈ beenSick))

/-- How desirable a world is to me, `w1` best and `w3` worst. -/
def rank : HealthWorld → ℕ
  | w1 => 0
  | w2 => 1
  | w3 => 2

/-- The distance between worlds, on which the two sick worlds are closer to each other than either
is to the healthy one. -/
def distance (a b : HealthWorld) : ℕ := if a = b then 0 else if a = w1 ∨ b = w1 then 2 else 1

/-- Similarity to a world is closeness in `distance`, and a world is more desirable than another
when it ranks higher, at every evaluation world. -/
abbrev frame : Frame HealthWorld :=
  ⟨fun w' ↦ Preorder.lift (distance w'), fun _ x y ↦ rank x < rank y⟩

instance (w : HealthWorld) : DecidableRel (frame.sim w).le :=
  fun x y ↦ inferInstanceAs (Decidable (distance w x ≤ distance w y))

instance (w : HealthWorld) : DecidableRel (frame.pref w) :=
  fun x y ↦ inferInstanceAs (Decidable (rank x < rank y))

instance (w : HealthWorld) : Std.Antisymm (frame.pref w) :=
  ⟨fun _ _ h h' ↦ (lt_asymm h h').elim⟩

/-- On the rule (31), *I want to get well* is true and *I want to have been sick* false, though
getting well entails having been sick: from each belief world the closest world where I have not
been sick is `w1`, which is better. -/
theorem want_getWell_not_want_beenSick (w : HealthWorld) :
    getWell ⊆ beenSick ∧ Want frame .univ dox w getWell ∧ ¬ Want frame .univ dox w beenSick := by
  refine ⟨?_, by cases w <;> decide⟩
  rintro _ rfl
  decide

-- the similarity does the work: with every world equally similar, *I want to get well* is false
theorem not_want_getWell_top (w : HealthWorld) :
    ¬ Want ⟨fun _ ↦ ⊤, frame.pref⟩ .univ dox w getWell := fun h ↦
  (by decide : ¬ rank w2 < rank w1)
    (h w2 (by decide) w2 (by simp [Frame.closest, getWell]) w1 (by simp [Frame.closest, getWell]))

-- (40)
theorem not_isContingent_dox_beenSick : ¬ Desire.IsContingent dox beenSick :=
  fun ⟨_, _, hd, hs⟩ ↦ hs hd

/-- On the context change rule (39), the similar worlds drawn from the belief worlds, I trivially
want to have been sick, which I believe, and also not to have been sick. -/
theorem want_dox_beenSick (w : HealthWorld) :
    Want frame dox dox w beenSick ∧ Want frame dox dox w beenSickᶜ :=
  ⟨.of_not_isContingent not_isContingent_dox_beenSick,
    .of_not_isContingent (Desire.isContingent_compl.not.2 not_isContingent_dox_beenSick)⟩

/-- *I want to get well* meets the amendment (40), and the context change rule makes it true and
so *I want not to get well* false. -/
theorem want_getWell_not_want_compl (w : HealthWorld) :
    Want frame dox dox w getWell ∧ ¬ Want frame dox dox w getWellᶜ := by
  have hc : Desire.IsContingent dox getWell := ⟨⟨w2, by decide, rfl⟩, w3, by decide, by decide⟩
  have h : Want frame dox dox w getWell := by cases w <;> decide
  exact ⟨h, h.not_compl hc.nonempty hc⟩

end HealthWorld

end Heim1992
