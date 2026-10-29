module

public import Linglib.Semantics.Attitudes.Preference.Conditional
public import Linglib.Semantics.Dynamic.Partial
public import Linglib.Logic.Modal.Defs
public import Mathlib.Data.Set.Lattice.Bounded

/-!
# Heim (1992): Presupposition Projection and the Semantics of Attitude Verbs

Heim gives the attitude predicates context change potentials and derives their projection
behaviour. The belief rule (18) is `believes`, a `CCP.Partial` combinator over the doxastic
accessibility of (11)–(12): the report is defined iff the complement is defined on each doxastic
state, so a complement presupposing `p` yields a report presupposing that its holder believes `p`,
Karttunen's generalization. The factive rule of footnote 47 makes *know* admit only contexts that
admit its complement's presupposition, which a belief report need not. The desire half replaces
the Hintikka-style rule (27) with a comparison over similarity, `Desire.Conditional.Want`. In
its truth-conditional form (31) the similar worlds are drawn from all worlds, and it [blocks
Stalnaker's inference](##HealthWorld.want_getWell_not_want_beenSick) from *I want to get well*
to *I want to have been sick*. In its context change form (39) they are drawn from the belief
worlds, which [makes a believed complement and its negation both
wanted](##want_and_want_compl_of_believes); the amendment (40) makes such ascriptions undefined,
and under it [wanting `p` excludes wanting `¬p`](##HealthWorld.want_getWell_not_want_compl).

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

/-- On atomic complements, Karttunen's rule (3) makes `c` admit `a believes φ` iff the doxastic
image of `c` admits `φ`. -/
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
  · simp [believes, mem_ofTrivalent_self, ModalLogic.Box]
    exact fun hw h1 ↦ ⟨hw, fun v hv ↦ by simp [h1 v hv]⟩

/-- (20) presupposes nothing, given the presupposition (22) of the *too*-clause. -/
theorem believes_too_admits (m s : Set W) [DecidablePred (· ∈ m)] [DecidablePred (· ∈ s)] :
    (seq (believes Dox a (ofTrivalent fun w ↦ SignType.ofProp (w ∈ m)))
      (believes Dox a (ofTrivalent (m.indicator fun w ↦ SignType.ofProp (w ∈ s))))).Admits c :=
  ⟨fun _ _ _ _ ↦ SignType.ofProp_ne_zero, fun _ hw v hv ↦ by
    simpa [Set.indicator_apply_ne_zero] using (mem_ofTrivalent_self _ _).1 hw.2 v hv⟩

/-- Only contexts in which John already believes Mary is here admit (25), *John doubts that Mary_i
is here and believes that Susan_F is here too_i*. -/
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

/-- A context admitting a *know* report admits its complement's presupposition. -/
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

/-- On the context change rule (39), the similar worlds drawn from the belief worlds, a subject
who believes `p` or believes `¬p` trivially wants both `p` and `¬p`. -/
theorem want_and_want_compl_of_believes {W : Type*} {F : Frame W} {Dox p : Set W} {w : W}
    (h : Dox ⊆ p ∨ Dox ⊆ pᶜ) : Want F Dox Dox w p ∧ Want F Dox Dox w pᶜ := by
  rcases h with h | h
  · exact ⟨fun _ _ _ _ y hy ↦ (hy.1.2 (h hy.1.1)).elim, fun _ _ x hx ↦ (hx.1.2 (h hx.1.1)).elim⟩
  · exact ⟨fun _ _ x hx ↦ (h hx.1.1 hx.1.2).elim, fun _ _ _ _ y hy ↦ (hy.1.2 (h hy.1.1)).elim⟩

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
def dox : Set HealthWorld := {w | w ≠ w1}

instance : DecidablePred (· ∈ getWell) := fun w ↦ inferInstanceAs (Decidable (w = w2))

instance : DecidablePred (· ∈ beenSick) := fun w ↦ inferInstanceAs (Decidable (w ≠ w1))

instance : DecidablePred (· ∈ dox) := fun w ↦ inferInstanceAs (Decidable (w ≠ w1))

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
  ⟨fun _ _ h h' ↦ absurd (h.trans h') (lt_irrefl _)⟩

-- p. 194
theorem getWell_subset_beenSick : getWell ⊆ beenSick := by
  rintro _ rfl
  decide

/-- On the rule (31), *I want to get well* is true and *I want to have been sick* false, though
getting well entails having been sick: from each belief world the closest world where I have not
been sick is `w1`, which is better. -/
theorem want_getWell_not_want_beenSick (w : HealthWorld) :
    Want frame .univ dox w getWell ∧ ¬ Want frame .univ dox w beenSick := by
  cases w <;> decide

-- p. 198
theorem want_dox_beenSick (w : HealthWorld) :
    Want frame dox dox w beenSick ∧ Want frame dox dox w beenSickᶜ :=
  want_and_want_compl_of_believes (.inl fun _ ↦ id)

/-- Under the amendment (40) *I want to have been sick* is undefined, since I believe I have
been sick. -/
theorem not_isContingent_dox_beenSick : ¬ Desire.IsContingent dox beenSick :=
  fun ⟨_, _, hd, hs⟩ ↦ hs hd

/-- *I want to get well* meets the amendment (40), and the context change rule makes it true and
so *I want not to get well* false. -/
theorem want_getWell_not_want_compl (w : HealthWorld) :
    Want frame dox dox w getWell ∧ ¬ Want frame dox dox w getWellᶜ := by
  have h : Want frame dox dox w getWell := by cases w <;> decide
  exact ⟨h, h.not_compl ⟨w2, by decide⟩ ⟨⟨w2, by decide, rfl⟩, w3, by decide, by decide⟩⟩

end HealthWorld

end Heim1992
