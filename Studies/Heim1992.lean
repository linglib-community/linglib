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
the Hintikka-style rule (27) with the comparative semantics (31) on similarity, the library's
`Desire.Conditional.Want`, with the amendment (40) blocking `want p ∧ want ¬p`.

## Main statements

* `admits_believes_iff`, `believes_ofTrivalent`: on atomic complements the belief rule is
  Karttunen's admittance in the holder's beliefs, and the update with a trivalent proposition.
* `believes_too_admits`, `doubt_too_admits_iff`: the *too*-discourse presupposes nothing, and its
  *doubt* variant is admitted only by contexts its first conjunct reduces to the absurd one.
* `admits_of_admits_knows`, `believes_admits_not_knows`: *know* passes on its complement's
  presupposition and *believe* need not, as Patrick's cello shows.
* `defined_recovered`, `not_want_recovered_compl`: on a four-world model shaped like Asher's
  Concorde case, the amendment blocks wanting both `p` and `¬p`.

## Implementation notes

* The three-world model of Section 4.1 for Stalnaker's get-well and have-been-sick contrast needs
  a non-trivial similarity ordering and is not formalized; the four-world model here uses the
  trivial ordering.

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

/-! ### Desire reports: the four-world model -/

/-- Worlds are classified by two binary dimensions, recovered (`r`) and sick (`s`), with
`w0 = r ∧ s`, `w1 = r ∧ ¬s`, `w2 = ¬r ∧ s` and `w3 = ¬r ∧ ¬s`. -/
inductive HealthWorld where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, Fintype

def recovered : Set HealthWorld | .w0 | .w1 => True | _ => False
def sick : Set HealthWorld | .w0 | .w2 => True | _ => False

instance : DecidablePred (· ∈ recovered) := fun w ↦ by
  cases w <;> first | exact isTrue trivial | exact isFalse id

/-- The naive Hintikka rule (27), rejected on [asher-1987]'s Concorde case (32), predicts `wants
recovered` false under the belief state `sick`. -/
theorem not_sick_subset_recovered : ¬ sick ⊆ recovered := fun h ↦ @h .w2 trivial

/-- Every world is equally similar to every other. -/
abbrev trivialSim (_ : HealthWorld) : Preorder HealthWorld := ⊤

/-- Recovered worlds are preferred to non-recovered ones, at every evaluation world. -/
def prefRecovered : HealthWorld → HealthWorld → HealthWorld → Prop :=
  fun _ x y ↦ x ∈ recovered ∧ y ∉ recovered

instance (w : HealthWorld) : DecidableRel (prefRecovered w) :=
  fun x y ↦ inferInstanceAs (Decidable (x ∈ recovered ∧ y ∉ recovered))

instance (w : HealthWorld) : Std.Antisymm (prefRecovered w) :=
  ⟨fun _ _ ⟨_, hny⟩ ⟨hy, _⟩ ↦ absurd hy hny⟩

abbrev heimFrame : Frame HealthWorld := ⟨trivialSim, prefRecovered⟩

/-- Under the (40) amendment, `want recovered` is defined when both recovered and non-recovered
worlds are believed possible. -/
theorem defined_recovered : Desire.IsContingent Set.univ recovered :=
  ⟨⟨.w0, trivial, trivial⟩, ⟨.w2, trivial, id⟩⟩

/-- Under (40) and an asymmetric preference, `want recovered` excludes `want ¬recovered`,
independently of the worry of (41)–(42) and the remedy (43). -/
theorem not_want_recovered_compl (h : Want heimFrame Set.univ .w0 recovered) :
    ¬ Want heimFrame Set.univ .w0 recoveredᶜ :=
  h.not_compl defined_recovered

end Heim1992
