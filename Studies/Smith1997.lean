module

public import Linglib.Semantics.Aspect.Defs
public import Linglib.Semantics.Aspect.Viewpoint

/-!
# Smith (1997): The Parameter of Aspect

Aspectual meaning as an independent choice of situation type (`VendlerClass`) and viewpoint
(`ViewpointType`). What a viewpoint makes visible is derived from the substrate's relation
between topic time and situation time, not stipulated per viewpoint.

## Main results

* `showsInitialPoint_iff`, `showsFinalPoint_iff`, `presentsClosed_iff`,
  `focusesPreliminaryStages_iff`: what each viewpoint makes visible (section 4.1).
* `perfective_closed`, `imperfective_open`, `neutral_intermediate`,
  `neutral_no_preliminary_stages`: the neutral viewpoint between the other two (section 4.2).
* `completion_iff_telic`: the perfective conveys completion exactly for telic types.
* `completionInvisible_iff`: the imperfective paradox (section 4.3.2).
* `Language.system`: the viewpoint systems of the four languages of Part II.

## Implementation notes

* A visibility property quantifies over every linear order, and is decided as the inclusion of
  the viewpoint's Allen cell in the property's cell (`Allen.forall_toSetRel_subset_iff`).
* The compositional rules of section 3.3 are not formalized.

## References

* [smith-1997]
* [klein-1994]
-/

@[expose] public section

open Aspect

namespace Smith1997

/-! ### Visibility, section 4.1 -/

/-- The viewpoint asserts the initial point of the situation. -/
def ShowsInitialPoint (v : ViewpointType) : Prop :=
  ∀ {T : Type} [LinearOrder T] {tt tsit : NonemptyInterval T},
    v.ttTSitRelation tt tsit → tsit.fst ∈ tt

/-- The viewpoint asserts the final point of the situation. -/
def ShowsFinalPoint (v : ViewpointType) : Prop :=
  ∀ {T : Type} [LinearOrder T] {tt tsit : NonemptyInterval T},
    v.ttTSitRelation tt tsit → tsit.snd ∈ tt

/-- The viewpoint presents the situation as closed: the topic time reaches its final point. -/
def PresentsClosed (v : ViewpointType) : Prop :=
  ∀ {T : Type} [LinearOrder T] {tt tsit : NonemptyInterval T},
    v.ttTSitRelation tt tsit → tsit.snd ≤ tt.snd

/-- The viewpoint focuses a topic time strictly inside the situation. -/
def FocusesPreliminaryStages (v : ViewpointType) : Prop :=
  ∀ {T : Type} [LinearOrder T] {tt tsit : NonemptyInterval T},
    v.ttTSitRelation tt tsit → tt < tsit

/-- A visibility property of a viewpoint, that every topic time and situation time it relates
stand in the cell `D`, is the inclusion of the viewpoint's realizable relations in `D`. -/
private theorem forall_imp_iff {D : Finset Allen.Relation}
    {P : ∀ {T : Type} [LinearOrder T], NonemptyInterval T → NonemptyInterval T → Prop}
    (hP : ∀ {T : Type} [LinearOrder T] (tt tsit : NonemptyInterval T),
      P tt tsit ↔ (tt, tsit) ∈ Allen.toSetRel D) (v : ViewpointType) :
    (∀ {T : Type} [LinearOrder T] {tt tsit : NonemptyInterval T},
      v.ttTSitRelation tt tsit → P tt tsit) ↔ v.cell ∩ Allen.atoms ⊆ D := by
  rw [← Allen.forall_toSetRel_subset_iff]
  exact ⟨fun h T _ ⟨tt, tsit⟩ hv ↦ (hP tt tsit).1 (h ((v.ttTSitRelation_iff tt tsit).2 hv)),
    fun h T _ tt tsit hv ↦ (hP tt tsit).2 (h T ((v.ttTSitRelation_iff tt tsit).1 hv))⟩

/-- The initial point: the perfective and the neutral viewpoint assert it. -/
theorem showsInitialPoint_iff (v : ViewpointType) :
    ShowsInitialPoint v ↔ v = .perfective ∨ v = .neutral := by
  refine (forall_imp_iff (D := Allen.inv Allen.startsWithin)
    (P := @fun _ _ tt tsit ↦ tsit.fst ∈ tt) (fun _ _ ↦ by simp) v).trans ?_
  cases v <;> decide +kernel

/-- The final point: only the perfective asserts it. -/
theorem showsFinalPoint_iff (v : ViewpointType) : ShowsFinalPoint v ↔ v = .perfective := by
  refine (forall_imp_iff
    (D := Allen.atoms.filter fun r ↦ r.fstSnd ≠ .gt ∧ r.sndSnd ≠ .lt)
    (P := @fun _ _ tt tsit ↦ tsit.snd ∈ tt) (fun _ _ ↦ ?_) v).trans ?_
  · rw [Allen.mem_toSetRel, Allen.relation_mem_filter]
    simp [Allen.relation, Allen.ofEndpoints, NonemptyInterval.mem_def, compare_le_iff_le,
      compare_ge_iff_ge]
  · cases v <;> decide +kernel

/-- Closure: the perfective and the perfect present the situation as closed. -/
theorem presentsClosed_iff (v : ViewpointType) :
    PresentsClosed v ↔ v = .perfective ∨ v = .perfect := by
  refine (forall_imp_iff (D := Allen.atoms.filter (·.sndSnd ≠ .lt))
    (P := @fun _ _ tt tsit ↦ tsit.snd ≤ tt.snd) (fun _ _ ↦ ?_) v).trans ?_
  · rw [Allen.mem_toSetRel, Allen.relation_mem_filter]
    simp [Allen.relation, Allen.ofEndpoints, compare_ge_iff_ge]
  · cases v <;> decide +kernel

/-- Preliminary stages: only the imperfective places the topic time strictly inside the
situation. -/
theorem focusesPreliminaryStages_iff (v : ViewpointType) :
    FocusesPreliminaryStages v ↔ v = .imperfective := by
  refine (forall_imp_iff (D := Allen.lt) (P := @fun _ _ tt tsit ↦ tt < tsit)
    (fun _ _ ↦ by simp) v).trans ?_
  cases v <;> decide +kernel

/-- The perfective makes both endpoints visible and presents the situation as closed,
section 4.2.1. -/
theorem perfective_closed :
    ShowsInitialPoint .perfective ∧ ShowsFinalPoint .perfective ∧ PresentsClosed .perfective :=
  ⟨(showsInitialPoint_iff _).mpr (Or.inl rfl), (showsFinalPoint_iff _).mpr rfl,
    (presentsClosed_iff _).mpr (Or.inl rfl)⟩

/-- The imperfective makes neither endpoint visible and is open, section 4.2.2. -/
theorem imperfective_open :
    ¬ ShowsInitialPoint .imperfective ∧ ¬ ShowsFinalPoint .imperfective ∧
      ¬ PresentsClosed .imperfective := by
  rw [showsInitialPoint_iff, showsFinalPoint_iff, presentsClosed_iff]
  decide

/-- The neutral viewpoint is intermediate, section 4.2.3: the initial point visible as under the
perfective, the final point unasserted as under the imperfective, and open. -/
theorem neutral_intermediate :
    ShowsInitialPoint .neutral ∧ ¬ ShowsFinalPoint .neutral ∧ ¬ PresentsClosed .neutral := by
  refine ⟨(showsInitialPoint_iff _).mpr (Or.inr rfl), ?_, ?_⟩
  · rw [showsFinalPoint_iff]; decide
  · rw [presentsClosed_iff]; decide

/-- Only the imperfective focuses preliminary stages, the discriminator between the neutral
viewpoint and the imperfective, section 4.2.3, (41). -/
theorem neutral_no_preliminary_stages :
    ¬ FocusesPreliminaryStages .neutral ∧ FocusesPreliminaryStages .imperfective := by
  refine ⟨?_, (focusesPreliminaryStages_iff _).mpr rfl⟩
  rw [focusesPreliminaryStages_iff]; decide

/-- The neutral viewpoint sides with the perfective on the initial point and with the
imperfective on the final point. -/
theorem neutral_between_perf_imperf :
    (ShowsInitialPoint .neutral ↔ ShowsInitialPoint .perfective) ∧
      (ShowsFinalPoint .neutral ↔ ShowsFinalPoint .imperfective) :=
  ⟨iff_of_true neutral_intermediate.1 perfective_closed.1,
    iff_of_false neutral_intermediate.2.1 imperfective_open.2.1⟩

/-! ### The independence of the components, section 4.3 -/

/-- An aspectual interpretation: a situation type and a viewpoint, chosen independently. -/
structure AspectualInterpretation where
  situationType : VendlerClass
  viewpoint : ViewpointType
  deriving DecidableEq

/-- The imperfective paradox, section 4.3.2: the situation type is visible whatever the
viewpoint, so a telic situation's natural endpoint is known though not asserted under a
viewpoint that does not show the final point. -/
def CompletionInvisible (ai : AspectualInterpretation) : Prop :=
  ai.situationType.telicity = .telic ∧ ¬ ShowsFinalPoint ai.viewpoint

/-- Completion is invisible exactly for telic situation types under a non-perfective
viewpoint. -/
theorem completionInvisible_iff (ai : AspectualInterpretation) :
    CompletionInvisible ai ↔ ai.situationType.telicity = .telic ∧ ai.viewpoint ≠ .perfective := by
  rw [CompletionInvisible, showsFinalPoint_iff]

/-- *We were walking to school*, (47): an accomplishment under the imperfective. -/
theorem walking_to_school : CompletionInvisible ⟨.accomplishment, .imperfective⟩ :=
  (completionInvisible_iff _).mpr ⟨rfl, by decide⟩

/-! ### The perfective's final point, section 4.2.1

The perfective presents its situation as closed, and the closed situation is completed or
terminated according to its situation type, (10) and (11). -/

/-- What the perfective conveys of the final point: completion for a telic situation type,
termination for an atelic one, and nothing under another viewpoint. -/
inductive PerfectiveEffect
  | completion | termination | noEffect
  deriving DecidableEq

/-- The perfective effect of an aspectual interpretation. -/
def perfectiveEffect (ai : AspectualInterpretation) : PerfectiveEffect :=
  match ai.viewpoint with
  | .perfective => if ai.situationType.telicity = .telic then .completion else .termination
  | _ => .noEffect

/-- Under the perfective, completion is conveyed exactly by the telic situation types. -/
theorem completion_iff_telic (c : VendlerClass) :
    perfectiveEffect ⟨c, .perfective⟩ = .completion ↔ c.telicity = .telic := by
  cases c <;> decide

/-- The imperfective conveys neither completion nor termination. -/
theorem imperfective_noEffect (c : VendlerClass) :
    perfectiveEffect ⟨c, .imperfective⟩ = .noEffect := rfl

/-! ### The aspectual systems of Part II, section 4.2 -/

/-- The relation between the perfective and statives, section 4.2.1: the perfective includes
the changes into and out of a state and closes it (French); it presents states open or closed
(English); or it does not apply to statives (Russian, Chinese, Navajo). -/
inductive PerfectiveStative
  | closed | openOrClosed | excluded
  deriving DecidableEq

/-- The interaction of viewpoint and situation type, section 4.2: an asymmetric system in
which one viewpoint is limited and the dominant one is available to every situation type, a
system in which every viewpoint is available to every situation type, or one in which
statives lie outside the viewpoint system. -/
inductive Interaction
  | asymmetric (dominant : ViewpointType) | symmetric | nonStativeOnly
  deriving DecidableEq

/-- A language's aspectual system: its viewpoints, their interaction with situation type, and
the treatment of statives by the perfective. -/
structure AspectualSystem where
  viewpoints : List ViewpointType
  interaction : Interaction
  perfectiveStative : PerfectiveStative
  deriving DecidableEq

/-- The four languages of Part II. -/
inductive Language
  | english | french | mandarin | navajo
  deriving DecidableEq

/-- The systems of section 4.2: English has the perfective and the progressive, the perfective
dominant, and presents states open or closed; French has the perfective, the imperfective and
the neutral viewpoint of its Futur, every viewpoint available to every situation type, and
its perfective closes states; Mandarin has perfectives, imperfectives and the neutral
viewpoint of a sentence without a viewpoint morpheme, and Navajo the perfective, the
imperfective and the neutral viewpoint of its Usitative and Iterative, both keeping statives
outside the viewpoint system. -/
def Language.system : Language → AspectualSystem
  | .english => ⟨[.perfective, .imperfective], .asymmetric .perfective, .openOrClosed⟩
  | .french => ⟨[.perfective, .imperfective, .neutral], .symmetric, .closed⟩
  | .mandarin => ⟨[.perfective, .imperfective, .neutral], .nonStativeOnly, .excluded⟩
  | .navajo => ⟨[.perfective, .imperfective, .neutral], .nonStativeOnly, .excluded⟩

/-- A language whose perfective does not apply to statives keeps them outside its viewpoint
system, and conversely. -/
theorem excluded_iff_nonStativeOnly (l : Language) :
    l.system.perfectiveStative = .excluded ↔ l.system.interaction = .nonStativeOnly := by
  cases l <;> decide

end Smith1997
