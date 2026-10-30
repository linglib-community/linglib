module

public import Linglib.Semantics.ArgumentStructure.LevinClass.Basic
public import Linglib.Data.Examples.LevinRappaportHovav1995
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Fragments.Romance.Italian.Verbs
public import Linglib.Fragments.Dutch.Verbs
public import Linglib.Semantics.ArgumentStructure.Unaccusativity
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.DeriveFintype

/-!
# Levin and Rappaport Hovav (1995): Unaccusativity

The linking rules of chapter 4 read three components of meaning off an argument: whether it is
the immediate cause of the eventuality, whether it undergoes a directed change, and whether its
existence is asserted or denied. The Immediate Cause Linking Rule (1) makes the immediate cause
the external argument, the Directed Change (24) and Existence (47) Linking Rules make the other
two direct internal arguments, and the Default Linking Rule (49) does the same for an argument
no other rule reaches. Where several rules apply, the one of highest precedence decides, and a
monadic verb is unaccusative when its sole argument is a direct internal argument.

## Main definitions

* `Ranking.position`: the position the rules assign an argument under a precedence order.
* `ranking`: the order of §4.2.4, the Directed Change and Existence rules over the Immediate
  Cause rule.
* `Unaccusative`: the verb's sole argument is a direct internal argument.
* `components`: the component sets of the classes in Appendix A, one per construal.

## Implementation notes

* A ranking lists the rules keyed to a component, highest precedence first, and the Default rule
  follows them all. The book leaves the order of the Directed Change and Existence rules open
  and raises the possibility that languages rank the rules differently (§4.2.4); `position_swap`
  shows that the open order is immaterial.
* A class the book discusses under several construals, such as the verbs of spatial
  configuration in their simple, maintain and assume position senses, lists one component set
  per construal. A data row records its verb's agentivity where the construals differ by it.
* The rules link every argument of a verb, the cause and the patient of transitive *break*
  alike (§4.1.2); the study classifies monadic verbs only.

## References

* [levin-hovav-1995]
* [levin-1993]
-/

@[expose] public section

namespace LevinRappaportHovav1995

open ArgumentStructure

/-- The components of a verb's meaning that the linking rules read off an argument (§4.2.4). An
argument may be the immediate cause of the eventuality, which makes the verb internally caused
(§3.2.1), undergo a directed change (§4.1.2), and have its existence asserted or denied
(§4.1.3). -/
inductive Component
  | immediateCause | directedChange | existence
  deriving DecidableEq, Fintype, Repr

/-- The argument-structure positions the rules assign. -/
inductive Position
  | external | directInternal
  deriving DecidableEq, Repr

/-- The position assigned by the linking rule keyed to the component. The Immediate Cause Linking
Rule (1) makes the immediate cause the external argument, and the Directed Change Linking Rule
(24) and the Existence Linking Rule (47) make their arguments direct internal arguments. -/
def Component.position : Component → Position
  | .immediateCause => .external
  | .directedChange | .existence => .directInternal

/-- A precedence order on the linking rules keyed to a component, highest first. -/
abbrev Ranking := List Component

namespace Ranking

variable (r : Ranking) (s : Finset Component)

/-- The applicable rule of highest precedence for an argument with the components `s`, `none`
when only the Default Linking Rule (49) applies. -/
def rule : Option Component := r.find? (· ∈ s)

/-- The position of an argument with the components `s`, the direct internal position by the
Default Linking Rule (49) when no other rule applies. -/
def position : Position := (r.rule s).elim .directInternal Component.position

theorem position_eq_external_iff :
    r.position s = .external ↔ r.rule s = some .immediateCause := by
  unfold position
  rcases r.rule s with _ | ⟨_ | _ | _⟩ <;> simp [Component.position]

theorem position_eq_directInternal_iff :
    r.position s = .directInternal ↔ r.rule s ≠ some .immediateCause := by
  rw [ne_eq, ← position_eq_external_iff]
  cases r.position s <;> simp

variable {r s}

theorem rule_eq_some_of_subset {t : Finset Component} {c : Component} (hst : s ⊆ t)
    (h : r.rule t = some c) (hc : c ∈ s) : r.rule s = some c := by
  obtain ⟨-, as, bs, rfl, has⟩ := List.find?_eq_some_iff_append.mp h
  refine List.find?_eq_some_iff_append.mpr ⟨by simpa using hc, as, bs, rfl, fun a ha ↦ ?_⟩
  simpa using fun h ↦ (by simpa using has a ha : a ∉ t) (hst h)

end Ranking

/-- The precedence of §4.2.4, with the Directed Change and Existence Linking Rules over the
Immediate Cause Linking Rule. The book infers it from verbs that fall under two rules
(§4.2.1–§4.2.4). -/
def ranking : Ranking := [.directedChange, .existence, .immediateCause]

theorem ranking_position_eq_external_iff {s : Finset Component} :
    ranking.position s = .external ↔ s = {.immediateCause} := by
  decide +revert

-- §4.2.4
theorem position_swap :
    Ranking.position [.existence, .directedChange, .immediateCause] = ranking.position := by
  funext s
  revert s
  decide

/-- A ranking matches the book's iff internally caused verbs are unergative (§4.1.1) and those of
directed change (§4.2.1–§4.2.3) or existence (§4.2.4) unaccusative (§4.2). -/
theorem position_eq_ranking_iff (r : Ranking) : r.position = ranking.position ↔
    r.position {.immediateCause} = .external ∧
      r.position {.immediateCause, .directedChange} = .directInternal ∧
      r.position {.immediateCause, .existence} = .directInternal := by
  refine ⟨fun h ↦ by simp only [h]; decide, fun ⟨h₁, h₂, h₃⟩ ↦ funext fun s ↦ ?_⟩
  have key : r.position s = .external ↔ ranking.position s = .external := by
    rw [ranking_position_eq_external_iff]
    refine ⟨fun h ↦ ?_, fun h ↦ h ▸ h₁⟩
    rw [Ranking.position_eq_external_iff] at h
    rw [Ranking.position_eq_directInternal_iff] at h₂ h₃
    have hic : Component.immediateCause ∈ s := by simpa using List.find?_some h
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hic, fun c hc ↦ ?_⟩
    have := Ranking.rule_eq_some_of_subset (t := s) (s := {.immediateCause, c})
      (by simp [Finset.insert_subset_iff, hic, hc]) h (by simp)
    cases c <;> first | rfl | contradiction
  revert key
  cases r.position s <;> cases ranking.position s <;> simp

/-- Every ranking that matches the book's contains all three rules (§4.2). -/
theorem mem_of_position_eq_ranking {r : Ranking} (h : r.position = ranking.position)
    (c : Component) : c ∈ r := by
  obtain ⟨h₁, h₂, h₃⟩ := (position_eq_ranking_iff r).mp h
  rw [Ranking.position_eq_external_iff] at h₁
  rw [Ranking.position_eq_directInternal_iff] at h₂ h₃
  have hic : Component.immediateCause ∈ r := List.mem_of_find?_eq_some h₁
  have key {c : Component} (hc : r.rule {.immediateCause, c} ≠ some .immediateCause) :
      c ∈ r := by
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp
      (List.find?_isSome.mpr ⟨_, hic, by simp⟩ : (r.rule {.immediateCause, c}).isSome)
    obtain rfl | rfl : d = .immediateCause ∨ d = c := by simpa using List.find?_some hd
    · exact absurd hd hc
    · exact List.mem_of_find?_eq_some hd
  cases c
  exacts [hic, key h₂, key h₃]

/-- A monadic verb is unaccusative when its sole argument is a direct internal argument. -/
def Unaccusative (s : Finset Component) : Prop := ranking.position s = .directInternal

instance : DecidablePred Unaccusative := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- A verb is unergative exactly when its argument is the immediate cause and neither undergoes
a directed change nor has its existence at issue. -/
theorem unaccusative_iff {s : Finset Component} : Unaccusative s ↔ s ≠ {.immediateCause} := by
  rw [Unaccusative, ne_eq, ← ranking_position_eq_external_iff]
  cases ranking.position s <;> simp

-- §4.1.2, §4.2.1, §4.2.2, §4.2.3
theorem unaccusative_of_directedChange_mem {s : Finset Component}
    (h : .directedChange ∈ s) : Unaccusative s :=
  unaccusative_iff.mpr (by rintro rfl; simp at h)

-- §4.1.3, §4.2.4
theorem unaccusative_of_existence_mem {s : Finset Component} (h : .existence ∈ s) :
    Unaccusative s :=
  unaccusative_iff.mpr (by rintro rfl; simp at h)

/-! ### Appendix A: Levin's classes -/

/-- Appendix A's assignment of Levin's intransitive classes to the book's semantic classes, one
component set per construal the book discusses. The verbs of emission are internally caused
(§4.1.1.1); the verbs of inherently directed motion undergo a directed change, agentively or not
(§4.2.2); the roll verbs are externally caused with no directed change, and internally caused
when agentive (§4.1.4, §4.2.2); the run verbs are internally caused (§4.1.4); the verbs of
existence have their argument's existence at issue, agentively or not (§4.2.4), and so do the
verbs of appearance, occurrence and disappearance (§4.1.3); the verbs of spatial configuration
assert existence in their simple position sense, are internally caused in their maintain
position sense and add a directed change in their assume position sense (§4.1.1.2, §4.2.3); the
verbs of change of state undergo a directed change, externally caused for the break, bend,
cooking and other alternating verbs and internally caused for the entity-specific ones (§4.1.2,
§4.2.1). -/
def components : LevinClass → List (Finset Component)
  | .lightEmission | .soundEmission | .smellEmission | .substanceEmission => [{.immediateCause}]
  | .inherentlyDirectedMotion => [{.immediateCause, .directedChange}, {.directedChange}]
  | .roll => [∅, {.immediateCause}]
  | .run => [{.immediateCause}]
  | .exist => [{.immediateCause, .existence}, {.existence}]
  | .appear | .occurrence | .disappearance => [{.existence}]
  | .spatialConfiguration =>
    [{.existence}, {.immediateCause}, {.immediateCause, .directedChange}]
  | .break_ | .bend | .cooking | .otherChangeOfState => [{.directedChange}]
  | .entitySpecificChangeOfState => [{.immediateCause, .directedChange}]
  | _ => []

-- §4.1.1.1
theorem emission_not_unaccusative :
    ∀ c ∈ [LevinClass.lightEmission, .soundEmission, .smellEmission, .substanceEmission],
      ∀ s ∈ components c, ¬ Unaccusative s := by
  decide +kernel

-- §4.1.2, §4.2.1
theorem changeOfState_unaccusative :
    ∀ c ∈ [LevinClass.break_, .bend, .cooking, .otherChangeOfState,
      .entitySpecificChangeOfState], ∀ s ∈ components c, Unaccusative s := by
  decide +kernel

-- §4.2.2
theorem directedMotion_unaccusative :
    ∀ s ∈ components .inherentlyDirectedMotion, Unaccusative s := by
  decide

-- §4.1.3, §4.2.4
theorem existence_classes_unaccusative :
    ∀ c ∈ [LevinClass.exist, .appear, .occurrence, .disappearance],
      ∀ s ∈ components c, Unaccusative s := by
  decide +kernel

-- §4.1.4
theorem run_not_unaccusative : ∀ s ∈ components .run, ¬ Unaccusative s := by decide

-- §4.1.4, §4.2.2
theorem roll_variable :
    (∃ s ∈ components .roll, .immediateCause ∉ s ∧ Unaccusative s) ∧
      ∃ s ∈ components .roll, .immediateCause ∈ s ∧ ¬ Unaccusative s := by
  decide

-- §4.1.1.2, §4.2.3
theorem spatialConfiguration_variable :
    (∃ s ∈ components .spatialConfiguration, .existence ∈ s ∧ Unaccusative s) ∧
      (∃ s ∈ components .spatialConfiguration, .directedChange ∈ s ∧ Unaccusative s) ∧
      ∃ s ∈ components .spatialConfiguration, .immediateCause ∈ s ∧ ¬ Unaccusative s := by
  decide

/-! ### The diagnostics -/

/-- The position of a verb's sole argument that an acceptable instance of a row's diagnostic
indicates. The unergative resultative pattern, the X's way construction and a cognate object
indicate an external argument, the unaccusative resultative pattern a direct internal one
(§4.1.1, §4.1.2, §4.1.4). Locative inversion and there-insertion are no diagnostics here, since
chapter 6 finds unergative verbs in locative inversion too. -/
def diagnosticOf (ex : Datum) : Option Position :=
  ex.parse? "diagnostic" [("resultativeUnergativePattern", .external),
    ("wayConstruction", .external), ("cognateObject", .external),
    ("resultativeUnaccusativePattern", .directInternal)]

/-- The class of a row's verb, by Levin's section number. -/
def classOf (ex : Datum) : Option LevinClass :=
  (ex.feature? "class").bind LevinClass.ofNumberString?

/-- The construals of a row's verb are those of its class, narrowed by the row's agentivity where
it records one. An agentive argument is the immediate cause (§4.1.1); the rows record agentivity
only for verbs of motion and of spatial configuration, whose nonagentive construals lack an
immediate cause (§4.1.1.2, §4.1.4). -/
def construals (ex : Datum) : List (Finset Component) :=
  match classOf ex, ex.parse? "agentive" [("yes", true), ("no", false)] with
  | some c, some a => (components c).filter fun s ↦ decide (.immediateCause ∈ s) == a
  | some c, none => components c
  | none, _ => []

theorem construals_ne_nil : ∀ ex ∈ Examples.all, construals ex ≠ [] := by decide

/-- Every diagnostic row is acceptable exactly when the linking puts the verb's argument in the
position the diagnostic indicates. -/
theorem diagnostics_agree :
    ∀ ex ∈ Examples.all, ∀ p ∈ diagnosticOf ex, ∀ s ∈ construals ex,
      (ex.judgment = .acceptable ↔ ranking.position s = p) := by
  decide

/-- Locative inversion excludes the unaccusative (18a) and admits the unergative (22a), so it is no
unaccusative diagnostic (§6.2.2). -/
theorem locativeInversion_not_diagnostic :
    (Examples.ex6_18a.judgment ≠ .acceptable ∧ ∀ s ∈ construals Examples.ex6_18a, Unaccusative s) ∧
      Examples.ex6_22a.judgment = .acceptable ∧
      ∀ s ∈ construals Examples.ex6_22a, ¬ Unaccusative s := by
  decide

/-! ### The English fragment -/

/-- The English entry of a row's verb, in its default sense. -/
def entryOf (ex : Datum) : Option Verb :=
  (ex.feature? "verb").bind (Verb.find? (English.Verbs.verbs.map (·.toVerb)))

theorem entryOf_isSome :
    ∀ ex ∈ [Examples.ex4_25a, Examples.ex4_25b, Examples.ex4_25c, Examples.ex4_31a,
      Examples.ex4_50a, Examples.ex4_50b, Examples.ex6_1],
      (entryOf ex).isSome := by
  decide

/-- Where a row's class gives one verdict, the English fragment classifies the entry for its verb
as the linking rules do: *break*, *burn*, *freeze*, *arrive* and *appear* are unaccusative, and
*run* and *swim* unergative. -/
theorem isUnaccusative_agrees :
    ∀ ex ∈ Examples.all, ∀ v ∈ entryOf ex, ∀ c ∈ classOf ex,
      ((∀ s ∈ components c, Unaccusative s) → v.IsUnaccusative) ∧
        ((∀ s ∈ components c, ¬ Unaccusative s) → v.IsUnergative) := by
  decide +kernel

-- ch. 1 (13)–(15), §4.1.2 (29)
theorem italian_directedMotion_isUnaccusative :
    ∀ v ∈ [Italian.Verbs.venire, Italian.Verbs.arrivare], v.toVerb.IsUnaccusative := by
  decide

-- (2): *chiacchierare* 'chat', an agentive verb, is unergative, as is *lavorare* 'work'
theorem italian_agentive_isUnergative :
    ∀ v ∈ [Italian.Verbs.chiacchierare, Italian.Verbs.lavorare], v.toVerb.IsUnergative := by
  decide

theorem werken_isUnergative : Dutch.Verbs.werken.toVerb.IsUnergative := by decide

-- (78), §4.2.2: *salire* 'go up' is unaccusative, here by its change along a scale of height
theorem salire_isUnaccusative : Italian.Verbs.salire.toVerb.IsUnaccusative := by decide

-- (14), §5.1.1: a directional phrase makes *correre* 'run' unaccusative, while *nuotare* 'swim',
-- which selects none, stays as it is
theorem correre_withPath_isUnaccusative :
    (Italian.Verbs.correre.withPath (.ofCase .ill)).toVerb.IsUnaccusative ∧
      ¬ Italian.Verbs.correre.toVerb.IsUnaccusative ∧
      ¬ (Italian.Verbs.nuotare.withPath (.ofCase .ill)).toVerb.IsUnaccusative := by
  decide

/-- `Verb.IsUnaccusative` counts *buzz*, *flash* and *bleed* unaccusative by their causative pairs
((82), (92), (86)), though as emission verbs they are unergative (§3.2.5). -/
theorem causativePairs_diverge :
    ∀ v ∈ [English.Verbs.buzz, English.Verbs.flash, English.Verbs.bleed], v.IsUnaccusative ∧
      ∀ c ∈ v.levinClasses, ∀ s ∈ components c, ¬ Unaccusative s := by
  decide +kernel

end LevinRappaportHovav1995
