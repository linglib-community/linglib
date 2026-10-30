module

public import Linglib.Semantics.Quantification.Basic
public import Mathlib.Order.Hom.Basic
public import Linglib.Data.Examples.RitchieSchiller2024

/-!
# Ritchie and Schiller (2024): Default domain restriction possibilities

This file formalizes the paper's account of why some implicit restrictions on quantifier
domains, to the present location and time, are available without conversational setup
while others, by colour, history, aesthetics or subkind, are not. The domain of
quantification is what is relevant to the interlocutors' joint purpose, and when only the
minimal shared aims of predicting, explaining and manipulating the environment are in place
the domain is delivered by cognitive heuristics: perceptual availability, and the two
salience heuristics of perceptual salience and manipulability, which filter the available
objects. A `Situation` fixes what is present, perceivable, attention-grabbing and
controllable from a viewpoint, the heuristics are its filters, `Situation.restrictors`, and
every restriction they deliver lies within the here and now, `default_subset_present`,
which is why locational and temporal restrictions are the defaults. Non-default restrictions become
available when a discourse move or a prior plan installs a more specific purpose,
`Situation.domain`, and displacement is the same heuristics applied from another
viewpoint. The paper's examples are rows, and `default_of_acceptable` records that every
restriction acceptable without setup is a heuristic one.

## Implementation notes

The nesting of the heuristics is derived from their definition as intersections with the
available objects, so the filters form an order homomorphism from the heuristic scale to
domains and the quantifier entailments between them come from the substrate. The paper's
arguments against rational-pragmatic, discourse-structural and intentionalist explanations,
its objectivity and spatial-cognition supplements, and its proposed experiments are not
formalized.

## References

* [K. Ritchie, H. Schiller, *Default domain restriction possibilities*
  (2024)][ritchie-schiller-2024]
* [C. Roberts, *Information structure in discourse: towards an integrated formal theory of
  pragmatics* (2012)][roberts-2012]
* [H. P. Grice, *Logic and conversation* (1975)][grice-1975]
* [G. Scontras, J. Degen, N. D. Goodman, *Subjectivity predicts adjective ordering
  preferences* (2017)][scontras-degen-goodman-2017]
-/

@[expose] public section

namespace RitchieSchiller2024

open Quantifier.Det

/-! ### Cognitive heuristics -/

/-- A perceptual situation relative to viewpoints records which entities are present at the
viewpoint's location and time, which it could perceive with minimal bodily distortion,
which grab its attention, and which it could control, move or interact with. -/
structure Situation (V E : Type*) where
  present : V → Set E
  perceivable : V → Set E
  attentionGrabbing : V → Set E
  controllable : V → Set E

variable {V E : Type*} (s : Situation V E) (v : V)

namespace Situation

/-- The perceptually available entities are the perceivable ones, which only present objects
are. -/
def available : Set E := s.present v ∩ s.perceivable v

/-- The manipulable entities are the available and controllable ones, the second salience
heuristic. -/
def manipulable : Set E := s.available v ∩ s.controllable v

/-- The salient entities are the available ones that are attention-grabbing or manipulable,
manipulability being a way of being salient. -/
def salient : Set E := s.available v ∩ (s.attentionGrabbing v ∪ s.controllable v)

theorem available_subset_present : s.available v ⊆ s.present v := Set.inter_subset_left

theorem salient_subset_available : s.salient v ⊆ s.available v := Set.inter_subset_left

theorem manipulable_subset_salient : s.manipulable v ⊆ s.salient v :=
  Set.inter_subset_inter_right _ Set.subset_union_right

end Situation

/-- The heuristics as filters on the domain, from the most restrictive to none. -/
inductive Heuristic where
  | manipulability
  | salience
  | availability
  | none
  deriving DecidableEq, Fintype

namespace Heuristic

def toFin : Heuristic → Fin 4
  | .manipulability => 0
  | .salience => 1
  | .availability => 2
  | .none => 3

theorem toFin_injective : Function.Injective toFin := by
  intro a b h; cases a <;> cases b <;> simp_all [toFin]

noncomputable instance : LinearOrder Heuristic := LinearOrder.lift' toFin toFin_injective

instance : OrderTop Heuristic where
  top := .none
  le_top a := by cases a <;> decide

end Heuristic

/-- The default domain restriction possibilities of a situation are the domains the heuristics
deliver, nested because each filters the last, so an order homomorphism from the heuristic
scale to domains. -/
def Situation.restrictors : Heuristic →o Set E where
  toFun
    | .manipulability => s.manipulable v
    | .salience => s.salient v
    | .availability => s.available v
    | .none => Set.univ
  monotone' a b hab := by
    cases a <;> cases b <;> first
      | exact absurd hab (by decide)
      | exact subset_rfl
      | exact Set.subset_univ _
      | exact s.manipulable_subset_salient v
      | exact s.salient_subset_available v
      | exact (s.manipulable_subset_salient v).trans (s.salient_subset_available v)

theorem Situation.restrictors_top : s.restrictors v ⊤ = Set.univ := rfl

/-- A restriction is a default in a situation when a heuristic delivers it. -/
def Situation.IsDefault (C : Set E) : Prop := ∃ h, s.restrictors v h = C

theorem default_subset_present {h : Heuristic} (hh : h ≠ ⊤) :
    s.restrictors v h ⊆ s.present v := by
  cases h with
  | none => exact absurd rfl hh
  | availability => exact s.available_subset_present v
  | salience => exact (s.salient_subset_available v).trans (s.available_subset_present v)
  | manipulability =>
    exact (s.manipulable_subset_salient v).trans
      ((s.salient_subset_available v).trans (s.available_subset_present v))

theorem not_isDefault_of_not_subset {C : Set E} (hC : ¬ C ⊆ s.present v) (hu : C ≠ Set.univ) :
    ¬ s.IsDefault v C := by
  rintro ⟨h, rfl⟩
  by_cases hh : h = ⊤
  · exact hu (hh ▸ rfl)
  · exact hC (default_subset_present s v hh)

theorem every_salient_of_every_available (R S : E → Prop) :
    adjRestrict every (s.available v) R S → adjRestrict every (s.salient v) R S :=
  restrictorAntitone_every S fun _ hx ↦ ⟨hx.1, s.salient_subset_available v hx.2⟩

theorem some_available_of_some_salient (R S : E → Prop) :
    adjRestrict Quantifier.Det.some (s.salient v) R S →
      adjRestrict Quantifier.Det.some (s.available v) R S :=
  restrictorMonotone_some S fun _ hx ↦ ⟨hx.1, s.salient_subset_available v hx.2⟩

/-! ### Joint purposes -/

/-- The joint purpose in force is either the minimal shared aims, under which a heuristic fixes
the domain, or a specific purpose, installed by a discourse move or a prior plan, which makes
its own objects relevant. -/
inductive Purpose (E : Type*) where
  | minimal (h : Heuristic)
  | specific (relevant : Set E)

/-- The domain of quantification tracks the objects relevant to the joint purpose. -/
def Situation.domain : Purpose E → Set E
  | .minimal h => s.restrictors v h
  | .specific relevant => relevant

theorem isDefault_domain_minimal (h : Heuristic) : s.IsDefault v (s.domain v (.minimal h)) :=
  ⟨h, rfl⟩

theorem exists_specific_of_not_isDefault {p : Purpose E} (hp : ¬ s.IsDefault v (s.domain v p)) :
    ∃ relevant, p = .specific relevant := by
  cases p with
  | minimal h => exact absurd (isDefault_domain_minimal s v h) hp
  | specific relevant => exact ⟨relevant, rfl⟩

/-! ### The paper's examples -/

/-- What an implicit restriction restricts by. -/
inductive Restriction where
  | location
  | time
  | availability
  | salience
  | manipulability
  | color
  | aesthetic
  | history
  | subkind
  | shape
  | plan
  deriving DecidableEq, Fintype

/-- The restrictions the cognitive heuristics deliver. -/
def Restriction.IsHeuristic : Restriction → Prop
  | .location | .time | .availability | .salience | .manipulability => True
  | _ => False

instance : DecidablePred Restriction.IsHeuristic := λ r => by
  cases r <;> unfold Restriction.IsHeuristic <;> infer_instance

/-- Whether a locational or temporal restriction is to the speaker's here and now. -/
inductive Anchor where
  | hereNow
  | elsewhere
  deriving DecidableEq, Fintype

/-- The conversational setup, if any, that introduces a specific purpose. -/
inductive Setup where
  | none
  | question
  | assertion
  | directive
  | priorGoal
  | displacement
  deriving DecidableEq, Fintype

/-- An example records the intended restriction, its anchor, the setup, and the judgment. -/
structure Row where
  restriction : Restriction
  anchor : Anchor
  setup : Setup
  judgment : Judgment

/-- A default restriction possibility is a heuristic restriction anchored to the here and
now. -/
def Row.IsDefault (d : Row) : Prop := d.restriction.IsHeuristic ∧ d.anchor = .hereNow

instance : DecidablePred Row.IsDefault := λ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- A datum read into its row; the anchor is the here and now unless the row says
otherwise. -/
def Row.ofDatum (e : Datum) : Option Row := do
  let r ← e.parse? "restriction"
    [("location", .location), ("time", .time), ("availability", .availability),
     ("salience", .salience), ("manipulability", .manipulability), ("color", .color),
     ("aesthetic", .aesthetic), ("history", .history), ("subkind", .subkind),
     ("shape", .shape), ("plan", .plan)]
  let a := (e.parse? "anchor" [("hereNow", .hereNow), ("elsewhere", .elsewhere)]).getD .hereNow
  let s ← e.parse? "setup"
    [("none", .none), ("question", .question), ("assertion", .assertion),
     ("directive", .directive), ("priorGoal", .priorGoal), ("displacement", .displacement)]
  pure ⟨r, a, s, e.judgment⟩

theorem isSome_ofDatum : ∀ e ∈ Examples.all, (Row.ofDatum e).isSome := by decide

/-- The paper's examples. -/
def data : List Row := Examples.all.filterMap Row.ofDatum

theorem default_of_acceptable :
    ∀ d ∈ data, d.setup = .none → d.judgment = .acceptable → d.IsDefault := by
  decide

theorem nondefault_attested :
    (∃ d ∈ data, ¬ d.IsDefault ∧ d.judgment = .acceptable) ∧
      ∃ d ∈ data, d.IsDefault ∧ d.setup = .none ∧ d.judgment = .acceptable := by
  decide

end RitchieSchiller2024
