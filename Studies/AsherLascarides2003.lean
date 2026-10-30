module

public import Linglib.Data.Examples.AsherLascarides2003
public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Relation
public import Linglib.Data.Examples.Readers

/-!
# Asher & Lascarides 2003: the right frontier

In Segmented Discourse Representation Theory a discourse is a set of labelled constituents
whose contents include rhetorical relations between labels. New information may attach only
at an available label: the last label, any label whose content contains a relation mentioning
an available label, and any label linked to an available one by a subordinating relation —
Elaboration, Explanation, or the topic relation — but not by a coordinating one such as
Narration or Background. In the book's five-sentence narrative, an evening elaborated by a
meal and a dance competition, with the meal elaborated by salmon and cheese, the salmon clause
is off the frontier once the competition is last, so *It was a beautiful pink* cannot continue
the discourse. In the book's abstract example, a topic over a constituent containing two units
related by Background, the first of those units is the one label not available.

## Main definitions

* `Rel`, `Rel.Subordinating`: rhetorical relations, including the topic relation ⇓.
* `SDRS`, `SDRS.Above`, `SDRS.Available`: labelled structures, one-step ascent on the
  frontier, and availability as its reflexive-transitive closure from the last label.
* `example17`, `example21`: the two worked structures and their frontiers.

## References

* [asher-lascarides-2003]
-/

@[expose] public section

namespace AsherLascarides2003

open Relation

/-! ### Rhetorical relations -/

/-- The rhetorical relations of the worked structures, with the topic relation ⇓ between a
    summarizing constituent and the one it summarizes. -/
inductive Rel
  | narration
  | background
  | elaboration
  | explanation
  | topic
  deriving DecidableEq

/-- Elaboration, Explanation, and the topic relation subordinate; Narration and Background
    coordinate. -/
abbrev Rel.Subordinating (r : Rel) : Prop := r = .elaboration ∨ r = .explanation ∨ r = .topic

/-! ### Structures and the right frontier -/

variable {L : Type*}

/-- A relation conjunct `R(source, target)` in the content of `container`. -/
structure Edge (L : Type*) where
  container : L
  source : L
  target : L
  relation : Rel
  deriving DecidableEq

/-- A segmented discourse representation structure: its relation conjuncts and last label. -/
structure SDRS (L : Type*) where
  edges : List (Edge L)
  last : L

/-- One step up the frontier from `α` to `γ`: a relation in `γ`'s content mentions `α`, or a
    subordinating relation runs from `γ` to `α`. -/
def SDRS.Above (s : SDRS L) (α γ : L) : Prop :=
  (∃ e ∈ s.edges, e.container = γ ∧ (e.source = α ∨ e.target = α)) ∨
    ∃ e ∈ s.edges, e.source = γ ∧ e.target = α ∧ e.relation.Subordinating

instance [DecidableEq L] (s : SDRS L) (α γ : L) : Decidable (s.Above α γ) := by
  unfold SDRS.Above; infer_instance

/-- A label is available for attachment when it lies on the right frontier: reachable from
    the last label by ascending. -/
def SDRS.Available (s : SDRS L) : L → Prop := ReflTransGen s.Above s.last

/-! ### The worked examples -/

/-- The structure of the five-sentence narrative: the evening `1` elaborated by `6`, in which
    the meal `2` is narrated with the competition `5` and elaborated by `7`, in which the
    salmon `3` is narrated with the cheese `4`; the competition is last. -/
def example17 : SDRS ℕ where
  edges := [⟨0, 1, 6, .elaboration⟩, ⟨6, 2, 5, .narration⟩, ⟨6, 2, 7, .elaboration⟩,
    ⟨7, 3, 4, .narration⟩]
  last := 5

theorem available17_iff (γ : ℕ) : example17.Available γ ↔ γ ∈ [0, 1, 5, 6] := by
  constructor
  · intro h
    induction h with
    | refl => decide
    | tail _ hab ih =>
      simp [SDRS.Above, example17, Rel.Subordinating] at hab
      simp at ih ⊢
      omega
  · have h6 : example17.Available 6 := ReflTransGen.single (by decide)
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro (rfl | rfl | rfl | rfl)
    · exact h6.tail (by decide)
    · exact h6.tail (by decide)
    · exact ReflTransGen.refl
    · exact h6

/-- The label of the constituent introducing a row's pronoun antecedent. -/
def antecedentLabel? (r : Datum) : Option ℕ :=
  match r.feature? "antecedentLabel" with
  | some "3" => some 3
  | _ => none

theorem rows_continuation :
    ∀ r ∈ Examples.all, ∀ a ∈ antecedentLabel? r,
      (r.judgment = .acceptable ↔ example17.Available a) := by
  simp only [available17_iff]
  decide

/-- The abstract example: a topic `3` over a constituent `4` whose content relates `1` and
    `2` by Background, with `2` last. -/
def example21 : SDRS ℕ where
  edges := [⟨0, 3, 4, .topic⟩, ⟨4, 1, 2, .background⟩]
  last := 2

theorem available21_iff (γ : ℕ) : example21.Available γ ↔ γ ∈ [0, 2, 3, 4] := by
  constructor
  · intro h
    induction h with
    | refl => decide
    | tail _ hab ih =>
      simp [SDRS.Above, example21, Rel.Subordinating] at hab
      simp at ih ⊢
      omega
  · have h4 : example21.Available 4 := ReflTransGen.single (by decide)
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro (rfl | rfl | rfl | rfl)
    · exact h4.tail (by decide)
    · exact ReflTransGen.refl
    · exact h4.tail (by decide)
    · exact h4

end AsherLascarides2003
