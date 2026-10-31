module

public import Linglib.Data.Examples.Anderson2006b
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Minimal
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.Examples.Readers

/-!
# Anderson (2006): Modern Grammars of Case: A Retrospective

In the localist case grammar of the book's sixth chapter, a semantic relation combines three
first-order features, the absolutive, the source and the locative, with second-order features that
make its absolutive or its locative a source or a goal. Each feature occupies a cell of a grid of
two places, each with a plain member, a source and a goal: the absolutive is the plain nonspatial
member, the ergative the nonspatial source, and the locative the plain spatial member. A case form
that expresses several relations neutralizes them, leaving as residue the cells they share.

Goal specification makes a place of an argument a goal when a co-argument bears that place's
source. Subject formation gives an absolutive that is not a goal a second-order source, and the
subject is the argument a hierarchy ranks highest. The book's subjects share no cell, but once
formed they share the nonspatial source: unlike French *à*, subjecthood is a neutralization whose
residue a rule supplies.

## Implementation notes

* The comma of the hierarchy reads "combined with some other relation". The optional comma on the
  absolutive is left out: the *with*-phrase of *The tank flooded with sewage* is a circumstantial.
* The rows record second-order features as the book prints them. The rules and the hierarchy read
  only the cells, so to them a derived source and an inherent one look alike.
* A subject is any argument of maximal rank, since the hierarchy leaves equatives open.

## TODO

* The book prints the objects of *Bill read the book*, *knew* and *acquired* as plain absolutives,
  though goal specification makes them goals, and it prints the locative goals of *fell*, *flew*
  and *acquired* without the source that makes them goals, which directional verbs leave
  unexpressed. Recording those sources needs the verbs' valencies.

## References

* [anderson-2006b]
-/

@[expose] public section

namespace Anderson2006b

/-- The three first-order case features. -/
inductive Feature
  | abs
  | src
  | loc
  deriving DecidableEq

/-- The two places of the localist analysis. -/
inductive Place
  | nonspatial
  | spatial
  deriving DecidableEq, Fintype

/-- The two directions a second-order feature gives a place. -/
inductive Direction
  | src
  | goal
  deriving DecidableEq, Fintype

/-- A cell of the localist grid is a place with a direction, or with none for its plain member. -/
abbrev Cell := Place × Option Direction

/-- The absolutive is the plain nonspatial member, the ergative the nonspatial source, and the
locative the plain spatial member. -/
def Feature.cell : Feature → Cell
  | .abs => (.nonspatial, none)
  | .src => (.nonspatial, some .src)
  | .loc => (.spatial, none)

/-- A semantic relation is a combination of first-order features with second-order ones, each a
direction at a place. -/
structure Relation where
  /-- The first-order features. -/
  features : Finset Feature
  /-- The second-order features. -/
  second : Finset (Place × Direction) := ∅
  deriving DecidableEq

/-- A predication lists the relations its predicator's arguments bear. -/
abbrev Predication := List Relation

namespace Relation

instance : Membership Feature Relation := ⟨fun r f ↦ f ∈ r.features⟩

instance (f : Feature) (r : Relation) : Decidable (f ∈ r) :=
  inferInstanceAs (Decidable (f ∈ r.features))

variable {r : Relation} {p : Predication}

@[simp]
theorem mem_features {f : Feature} : f ∈ r.features ↔ f ∈ r := .rfl

/-- The cells a relation occupies, first-order and second-order features alike. -/
def cells (r : Relation) : Finset Cell :=
  r.features.image Feature.cell ∪ r.second.image (Prod.map id some)

/-- A relation bears the source of a place. -/
def HasSourceAt (r : Relation) (x : Place) : Prop := (x, some .src) ∈ r.cells

instance (x : Place) : Decidable (r.HasSourceAt x) := inferInstanceAs (Decidable (_ ∈ _))

@[simp]
theorem nonspatial_none_mem_cells : (.nonspatial, none) ∈ r.cells ↔ .abs ∈ r := by
  simp only [cells, Finset.mem_union, Finset.mem_image, mem_features]
  refine ⟨?_, fun h ↦ .inl ⟨.abs, h, rfl⟩⟩
  rintro (⟨f, hf, h⟩ | ⟨c, -, h⟩)
  · cases f <;> simp_all [Feature.cell]
  · simp [Prod.map] at h

/-! ### Named relations -/

/-- The absolutive, the semantically empty relation. -/
abbrev absolutive : Relation := ⟨{.abs}, ∅⟩

/-- The ergative, a source that is not locative. -/
abbrev ergative : Relation := ⟨{.src}, ∅⟩

/-- The simple locative. -/
abbrev locative : Relation := ⟨{.loc}, ∅⟩

/-- The experiencer, a locative source. -/
abbrev experiencer : Relation := ⟨{.src, .loc}, ∅⟩

/-- The contactive, an absolutive locative. -/
abbrev contactive : Relation := ⟨{.abs, .loc}, ∅⟩

/-- A relation is a patient when it combines the locative with the absolutive or the source. -/
def IsPatient (r : Relation) : Prop := .loc ∈ r ∧ (.abs ∈ r ∨ .src ∈ r)

instance : DecidablePred IsPatient := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

theorem isPatient_experiencer : IsPatient experiencer := by decide

theorem isPatient_contactive : IsPatient contactive := by decide

/-! ### Goals and derived sources -/

/-- Goal specification makes a place of an argument a goal when the argument bears that place's
plain member but not its source, and a co-argument bears its source. -/
def IsGoalAt (r : Relation) (x : Place) (p : Predication) : Prop :=
  (x, none) ∈ r.cells ∧ ¬ r.HasSourceAt x ∧ ∃ s ∈ p, s.HasSourceAt x

instance (x : Place) : Decidable (r.IsGoalAt x p) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Subject formation makes an absolutive a source when it bears no nonspatial source and is not
a nonspatial goal. -/
def IsDerivedSourceOf (r : Relation) (p : Predication) : Prop :=
  .abs ∈ r ∧ ¬ r.HasSourceAt .nonspatial ∧ ¬ r.IsGoalAt .nonspatial p

instance : Decidable (r.IsDerivedSourceOf p) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem isDerivedSourceOf_iff : r.IsDerivedSourceOf p ↔
    .abs ∈ r ∧ ¬ r.HasSourceAt .nonspatial ∧ ∀ s ∈ p, ¬ s.HasSourceAt .nonspatial := by
  simp +contextual [IsDerivedSourceOf, IsGoalAt]

/-- Subject formation gives a derived source a second-order source on its absolutive. -/
def formSubject (p : Predication) (r : Relation) : Relation :=
  if r.IsDerivedSourceOf p then { r with second := insert (.nonspatial, .src) r.second } else r

theorem hasSourceAt_formSubject_iff : (formSubject p r).HasSourceAt .nonspatial ↔
    r.HasSourceAt .nonspatial ∨ r.IsDerivedSourceOf p := by
  unfold formSubject
  split_ifs with h
  · simp [HasSourceAt, cells, h]
  · simp [h]

/-! ### Subject selection -/

/-- The rank of a relation on the subject selection hierarchy. A simple ergative outranks a
combined one, which outranks any absolutive, and a relation with neither is off the hierarchy. -/
def subjectRank (r : Relation) : ℕ :=
  if r.HasSourceAt .nonspatial then (if r.cells = ergative.cells then 3 else 2)
  else if .abs ∈ r then 1 else 0

theorem subjectRank_pos_iff : 0 < r.subjectRank ↔ r.HasSourceAt .nonspatial ∨ .abs ∈ r := by
  unfold subjectRank; split_ifs <;> simp_all

theorem two_le_subjectRank_iff : 2 ≤ r.subjectRank ↔ r.HasSourceAt .nonspatial := by
  unfold subjectRank; split_ifs <;> simp_all

theorem subjectRank_lt_ergative (h : r.cells ≠ ergative.cells) :
    r.subjectRank < ergative.subjectRank := by
  rw [show ergative.subjectRank = 3 by decide]
  unfold subjectRank; split_ifs <;> simp_all

/-- A subject of a predication is an argument of maximal rank on the hierarchy. -/
def IsSubjectOf (r : Relation) (p : Predication) : Prop :=
  MaximalFor (fun s ↦ s ∈ p ∧ 0 < s.subjectRank) subjectRank r

theorem isSubjectOf_iff :
    r.IsSubjectOf p ↔ r ∈ p ∧ 0 < r.subjectRank ∧ ∀ s ∈ p, s.subjectRank ≤ r.subjectRank := by
  rw [IsSubjectOf, maximalFor_iff_forall_gt]
  grind

instance : Decidable (r.IsSubjectOf p) := decidable_of_iff' _ isSubjectOf_iff

theorem isSubjectOf_iff_isDerivedSourceOf (hr : r ∈ p) (hsrc : ¬ r.HasSourceAt .nonspatial) :
    r.IsSubjectOf p ↔ r.IsDerivedSourceOf p := by
  rw [isSubjectOf_iff, isDerivedSourceOf_iff]
  grind [subjectRank_pos_iff, two_le_subjectRank_iff]

theorem IsSubjectOf.hasSourceAt_or_isDerivedSourceOf (h : r.IsSubjectOf p) :
    r.HasSourceAt .nonspatial ∨ r.IsDerivedSourceOf p :=
  or_iff_not_imp_left.2 fun hsrc ↦
    (isSubjectOf_iff_isDerivedSourceOf (isSubjectOf_iff.1 h).1 hsrc).1 h

/-- Every subject, once formed, bears the nonspatial source, inherent or derived. -/
theorem IsSubjectOf.hasSourceAt_formSubject (h : r.IsSubjectOf p) :
    (formSubject p r).HasSourceAt .nonspatial :=
  hasSourceAt_formSubject_iff.2 h.hasSourceAt_or_isDerivedSourceOf

theorem IsSubjectOf.not_isGoalAt (h : r.IsSubjectOf p) : ¬ r.IsGoalAt .nonspatial p := fun hg ↦
  h.hasSourceAt_or_isDerivedSourceOf.elim hg.2.1 fun hd ↦ hd.2.2 hg

/-! ### The book's examples -/

/-- The labels the example rows give the relations. -/
def labels : List (String × Relation) :=
  [("abs", absolutive), ("erg", ergative), ("loc", locative), ("abs,erg", ⟨{.abs, .src}, ∅⟩),
    ("erg,loc", experiencer), ("abs,loc", contactive), ("abs,erg,loc", ⟨{.abs, .src, .loc}, ∅⟩),
    ("loc{goal}", ⟨{.loc}, {(.spatial, .goal)}⟩), ("loc{src}", ⟨{.loc}, {(.spatial, .src)}⟩),
    ("erg,loc{goal}", ⟨{.src, .loc}, {(.spatial, .goal)}⟩),
    ("abs,erg,loc{goal}", ⟨{.abs, .src, .loc}, {(.spatial, .goal)}⟩)]

end Relation

/-! ### Neutralization -/

/-- The residue of a neutralization is the cells every neutralized relation occupies. -/
def residue (E : Finset Relation) : Finset Cell := E.inf Relation.cells

/-- The relations a row records under a key, if every label names one. -/
def relationsOf? (e : Datum) (key : String) : Option (List Relation) :=
  (e.features key).mapM (List.lookup · Relation.labels)

/-- The predication a row records. Adjuncts are not arguments. -/
abbrev Predication.ofRow? (e : Datum) : Option Predication := relationsOf? e "arg"

/-- The subject a row records. -/
def subject? (e : Datum) : Option Relation := e.parse? "subject" Relation.labels

/-- The subject a row records, once formed. -/
def formedSubject? (e : Datum) : Option Relation := do
  Relation.formSubject (← Predication.ofRow? e) (← subject? e)

/-- The hierarchy selects the subject the book records for each of its examples, and only that
argument. -/
theorem rows_subject : ∀ e ∈ Examples.all, e.feature? "subject" ≠ none →
    ∃ p ∈ Predication.ofRow? e, ∃ r ∈ subject? e,
      r.IsSubjectOf p ∧ ∀ s ∈ p, s.IsSubjectOf p → s = r := by
  decide +kernel

theorem read_object_goal :
    ∃ p ∈ Predication.ofRow? Examples.ex_39a, ∃ r ∈ p, r.IsGoalAt .nonspatial p := by
  decide +kernel

theorem suffered_subject :
    ∃ p ∈ Predication.ofRow? Examples.ex_34, ∃ r ∈ p, r.IsSubjectOf p ∧
      Relation.experiencer.features ⊆ r.features ∧ Relation.contactive.features ⊆ r.features ∧
        r.IsGoalAt .spatial p := by
  decide +kernel

/-- *À* neutralizes spatial goal and simple location, leaving in common a locative that is not a
source. -/
theorem residue_a : ∃ E ∈ relationsOf? Examples.ex_3 "neutralized",
    residue E.toFinset = Relation.locative.cells ∧ ∀ r ∈ E, ¬ r.HasSourceAt .spatial := by
  decide +kernel

theorem residue_subjects :
    ∃ E ∈ [Examples.ex_39a, Examples.ex_39c, Examples.ex_39h, Examples.ex_39i,
      Examples.ex_39j].mapM subject?, residue E.toFinset = Relation.ergative.cells := by
  decide +kernel

/-- With the subject of *Bill fell to the ground*, the book's subjects share no cell. -/
theorem residue_subjects_fell :
    ∃ E ∈ [Examples.ex_39a, Examples.ex_39b, Examples.ex_39c, Examples.ex_39h, Examples.ex_39i,
      Examples.ex_39j].mapM subject?, residue E.toFinset = ∅ := by
  decide +kernel

/-- Once formed, the book's subjects share the nonspatial source. -/
theorem residue_formedSubjects :
    ∃ E ∈ [Examples.ex_39a, Examples.ex_39b, Examples.ex_39c, Examples.ex_39h, Examples.ex_39i,
      Examples.ex_39j].mapM formedSubject?, residue E.toFinset = Relation.ergative.cells := by
  decide +kernel

theorem fell_flew_neutralized :
    ∃ r ∈ formedSubject? Examples.ex_39b, ∃ s ∈ subject? Examples.ex_39c,
      r.cells = s.cells ∧ r ≠ s := by
  decide +kernel

end Anderson2006b
