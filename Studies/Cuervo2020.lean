module

public import Studies.Cuervo2003

/-!
# Cuervo (2020): Datives as applicatives

This file formalizes the typology of applicatives that derives the interpretation of an applied
argument from the configuration of a single head, minimally one that orients a participant to its
complement. Three properties of the configuration decide the interpretation: whether the
complement is non-verbal or verbal, whether it is dynamic or stative, and whether a verbal head
embeds the applicative phrase. An applicative with a non-verbal complement is low, and its
argument a recipient, a source or a possessor by the relation of the head, the one distinction the
configuration does not supply. Over a verbal complement the argument is [affected when the
complement is a state and a verbal head embeds the phrase](##role_eq_affected_iff), [an
experiencer when none does](##role_eq_experiencer_iff), and over a dynamic complement [a causee
when embedded](##role_eq_causee_iff) and [a benefactive or instrumental
otherwise](##role_eq_benefactive_iff). The typology [refines the table of datives of the
dissertation](##role_mem_meanings), which leaves the causee unnamed and gives a non-embedded
applicative over a change both the experiencer and the benefactive reading.

## Implementation notes

* A high applicative is here any applicative with a verbal complement, so the affected and the
  high sites of `Minimalist.Appl.Site` are both high, embedded and non-embedded.
* Benefactive stands for the leaf of the typology that holds benefactives, malefactives, ethical
  datives and instrumentals, which the configuration does not tell apart.

## TODO

* The chapter's fourth property, an external argument above the applicative, separates the
  experiencer from the benefactive over a state and the accidental causer from the benefactive
  over a change. An event structure that is a chain of verbal heads cannot place Voice over a
  state, so the property is not represented.
* Applicatives with a prepositional or small-clause complement, which the chapter counts as low,
  and applicatives above the verbal domain.
* The chapter's examples are not yet rows of `Data/Examples`.

## References

* [cuervo-2020]
* [cuervo-2003]
* [wood-marantz-2017]
* [pylkkanen-2008]
-/

@[expose] public section

namespace Cuervo2020

open Minimalist

/-- The interpretations of an applied argument, the leaves of the typology. -/
inductive Role where
  | recipient
  | source
  | possessor
  | causee
  /-- A benefactive, malefactive, ethical or instrumental argument. -/
  | benefactive
  | affected
  | experiencer
  deriving DecidableEq, Repr

/-- The interpretation of the argument of a low applicative with the given relation. -/
def Role.ofRelation : Appl.LowRelation → Role
  | .recipient => .recipient
  | .source => .source
  | .possessor => .possessor

/-- The typology: the interpretation of an applied argument at a site, given the relation a low
applicative establishes. -/
def role (s : Appl.Site) (r : Appl.LowRelation) : Role :=
  match s.complementHead with
  | none => .ofRelation r
  | some v =>
    if v.Dynamic then if s.High then .benefactive else .causee
    else if s.High then .experiencer else .affected

variable {s : Appl.Site} {r : Appl.LowRelation}

theorem role_of_low (h : s.Low) : role s r = .ofRelation r := by
  simp [role, Appl.Site.complementHead_eq_none_iff.2 h]

/-- An argument is affected exactly when its applicative takes a state and a verbal head embeds
the applicative phrase. -/
theorem role_eq_affected_iff :
    role s r = .affected ↔ s.Affected ∧ s.complementHead = some .vBE := by
  obtain ⟨_ | ⟨v, a⟩, _ | ⟨w, b⟩⟩ := s <;> cases r <;> (try cases w) <;>
    simp [role, Role.ofRelation, Appl.Site.complementHead, Appl.Site.Affected, Appl.Site.High,
      LittleV.Dynamic]

/-- An argument is an experiencer exactly when its applicative takes a state and no verbal head
embeds the applicative phrase. -/
theorem role_eq_experiencer_iff :
    role s r = .experiencer ↔ s.High ∧ s.complementHead = some .vBE := by
  obtain ⟨_ | ⟨v, a⟩, _ | ⟨w, b⟩⟩ := s <;> cases r <;> (try cases w) <;>
    simp [role, Role.ofRelation, Appl.Site.complementHead, Appl.Site.High, LittleV.Dynamic]

/-- An argument is a causee exactly when its applicative takes a dynamic event and a verbal head
embeds the applicative phrase. -/
theorem role_eq_causee_iff :
    role s r = .causee ↔ s.Affected ∧ ∃ v ∈ s.complementHead, v.Dynamic := by
  obtain ⟨_ | ⟨v, a⟩, _ | ⟨w, b⟩⟩ := s <;> cases r <;> (try cases w) <;>
    simp [role, Role.ofRelation, Appl.Site.complementHead, Appl.Site.Affected, Appl.Site.High,
      LittleV.Dynamic]

-- the leaf of benefactives and instrumentals
theorem role_eq_benefactive_iff :
    role s r = .benefactive ↔ s.High ∧ ∃ v ∈ s.complementHead, v.Dynamic := by
  obtain ⟨_ | ⟨v, a⟩, _ | ⟨w, b⟩⟩ := s <;> cases r <;> (try cases w) <;>
    simp [role, Role.ofRelation, Appl.Site.complementHead, Appl.Site.High, LittleV.Dynamic]

/-! ### The table of the dissertation -/

/-- The meaning of [cuervo-2003]'s table that an interpretation is, the causee having none. -/
def Role.meaning? : Role → Option Cuervo2003.Meaning
  | .recipient => some (.low .recipient)
  | .source => some (.low .source)
  | .possessor => some (.low .possessor)
  | .causee => none
  | .benefactive => some .benefactive
  | .affected => some .affected
  | .experiencer => some .experiencer

/-- The typology refines the table of datives: at every site, the interpretation it gives is
among the meanings of the site's cell of the table, unless it is the causee. -/
theorem role_mem_meanings (h : s.heads ≠ []) :
    ∃ c, Cuervo2003.cell s r = some c ∧ ∀ m ∈ (role s r).meaning?, m ∈ Cuervo2003.meanings c := by
  obtain ⟨_ | ⟨v, a⟩, _ | ⟨w, b⟩⟩ := s
  · simp [Appl.Site.heads] at h
  all_goals (try cases w) <;> cases r <;>
    simp [Cuervo2003.cell, Cuervo2003.row, Cuervo2003.column, Cuervo2003.meanings, role,
      Role.ofRelation, Role.meaning?, Appl.Site.selector, Appl.Site.complementHead,
      Appl.Site.Low, Appl.Site.High, LittleV.Dynamic, List.getLast?_cons]

-- Over a change the table has the experiencer reading beside the benefactive of the typology.
example : role ⟨[], [.vGO]⟩ .possessor = .benefactive ∧
    Cuervo2003.meanings (.high, .vGO) = {.experiencer, .benefactive} := by decide

-- Where a dynamic event is embedded, the typology has the causee and the table its affected
-- column.
example : role ⟨[.vDO], [.vGO]⟩ .possessor = .causee ∧
    Cuervo2003.column ⟨[.vDO], [.vGO]⟩ .possessor = .affected := by decide

end Cuervo2020
