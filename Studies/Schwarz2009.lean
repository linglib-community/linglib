module

public import Linglib.Data.Examples.Schwarz2009
public import Linglib.Semantics.Mereology
public import Linglib.Semantics.Reference.Determiner
public import Linglib.Fragments.English.Determiners
public import Linglib.Fragments.Fering.Determiners
public import Linglib.Fragments.German.Determiners

/-!
# Schwarz (2009): Two Types of Definites in Natural Language

Schwarz takes the German contrast between a preposition contracted with the definite article, as in
*zum*, and the full form, as in *zu dem*, for a contrast between two definite articles, as is the
contrast between Fering's A-form and D-form. The weak article presupposes uniqueness in a resource
situation (184a) and the strong article adds an anaphoric index (295). They are
`DefiniteDescription.unique` and `DefiniteDescription.anaphoric`, the strong article being the weak
one over the restrictor narrowed to the antecedent, and English *the* denotes both.

Only the strong article is defined over a restrictor with a satisfier besides the antecedent (§6.1),
and the two agree where the antecedent is the only satisfier (§6.4.1). Both covary under
quantification, the weak article with the situation and the strong article with the assignment
(§2.3). Producer-product bridging, as in (275), is the strong article with its index as the relatum
of a relational noun (309), which has the structure of a possessive and brings back the uniqueness
requirement (pp. 272-273). Part-whole bridging and larger situation uses are the weak article over
the type-shifter Π (260), which picks out only parts of a relatum, so that it fails with *Autor*.
The paper's examples agree with these predictions except where §6.4.1 says they do not: the strong
article is predicted in part-whole bridging, where it is out.

## Main results

* `german_toDescriptions`, `fering_toDescriptions`, `english_toDescriptions`: the descriptions each
  article form denotes.
* `weak_eq_none_strong_eq_some`, `covarying_anaphora`: the contrast of §6.1, and its instance (31).
* `weak_covaries`, `strong_isSome_iff`: the weak article covaries with the situation and the strong
  article does not.
* `relational_isSome_iff`, `relational_anaphora_coauthored`: relational anaphora is defined iff the
  antecedent has exactly one relatum.
* `exists_le_of_shift`, `unique_shift_eq_none`: Π picks out only parts of a relatum.
* `rows_available`, `rows_unavailable`, `rows_strength`: the examples against the analysis.

## Implementation notes

(309) leaves its relatum variable unbound and (310b) swaps the relation's arguments; both are read
as ιx.R(g(1))(x)(s_r). Individuals are situations, as (260) assumes, here sets of atoms. The
Familiarity Condition (290b) enters only the examples' scenarios, as the requirement that an
antecedent bind the strong article's index, since assignments are total.

## TODO

* The bridging questionnaire of §2.2.4.2, and the Fering examples (10), (38) and (57).

## References

* [schwarz-2009]
* [hawkins-1978]
* [heim-1982]
* [ebert-1971]
-/

@[expose] public section

namespace Schwarz2009

open Semantics
open DefiniteDescription (Restrictor)

variable {E W : Type}

/-! ### The forms and their descriptions -/

section Forms

variable (R : Restrictor E W) (d : ℕ)

/-- The German contracted article denotes the weak article and the non-contracted one the strong
article (Table 2.1). -/
theorem german_toDescriptions :
    German.Determiners.contracted.toDescriptions R d = {.unique R} ∧
      German.Determiners.nonContracted.toDescriptions R d = {.anaphoric R d} := by
  have h₁ : German.Determiners.contracted.strengths = {.uniqueness} := by decide
  have h₂ : German.Determiners.nonContracted.strengths = {.familiarity} := by decide
  simp [Article.toDescriptions, h₁, h₂, DefiniteDescription.ofStrength]

/-- Fering's A-form denotes the weak article and its D-form the strong article (9). -/
theorem fering_toDescriptions :
    Fering.Determiners.aForm.toDescriptions R d = {.unique R} ∧
      Fering.Determiners.dForm.toDescriptions R d = {.anaphoric R d} := by
  have h₁ : Fering.Determiners.aForm.strengths = {.uniqueness} := by decide
  have h₂ : Fering.Determiners.dForm.strengths = {.familiarity} := by decide
  simp [Article.toDescriptions, h₁, h₂, DefiniteDescription.ofStrength]

/-- English *the* denotes both articles, having every use of Hawkins's classification
(Table 2.3). -/
theorem english_toDescriptions :
    English.Determiners.the.toDescriptions R d = {.unique R, .anaphoric R d} := by
  have h : English.Determiners.the.strengths = {.uniqueness, .familiarity} := by decide
  simp [Article.toDescriptions, h, DefiniteDescription.ofStrength]

end Forms

/-! ### What the strong article can do that the weak article cannot (§6.1) -/

section Contrast

variable {R : Restrictor E W} {d : ℕ} {g : Assignment E} {s : W}

/-- Over a restrictor with a satisfier besides the antecedent, the weak article fails uniqueness and
the strong article returns the antecedent. -/
theorem weak_eq_none_strong_eq_some {y : E} (hd : R g s (g d)) (hy : R g s y) (hne : y ≠ g d) :
    ⟦DefiniteDescription.unique R⟧ g s = none ∧
      ⟦DefiniteDescription.anaphoric R d⟧ g s = some (g d) :=
  ⟨DefiniteDescription.denote_unique_eq_none_of_ne R g s hd hy hne.symm,
    (DefiniteDescription.denote_anaphoric_eq_some_iff R d g s).2 ⟨hd, rfl⟩⟩

end Contrast

/-- The people at the lectures of (28) and (31) are each lecture's ornithologist and a student. -/
inductive Person where
  | ornithologist (lecture : Fin 2)
  | student

/-- *Mann* 'man' holds at a lecture of its ornithologist and of the student. -/
def man : Restrictor Person (Fin 2) := fun _ l x ↦ x = .ornithologist l ∨ x = .student

/-- The assignment on which the indefinite *ein Ornithologe* binds the index to a lecture's
ornithologist. -/
def boundTo (l : Fin 2) : Assignment Person := fun _ ↦ .ornithologist l

/-- In (31), at every lecture *#vom Mann* fails uniqueness, the student being a man too, and *von
dem Mann* is the ornithologist that the index is bound to. (28) is the case of one lecture. -/
theorem covarying_anaphora (l : Fin 2) :
    ⟦DefiniteDescription.unique man⟧ (boundTo l) l = none ∧
      ⟦DefiniteDescription.anaphoric man 1⟧ (boundTo l) l = some (.ornithologist l) :=
  weak_eq_none_strong_eq_some (y := .student) (.inl rfl) (.inr rfl) nofun

/-! ### Two mechanisms of covariation (§2.3) -/

section Covariation

variable (f : W → E) (d : ℕ) (g : Assignment E) (s : W)

/-- The weak article covaries with the situation. Over a restrictor that holds at each situation of
one entity, as *Gewinner* holds at each round of its winner in (48), it denotes that entity. -/
theorem weak_covaries : ⟦DefiniteDescription.unique fun _ s x ↦ x = f s⟧ g s = some (f s) :=
  iota_ident (f s)

/-- The strong article does not covary with the situation. At a fixed assignment it is defined over
the same restrictor only at the situations whose entity is the antecedent. -/
theorem strong_isSome_iff : (⟦DefiniteDescription.anaphoric (fun _ s x ↦ x = f s) d⟧ g s).isSome ↔
    g d = f s :=
  DefiniteDescription.denote_anaphoric_isSome_iff _ d g s

end Covariation

/-! ### Relational anaphora (§6.2.3) -/

section Relational

variable (R : E → E → W → Prop) (d : ℕ) (g : Assignment E) (s : W)

/-- The relational strong article (309) takes its index `d` as the relatum of the relational noun
`R`, read as `R y x s` for referent `x` of relatum `y` at `s`, and so is the possessive description
whose possessor is the antecedent. -/
def relational : DefiniteDescription E W := .possessive ⊤ (fun g _ ↦ g d) fun _ s y x ↦ R y x s

/-- In relational anaphora the uniqueness requirement resurfaces, the description being defined iff
the antecedent has exactly one relatum. -/
theorem relational_isSome_iff : (⟦relational R d⟧ g s).isSome ↔ ∃! x, R (g d) x s :=
  (DefiniteDescription.denote_possessive_isSome_iff ⊤ (fun g _ ↦ g d) _ g s).trans <| by simp

end Relational

/-! ### Part-whole bridging and larger situation uses (chapter 5) -/

section Shift

open Mereology

variable {S : Type} [PartialOrder S]

/-- The type-shifter Π of (260) makes a property of a relational noun `R`. An individual `x` has it
at `s` when `x` stands in `R` to a whole `y`, evaluated at `y` itself, that overlaps `s`;
individuals are situations, so the whole is one. -/
def shift (R : S → S → S → Prop) : Restrictor S S := fun _ s x ↦ ∃ y, R y x y ∧ Overlap s y

/-- A relational noun is local when it holds at a situation only of parts of the situation, as
*Bürgermeister* evaluated at a town holds of a mayor who is part of the town. -/
def IsLocal (R : S → S → S → Prop) : Prop := ∀ y x s, R y x s → x ≤ s

variable {R : S → S → S → Prop} {g : Assignment S} {s x y : S}

/-- Π of a local relational noun picks out only parts of a whole that overlaps the situation. -/
theorem exists_le_of_shift (hR : IsLocal R) (h : shift R g s x) :
    ∃ y, x ≤ y ∧ R y x y ∧ Overlap s y :=
  let ⟨y, hy, ho⟩ := h
  ⟨y, hR y x y hy, hy, ho⟩

theorem shift_of_le (hy : R y x y) (hys : y ≤ s) (hb : ¬ IsBot y) : shift R g s x :=
  ⟨y, hy, (Overlap.of_le hb hys).symm⟩

/-- The weak article over Π of a local relational noun whose referents are not part of their
relata, as authors are not part of their books, is undefined. -/
theorem unique_shift_eq_none (hR : IsLocal R) (hpart : ∀ y x s, R y x s → ¬ x ≤ y)
    (g : Assignment S) (s : S) : ⟦DefiniteDescription.unique (shift R)⟧ g s = none :=
  (iota_eq_none_iff _).2 fun ⟨x, ⟨y, hy, _⟩, _⟩ ↦ hpart y x y hy (hR y x y hy)

end Shift

/-! ### The scenes of (58), (231) and (275) -/

/-- The atoms of the scenes are a fridge's crisper and the rest of the fridge, a train station and
the town's mayor, two novels, one of them coauthored, and their two authors. -/
inductive Atom where
  | crisper
  | cabinet
  | station
  | mayor
  | novel
  | coauthoredNovel
  | author
  | coauthor
  deriving DecidableEq, Fintype

/-- A situation, an individual among them, is a set of atoms, and parthood is inclusion. -/
abbrev Sit := Finset Atom

/-- The fridge of (58). -/
def fridge : Sit := {.crisper, .cabinet}

/-- The town of (231), with its train station and its mayor. -/
def town : Sit := {.station, .mayor}

/-- *Gemüsefach* 'crisper' holds at a situation of the fridge's crisper. -/
def crisperOf (y x s : Sit) : Prop := y = fridge ∧ x = {.crisper} ∧ x ≤ s

/-- *Bürgermeister* 'mayor' holds at a situation of the town's mayor. -/
def mayorOf (y x s : Sit) : Prop := y = town ∧ x = {.mayor} ∧ x ≤ s

/-- *Autor* 'author' holds at a situation of the author of the novel, and of both authors of the
coauthored novel. -/
def authorOf (y x s : Sit) : Prop :=
  (y = {.novel} ∧ x = {.author} ∨ y = {.coauthoredNovel} ∧ (x = {.author} ∨ x = {.coauthor})) ∧
    x ≤ s

/-- *Roman* 'novel' holds of both novels. -/
def novel : Restrictor Sit Sit := fun _ _ x ↦ x = {.novel} ∨ x = {.coauthoredNovel}

theorem isLocal_authorOf : IsLocal authorOf := fun _ _ _ h ↦ h.2

theorem not_le_of_authorOf {y x s : Sit} (h : authorOf y x s) : ¬ x ≤ y := by
  obtain ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩, -⟩ := h <;> decide

/-- In (58) the fridge is the situation, and *im Gemüsefach* is its crisper. -/
theorem partWhole_bridging (g : Assignment Sit) :
    ⟦DefiniteDescription.unique (shift crisperOf)⟧ g fridge = some {.crisper} :=
  (DefiniteDescription.denote_unique_eq_some_iff _ _ _).2
    ⟨shift_of_le ⟨rfl, rfl, by decide⟩ le_rfl (by simp [fridge]), fun _ ⟨_, ⟨_, h, _⟩, _⟩ ↦ h⟩

/-- In (231) the situation is the train station, and *vom Bürgermeister* is the mayor of its town,
who is not part of the situation. -/
theorem larger_situation (g : Assignment Sit) :
    ⟦DefiniteDescription.unique (shift mayorOf)⟧ g {.station} = some {.mayor} ∧
      ¬ ({.mayor} : Sit) ≤ {.station} :=
  ⟨(DefiniteDescription.denote_unique_eq_some_iff _ _ _).2
    ⟨⟨town, ⟨rfl, rfl, by decide⟩, Mereology.Overlap.of_le (by simp) (by decide)⟩,
      fun _ ⟨_, ⟨_, h, _⟩, _⟩ ↦ h⟩, by decide⟩

/-- In (62) and (275) *#vom Autor* is undefined, authors not being part of their books. -/
theorem author_weak (g : Assignment Sit) (s : Sit) :
    ⟦DefiniteDescription.unique (shift authorOf)⟧ g s = none :=
  unique_shift_eq_none isLocal_authorOf (fun _ _ _ ↦ not_le_of_authorOf) g s

/-- In (275), after *einen Roman*, *von dem Autor* is the novel's author. -/
theorem relational_anaphora :
    ⟦relational authorOf 1⟧ (fun _ ↦ {.novel}) Finset.univ = some {.author} :=
  (DefiniteDescription.denote_possessive_eq_some_iff _ _ _ _ _).2
    ⟨⟨trivial, .inl ⟨rfl, rfl⟩, by decide⟩, fun _ ⟨_, h, _⟩ ↦
      h.elim And.right fun ⟨h, _⟩ ↦ absurd h (by decide)⟩

/-- Antecedent to the coauthored novel, *von dem Autor* fails uniqueness, though *von dem Roman*
picks out the novel. -/
theorem relational_anaphora_coauthored :
    ⟦relational authorOf 1⟧ (fun _ ↦ {.coauthoredNovel}) Finset.univ = none ∧
      ⟦DefiniteDescription.anaphoric novel 1⟧ (fun _ ↦ {.coauthoredNovel}) Finset.univ =
        some {.coauthoredNovel} :=
  ⟨iota_eq_none_of_ne _ (e := {.author}) (e' := {.coauthor})
      ⟨trivial, .inr ⟨rfl, .inl rfl⟩, by decide⟩ ⟨trivial, .inr ⟨rfl, .inr rfl⟩, by decide⟩
      (by decide),
    (DefiniteDescription.denote_anaphoric_eq_some_iff _ _ _ _).2 ⟨.inr rfl, rfl⟩⟩

/-- In (231) the index of *#von dem Bürgermeister* is bound by the train station, which has no
mayor, so the relational strong article is undefined. -/
theorem larger_situation_strong :
    ⟦relational mayorOf 1⟧ (fun _ ↦ {.station}) Finset.univ = none :=
  (iota_eq_none_iff _).2 fun ⟨_, ⟨_, h, _⟩, _⟩ ↦ absurd h (by decide)

/-- The relational strong article is defined in (58) as anaphora to the fridge, where *#in dem
Gemüsefach* is out, so the analysis overgenerates there, as §6.4.1 acknowledges. -/
theorem partWhole_bridging_strong :
    ⟦relational crisperOf 1⟧ (fun _ ↦ fridge) fridge = some {.crisper} :=
  (DefiniteDescription.denote_possessive_eq_some_iff _ _ _ _ _).2
    ⟨⟨trivial, rfl, rfl, by decide⟩, fun _ ⟨_, _, h, _⟩ ↦ h⟩

/-! ### The examples -/

/-- The scenario of an example as the paper describes it. A plain noun's referent is unique in the
resource situation or not and has an antecedent or not; a relational noun's referent is part of its
relatum or not, and the strong article's index is bound to the relatum or to something else. -/
inductive Scenario where
  | plain (unique antecedent : Bool)
  | relational (part toRelatum : Bool)
  deriving DecidableEq

/-- The plain noun of a scenario holds of the referent `0`, and of `1` too unless the referent is
unique. -/
def plainNoun (unique : Bool) : Restrictor (Fin 2) Unit :=
  fun _ _ x ↦ x = 0 ∨ unique = false ∧ x = 1

/-- The relational noun of a scenario is *Bürgermeister* if its referent is part of its relatum and
*Autor* if not. -/
def relationalNoun (part : Bool) : Sit → Sit → Sit → Prop := cond part mayorOf authorOf

/-- The antecedent binding the strong article's index is the relatum, the town or the novel, or else
the train station. -/
def antecedentOf (part toRelatum : Bool) : Sit :=
  cond toRelatum (cond part town {.novel}) {.station}

namespace Scenario

/-- The weak article is available when its description is defined, over a relational noun through
Π at the train station's situation. -/
def WeakAvailable : Scenario → Prop
  | plain u _ => (⟦DefiniteDescription.unique (plainNoun u)⟧ (fun _ ↦ 0) ()).isSome
  | relational p _ =>
      (⟦DefiniteDescription.unique (shift (relationalNoun p))⟧ (fun _ ↦ ∅) {.station}).isSome

/-- The strong article is available when an antecedent makes its index familiar (290b) and its
description is then defined, over a relational noun as relational anaphora (309). -/
def StrongAvailable : Scenario → Prop
  | plain u a => a = true ∧ (⟦DefiniteDescription.anaphoric (plainNoun u) 1⟧ (fun _ ↦ 0) ()).isSome
  | relational p r =>
      (⟦Schwarz2009.relational (relationalNoun p) 1⟧ (fun _ ↦ antecedentOf p r) Finset.univ).isSome

/-- An article strength is available when its article is. -/
def Available (sc : Scenario) : DefiniteDescription.Strength → Prop
  | .uniqueness => sc.WeakAvailable
  | .familiarity => sc.StrongAvailable

/-- The weak article's prediction is that the referent is unique, or part of its relatum. -/
def weak : Scenario → Bool
  | plain u _ => u
  | relational p _ => p

/-- The strong article's prediction is that an antecedent binds its index to the referent, or to
the relatum. -/
def strong : Scenario → Bool
  | plain _ a => a
  | relational _ r => r

/-- The prediction for an article strength. -/
def predicted (sc : Scenario) : DefiniteDescription.Strength → Bool
  | .uniqueness => sc.weak
  | .familiarity => sc.strong

theorem weakAvailable_iff : ∀ sc : Scenario, sc.WeakAvailable ↔ sc.weak = true
  | plain true _ => iff_of_true ((DefiniteDescription.denote_unique_isSome_iff _ _ _).2
      ⟨0, .inl rfl, fun _ h ↦ h.resolve_right fun ⟨h, _⟩ ↦ nomatch h⟩) rfl
  | plain false _ => iff_of_false (by
      show ¬ (⟦DefiniteDescription.unique (plainNoun false)⟧ (fun _ ↦ 0) ()).isSome
      rw [DefiniteDescription.denote_unique_eq_none_of_ne _ _ () (x := 0) (y := 1) (.inl rfl)
        (.inr ⟨rfl, rfl⟩) (by decide)]
      exact Bool.false_ne_true) Bool.false_ne_true
  | relational true _ => iff_of_true (by
      show (⟦DefiniteDescription.unique (shift mayorOf)⟧ (fun _ ↦ ∅) {.station}).isSome
      rw [(larger_situation _).1]; rfl) rfl
  | relational false _ => iff_of_false (by
      show ¬ (⟦DefiniteDescription.unique (shift authorOf)⟧ (fun _ ↦ ∅) {.station}).isSome
      rw [author_weak]; exact Bool.false_ne_true) Bool.false_ne_true

theorem strongAvailable_iff : ∀ sc : Scenario, sc.StrongAvailable ↔ sc.strong = true
  | plain u a => by
    show a = true ∧ (⟦DefiniteDescription.anaphoric (plainNoun u) 1⟧ (fun _ ↦ 0) ()).isSome ↔
      a = true
    rw [DefiniteDescription.denote_anaphoric_isSome_iff]
    exact and_iff_left (.inl rfl)
  | relational p r => by
    have h : ({.station} : Sit) ≠ town := by decide
    simp only [StrongAvailable, relational_isSome_iff, strong]
    cases p <;> cases r <;> simp [relationalNoun, antecedentOf, mayorOf, authorOf, h]

theorem available_iff (sc : Scenario) : ∀ p, sc.Available p ↔ sc.predicted p = true
  | .uniqueness => sc.weakAvailable_iff
  | .familiarity => sc.strongAvailable_iff

end Scenario

/-- The scenario of a row, read from its paper features. -/
def scenario? (d : Datum) : Option Scenario :=
  match d.parse? "relation" [("part", true), ("nonPart", false)] with
  | some p => (d.parse? "antecedent" [("relatum", true), ("other", false)]).map (.relational p)
  | none => do
    let u ← d.parse? "unique" [("yes", true), ("no", false)]
    let a ← d.parse? "antecedent" [("yes", true), ("no", false)]
    some (.plain u a)

/-- The article strength of a row. -/
def article? (d : Datum) : Option DefiniteDescription.Strength :=
  d.parse? "article" [("weak", .uniqueness), ("strong", .familiarity)]

/-- The use of a row in Hawkins's classification. -/
def use? (d : Datum) : Option DefiniteDescription.Use :=
  d.parse? "use" [("anaphoric", .anaphoric),
    ("immediateSituation", .immediateSituation), ("largerSituation", .largerSituation),
    ("partWholeBridging", .bridging .partWhole), ("producerBridging", .bridging .relational)]

/-- Every form the paper accepts is available in its scenario. -/
theorem rows_available : ∀ d ∈ Examples.all, ∀ sc ∈ scenario? d, ∀ p ∈ article? d,
    d.judgment = .acceptable → sc.Available p := by
  simp only [Scenario.available_iff]
  decide

/-- Every form the paper rules out is unavailable in its scenario, except the strong article
anaphoric to the whole in part-whole bridging, the overgeneration that §6.4.1 asks about. -/
theorem rows_unavailable : ∀ d ∈ Examples.all, ∀ sc ∈ scenario? d, ∀ p ∈ article? d,
    d.judgment ≠ .acceptable → sc.Available p → sc = .relational true true ∧ p = .familiarity := by
  simp only [Scenario.available_iff]
  decide

/-- Every form the paper accepts has the strength its use calls for (§2.3). -/
theorem rows_strength : ∀ d ∈ Examples.all, ∀ u ∈ use? d, ∀ p ∈ article? d,
    d.judgment = .acceptable → u.strength = p := by
  decide

end Schwarz2009
