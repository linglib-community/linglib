module

public import Linglib.Semantics.Reference.Iota
public import Linglib.Semantics.Modification.Basic
public import Linglib.Semantics.ConventionalImplicature
public import Linglib.Data.Examples.AhnKocabDavidson2026
public import Linglib.Data.Examples.Readers

/-!
# Ahn, Kocab & Davidson 2026: sign language loci as spatial modifiers

Sign language loci — areas of signing space that nominals are pointed to and that verbs
start or end at — are analysed as one spatial modifier `IX_LOC = λo λx. R(x, o)`, an
intersective restriction relating an entity to a location. Nominal uses compose it with a
covert demonstrative (the unique entity associated with the location); verbal uses
incorporate the restricted argument into the verb, replacing agreement. Being a modifier,
a locus is subject to the same *Be brief* competition as any other restriction, so it is
licensed only when reference must be disambiguated.

This file defines `ixLoc`, the demonstrative `that` over `Modifier.intersective`, the
two-dimensional introducing and anaphoric uses, `incorporate`, and a verb's Padden class
read off its selection. `that_isSome_iff` is the uniqueness presupposition; `scenario_help`
derives the interpretation of `AHELPB` from the incorporated points; `paddenClass_of_selection`
recovers the agreeing/spatial/plain trichotomy; the row theorems state the pragmatic
hypothesis over the consultants' judgments.

## TODO

The experiment's ratings in the number, animacy and narrative conditions are results for
`Data/Experiments`; the hypothesis over them, including that the narrative manipulation did not
disambiguate, is not yet stated. The stimuli of Appendix A1 are printed unmarked.

## References

* [ahn-kocab-davidson-2026]
* [potts-2005]
* [kaplan-1989]
* [ariel-2001]
* [grice-1975]
* [aissen-2003]
-/

@[expose] public section

namespace AhnKocabDavidson2026

open ConventionalImplicature (TwoDim)

variable {E L W : Type*}

/-! ### The spatial modifier -/

/-- `⟦IX_LOC⟧ = λo λx. R(x, o)`: pointing at `o` predicates of `x` that it is associated with
`o`, for whatever relation `R` the context supplies. -/
def ixLoc (R : E → L → Prop) (o : L) : E → Prop := λ x => R x o

/-- The demonstrative `⟦that⟧ = λR λP. ιx. P(x) ∧ R(x)`: the unique entity meeting the
spatial and the nominal restriction. -/
noncomputable def that (R P : E → Prop) : Option E := iota (Modifier.intersective R P)

theorem that_isSome_iff (R P : E → Prop) : (that R P).isSome ↔ ∃! x, P x ∧ R x := by
  simp [that, iota_isSome_iff, and_comm]

theorem that_top (R : E → Prop) : that R ⊤ = iota R :=
  congrArg iota (inf_top_eq R)

/-! ### The continuum of relations

Deictic, metonymic, and abstract uses differ only in `R`: the location of the referent, a
location associated with it, or a location arbitrarily assigned to it by introduction. -/

/-- Direct deixis: `x` is currently located at `o`. -/
def locatedAt (at_ : E → L) : E → L → Prop := λ x o => at_ x = o

/-- Arbitrary association by introduction: `x` has been assigned locus `o`. -/
def assigned (assoc : E → Option L) : E → L → Prop := λ x o => assoc x = some o

theorem that_assigned_isSome (assoc : E → Option L) (h : ∀ x y o, assoc x = some o →
    assoc y = some o → x = y) (o : L) :
    (that (ixLoc (assigned assoc) o) ⊤).isSome ↔ ∃ x, assoc x = some o := by
  rw [that_isSome_iff]
  exact ⟨λ ⟨x, hx, _⟩ => ⟨x, hx.2⟩, λ ⟨x, hx⟩ => ⟨x, ⟨trivial, hx⟩, λ y hy => h y x o hy.2 hx⟩⟩

/-! ### Introducing and anaphoric uses -/

/-- The introducing use `SOL IX_a …`: the association is use-conditional, supplementing the
at-issue clause `p`. -/
def introducing (p : W → Prop) (R : W → E → L → Prop) (x : E) (o : L) :
    TwoDim W (W → Prop) :=
  ⟨p, fun w ↦ R w x o⟩

/-- The anaphoric use `∅ IX_a DANCE`: asserts of an entity associated with `o` that it
satisfies `P` and presupposes, use-conditionally, that exactly one entity is. -/
def anaphoric (P : W → E → Prop) (R : W → E → L → Prop) (o : L) : TwoDim W (W → Prop) :=
  ⟨fun w ↦ ∃ x, R w x o ∧ P w x, fun w ↦ ∃! x, R w x o⟩

theorem introducing_neg_notAtIssue (p : W → Prop) (R : W → E → L → Prop) (x : E) (o : L) :
    (introducing p R x o).neg.notAtIssue = fun w ↦ R w x o :=
  rfl

theorem anaphoric_atIssue (P : W → E → Prop) (R : W → E → L → Prop) (o : L) (w : W)
    (h : (anaphoric P R o).notAtIssue w) :
    (anaphoric P R o).atIssue w ↔ ∀ x, R w x o → P w x := by
  obtain ⟨x, hx, hu⟩ := h
  exact ⟨λ ⟨y, hy, hP⟩ z hz => hu z hz ▸ hu y hy ▸ hP, λ hall => ⟨x, hx, hall x hx⟩⟩

/-! ### Incorporation into verbs -/

/-- Locational modification `AVB`: the points restrict the verb's subject and object slots. -/
def incorporate (V : E → E → Prop) (subj obj : E → Prop) : E → E → Prop :=
  λ x y => Modifier.intersective subj (V · y) x ∧ obj y

/-- Locational modification of an intransitive, `V_a`: the point restricts the sole slot. -/
def incorporate₁ (V : E → Prop) (subj : E → Prop) : E → Prop := Modifier.intersective subj V

/-- The scenario Jin at locus A, Sol at locus B. -/
inductive Entity | jin | sol
  deriving DecidableEq

/-- Loci. -/
inductive Locus | a | b
  deriving DecidableEq

/-- Jin was introduced at A and Sol at B. -/
def scenario : Entity → Locus → Prop
  | .jin, .a | .sol, .b => True
  | _, _ => False

instance : DecidableRel scenario := λ x o => by
  cases x <;> cases o <;> simp only [scenario] <;> infer_instance

theorem scenario_help (help : Entity → Entity → Prop) [DecidableRel help] (h : help .jin .sol) :
    incorporate help (ixLoc scenario .a) (ixLoc scenario .b) .jin .sol ∧
      ¬ incorporate help (ixLoc scenario .a) (ixLoc scenario .b) .sol .jin :=
  ⟨⟨⟨trivial, h⟩, trivial⟩, λ ⟨⟨hs, _⟩, _⟩ => hs⟩

/-! ### Selection and Padden's classes -/

/-- What a verb's argument slot selects: a person locus, a location locus, or nothing. -/
inductive Selection | personal | locational | unspecified
  deriving DecidableEq, Repr

/-- A verb's selectional specification for its subject and object slots. -/
structure Verb where
  gloss : String
  subject : Selection
  object : Selection
  deriving Repr

/-- Padden's trichotomy of sign language verbs. -/
inductive PaddenClass | agreeing | spatial | plain
  deriving DecidableEq, Repr

/-- Padden's class, read off selection: a verb selecting a location is spatial, one selecting
persons only is agreeing, one selecting nothing is plain. -/
def Verb.paddenClass (v : Verb) : PaddenClass :=
  if v.subject = .locational ∨ v.object = .locational then .spatial
  else if v.subject = .personal ∨ v.object = .personal then .agreeing
  else .plain

/-- `HELP`, `WALK-TO`, `PUT`, `MOVE`, and `DANCE`. -/
def help : Verb := ⟨"HELP", .personal, .personal⟩
def walkTo : Verb := ⟨"WALK-TO", .personal, .locational⟩
def put : Verb := ⟨"PUT", .personal, .locational⟩
def move : Verb := ⟨"MOVE", .locational, .locational⟩
def dance : Verb := ⟨"DANCE", .unspecified, .unspecified⟩

theorem paddenClass_of_selection :
    help.paddenClass = .agreeing ∧ put.paddenClass = .spatial ∧ move.paddenClass = .spatial ∧
      dance.paddenClass = .plain := by decide

/-! ### The pragmatic hypothesis

Locus use is licensed to disambiguate between potential antecedents. Rows carry `locus`
(whether nouns and verbs are locus-marked), `resolved` (whether context or an overt nominal
already resolves reference), and `condition` (`consultant` for the elicited contrasts, else
the experiment's manipulation). The consultants' judgments are counts of the three signers who
accept a sentence. -/

open Examples

theorem unresolved_without_locus_degraded :
    ∀ row ∈ Examples.all, row.feature? "condition" = some "consultant" →
      row.feature? "locus" = some "false" → row.feature? "resolved" = some "false" →
      row.judgment ≠ .acceptable := by decide

theorem resolved_without_locus_acceptable :
    ∀ row ∈ Examples.all, row.feature? "condition" = some "consultant" →
      row.feature? "locus" = some "false" → row.feature? "resolved" = some "true" →
      row.judgment = .acceptable := by decide

theorem locus_acceptable :
    ∀ row ∈ Examples.all, row.feature? "condition" = some "consultant" →
      row.feature? "locus" = some "true" → row.judgment = .acceptable := by
  decide

end AhnKocabDavidson2026
