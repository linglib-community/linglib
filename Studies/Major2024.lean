module

public import Linglib.Data.Examples.Major2024
public import Linglib.Fragments.Uyghur.Complementizers
public import Linglib.Fragments.Washo.Clause
public import Linglib.Semantics.Presupposition.Verb
public import Studies.BakerVinokurova2010
public import Linglib.Syntax.Minimalist.Category.ExtendedProjection

/-!
# Major (2024): Re-analyzing 'say' complementation: Implications for case theory and beyond

Uyghur *dep* follows a finite clause where English has *that*, and Major argues that it is what
its morphology shows, the converb in *-(I)p* of the verb *de-* 'say'. A *dep* clause then has the
outside of a converb clause and the inside of a clause of saying. Outside, it adjoins to the
matrix VP or TP and is never an argument: no verb takes it, it is no subject, a factive verb does
not presuppose it, and the diagnostics of the two heights sort it as they sort any converb clause.
Bochnak and Hanink's modifier clauses of Washo are the same kind of clause. Inside, *de-* keeps
its obligatory complement, and its `v` values the subject of that complement accusative as the
`v` of a transitive verb values an object.

The accusative subject bears on case theory. Baker and Vinokurova take Sakha *dien*, the same
converb of 'say', for a complementizer, so that an accusative subject beside an unaccusative
matrix verb has no `v` above it and calls for a dependent case rule. With 'say' in the clause
there is a `v`, and the dependent rule and Agree then value the same cases, while with a
complementizer each goes wrong on the Uyghur examples.

## Implementation notes

* The feature `[+ACC/SPEC]` of `v` is one Boolean, which makes `v` a probe and shifts its goal
  to the edge of the verb phrase. Case is assigned by Baker and Vinokurova's two grammars, theirs
  with the dependent accusative and the one with Agree alone.
* A *dep* clause is its own domain of case, the subject of 'say' above the subject of its
  complement; the complementizer analysis instead puts the raised subject among the matrix NPs.
* The voice of 'say' follows a row's `sayer`: an agent's saying is an activity, and a saying
  whose source is inanimate or missing is a state with no external argument.
* A row's `height` is the paper's classification of its converb clause, and a diagnostic is
  read as scope under a matrix head, negation for a negative concord item and `v` for the
  pro-form of a manner.

## TODO

* Raising against prolepsis, by default agreement on the embedded verb, and the complementary
  distribution of accusative subjects and indexical shift.
* The nominative of a subject promoted out of a *dep* clause under a passive matrix verb.

## References

* [major-2024]
* [baker-vinokurova-2010]
* [bochnak-hanink-2021]
-/

@[expose] public section

namespace Major2024

open Minimalist BakerVinokurova2010 Uyghur

/-- `verb? key r` is the fragment entry that the feature `key` of the row `r` names. -/
def verb? (key : String) (r : Datum) : Option Verb := (r.feature? key).bind (Verb.find? verbs ·)

/-- The linker of a row's embedded clause is the converb suffix on a *dep* clause, as on any
converb clause, and *-lik* on a participial one. -/
def linker? (r : Datum) : Option Complementizer :=
  r.parse? "clause" [("dep", ip), ("converb", ip), ("participial", lik)]

/-! ### 'Say' inside the converb clause -/

/-- A verb is acceptable with or without a complement exactly when it has a frame for it,
whether it is finite or under the converb suffix: *de-* needs its complement in a *dep* clause as
*oyla-* 'think' does in its converb clause, and *warqira-* 'scream' takes none. -/
theorem subcategorization :
    ∀ r ∈ Examples.all, ∀ fr ∈ r.parse? "complement"
        [("none", ArgumentFrame.intransitive), ("dp", .np), ("participial", .typedBy lik)],
      ∃ v ∈ verb? "verb" r, (r.judgment = .acceptable ↔ ∃ g ∈ v.valency.frames, fr ≤ g) := by
  decide

/-! ### No argument -/

/-- No verb takes a converb clause. -/
theorem not_takes_ip (v : Verb) : ¬ v.Takes ip := Verb.not_takes_of_blank rfl rfl

theorem dep_unselected :
    ∃ r ∈ Examples.all, r.judgment = .acceptable ∧ r.feature? "clause" = some "dep" ∧
      ∃ v ∈ verb? "matrixVerb" r, ¬ v.TakesClausal := by
  decide

theorem clausal_subject :
    ∀ r ∈ Examples.all, r.feature? "diagnostic" = some "subject" → ∃ z ∈ linker? r,
      (r.judgment = .acceptable ↔ ∃ p : ArgumentFrame.Position, p.Takes z) := by
  simp only [ArgumentFrame.Position.exists_takes_iff]
  decide

/-- Denying the content of a clause is contradictory exactly when a factive verb takes the
clause: under *bil-* 'know' a participial clause is presupposed and a *dep* clause is not. -/
theorem factive_denial :
    ∀ r ∈ Examples.all, r.feature? "diagnostic" = some "denial" →
      ∃ v ∈ verb? "matrixVerb" r, ∃ z ∈ linker? r,
        (r.judgment = .acceptable ↔ ¬ (v.IsFactive ∧ v.Takes z)) := by
  decide

theorem forget_that :
    ∀ r ∈ Examples.all, ∀ j ∈ r.readings.lookup "forgot that",
      ∃ v ∈ verb? "matrixVerb" r, ∃ z ∈ linker? r, (j = .acceptable ↔ v.Takes z) := by
  decide

theorem washo_parallel :
    (∀ v : Verb, ¬ v.Takes Washo.aq) ∧
      (∃ p : ArgumentFrame.Position, p.Takes Washo.ge) ∧
      ∃ p : ArgumentFrame.Position, p.Takes lik := by
  refine ⟨fun _ ↦ Verb.not_takes_of_blank rfl rfl, ?_, ?_⟩ <;>
    exact ArgumentFrame.Position.exists_takes_iff.2 (by decide)

/-! ### Two heights -/

theorem adjoined_below :
    ∀ h ∈ [Cat.v, .Asp, .Neg, .T], Cat.V.fValue < h.fValue ∧ ¬ Cat.T.fValue < h.fValue := by
  decide

theorem height_diagnostics :
    ∀ r ∈ Examples.all, ∀ s ∈ r.parse? "height" [("VP", Cat.V), ("TP", .T)],
      ∃ h ∈ r.parse? "diagnostic" [("nci", Cat.Neg), ("proform", .v)],
        (r.judgment = .acceptable ↔ s.fValue < h.fValue) := by
  decide

/-! ### Accusative from `v` -/

/-- The verb phrase has `v` as a probe when `v` bears `[+ACC/SPEC]`. -/
def vProbe (active : Bool) : List (Cat × Cat) := if active then [(.v, .v)] else []

/-- `vP g tensed active` is the cases `g` gives a subject and the NP below `v`, which
`[+ACC/SPEC]` attracts to the edge of the verb phrase, under finite T or, as in a converb clause,
under none. -/
def vP (g : CaseAssigners) (tensed active : Bool) : List (Option Case) :=
  cases g ((if tensed then finite else []) ++ vProbe active) [subject, internal active]

theorem vP_eq (tensed active : Bool) : ∀ g ∈ [grammar, pureChomsky],
    vP g tensed active =
      [if tensed then some .nom else none, if active then some .acc else none] := by
  cases tensed <;> cases active <;> decide

theorem shifted_without_v :
    cases grammar finite [subject, internal true] = [some .nom, some .acc] ∧
      cases pureChomsky finite [subject, internal true] = [some .nom, none] := by
  decide

/-- `case? r` is the case the gloss of the row `r` shows on the NP at issue. -/
def case? (r : Datum) : Option (Option Case) :=
  r.parse? "case" [("ACC", some .acc), ("GEN", some .gen), ("bare", none)]

/-- The voice of the verb whose `v` is above the NP at issue is the verb's own above an object,
and above the subject of the complement of *de-* it is the voice of an agent's saying or of the
state of a source that is no agent. -/
def voice? (r : Datum) : Option VoiceType :=
  (r.parse? "sayer"
    [("animate", .agentive), ("inanimate", .nonThematic), ("none", .nonThematic)]).orElse
    fun _ ↦ (verb? "verb" r).bind (·.voiceType)

/-- An object, or the subject of the complement of *de-*, is acceptable in a case exactly when
some setting of `[+ACC/SPEC]` gives it that case, the feature being borne only by a θ-assigning
`v` and shown by the NP's place before an adverb: so a predicate nominal under *bol-* 'become'
and the subject below a saying with no agent stay bare, under either modality. -/
theorem case_below_v :
    ∀ g ∈ [grammar, pureChomsky], ∀ r ∈ Examples.all, ∀ c ∈ case? r,
      r.feature? "clause" ≠ some "participial" → ∃ vt ∈ voice? r,
        (r.judgment = .acceptable ↔ ∃ active : Bool, (active = true → vt.AssignsTheta) ∧
          (∀ b ∈ r.parse? "objectPosition" [("beforeAdverb", true), ("afterAdverb", false)],
            active = b) ∧
          (vP g (r.feature? "clause" != some "dep") active)[1]? = some c) := by
  decide

theorem participial_subject_genitive :
    ∀ g ∈ [grammar, pureChomsky], ∀ r ∈ Examples.all, ∀ c ∈ case? r,
      r.feature? "clause" = some "participial" →
        (r.judgment = .acceptable ↔ cases g [(.D, .D)] [possessor] = [c]) := by
  decide

/-! ### Were *dep* a complementizer -/

/-- If *dep* is a complementizer, the subject of its clause raises to the clause edge and so
into the matrix clause, below a matrix subject or implied agent and an accusative matrix object,
where finite T probes and the `v` of an active θ-assigning verb; these are the cases the row then
has. -/
def complementizerCases (g : CaseAssigners) (r : Datum) : List (Option Case) :=
  cases g
    (finite ++ vProbe (decide (r.feature? "matrixVoice" ≠ some "passive" ∧
      ∃ v ∈ verb? "matrixVerb" r, ∃ vt ∈ v.voiceType, vt.AssignsTheta)))
    ((if r.feature? "matrixSubject" ≠ some "none" ∨ r.feature? "impliedAgent" = some "yes"
      then [subject] else []) ++
      (if r.feature? "matrixObject" = some "ACC" then [internal true] else []) ++ [internal true])

/-- With a complementizer and Agree alone the raised subject is caseless where the examples have
it accusative: beside unaccusative *ket-* 'leave', beside a passive, and beside *éyt-* 'tell',
whose one `v` has an object of its own. By `pureChomsky_v_of_acc` nothing but a `v` could value
it, which is the argument for the dependent rule that the verb inside *dep* answers. -/
theorem complementizer_agree :
    ∀ r ∈ [Examples.ex_123, Examples.ex_122, Examples.ex_124],
      r.judgment = .acceptable ∧ case? r = some (some .acc) ∧
        (complementizerCases pureChomsky r).getLast? = some none := by
  decide

/-- With a complementizer the dependent rule values the raised subject accusative wherever the
matrix clause has an argument: so beside the inanimate subject 'this news', where the accusative
is out, and not when the news is a locative whose source is inside a relative clause, where the
accusative is in. -/
theorem complementizer_dependent :
    Examples.ex_128_acc.judgment = .ungrammatical ∧
      (complementizerCases grammar Examples.ex_128_acc).getLast? = some (some .acc) ∧
    Examples.ex_129.judgment = .acceptable ∧ case? Examples.ex_129 = some (some .acc) ∧
      (complementizerCases grammar Examples.ex_129).getLast? = some (some .nom) := by
  decide

end Major2024
