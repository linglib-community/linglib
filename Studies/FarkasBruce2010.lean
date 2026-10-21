module

public import Linglib.Data.Examples.FarkasBruce2010
public import Linglib.Discourse.Commitment.Table
public import Linglib.Discourse.Response
public import Linglib.Discourse.Role
public import Linglib.Fragments.English.Particles
public import Linglib.Fragments.German.Particles
public import Linglib.Fragments.Romance.French.Particles
public import Linglib.Fragments.Romanian.Particles

/-!
# Farkas and Bruce (2010): On Reacting to Assertions and Polar Questions

This file formalizes Farkas and Bruce's account of why reactions to assertions and to polar
questions overlap only in part. The context structure is `Commitment.Table`: the participants'
discourse commitments, the common ground, and the Table, whose items project the common grounds that
would settle them. A default assertion commits its author, places the declarative on the Table and
projects confirmation alone (9); a default polar question places the interrogative on the Table and
projects both resolutions (12). So an assertion leaves the common ground as it was, unlike
Stalnaker's update (`Table.commonGround_assert`, `assert_not_narrowing`); the two moves differ in
whether the author is committed and in whether the projected set is inquisitive
(`projectedSet_assert`, `projectedSet_polarQuestion`), and agree in deciding the sentence radical in
every projected common ground (`Table.mem_of_mem_projectedSet_assert`,
`Table.mem_or_compl_mem_of_mem_projectedSet_polarQuestion`). Confirmation (16) followed by the
common-ground increase `M'` (17) settles an assertion (`shared_assert_confirm`,
`isStable_settle_assert`, `mem_commonGround_settle`); a total denial (22) leaves nothing consistent
projected and the conversation in crisis (21, `Table.inCrisis_assert_assert_compl`), from which
agreeing to disagree (23) recovers with the commitments intact (`not_inCrisis_agreeToDisagree`,
`discourseCommitments_agreeToDisagree`). A reverse answer to a polar question (28) is no crisis
(`not_inCrisis_polarQuestion_assert_compl`), a confirming answer (24) projects the single common
ground with the answer (`projectedSet_polarQuestion_assert`), and the questioner's confirmation of
it settles the question (`isStable_settle_polarQuestion`).

§4.3 and §5 classify responding assertions by two features: the relative polarity [same] or
[reverse] of the response to the sentence radical on the Table (31) and the absolute polarity [+] or
[−] of the asserted sentence. `Sentence` is a radical with its polarity and `Confirming`/`Reversing`
the move types (26) and (29) on sentences; the same [reverse] response is a denial after an
assertion and a reverse answer after a question (`inCrisis_reversing_assert`,
`not_inCrisis_reversing_polarQuestion`). On a shared radical a sentence confirms or reverses another
iff the `Discourse.Response` of their polarities is [same] or [reverse], as (31) defines the
features (`Confirming.iff_relative_eq_positive`, `Reversing.iff_relative_eq_negative`).

§5.2 says what the polarity particles mark, as sets of responses bearing features: the English *yes*
[same] or [+] and *no* [reverse] or [−], their double duty (`english`); the Romanian *da* [+], *nu*
[−] and *ba* [reverse] except in a [reverse, −] answer to a question (`romanian`); and French *si*
and German *doch* the marked combination [reverse, +] (`reversePositive`). Both English particles
can confirm a negative question, while in Romanian only *nu* does
(`english_confirmsNegativeQuestion`, `romanian_confirmsNegativeQuestion_iff`). `rows` are the
responding assertions of (4), (5) and (35)–(50), whose particles are the fragments' polarity
particles; every acceptable response is one its English and Romanian particles mark (`english_mem`,
`romanian_mem`), *si* and *doch* occur in [reverse, +] responses only
(`si_doch_mem_reversePositive`), and *ba* is possible in every denial (`ba_denial`) and required to
be absent from a [reverse, −] answer (`ba_not_reverse_answer_neg`).

## Implementation notes

* The Table records the issue a sentence raises, not its syntactic object, so a negative polar
  question raises the same issue as its positive counterpart (15), `Question.polar_compl`, and
  the relative polarity of a response is computed from the sentences of the exchange rather
  than read off the Table.
* `M'` is `Table.settle`, which strips the shared proposition from the individual
  commitment lists as (17) prescribes; the projected set is derived from the Table rather than
  stored, as the paper notes it can be.
* Rows record the polarities of the initiating and responding sentences as a
  `Discourse.Response`; since a responding assertion shares its radical with the initiating
  sentence, [same] is agreement of polarity and [reverse] its reversal.
* The paper discusses only *si* of the French particles and only *doch* of the German ones, so
  what they mark is a named set rather than an interpretation of the whole fragment.

## TODO

* (5) accepts a bare *nu* denial of a positive assertion that (42) stars, so §5.2's claim that
  *ba* is required in a [reverse, −] denial is left as the weaker `ba_denial`.

## References

* [farkas-bruce-2010]
* [stalnaker-1978]
-/

@[expose] public section

namespace FarkasBruce2010

open Commitment
open Filter

variable {W : Type*} (K : Table Discourse.Role W) (p : Set W)

/-- In a total denial (22) the speaker asserts `p` and the addressee asserts its negation. -/
abbrev denial : Table Discourse.Role W := (K.assert .speaker p).assert .addressee pᶜ

/-! ### Default assertions and default polar questions -/

/-- A world can survive the assertion of `p` without satisfying `p`, since only the projected set
moves; `Commitment.Table` is not a `HasAssertion` instance under its own `assert`. -/
theorem assert_not_narrowing :
    ∃ (K : Table Discourse.Role Bool) (p : Set Bool) (w : Bool),
      w ∈ HasCommonGround.contextSet (K.assert .speaker p) ∧ w ∉ p :=
  ⟨.empty, {true}, false, by simp [HasCommonGround.contextSet], Bool.false_ne_true⟩

/-- From a stable context an assertion projects the single common ground with `p`, a
categorical bias towards confirmation (8). -/
theorem projectedSet_assert (a : Discourse.Role) (hK : K.IsStable) (hp : K.commonGround ⊓ 𝓟 p ≠ ⊥) :
    (K.assert a p).projectedSet = {K.commonGround ⊓ 𝓟 p} := by
  rw [Table.projectedSet_assert, Table.projectedSet_of_isStable hK,
    Table.project_singleton_ofSet hp]

/-- From a stable context a polar question projects both resolutions, an inquisitive context
(11). -/
theorem projectedSet_polarQuestion (hK : K.IsStable) (hp : K.commonGround ⊓ 𝓟 p ≠ ⊥)
    (hnp : K.commonGround ⊓ 𝓟 pᶜ ≠ ⊥) :
    (K.polarQuestion p).projectedSet = {K.commonGround ⊓ 𝓟 p, K.commonGround ⊓ 𝓟 pᶜ} := by
  rw [Table.projectedSet_polarQuestion, Table.projectedSet_of_isStable hK,
    Table.project_singleton_polar hp hnp]

/-! ### Confirmation, denial, and agreeing to disagree -/

/-- After the addressee confirms (16), the asserted proposition is on every commitment
list. -/
theorem shared_assert_confirm : ((K.assert .speaker p).commit .addressee p).Shared p := by
  intro a
  cases a
  · rw [Table.discourseCommitments_commit_of_ne (by decide)]
    exact Table.mem_discourseCommitments_assert _ _ _
  · exact Table.mem_discourseCommitments_commit_self _ _ _ _ _

/-- The shared proposition enters the common ground (17). -/
theorem mem_commonGround_settle :
    p ∈ (K.settle p).commonGround := mem_inf_of_right (mem_principal_self p)

/-- The settled assertion is popped (17), and from a stable context the Table is empty
again. -/
theorem isStable_settle_assert (hK : K.IsStable) :
    (((K.assert .speaker p).commit .addressee p).settle p).IsStable := by
  rw [Table.settle_commit_self, Table.settle_assert_self]
  exact Table.isStable_settle_of_isStable p hK

/-- Agreeing to disagree (23) removes the contradictory pair from the Table, and with a
consistent common ground the crisis is over. -/
theorem not_inCrisis_agreeToDisagree (hK : K.IsStable) (hcg : K.commonGround ≠ ⊥) :
    ¬ (denial K p).agreeToDisagree.InCrisis := by
  rw [Table.inCrisis_agreeToDisagree_assert_assert, Table.inCrisis_iff,
    Table.projectedSet_of_isStable hK]
  exact fun h ↦ hcg (h _ rfl)

/-- After agreeing to disagree (23) each participant stays committed to what they asserted. -/
theorem discourseCommitments_agreeToDisagree :
    p ∈ (denial K p).agreeToDisagree.discourseCommitments .speaker ∧
      pᶜ ∈ (denial K p).agreeToDisagree.discourseCommitments .addressee := by
  rw [Table.discourseCommitments_agreeToDisagree,
    Table.discourseCommitments_assert_of_ne (by decide)]
  exact ⟨Table.mem_discourseCommitments_assert _ _ _, Table.mem_discourseCommitments_assert _ _ _⟩

/-! ### Reacting to a polar question -/

/-- A resolving answer to a polar question projects the single common ground with the answer,
the projected resolution inconsistent with it being discarded. -/
theorem projectedSet_polarQuestion_assert (hK : K.IsStable) (b : Discourse.Role) {q : Set W}
    (hq : q ∈ ({p, pᶜ} : Set (Set W))) (hc : K.commonGround ⊓ 𝓟 q ≠ ⊥) :
    ((K.polarQuestion p).assert b q).projectedSet = {K.commonGround ⊓ 𝓟 q} := by
  rw [Table.projectedSet_assert, Table.projectedSet_polarQuestion,
    Table.projectedSet_of_isStable hK]
  ext f
  simp only [Table.mem_project, Question.alt_ofSet, Set.mem_singleton_iff, exists_eq_left]
  constructor
  · rintro ⟨⟨_, ⟨⟨r, hr, rfl⟩, -⟩, rfl⟩, hf⟩
    rcases (Question.alt_polar_iff p r).1 hr with ⟨-, rfl⟩ | ⟨-, -, rfl | rfl⟩
    · rw [principal_univ, inf_top_eq]
    · rcases hq with rfl | rfl
      · rw [inf_assoc, inf_idem]
      · exact absurd (by simp [inf_assoc, inf_principal]) hf
    · rcases hq with rfl | rfl
      · exact absurd (by simp [inf_assoc, inf_principal]) hf
      · rw [inf_assoc, inf_idem]
  · rintro rfl
    refine ⟨⟨K.commonGround ⊓ 𝓟 q, ⟨⟨q, ?_, rfl⟩, hc⟩, by rw [inf_assoc, inf_idem]⟩, hc⟩
    rcases hq with rfl | rfl
    · by_cases hu : q = Set.univ
      · exact (Question.alt_polar_iff _ _).2 (Or.inl ⟨Or.inr hu, hu⟩)
      · exact (Question.alt_polar_iff _ _).2
          (Or.inr ⟨fun e ↦ hc (by simp [e]), hu, Or.inl rfl⟩)
    · by_cases he : p = ∅
      · exact (Question.alt_polar_iff _ _).2 (Or.inl ⟨Or.inl he, by simp [he]⟩)
      · exact (Question.alt_polar_iff _ _).2
          (Or.inr ⟨he, fun e ↦ hc (by simp [e]), Or.inr rfl⟩)

/-- A reverse answer (27) is no crisis, since the question projected both resolutions. -/
theorem not_inCrisis_polarQuestion_assert_compl (hK : K.IsStable) (b : Discourse.Role)
    (hnp : K.commonGround ⊓ 𝓟 pᶜ ≠ ⊥) : ¬ ((K.polarQuestion p).assert b pᶜ).InCrisis := by
  rw [Table.inCrisis_iff, projectedSet_polarQuestion_assert K p hK b (Or.inr rfl) hnp]
  exact fun h ↦ hnp (h _ rfl)

/-- The questioner's confirmation (16) of an answer (24) settles the question. -/
theorem isStable_settle_polarQuestion (hK : K.IsStable) :
    ((((K.polarQuestion p).assert .addressee p).commit .speaker p).settle p).IsStable := by
  rw [Table.settle_commit_self, Table.settle_assert_self,
    Table.settle_polarQuestion_self]
  exact Table.isStable_settle_of_isStable p hK

/-! ### Responding assertions and polarity features -/

open Discourse

/-- A sentence radical with its polarity, `S` or `¬S`. -/
structure Sentence (W : Type*) where
  radical : Set W
  polarity : Polarity

/-- The proposition a sentence denotes is its polarity acting on its radical. -/
def Sentence.prop (s : Sentence W) : Set W := s.polarity • s.radical

/-- A response confirms (26) when it commits to the proposition of the sentence on the Table. -/
def Confirming (s t : Sentence W) : Prop := t.prop = s.prop

/-- A response reverses (29) when it commits to the complement of that proposition. -/
def Reversing (s t : Sentence W) : Prop := t.prop = s.propᶜ

/-- With a shared radical, a response to either move reverses iff it is [reverse] (31). -/
theorem Reversing.iff_relative_eq_negative [Nonempty W] {s t : Sentence W}
    (h : t.radical = s.radical) (m : InitiatingMove) :
    Reversing s t ↔ (⟨m, s.polarity, t.polarity⟩ : Response).relative = .negative := by
  rw [Reversing, Sentence.prop, Sentence.prop, h]
  exact Response.polarity_smul_eq_compl_iff (x := ⟨m, s.polarity, t.polarity⟩) _

/-- With a shared radical, a response to either move confirms iff it is [same] (31). -/
theorem Confirming.iff_relative_eq_positive [Nonempty W] {s t : Sentence W}
    (h : t.radical = s.radical) (m : InitiatingMove) :
    Confirming s t ↔ (⟨m, s.polarity, t.polarity⟩ : Response).relative = .positive := by
  rw [Confirming, Sentence.prop, Sentence.prop, h]
  exact Response.polarity_smul_eq_iff (x := ⟨m, s.polarity, t.polarity⟩) _

/-- A [reverse] response to an assertion is a denial, which puts the conversation in crisis. -/
theorem inCrisis_reversing_assert {s t : Sentence W} (h : Reversing s t) (a b : Discourse.Role) :
    ((K.assert a s.prop).assert b t.prop).InCrisis := by
  rw [h]
  exact K.inCrisis_assert_assert_compl a s.prop b

/-- The same [reverse] response to the polar question is a reverse answer, which is no crisis. -/
theorem not_inCrisis_reversing_polarQuestion {s t : Sentence W} (h : Reversing s t)
    (hK : K.IsStable) (b : Discourse.Role) (hc : K.commonGround ⊓ 𝓟 s.propᶜ ≠ ⊥) :
    ¬ ((K.polarQuestion s.prop).assert b t.prop).InCrisis := by
  rw [h]
  exact not_inCrisis_polarQuestion_assert_compl K s.prop hK b hc

/-! ### Polarity particles -/

/-- The English *yes* marks [same] or [+], and *no* marks [reverse] or [−] (§5.2). -/
def english : English.PolarityParticle → Set Response
  | .yes => {x | x.HasFeature (.relative .positive) ∨ x.HasFeature (.absolute .positive)}
  | .no => {x | x.HasFeature (.relative .negative) ∨ x.HasFeature (.absolute .negative)}

/-- The Romanian *da* marks [+], *nu* [−], and *ba* [reverse], except in a [reverse, −] answer to
a question, where *ba* is impossible (43) (§5.2). -/
def romanian : Romanian.PolarityParticle → Set Response
  | .da => {x | x.HasFeature (.absolute .positive)}
  | .nu => {x | x.HasFeature (.absolute .negative)}
  | .ba => {x | x.HasFeature (.relative .negative) ∧
      ¬ (x.reactsTo = .polarQuestion ∧ x.HasFeature (.absolute .negative))}

/-- [reverse, +], the combination French *si* and German *doch* mark (46)–(49). -/
def reversePositive : Set Response :=
  {x | x.HasFeature (.relative .negative) ∧ x.HasFeature (.absolute .positive)}

instance (p : English.PolarityParticle) : DecidablePred (· ∈ english p) := fun _ ↦ by
  cases p <;> exact inferInstanceAs (Decidable (_ ∨ _))

instance (p : Romanian.PolarityParticle) : DecidablePred (· ∈ romanian p) := fun x ↦ by
  cases p
  · exact inferInstanceAs (Decidable (x.HasFeature (.absolute .positive)))
  · exact inferInstanceAs (Decidable (x.HasFeature (.absolute .negative)))
  · exact inferInstanceAs (Decidable (_ ∧ _))

instance : DecidablePred (· ∈ reversePositive) := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- Both English particles confirm a negative, *no* as [−], *Is Sam not home?* — *No, he
isn't* (35), and *yes* as [same], *Sam is not home.* — *Yes. He is not.* (38). -/
theorem english_confirmsNegativeQuestion (p : English.PolarityParticle) :
    Response.ConfirmsNegativeQuestion (english p) := by
  cases p <;> decide

/-- Of the Romanian particles only the absolute *nu* confirms a negative; *da* marks [+] and
*ba* [reverse]. -/
theorem romanian_confirmsNegativeQuestion_iff (p : Romanian.PolarityParticle) :
    Response.ConfirmsNegativeQuestion (romanian p) ↔ p = .nu := by
  cases p <;> decide

/-! ### The examples -/

/-- The polarity particles of the paper's examples, from the fragments of the four languages. -/
inductive Particle
  | en (p : English.PolarityParticle)
  | ro (p : Romanian.PolarityParticle)
  | fr (p : French.PolarityParticle)
  | de (p : German.PolarityParticle)
  deriving DecidableEq, Repr

/-- A responding assertion of the paper's examples, with its response, its particles, and its
judgment. -/
structure Row where
  response : Response
  particles : List Particle
  judgment : Judgment
  deriving DecidableEq, Repr

def moveTable : List (String × InitiatingMove) :=
  [("assertion", .assertion), ("question", .polarQuestion)]

def polarityTable : List (String × Polarity) := [("positive", .positive), ("negative", .negative)]

/-- The particles of each language, by Glottocode and spelling. -/
def particleTable : List (String × List (String × Particle)) :=
  [("stan1293", [English.PolarityParticle.yes, .no].map fun p ↦ (p.form, .en p)),
    ("roma1327", [Romanian.PolarityParticle.da, .nu, .ba].map fun p ↦ (p.form, .ro p)),
    ("stan1290", [French.PolarityParticle.oui, .non, .si].map fun p ↦ (p.form, .fr p)),
    ("stan1295", [German.PolarityParticle.ja, .nein, .doch].map fun p ↦ (p.form, .de p))]

def Row.ofDatum (ex : Datum) : Option Row := do
  let table ← List.lookup ex.language particleTable
  let reactsTo ← ex.parse? "reaction" moveTable
  let antecedent ← ex.parse? "input" polarityTable
  let polarity ← ex.parse? "response" polarityTable
  let particle ← ex.parse? "particle" table
  let particles := particle :: (ex.parse? "particle2" table).toList
  pure ⟨⟨reactsTo, antecedent, polarity⟩, particles, ex.judgment⟩

theorem row_ofDatum_isSome : ∀ ex ∈ Examples.all, (Row.ofDatum ex).isSome := by decide

def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- Every acceptable response is one its English particles mark. -/
theorem english_mem : ∀ r ∈ rows, r.judgment = .acceptable →
    ∀ p : English.PolarityParticle, .en p ∈ r.particles → r.response ∈ english p := by
  decide

/-- Every acceptable response is one its Romanian particles mark. -/
theorem romanian_mem : ∀ r ∈ rows, r.judgment = .acceptable →
    ∀ p : Romanian.PolarityParticle, .ro p ∈ r.particles → r.response ∈ romanian p := by
  decide

/-- *ba* is possible in every denial. -/
theorem ba_denial : ∀ r ∈ rows, r.response.reactsTo = .assertion →
    r.response.relative = .negative → .ro .ba ∈ r.particles → r.judgment = .acceptable := by
  decide

/-- In a Romanian [reverse, −] answer to a question, *ba* is impossible and its absence
acceptable. -/
theorem ba_not_reverse_answer_neg : ∀ r ∈ rows, (∃ p, .ro p ∈ r.particles) →
    r.response.reactsTo = .polarQuestion → r.response.relative = .negative →
    r.response.polarity = .negative → (r.judgment = .acceptable ↔ .ro .ba ∉ r.particles) := by
  decide

/-- French *si* and German *doch* mark the combination [reverse, +], after assertions and
questions alike. -/
theorem si_doch_mem_reversePositive : ∀ r ∈ rows, .fr .si ∈ r.particles ∨ .de .doch ∈ r.particles →
    r.response ∈ reversePositive ∧ r.judgment = .acceptable := by
  decide

end FarkasBruce2010
