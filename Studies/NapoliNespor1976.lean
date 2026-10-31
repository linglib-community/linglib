module

public import Linglib.Data.Examples.NapoliNespor1976
public import Linglib.Discourse.SpeechAct
public import Linglib.Fragments.Romance.Italian.PolarityItems
public import Linglib.Semantics.Mood.Defs
public import Linglib.Semantics.Polarity.Basic
public import Linglib.Data.Examples.Readers

/-!
# Napoli and Nespor (1976)

Italian comparatives admit a *non* that leaves their truth conditions alone, *Maria è più
intelligente di quanto non sia Carlo* 'Maria is more intelligent than Carlo is'. Napoli and Nespor
call it *non₂* and argue that it is a real negation. It is used when the speaker infers, without
being told, that the comparison contradicts a belief someone holds, and it negates the complement
of an abstract clause, roughly 'I expect that', that is never pronounced. The abstract clause
selects the subjunctive, gives the complementizer *che* a place, keeps the compared predicate far
enough from its antecedent to be the clitic *lo*, licenses negative polarity items and controls a
gerund whose subject is the speaker; an optional rule deletes *non₂* and leaves the rest. A
sentence is derived from the plain structure or from the abstract one, and its judgment is that of
its best derivation in its context.

## Main definitions

* `NapoliNespor1976.Sentence`: what a row records of an example.
* `NapoliNespor1976.Sentence.grade`: how each structure derives a sentence.
* `NapoliNespor1976.Sentence.Felicitous`: what each structure demands of the context.
* `NapoliNespor1976.Sentence.verdict`: the grade of the best derivation in a context.

## Implementation notes

* The analysis allows a set of judgments rather than one, since an optional rule and a variety of
  speakers the paper has not found grade the examples it prints with `(?)`, `?(?)` and `?*`. A row
  records the first mark printed; the paper's `?*` and `*?` are recorded as `??`.
* In (10) the paper reads the belief of a clausal comparative, *di quanto è Carlo*, as the
  listener's, and its rows record the listener as the holder.
* An indirect question raises its proposition without asserting it, so a negated matrix, *Non sono
  sicura se* (89), does not make the speaker agree with the belief.

## References

* [napoli-nespor-1976]
* [seuren-1969]
* [antinucci-puglielli-1971]

## TODO

The reduced comparatives (83)–(85), the positions of gerunds (40)–(43), the indirect questions
(88) and (90), and *pur* and *neanche* outside comparatives (46)–(51) are not rows.
-/

@[expose] public section

namespace NapoliNespor1976

open Discourse.SpeechAct (Force)

/-! ### What a row records -/

/-- How the speaker knows the belief that the comparison bears on. -/
inductive Evidence where
  /-- The listener has revealed nothing (6). -/
  | none
  /-- The speaker infers the belief from what the listener said (7), (9). -/
  | inferred
  /-- The listener stated the belief (8), (30). -/
  | explicit
  deriving DecidableEq, Repr, Fintype

/-- Whose belief the comparison bears on. -/
inductive Holder where
  /-- The listener, now. -/
  | addressee
  /-- The listener at an earlier time, *di quanto tu credevi* (13). -/
  | formerAddressee
  /-- Someone else, *di quanto lui crede* (14). -/
  | thirdParty
  deriving DecidableEq, Repr

/-- The constructions of the rows. -/
inductive Construction where
  /-- A comparative of inequality, *più* or *meno* … *di quanto*. -/
  | inequality
  /-- A comparative of equality, *tanto* … *quanto*. -/
  | equality
  /-- An indirect question (§4). -/
  | indirectQuestion
  deriving DecidableEq, Repr

/-- The standard of a comparison is a clause, *di quanto è Carlo* (4), or a belief, *di quanto tu
credi* (5). -/
inductive Standard where
  | clausal
  | belief
  deriving DecidableEq, Repr

/-- A printed *non* in the embedded clause is either ordinary negation, *non₁* (16), or *non₂*
(17). -/
inductive Negation where
  | none
  | non₁
  | non₂
  deriving DecidableEq, Repr

/-- The complementizer of the embedded clause. -/
inductive Complementizer where
  /-- *(di) quanto*, the comparative quantifier in complementizer position. -/
  | quanto
  | che
  /-- *se* 'if', of an indirect question. -/
  | se
  deriving DecidableEq, Repr

/-- The predicate of a comparative clause, when it is not deleted. -/
inductive Predicate where
  /-- A predicate adjective, repeated (75) or another one (82). -/
  | adjective
  /-- The clitic *lo* for the predicate adjective (79). -/
  | lo
  deriving DecidableEq, Repr

/-- The words of a sentence the analysis is sensitive to. -/
inductive Element where
  /-- *pur con* 'even with' (48). -/
  | pur
  /-- *neanche* 'not … either' in a conjunct (52). -/
  | neanche
  /-- *affatto* 'at all' (footnote 13). -/
  | affatto
  /-- A degree modifier, *molto* 'much' (32) or *due metri* 'two meters' (33). -/
  | degreeModifier
  /-- *con assoluta certezza* 'with absolute certainty' (34). -/
  | certainty
  /-- A gerund in the embedded clause whose subject is the speaker, *rendendomi conto* (38). -/
  | speakerGerund
  deriving DecidableEq, Repr

namespace Element

/-- An element is a negative polarity item when its fragment entry has a licensor. -/
def IsNPI : Element → Prop
  | pur => Italian.PolarityItems.pur.IsNPI
  | neanche => Italian.PolarityItems.neanche.IsNPI
  | affatto => Italian.PolarityItems.affatto.IsNPI
  | _ => False

instance : DecidablePred IsNPI := fun e ↦ by cases e <;> unfold IsNPI <;> infer_instance

/-- An element demands precise knowledge, of a degree (32), (33) or of the listener's belief (34),
as *affatto* does (footnote 13). -/
def DemandsPrecision : Element → Prop
  | degreeModifier | certainty | affatto => True
  | pur | neanche | speakerGerund => False

instance : DecidablePred DemandsPrecision := fun e ↦ by
  cases e <;> unfold DemandsPrecision <;> infer_instance

theorem pur_isNPI : pur.IsNPI := by decide

theorem neanche_isNPI : neanche.IsNPI := by decide

end Element

/-- A row records of an example the move its matrix makes, whose belief the comparison bears on,
and the form of the embedded clause. -/
structure Sentence where
  force : Force
  matrix : Polarity
  construction : Construction
  /-- The standard of a comparison; an indirect question has none. -/
  standard : Option Standard
  holder : Holder
  negation : Negation
  mood : Mood.Grammatical
  complementizer : Complementizer
  /-- The mood the matrix selects for a plain clause, the subjunctive under *non sono sicura se*
  (89) and the indicative otherwise. -/
  plainMood : Mood.Grammatical
  predicate : Option Predicate
  elements : List Element
  deriving DecidableEq, Repr

/-! ### Derivations -/

/-- In the underlying structures (Figs. 1–4) the embedded clause stands alone, or it is the
negated complement S₃ of an abstract clause S₂, 'I expect that'. -/
inductive Structure where
  | plain
  | abstract
  deriving DecidableEq, Repr, Fintype

/-- A sentence is derived, from worst to best, not at all, felicitously only in another context,
only for speakers whose abstract verb takes the indicative, whom the paper has not found (§3.22),
by the optional rule deleting *non₂* (§3.22), or by the obligatory rules. -/
inductive Grade where
  | out
  | contextual
  | indicative
  | deletion
  | regular
  deriving DecidableEq, Repr, Fintype

instance : LinearOrder Grade := LinearOrder.lift' Grade.ctorIdx (by decide)

/-- The judgments a grade allows. Speakers differ on the optional deletion, unmarked or `?` (60d),
(63); the indicative after *non₂* is `?` or `??` (27), (60b); a sentence infelicitous in its
context is `??` (6) or worse (31). -/
def Grade.judgments : Grade → List Judgment
  | .out => [.ungrammatical]
  | .contextual => [.questionable, .ungrammatical]
  | .indicative => [.marginal, .questionable]
  | .deletion => [.acceptable, .marginal]
  | .regular => [.acceptable]

namespace Sentence

variable (s : Sentence)

/-- The plain structure derives a clause in the mood its matrix selects, introduced by *quanto* or
*se*, whose *non*, if any, is ordinary negation. With no abstract clause there is no second
complementizer to leave *che* (§3.24), the predicate is too close to its antecedent to be the
unstressed *lo* (§3.25), a polarity item has no negation to license it unless the clause is
negated, and a gerund whose subject is the speaker has no clause with that subject to control it
(§3.1). -/
def plainGrade : Grade :=
  if s.negation ≠ .non₂ ∧ s.mood = s.plainMood ∧ s.complementizer ≠ .che ∧
      s.predicate ≠ some .lo ∧ (∀ e ∈ s.elements, e.IsNPI → s.negation = .non₁) ∧
      .speakerGerund ∉ s.elements
  then .regular else .out

/-- The abstract structure negates the clause and puts it in the subjunctive its verb selects;
*non₂* surfaces unless the optional rule deletes it, and with the indicative for speakers whose
abstract verb takes it (§3.22). *Che* is possible, but a predicate needs *quanto* in
complementizer position, which *che* blocks (§3.25). -/
def abstractGrade : Grade :=
  if s.complementizer = .che ∧ s.predicate.isSome then .out
  else match s.negation, s.mood with
    | .non₂, .subjunctive => .regular
    | .none, .subjunctive => .deletion
    | .non₂, .indicative => .indicative
    | _, _ => .out

/-- The grade with which a structure derives the sentence. -/
def grade : Structure → Grade
  | .plain => s.plainGrade
  | .abstract => s.abstractGrade

/-- The move contradicts the belief: an assertion of the comparison contradicts it, and a denial
agrees with it (18); a question asks rather than contradicts, so the belief cannot be that of the
listener it asks (10)–(14); an indirect question raises its proposition without asserting it
(89). -/
def Contradicts : Prop :=
  if s.force = .question then s.holder ≠ .addressee
  else s.construction = .indirectQuestion ∨ s.matrix = .positive

instance : Decidable s.Contradicts := by unfold Contradicts; infer_instance

/-- The sentence demands precise knowledge, by being a comparative of equality (§2.3) or by one
of its words. -/
def DemandsPrecision : Prop :=
  s.construction = .equality ∨ ∃ e ∈ s.elements, e.DemandsPrecision

instance : Decidable s.DemandsPrecision := by unfold DemandsPrecision; infer_instance

/-- The sentence asks the listener to confirm a comparison with the listener's present belief,
which one does not ask of someone who does not hold it (12a). -/
def AsksHolder : Prop :=
  s.force = .question ∧ s.holder = .addressee ∧ s.standard = some .belief

instance : Decidable s.AsksHolder := by unfold AsksHolder; infer_instance

/-- A structure is felicitous when the evidence is `e`: precision needs a belief the listener
stated (30), (31), a question cannot ask its listener to confirm a comparison with that listener's
present belief (12a), and the abstract clause presupposes a belief that the speaker has inferred
and the move contradicts (§2). -/
def Felicitous (σ : Structure) (e : Evidence) : Prop :=
  (s.DemandsPrecision → e = .explicit) ∧ ¬ s.AsksHolder ∧
    (σ = .abstract → e = .inferred ∧ s.Contradicts)

instance (σ : Structure) (e : Evidence) : Decidable (s.Felicitous σ e) := by
  unfold Felicitous; infer_instance

/-- A structure is felicitous in the context of a row, with the evidence it records or, for an
example judged out of context, with some evidence. -/
def FelicitousIn (σ : Structure) : Option Evidence → Prop
  | some e => s.Felicitous σ e
  | none => ∃ e, s.Felicitous σ e

instance (σ : Structure) (c : Option Evidence) : Decidable (s.FelicitousIn σ c) := by
  cases c <;> unfold FelicitousIn <;> infer_instance

/-- In a context a structure has the grade of its derivation when it is felicitous there, and
`contextual` when it is felicitous only elsewhere. -/
def gradeIn (σ : Structure) (c : Option Evidence) : Grade :=
  if s.FelicitousIn σ c then s.grade σ
  else if s.grade σ ≠ .out ∧ ∃ e, s.Felicitous σ e then .contextual else .out

/-- The grade of the best derivation in a context. -/
def verdict (c : Option Evidence) : Grade := max (s.gradeIn .plain c) (s.gradeIn .abstract c)

/-! ### The semantic conditions -/

variable {s}

/-- *Non₂* does not follow a negated declarative matrix ((18), (20)), though it does follow the
matrix of an indirect question (89). -/
theorem not_contradicts_of_negative (hf : s.force = .assertion)
    (hc : s.construction ≠ .indirectQuestion) (hm : s.matrix = .negative) : ¬ s.Contradicts := by
  simp [Contradicts, hf, hc, hm]

-- (10), (14)
theorem contradicts_iff_of_question (hf : s.force = .question) :
    s.Contradicts ↔ s.holder ≠ .addressee := by
  simp [Contradicts, hf]

/-- No context makes the abstract structure felicitous in a sentence demanding precision, so negated
equality (25) excludes *non₂*, against [seuren-1969] and [antinucci-puglielli-1971]. -/
theorem not_felicitous_abstract_of_demandsPrecision (h : s.DemandsPrecision) (e : Evidence) :
    ¬ s.Felicitous .abstract e := fun ⟨hp, _, ha⟩ ↦ by
  simpa [hp h] using (ha rfl).1

-- footnote 13
theorem not_felicitous_abstract_of_affatto (h : .affatto ∈ s.elements) (e : Evidence) :
    ¬ s.Felicitous .abstract e :=
  not_felicitous_abstract_of_demandsPrecision (.inr ⟨_, h, trivial⟩) e

/-! ### The syntactic diagnostics -/

-- §3.24
theorem plainGrade_eq_out_of_che (h : s.complementizer = .che) : s.plainGrade = .out := by
  simp [plainGrade, h]

-- (79)
theorem plainGrade_eq_out_of_lo (h : s.predicate = some .lo) : s.plainGrade = .out := by
  simp [plainGrade, h]

-- (80b), (81), (82c)
theorem abstractGrade_eq_out_of_che (h : s.complementizer = .che) (hp : s.predicate.isSome) :
    s.abstractGrade = .out := by
  simp [abstractGrade, h, hp]

-- (48a), (52a)
theorem plainGrade_eq_out_of_npi {e : Element} (he : e ∈ s.elements) (hn : e.IsNPI)
    (hs : s.negation = .none) : s.plainGrade = .out := by
  rw [plainGrade, ite_eq_right_iff]
  rintro ⟨-, -, -, -, h, -⟩
  exact absurd (h e he hn) (by simp [hs])

end Sentence

/-! ### The rows -/

/-- The sentence a row records. -/
def sentence? (d : Datum) : Option Sentence := do
  let moods := [("indicative", Mood.Grammatical.indicative), ("subjunctive", .subjunctive)]
  let force ← d.parse? "force"
    [("declarative", Force.assertion), ("interrogative", .question)]
  let matrix ← d.parse? "matrix" [("positive", Polarity.positive), ("negative", .negative)]
  let construction ← d.parse? "construction" [("piu", Construction.inequality),
    ("meno", .inequality), ("tanto", .equality), ("indirectQuestion", .indirectQuestion)]
  let holder ← d.parse? "holder" [("addressee", Holder.addressee),
    ("formerAddressee", .formerAddressee), ("thirdParty", .thirdParty)]
  let negation ← d.parse? "negation" [("none", Negation.none), ("non1", .non₁), ("non2", .non₂)]
  let mood ← d.parse? "mood" moods
  let complementizer ← d.parse? "complementizer"
    [("quanto", Complementizer.quanto), ("che", .che), ("se", .se)]
  let elements ← (d.features "element").mapM fun v ↦ List.lookup v
    [("pur", Element.pur), ("neanche", .neanche), ("affatto", .affatto),
      ("degreeModifier", .degreeModifier), ("certainty", .certainty),
      ("speakerGerund", .speakerGerund)]
  return { force, matrix, construction, holder, negation, mood, complementizer, elements
           standard := d.parse? "standard" [("clausal", Standard.clausal), ("belief", .belief)]
           plainMood := (d.parse? "plainMood" moods).getD .indicative
           predicate := d.parse? "predicate" [("adjective", Predicate.adjective), ("lo", .lo)] }

/-- The evidence a row records, for an example judged in a context. -/
def evidence? (d : Datum) : Option Evidence :=
  d.parse? "evidence" [("none", Evidence.none), ("inferred", .inferred), ("explicit", .explicit)]

/-- The analysis allows the judgment of every row. -/
theorem rows_judgment : ∀ d ∈ Examples.all,
    ∃ s ∈ sentence? d, d.judgment ∈ (s.verdict (evidence? d)).judgments := by
  decide

/-- The readings of an indefinite in the embedded clause. -/
inductive Specificity where
  | specific
  | nonspecific
  deriving DecidableEq, Repr

/-- The plain structure leaves an indefinite both readings and the negated clause of the abstract
one only the non-specific reading, as in a negated sentence (44)–(45). -/
def Structure.Allows : Structure → Specificity → Prop
  | .plain, _ => True
  | .abstract, r => r = .nonspecific

instance (σ : Structure) : DecidablePred σ.Allows := fun r ↦ by
  cases σ <;> unfold Structure.Allows <;> infer_instance

/-- A reading of the second indefinite is acceptable exactly when some structure deriving the
sentence allows it ((45), (62)). -/
theorem rows_readings : ∀ d ∈ Examples.all, ∀ s ∈ sentence? d, ∀ x ∈ d.readings,
    ∀ r ∈ [("specific", Specificity.specific), ("nonspecific", .nonspecific)].lookup x.1,
      (x.2 = .acceptable ↔ ∃ σ : Structure, s.grade σ ≠ .out ∧ σ.Allows r) := by
  decide

end NapoliNespor1976
