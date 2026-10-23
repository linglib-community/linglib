module

public import Linglib.Semantics.Questions.Bias
public import Linglib.Data.Examples.SeeligerRepp2018

/-!
# Seeliger & Repp (2018): Biased declarative questions in Swedish and German

[seeliger-repp-2018] distinguish two kinds of question with declarative syntax. A declarative
question such as *Peter is coming?* requires contextual evidence for the proposition the
declarative denotes and a speaker who had not assumed it; a rejecting question such as *Surely
Peter is coming?*, German *Peter kommt doch wohl?*, Swedish *Men Peter kommer väl?*, requires
evidence against it and a speaker who had assumed it. The profiles are stated in the
two-dimensional bias scheme of [sudo-2013], evidential and epistemic, which the paper extends with
'minus' values for epistemic bias (Section 2): the substrate's `Question.BiasValue`, a set of
states of evidence or belief, [+s] being `plus s` and [−s] its complement `minus s`.

Table 1's four types follow from the polarity of the declarative (`table1`): a declarative
question of polarity `s` has evidential bias [+s] and epistemic bias [−s] (`dqProfile`), and the
preliminary REJECTQ operator (17), λq: [¬q]^evid & [q]^epist. {q, ¬q}, gives a rejecting question
[+(¬s)] and [+s] (`rejectQ`). A rejecting question is therefore used in a proper subset of the
situations of the declarative question of the opposite polarity, the observation of p. 138
(`felicity_rejectQ_ssubset`). The revised operator (40), with the illocutionary modifier VERUM
or FALSUM, derives the positive rejecting question (`rejectQWith_verum`) but not the negative one:
FALSUM requires only that the evidence not support ¬p and that the speaker not have been
committed to p, which admits neutral evidence and no prior assumption, situations Table 1 excludes
(`felicity_rejectQ_ssubset_rejectQWith_falsum`).

Swedish marks a rejecting question with at least one morpho-syntactic cue (p. 157): a negative one
with fronted negation or *väl*, a positive one with *men* 'but' and *väl*, or with clause-initial
*visst* or *nog* when the evidence is direct. `SwedishCues.MarksRQ` states the generalization and
`marking_iff` checks it against the examples of Sections 3 and 5.3.

## Implementation notes

* The question REJECTQ forms from a declarative of polarity `s` with prejacent `p` is the polar
  question on `s • p`, which is the polar question on `p` (`Question.polar_smul`). The
  commitment-modified propositions IM(q) of (40) are not modelled, only the presuppositions.
* The declarative polarity is Table 1's simplified 'Declarative denotes' column: the paper argues
  in Section 6.1 that the negation of a negative rejecting question is FALSUM, not propositional
  negation.

## TODO

* The acceptability experiment of Section 5.4 (Table 2), the German rejections of Section 4.2
  that show *doch wohl* to be non-compositional, and the polarity-item diagnostics of Section 6.1
  are not yet encoded.
* The comparison with the monopolar declarative questions of [krifka-2015] (footnote 17), which
  predict the rows of declarative but not of rejecting questions.

## References

* [seeliger-repp-2018]
* [sudo-2013]
* [krifka-2015]
-/

@[expose] public section

namespace SeeligerRepp2018

open Question (BiasValue BiasProfile)
open Question.BiasValue (plus minus neutral)

/-! ### Declarative and rejecting questions (Sections 2, 3 and 4.3) -/

/-- A declarative question of polarity `s`: evidence for the proposition the declarative denotes,
and a speaker who had not assumed it (Section 2). -/
def dqProfile (s : Polarity) : BiasProfile := ⟨plus s, minus s⟩

/-- The preliminary REJECTQ (17), λq: [¬q]^evid & [q]^epist. {q, ¬q}, on the proposition of a
declarative of polarity `s`: evidence for the opposite proposition, and a speaker who had
assumed it. -/
def rejectQ (s : Polarity) : BiasProfile := ⟨plus (.negative * s), plus s⟩

/-- A rejecting question is used in a proper subset of the situations of the declarative question
of the opposite polarity (p. 138): the negative one within the positive declarative question's,
the positive one within the negative declarative question's. -/
theorem felicity_rejectQ_ssubset (s : Polarity) :
    (rejectQ s).felicity ⊂ (dqProfile (.negative * s)).felicity := by
  cases s <;> decide

/-! ### The illocutionary modifiers (Section 6.2) -/

/-- The illocutionary modifiers of (40): VERUM, a high degree of commitment, and FALSUM, a zero
degree. -/
inductive Modifier where
  | verum
  | falsum
  deriving DecidableEq, Repr

/-- The contexts in which a basis gives the modifier's degree of commitment to the `s`
proposition: VERUM needs the basis to support it, FALSUM that it not support it. -/
def Modifier.bias : Modifier → Polarity → BiasValue
  | .verum, s => plus s
  | .falsum, s => minus s

/-- The revised REJECTQ (40), λqλIM: [IM(¬q)]^evid & [IM(q)]^epist. {IM(q), ¬IM(q)}, with `q` the
non-negative proposition, as in (41): the positive rejecting question has VERUM, the negative one
FALSUM. -/
def rejectQWith (m : Modifier) : BiasProfile := ⟨m.bias .negative, m.bias .positive⟩

/-- With VERUM, (40) agrees with (17) on the positive rejecting question. -/
theorem rejectQWith_verum : rejectQWith .verum = rejectQ .positive := rfl

/-- With FALSUM, (40) is strictly weaker than (17) and Table 1 on the negative rejecting question:
it admits neutral evidence without a prior assumption. -/
theorem felicity_rejectQ_ssubset_rejectQWith_falsum :
    (rejectQ .negative).felicity ⊂ (rejectQWith .falsum).felicity ∧
      (0, 0) ∈ (rejectQWith .falsum).felicity := by
  decide

/-! ### Table 1 -/


/-- The two kinds of question with declarative syntax. -/
inductive Kind where
  | declarative
  | rejecting
  deriving DecidableEq, Repr

/-- The profile of a question of the given kind and polarity. -/
def Kind.profile : Kind → Polarity → BiasProfile
  | .declarative => dqProfile
  | .rejecting => rejectQ

/-- The four types of Table 1, with their kind and the polarity of the declarative. -/
def typeTable : List (String × Kind × Polarity) :=
  [("PDQ", .declarative, .positive), ("NDQ", .declarative, .negative),
    ("PRQ", .rejecting, .positive), ("NRQ", .rejecting, .negative)]

/-- The bias values of the annotation. -/
def biasTable : List (String × BiasValue) :=
  [("+positive", plus .positive), ("+negative", plus .negative),
    ("-positive", minus .positive), ("-negative", minus .negative), ("neutral", neutral)]

/-- An example of Table 1: the kind and polarity of the question, and the profile the example
records. -/
structure Row where
  /-- Declarative or rejecting. -/
  kind : Kind
  /-- The polarity of the declarative. -/
  polarity : Polarity
  /-- The recorded bias profile. -/
  profile : BiasProfile
  deriving DecidableEq

/-- The row of an example annotated with a type and a bias profile. -/
def Row.ofDatum (ex : Datum) : Option Row := do
  let (k, s) ← ex.parse? "type" typeTable
  let ev ← ex.parse? "evidential" biasTable
  let ep ← ex.parse? "epistemic" biasTable
  pure ⟨k, s, ⟨ev, ep⟩⟩

/-- The examples (5) to (8) of Table 1. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem rows_length : rows.length = 13 := by decide

/-- Table 1: every example has the profile of its kind and polarity. -/
theorem table1 : ∀ r ∈ rows, r.profile = r.kind.profile r.polarity := by decide +kernel

/-! ### Marking rejecting questions in Swedish (Sections 3, 5.3 and 6) -/

/-- The morpho-syntactic cues of a Swedish declarative that bear on a rejecting reading, and
whether the contextual evidence is direct. *Väl* is `Swedish.Particles.val`. -/
structure SwedishCues where
  /-- The negation is fronted. -/
  fronted : Bool
  /-- Clause-medial *väl*. -/
  val : Bool
  /-- Clause-initial *men* 'but'. -/
  men : Bool
  /-- Clause-initial *visst* or *nog*. -/
  initial : Bool
  /-- The contextual evidence is direct. -/
  direct : Bool
  deriving DecidableEq, Repr

/-- The generalization of p. 157: a negative rejecting question needs fronted negation or *väl*;
a positive one *men* with *väl*, or clause-initial *visst* or *nog* when the evidence is
direct. -/
def SwedishCues.MarksRQ (c : SwedishCues) : Polarity → Prop
  | .negative => c.fronted = true ∨ c.val = true
  | .positive => (c.men = true ∧ c.val = true) ∨ (c.initial = true ∧ c.direct = true)

instance (c : SwedishCues) (s : Polarity) : Decidable (c.MarksRQ s) := by
  cases s <;> unfold SwedishCues.MarksRQ <;> infer_instance

/-- An example of a Swedish declarative in the context of a rejecting question. -/
structure MarkingRow where
  /-- The polarity of the rejecting question. -/
  polarity : Polarity
  /-- The cues of the declarative. -/
  cues : SwedishCues
  /-- Whether the declarative can be the rejecting question. -/
  judgment : Judgment
  deriving DecidableEq

/-- Presence of a cue in the annotation. -/
def yesNo : List (String × Bool) := [("yes", true), ("no", false)]

/-- The marking row of an example annotated with its cues. -/
def MarkingRow.ofDatum (ex : Datum) : Option MarkingRow := do
  let (k, s) ← ex.parse? "type" typeTable
  guard (k = .rejecting)
  let fronted ← ex.parse? "negation" [("fronted", true), ("low", false), ("none", false)]
  let val ← ex.parse? "väl" yesNo
  let men ← ex.parse? "men" yesNo
  let initial ← ex.parse? "visst/nog" yesNo
  let direct ← ex.parse? "evidence" [("direct", true), ("indirect", false)]
  pure ⟨s, ⟨fronted, val, men, initial, direct⟩, ex.judgment⟩

/-- The Swedish examples (7c), (8c), (8c′), (23) and (24). -/
def markingRows : List MarkingRow := Examples.all.filterMap MarkingRow.ofDatum

/-- The rows cover the three Swedish rejecting questions of (7) and (8) and the eight of (23)
and (24). -/
theorem markingRows_length : markingRows.length = 11 := by decide

theorem marking_iff :
    ∀ r ∈ markingRows, (r.judgment = .acceptable ↔ r.cues.MarksRQ r.polarity) := by
  decide

end SeeligerRepp2018
