module

public import Linglib.Discourse.SpeechAct
public import Linglib.Fragments.Romance.Italian.PolarityItems
public import Linglib.Semantics.Mood.Defs
public import Linglib.Semantics.Polarity.Basic
public import Linglib.Data.Examples.Judgment

/-!
# Napoli & Nespor (1976): Negatives in Comparatives

This file formalizes [napoli-nespor-1976]'s account of the Italian *non* that appears in
comparative clauses without reversing truth conditions, *Maria è più intelligente di quanto non
sia Carlo* 'Maria is more intelligent than Carlo is'. Against [antinucci-puglielli-1971]'s
pleonastic element and [seuren-1969]'s underlyingly negative *than*-clause, the paper takes this
*non₂* to be real negation licensed by the discourse move: the speaker presupposes that the
assertion contradicts a belief inferred from the interlocutor's prior discourse, the move is an
assertion, the matrix clause is not negated, and the construction does not demand precise
knowledge of the compared degrees (`Move.Licensed`). The acceptability paradigm of dialogues
between Dario and Paolo, comparative constructions, and an indirect question records the facts
of each move with the reported judgment, and `paradigm_licensed_iff` shows the four conditions
reproduce every judgment. Six morphosyntactic diagnostics witness the underlying negation:
subjunctive mood and non-specific indefinites in the *than*-clause, the complementizer *che*, the
predicative clitic *lo*, *neanche*-conjunction, and the weak NPI *pur*. The NPI *affatto*, which
requires precise knowledge of the listener's belief, is excluded from every *non₂*-comparative by
the precision condition (`pur_admissible`, `affatto_blocked`).

## Implementation notes

The paper's own implementation, a Generative Semantics abstract higher clause hosting *non₂* and
optionally deleted, is not formalized; only the licensing conditions and their surface
diagnostics are. The paper's condition on precision splits into two facts of a move: whether the
contradicted belief was inferred or stated explicitly, and whether the construction, an equality
comparative or an explicit degree modifier, demands precise knowledge of the degrees.

## References

* [napoli-nespor-1976]
* [antinucci-puglielli-1971]
* [seuren-1969]

## TODO

The paradigm's moves are typed from the paper's descriptions of its dialogues; the
dialogues themselves are not yet rows of `Data/Examples/NapoliNespor1976.json`.
-/

@[expose] public section

namespace NapoliNespor1976

open Italian.PolarityItems PolarityItem Mood

/-! ### The licensing condition -/

/-- The speaker's relation to the belief the assertion contradicts. -/
inductive PriorBelief where
  /-- The interlocutor's prior discourse implies a contrary belief. -/
  | inferred
  /-- The interlocutor stated the contrary belief explicitly. -/
  | explicit
  /-- No contrary belief is in play. -/
  | absent
  deriving DecidableEq, Repr

/-- The constructions hosting a *non₂* candidate. -/
inductive Construction where
  /-- *più … di quanto*. -/
  | piu
  /-- *meno … di quanto*. -/
  | meno
  /-- The equality comparative *tanto … quanto*. -/
  | equality
  /-- A comparative with an explicit degree modifier, *molto più*, *due metri più*. -/
  | explicitDegree
  /-- An indirect question, *chissà se*. -/
  | indirectQuestion
  deriving DecidableEq, Repr

/-- The construction demands precise knowledge of the compared degrees. -/
def Construction.Precise (c : Construction) : Prop := c = .equality ∨ c = .explicitDegree

instance (c : Construction) : Decidable c.Precise := inferInstanceAs (Decidable (_ ∨ _))

/-- A discourse move hosting a *non₂* candidate. -/
structure Move where
  priorBelief : PriorBelief
  force : Discourse.SpeechAct.Force
  matrix : Polarity
  construction : Construction
  deriving DecidableEq, Repr

/-- The licensing condition on *non₂*: the assertion contradicts a belief the speaker inferred
from the interlocutor's discourse, the move is an assertion, the matrix is affirmative, and the
construction does not demand precision. -/
def Move.Licensed (m : Move) : Prop :=
  m.priorBelief = .inferred ∧ m.force = .declarative ∧ m.matrix = .positive ∧
    ¬ m.construction.Precise

instance (m : Move) : Decidable m.Licensed := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-! ### The acceptability paradigm

Four dialogues between Dario and Paolo vary the speaker's epistemic state, comparative
constructions isolate the remaining conditions, with *meno*-comparatives as the positive control,
and an indirect question shows the condition is a property of the move rather than of comparative
syntax. -/

/-- A row of the paradigm: the move and the reported acceptability of *non₂*. -/
structure Row where
  move : Move
  judgment : Judgment
  deriving DecidableEq, Repr

/-- An assertion of *Maria è più intelligente di quanto non sia Carlo* against a prior belief of
the given status. -/
def assertion (b : PriorBelief) : Move := ⟨b, .declarative, .positive, .piu⟩

/-- Dario gives no opinion of Maria or Carlo; Paolo asserts that Maria is more intelligent. -/
def noOpinionContext : Row := ⟨assertion .absent, .unacceptable⟩

/-- Dario implies Carlo would beat Maria at chess; Paolo asserts that Maria is more
intelligent. -/
def chessContext : Row := ⟨assertion .inferred, .acceptable⟩

/-- Dario calls Maria stupid in so many words; Paolo disagrees. -/
def explicitCriticismContext : Row := ⟨assertion .explicit, .unacceptable⟩

/-- Dario's complaint implies he expects Maria cannot help; Paolo asserts she is smart enough
to ask. -/
def complaintContext : Row := ⟨assertion .inferred, .acceptable⟩

/-- *È più intelligente di quanto non sia Carlo?*: the move is a question. -/
def questionedComparative : Row :=
  ⟨⟨.inferred, .interrogative, .positive, .piu⟩, .unacceptable⟩

/-- *Maria non è più intelligente di quanto non sia Carlo*: the matrix is negated. -/
def matrixNegatedComparative : Row :=
  ⟨⟨.inferred, .declarative, .negative, .piu⟩, .unacceptable⟩

/-- *Maria è tanto intelligente quanto è Carlo*: an equality comparative demands precise
knowledge of the compared degrees. -/
def equalityComparative : Row :=
  ⟨⟨.inferred, .declarative, .positive, .equality⟩, .unacceptable⟩

/-- *Molto più intelligente*, *due metri più alta*: an explicit degree modifier demands precise
knowledge of the gap. -/
def precisionComparative : Row :=
  ⟨⟨.inferred, .declarative, .positive, .explicitDegree⟩, .unacceptable⟩

/-- *Maria è meno intelligente di quanto tu non creda*: a *meno*-comparative admits *non₂* under
the same conditions as *più*, while a negated equality comparative, semantically close to it,
rejects *non₂*, so the equality restriction cannot reduce to equality linking two similar things
(contra [seuren-1969] and [antinucci-puglielli-1971]). -/
def menoComparative : Row :=
  ⟨⟨.inferred, .declarative, .positive, .meno⟩, .acceptable⟩

/-- *Chissà se non vale la pena di comprarlo*: an indirect question whose negated proposition the
speaker presupposes to be contrary to expectation. -/
def chissaSeNon : Row :=
  ⟨⟨.inferred, .declarative, .positive, .indirectQuestion⟩, .acceptable⟩

/-- The paper's acceptability paradigm. -/
def paradigm : List Row :=
  [noOpinionContext, chessContext, explicitCriticismContext, complaintContext,
    questionedComparative, matrixNegatedComparative, equalityComparative, precisionComparative,
    menoComparative, chissaSeNon]

/-- The four conditions reproduce the paper's judgment on every row, each condition failing on
its own row. -/
theorem paradigm_licensed_iff : ∀ r ∈ paradigm, r.move.Licensed ↔ r.judgment = .acceptable := by
  decide

/-! ### Morphosyntactic diagnostics for underlying negation

Two diagnostics are forced choices in the *than*-clause, mood and the specificity of indefinites;
four are admissibility asymmetries, in which the marked alternant (the complementizer *che*, the
predicative clitic *lo*, *neanche*-conjunction, the weak NPI *pur*) is possible only under
licensed *non₂* while the default (*di quanto*, a repeated predicate, plain conjunction) remains
available throughout. -/

/-- Specificity of indefinites embedded in the *than*-clause. -/
inductive SpecificityProfile where
  /-- Both specific and non-specific readings are available. -/
  | unrestricted
  /-- Only the non-specific reading, under the scope of underlying negation. -/
  | nonspecificOnly
  deriving DecidableEq, Repr

/-- The Italian comparative complementizers. -/
inductive Complementizer where
  /-- The default *than*-complementizer. -/
  | diQuanto
  /-- The alternant admissible only under *non₂*. -/
  | che
  deriving DecidableEq, Repr

/-- Whether the predicative clitic *lo* substitutes for a repeated predicate adjective in the
*than*-clause. -/
inductive Clitic where
  | present
  | absent
  deriving DecidableEq, Repr

/-- Mood of the *than*-clause: subjunctive exactly under licensed *non₂*, the paper's optional
deletion of *non₂* deriving surface subjunctive without *non*; lexical mood control by *credere*
and its kin is abstracted away. -/
def predictedMood (m : Move) : Grammatical := if m.Licensed then .subjunctive else .indicative

/-- Embedded indefinites are restricted to the non-specific reading under licensed *non₂*. -/
def predictedSpecificity (m : Move) : SpecificityProfile :=
  if m.Licensed then .nonspecificOnly else .unrestricted

/-- *Di quanto* occurs with and without *non₂*; *che* only with it. -/
def ComplementizerAdmissible (m : Move) : Complementizer → Prop
  | .diQuanto => True
  | .che => m.Licensed

/-- A clitic-less comparative is always available; *lo* only under *non₂*, and optionally. -/
def CliticAdmissible (m : Move) : Clitic → Prop
  | .present => m.Licensed
  | .absent => True

/-- An item that needs its clause negated at some level, *neanche* in a conjunction or the NPI
*pur*, is admissible in a comparative iff *non₂* is licensed there; the negation requirement is
the item's Fragment entry. -/
def NegationAdmissible (m : Move) (e : PolarityItem) : Prop :=
  m.Licensed ∧ .negation ∈ e.licensingContexts

/-- *Affatto* 'at all' needs its clause negated and requires precise knowledge of the listener's
belief, which a belief only inferred from the listener's discourse does not give. -/
def AffattoAdmissible (m : Move) : Prop :=
  NegationAdmissible m affatto ∧ m.priorBelief ≠ .inferred

/-- *Neanche*-conjunction is admissible in the chess dialogue. -/
theorem neanche_admissible : NegationAdmissible chessContext.move neanche :=
  ⟨by decide, by simp [neanche]⟩

/-- *Pur* is admissible wherever *non₂* is licensed. -/
theorem pur_admissible {m : Move} (h : m.Licensed) : NegationAdmissible m pur :=
  ⟨h, by simp [pur]⟩

/-- *Affatto* meets the negation requirement wherever *non₂* is licensed, like *pur*. -/
theorem negationAdmissible_affatto {m : Move} (h : m.Licensed) :
    NegationAdmissible m affatto :=
  ⟨h, by simp [affatto]⟩

/-- *Affatto* is inadmissible in every *non₂*-comparative: *non₂* requires inferred and imprecise
knowledge of the listener's belief, *affatto* precise knowledge. -/
theorem affatto_blocked (m : Move) : ¬ AffattoAdmissible m :=
  fun ⟨⟨h, _⟩, h'⟩ ↦ h' h.1

end NapoliNespor1976
