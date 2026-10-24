module

public import Linglib.Fragments.Adyghe.Clause
public import Linglib.Fragments.Slavic.Bulgarian.Clause
public import Linglib.Fragments.Ndebele.Clause
public import Linglib.Fragments.NezPerce.Clause
public import Linglib.Data.Examples.Deal2026
public import Linglib.Data.Examples.Krapova2010
public import Studies.BochnakHanink2021
public import Linglib.Syntax.Category.Verb.ArgumentFrame.Takes
public import Linglib.Semantics.Presupposition.FamilyVariant
public import Studies.Karttunen1971b
public import Linglib.Syntax.Minimalist.Clause.Spine
public import Linglib.Semantics.Presupposition.Verb

/-!
# Deal (2026): Clausal complementation as relativization, revisited

Deal types notional complement clauses by their internal and external syntax. The relative
embeddings of Nez Perce, whose edge obligatorily carries the relative pronoun *yox̂* and the
complementizer *ke*, are CPs containing an Ā-dependency launched above TP, not DPs or PPs, so
clausal complementation is not uniformly relativization, against Kayne and Arsenijević. Table
(79) places each construction by its extended spine, the heads projected from V up through any
nominal or adpositional shell over C, and by whether the CP contains an Ā-dependency. Every cell
is filled, so the internal syntax of a clause does not predict its external syntax, and
factivity cross-cuts the Ā axis as well (table (80)).

The Nez Perce embedding strategy is read off the paper's judgments in
`Data/Examples/Deal2026.json`. The Adyghe Ā flag is that the typer 'think' takes carries the
Fragment's relativizer *zV-*, and the Bulgarian flag is Krapova's double requirement over the
Fragment's frames, checked against her sentences (56)–(59) in `Data/Examples/Krapova2010.json`.

## Main results

* `relative_factive`, `projection_rows`: every relative embedding is factive, factivity being
  the Fragment entries' Karttunen class, which the projection trials (33)–(36) and (68) confirm
  row by row.
* `table79`, `table80`: each shell over C, none, D N or P D, occurs with and without an
  Ā-dependency, and factivity varies independently of the Ā-dependency.
* `detoComplement_iff`, `deto_rows`: the double requirement picks out Krapova's *deto*-takers.
* `paradigm_case_discriminates`: the case half of the diagnostic (21) that *yox̂* is a D.

## Implementation notes

The Ā column of (79) is a datum for English, Ndebele and Washo, whose Fragments carry no
relativizer observable, and the Washo V D CP structure of footnote 33, the complementation
spine Bochnak and Hanink propose, is a row beside the table's six. Table (81), nominalization
against factivity, needs Turkish *düşün-* 'think', which has no Fragment.

## TODO

* *ke*-agreement (§2, after Deal's earlier analysis): the φ-probe on C interacts with all
  φ-features, probing from the subject downward until [addr] satisfies it; needs
  value-sensitive satisfaction and ordered-goal probing.
* §6: relative embeddings block indexical shift and take matrix-matching tense as temporal de
  re, while simplex embeddings allow shift and relative tense; rests on Deal's clause-type
  semantics.

## References

* [deal-2026]
* [kayne-2008]
* [kayne-2014]
* [arsenijevic-2009]
* [caponigro-polinsky-2011]
* [krapova-2010]
* [pietraszko-2019]
* [bochnak-hanink-2021]
* [hanink-bochnak-2017]
* [hankamer-mikkelsen-2021]
* [chomsky-1970]
* [deal-2025b]
* [deal-2015a-nels]
* [karttunen-1971b]
* [tonhauser-beaver-roberts-simons-2013]
-/

@[expose] public section

namespace Deal2026

open NezPerce Minimalist

/-! ### The embedding strategy -/

/-- The two embedding strategies are relative embedding, whose complement obligatorily carries
the *yox̂ ke* edge and contains an Ā-dependency above TP, and simplex embedding of a bare CP. -/
inductive EmbeddingStrategy where
  | relative
  | simplex
  deriving DecidableEq, Repr

/-- A predicate embeds relatively when some grammatical notional complement of it carries the
*yox̂ ke* edge ((27)–(28)); *cuukwe*'s (66b) is only marginal. -/
def RelativeEmbedding (v : Verb) : Prop :=
  ∃ row ∈ Examples.all, row.feature? "verb" = some v.form ∧
    row.feature? "edge" = some "yoxKe" ∧ row.judgment = .acceptable

instance (v : Verb) : Decidable (RelativeEmbedding v) :=
  inferInstanceAs (Decidable (∃ row ∈ Examples.all, _))

/-- A predicate's strategy is relative when it embeds relatively and simplex otherwise. Both
strategies select a CP; the contrast is internal to the clause selected. -/
def strategy (v : Verb) : EmbeddingStrategy :=
  if RelativeEmbedding v then .relative else .simplex

/-- The relative-embedding predicates take no noun-phrase object, (41). -/
theorem nominal_rows :
    ∀ row ∈ Examples.all, row.feature? "diagnostic" = some "nominalComplement" →
      ∀ v ∈ verbs, row.feature? "verb" = some v.form →
        (row.judgment = .acceptable ↔ ∃ fr ∈ v.valency.frames, fr.HasNominal) := by
  decide

/-- Every relative embedding is factive (§7). -/
theorem relative_factive :
    ∀ v ∈ verbs, strategy v = .relative → v.IsFactive := by
  decide

/-- Consultants endorse the complement under negation, in a question or in a conditional
antecedent exactly for the factive predicates, the projection trials (33)–(36) and (68). -/
theorem projection_rows :
    ∀ row ∈ Examples.all, ∀ _ ∈ row.environment?, ∀ v ∈ verbs, row.feature? "verb" = some v.form →
      (row.projective? = some true ↔ v.IsFactive) := by
  decide

/-- *cuukwe* 'know' projects from a third-person conditional antecedent (68), which
[karttunen-1971b]'s semi-factive postulates, built on first-person conditionals (25), do not
predict. -/
theorem cuukwe_conditional_projects :
    ¬ Karttunen1971b.Projects .semi .conditionalAntecedent ∧
      (∃ row ∈ Examples.all, row.environment? = some .conditionalAntecedent ∧
        row.person? = some .third ∧ row.feature? "verb" = some cuukwe.form ∧
        row.projective? = some true) ∧
      ∀ row ∈ Karttunen1971b.Examples.all, row.environment? = some .conditionalAntecedent →
        row.person? = some .first := by
  decide

/-! ### Table (79): internal against external syntax -/

/-- A cell of table (79) pairs the extended spine of a notional complement, the heads projected
from V up through any shell over C, with whether the CP contains an Ā-dependency. -/
structure Cell where
  spine : ClauseSpine
  internalAbar : Bool

/-- A Nez Perce cell is a bare CP whose Ā-dependency is the relative strategy. -/
def nezPerce (v : Verb) : Cell := ⟨ClauseSpine.cP, strategy v == .relative⟩

/-- English simplex V complementation, *think*, is a bare CP without an Ā-dependency. -/
def englishThink : Cell := ⟨ClauseSpine.cP, false⟩

/-- The Adyghe relative embedding of (43) is V D N CP with an Ā-dependency. Its flag comes from
the Fragment, where the clause-typer 'think' takes carries the relativizer *zV-*
([caponigro-polinsky-2011]). -/
def adygheRelative : Cell :=
  ⟨ClauseSpine.cP.append [.N, .D],
    decide (∃ z ∈ Adyghe.gwepshesa.typers Adyghe.complementizers, Adyghe.relativizer ∈ z.morphs)⟩

/-- By Krapova's double requirement, reported at footnote 22, *deto* introduces the complement
of a predicate that is an emotive factive, a factive preferential attitude, and takes a *za*
phrase. -/
def DetoComplement (v : Verb) : Prop :=
  (∃ a ∈ v.attitude, a.IsPreferential) ∧ v.IsFactive ∧
    ∃ fr ∈ v.valency.frames, fr.HasAdpositional

instance (v : Verb) : Decidable (DetoComplement v) :=
  inferInstanceAs (Decidable ((∃ a ∈ v.attitude, _) ∧ _ ∧ ∃ fr ∈ v.valency.frames, _))

/-- The double requirement picks out exactly the predicates Krapova lists as *deto*-takers, and
neither condition suffices, since *văzmuštavam se* 'resent' is emotive without a *za* phrase and
*razbiram* 'comprehend' is factive without being emotive. -/
theorem detoComplement_iff :
    (∀ v ∈ Bulgarian.verbs, DetoComplement v ↔ v.form ∈ Bulgarian.detoTakers.map (·.form)) ∧
      ¬ DetoComplement Bulgarian.vazmushtavamSe ∧ ¬ DetoComplement Bulgarian.razbiram := by
  decide

/-- Krapova's *deto* sentences (56) and (58) are grammatical iff the predicate meets the double
requirement, and their *če* variants always are (fn. 46). -/
theorem deto_rows :
    ∀ row ∈ Krapova2010.Examples.all, row.feature? "diagnostic" = some "detoSelection" →
      ∀ v ∈ Bulgarian.verbs, row.feature? "verb" = some v.form →
        (row.judgment = .acceptable ↔ DetoComplement v) ∧
          ∀ a ∈ row.alternatives, a.2 = .acceptable := by
  decide

/-- The nominal paraphrases (59) take the preposition *za* and no other, the adpositional frame
of the Fragment's emotive factives. -/
theorem zaPhrase_rows :
    ∀ row ∈ Krapova2010.Examples.all, row.feature? "diagnostic" = some "zaPhrase" →
      ∀ v ∈ Bulgarian.verbs, row.feature? "verb" = some v.form →
        (row.judgment = .acceptable ↔ ∃ fr ∈ v.valency.frames, fr.HasAdpositional) ∧
          ∀ a ∈ row.alternatives, a.2 = .ungrammatical := by
  decide

/-- In Krapova's factivity tests (57a–b) the complement survives negation and a question exactly
for the factive predicates. -/
theorem krapova_projection_rows :
    ∀ row ∈ Krapova2010.Examples.all, ∀ _ ∈ row.environment?,
      ∀ v ∈ Bulgarian.verbs, row.feature? "verb" = some v.form →
        (row.projective? = some true ↔ v.IsFactive) := by
  decide

/-- In Krapova's contradiction tests (57c) and footnote 46, a continuation denying the
complement is starred exactly under a factive predicate, under *deto* and *če* alike. -/
theorem krapova_contradiction_rows :
    ∀ row ∈ Krapova2010.Examples.all, row.feature? "diagnostic" = some "contradiction" →
      ∀ v ∈ Bulgarian.verbs, row.feature? "verb" = some v.form →
        ((∃ a ∈ row.alternatives, a.2 = .ungrammatical) ↔ v.IsFactive) := by
  decide

/-- English N complementation, *the fact that S*, is V D N CP without an Ā-dependency, the DP
shell with an N co-argument of [hankamer-mikkelsen-2021]. -/
def englishNComplementation : Cell := ⟨ClauseSpine.cP.append [.N, .D], false⟩

/-- The Bulgarian relative embedding of (49) is V P D CP with an Ā-dependency. Its flag comes
from the Fragment, where *săžaljavam* 'regret' meets the double requirement and so takes the
*deto* complement Krapova analyzes as a hidden relative. -/
def bulgarianRelative : Cell :=
  ⟨ClauseSpine.cP.append [.D, .P], decide (DetoComplement Bulgarian.sazhaljavam)⟩

/-- The Ndebele embedding of (78) is V P D CP without an Ā-dependency. The preposition *nga*
'about' sits over the class-15 augment, which [pietraszko-2019] takes as a D over *kuthi*. -/
def ndebeleEmbedding : Cell := ⟨ClauseSpine.cP.append [.D, .P], false⟩

/-- The Washo factive of footnote 33 is V D CP without an Ā-dependency or an N, a silent D over
the nominalized clause ([hanink-bochnak-2017], [bochnak-hanink-2021]), whose index binds without
movement ([hanink-2021]). -/
def washoFactive : Cell := ⟨BochnakHanink2021.complementSpine, false⟩

/-- The rows are the six cells of table (79), with the V CP cell without an Ā-dependency
witnessed twice, and the Washo structure. -/
def rows : List Cell :=
  [nezPerce liloy, nezPerce neki, englishThink, adygheRelative, englishNComplementation,
    bulgarianRelative, ndebeleEmbedding, washoFactive]

/-- Every cell of table (79) is filled, so a clause's internal syntax does not predict its external
syntax. -/
theorem table79 :
    ∀ shell ∈ [([] : List Cat), [.N, .D], [.D, .P]], ∀ abar ∈ [true, false],
      ∃ c ∈ rows, c.spine.above .C = shell ∧ c.internalAbar = abar := by
  decide

/-! ### Table (80): factivity against the Ā axis -/

/-- Every cell of table (80) is filled, so factivity and relative-embedding syntax vary
independently. -/
theorem table80 :
    (∃ v ∈ verbs, v.IsFactive ∧ strategy v = .relative) ∧
      (∃ v ∈ verbs, v.IsFactive ∧ strategy v = .simplex) ∧
      (∃ v ∈ verbs, ¬ v.IsFactive ∧ strategy v = .simplex) ∧
      (∃ v ∈ Adyghe.verbs, v.toVerb.Takes Adyghe.zeRe ∧ ¬ v.toVerb.IsFactive) := by
  decide

/-! ### The D-inflection diagnostic (21) -/

/-- The relative pronoun *yox̂* ~ *ko* inflects for case, in that cells of the paradigm with
distinct cases share no forms. This is the case half of the diagnostic that *yox̂* ~ *ko* is a D
while the invariant *ke* is a C. -/
theorem paradigm_case_discriminates :
    ∀ p ∈ relativePronounParadigm, ∀ q ∈ relativePronounParadigm,
      p.case ≠ q.case → ∀ f ∈ p.forms, f ∉ q.forms := by
  decide

end Deal2026
