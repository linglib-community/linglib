module

public import Mathlib.Data.Fin.VecNotation
public import Linglib.Data.Examples.Lechner2004
public import Linglib.Syntax.Binding.Tree

/-!
# Lechner (2004): Ellipsis in comparatives

This file formalizes two of Lechner's binding arguments that the ellipsis sites of comparatives
are projected in syntax. In a clausal comparative the site of Comparative Deletion is
reconstructed at LF, where its copy of a name counts as a pronoun, so that coreference is out in
(24) and restored in (25), whose site sits in a further clause; neither Kennedy's semantic
resolution nor reconstruction of the name as an R-expression predicts both. A phrasal comparative
is a Gapped clause, a copy of the matrix clause with the remnant in the position of its
correlate, and the remnant inherits the correlate's c-command relations (Prediction V). Lechner's
minimal pairs vary the height of the correlate against a coindexed matrix term, and the Gapped
clause separates the halves of each pair, while Heim's direct analysis, which raises the remnant
out of the clause, gives both halves one verdict.

## Main definitions

* `Lechner2004.Resolution`: the resolution of a deletion site, semantic, syntactic, or syntactic
  under Fiengo and May's vehicle change.
* `Lechner2004.PhrasalComparative.gapped`, `Lechner2004.PhrasalComparative.direct`: the Gapped
  clause and the LF of the direct analysis.

## Main results

* `Lechner2004.resolution_fits_iff`: only reconstruction under vehicle change predicts (24)–(25).
* `Lechner2004.PhrasalComparative.gapped_cCommands_iff`,
  `Lechner2004.PhrasalComparative.cCommands_gapped_iff`: Prediction V.
* `Lechner2004.analysis_fits_iff`, `Lechner2004.direct_same`: only the Gapped clause predicts the
  minimal pairs (83)–(91).

## Implementation notes

Trees carry categories only, and German clauses have their underlying hierarchy, subject over
dative over accusative. Binding is computed within the Gapped clause, which coordinates with the
matrix clause outside the c-command domain of its terms. Heim's LF, in which *-er* takes the
correlate and the remnant as a pair ((55), (88)), is rendered by adjoining both to the clause,
the configuration in which Lechner reads c-command off (88) and (92)–(93); its base-position
reading is computed on the surface tree. The ?? of (91) counts against coreference. The book
calls the effect in (24) a Principle C violation, but with the copy a pronoun, as (25) shows it
to be, (24) violates Condition B.

## TODO

Prediction IV ((75)–(77)), Predictions I–III of §3.1, the arguments from reflexives and the
Coordinate Structure Constraint of chapter 2, §§2.2–2.3, and the argument of (27)–(29) against a
surface Principle B account of (24) are not formalized.

## References

* [lechner-2004]
* [kennedy-1999]
* [heim-1985]
* [fiengo-may-1994]
-/

@[expose] public section

namespace Lechner2004

open Core.Order PhraseStructure PhraseStructure.Tree Binding
open RoseTree (IsBranchingAt CCommands cCommands_replaceAt_of_le cCommands_replaceAt_self)

/-! ### Trees and coreference -/

/-- `np` is a nominal, a terminal noun phrase. -/
abbrev np : Tree Cat Unit := .terminal .N ()

/-- `word c` is a word of category `c`. -/
abbrev word (c : Cat) : Tree Cat Unit := .terminal c ()

/-- `nominalIn` is a noun phrase with a nominal beside its head noun, as in *Peter's sister* and
*die Frau des Präsidenten*. -/
abbrev nominalIn : Tree Cat Unit := .node .N [np, word .N]

/-- The binding configuration of the positions `p` and `q` of `t` reads them as `0` and `1`. -/
abbrev pairConfiguration (t : Tree Cat Unit) (p q : TreePath) : Configuration (Fin 2) :=
  t.clauseConfiguration.comap ![p, q]

/-- A nominal of class `k` at `q` of `t` may corefer with the nominal at `p` when, if a nominal
occupies `q`, it meets its binding condition under the dependency relating the two. -/
def MayCorefer (t : Tree Cat Unit) (p q : TreePath) (k : BindingClass) : Prop :=
  t.subtreeAt q.toList = some np → (pairConfiguration t p q).Condition (pair 0 1) ∅ 1 k

instance (t : Tree Cat Unit) (p q : TreePath) (k : BindingClass) :
    Decidable (MayCorefer t p q k) :=
  inferInstanceAs (Decidable (_ → _))

/-- A judgment attests the coreferential reading when it is acceptable or marginal. -/
def Attested (e : Datum) : Prop := .marginal ≤ e.judgment

instance (e : Datum) : Decidable (Attested e) := inferInstanceAs (Decidable (_ ≤ _))

/-! ### Comparative Deletion (chapter 2, §2.1) -/

/-- A clausal comparative with Comparative Deletion is given by its *than*-clause, with a trace
at the deletion site, the position of the pronoun, the antecedent adjective phrase, and the
address of the name inside the antecedent. -/
structure CDComparative where
  /-- The *than*-clause, a trace at the deletion site. -/
  thanClause : Tree Cat Unit
  /-- The deletion site. -/
  site : TreePath
  /-- The pronoun coindexed with the name. -/
  pronoun : TreePath
  /-- The antecedent adjective phrase of the matrix clause. -/
  antecedent : Tree Cat Unit
  /-- The address of the name inside the antecedent. -/
  name : List ℕ

namespace CDComparative

/-- `c.copy` is the position the copy of the name would occupy in the *than*-clause. -/
def copy (c : CDComparative) : TreePath := ⟨c.site.toList ++ c.name⟩

/-- `c.reconstructed` is the *than*-clause with the antecedent reconstructed at the site. -/
def reconstructed (c : CDComparative) : Tree Cat Unit :=
  c.thanClause.replaceAt c.site.toList c.antecedent

end CDComparative

/-- A deletion site is resolved in the semantics, leaving no syntactic copy, by syntactic
reconstruction of its antecedent, or by syntactic reconstruction under vehicle change, which
makes the copied name a pronoun. -/
inductive Resolution where
  | semantic
  | syntactic
  | vehicleChange
  deriving DecidableEq, Fintype, Repr

/-- `r.lf c` is the *than*-clause at LF, which semantic resolution leaves with its trace and
syntactic resolution reconstructs. -/
def Resolution.lf : Resolution → CDComparative → Tree Cat Unit
  | .semantic, c => c.thanClause
  | .syntactic, c | .vehicleChange, c => c.reconstructed

/-- The copied name is a pronoun under vehicle change and an R-expression otherwise. -/
def Resolution.copyClass : Resolution → BindingClass
  | .vehicleChange => .pronoun
  | .semantic | .syntactic => .rExpression

/-- A resolution permits coreference between the pronoun and the name when the copy of the name
at LF, if there is one, meets its binding condition. -/
def Resolution.Permits (r : Resolution) (c : CDComparative) : Prop :=
  MayCorefer (r.lf c) c.pronoun c.copy r.copyClass

instance (r : Resolution) (c : CDComparative) : Decidable (r.Permits c) :=
  inferInstanceAs (Decidable (MayCorefer _ _ _ _))

theorem cCommands_copy_iff (c : CDComparative) {p : TreePath} (hsp : ¬ c.site ≤ p)
    (hps : ¬ p ≤ c.site) : CCommands c.reconstructed p c.copy ↔ CCommands c.thanClause p c.site :=
  cCommands_replaceAt_of_le (TreePath.le_def.2 (List.prefix_append _ _)) hsp hps

/-- `proudOfJohn` is the antecedent *d-proud of John* of (24) and (25). -/
def proudOfJohn : Tree Cat Unit := .node .Adj [word .Adj, .node .P [word .P, np]]

/-- `cd24` is the *than*-clause of (24), *than he is △*. -/
def cd24 : CDComparative where
  thanClause := .node .S [np, .node .V [word .V, .trace 0 .Adj]]
  site := ⟨[1, 1]⟩
  pronoun := ⟨[0]⟩
  antecedent := proudOfJohn
  name := [1, 1]

/-- `cd25` is the *than*-clause of (25), *than he believes that I am △*. -/
def cd25 : CDComparative where
  thanClause := .node .S [np, .node .V [word .V,
    .node .C [word .C, .node .S [np, .node .V [word .V, .trace 0 .Adj]]]]]
  site := ⟨[1, 1, 1, 1, 1]⟩
  pronoun := ⟨[0]⟩
  antecedent := proudOfJohn
  name := [1, 1]

/-- `cdData` pairs each clausal comparative with its row. -/
def cdData : List (CDComparative × Datum) :=
  [(cd24, Examples.ch2_24), (cd25, Examples.ch2_25)]

theorem copy_present : ∀ d ∈ cdData, d.1.thanClause.subtreeAt d.1.pronoun.toList = some np ∧
    d.1.reconstructed.subtreeAt d.1.copy.toList = some np ∧
      d.1.thanClause.subtreeAt d.1.copy.toList = none := by
  decide

/-- Of the three resolutions only syntactic reconstruction under vehicle change predicts the
judgments of (24) and (25). -/
theorem resolution_fits_iff (r : Resolution) :
    (∀ d ∈ cdData, r.Permits d.1 ↔ Attested d.2) ↔ r = .vehicleChange := by
  revert r; decide

/-! ### Phrasal comparatives (chapter 4, §3.2) -/

/-- In Lechner's test context A (82) for Prediction V the matrix term is a pronoun and the
remnant contains a name, and in test context B (89) the matrix term is a name and the remnant
is a pronoun. -/
inductive TestContext where
  | a
  | b
  deriving DecidableEq, Repr

/-- `k.pronounName m r` orders a matrix term at `m` and a remnant's nominal at `r` as pronoun and
name. -/
def TestContext.pronounName : TestContext → TreePath → TreePath → TreePath × TreePath
  | .a, m, r => (m, r)
  | .b, m, r => (r, m)

/-- A phrasal comparative with a coindexed pair is given by its matrix clause, with a trace at the
base of the *than*-phrase, its correlate, its remnant, the matrix term, and the address of the
remnant's coindexed nominal. -/
structure PhrasalComparative where
  /-- The matrix clause, a trace at the base of the *than*-phrase. -/
  matrix : Tree Cat Unit
  /-- The base of the *than*-phrase. -/
  thanPhrase : TreePath
  /-- The correlate of the remnant. -/
  correlate : TreePath
  /-- The remnant. -/
  remnant : Tree Cat Unit
  /-- The matrix term coindexed with the remnant's nominal. -/
  mTerm : TreePath
  /-- The address of the coindexed nominal inside the remnant. -/
  inRemnant : List ℕ
  /-- Which of the two is the pronoun. -/
  context : TestContext

namespace PhrasalComparative

variable (e : PhrasalComparative)

/-- The Gapped clause of the PC-Hypothesis, the matrix clause with the remnant in the position of
the correlate. -/
def gapped : Tree Cat Unit := e.matrix.replaceAt e.correlate.toList e.remnant

/-- The sentence, the *than*-phrase in its base with the remnant as its complement. -/
def sentence : Tree Cat Unit :=
  e.matrix.replaceAt e.thanPhrase.toList (Tree.node .P [word .P, e.remnant])

/-- The LF of the direct analysis adjoins the remnant and the correlate to the clause they leave
traces in, so that the clause is one category of three segments. -/
def direct : Tree Cat Unit :=
  .adjoin .S [e.remnant, .adjoin .S [(e.matrix.subtreeAt e.correlate.toList).getD np,
    (e.sentence.replaceAt (e.thanPhrase.toList ++ [1]) (Tree.trace 1 .N)).replaceAt
      e.correlate.toList (Tree.trace 0 .N)]]

theorem gapped_cCommands_iff (m : TreePath) :
    CCommands e.gapped e.correlate m ↔ CCommands e.matrix e.correlate m :=
  cCommands_replaceAt_self

theorem cCommands_gapped_iff {m : TreePath} (hcm : ¬ e.correlate ≤ m) (hmc : ¬ m ≤ e.correlate)
    (q : List ℕ) :
    CCommands e.gapped m ⟨e.correlate.toList ++ q⟩ ↔ CCommands e.matrix m e.correlate :=
  cCommands_replaceAt_of_le (TreePath.le_def.2 (List.prefix_append _ _)) hcm hmc

theorem cCommands_sentence_iff {m : TreePath} (htm : ¬ e.thanPhrase ≤ m)
    (hmt : ¬ m ≤ e.thanPhrase) (q : List ℕ) :
    CCommands e.sentence m ⟨e.thanPhrase.toList ++ q⟩ ↔ CCommands e.matrix m e.thanPhrase :=
  cCommands_replaceAt_of_le (TreePath.le_def.2 (List.prefix_append _ _)) htm hmt

theorem not_cCommands_direct (m q : List ℕ) :
    ¬ CCommands e.direct ⟨1 :: 1 :: m⟩ ⟨0 :: q⟩ := by
  rintro ⟨h, -, -⟩
  have hb : IsBranchingAt e.direct ⟨[1]⟩ := ⟨_, rfl, by simp⟩
  have hlt : (⟨[1]⟩ : TreePath) < ⟨1 :: 1 :: m⟩ :=
    lt_of_le_of_ne (TreePath.le_def.2 ⟨1 :: m, rfl⟩) (by simp)
  simpa [TreePath.le_def] using h hb hlt

theorem direct_cCommands (m : List ℕ) : CCommands e.direct ⟨[0]⟩ ⟨1 :: m⟩ := by
  refine ⟨fun ⟨l⟩ _ hx ↦ ?_, by simp [TreePath.le_def], by simp [TreePath.le_def]⟩
  obtain rfl : l = [] := List.length_eq_zero_iff.1 (by simpa using TreePath.length_strictMono hx)
  exact List.nil_prefix

end PhrasalComparative

/-- A phrasal comparative is analyzed as a Gapped clause, or directly, with Condition C read at the
raised position of the remnant or at its base in the *than*-phrase. -/
inductive Analysis where
  | reduction
  | directRaised
  | directBase
  deriving DecidableEq, Fintype, Repr

/-- `a.rep e` is the representation of `e` under `a`, with the positions of the matrix term and of
the remnant's nominal. -/
def Analysis.rep : Analysis → PhrasalComparative → Tree Cat Unit × TreePath × TreePath
  | .reduction, e => (e.gapped, e.mTerm, ⟨e.correlate.toList ++ e.inRemnant⟩)
  | .directRaised, e => (e.direct, ⟨1 :: 1 :: e.mTerm.toList⟩, ⟨0 :: e.inRemnant⟩)
  | .directBase, e => (e.sentence, e.mTerm, ⟨e.thanPhrase.toList ++ 1 :: e.inRemnant⟩)

/-- `a.pronounName e` gives the positions of the pronoun and the name in `a.rep e`. -/
def Analysis.pronounName (a : Analysis) (e : PhrasalComparative) : TreePath × TreePath :=
  e.context.pronounName (a.rep e).2.1 (a.rep e).2.2

/-- An analysis permits the coreferential reading when the name meets Condition C in its
representation. -/
def Analysis.Permits (a : Analysis) (e : PhrasalComparative) : Prop :=
  MayCorefer (a.rep e).1 (a.pronounName e).1 (a.pronounName e).2 .rExpression

instance (a : Analysis) (e : PhrasalComparative) : Decidable (a.Permits e) :=
  inferInstanceAs (Decidable (MayCorefer _ _ _ _))

/-- `introduced` is the English clause *subject introduced object to more friends*, with a trace at
the base of the *than*-phrase in the degree phrase. -/
def introduced : Tree Cat Unit :=
  .node .S [np, .node .V [word .V,
    .node .V [np, .node .P [word .P, .node .N [word .N, .trace 0 .P]]]]]

/-- In (83a), *Sally introduced him to more friends than Peter's sister*, the correlate, the
subject, is higher than the pronoun. -/
def ex83 : PhrasalComparative where
  matrix := introduced
  thanPhrase := ⟨[1, 1, 1, 1, 1]⟩
  correlate := ⟨[0]⟩
  remnant := nominalIn
  mTerm := ⟨[1, 1, 0]⟩
  inRemnant := [0]
  context := .a

/-- In (85a), *He introduced Sally to more friends than Peter's sister*, the correlate, the
object, is lower than the pronoun. -/
def ex85 : PhrasalComparative where
  matrix := introduced
  thanPhrase := ⟨[1, 1, 1, 1, 1]⟩
  correlate := ⟨[1, 1, 0]⟩
  remnant := nominalIn
  mTerm := ⟨[0]⟩
  inRemnant := [0]
  context := .a

/-- `vorgestellt` is the German clause *subject dative more people introduced*, with a trace at the
base of the *than*-phrase in the degree phrase. -/
def vorgestellt : Tree Cat Unit :=
  .node .S [np, .node .V [np, .node .V [.node .N [word .N, .trace 0 .P], word .V]]]

/-- In (87a), *Sie hat ihm mehr Leute vorgestellt als Peters Schwester*, with a nominative
remnant, the correlate, the subject, is higher than the pronoun. -/
def ex87a : PhrasalComparative where
  matrix := vorgestellt
  thanPhrase := ⟨[1, 1, 0, 1]⟩
  correlate := ⟨[0]⟩
  remnant := nominalIn
  mTerm := ⟨[1, 0]⟩
  inRemnant := [0]
  context := .a

/-- In (87b), *Er hat ihr mehr Leute vorgestellt als Peters Schwester*, with a dative remnant,
the correlate, the dative, is lower than the pronoun. -/
def ex87b : PhrasalComparative where
  matrix := vorgestellt
  thanPhrase := ⟨[1, 1, 0, 1]⟩
  correlate := ⟨[1, 0]⟩
  remnant := nominalIn
  mTerm := ⟨[0]⟩
  inRemnant := [0]
  context := .a

/-- `schaetzt subj obj` is the German clause *subject object more appreciates*, with a trace at the
base of the *than*-phrase in the degree adverb. -/
def schaetzt (subj obj : Tree Cat Unit) : Tree Cat Unit :=
  .node .S [subj, .node .V [obj, .node .V [.node .Adv [word .Adv, .trace 0 .P], word .V]]]

/-- In (90a), *Die Frau des Präsidenten schätzt die Öffentlichkeit mehr als ihn*, the correlate,
the object, is lower than the name. -/
def ex90 : PhrasalComparative where
  matrix := schaetzt nominalIn np
  thanPhrase := ⟨[1, 1, 0, 1]⟩
  correlate := ⟨[1, 0]⟩
  remnant := np
  mTerm := ⟨[0, 0]⟩
  inRemnant := []
  context := .b

/-- In (91a), *Die Öffentlichkeit schätzt die Frau des Präsidenten mehr als er*, the correlate,
the subject, is higher than the name. -/
def ex91 : PhrasalComparative where
  matrix := schaetzt np nominalIn
  thanPhrase := ⟨[1, 1, 0, 1]⟩
  correlate := ⟨[0]⟩
  remnant := np
  mTerm := ⟨[1, 0, 0]⟩
  inRemnant := []
  context := .b

/-- `phrasalData` pairs each phrasal comparative with its row. -/
def phrasalData : List (PhrasalComparative × Datum) :=
  [(ex83, Examples.ch4_83a), (ex85, Examples.ch4_85a), (ex87a, Examples.ch4_87a),
    (ex87b, Examples.ch4_87b), (ex90, Examples.ch4_90a), (ex91, Examples.ch4_91a)]

theorem rep_nominals (a : Analysis) : ∀ d ∈ phrasalData,
    (a.rep d.1).1.subtreeAt (a.rep d.1).2.1.toList = some np ∧
      (a.rep d.1).1.subtreeAt (a.rep d.1).2.2.toList = some np := by
  revert a; decide

theorem analysis_fits_iff (a : Analysis) :
    (∀ d ∈ phrasalData, a.Permits d.1 ↔ Attested d.2) ↔ a = .reduction := by
  revert a; decide

theorem direct_same (a : Analysis) (ha : a ≠ .reduction) :
    (a.Permits ex83 ↔ a.Permits ex85) ∧ (a.Permits ex87a ↔ a.Permits ex87b) ∧
      (a.Permits ex90 ↔ a.Permits ex91) := by
  revert a; decide

end Lechner2004
