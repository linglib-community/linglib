module

public import Linglib.Syntax.Minimalist.LateMerger
public import Studies.BakerVinokurova2010
public import Linglib.Data.Examples.Gong2022

/-!
# Gong (2022): Case in Wholesale Late Merger: Evidence from Mongolian Scrambling

This file formalizes [gong-2022]'s argument that Condition C reconstruction in Mongolian
scrambling tracks case rather than the A/Ā distinction or the subject status of the binder.
Under [takahashi-hulsey-2009]'s wholesale late merger a determiner moves alone and its restrictor
merges countercyclically at a chain position where the resulting DP receives case, so scrambling
bleeds Condition C exactly when the chain has a case position above the pronoun binder, the
paper's condition (2) (`Bleeds`). The hybrid case rules (26) make accusative a dependent case,
valued on an NP that an unmarked argumental NP of the same domain c-commands, nominative the
case finite T assigns, and dative nonstructural (`Site.DependentAcc`, `Site.Nominative`). Read
off the derivations (27b), (28b), (29c), (55), and (57), the chain positions of short,
intermediate, and long-distance scrambling predict every judgment of the pool
(`rows_reconstruction`): a dative binder is bled and a subject binder is not, while the
embedded-subject binder of (61) is bled because the matrix VP-adjoined position competes for case
with the matrix subject, which refutes [frank-lee-rambow-1996]'s Subject Binding Generalization
(`sbg_fails`) and is what an account by movement type cannot state (`is_not_uniform`). The same
dependent-case rule licenses accusative on an embedded subject exactly when a nominative matrix
competitor is present, section 5.1 (`acc_subjects`), and the Mongolian grammar differs from
[baker-vinokurova-2010]'s Sakha only in having no dependent dative
(`mongolian_differs_from_sakha_in_dat_only`).

## Implementation notes

The ditransitive's cases are read off a derivation (`ditransitive`), whose direct object shifts to
the specifier of vP for the paper's VP-edge site, and Sakha's off [baker-vinokurova-2010]'s. For the
scrambling chains, heights order the positions of a clause and, for clause-external scrambling, the
matrix clause above the embedded one. A site records the arguments of its spell-out domain with the
case they bear when the mover lands, so the presubject position sees a subject already valued
nominative, the paper's assumption that case is valued as soon as its conditions are met. A
lexically cased DP is licensed in its base position and a PP has no restrictor to late-merge, so
neither can be bled. The CP edge of an embedded clause is a step of successive-cyclic movement
without a case competitor.

## References

* [gong-2022]
* [takahashi-hulsey-2009]
* [baker-vinokurova-2010]
* [frank-lee-rambow-1996]
* [lebeaux-1988]
-/

@[expose] public section

namespace Gong2022

open Minimalist

/-! ### The hybrid case rules (26) at a landing site -/

/-- An argumental NP of a spell-out domain: its height and the case it bears, if any, when the
mover lands. -/
structure Arg where
  height : ℕ
  valued : Option Case
  deriving DecidableEq, Repr

/-- A landing site of a scrambling chain: its height, the arguments of its spell-out domain, and
whether it is the specifier finite T agrees into. -/
structure Site where
  height : ℕ
  domain : List Arg
  specTP : Bool := false
  deriving DecidableEq, Repr

/-- (26a): an unmarked argument of the domain c-commands the site, so a DP there is valued
accusative as a dependent case. -/
def Site.DependentAcc (s : Site) : Prop := ∃ a ∈ s.domain, s.height < a.height ∧ a.valued = none

/-- (26b): finite T values a DP at its specifier nominative when no unmarked argument is closer
to T. -/
def Site.Nominative (s : Site) : Prop :=
  s.specTP = true ∧ ∀ a ∈ s.domain, s.height < a.height → a.valued ≠ none

/-- A position where the late-merged restrictor's DP receives structural case. -/
def Site.HasCase (s : Site) : Prop := s.DependentAcc ∨ s.Nominative

instance (s : Site) : Decidable s.DependentAcc := inferInstanceAs (Decidable (∃ _ ∈ _, _))
instance (s : Site) : Decidable s.Nominative := inferInstanceAs (Decidable (_ ∧ _))
instance (s : Site) : Decidable s.HasCase := inferInstanceAs (Decidable (_ ∨ _))

/-- What scrambles: a DP with structural case, a DP with lexical dative, or a PP. -/
inductive Mover where
  | dp
  | lexicalDP
  | pp
  deriving DecidableEq, Repr

/-- Condition (2): scrambling bleeds Condition C when the mover is a DP whose restrictor can
receive structural case at a chain position above the binder. -/
def Bleeds (m : Mover) (chain : List Site) (binder : ℕ) : Prop :=
  m = .dp ∧ LateMergerBleeds Site.HasCase Site.height chain binder

instance (m : Mover) (chain : List Site) (binder : ℕ) : Decidable (Bleeds m chain binder) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### The positions of the paper's derivations -/

/-- The subject at the edge of the verb phrase, unmarked until T merges, above the dative
indirect object. -/
def subjectUnmarked : Arg := ⟨3, none⟩

/-- The dative indirect object. -/
def io : Arg := ⟨1, some .dat⟩

/-- The VP-edge position of (27b) and (28b): between the subject and the indirect object, valued
accusative by competition with the subject. -/
def vpEdge : Site := ⟨2, [subjectUnmarked, io], false⟩

/-- The presubject position of (29c): the subject below it is already nominative, and nothing
c-commands it. -/
def presubject : Site := ⟨4, [⟨3, some .nom⟩, io], false⟩

/-- The edge of the embedded CP, a step of successive-cyclic movement, (55b). -/
def cpEdge : Site := ⟨4, [], false⟩

/-- The matrix VP-adjoined position of (55c): above the matrix dative argument, below the
matrix subject, which has not yet been valued. -/
def matrixVP : Site := ⟨6, [⟨7, none⟩, ⟨5, some .dat⟩], false⟩

/-- The matrix presubject position of (57): the matrix subject is nominative by then. -/
def matrixPresubject : Site := ⟨8, [⟨7, some .nom⟩, ⟨5, some .dat⟩], false⟩

/-- The specifier of finite T in the passive (85b): the agent is instrumental, the goal dative,
so T values the derived subject nominative. -/
def specTP : Site := ⟨4, [⟨2, some .inst⟩, io], true⟩

/-! ### The Mongolian grammar of structural case (26) -/

/-- The Mongolian grammar of structural case: accusative on the lower of two NPs in the
    clause, nominative from T under Agree, and no dependent dative; genitive from D is
    [baker-vinokurova-2010]'s, kept for the comparison with Sakha. -/
def grammar : CaseAssigners where
  rules
    | .C => { low := some .acc }
    | _ => {}
  agreeCase
    | .T => some .nom
    | .D => some .gen
    | _ => none

open BakerVinokurova2010 (subjD objD goalD verb₂ littleV tense comp IsPhaseHead)

/-- A Mongolian ditransitive: the dative indirect object in the specifier of VP, and the direct
    object shifted above it to the edge of vP, below the subject. -/
def ditransitive : Derivation :=
  ⟨verb₂, [.em .left objD, .em .left goalD, .em .right littleV, .im objD .left,
    .em .left subjD, .em .right tense, .em .right comp]⟩

/-- The cases a grammar reads off a derivation, the indirect object `goalD` dative from its
    lexical head where `datIO` says so. -/
def casesOf (g : CaseAssigners) (d : Derivation) (datIO : Bool) :
    Option (Case.Valuation LexicalItem.Token (Case × Case.Mechanism)) :=
  d.externalize?.map fun t ↦
    g.assignOn .raising t (complementDomain .raising t ∅) IsPhaseHead
      (fun x ↦ if datIO && x = goalD then some .dat else none) (fun _ ↦ True) [subjD, objD, goalD]

/-- The cases of the Mongolian ditransitive. -/
def ditransitiveCases : Option (Case.Valuation LexicalItem.Token (Case × Case.Mechanism)) :=
  casesOf grammar ditransitive true

theorem do_gets_dependent_acc :
    ditransitiveCases.bind (·.valueOf objD) = some (.acc, .dependent) := by decide +kernel

theorem subject_gets_nom_by_agree :
    ditransitiveCases.bind (·.valueOf subjD) = some (.nom, .agree) := by decide +kernel

theorem io_has_lexical_case :
    ditransitiveCases.bind (·.valueOf goalD) = some (.dat, .lexical) := by decide +kernel

theorem vpEdge_dependentAcc :
    vpEdge.DependentAcc ∧ ¬ presubject.HasCase ∧
      (ditransitiveCases.bind (·.valueOf objD)).map (·.2) = some .dependent := by
  decide +kernel

/-! ### The scrambling constructions and their chains -/

/-- The scrambling constructions of the pool. -/
inductive Construction where
  /-- Short scrambling, the direct object over the indirect object. -/
  | SS
  /-- Intermediate scrambling, an object to the presubject position. -/
  | IS
  /-- Clause-external scrambling of an accusative embedded subject or of an embedded object,
  to the matrix presubject position. -/
  | LDS
  /-- Clause-external scrambling stopping at the matrix VP-adjoined position, (58). -/
  | intermediate
  /-- Scrambling of the dative indirect object over the subject, (79). -/
  | IO
  /-- Passivization, (85). -/
  | passive
  deriving DecidableEq, Repr

/-- The chain positions each construction makes available, in the paper's derivations. -/
def Construction.chain : Construction → List Site
  | .SS => [vpEdge]
  | .IS | .IO => [vpEdge, presubject]
  | .LDS => [cpEdge, matrixVP, matrixPresubject]
  | .intermediate => [cpEdge, matrixVP]
  | .passive => [specTP]

/-- The pronoun that binds the R-expression in the base order. -/
inductive Binder where
  | io
  | subject
  | matrixDat
  | matrixSubject
  | embeddedSubject
  deriving DecidableEq, Repr

/-- The binder's height. -/
def Binder.height : Binder → ℕ
  | .io => 1
  | .subject | .embeddedSubject => 3
  | .matrixDat => 5
  | .matrixSubject => 7

/-- Whether the binder is a subject, the Subject Binding Generalization's criterion. -/
def Binder.IsSubject : Binder → Prop
  | .subject | .matrixSubject | .embeddedSubject => True
  | .io | .matrixDat => False

instance (b : Binder) : Decidable b.IsSubject := by
  cases b <;> simp only [Binder.IsSubject] <;> infer_instance

/-! ### The pool -/

/-- A scrambled order: its construction, the base-order binder, the mover, and the worst mark
the paper prints on it (`??/*` counts as `*`). -/
structure Row where
  construction : Construction
  binder : Binder
  mover : Mover
  judgment : Judgment
  deriving DecidableEq, Repr

/-- The paper's obligatory reconstruction: the coindexed reading is rejected. -/
def Row.Reconstructs (r : Row) : Prop :=
  r.judgment = .ungrammatical ∨ r.judgment = .unacceptable

instance (r : Row) : Decidable r.Reconstructs := inferInstanceAs (Decidable (_ ∨ _))

def Row.ofDatum (ex : Datum) : Option Row := do
  let construction ← ex.parse? "construction"
    [("SS", Construction.SS), ("IS", .IS), ("ACC-SUBJ", .LDS), ("LDS", .LDS), ("PP-LDS", .LDS),
      ("ACC-SUBJ intermediate", .intermediate), ("LDS intermediate", .intermediate), ("IO", .IO),
      ("passive", .passive)]
  let binder ← ex.parse? "binder"
    [("IO", Binder.io), ("subject", .subject), ("matrix DAT", .matrixDat),
      ("matrix subject", .matrixSubject), ("embedded subject", .embeddedSubject)]
  let mover ← ex.parse? "mover" [("DP", Mover.dp), ("DP-lexical", .lexicalDP), ("PP", .pp)]
  pure ⟨construction, binder, mover, ex.judgments.foldl (· ⊓ ·) ex.judgment⟩

/-- The scrambled orders (18b) to (21b), (32b), (33), (40), (41), (58), (61), (79), (85b), (86),
(93b), and (94b). -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

example : rows.length = 16 := by decide

/-- Condition (2) with the hybrid case rules predicts every judgment: reconstruction is
obligatory exactly when no chain position above the binder receives case. -/
theorem rows_reconstruction :
    ∀ r ∈ rows, r.Reconstructs ↔ ¬ Bleeds r.mover r.construction.chain r.binder.height := by
  decide

/-- Intermediate scrambling of a DP to one landing site reconstructs in (20b) but not in (19b)
(Section 2.3). -/
theorem is_not_uniform :
    ∃ r₁ ∈ rows, ∃ r₂ ∈ rows, r₁.construction = .IS ∧ r₂.construction = .IS ∧
      r₁.mover = .dp ∧ r₂.mover = .dp ∧ ¬ r₁.Reconstructs ∧ r₂.Reconstructs := by
  decide

/-- The Subject Binding Generalization (24) fits the clause-internal data but fails for (61) and
(94b) (Section 4.2). -/
theorem sbg_fails :
    (∀ r ∈ rows, r.construction = .SS ∨ r.construction = .IS →
      (r.Reconstructs ↔ r.binder.IsSubject)) ∧
      (∃ r ∈ rows, r.binder = .embeddedSubject ∧ r.mover = .dp ∧ ¬ r.Reconstructs) ∧
      ∃ r ∈ rows, ¬ r.binder.IsSubject ∧ r.Reconstructs := by
  decide

/-! ### Section 5.1: accusative on embedded subjects -/

/-- The matrix argument that could compete with the embedded subject for case. -/
inductive Competitor where
  | nom
  | dat
  | absent
  deriving DecidableEq, Repr

/-- The embedded subject at the edge of its clause, in the matrix domain: the site (26a)
evaluates. -/
def Competitor.site : Competitor → Site
  | .nom => ⟨4, [⟨7, none⟩], false⟩
  | .dat => ⟨4, [⟨7, some .dat⟩], false⟩
  | .absent => ⟨4, [], false⟩

/-- An accusative-marked embedded subject with its matrix competitor and judgment. -/
structure AccRow where
  competitor : Competitor
  judgment : Judgment
  deriving DecidableEq, Repr

def AccRow.ofDatum (ex : Datum) : Option AccRow := do
  let competitor ← ex.parse? "competitor"
    [("NOM", Competitor.nom), ("DAT", .dat), ("none", .absent)]
  pure ⟨competitor, ex.judgment⟩

/-- (47), (48), (63), (64), and (65). -/
def accRows : List AccRow := Examples.all.filterMap AccRow.ofDatum

example : accRows.length = 5 := by decide

theorem acc_subjects :
    ∀ r ∈ accRows, r.judgment = .acceptable ↔ r.competitor.site.DependentAcc := by
  decide

/-! ### Section 5.3: dative is not a dependent case -/

theorem mongolian_differs_from_sakha_in_dat_only :
    grammar.rules .v = { BakerVinokurova2010.grammar.rules .v with high := none } ∧
    grammar.rules .C = BakerVinokurova2010.grammar.rules .C ∧
    grammar.agreeCase = BakerVinokurova2010.grammar.agreeCase :=
  ⟨rfl, rfl, funext fun c ↦ by cases c <;> rfl⟩

theorem mongolian_derives_no_dative :
    (∀ s ∈ casesOf grammar (BakerVinokurova2010.ditransitiveClause true) false, ∀ p ∈ s,
      p.2.map (·.1) ≠ some .dat) ∧
    (casesOf grammar (BakerVinokurova2010.ditransitiveClause true) false).bind (·.valueOf goalD) ≠
      (casesOf BakerVinokurova2010.grammar (BakerVinokurova2010.ditransitiveClause true) false).bind
        (·.valueOf goalD) := by
  decide +kernel

end Gong2022
