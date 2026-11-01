module

public import Linglib.Data.Examples.Chomsky1981
public import Linglib.Data.Examples.Readers
public import Linglib.Syntax.Binding.Tree
public import Linglib.Syntax.Tree.Projection
public import Studies.Reinhart1976
public import Linglib.Fragments.English.Adpositions
public import Linglib.Fragments.English.Auxiliaries
public import Linglib.Fragments.English.Determiners
public import Linglib.Fragments.English.Nouns
public import Linglib.Fragments.English.Pronouns
public import Linglib.Fragments.English.Verbs.Inventory

/-!
# Chomsky (1981): the binding theory

This file formalizes the binding theory of *Lectures on Government and Binding*: an anaphor is bound
in its governing category, a pronominal is free there, and an R-expression is free. The positions
are the noun phrases of a phrase-structure tree, command is c-command, and a reading is the
dependency among the noun phrases it coindexes; the book's notions are defined from these. The
SUBJECT of a finite clause is the agreement of its inflection, that of any other clause or of a noun
phrase its subject; a SUBJECT is accessible to a position it c-commands unless the position lies
inside the node that shares its index; and the governing category of a position is the smallest node
with a SUBJECT accessible to it. The book's c-command [is c-command on noun
phrases](##cCommands12_iff) but for the mother. One domain serving both principles, [an anaphor and
a pronominal are in complementary distribution](##condition_iff_not_condition_pronoun), and the
definitions [decide the book's examples of anaphors and pronouns in noun
phrases](##acceptable_iff_licit) but *John read his book*, which [the binding theory
excludes](##judgment_92v), as the book observes.

## Implementation notes

* A clause is `NP INFL VP`, its inflection a node of category `Aux` that is finite, and so bears
  agreement, when its form is. A past inflection has no form of its own.
* A noun phrase is a maximal projection labelled `N`, or a noun phrase with a subject, labelled
  `Det` with the subject as its first daughter. An article is no noun phrase.
* The governing category drops the requirement that it contain a governor of the position, which
  the book observes to be idle for governed positions, as all those of the examples are.
* Accessibility consults only the index agreement shares with the subject, not the indices of a
  reading; none of the examples turns on the others.
* Material with no bearing on binding is left out of the trees: complementizers and *on sale*.
  Head nouns are singular tokens, the number of a noun phrase playing no part, and *about* and the
  copula, which have no fragment entries, are plain tokens.
* Page numbers are those of the seventh edition (1993).

## TODO

* The remaining binding examples of chapter 3: the pleonastic *it* and *there* of the extraposed
  clauses, the gerunds, and PRO, which needs the governor the governing category drops here.

## References

* [chomsky-1981]
* [reinhart-1976]
-/

@[expose] public section

namespace Chomsky1981

open Morphology (Word)
open Core.Order PhraseStructure PhraseStructure.Tree Binding
open RoseTree (CCommands)

/-! ### Representations -/

/-- `word c w` is the word `w` of category `c`. -/
abbrev word (c : Cat) (w : Word) : Tree Cat Word := .terminal c w

/-- `np w` is the one-word noun phrase `w`. -/
abbrev np (w : Word) : Tree Cat Word := word .N w

/-- `nphrase cs` is the noun phrase of the daughters `cs`, its head noun among them. -/
abbrev nphrase (cs : List (Tree Cat Word)) : Tree Cat Word := .node .N cs

/-- `poss w x` is the noun phrase with the subject `w`. -/
abbrev poss (w : Word) (x : Tree Cat Word) : Tree Cat Word := .node .Det [np w, x]

/-- `pp p x` is the prepositional phrase of `p` and `x`. -/
abbrev pp (p : Word) (x : Tree Cat Word) : Tree Cat Word := .node .P [word .P p, x]

/-- `clause subj infl v cs` is the clause `NP INFL VP` of the subject `subj`, the inflection
`infl` and the verb phrase of `v` and `cs`. -/
abbrev clause (subj : Tree Cat Word) (infl v : Word) (cs : List (Tree Cat Word)) :
    Tree Cat Word :=
  .node .S [subj, word .Aux infl, .node .V (word .V v :: cs)]

/-- An inflection is finite, and so bears agreement, when its form is finite. -/
def IsFinite (w : Word) : Prop := w.features .verbForm = some .Fin

instance : DecidablePred IsFinite := fun _ ↦ inferInstanceAs (Decidable (_ = _))

variable {t : Tree Cat Word}

/-! ### Noun phrases -/

/-- The noun phrases of `t` with their positions: the maximal projections labelled `N` and the
phrases labelled `Det`, which have subjects. -/
def nominals (t : Tree Cat Word) : List (TreePath × Tree Cat Word) :=
  t.positionedSubtrees.filter fun x ↦
    x.1 ∈ maximalProjectionsAt t ∧ (Tree.cat x.2 = .N ∨ Tree.cat x.2 = .Det ∧ x.2.children ≠ [])

/-- The type of noun phrases of `t`. -/
abbrev Nominal (t : Tree Cat Word) : Type := {x // x ∈ nominals t}

/-- The word of a one-word noun phrase. -/
def word? : Tree Cat Word → Option Word
  | PhraseStructure.Tree.terminal _ w => some w
  | _ => none

/-- The binding class of a noun phrase: that of its word, and an R-expression's for a phrase. -/
def classOf (x : Nominal t) : Option BindingClass :=
  (word? x.1.2).elim (some .rExpression) bindingClassOf

/-! ### The governing category -/

/-- The SUBJECT of a node: the agreement of the inflection of a finite clause, the subject of
any other clause, and the subject of a noun phrase that has one. -/
def subject (t : Tree Cat Word) (m : TreePath) : Option TreePath :=
  match t[m]? with
  | some (PhraseStructure.Tree.node .S [_, PhraseStructure.Tree.terminal _ infl, _]) =>
    some ⟨m.toList ++ [if IsFinite infl then 1 else 0]⟩
  | some (PhraseStructure.Tree.node .Det (_ :: _)) => some ⟨m.toList ++ [0]⟩
  | _ => none

/-- Agreement shares the index of the subject it governs: the inflection that is the SUBJECT of
its clause bears the index of the clause's subject. -/
def agreement (t : Tree Cat Word) (s : TreePath) : Option TreePath :=
  if s.toList.getLast? = some 1 ∧ subject t s.parent = some s then
    some ⟨s.parent.toList ++ [0]⟩
  else none

/-- The configuration on the noun phrases of `t` takes c-command, and the domain of a position
is its governing category, the smallest node with a SUBJECT accessible to it. -/
abbrev configuration (t : Tree Cat Word) : Configuration (Nominal t) :=
  (t.configuration (t.withAccessibleSubject (subject t) (agreement t))).comap (·.1.1)

/-- The book's c-command, for a noun phrase `a`, whose projection line is `a` alone: `a` does not
contain `b`, and every node properly dominating `a` dominates `b`. -/
def CCommands12 (a b : TreePath) : Prop := ¬ a ≤ b ∧ ∀ d < a, d ≤ b

/-- The book's c-command of a noun phrase is c-command, save that it also relates the noun phrase
to its mother ((12), p. 166). -/
theorem cCommands12_iff {a b : TreePath} (ha : a ≠ ⊥) (hp : t.IsBranchingAt a.parent) :
    CCommands12 a b ↔ t.CCommands a b ∨ b = a.parent := by
  have hlt : a.parent < a := by
    rw [← TreePath.pred_eq_parent]
    exact Order.pred_lt_of_not_isMin (by simpa [isMin_iff_eq_bot] using ha)
  have hall : (∀ d < a, d ≤ b) ↔ a.parent ≤ b := by
    refine ⟨fun h ↦ h _ hlt, fun h d hd ↦ le_trans ?_ h⟩
    rw [← TreePath.pred_eq_parent]
    exact Order.le_pred_of_lt hd
  rw [CCommands12, hall, RoseTree.cCommands_iff_parent_lt ha hp]
  constructor
  · rintro ⟨hab, hpb⟩
    rcases hpb.lt_or_eq with hpb | rfl
    exacts [.inl ⟨hpb, hab⟩, .inr rfl]
  · rintro (⟨hpb, hab⟩ | rfl)
    exacts [⟨hab, hpb.le⟩, ⟨fun h ↦ hlt.not_ge h, le_rfl⟩]

/-! ### Licit dependencies -/

/-- The dependency `L` is licit when the noun phrases it relates agree and it satisfies the three
principles, with no anaphor exempt. -/
def Licit (t : Tree Cat Word) (L : Nominal t → Nominal t → Prop) : Prop :=
  (∀ a b, L a b → ∀ v ∈ word? a.1.2, ∀ w ∈ word? b.1.2, HasPhi.Agree v w) ∧
    (configuration t).Satisfies L ∅ classOf

instance (L : Nominal t → Nominal t → Prop) [DecidableRel L] : Decidable (Licit t L) :=
  have : Decidable ((configuration t).Satisfies L ∅ classOf) := inferInstance
  have : Decidable (∀ a b, L a b → ∀ v ∈ word? a.1.2, ∀ w ∈ word? b.1.2, HasPhi.Agree v w) :=
    inferInstance
  inferInstanceAs (Decidable (_ ∧ _))

/-- An anaphor that nothing in its governing category c-commands makes every dependency illicit,
which excludes an anaphoric subject of a finite clause. -/
theorem not_licit_of_not_locallyCommanded {b : Nominal t} {c : BindingClass}
    (hb : classOf b = some c) (hc : c.IsAnaphor) (hl : ¬ (configuration t).LocallyCommanded b)
    (L : Nominal t → Nominal t → Prop) : ¬ Licit t L :=
  fun ⟨_, h⟩ ↦ hl ((Configuration.condition_empty_iff hc).1 (h b c hb)).2

/-- One domain serving both principles, an anaphor meets Principle A exactly where a pronominal
in its place would violate Principle B, under any dependency ((12), p. 188). -/
theorem condition_iff_not_condition_pronoun {b : Nominal t} {c : BindingClass} (hc : c.IsAnaphor)
    (L : Nominal t → Nominal t → Prop) :
    (configuration t).Condition L ∅ b c ↔ ¬ (configuration t).Condition L ∅ b .pronoun :=
  Configuration.condition_iff_not_condition_pronoun hc (Set.notMem_empty b) rfl

-- For two noun phrases related to each other alone, Principle C is Reinhart's restriction (10b)
-- [reinhart-1976].
theorem permits_iff {a b : Nominal t} (hab : a ≠ b) (pron : List TreePath) :
    Reinhart1976.Permits (CCommands t) pron a.1.1 b.1.1 ↔
      (b.1.1 ∉ pron → ¬ (configuration t).Bound (pair a b) b) ∧
        (a.1.1 ∉ pron → ¬ (configuration t).Bound (pair a b) a) := by
  rw [Configuration.bound_pair_iff hab, pair_comm, Configuration.bound_pair_iff hab.symm]
  simp only [Reinhart1976.Permits, not_imp_not]
  rfl

/-! ### The examples -/

/-- A reading of an example: its representation and the two noun phrases the book coindexes. -/
structure Reading where
  /-- The representation. -/
  tree : Tree Cat Word
  /-- The antecedent. -/
  antecedent : TreePath
  /-- The noun phrase coindexed with the antecedent. -/
  dependent : TreePath

/-- A reading is licit when relating its two noun phrases, and no others, is licit. -/
def Reading.Licit (r : Reading) : Prop :=
  ∃ a b : Nominal r.tree, a.1.1 = r.antecedent ∧ b.1.1 = r.dependent ∧
    Chomsky1981.Licit r.tree (pair a b)

instance (r : Reading) : Decidable r.Licit :=
  have (a b : Nominal r.tree) : Decidable (Chomsky1981.Licit r.tree (pair a b)) := inferInstance
  inferInstanceAs (Decidable (∃ (_ : Nominal r.tree) (_ : Nominal r.tree), _ ∧ _ ∧ _))

section Examples

open English

abbrev john := Nouns.john.toWord
abbrev i_ := Pronouns.i.toWord
abbrev me_ := Pronouns.me.toWord
abbrev my := Pronouns.my.toWord
abbrev him := Pronouns.him.toWord
abbrev his := Pronouns.his.toWord
abbrev they := Pronouns.they.toWord
abbrev eachOther := Pronouns.eachOther.toWord
abbrev picture := Nouns.picture.toWordSg
abbrev book := Nouns.book.toWordSg
abbrev story := Nouns.story.toWordSg
abbrev a_ := Determiners.a.toWord
abbrev the := Determiners.the.toWord
abbrev of_ := Adpositions.of_.toWord
abbrev about := Word.mk' "about" .ADP
abbrev be := Word.mk' "be" .VERB
abbrev past : Word := { form := "", cat := .AUX, features := Auxiliaries.finite .Past }
abbrev to_ := Auxiliaries.toInf
abbrev would := Auxiliaries.would.toWord
abbrev saw := Verbs.see.toWord .past
abbrev read := Verbs.read.toWord .past
abbrev thought := Verbs.think.toWord .past
abbrev heard := Verbs.hear.toWord .past
abbrev hear := Verbs.hear.toWord .base
abbrev expected := Verbs.expect.toWord .past

/-- *John saw my picture of him.* -/
def r92i : Reading :=
  ⟨clause (np john) past saw [poss my (nphrase [word .N picture, pp of_ (np him)])], ⟨[0]⟩,
    ⟨[2, 1, 1, 1, 1]⟩⟩

/-- *I saw John's picture of him.* -/
def r92ii : Reading :=
  ⟨clause (np i_) past saw [poss john (nphrase [word .N picture, pp of_ (np him)])], ⟨[2, 1, 0]⟩,
    ⟨[2, 1, 1, 1, 1]⟩⟩

/-- *John saw a picture of him.* -/
def r92iii : Reading :=
  ⟨clause (np john) past saw [nphrase [word .Det a_, word .N picture, pp of_ (np him)]], ⟨[0]⟩,
    ⟨[2, 1, 2, 1]⟩⟩

/-- *John thought I saw a picture of him.* -/
def r92iv : Reading :=
  ⟨clause (np john) past thought
      [clause (np i_) past saw [nphrase [word .Det a_, word .N picture, pp of_ (np him)]]],
    ⟨[0]⟩, ⟨[2, 1, 2, 1, 2, 1]⟩⟩

/-- *John read his book.* -/
def r92v : Reading :=
  ⟨clause (np john) past read [poss his (nphrase [word .N book])], ⟨[0]⟩, ⟨[2, 1, 0]⟩⟩

/-- *John thought I saw his book.* -/
def r92vi : Reading :=
  ⟨clause (np john) past thought [clause (np i_) past saw [poss his (nphrase [word .N book])]],
    ⟨[0]⟩, ⟨[2, 1, 2, 1, 0]⟩⟩

/-- *They read each other's books.* -/
def r93 : Reading :=
  ⟨clause (np they) past read [poss eachOther (nphrase [word .N book])], ⟨[0]⟩, ⟨[2, 1, 0]⟩⟩

/-- *They heard my stories about each other.* -/
def r78my : Reading :=
  ⟨clause (np they) past heard [poss my (nphrase [word .N story, pp about (np eachOther)])],
    ⟨[0]⟩, ⟨[2, 1, 1, 1, 1]⟩⟩

/-- *They heard the stories about each other.* -/
def r78the : Reading :=
  ⟨clause (np they) past heard [nphrase [word .Det the, word .N story, pp about (np eachOther)]],
    ⟨[0]⟩, ⟨[2, 1, 2, 1]⟩⟩

/-- *They heard stories about each other.* -/
def r78none : Reading :=
  ⟨clause (np they) past heard [nphrase [word .N story, pp about (np eachOther)]], ⟨[0]⟩,
    ⟨[2, 1, 1, 1]⟩⟩

/-- *They expected me to hear stories about each other.* -/
def r79i : Reading :=
  ⟨clause (np they) past expected
      [clause (np me_) to_ hear [nphrase [word .N story, pp about (np eachOther)]]],
    ⟨[0]⟩, ⟨[2, 1, 2, 1, 1, 1]⟩⟩

/-- *They expected that pictures of each other would be on sale.* -/
def r79ii : Reading :=
  ⟨clause (np they) past expected
      [clause (nphrase [word .N picture, pp of_ (np eachOther)]) would be []],
    ⟨[0]⟩, ⟨[2, 1, 0, 1, 1]⟩⟩

/-- *They thought I expected that pictures of each other would be on sale.* -/
def r80 : Reading :=
  ⟨clause (np they) past thought [clause (np i_) past expected
      [clause (nphrase [word .N picture, pp of_ (np eachOther)]) would be []]],
    ⟨[0]⟩, ⟨[2, 1, 2, 1, 0, 1, 1]⟩⟩

end Examples

/-- The examples with their readings. -/
def rows : List (Datum × Reading) :=
  [(Examples.ex_92i, r92i), (Examples.ex_92ii, r92ii), (Examples.ex_92iii, r92iii),
    (Examples.ex_92iv, r92iv), (Examples.ex_92v, r92v), (Examples.ex_92vi, r92vi),
    (Examples.ex_93, r93), (Examples.ex_78_my, r78my), (Examples.ex_78_the, r78the),
    (Examples.ex_78_none, r78none), (Examples.ex_79i, r79i), (Examples.ex_79ii, r79ii),
    (Examples.ex_80, r80)]

theorem map_fst_rows : rows.map Prod.fst = Examples.all := rfl

theorem mem_nominals_rows : ∀ p ∈ rows, p.2.antecedent ∈ (nominals p.2.tree).map Prod.fst ∧
    p.2.dependent ∈ (nominals p.2.tree).map Prod.fst := by
  decide +kernel

/-- The definitions decide the binding examples of chapter 3 but (92v): each is acceptable
exactly when its reading is licit. -/
theorem acceptable_iff_licit :
    ∀ p ∈ rows, p.1 ≠ Examples.ex_92v → (p.1.judgment = .acceptable ↔ p.2.Licit) := by
  decide +kernel

-- pp. 213-214: in (79ii) the SUBJECT of the embedded clause is its agreement, which shares the
-- index of the subject containing *each other* and so is not accessible to it; the matrix
-- clause, whose agreement is, is the governing category.
theorem governingCategory_79ii :
    subject r79ii.tree ⟨[2, 1]⟩ = some ⟨[2, 1, 1]⟩ ∧
      agreement r79ii.tree ⟨[2, 1, 1]⟩ = some ⟨[2, 1, 0]⟩ ∧
      ⟨[2, 1]⟩ ∉ r79ii.tree.withAccessibleSubject (subject r79ii.tree) (agreement r79ii.tree)
        r79ii.dependent ∧
      ⟨[]⟩ ∈ r79ii.tree.withAccessibleSubject (subject r79ii.tree) (agreement r79ii.tree)
        r79ii.dependent := by
  decide +kernel

/-- *John read his book* is acceptable, but the binding theory excludes it, the clause being the
governing category of the possessive pronoun ((92v), p. 217). -/
theorem judgment_92v : Examples.ex_92v.judgment = .acceptable ∧ ¬ r92v.Licit := by
  decide +kernel

end Chomsky1981
