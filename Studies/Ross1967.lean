module

public import Linglib.Syntax.Cat
public import Linglib.Syntax.Tree.Projection
public import Linglib.Data.Examples.Ross1967

/-!
# Ross (1967): Constraints on Variables in Syntax

Ross's constraints on the variables of reordering transformations, the Complex NP Constraint, the
Coordinate Structure Constraint, the Left Branch Condition and the Sentential Subject Constraint,
are violated when a movement crosses the configuration they name in a constituent-structure tree.
[A chopping rule's example is acceptable exactly when it violates none](##Ross1967.chopping_rows),
and [a copying rule's examples are acceptable though each crosses an
island](##Ross1967.copying_rows). On Ross's complex NP, a noun phrase over a noun phrase and a
sentence, [the outer phrase is lexically headed exactly when the inner one
is](##Ross1967.hasLexicalHead_complexNP), so leaving its sentence [violates the CNPC under a
noun](##Ross1967.Movement.cnpc_of_complexNP) but [not under *it*](##Ross1967.cnpc_lexical_head).

## Implementation notes

Trees carry the categories of `PhraseStructure.Cat`, which have no levels: a noun phrase is a node
of category `N`, a coordinate structure a node of category `Conj` headed by its conjunction word,
whose other daughters are the conjuncts. A noun phrase has a lexical head noun when its lexical
head (`PhraseStructure.IsLexicalHeadOf`) is a word, the `[+N, +Lex]` node of Ross's diagram of the
complex NP. The library's lexical head is any minimal projection, and `[N it]`, whose pronoun has
category `Pron` and not `N`, is one; so the abstract pronoun *it* is not `[+Lex]`, and neither is
any other pronoun or proper name. The trees are the dissertation's diagrams reduced to the
categories the constraints mention, with the moved constituent in its source position. A relative
clause or the clause in apposition to an abstract noun is the sister of the noun phrase it modifies
under a further noun phrase, the `[NP NP S]` structure Ross argues for. Questions and
topicalizations land at the root and relativizations at the relative clause. Dominance in the
Sentential Subject Constraint is read as immediate, the configuration of a sentence exhaustively
dominated by a subject NP, so that the constraint does not reach a clause inside a relative clause
on a subject. The A-over-A principle, the pied-piping convention, upward boundedness, and the
definition of islands as the domains of chopping rules are not formalized.

## References

* [ross-1967]
-/

@[expose] public section

namespace Ross1967

open PhraseStructure Core.Order
open PhraseStructure.Cat (N V P Adj Conj)

/-! ### Trees and movements -/

/-- A word of a part of speech. -/
def w (pos : UD.UPOS) (form : String) : Tree Cat String := .terminal (.lex pos) form

/-- A node of `t` has a lexical head when its lexical head is a word. The noun *claim* is the
lexical head of `[N [N the claim] S]`; the head relation of `[N [N it] S]` stops at `[N it]`, which
is minimal but not a word. -/
def HasLexicalHead (t : Tree Cat String) (p : List ℕ) : Prop :=
  ∃ x ∈ t.positionedTerminals, IsLexicalHeadOf (Tree.HeadDaughterAt t) x.1 ⟨p⟩

instance (t : Tree Cat String) (p : List ℕ) : Decidable (HasLexicalHead t p) :=
  inferInstanceAs (Decidable (∃ x ∈ _, _))

/-- On Ross's complex NP, a noun phrase over a noun phrase and a sentence, the inner noun phrase is
the head daughter, so the outer one has a lexical head exactly when the inner one does. -/
theorem hasLexicalHead_complexNP {t : Tree Cat String} {p : List ℕ} {inner s : Tree Cat String}
    (ht : t[p]? = some (Tree.node N [inner, s])) (hi : inner.cat = N) (hs : s.cat = .S) :
    HasLexicalHead t p ↔ HasLexicalHead t (p ++ [0]) := by
  have hmd : Tree.HeadDaughterAt t ⟨p⟩ ⟨p ++ [0]⟩ :=
    ⟨0, by simp [Tree.headIndexAt, Tree.headIndex?, ht, List.zipIdx, hi, hs], rfl⟩
  simp only [HasLexicalHead, isLexicalHeadOf_iff_of_rel (headDaughterRel_rightUnique _) hmd]

/-- A movement in a tree records the position of the moved constituent and the position it
lands at. -/
structure Movement where
  tree : Tree Cat String
  source : List ℕ
  landing : List ℕ

namespace Movement

variable (m : Movement)

/-- The subtree at a position. -/
def at? (p : List ℕ) : Option (Tree Cat String) := m.tree[p]?

/-- The category at a position. -/
def cat? (p : List ℕ) : Option Cat := (m.at? p).map Tree.cat

/-- The positions the movement crosses are the strict ancestors of the source that do not
dominate the landing site, the constituents the moved element is moved out of. -/
def crossed : List (List ℕ) :=
  m.source.inits.filter fun p ↦ p ≠ m.source ∧ ¬ p <+: m.landing

/-- A conjunct is a daughter of a coordinate structure other than its head, the conjunction. -/
def IsConjunct (p : List ℕ) : Prop :=
  m.cat? p.dropLast = some Conj ∧ ¬ Tree.HeadDaughterAt m.tree ⟨p.dropLast⟩ ⟨p⟩

instance (p : List ℕ) : Decidable (m.IsConjunct p) := inferInstanceAs (Decidable (_ ∧ _))

/-- (4.20): the Complex NP Constraint is violated when the movement leaves a noun phrase with a
lexical head noun and a sentence that the noun phrase dominates. -/
def CNPC : Prop :=
  ∃ np ∈ m.crossed, m.cat? np = some N ∧ HasLexicalHead m.tree np ∧
    ∃ s ∈ m.crossed, np <+: s ∧ m.cat? s = some .S

/-- The Coordinate Structure Constraint is violated when the moved element is a conjunct leaving its
coordinate structure, or the movement leaves a conjunct. -/
def CSC : Prop :=
  (m.IsConjunct m.source ∧ m.source.dropLast ∈ m.crossed) ∨
    ∃ c ∈ m.crossed, m.IsConjunct c

/-- The Sentential Subject Constraint is violated when the movement leaves a sentence immediately
dominated by a noun phrase that is itself immediately dominated by a sentence. -/
def SSC : Prop :=
  ∃ s ∈ m.crossed, m.cat? s = some .S ∧ m.cat? s.dropLast = some N ∧
    m.cat? s.dropLast.dropLast = some .S

/-- The Left Branch Condition is violated when the moved element is a noun phrase that is the
leftmost daughter of a noun phrase the movement leaves. -/
def LBC : Prop :=
  m.cat? m.source = some N ∧ m.source.getLast? = some 0 ∧
    m.cat? m.source.dropLast = some N ∧ m.source.dropLast ∈ m.crossed

instance : Decidable m.CNPC := by unfold CNPC; infer_instance
instance : Decidable m.CSC := by unfold CSC; infer_instance
instance : Decidable m.SSC := by unfold SSC; infer_instance
instance : Decidable m.LBC := by unfold LBC; infer_instance

/-- The movement violates one of the four constraints. -/
def Violates : Prop := m.CNPC ∨ m.CSC ∨ m.SSC ∨ m.LBC

instance : Decidable m.Violates := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

variable {m}

/-- Leaving the sentence of Ross's complex NP violates the Complex NP Constraint when the inner
noun phrase has a lexical head. -/
theorem cnpc_of_complexNP {np : List ℕ} {inner s : Tree Cat String}
    (ht : m.at? np = some (Tree.node N [inner, s])) (hi : inner.cat = N) (hs : s.cat = .S)
    (hnp : np ∈ m.crossed) (hs' : np ++ [1] ∈ m.crossed)
    (hlex : HasLexicalHead m.tree (np ++ [0])) : m.CNPC :=
  have ht' : m.tree[np]? = some (Tree.node N [inner, s]) := ht
  ⟨np, hnp, by simp [cat?, ht], (hasLexicalHead_complexNP ht' hi hs).2 hlex, np ++ [1], hs',
    List.prefix_append _ _, by simp [cat?, at?, RoseTree.getElem?_append, ht', hs]⟩

end Movement

/-! ### The dissertation's examples -/

/-- In *This is a hat which I'm going to see to it that my wife buys* the relativized NP is in a
clause in construction with the abstract pronoun *it*. -/
def seeToIt : Tree Cat String :=
  .node .S [.node N [w .PRON "this"],
    .node V [w .AUX "is",
      .node N [.node N [w .DET "a", w .NOUN "hat"],
        .node .S [.node N [w .PRON "I"],
          .node V [w .AUX "am", w .VERB "going",
            .node V [w .PART "to", w .VERB "see",
              .node P [w .ADP "to",
                .node N [.node N [w .PRON "it"],
                  .node .S [w .SCONJ "that", .node N [w .PRON "my", w .NOUN "wife"],
                    .node V [w .VERB "buys", .node N [w .PRON "which"]]]]]]]]]]]

/-- In *Who does Phineas know a girl who is jealous of?* the questioned NP is inside the relative
clause on *girl*. -/
def phineas : Tree Cat String :=
  .node .S [.node N [w .PROPN "Phineas"],
    .node V [w .VERB "knows",
      .node N [.node N [w .DET "a", w .NOUN "girl"],
        .node .S [.node N [w .PRON "who"],
          .node V [w .AUX "is",
            .node Adj [w .ADJ "jealous", .node P [w .ADP "of", .node N [w .PRON "who"]]]]]]]]

/-- The relative clause of *the hat which I believed the claim that Otto was wearing*. -/
def hatClaim : Tree Cat String :=
  .node .S [.node N [.node N [w .DET "the", w .NOUN "hat"],
      .node .S [.node N [w .PRON "I"],
        .node V [w .VERB "believed",
          .node N [.node N [w .DET "the", w .NOUN "claim"],
            .node .S [w .SCONJ "that", .node N [w .PROPN "Otto"],
              .node V [w .AUX "was", w .VERB "wearing", .node N [w .PRON "which"]]]]]]],
    .node V [w .AUX "is", w .ADJ "red"]]

/-- The relative clause of *the hat which I believed that Otto was wearing*. -/
def hatThat : Tree Cat String :=
  .node .S [.node N [.node N [w .DET "the", w .NOUN "hat"],
      .node .S [.node N [w .PRON "I"],
        .node V [w .VERB "believed",
          .node .S [w .SCONJ "that", .node N [w .PROPN "Otto"],
            .node V [w .AUX "was", w .VERB "wearing", .node N [w .PRON "which"]]]]]],
    .node V [w .AUX "is", w .ADJ "red"]]

/-- In *What sofa will he put the chair between some table and?* the questioned NP is a
conjunct. -/
def sofa : Tree Cat String :=
  .node .S [.node N [w .PRON "he"],
    .node V [w .VERB "put", .node N [w .DET "the", w .NOUN "chair"],
      .node P [w .ADP "between",
        .node Conj [.node N [w .DET "some", w .NOUN "table"], w .CCONJ "and",
          .node N [w .DET "what", w .NOUN "sofa"]]]]]

/-- *The lute which Henry plays and sings madrigals* relativizes out of a conjoined VP. -/
def lute : Tree Cat String :=
  .node .S [.node N [.node N [w .DET "the", w .NOUN "lute"],
      .node .S [.node N [w .PROPN "Henry"],
        .node Conj [.node V [w .VERB "plays", .node N [w .PRON "which"]], w .CCONJ "and",
          .node V [w .VERB "sings", .node N [w .NOUN "madrigals"]]]]],
    .node V [w .AUX "is", w .ADJ "warped"]]

/-- *Which trombone did the nurse polish and the plumber computed my tax?* questions out of a
conjoined sentence. -/
def trombone : Tree Cat String :=
  .node .S [.node Conj [
    .node .S [.node N [w .DET "the", w .NOUN "nurse"],
      .node V [w .VERB "polish", .node N [w .DET "which", w .NOUN "trombone"]]],
    w .CCONJ "and",
    .node .S [.node N [w .DET "the", w .NOUN "plumber"],
      .node V [w .VERB "computed", .node N [w .PRON "my", w .NOUN "tax"]]]]]

/-- In *The boy whose guardian's employer we elected president* the possessor NPs are nested on
left branches. -/
def guardian : Tree Cat String :=
  .node .S [.node N [.node N [w .DET "the", w .NOUN "boy"],
      .node .S [.node N [w .PRON "we"],
        .node V [w .VERB "elected",
          .node N [.node N [.node N [w .PRON "whose"], w .NOUN "guardian's"],
            w .NOUN "employer"],
          .node N [w .NOUN "president"]]]],
    .node V [w .VERB "ratted", .node P [w .ADP "on", .node N [w .PRON "us"]]]]

/-- The predicate of the teacher sentences. -/
def battleax : Tree Cat String :=
  .node V [w .AUX "is",
    .node N [w .DET "a", w .ADJ "crusty", w .ADJ "old", w .NOUN "battleax"]]

/-- *that the principal would fire who*. -/
def fireClause : Tree Cat String :=
  .node .S [w .SCONJ "that", .node N [w .DET "the", w .NOUN "principal"],
    .node V [w .AUX "would", w .VERB "fire", .node N [w .PRON "who"]]]

/-- *The teacher who the reporters expected that the principal would fire*. -/
def teacherActive : Tree Cat String :=
  .node .S [.node N [.node N [w .DET "the", w .NOUN "teacher"],
      .node .S [.node N [w .DET "the", w .NOUN "reporters"],
        .node V [w .VERB "expected", fireClause]]],
    battleax]

/-- In *The teacher who that the principal would fire was expected by the reporters* the
that-clause is a sentential subject. -/
def teacherPassive : Tree Cat String :=
  .node .S [.node N [.node N [w .DET "the", w .NOUN "teacher"],
      .node .S [.node N [fireClause],
        .node V [w .AUX "was", w .VERB "expected",
          .node P [w .ADP "by", .node N [w .DET "the", w .NOUN "reporters"]]]]],
    battleax]

/-- In *The teacher who it was expected by the reporters that the principal would fire* the
that-clause is extraposed. -/
def teacherExtraposed : Tree Cat String :=
  .node .S [.node N [.node N [w .DET "the", w .NOUN "teacher"],
      .node .S [.node N [w .PRON "it"],
        .node V [w .AUX "was", w .VERB "expected",
          .node P [w .ADP "by", .node N [w .DET "the", w .NOUN "reporters"]], fireClause]]],
    battleax]

/-- *Of which cars were the hoods damaged by the explosion?* moves a subconstituent of a phrasal
subject. -/
def hoods : Tree Cat String :=
  .node .S [.node N [w .DET "the", w .NOUN "hoods",
      .node P [w .ADP "of", .node N [w .DET "which", w .NOUN "cars"]]],
    .node V [w .AUX "were", w .VERB "damaged",
      .node P [w .ADP "by", .node N [w .DET "the", w .NOUN "explosion"]]]]

/-- In *My father, the man he works with in Boston is going to tell the police …* the
dislocated NP is the subject of a relative clause. -/
def father : Tree Cat String :=
  .node .S [.node N [.node N [w .DET "the", w .NOUN "man"],
      .node .S [.node N [w .PRON "my", w .NOUN "father"],
        .node V [w .VERB "works", .node P [w .ADP "with", .node N [w .PRON "who"]],
          .node P [w .ADP "in", .node N [w .PROPN "Boston"]]]]],
    .node V [w .AUX "is", w .VERB "going",
      .node P [w .ADP "to", .node V [w .VERB "tell", .node N [w .DET "the", w .NOUN "police"]]]]]

/-- In *This guitar, I've sung folksongs and accompanied myself on it all my life* the
dislocated NP is inside a conjunct. -/
def guitar : Tree Cat String :=
  .node .S [.node N [w .PRON "I"],
    .node V [w .AUX "have",
      .node Conj [.node V [w .VERB "sung", .node N [w .NOUN "folksongs"]], w .CCONJ "and",
        .node V [w .VERB "accompanied", .node N [w .PRON "myself"],
          .node P [w .ADP "on", .node N [w .DET "this", w .NOUN "guitar"]]]]]]

/-- In *My father, that he's lived here all his life is well-known to the cops* the dislocated
NP is inside a sentential subject. -/
def lived : Tree Cat String :=
  .node .S [.node N [.node .S [w .SCONJ "that", .node N [w .PRON "my", w .NOUN "father"],
      .node V [w .AUX "has", w .VERB "lived", w .ADV "here",
        .node N [w .DET "all", w .PRON "his", w .NOUN "life"]]]],
    .node V [w .AUX "is", w .ADJ "well-known",
      .node P [w .ADP "to", .node N [w .DET "the", w .NOUN "cops"]]]]

/-- In *My wife, somebody stole her handbag last night* the dislocated NP is a possessor on a
left branch. -/
def handbag : Tree Cat String :=
  .node .S [.node N [w .PRON "somebody"],
    .node V [w .VERB "stole",
      .node N [.node N [w .PRON "my", w .NOUN "wife"], w .NOUN "handbag"],
      .node N [w .ADJ "last", w .NOUN "night"]]]

/-- The movement of each example, by the dissertation's number. Questions and dislocations
land at the root, relativizations at the relative clause. -/
def movement : String → Option Movement
  | "(4.13a)" => some ⟨seeToIt, [1, 1, 1, 1, 2, 2, 1, 1, 2, 1], [1, 1, 1]⟩
  | "(4.15a)" => some ⟨phineas, [1, 1, 1, 1, 1, 1, 1], []⟩
  | "(4.18a)" => some ⟨hatClaim, [0, 1, 1, 1, 1, 2, 2], [0, 1]⟩
  | "(4.18b)" => some ⟨hatThat, [0, 1, 1, 1, 2, 2], [0, 1]⟩
  | "(2.18)" => some ⟨sofa, [1, 2, 1, 2], []⟩
  | "(4.82a)" => some ⟨lute, [0, 1, 1, 0, 1], [0, 1]⟩
  | "(4.82d)" => some ⟨trombone, [0, 0, 1, 1], []⟩
  | "(4.184a)" => some ⟨guardian, [0, 1, 1, 1], [0, 1]⟩
  | "(4.184b)" => some ⟨guardian, [0, 1, 1, 1, 0], [0, 1]⟩
  | "(4.184c)" => some ⟨guardian, [0, 1, 1, 1, 0, 0], [0, 1]⟩
  | "(4.251a)" => some ⟨teacherActive, [0, 1, 1, 1, 2, 2], [0, 1]⟩
  | "(4.251b)" => some ⟨teacherPassive, [0, 1, 0, 0, 2, 2], [0, 1]⟩
  | "(4.251c)" => some ⟨teacherExtraposed, [0, 1, 1, 3, 2, 2], [0, 1]⟩
  | "(4.252)" => some ⟨hoods, [0, 2], []⟩
  | "(6.128b)" => some ⟨father, [0, 1, 0], []⟩
  | "(6.135b)" => some ⟨guitar, [1, 1, 2, 2, 1], []⟩
  | "(6.136)" => some ⟨lived, [0, 0, 1], []⟩
  | "(6.137)" => some ⟨handbag, [1, 1, 0], []⟩
  | _ => none

/-! ### The rows -/

/-- Whether a reordering rule chops its term, substituting nothing or another term for it, or
copies it, leaving a pronoun in its place. -/
inductive Rule
  | chopping
  | copying
  deriving DecidableEq, Repr

/-- The four constraints. -/
inductive Constraint
  | cnpc
  | csc
  | ssc
  | lbc
  deriving DecidableEq, Repr

/-- The constraint's condition on a movement. -/
def Constraint.Fires : Constraint → Movement → Prop
  | .cnpc, m => m.CNPC
  | .csc, m => m.CSC
  | .ssc, m => m.SSC
  | .lbc, m => m.LBC

instance (c : Constraint) (m : Movement) : Decidable (c.Fires m) := by
  unfold Constraint.Fires; cases c <;> infer_instance

/-- An example records its movement, the kind of rule that moved it, the constraint the
dissertation holds responsible, if any, and its judgment. -/
structure Row where
  movement : Movement
  rule : Rule
  constraint : Option Constraint
  judgment : Judgment

/-- The row of an example. -/
def Row.ofDatum (r : Datum) : Option Row := do
  let m ← Ross1967.movement r.source.paperLabel
  let rule ← r.parse? "rule" [("question", Rule.chopping), ("relativization", .chopping),
    ("topicalization", .chopping), ("leftDislocation", .copying)]
  let c := r.parse? "constraint" [("CNPC", Constraint.cnpc), ("CSC", .csc), ("SSC", .ssc),
    ("LBC", .lbc)]
  pure ⟨m, rule, c, r.judgment⟩

/-- The examples. -/
def data : List Row := Examples.all.filterMap Row.ofDatum

theorem data_length : data.length = Examples.all.length := by decide +kernel

/-- A chopping rule's example is acceptable exactly when its movement violates none of the four
constraints. -/
theorem chopping_rows :
    ∀ d ∈ data, d.rule = .chopping →
      (d.judgment = .acceptable ↔ ¬ d.movement.Violates) := by
  decide +kernel

-- (4.18a), (4.13a): relativizing out of the clause of *the claim* violates the CNPC, out of the
-- clause of *it* does not
theorem cnpc_lexical_head :
    (∃ m ∈ movement "(4.18a)", m.CNPC) ∧ ∃ m ∈ movement "(4.13a)", ¬ m.CNPC := by
  decide +kernel

-- (4.18a): the complex NP over *the claim* satisfies the hypotheses of `cnpc_of_complexNP`
example : (⟨hatClaim, [0, 1, 1, 1, 1, 2, 2], [0, 1]⟩ : Movement).CNPC :=
  Movement.cnpc_of_complexNP (np := [0, 1, 1, 1]) rfl rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

-- (4.13a): `[N it]` is the lexical head of the complex NP over *it*, but it is not a word, as
-- Ross's `[+Lex]` requires
example : IsLexicalHeadOf (Tree.HeadDaughterAt seeToIt) ⟨[1, 1, 1, 1, 2, 2, 1, 0]⟩
      ⟨[1, 1, 1, 1, 2, 2, 1]⟩ ∧ ¬ HasLexicalHead seeToIt [1, 1, 1, 1, 2, 2, 1] := by
  decide +kernel

theorem attributions : ∀ d ∈ data, ∀ c ∈ d.constraint, c.Fires d.movement := by
  decide +kernel

/-- A copying rule's examples are acceptable, though each of their movements violates one of the
constraints. -/
theorem copying_rows :
    ∀ d ∈ data, d.rule = .copying → d.judgment = .acceptable ∧ d.movement.Violates := by
  decide +kernel

theorem ssc_cnpc_independent :
    (∃ d ∈ data, d.movement.SSC ∧ ¬ d.movement.CNPC) ∧
      ∃ d ∈ data, d.movement.CNPC ∧ ¬ d.movement.SSC := by
  decide +kernel

end Ross1967
