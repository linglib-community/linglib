module

public import Linglib.Data.UD.DepRel
public import Linglib.Syntax.DependencyGrammar.Stemma
public import Linglib.Data.UD.UPOS
public import Linglib.Morphology.Word.Basic
public import Linglib.Data.Examples.OsborneLi2023

/-!
# Osborne and Li (2023): Coordination and Referential Dependencies

This file formalizes Osborne and Li's Conjunct Referential Dependency Constraint,
the descriptive generalization of the paper's fifth section: a referentially dependent
conjunct valent can be co-valued with a full co-valent, but a referentially dependent full
valent can hardly be co-valued with a conjunct co-valent. A conjunct valent of a predicate is
a conjunct of a coordinate structure that is a valent of the predicate, and a full valent is
a valent that is not a conjunct valent (`IsConjunctValent`, `IsFullValent`); the constraint is
violated when a pronoun that is a full valent takes a conjunct co-valent as its antecedent
(`Violates`), so it is silent where no coordinate structure is present
(`not_violates_of_no_conjuncts`), and since a conjunct valent is never a full valent no pair
violates it in both directions (`Violates.not_symm`). The paper's judgments are crowdsourced
mean scores on a scale from 1, the co-valued reading easily possible, to 4, impossible, the
double question mark marking the strongly marginal middle, the library's questionable
judgment. Each stimulus is a dependency tree over one of the paper's examples, and over the
stimuli a violation is never acceptable while a coordinate stimulus without a violation is
acceptable (`violation_degraded`, `no_violation_acceptable`), the non-coordinate baselines
falling under Condition B, on which the paper is silent. The *vote* answer of (55a) is the
paper's own counterexample, a violation judged acceptable (`vote_counterexample`).

## Implementation notes

A valent is a direct dependent of the predicate by a core-argument or oblique relation
(`IsValentRel`), a simplification of the paper's catena-based notion that the example set does
not exercise; the first conjunct heads the coordinate structure in the Universal Dependencies
convention, and referential dependence is being a pronoun. The rows of
`Data/Examples/OsborneLi2023` carry the paper's respondent counts and mean scores.

## References

* [osborne-li-2023]
-/

@[expose] public section

namespace OsborneLi2023

open DependencyGrammar
open Stemma (node leaf)
open Morphology (Word)

/-! ### Conjunct and full valents -/

section Valents

variable {n : ℕ} (g : Graph UD.DepRel n)

/-- The relations of valents are the core-argument relations and the oblique, which UD classifies
as non-core. -/
def IsValentRel (r : UD.DepRel) : Prop := r.IsCore ∨ r = .obl

instance : DecidablePred IsValentRel := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The conjuncts of the coordinate structure headed at `c`, which are the head, the first
conjunct, and its `conj` dependents. -/
def allConjuncts (c : Fin n) : Finset (Fin n) :=
  insert c {w ∈ g.children c | g.label c w = some .conj}

/-- Position `c` heads a coordinate structure, having a `conj` dependent. -/
def HasConjuncts (c : Fin n) : Prop :=
  ∃ w ∈ g.children c, g.label c w = some .conj

instance (c : Fin n) : Decidable (HasConjuncts g c) := Finset.decidableExistsAndFinset

/-- `valent` is a conjunct valent of `pred` when it is a conjunct of a coordinate structure that
fills a valency role of `pred`. -/
def IsConjunctValent (pred valent : Fin n) : Prop :=
  ∃ c ∈ g.children pred, ∃ r ∈ g.label pred c, IsValentRel r ∧
    HasConjuncts g c ∧ valent ∈ allConjuncts g c

instance (pred valent : Fin n) : Decidable (IsConjunctValent g pred valent) :=
  Finset.decidableExistsAndFinset

/-- `valent` is a full valent of `pred` when it is a valent of `pred` that is complete, that is,
not a conjunct valent. -/
def IsFullValent (pred valent : Fin n) : Prop :=
  (∃ r ∈ g.label pred valent, IsValentRel r) ∧ ¬ IsConjunctValent g pred valent

instance (pred valent : Fin n) : Decidable (IsFullValent g pred valent) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The constraint is violated when the pronoun `ana`, a full valent of `pred`, is co-valued
with a conjunct valent `ante` of the same predicate. -/
def Violates (pred ana ante : Fin n) : Prop :=
  (g.words ana).cat = .PRON ∧ IsFullValent g pred ana ∧ IsConjunctValent g pred ante

instance (pred ana ante : Fin n) : Decidable (Violates g pred ana ante) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

variable {g}

theorem Violates.not_symm {pred ana ante : Fin n} (h : Violates g pred ana ante) :
    ¬ Violates g pred ante ana :=
  fun h' ↦ h'.2.1.2 h.2.2

theorem not_violates_of_no_conjuncts (h : ∀ c, ¬ HasConjuncts g c) (pred ana ante : Fin n) :
    ¬ Violates g pred ana ante :=
  fun ⟨_, _, c, _, _, _, _, hc, _⟩ ↦ h c hc

end Valents

/-! ### The stimuli -/

/-- A stimulus is the stemma of an example, whose head is the predicate, with the position of the
referentially dependent expression and of its intended antecedent, and the example's row. -/
structure Stimulus where
  stemma : Stemma UD.DepRel
  ana : Fin stemma.size
  ante : Fin stemma.size
  row : Datum

/-- The dependency tree of the stimulus. -/
abbrev Stimulus.tree (s : Stimulus) : Graph UD.DepRel s.stemma.size := s.stemma.toGraph

/-- The stimulus violates the constraint. -/
def Stimulus.Violates (s : Stimulus) : Prop :=
  OsborneLi2023.Violates s.tree s.tree.root s.ana s.ante

instance : DecidablePred Stimulus.Violates :=
  fun s ↦ inferInstanceAs (Decidable (Violates s.tree s.tree.root s.ana s.ante))

/-- The stimulus contains a coordinate structure. -/
def Stimulus.Coordinate (s : Stimulus) : Prop := ∃ c, HasConjuncts s.tree c

instance : DecidablePred Stimulus.Coordinate := fun _ ↦ Fintype.decidableExistsFintype

/-- (2a) *Max and Lucie talked about him* has a full-valent pronoun with a conjunct antecedent. -/
def ex2a : Stimulus where
  stemma :=
    node (.mk' "talked" .VERB)
      [(.nsubj, node (.mk' "Max" .PROPN)
         []
         [(.cc, leaf (.mk' "and" .CCONJ)), (.conj, leaf (.mk' "Lucie" .PROPN))])]
      [(.obl, node (.mk' "him" .PRON) [(.case, leaf (.mk' "about" .ADP))] [])]
  ana := 5
  ante := 0
  row := Examples.ex2a

/-- In (3a) *John and Mary talked about himself* the reflexive fares no better. -/
def ex3a : Stimulus where
  stemma :=
    node (.mk' "talked" .VERB)
      [(.nsubj, node (.mk' "John" .PROPN)
         []
         [(.cc, leaf (.mk' "and" .CCONJ)), (.conj, leaf (.mk' "Mary" .PROPN))])]
      [(.obl, node (.mk' "himself" .PRON) [(.case, leaf (.mk' "about" .ADP))] [])]
  ana := 5
  ante := 0
  row := Examples.ex3a

/-- In (5a) *Both John and Mary love him* the paired coordinator forces distribution, and the
sentence is judged worse than the constraint alone predicts. -/
def ex5a : Stimulus where
  stemma :=
    node (.mk' "love" .VERB)
      [(.nsubj, node (.mk' "John" .PROPN)
         [(.cc, leaf (.mk' "Both" .CCONJ))]
         [(.cc, leaf (.mk' "and" .CCONJ)), (.conj, leaf (.mk' "Mary" .PROPN))])]
      [(.obj, leaf (.mk' "him" .PRON))]
  ana := 5
  ante := 1
  row := Examples.ex5a

/-- (9a) *Max talked about himself* is the non-coordinate reflexive baseline. -/
def ex9a : Stimulus where
  stemma :=
    node (.mk' "talked" .VERB)
      [(.nsubj, leaf (.mk' "Max" .PROPN))]
      [(.obl, node (.mk' "himself" .PRON) [(.case, leaf (.mk' "about" .ADP))] [])]
  ana := 3
  ante := 0
  row := Examples.ex9a

/-- (9b) *Max talked about him* is the non-coordinate pronoun baseline, marginal by Condition B,
on which the constraint is silent. -/
def ex9b : Stimulus where
  stemma :=
    node (.mk' "talked" .VERB)
      [(.nsubj, leaf (.mk' "Max" .PROPN))]
      [(.obl, node (.mk' "him" .PRON) [(.case, leaf (.mk' "about" .ADP))] [])]
  ana := 3
  ante := 0
  row := Examples.ex9b

/-- In (11a) *Max and Lucie talked about his work* the possessive is no valent of the verb. -/
def ex11a : Stimulus where
  stemma :=
    node (.mk' "talked" .VERB)
      [(.nsubj, node (.mk' "Max" .PROPN)
         []
         [(.cc, leaf (.mk' "and" .CCONJ)), (.conj, leaf (.mk' "Lucie" .PROPN))])]
      [(.obl, node (.mk' "work" .NOUN)
         [(.case, leaf (.mk' "about" .ADP)), (.nmod, leaf (.mk' "his" .PRON))]
         [])]
  ana := 5
  ante := 0
  row := Examples.ex11a

/-- In (11e) *Max and Lucie talked about Max* the name is not referentially dependent. -/
def ex11e : Stimulus where
  stemma :=
    node (.mk' "talked" .VERB)
      [(.nsubj, node (.mk' "Max" .PROPN)
         []
         [(.cc, leaf (.mk' "and" .CCONJ)), (.conj, leaf (.mk' "Lucie" .PROPN))])]
      [(.obl, node (.mk' "Max" .PROPN) [(.case, leaf (.mk' "about" .ADP))] [])]
  ana := 5
  ante := 0
  row := Examples.ex11e

/-- In (20b) *Hank and Hillary appear to her to be good friends* the experiencer of a raising
predicate is a full valent. -/
def ex20b : Stimulus where
  stemma :=
    node (.mk' "appear" .VERB)
      [(.nsubj, node (.mk' "Hank" .PROPN)
         []
         [(.cc, leaf (.mk' "and" .CCONJ)), (.conj, leaf (.mk' "Hillary" .PROPN))])]
      [(.obl, node (.mk' "her" .PRON) [(.case, leaf (.mk' "to" .ADP))] []),
       (.xcomp, node (.mk' "friends" .NOUN)
         [(.mark, leaf (.mk' "to" .PART)),
          (.cop, leaf (.mk' "be" .AUX)),
          (.amod, leaf (.mk' "good" .ADJ))]
         [])]
  ana := 5
  ante := 2
  row := Examples.ex20b

/-- In (24a) *John talked about himself and his mother* the reflexive heads the coordinate
object, so it is a conjunct valent and *John* a full valent, the permitted direction. -/
def ex24a : Stimulus where
  stemma :=
    node (.mk' "talked" .VERB)
      [(.nsubj, leaf (.mk' "John" .PROPN))]
      [(.obl, node (.mk' "himself" .PRON)
         [(.case, leaf (.mk' "about" .ADP))]
         [(.cc, leaf (.mk' "and" .CCONJ)),
          (.conj, node (.mk' "mother" .NOUN) [(.nmod, leaf (.mk' "his" .PRON))] [])])]
  ana := 3
  ante := 0
  row := Examples.ex24a

/-- In (28d) *John expected Mary and him to be able to leave soon* the pronoun is a conjunct of
the raised object. -/
def ex28d : Stimulus where
  stemma :=
    node (.mk' "expected" .VERB)
      [(.nsubj, leaf (.mk' "John" .PROPN))]
      [(.obj, node (.mk' "Mary" .PROPN)
         []
         [(.cc, leaf (.mk' "and" .CCONJ)), (.conj, leaf (.mk' "him" .PRON))]),
       (.xcomp, node (.mk' "able" .ADJ)
         [(.mark, leaf (.mk' "to" .PART)), (.cop, leaf (.mk' "be" .AUX))]
         [(.xcomp, node (.mk' "leave" .VERB)
            [(.mark, leaf (.mk' "to" .PART))]
            [(.advmod, leaf (.mk' "soon" .ADV))])])]
  ana := 4
  ante := 0
  row := Examples.ex28d

/-- The paper's stimuli. -/
def stimuli : List Stimulus :=
  [ex2a, ex3a, ex5a, ex9a, ex9b, ex11a, ex11e, ex20b, ex24a, ex28d]

theorem violation_degraded : ∀ s ∈ stimuli, s.Violates → s.row.judgment ≠ .acceptable := by
  decide

theorem no_violation_acceptable :
    ∀ s ∈ stimuli, s.Coordinate → ¬ s.Violates → s.row.judgment = .acceptable := by
  decide

/-! ### The counterexample of the sixth section -/

/-- (55a) *Who voted for Sophy? Sophy and Edgar voted for her* is a violation the informants
accept, which the paper attributes to an identity split between the candidate and the voter. -/
def ex55a : Stimulus where
  stemma :=
    node (.mk' "voted" .VERB)
      [(.nsubj, node (.mk' "Sophy" .PROPN)
         []
         [(.cc, leaf (.mk' "and" .CCONJ)), (.conj, leaf (.mk' "Edgar" .PROPN))])]
      [(.obl, node (.mk' "her" .PRON) [(.case, leaf (.mk' "for" .ADP))] [])]
  ana := 5
  ante := 0
  row := Examples.ex55a

theorem vote_counterexample : ex55a.Violates ∧ ex55a.row.judgment = .acceptable := by decide

end OsborneLi2023
