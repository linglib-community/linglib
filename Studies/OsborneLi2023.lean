module

public import Linglib.Data.UD.DepRel
public import Linglib.Syntax.DependencyGrammar.Basic
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

/-- A stimulus is the dependency tree of an example with its predicate, the referentially
dependent expression and its intended antecedent, and the example's row. -/
structure Stimulus where
  n : ℕ
  tree : Graph UD.DepRel n
  pred : Fin n
  ana : Fin n
  ante : Fin n
  row : Datum

/-- The stimulus violates the constraint. -/
def Stimulus.Violates (s : Stimulus) : Prop := OsborneLi2023.Violates s.tree s.pred s.ana s.ante

instance : DecidablePred Stimulus.Violates :=
  fun s ↦ inferInstanceAs (Decidable (Violates s.tree s.pred s.ana s.ante))

/-- The stimulus contains a coordinate structure. -/
def Stimulus.Coordinate (s : Stimulus) : Prop := ∃ c, HasConjuncts s.tree c

instance : DecidablePred Stimulus.Coordinate := fun _ ↦ Fintype.decidableExistsFintype

/-- (2a) *Max and Lucie talked about him* has a full-valent pronoun with a conjunct antecedent. -/
def ex2a : Stimulus :=
  ⟨6, .ofArcs
    [Word.mk' "Max" .PROPN, Word.mk' "and" .CCONJ, Word.mk' "Lucie" .PROPN,
     Word.mk' "talked" .VERB, Word.mk' "about" .ADP, Word.mk' "him" .PRON]
    3 [(3, 0, .nsubj), (0, 1, .cc), (0, 2, .conj), (3, 5, .obl), (5, 4, .case)],
   3, 5, 0, Examples.ex2a⟩

/-- In (3a) *John and Mary talked about himself* the reflexive fares no better. -/
def ex3a : Stimulus :=
  ⟨6, .ofArcs
    [Word.mk' "John" .PROPN, Word.mk' "and" .CCONJ, Word.mk' "Mary" .PROPN,
     Word.mk' "talked" .VERB, Word.mk' "about" .ADP, Word.mk' "himself" .PRON]
    3 [(3, 0, .nsubj), (0, 1, .cc), (0, 2, .conj), (3, 5, .obl), (5, 4, .case)],
   3, 5, 0, Examples.ex3a⟩

/-- In (5a) *Both John and Mary love him* the paired coordinator forces distribution, and the
sentence is judged worse than the constraint alone predicts. -/
def ex5a : Stimulus :=
  ⟨6, .ofArcs
    [Word.mk' "Both" .CCONJ, Word.mk' "John" .PROPN, Word.mk' "and" .CCONJ,
     Word.mk' "Mary" .PROPN, Word.mk' "love" .VERB, Word.mk' "him" .PRON]
    4 [(4, 1, .nsubj), (1, 0, .cc), (1, 2, .cc), (1, 3, .conj), (4, 5, .obj)],
   4, 5, 1, Examples.ex5a⟩

/-- (9a) *Max talked about himself* is the non-coordinate reflexive baseline. -/
def ex9a : Stimulus :=
  ⟨4, .ofArcs
    [Word.mk' "Max" .PROPN, Word.mk' "talked" .VERB, Word.mk' "about" .ADP,
     Word.mk' "himself" .PRON]
    1 [(1, 0, .nsubj), (1, 3, .obl), (3, 2, .case)],
   1, 3, 0, Examples.ex9a⟩

/-- (9b) *Max talked about him* is the non-coordinate pronoun baseline, marginal by Condition B,
on which the constraint is silent. -/
def ex9b : Stimulus :=
  ⟨4, .ofArcs
    [Word.mk' "Max" .PROPN, Word.mk' "talked" .VERB, Word.mk' "about" .ADP,
     Word.mk' "him" .PRON]
    1 [(1, 0, .nsubj), (1, 3, .obl), (3, 2, .case)],
   1, 3, 0, Examples.ex9b⟩

/-- In (11a) *Max and Lucie talked about his work* the possessive is no valent of the verb. -/
def ex11a : Stimulus :=
  ⟨7, .ofArcs
    [Word.mk' "Max" .PROPN, Word.mk' "and" .CCONJ, Word.mk' "Lucie" .PROPN,
     Word.mk' "talked" .VERB, Word.mk' "about" .ADP, Word.mk' "his" .PRON,
     Word.mk' "work" .NOUN]
    3 [(3, 0, .nsubj), (0, 1, .cc), (0, 2, .conj), (3, 6, .obl), (6, 4, .case),
       (6, 5, .nmod)],
   3, 5, 0, Examples.ex11a⟩

/-- In (11e) *Max and Lucie talked about Max* the name is not referentially dependent. -/
def ex11e : Stimulus :=
  ⟨6, .ofArcs
    [Word.mk' "Max" .PROPN, Word.mk' "and" .CCONJ, Word.mk' "Lucie" .PROPN,
     Word.mk' "talked" .VERB, Word.mk' "about" .ADP, Word.mk' "Max" .PROPN]
    3 [(3, 0, .nsubj), (0, 1, .cc), (0, 2, .conj), (3, 5, .obl), (5, 4, .case)],
   3, 5, 0, Examples.ex11e⟩

/-- In (20b) *Hank and Hillary appear to her to be good friends* the experiencer of a raising
predicate is a full valent. -/
def ex20b : Stimulus :=
  ⟨10, .ofArcs
    [Word.mk' "Hank" .PROPN, Word.mk' "and" .CCONJ, Word.mk' "Hillary" .PROPN,
     Word.mk' "appear" .VERB, Word.mk' "to" .ADP, Word.mk' "her" .PRON,
     Word.mk' "to" .PART, Word.mk' "be" .AUX, Word.mk' "good" .ADJ,
     Word.mk' "friends" .NOUN]
    3 [(3, 0, .nsubj), (0, 1, .cc), (0, 2, .conj), (3, 5, .obl), (5, 4, .case),
       (3, 9, .xcomp), (9, 6, .mark), (9, 7, .cop), (9, 8, .amod)],
   3, 5, 2, Examples.ex20b⟩

/-- In (24a) *John talked about himself and his mother* the reflexive heads the coordinate
object, so it is a conjunct valent and *John* a full valent, the permitted direction. -/
def ex24a : Stimulus :=
  ⟨7, .ofArcs
    [Word.mk' "John" .PROPN, Word.mk' "talked" .VERB, Word.mk' "about" .ADP,
     Word.mk' "himself" .PRON, Word.mk' "and" .CCONJ, Word.mk' "his" .PRON,
     Word.mk' "mother" .NOUN]
    1 [(1, 0, .nsubj), (1, 3, .obl), (3, 2, .case), (3, 4, .cc), (3, 6, .conj),
       (6, 5, .nmod)],
   1, 3, 0, Examples.ex24a⟩

/-- In (28d) *John expected Mary and him to be able to leave soon* the pronoun is a conjunct of
the raised object. -/
def ex28d : Stimulus :=
  ⟨11, .ofArcs
    [Word.mk' "John" .PROPN, Word.mk' "expected" .VERB, Word.mk' "Mary" .PROPN,
     Word.mk' "and" .CCONJ, Word.mk' "him" .PRON, Word.mk' "to" .PART, Word.mk' "be" .AUX,
     Word.mk' "able" .ADJ, Word.mk' "to" .PART, Word.mk' "leave" .VERB, Word.mk' "soon" .ADV]
    1 [(1, 0, .nsubj), (1, 2, .obj), (2, 3, .cc), (2, 4, .conj), (1, 7, .xcomp),
       (7, 5, .mark), (7, 6, .cop), (7, 9, .xcomp), (9, 8, .mark), (9, 10, .advmod)],
   1, 4, 0, Examples.ex28d⟩

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
def ex55a : Stimulus :=
  ⟨6, .ofArcs
    [Word.mk' "Sophy" .PROPN, Word.mk' "and" .CCONJ, Word.mk' "Edgar" .PROPN,
     Word.mk' "voted" .VERB, Word.mk' "for" .ADP, Word.mk' "her" .PRON]
    3 [(3, 0, .nsubj), (0, 1, .cc), (0, 2, .conj), (3, 5, .obl), (5, 4, .case)],
   3, 5, 0, Examples.ex55a⟩

theorem vote_counterexample : ex55a.Violates ∧ ex55a.row.judgment = .acceptable := by decide

end OsborneLi2023
