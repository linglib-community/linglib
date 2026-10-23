module

public import Linglib.Fragments.English.Auxiliaries
public import Linglib.Fragments.English.Nouns
public import Linglib.Fragments.English.Pronouns
public import Linglib.Fragments.English.TemporalDeictic
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Syntax.DependencyGrammar.Projectivity
public import Linglib.Syntax.DependencyGrammar.Valency
public import Linglib.Logic.Nonmonotonic.Inheritance
public import Linglib.Core.Relation.ReflTransGen
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fin.VecNotation

/-!
# Gisborne (2026): Mutual dependency, English wh-clauses and Word Grammar

This file formalizes Gisborne's account of word order under mutual dependency in Word Grammar.
Word order is fixed by landmarks, which must form a projective tree as in Robinson's axioms, and
we compare Hudson's earlier and later theories of landmarks with Gisborne's revision, in which an
extracted word is placed by a positional head outside the landmark tree.

## Main definitions

* `Analysis n`: a Word Grammar analysis of `n` words, a network of typed dependencies in which a
  word may have several heads and two words may depend on each other.
* `Analysis.IsLandmark A w p`: `p` is the landmark of `w` by Hudson's 2007 rules, under which a
  head is a landmark unless it is subordinate to another head.
* `Analysis.Orders A L root`: the landmark relation `L` forms a projective tree from `root`, with
  every word on its side of its landmark.
* `Analysis.OrderedByLandmarks A`, `Analysis.OrderedByChosenLandmarks A`,
  `Analysis.OrderedByPositionalHeads A`: `A` is ordered by the 2007 theory, by landmarks chosen as
  in the 2018 theory, and by the revision.

## Main statements

* `Analysis.isLandmark_iff`: the 2007 rules, stated as default inheritance, make `p` the landmark
  of `w` exactly when `p` is a head of `w` not subordinate to another of its heads.
* `Analysis.not_orderedByLandmarks_of_extraction`: an analysis is not ordered by the 2007 theory
  when a word is extracted from a head that it heads and has another head as well.
* `Analysis.OrderedByLandmarks.orderedByPositionalHeads`: the revision orders every analysis the
  2007 theory orders.
* `orderedByPositionalHeads_whatHeBoughtCostLots`, `not_orderedByLandmarks_whatHeBoughtCostLots`:
  the revision orders the free relative *What he bought cost lots*, and the 2007 theory does not.

## Implementation notes

* The landmark rules are a `DefaultInheritance` network over the concepts *parent* and
  *subordinate parent*, and a landmark relation is checked for `IsTree` and `IsProjective` as a
  `DependencyGrammar.Graph` with UD's `dep` on each arc.
* Each dependency type fixes the direction of its head with respect to its dependent
  (`Rel.direction`), and an extractee's direction overrides an object's.
* Chosen landmarks range over each word's heads; the Best Landmark Principle's preference for the
  nearest more prominent word is not modelled.

## TODO

* The distributional evidence that free relatives are headed by their wh word and dependent
  interrogatives by their verb.

## References

* [N. Gisborne, *Mutual Dependency, English wh-Clauses and Word Grammar* (2026)][gisborne-2026]
* [R. Hudson, *Language Networks: The New Word Grammar* (2007)][hudson-2007]
* [R. Hudson, *Pied-Piping in Cognition* (2018)][hudson-2018]
* [J. J. Robinson, *Dependency Structures and Transformational Rules* (1970)][robinson-1970]
-/

@[expose] public section

namespace Gisborne2026

open DependencyGrammar DefaultInheritance Relation
open Morphology (Word)

/-! ### Word Grammar analyses -/

/-- The dependencies of the diagrams are subject, object, complement, the complement of a raising
verb labelled xc in (9), extractee, and adjuncts before and after their heads. -/
inductive Rel where
  | subj
  | obj
  | comp
  | xcomp
  | extractee
  | preAdjunct
  | postAdjunct
  deriving DecidableEq, Fintype, Repr

/-- The direction of a head with respect to a dependent of each type, head-final for subjects,
extractees and pre-adjuncts, which stand before it, and head-initial for the others. -/
def Rel.direction : Rel → HeadDirection
  | .subj | .extractee | .preAdjunct => .headFinal
  | .obj | .comp | .xcomp | .postAdjunct => .headInitial

/-- A Word Grammar analysis has the words in their order, the typed dependencies, each from a head
to a dependent, and the root. Several dependencies may link one pair, and two words may depend
on each other. -/
structure Analysis (n : ℕ) where
  /-- The words in their order. -/
  words : Fin n → Word
  /-- The dependencies, head first. -/
  arcs : List (Fin n × Fin n × Rel)
  /-- The root. -/
  root : Fin n

namespace Analysis

variable {n : ℕ} (A : Analysis n) {h p q w : Fin n}

/-- `w` depends on `h` by `r`. -/
def Dep (h w : Fin n) (r : Rel) : Prop := (h, w, r) ∈ A.arcs

instance (h w : Fin n) (r : Rel) : Decidable (A.Dep h w r) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- `h` is a parent of `w`. -/
def Parent (h w : Fin n) : Prop := ∃ r, A.Dep h w r

instance : DecidableRel A.Parent := fun _ _ ↦ inferInstanceAs (Decidable (∃ _, _))

/-- `x` is subordinate to `y`: a chain of dependencies leads from `y` to `x`. -/
def Subordinate (x y : Fin n) : Prop := TransGen A.Parent y x

instance : DecidableRel A.Subordinate := fun _ _ ↦ inferInstanceAs (Decidable (TransGen _ _ _))

/-- `p` is a subordinate parent of `w`: a parent of `w` subordinate to another of its
parents. -/
def SubordinateParent (w p : Fin n) : Prop :=
  A.Parent p w ∧ ∃ q, q ≠ p ∧ A.Parent q w ∧ A.Subordinate p q

instance : DecidableRel A.SubordinateParent := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-! ### The landmark rules -/

/-- The concepts of the landmark rules are parents, subordinate parents, and the pairs of a word
and a position, the exemplars. -/
inductive Concept (A : Analysis n) where
  | parent
  | subordinateParent
  | pair (w p : Fin n)
  deriving DecidableEq, Fintype

/-- The concepts each concept immediately isA. A subordinate parent is a parent, and a pair of a
word and one of its parents is a subordinate parent or else a parent. -/
def conceptParents : Concept A → List (Concept A)
  | .parent => []
  | .subordinateParent => [.parent]
  | .pair w p =>
    if A.SubordinateParent w p then [.subordinateParent] else if A.Parent p w then [.parent]
    else []

/-- The depth of a concept below *parent*. -/
def Concept.rank : Concept A → ℕ
  | .parent => 0
  | .subordinateParent => 1
  | .pair .. => 2

instance : PartialOrder (Concept A) :=
  partialOrderOfCovers (fun a b ↦ b ∈ A.conceptParents a) (Concept.rank A) (by
    rintro (_ | _ | ⟨w, p⟩) b hb <;> simp only [conceptParents] at hb
    · simp at hb
    · simp_all [Concept.rank]
    · split_ifs at hb <;> simp_all [Concept.rank])

/-- The landmark rules, by which parents are landmarks and subordinate parents are not. -/
def landmarkRule : Concept A → Option Bool
  | .parent => some true
  | .subordinateParent => some false
  | .pair .. => none

/-- `p` is the landmark of `w`: the pair of `w` and `p` inherits *landmark* by the rules. -/
def IsLandmark (w p : Fin n) : Prop :=
  true ∈ inherited A.landmarkRule (.pair w p)

variable {A}

theorem subordinateParent_le_parent : (Concept.subordinateParent : Concept A) ≤ .parent :=
  ReflTransGen.single (by simp [conceptParents])

theorem pair_le_iff {c : Concept A} : Concept.pair w p ≤ c ↔
    c = .pair w p ∨ c = .subordinateParent ∧ A.SubordinateParent w p ∨
      c = .parent ∧ A.Parent p w := by
  constructor
  · intro hc
    change ReflTransGen _ _ _ at hc
    induction hc with
    | refl => exact .inl rfl
    | tail _ hbc ih =>
      rcases ih with rfl | ⟨rfl, hs⟩ | ⟨rfl, -⟩
      · simp only [conceptParents] at hbc
        split_ifs at hbc with h₁ h₂ <;> simp_all
      · simp only [conceptParents, List.mem_singleton] at hbc
        exact .inr (.inr ⟨hbc, hs.1⟩)
      · simp [conceptParents] at hbc
  · rintro (rfl | ⟨rfl, hs⟩ | ⟨rfl, hp⟩)
    · exact le_rfl
    · exact ReflTransGen.single (by simp [conceptParents, hs])
    · by_cases hs : A.SubordinateParent w p
      · exact le_trans (ReflTransGen.single (by simp [conceptParents, hs]))
          subordinateParent_le_parent
      · exact ReflTransGen.single (by simp [conceptParents, hs, hp])

theorem mem_specifiers_pair {c : Concept A} :
    c ∈ specifiers A.landmarkRule (.pair w p) ↔
      c = .subordinateParent ∧ A.SubordinateParent w p ∨ c = .parent ∧ A.Parent p w := by
  rw [mem_specifiers, pair_le_iff]
  rcases c with _ | _ | ⟨w', p'⟩ <;> simp [landmarkRule]

/-- The landmark rules make `p` the landmark of `w` exactly when `p` is a parent of `w` and not
a subordinate parent. -/
theorem isLandmark_iff : A.IsLandmark w p ↔ A.Parent p w ∧ ¬ A.SubordinateParent w p := by
  by_cases hs : A.SubordinateParent w p
  · have : inherited A.landmarkRule (.pair w p) = {false} :=
      inherited_eq_singleton_of_isLeast (m := .subordinateParent)
        ⟨mem_specifiers_pair.2 (.inl ⟨rfl, hs⟩), fun c hc ↦ by
          rcases mem_specifiers_pair.1 hc with ⟨rfl, -⟩ | ⟨rfl, -⟩
          exacts [le_rfl, subordinateParent_le_parent]⟩ rfl
    simp [IsLandmark, this, hs]
  · by_cases hp : A.Parent p w
    · have : inherited A.landmarkRule (.pair w p) = {true} :=
        inherited_eq_singleton_of_isLeast (m := .parent)
          ⟨mem_specifiers_pair.2 (.inr ⟨rfl, hp⟩), fun c hc ↦ by
            rcases mem_specifiers_pair.1 hc with ⟨rfl, h⟩ | ⟨rfl, -⟩
            exacts [absurd h hs, le_rfl]⟩ rfl
      simp [IsLandmark, this, hs, hp]
    · simp only [hp, false_and, iff_false]
      rintro ⟨m, hm, -⟩
      rcases mem_specifiers_pair.1 hm.prop with ⟨-, h⟩ | ⟨-, h⟩
      exacts [hs h, hp h]

instance : Decidable (A.IsLandmark w p) := decidable_of_iff _ isLandmark_iff.symm

/-! ### Landmark trees and word order -/

variable (A) (L : Fin n → Fin n → Prop) [DecidableRel L] (root : Fin n)

/-- The graph of a landmark relation, `L w p` saying that `p` is the landmark of `w`, rooted at
`root`, with an arc from each word's landmark to the word, labelled with UD's unspecified relation.
-/
def graphOf : Graph n where
  words := A.words
  label p w := if L w p then some .dep else none
  root := root

/-- Every word stands on the side of its landmark that its dependency on the landmark fixes, the
extractee's side when it is extracted from the landmark, which overrides the side of its other
dependency there. -/
def RespectsLandmarks : Prop :=
  ∀ w p, L w p → ∃ r, A.Dep p w r ∧ r.direction.Orders p w ∧ (A.Dep p w .extractee → r = .extractee)

/-- The landmarks order the analysis when they form a projective tree from the root and every word
stands on its side of its landmark. -/
def Orders : Prop :=
  (A.graphOf L root).IsTree ∧ (A.graphOf L root).IsProjective ∧ A.RespectsLandmarks L

/-- Extraction by landmark, where the head a word is extracted from is its landmark. -/
def ExtractionBy : Prop := ∀ h w, A.Dep h w .extractee → L w h

instance : Decidable (A.RespectsLandmarks L) := inferInstanceAs (Decidable (∀ _ _, _))
instance : Decidable (A.Orders L root) := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable (A.ExtractionBy L) := inferInstanceAs (Decidable (∀ _ _, _))

/-- The graph in which every parent is a landmark, as in the diagrams (52) to (55). -/
abbrev parentGraph : Graph n := A.graphOf (fun w p ↦ A.Parent p w) A.root

/-- The positional head of an extracted word, by the revision's start-rule of extraction, is the
head it is extracted from. -/
def PositionalHead (w h : Fin n) : Prop := A.Dep h w .extractee

instance (w h : Fin n) : Decidable (A.PositionalHead w h) :=
  inferInstanceAs (Decidable (A.Dep _ _ _))

/-- Every extracted word stands on the extractee's side of its positional head, before it. -/
def RespectsPositionalHeads : Prop :=
  ∀ w h, A.PositionalHead w h → Rel.extractee.direction.Orders h w

/-- Word order by the 2007 theory. The landmarks the rules pick out order the analysis, and an
extracted word's landmark is the head it is extracted from. -/
def OrderedByLandmarks : Prop := A.Orders A.IsLandmark A.root ∧ A.ExtractionBy A.IsLandmark

/-- Word order by the revised theory. The landmarks the rules pick out order the analysis, and
every extracted word precedes its positional head. -/
def OrderedByPositionalHeads : Prop := A.Orders A.IsLandmark A.root ∧ A.RespectsPositionalHeads

/-- A choice of landmarks in the later theory of [hudson-2018], where the Best Landmark
Principle assigns them in place of the rules, giving each word one of its parents or none. -/
abbrev Choice : Type := (w : Fin n) → Option {p // A.Parent p w}

/-- The landmark relation of a choice. -/
def Choice.Landmark {A : Analysis n} (c : A.Choice) (w p : Fin n) : Prop :=
  (c w).map Subtype.val = some p

instance (c : A.Choice) : DecidableRel c.Landmark := fun _ _ ↦ inferInstanceAs (Decidable (_ = _))

/-- Word order by the later theory. Some root and some choice of landmarks order the analysis,
and every extracted word's landmark is the head it is extracted from. -/
def OrderedByChosenLandmarks : Prop :=
  ∃ root, ∃ c : A.Choice, A.Orders c.Landmark root ∧ A.ExtractionBy c.Landmark

instance : Decidable A.RespectsPositionalHeads := inferInstanceAs (Decidable (∀ _ _, _))
instance : Decidable A.OrderedByLandmarks := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable A.OrderedByPositionalHeads := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable A.OrderedByChosenLandmarks := inferInstanceAs (Decidable (∃ _, ∃ _, _))

variable {A L root}

@[simp] theorem graphOf_adj : (A.graphOf L root).Adj p w ↔ L w p := by
  simp only [Graph.Adj, graphOf]
  split_ifs <;> simp [*]

theorem not_isTree_graphOf (h₁ : L w p) (h₂ : L p w) : ¬ (A.graphOf L root).IsTree := fun hT ↦
  hT.not_dominates_of_adj (graphOf_adj.2 h₁) (.single (graphOf_adj.2 h₂))

theorem not_isTree_parentGraph (h₁ : A.Parent p w) (h₂ : A.Parent w p) :
    ¬ A.parentGraph.IsTree :=
  not_isTree_graphOf h₁ h₂

theorem not_extractionBy_isLandmark (hex : A.Dep h w .extractee)
    (hs : A.SubordinateParent w h) : ¬ A.ExtractionBy A.IsLandmark := fun hE ↦
  (isLandmark_iff.1 (hE h w hex)).2 hs

/-- A word that heads the clause it is extracted from and depends on a head outside it cannot be
positioned by landmarks, since the head it is extracted from is subordinate to the outside head. -/
theorem not_orderedByLandmarks_of_extraction (hex : A.Dep h w .extractee) (hq : A.Parent q w)
    (hqh : q ≠ h) (hwh : A.Parent w h) : ¬ A.OrderedByLandmarks := fun hO ↦
  not_extractionBy_isLandmark hex ⟨⟨_, hex⟩, q, hqh, hq, .head hq (.single hwh)⟩ hO.2

/-- The revision accepts every analysis the 2007 theory accepts, since an extracted word precedes
the head it is extracted from when that head is its landmark. -/
theorem OrderedByLandmarks.orderedByPositionalHeads (hO : A.OrderedByLandmarks) :
    A.OrderedByPositionalHeads := by
  refine ⟨hO.1, fun w h hex ↦ ?_⟩
  obtain ⟨r, -, hr, hx⟩ := hO.1.2.2 w h (hO.2 h w hex)
  exact hx hex ▸ hr

end Analysis

/-! ### Raising, (9) -/

abbrev they := English.Pronouns.they.toWord
abbrev seemed := English.Verbs.seem.toWord .past
abbrev to_ := English.Auxiliaries.toInf
abbrev dance := English.Verbs.dance.toWord .base

/-- In *They seemed to dance*, (9), the subject depends on each verb, and each verb's xc complement
is the next. -/
def theySeemedToDance : Analysis 4 where
  words := ![they, seemed, to_, dance]
  arcs := [(1, 0, .subj), (2, 0, .subj), (3, 0, .subj), (1, 2, .xcomp), (2, 3, .xcomp)]
  root := 1

/-- The network of (9) is neither a tree nor projective, since the subject has three parents. -/
theorem not_isTree_parentGraph_theySeemedToDance :
    ¬ theySeemedToDance.parentGraph.IsTree ∧ ¬ theySeemedToDance.parentGraph.IsProjective := by
  decide

theorem isLandmark_theySeemedToDance :
    theySeemedToDance.IsLandmark 0 1 ∧ ¬ theySeemedToDance.IsLandmark 0 2 ∧
      ¬ theySeemedToDance.IsLandmark 0 3 := by
  decide

/-- The landmarks of (9) form a projective tree. -/
theorem orderedByLandmarks_theySeemedToDance : theySeemedToDance.OrderedByLandmarks := by
  decide

/-! ### Dependent interrogatives, (51) and (52) -/

abbrev know := English.Verbs.know.toWord .base
abbrev what := English.Pronouns.what.toWord
abbrev she := English.Pronouns.she.toWord
abbrev said := English.Verbs.say.toWord .past

/-- In (51), *(I don't) know what she said* with the verb as head, *said* is the complement of
*know*, and *what* its extracted object. -/
def verbHeaded : Analysis 4 where
  words := ![know, what, she, said]
  arcs := [(0, 3, .comp), (3, 1, .extractee), (3, 1, .obj), (3, 2, .subj)]
  root := 0

theorem orderedByLandmarks_verbHeaded : verbHeaded.OrderedByLandmarks := by decide

/-- In (52), the traditional analysis with the wh word as head, *what* is the complement of *know*
and takes *said* as its complement, and it is also *said*'s extracted object. -/
def whHeaded : Analysis 4 where
  words := ![know, what, she, said]
  arcs := [(0, 1, .comp), (1, 3, .comp), (3, 1, .extractee), (3, 1, .obj), (3, 2, .subj)]
  root := 0

theorem not_orderedByLandmarks_whHeaded :
    ¬ whHeaded.parentGraph.IsTree ∧ ¬ whHeaded.OrderedByLandmarks :=
  ⟨Analysis.not_isTree_parentGraph (p := 1) (w := 3) ⟨.comp, by decide⟩ ⟨.obj, by decide⟩,
    Analysis.not_orderedByLandmarks_of_extraction (h := 3) (w := 1) (q := 0) (by decide)
      ⟨.comp, by decide⟩ (by decide) ⟨.comp, by decide⟩⟩

/-- The revised theory also orders the wh-headed analysis, which the paper rejects on the
distributional evidence of Section 4. -/
theorem orderedByPositionalHeads_whHeaded : whHeaded.OrderedByPositionalHeads := by decide

/-! ### Free relatives, (53), (55) to (58) -/

abbrev i := English.Pronouns.i.toWord
abbrev ate := English.Verbs.eat.toWord .past

/-- In (53), *I ate what they ate*, *what* is the object of the first *ate*, takes the second as its
complement, and is the second's extracted object. -/
def iAteWhatTheyAte : Analysis 5 where
  words := ![i, ate, what, they, ate]
  arcs := [(1, 0, .subj), (1, 2, .obj), (2, 4, .comp), (4, 2, .extractee), (4, 2, .obj),
    (4, 3, .subj)]
  root := 1

/-- The free relative (53) fails the 2007 theory whichever way it goes, as (55) does. -/
theorem not_orderedByLandmarks_iAteWhatTheyAte :
    ¬ iAteWhatTheyAte.parentGraph.IsTree ∧ ¬ iAteWhatTheyAte.OrderedByLandmarks :=
  ⟨Analysis.not_isTree_parentGraph (p := 2) (w := 4) ⟨.comp, by decide⟩ ⟨.obj, by decide⟩,
    Analysis.not_orderedByLandmarks_of_extraction (h := 4) (w := 2) (q := 1) (by decide)
      ⟨.obj, by decide⟩ (by decide) ⟨.comp, by decide⟩⟩

/-- The revised theory orders the free relative (53). -/
theorem orderedByPositionalHeads_iAteWhatTheyAte : iAteWhatTheyAte.OrderedByPositionalHeads := by
  decide

abbrev he := English.Pronouns.he.toWord
abbrev bought := English.Verbs.buy.toWord .past
abbrev cost := English.Verbs.cost.toWord .past
abbrev lots := (English.Nouns.lot.toWord .plural).get rfl

/-- In (55) and (56), *What he bought cost lots*, *What* is the subject of *cost*, takes *bought* as
its complement, and is *bought*'s extracted object. -/
def whatHeBoughtCostLots : Analysis 5 where
  words := ![what, he, bought, cost, lots]
  arcs := [(3, 0, .subj), (0, 2, .comp), (2, 0, .extractee), (2, 0, .obj), (2, 1, .subj),
    (3, 4, .comp)]
  root := 3

/-- In (55), the parent graph is not a tree, and taking every parent as a landmark fails to order
the sentence. -/
theorem not_orderedByLandmarks_whatHeBoughtCostLots :
    ¬ whatHeBoughtCostLots.parentGraph.IsTree ∧ ¬ whatHeBoughtCostLots.OrderedByLandmarks :=
  ⟨Analysis.not_isTree_parentGraph (p := 0) (w := 2) ⟨.comp, by decide⟩ ⟨.obj, by decide⟩,
    Analysis.not_orderedByLandmarks_of_extraction (h := 2) (w := 0) (q := 3) (by decide)
      ⟨.subj, by decide⟩ (by decide) ⟨.comp, by decide⟩⟩

/-- In (57a) to (57f), *What* is the landmark of *bought*, *bought* the positional head of *What*,
and *cost* the landmark of *What*. -/
theorem landmarks_whatHeBoughtCostLots :
    whatHeBoughtCostLots.IsLandmark 2 0 ∧ whatHeBoughtCostLots.PositionalHead 0 2 ∧
      whatHeBoughtCostLots.IsLandmark 0 3 ∧ ¬ whatHeBoughtCostLots.IsLandmark 0 2 := by
  decide

/-- In (56), *What he bought cost lots* is ordered by its positional heads. -/
theorem orderedByPositionalHeads_whatHeBoughtCostLots :
    whatHeBoughtCostLots.OrderedByPositionalHeads := by
  decide

abbrev we := English.Pronouns.we.toWord
abbrev saw := English.Verbs.see.toWord .past
abbrev happened := English.Verbs.happen.toWord .past

/-- In (58), *We saw what happened*, a subject free relative without extraction, *what* is the
complement of *saw*, takes *happened* as its complement, and is its subject. -/
def weSawWhatHappened : Analysis 4 where
  words := ![we, saw, what, happened]
  arcs := [(1, 0, .subj), (1, 2, .comp), (2, 3, .comp), (3, 2, .subj)]
  root := 1

/-- The mutual dependency of (58) would make *what* and *happened* each other's landmark, as in
(54). -/
theorem not_isTree_parentGraph_weSawWhatHappened : ¬ weSawWhatHappened.parentGraph.IsTree :=
  Analysis.not_isTree_parentGraph (p := 2) (w := 3) ⟨.comp, by decide⟩ ⟨.subj, by decide⟩

/-- The Subordinate Head Rule leaves *what* with its one landmark *saw*, and the 2007 theory
orders the subject free relative (58). -/
theorem orderedByLandmarks_weSawWhatHappened : weSawWhatHappened.OrderedByLandmarks := by
  decide

/-! ### The later theory of landmarks, (11) to (14)

In the later theory [hudson-2018] landmarks are chosen online by the Best Landmark Principle
rather than inherited, and in a mutual dependency either word may be the landmark of the other.
Hudson's analyses of (11b) to (11e), which the paper diagrams in (12) and (13), are ordered or not
by some choice of landmarks. -/

abbrev then_ := Word.mk' English.TemporalDeictic.then_.form .ADV
abbrev wonder := English.Verbs.wonder.toWord .base

/-- In (11b), *What happened then?*, *what* is the subject of *happened* and takes it as its
complement, and *then* follows *happened* as its adjunct. -/
def whatHappenedThen : Analysis 3 where
  words := ![what, happened, then_]
  arcs := [(1, 0, .subj), (0, 1, .comp), (1, 2, .postAdjunct)]
  root := 1

theorem landmarks_whatHappenedThen :
    (∃ root, ∃ c : whatHappenedThen.Choice,
      whatHappenedThen.Orders c.Landmark root ∧ c.Landmark 0 1) ∧
    ∃ root, ∃ c : whatHappenedThen.Choice,
      whatHappenedThen.Orders c.Landmark root ∧ c.Landmark 1 0 := by
  decide

/-- In (11c), *Then what happened?*, *then* precedes *happened* as its adjunct. -/
def thenWhatHappened : Analysis 3 where
  words := ![then_, what, happened]
  arcs := [(2, 0, .preAdjunct), (2, 1, .subj), (1, 2, .comp)]
  root := 2

theorem landmarks_thenWhatHappened : thenWhatHappened.OrderedByChosenLandmarks ∧
    ∀ root (c : thenWhatHappened.Choice),
      thenWhatHappened.Orders c.Landmark root → c.Landmark 1 2 := by
  decide

/-- In (11d), *I wonder what happened then*, *what* is the complement of *wonder*. -/
def iWonderWhatHappenedThen : Analysis 5 where
  words := ![i, wonder, what, happened, then_]
  arcs := [(1, 0, .subj), (1, 2, .comp), (2, 3, .comp), (3, 2, .subj), (3, 4, .postAdjunct)]
  root := 1

theorem landmarks_iWonderWhatHappenedThen : iWonderWhatHappenedThen.OrderedByChosenLandmarks ∧
    ∀ root (c : iWonderWhatHappenedThen.Choice),
      iWonderWhatHappenedThen.Orders c.Landmark root → c.Landmark 3 2 := by
  decide

/-- (11e), *I wonder then what happened*, has the dependencies of (11c) under *wonder*. -/
def iWonderThenWhatHappened : Analysis 5 where
  words := ![i, wonder, then_, what, happened]
  arcs := [(1, 0, .subj), (1, 3, .comp), (4, 2, .preAdjunct), (3, 4, .comp), (4, 3, .subj)]
  root := 1

/-- No choice of landmarks orders (11e), as the link from *then* to *happened* crosses the one from
*what* to *wonder* (13). -/
theorem not_orderedByChosenLandmarks_iWonderThenWhatHappened :
    ¬ iWonderThenWhatHappened.OrderedByChosenLandmarks := by
  decide

/-- In (14), *I wonder what they saw* with the wh word as head, *what* is the complement of
*wonder*, takes *saw* as its complement, and is its extracted object. -/
def iWonderWhatTheySaw : Analysis 5 where
  words := ![i, wonder, what, they, saw]
  arcs := [(1, 0, .subj), (1, 2, .comp), (2, 4, .comp), (4, 2, .extractee), (4, 2, .obj),
    (4, 3, .subj)]
  root := 1

/-- The later theory cannot order the extraction in (14), and the revision orders it. -/
theorem not_orderedByChosenLandmarks_iWonderWhatTheySaw :
    ¬ iWonderWhatTheySaw.OrderedByChosenLandmarks ∧
      iWonderWhatTheySaw.OrderedByPositionalHeads := by
  decide

end Gisborne2026
