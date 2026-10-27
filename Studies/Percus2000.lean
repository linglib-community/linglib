module

public import Linglib.Logic.Assignment
public import Linglib.Semantics.Reference.Context.Index

/-!
# Percus (2000): Constraints on Some Other Variables in Syntax

This file formalizes the situation-pronoun syntax of [percus-2000]. Every predicate carries a
situation pronoun, every clause introduces an indexed λ binding situations, and two
generalizations restrict which λ a pronoun may take: Generalization X (34), that the situation
pronoun a verb selects for is coindexed with the nearest λ above it, and Generalization Y
(39), that the situation pronoun an adverbial quantifier selects for is likewise locally
bound, whereas the pronoun inside a determiner phrase may be bound from higher up (`LF.GenX`,
`QLF.GenY`). For *Mary thinks that my brother is Canadian* (26a) this admits the indexing
(27), *my brother* transparent and *is Canadian* opaque, and excludes the indexing (33),
*my brother* opaque and *is Canadian* transparent. The paper's two scenarios are two models:
where Mary takes Allon, the speaker's brother, not to be the brother but to be Canadian, the
sentence is judged true, and only the licensed transparent-phrase indexing makes it so
(`scenario_allon`); where Mary takes Pierre, a Canadian, to be the brother and so to be
American, the sentence is judged false, and the one indexing that would make it true is the
excluded one (`scenario_pierre`). For *Mary thinks that my brother always won the game*
(35a), binding the quantifier's pronoun to the matrix λ, the indexing (37), would make the
sentence true when Mary is unaware of the games Pierre won, where it is judged false, and
binding it to the embedded λ, the indexing (38), makes it true when Mary is deluded about
games Pierre lost, where it is judged true (`scenario_unaware`, `scenario_deluded`).

## Implementation notes

Situation assignments specialize the assignments of `Logic/Assignment` to indices of world
and time, the λ-binding of situation pronouns being the predicate abstraction of
[heim-kratzer-1998]; the models have two worlds, with a trivial time coordinate for (26a)
and the rounds of the game for (35a). The coindexing of both embedded pronouns with the
matrix λ is ruled out independently of the generalizations (fn. 18), and the motivation of
Generalization X from counterfactuals (40) is not formalized.

## References

* [percus-2000]
* [heim-kratzer-1998]
-/

@[expose] public section

namespace Percus2000

open Kaplan

/-- An assignment of situations to variable indices. -/
abbrev SituationAssignment (W T : Type*) := Assignment (Index W T)

/-- Belief with situation binding: the complement holds at every doxastic alternative of the
agent, the binder `n` reset to that alternative. -/
def believeSit {W T E : Type*} (dox : E → Index W T → List (Index W T)) (agent : E) (n : ℕ)
    (complement : SituationAssignment W T → Prop) (g : SituationAssignment W T)
    (s : Index W T) : Prop :=
  ∀ s' ∈ dox agent s, complement (Function.update g n s')

instance {W T E : Type*} (dox : E → Index W T → List (Index W T)) (agent : E) (n : ℕ)
    (complement : SituationAssignment W T → Prop) [DecidablePred complement]
    (g : SituationAssignment W T) (s : Index W T) :
    Decidable (believeSit dox agent n complement g s) := by
  unfold believeSit; infer_instance

/-- An adverb of quantification over the situations its restrictor supplies, the binder `n`
reset to each. -/
def alwaysAt {W T : Type*} (domain : Index W T → List (Index W T)) (restrictor : Index W T)
    (n : ℕ) (scope : SituationAssignment W T → Prop) (g : SituationAssignment W T) : Prop :=
  ∀ s' ∈ domain restrictor, scope (Function.update g n s')

instance {W T : Type*} (domain : Index W T → List (Index W T)) (restrictor : Index W T)
    (n : ℕ) (scope : SituationAssignment W T → Prop) [DecidablePred scope]
    (g : SituationAssignment W T) : Decidable (alwaysAt domain restrictor n scope g) := by
  unfold alwaysAt; infer_instance

/-! ### Generalizations X (34) and Y (39) -/

/-- An indexing of the embedded clause of an attitude sentence, the positions S and T of
(26b): the matrix λ carries index 1 and the embedded λ index 2, and the indexing records the
λ the embedded verb's situation pronoun and the embedded determiner phrase's pronoun take. -/
structure LF where
  verb : ℕ
  noun : ℕ
  deriving DecidableEq

/-- Generalization X (34): the verb's situation pronoun is coindexed with the nearest λ; the
determiner phrase's pronoun is unconstrained. -/
def LF.GenX (lf : LF) : Prop := lf.verb = 2

instance : DecidablePred LF.GenX := λ lf => inferInstanceAs (Decidable (lf.verb = 2))

/-- The indexing (27), S = s₂ and T = s₁: the determiner phrase transparent and the predicate
opaque. -/
def transparentDP : LF := ⟨2, 1⟩

/-- The indexing (33), S = s₁ and T = s₂: the predicate transparent and the determiner phrase
opaque. -/
def transparentPredicate : LF := ⟨1, 2⟩

/-- Both pronouns bound by the embedded λ: everything opaque. -/
def allOpaque : LF := ⟨2, 2⟩

-- Generalization X
theorem genX_indexings :
    allOpaque.GenX ∧ transparentDP.GenX ∧ ¬ transparentPredicate.GenX := by
  decide

/-- An indexing for an adverb of quantification in an attitude complement, the position S of
(35b): the λ its situation pronoun takes. -/
structure QLF where
  quant : ℕ
  deriving DecidableEq

/-- Generalization Y (39): the adverb's situation pronoun is coindexed with the nearest λ. -/
def QLF.GenY (q : QLF) : Prop := q.quant = 2

instance : DecidablePred QLF.GenY := λ q => inferInstanceAs (Decidable (q.quant = 2))

/-! ### The models -/

/-- The actual world and Mary's belief world. -/
inductive W where
  | actual
  | belief
  deriving DecidableEq

inductive Person where
  | mary
  | allon
  | pierre
  deriving DecidableEq

/-- The speaker's brother in a world: Allon in fact, Pierre in Mary's belief world, where she
takes Pierre to be the brother and Allon not to be. -/
def brother : W → Person
  | .actual => .allon
  | .belief => .pierre

/-- Situations with a trivial time coordinate. -/
abbrev Sit := Index W Unit

def sActual : Sit := ⟨.actual, ()⟩
def sBelief : Sit := ⟨.belief, ()⟩

/-- The paper's two scenarios for (26a): Mary takes Allon not to be the brother but to be
Canadian, and the sentence is judged true; Mary takes Pierre, a Canadian, to be the brother
and, knowing the speaker is American, to be American, and the sentence is judged false. -/
inductive Scenario where
  | allon
  | pierre
  deriving DecidableEq

/-- Who is Canadian in which world under each scenario. -/
def IsCanadian : Scenario → Person → Sit → Prop
  | .allon, .allon, ⟨.belief, _⟩ => True
  | .pierre, .pierre, ⟨.actual, _⟩ => True
  | _, _, _ => False

instance (sc : Scenario) (p : Person) (s : Sit) : Decidable (IsCanadian sc p s) := by
  unfold IsCanadian
  obtain ⟨w, _⟩ := s
  cases sc <;> cases p <;> cases w <;> infer_instance

/-- Mary's doxastic alternatives: the belief world. -/
def doxMary : Sit → List Sit := λ _ => [sBelief]

def g₀ : SituationAssignment W Unit := λ _ => sActual

/-- The reading of (26a) under an indexing, (28b) and (34b): at every belief alternative of
Mary's, the brother in the world the determiner phrase's pronoun denotes is Canadian at the
situation the verb's pronoun denotes. -/
def canadianReading (sc : Scenario) (lf : LF) : Prop :=
  believeSit (λ _ => doxMary) Person.mary 2
    (λ g => IsCanadian sc (brother (g lf.noun).world) (g lf.verb)) g₀ sActual

instance (sc : Scenario) (lf : LF) : Decidable (canadianReading sc lf) := by
  unfold canadianReading believeSit; infer_instance

/-- The first scenario: the sentence is judged true, and the licensed transparent-phrase
indexing (27) is what makes it true, the all-opaque indexing making it false. -/
theorem scenario_allon :
    canadianReading .allon transparentDP ∧ ¬ canadianReading .allon allOpaque := by
  decide

/-- In the second scenario only the transparent-predicate indexing (33) makes the sentence true, and
Generalization X excludes it. -/
theorem scenario_pierre :
    canadianReading .pierre transparentPredicate ∧ ¬ transparentPredicate.GenX ∧
      ¬ canadianReading .pierre transparentDP ∧ ¬ canadianReading .pierre allOpaque := by
  decide

/-! ### Generalization Y -/

/-- Three rounds of the game. -/
inductive Round where
  | r1
  | r2
  | r3
  deriving DecidableEq

/-- Situations with a round as their time coordinate. -/
abbrev RSit := Index W Round

/-- The paper's two scenarios for (35a): Mary, unaware of the games, wrongly takes Pierre to
be the brother, and Pierre won every game, the sentence being judged false; Mary is deluded
that Pierre, whom she takes to be the brother, won every game he in fact lost, the sentence
being judged true. -/
inductive GameScenario where
  | unaware
  | deluded
  deriving DecidableEq

/-- Who won which round in which world under each scenario. -/
def Won : GameScenario → Person → RSit → Prop
  | .unaware, .pierre, ⟨.actual, _⟩ => True
  | .deluded, .pierre, ⟨.belief, _⟩ => True
  | _, _, _ => False

instance (sc : GameScenario) (p : Person) (s : RSit) : Decidable (Won sc p s) := by
  unfold Won
  obtain ⟨w, _⟩ := s
  cases sc <;> cases p <;> cases w <;> infer_instance

/-- The rounds of a situation's world. -/
def rounds (s : RSit) : List RSit := [⟨s.world, .r1⟩, ⟨s.world, .r2⟩, ⟨s.world, .r3⟩]

/-- Mary's doxastic alternatives, round by round. -/
def doxMaryR : RSit → List RSit := λ s => [⟨.belief, s.time⟩]

def g₃ : SituationAssignment W Round := λ _ => ⟨.actual, .r1⟩

/-- The reading of (35a) under an indexing, (37b) and (38b): the determiner phrase's pronoun
is bound by the embedded λ, and the adverb ranges over the rounds of the world its pronoun
denotes. -/
def alwaysReading (sc : GameScenario) (q : QLF) : Prop :=
  believeSit (λ _ => doxMaryR) Person.mary 2
    (λ g => alwaysAt rounds (g q.quant) 3 (λ g' => Won sc (brother (g 2).world) (g' 3)) g)
    g₃ ⟨.actual, .r1⟩

instance (sc : GameScenario) (q : QLF) : Decidable (alwaysReading sc q) := by
  unfold alwaysReading believeSit alwaysAt; infer_instance

/-- The indexing (37), the adverb's pronoun bound by the matrix λ, would make the sentence true
where it is judged false; Generalization Y excludes it. -/
theorem scenario_unaware :
    alwaysReading .unaware ⟨1⟩ ∧ ¬ (⟨1⟩ : QLF).GenY ∧ ¬ alwaysReading .unaware ⟨2⟩ := by
  decide

/-- The indexing (38), binding the adverb's pronoun by the embedded λ, makes the sentence true where
it is judged true, and matrix binding does not. -/
theorem scenario_deluded :
    alwaysReading .deluded ⟨2⟩ ∧ (⟨2⟩ : QLF).GenY ∧ ¬ alwaysReading .deluded ⟨1⟩ := by
  decide

end Percus2000
