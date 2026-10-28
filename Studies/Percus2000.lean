module

public import Linglib.Semantics.Composition.Tree
public import Linglib.Semantics.Reference.Context.Index
public import Linglib.Data.Examples.Percus2000

/-!
# Percus (2000): Constraints on Some Other Variables in Syntax

Situation pronouns are covert variables over situations: a predicate selects one, a description
contains one, and a λ binding situations tops the complement of an attitude verb and the scope of
an adverbial quantifier. Percus argues that the pronoun a verb or an adverbial quantifier selects
must be coindexed with the nearest λ above it, while the pronoun in a description may be bound from
higher up. With situation pronouns as traces of type $s$, [the composition engine computes his
interpretations](##interp_lf), his two generalizations are [one condition on
trees](##locallyBound_lf), and the indexings it admits match the judgments [for the attitude
report](##judgments_26a) and [for the adverbial quantifier](##judgments_35a).

## Implementation notes

A situation is a world and a round of the game, and Mary's belief alternatives keep the round. The
condition that Mary be in the situation of evaluation, shared by every indexing, is omitted, and
*my brother* denotes the brother in the world of its situation, without the uniqueness Percus
builds in. The restrictor of *always* is a free variable of type $⟨s,t⟩$, which the context assigns
the rounds of the game.

A situation pronoun counts as selected when its sister denotes a proposition. This covers the
pronoun a verb selects and the one an adverbial quantifier selects at once, where Percus states the
two generalizations separately; the pronoun inside *my brother* has a sister of type $⟨s,e⟩$ and is
not selected. The nearest λ counts only binders of situation pronouns, as Percus restricts it. The
indexing that binds both embedded pronouns to the higher λ, which Percus sets aside on independent
grounds, is excluded by the same condition here.

## Errata

The number (34) labels both the interpretation of the indexing (33) and Generalization X.

## References

* [percus-2000]
* [von-fintel-heim-2011]
* [heim-kratzer-1998]
-/

@[expose] public section

namespace Percus2000

open Montague PhraseStructure Tree Kaplan

/-! ### The model -/

/-- The actual world and Mary's belief world. -/
inductive World where
  | actual
  | belief
  deriving DecidableEq, Fintype

inductive Person where
  | mary
  | allon
  | pierre
  deriving DecidableEq

/-- The rounds of the game. -/
inductive Round where
  | r1
  | r2
  | r3
  deriving DecidableEq, Fintype

/-- A situation is a world and a round. -/
abbrev Sit := Index World Round

/-- The situation of utterance. -/
def s₀ : Sit := (.actual, .r1)

/-- The speaker's brother in a world: Allon in fact, Pierre in Mary's belief world, where she
takes Pierre to be the brother. -/
def brother : World → Person
  | .actual => .allon
  | .belief => .pierre

/-- A believer's alternatives to a situation: the belief world at the same round. -/
def dox (_ : Person) (s : Sit) : List Sit := [(.belief, s.time)]

/-- The rounds of the game in the world of a situation. -/
def rounds (s : Sit) : List Sit := [(s.world, .r1), (s.world, .r2), (s.world, .r3)]

/-- The rounds of the game: every situation of the model is a round. -/
def gameRound (_ : Sit) : Prop := True

instance : DecidablePred gameRound := fun _ ↦ inferInstanceAs (Decidable True)

/-- The paper's scenarios: three for (26a), two for (35a). -/
inductive Scenario where
  | allon
  | pierreCanadian
  | pierreAmerican
  | unaware
  | deluded
  deriving DecidableEq

/-- Who is Canadian in which world under each scenario. -/
def IsCanadian : Scenario → Person → World → Prop
  | .allon, .allon, .belief => True
  | .pierreCanadian, .pierre, _ => True
  | .pierreAmerican, .pierre, .actual => True
  | _, _, _ => False

instance (sc : Scenario) (x : Person) (w : World) : Decidable (IsCanadian sc x w) := by
  cases sc <;> cases x <;> cases w <;> unfold IsCanadian <;> infer_instance

/-- Who won the game in which situation under each scenario. -/
def Won : Scenario → Person → Sit → Prop
  | .unaware, .pierre, (.actual, _) => True
  | .deluded, .pierre, (.belief, _) => True
  | _, _, _ => False

instance (sc : Scenario) (x : Person) (s : Sit) : Decidable (Won sc x s) := by
  obtain ⟨w, r⟩ := s
  cases sc <;> cases x <;> cases w <;> unfold Won <;> infer_instance

/-! ### The lexicon and the structures -/

/-- The words of (26a) and (35a); *won* includes its object *the game*. -/
inductive Word where
  | mary
  | thinks
  | myBrother
  | isCanadian
  | always
  | won

/-- The denotations: *thinks* is universal over its subject's belief alternatives, *my brother*
the brother in the world of its situation, and *always* universal over the rounds in the world of
its situation that its restrictor holds of. -/
def lex (sc : Scenario) : Word → Option (Denotation Person Sit)
  | .mary => some ⟨.e, Person.mary⟩
  | .thinks => some ⟨(.s ⇒ .t) ⇒ .e ⇒ .s ⇒ .t, fun p x s ↦ ∀ s' ∈ dox x s, p s'⟩
  | .myBrother => some ⟨.s ⇒ .e, fun s ↦ brother s.world⟩
  | .isCanadian => some ⟨.e ⇒ .s ⇒ .t, fun x s ↦ IsCanadian sc x s.world⟩
  | .always => some ⟨(.s ⇒ .t) ⇒ (.s ⇒ .t) ⇒ .s ⇒ .t,
      fun scope restr s ↦ ∀ s' ∈ rounds s, restr s' → scope s'⟩
  | .won => some ⟨.e ⇒ .s ⇒ .t, fun x s ↦ Won sc x s⟩

/-- The types of the words, the same in every scenario. -/
def wordTy (w : Word) : Option Ty := (lex .allon w).map (·.1)

/-- The typing of the indices: the restrictor `ssh₈` of *always* is a variable over propositions,
every other index a situation pronoun. -/
def indexTy (n : ℕ) : Ty := if n = 8 then .s ⇒ .t else .s

/-- The context's assignment: `ssh₈` denotes the rounds of the game and a free situation pronoun
the situation of utterance. -/
def g₀ (n : ℕ) : Ty.Domain Person Sit (indexTy n) := by
  unfold indexTy
  split
  · exact gameRound
  · exact s₀

/-- The two λ's of (26b) and (35b): `upper` is the λ adjoined to the root, index 1, and `lower` the
λ below *thinks*, index 2. -/
inductive Binder where
  | upper
  | lower
  deriving DecidableEq, Fintype

/-- The index of a λ. -/
def Binder.index : Binder → ℕ
  | .upper => 1
  | .lower => 2

/-- The situation a pronoun coindexed with a λ denotes, at the situation of evaluation `s` and
Mary's belief alternative `s'`. -/
def Binder.sit : Binder → Sit → Sit → Sit
  | .upper, s, _ => s
  | .lower, _, s' => s'

/-- The matrix [λ₁ [s₁ [Mary [thinks _]]]] of (26b) and (35b), over the complement of *thinks*. -/
def matrix (X : Tree Unit Word) : Tree Unit Word :=
  .binder 1 (.bin (.tr 1) (.bin (.leaf .mary) (.bin (.leaf .thinks) X)))

/-- The embedded clause of (26b), [λ₂ [S [[my brother T] is Canadian]]]. -/
def vpb (S T : Binder) : Tree Unit Word :=
  .binder 2 (.bin (.tr S.index) (.bin (.bin (.leaf .myBrother) (.tr T.index)) (.leaf .isCanadian)))

/-- The embedded clause of (35b), [λ₂ [S [ssh₈ [always [λ₃ [s₃ [[my brother s₂] won]]]]]]]. -/
def advp (S : Binder) : Tree Unit Word :=
  .binder 2 (.bin (.tr S.index) (.bin (.tr 8) (.bin (.leaf .always)
    (.binder 3 (.bin (.tr 3) (.bin (.bin (.leaf .myBrother) (.tr 2)) (.leaf .won)))))))

/-- (26b), with the pronoun that *is Canadian* selects coindexed with `S` and the pronoun in *my
brother* with `T`: (27) is `lf .lower .upper`, (31) `lf .lower .lower` and (33)
`lf .upper .lower`. -/
def lf (S T : Binder) : Tree Unit Word := matrix (vpb S T)

/-- (35b), with the pronoun that *always* selects coindexed with `S`: (37) is `lfAlways .upper` and
(38) `lfAlways .lower`. -/
def lfAlways (S : Binder) : Tree Unit Word := matrix (advp S)

/-! ### The interpretations

As Percus computes them, the value of the embedded clause comes first, under any assignment, and
then the value of the matrix over it. -/

open scoped Assignment

theorem interp_matrix {sc : Scenario} {X : Tree Unit Word}
    {p : (∀ n, Ty.Domain Person Sit (indexTy n)) → Sit → Prop}
    (h : ∀ g, interpWith indexTy (lex sc) g X = some ⟨.s ⇒ .t, p g⟩) :
    interpWith indexTy (lex sc) g₀ (matrix X) =
      some ⟨.s ⇒ .t, fun s ↦ ∀ s' ∈ dox .mary s, p (g₀[1 ↦ s]) s'⟩ := by
  simp only [matrix, interpWith_bind, interpWith_node_binary, interpWith_trace,
    interpWith_terminal, h, lex, Option.bind_some]
  rfl

-- (30b)
theorem interp_vpb (sc : Scenario) (S T : Binder) (g : ∀ n, Ty.Domain Person Sit (indexTy n)) :
    interpWith indexTy (lex sc) g (vpb S T) = some ⟨.s ⇒ .t, fun s' ↦
      IsCanadian sc (brother (T.sit (g 1) s').world) (S.sit (g 1) s').world⟩ := by
  cases S <;> cases T <;> rfl

theorem interp_advp (sc : Scenario) (S : Binder) (g : ∀ n, Ty.Domain Person Sit (indexTy n)) :
    interpWith indexTy (lex sc) g (advp S) = some ⟨.s ⇒ .t, fun s' ↦
      ∀ r ∈ rounds (S.sit (g 1) s'), g 8 r → Won sc (brother s'.world) r⟩ := by
  cases S <;> rfl

/-- The engine computes Percus's interpretations of (26b): at a situation `s`, every belief
alternative `s'` of Mary's is such that the brother in the world of the situation `T` names is
Canadian in the world of the situation `S` names ((28b), (32b), (34b)). -/
theorem interp_lf (sc : Scenario) (S T : Binder) :
    interpWith indexTy (lex sc) g₀ (lf S T) = some ⟨.s ⇒ .t, fun s ↦
      ∀ s' ∈ dox .mary s, IsCanadian sc (brother (T.sit s s').world) (S.sit s s').world⟩ := by
  rw [lf, interp_matrix (interp_vpb sc S T)]
  simp only [Function.update_self]

theorem g₀_eight : g₀ 8 = gameRound := rfl

-- (37b), (38b)
theorem interp_lfAlways (sc : Scenario) (S : Binder) :
    interpWith indexTy (lex sc) g₀ (lfAlways S) = some ⟨.s ⇒ .t, fun s ↦
      ∀ s' ∈ dox .mary s, ∀ r ∈ rounds (S.sit s s'), gameRound r →
        Won sc (brother s'.world) r⟩ := by
  rw [lfAlways, interp_matrix (interp_advp sc S)]
  simp only [Function.update_self, Function.update_of_ne (show (8 : ℕ) ≠ 1 by decide), g₀_eight]

/-- A structure of type $⟨s,t⟩$ is true at the situation of utterance in a scenario. -/
def Holds (sc : Scenario) (t : Tree Unit Word) : Prop :=
  ∃ p, interpWith indexTy (lex sc) g₀ t = some ⟨.s ⇒ .t, p⟩ ∧ p s₀

theorem holds_lf {sc : Scenario} {S T : Binder} :
    Holds sc (lf S T) ↔
      ∀ s' ∈ dox .mary s₀, IsCanadian sc (brother (T.sit s₀ s').world) (S.sit s₀ s').world := by
  simp [Holds, interp_lf]

theorem holds_lfAlways {sc : Scenario} {S : Binder} :
    Holds sc (lfAlways S) ↔ ∀ s' ∈ dox .mary s₀, ∀ r ∈ rounds (S.sit s₀ s'), gameRound r →
      Won sc (brother s'.world) r := by
  simp [Holds, interp_lfAlways]

/-! ### Generalizations X and Y -/

/-- The situation pronoun a binary node selects, if one daughter is a situation pronoun whose sister
denotes a proposition, paired with the index `k` of the nearest situation λ above it. -/
def selectedAt (k : Option ℕ) : List (Tree Unit Word) → List (ℕ × Option ℕ)
  | [Tree.trace n _, b] | [b, Tree.trace n _] =>
    if indexTy n = .s ∧ ty? indexTy wordTy b = some (.s ⇒ .t) then [(n, k)] else []
  | _ => []

mutual

/-- The selected situation pronouns of a tree, each paired with the index of the nearest situation
λ above it, given that index `k` above the tree. -/
def selected : Tree Unit Word → Option ℕ → List (ℕ × Option ℕ)
  | RoseTree.node (.bind n _) cs, k => selectedList cs (if indexTy n = .s then some n else k)
  | RoseTree.node _ cs, k => selectedAt k cs ++ selectedList cs k

/-- The selected situation pronouns of a list of sisters. -/
def selectedList : List (Tree Unit Word) → Option ℕ → List (ℕ × Option ℕ)
  | [], _ => []
  | t :: ts, k => selected t k ++ selectedList ts k

end

/-- Generalizations X and Y: every selected situation pronoun is coindexed with the nearest
situation λ above it. -/
def LocallyBound (t : Tree Unit Word) : Prop := ∀ p ∈ selected t none, p.2 = some p.1

instance : DecidablePred LocallyBound := fun t ↦
  inferInstanceAs (Decidable (∀ p ∈ selected t none, p.2 = some p.1))

/-- Generalization X admits exactly the structures of (26b) whose predicate pronoun is coindexed
with the lower λ, (27) and (31), whatever λ binds the pronoun in the description. -/
theorem locallyBound_lf (S T : Binder) : LocallyBound (lf S T) ↔ S = .lower := by
  revert S T; decide

-- Generalization Y (39)
theorem locallyBound_lfAlways (S : Binder) : LocallyBound (lfAlways S) ↔ S = .lower := by
  revert S; decide

/-! ### The judgments -/

open Examples in
/-- The structures Generalization X admits make (26a) true in exactly the scenarios where it is
judged true, while the excluded indexing (33) would make it true where it is judged false. -/
theorem judgments_26a :
    ((∃ S T, LocallyBound (lf S T) ∧ Holds .allon (lf S T)) ↔
      ex26a_allon.feature? "truthValue" = some "true") ∧
    ((∃ S T, LocallyBound (lf S T) ∧ Holds .pierreCanadian (lf S T)) ↔
      ex26a_pierreCanadian.feature? "truthValue" = some "true") ∧
    ((∃ S T, LocallyBound (lf S T) ∧ Holds .pierreAmerican (lf S T)) ↔
      ex26a_pierreAmerican.feature? "truthValue" = some "true") ∧
    Holds .pierreAmerican (lf .upper .lower) := by
  simp only [holds_lf]
  decide

open Examples in
/-- The structure Generalization Y admits makes (35a) true in exactly the scenario where it is
judged true, while the excluded indexing (37) would make it true where it is judged false. -/
theorem judgments_35a :
    ((∃ S, LocallyBound (lfAlways S) ∧ Holds .unaware (lfAlways S)) ↔
      ex35a_unaware.feature? "truthValue" = some "true") ∧
    ((∃ S, LocallyBound (lfAlways S) ∧ Holds .deluded (lfAlways S)) ↔
      ex35a_deluded.feature? "truthValue" = some "true") ∧
    Holds .unaware (lfAlways .upper) := by
  simp only [holds_lfAlways]
  decide

end Percus2000
