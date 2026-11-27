/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.Examples.Larson1988
public import Linglib.Syntax.Tree.Shell
public import Linglib.Syntax.Tree.Cat
public import Linglib.Languages.English.Nouns
public import Linglib.Languages.English.Determiners
public import Linglib.Languages.English.Verbs.Levin
public import Linglib.Syntax.Category.Adposition.Word
public import Linglib.Syntax.Category.Determiner.Word
public import Linglib.Syntax.Category.Noun.Word

/-!
# Larson (1988): On the Double Object Construction

A phrase is `[XP Spec [X′ X YP]]`, a head with one complement and one specifier, and a verb with
several arguments projects a stack of such phrases, `stack`: the lowest argument is the
complement of the verb and the next its specifier, and each further argument is the specifier of
a phrase whose head is empty and whose complement is the phrase below. At D-Structure the verb is
the lowest head, `dLayers`, and at S-Structure it has raised to the highest, leaving a trace in
each head below, `sLayers`. Whatever the heads, one argument c-commands another exactly when it
is the higher (`cCommands_argPos_iff`), so when the roles of the arguments descend the hierarchy
agent > theme > goal > oblique, one argument c-commands another exactly when its role is the
higher (`cCommands_argPos_iff_role_lt`). In *John sent a letter to Mary* the theme therefore
c-commands the goal and not conversely, where a flat verb phrase has its two objects c-command
each other and a left-branching one has the second c-command the first.

PASSIVE assigns the role of a specifier to an adjunct of its sister, `Shell.demote`, and moves a
noun phrase into the specifier. In the lower verb phrase it is Dative Shift: the theme is adjoined
to V′ and the goal moves to the specifier, which gives the double object construction
`doubleObject`, where the goal c-commands the theme and not conversely
(`cCommands_doubleObject`). In the clause it is Passive, `passive`, where the subject c-commands
the *by*-phrase and not conversely. The dative passive *Mary was sent a letter* moves the goal of
the oblique structure to the subject in one step, `indirectPassive`. Of two objects in either
frame, the one that licenses an anaphor, binds a pronoun, moves as a *wh*-phrase, or licenses
*the other* or a polarity item in the other is the one that c-commands the other
(`acceptable_iff_cCommands`).

Dative Shift deletes *to*, and the deletion is recoverable when the roles the verb assigns to its
indirect object include the role *to* assigns. A verb shifts exactly when they do
(`acceptable_iff_recoverable`).

## Implementation notes

* C-command is that of the first branching node, which the paper assumes. The categories V, V′
  and VP are one category `V`, and I, I′ and IP one category `Aux`; an empty position is a node
  without daughters.
* The asymmetry among the arguments rests on `PhraseStructure.commands_of_covBy_of_lt` and
  `PhraseStructure.not_commands_of_covBy_of_lt`, which hold of a path in any dominance order.
* The absorption of *to* is not an operation on trees: the D-Structure of the double object
  construction, `shiftedD`, has the goal as a bare noun phrase.
* The passive (24) adjoins the *by*-phrase to the verb phrase, the complement of the inflection,
  so it is not `Shell.demote` applied to a layer.
* The paper says of *send* and *promise* only that they specify a goal, and gives the pair
  beneficiary and goal for *give*, which heads no row with a verb column.
* The third line of (5d), with the preposition pied-piped, is not among the rows.

## TODO

* Case: the two Objective Cases, V′ Reanalysis and with it heavy NP shift, and the exclusion of
  *A letter was sent Mary*.
* The verbs that have the double object frame alone, *spare* and *envy*, the psych verbs, and the
  applicative constructions, where an affix on the verb makes the deletion recoverable.

## References

* [larson-1988]
* [barss-lasnik-1986]
-/

@[expose] public section

namespace Larson1988

open PhraseStructure Tree Shell

variable {W : Type*}

/-! ### Projection -/

/-- The empty position of category `c`. -/
abbrev empty (c : Cat) : Tree Cat W := .node c []

/-- Argument Demotion: the role of the specifier is assigned to an adjunct of X′, and the
specifier is empty. -/
def Shell.demote (L : Shell W) : Shell W := { L with spec := empty .N, adjunct := some L.spec }

variable {ls : List (Shell W)} {L : Shell W} {x : Tree Cat W} {i j k : ℕ}

/-! ### The Thematic Hierarchy -/

/-- The tiers of the Thematic Hierarchy, the lowest first: obliques of manner, place and time,
then goal, theme and agent. -/
inductive Role where
  | oblique
  | goal
  | theme
  | agent
  deriving DecidableEq, Fintype

/-- The height of a role on the hierarchy. -/
def Role.rank : Role → ℕ
  | .oblique => 0
  | .goal => 1
  | .theme => 2
  | .agent => 3

theorem Role.rank_injective : Function.Injective Role.rank := by
  intro a b
  cases a <;> cases b <;> simp [Role.rank]

instance : LinearOrder Role := LinearOrder.lift' Role.rank Role.rank_injective

/-- The height of a role, as an order embedding. -/
def Role.rankOrderEmbedding : Role ↪o ℕ := ⟨⟨Role.rank, Role.rank_injective⟩, Iff.rfl⟩

@[simp] theorem Role.coe_rankOrderEmbedding : ⇑Role.rankOrderEmbedding = Role.rank := rfl

/-- (P2): when the roles of the arguments of a projection descend the hierarchy, one argument
c-commands another exactly when its role is the higher. -/
theorem cCommands_argPos_iff_role_lt (ls : List (Shell W)) (x : Tree Cat W) {role : ℕ → Role}
    (hrole : StrictAntiOn role (Set.Iic ls.length)) (hi : i ≤ ls.length) (hj : j ≤ ls.length) :
    (stack ls x).CCommands (argPos ls i) (argPos ls j) ↔ role j < role i :=
  (cCommands_argPos_iff ls x hi hj).trans (hrole.lt_iff_gt hj hi).symm

/-! ### V Raising -/

/-- The layers of a D-Structure: the verb `v` is the head of the lowest of the specifiers `ss`,
and the heads above it are empty. -/
def dLayers (v : Tree Cat W) : List (Tree Cat W) → List (Shell W)
  | [] => []
  | [s] => [{ spec := s, head := v }]
  | s :: ss => { spec := s, head := empty .V } :: dLayers v ss

/-- The layers of an S-Structure: the verb has raised to the highest head, and each head below
is its trace. -/
def sLayers (v : Tree Cat W) : List (Tree Cat W) → List (Shell W)
  | [] => []
  | s :: ss => { spec := s, head := v } :: ss.map fun s ↦ { spec := s, head := trace 0 .V }

variable {v s agent theme goal prep infl byP : Tree Cat W} {ss : List (Tree Cat W)}

-- Before the verb raises the arguments all but the lowest precede it: *John a letter send to
-- Mary*.
theorem yield_stack_dLayers (v x : Tree Cat W) : ∀ {ss : List (Tree Cat W)}, ss ≠ [] →
    (stack (dLayers v ss) x).yield = ss.flatMap yield ++ (v.yield ++ x.yield)
  | [s], _ => by simp [dLayers]
  | s :: s' :: ss, _ => by
    simp [dLayers, yield_stack_dLayers v x (ss := s' :: ss) (by simp)]

-- After it raises only the highest does: *John send a letter to Mary*.
theorem yield_stack_sLayers (v s x : Tree Cat W) (ss : List (Tree Cat W)) :
    (stack (sLayers v (s :: ss)) x).yield =
      s.yield ++ (v.yield ++ (ss.flatMap yield ++ x.yield)) := by
  suffices h : (stack (ss.map fun s ↦ ({ spec := s, head := trace 0 .V } : Shell W)) x).yield =
      ss.flatMap yield ++ x.yield by simp [sLayers, h]
  induction ss with
  | nil => simp
  | cons s ss ih => simp [ih]

/-- Move α: the phrase at `src` takes the empty position `dst` and leaves the trace `i`. -/
def move (i : ℕ) (src dst : GornAddress) (t : Tree Cat W) : Tree Cat W :=
  t[src]?.elim t fun a ↦
    (t.replaceAt src.toList (trace i (Tree.cat a) : Tree Cat W)).replaceAt dst.toList a

/-! ### The oblique dative -/

/-- (13): the D-Structure of the oblique dative, the theme over the verb and the *to*-phrase. -/
abbrev obliqueD (v agent theme pp : Tree Cat W) : Tree Cat W :=
  stack (dLayers v [agent, theme]) pp

/-- (14): its S-Structure. -/
abbrev oblique (v agent theme pp : Tree Cat W) : Tree Cat W := stack (sLayers v [agent, theme]) pp

-- (14): the verb raises from the lower head to the upper.
theorem move_obliqueD (hv : Tree.cat v = .V) :
    move 0 ⟨[1, 1, 1, 0]⟩ ⟨[1, 0]⟩ (obliqueD v agent theme x) =
      oblique v agent theme x := by
  simp [move, obliqueD, oblique, dLayers, sLayers, Shell.over, Shell.bar, RoseTree.replaceAt_cons,
    hv]

/-! ### The structures the paper rejects -/

-- (4a): in a flat verb phrase the two objects c-command each other.
theorem cCommands_flat (v a b : Tree Cat W) :
    (node .V [v, a, b]).CCommands (.of 1) (.of 2) ∧
      (node .V [v, a, b]).CCommands (.of 2) (.of 1) := by
  have h : (1 : GornAddress) ∈ (node .V [v, a, b]).branching := by
    simp [RoseTree.mem_branching]
  exact ⟨by simpa using RoseTree.cCommands_mul_of h (i := 1) (j := 2) (by decide) 1,
    by simpa using RoseTree.cCommands_mul_of h (i := 2) (j := 1) (by decide) 1⟩

-- (4b): in a left-branching one the second object c-commands the first and not conversely.
theorem cCommands_leftBranching (v a b : Tree Cat W) :
    (node .V [.node .V [v, a], b]).CCommands (.of 1) (.of 0 * .of 1) ∧
      ¬ (node .V [.node .V [v, a], b]).CCommands (.of 0 * .of 1) (.of 1) := by
  refine ⟨?_, ?_⟩
  · simpa using RoseTree.cCommands_mul_of (t := node .V [.node .V [v, a], b]) (p := 1)
      (by simp [RoseTree.mem_branching]) (i := 1) (j := 0) (by decide) (.of 1)
  · simpa using RoseTree.not_cCommands_mul_of_mul (t := node .V [.node .V [v, a], b])
      (p := 1) (i := 1) (j := 0) (q := .of 1) (by simp [RoseTree.mem_branching]) (by decide)
      (by decide)

/-! ### PASSIVE -/

/-- The layers of the double object construction at S-Structure: the goal in the lower
specifier, the theme the adjunct of V′. -/
abbrev shiftedLayers (v agent goal theme : Tree Cat W) : List (Shell W) :=
  [{ spec := agent, head := v }, { spec := goal, head := trace 0 .V, adjunct := some theme }]

/-- (80), with *to* absorbed: the D-Structure of the double object construction, the oblique
dative with the role of the lower specifier demoted. -/
abbrev shiftedD (v agent goal theme : Tree Cat W) : Tree Cat W :=
  stack ((dLayers v [agent, theme]).modify 1 Shell.demote) goal

/-- (26): the double object construction. The goal has moved to the lower specifier and the verb
has raised. -/
abbrev doubleObject (v agent goal theme : Tree Cat W) : Tree Cat W :=
  stack (shiftedLayers v agent goal theme) (trace 1 .N)

/-- (24): the passive. The object has moved to the subject, and the *by*-phrase is adjoined to
the verb phrase. -/
def passive (infl v patient byP : Tree Cat W) : Tree Cat W :=
  ({ cat := .Aux, spec := patient, head := infl } : Shell W).over
    (adjoin .V [node .V [v, trace 1 .N], byP])

/-- (40): the dative passive. The goal has moved from the complement of the verb to the subject,
and the theme is in the lower specifier. -/
abbrev indirectPassive (infl v goal theme : Tree Cat W) : Tree Cat W :=
  stack ({ cat := .Aux, spec := goal, head := infl } :: sLayers v [empty .N, theme]) (trace 1 .N)

-- (25), (26): Dative Shift is the movement of the goal to the lower specifier.
theorem move_move_shiftedD (hv : Tree.cat v = .V) (hg : Tree.cat goal = .N) :
    move 0 ⟨[1, 1, 1, 0, 0]⟩ ⟨[1, 0]⟩
      (move 1 ⟨[1, 1, 1, 0, 1]⟩ ⟨[1, 1, 0]⟩ (shiftedD v agent goal theme)) =
      doubleObject v agent goal theme := by
  simp [move, shiftedD, doubleObject, shiftedLayers, dLayers, Shell.demote, Shell.over, Shell.bar,
    RoseTree.replaceAt_cons, hv, hg]

-- (40): the dative passive is one movement of the goal out of the D-Structure of the oblique
-- dative, whose subject is empty.
theorem move_move_obliqueD (hv : Tree.cat v = .V) (hg : Tree.cat goal = .N) :
    move 1 ⟨[1, 1, 1, 1, 1, 1]⟩ ⟨[0]⟩ (move 0 ⟨[1, 1, 1, 1, 1, 0]⟩ ⟨[1, 1, 1, 0]⟩
      (({ cat := .Aux, spec := empty .N, head := infl } : Shell W).over
        (obliqueD v (empty .N) theme goal))) =
      indirectPassive infl v goal theme := by
  simp [move, obliqueD, indirectPassive, dLayers, sLayers, Shell.over, Shell.bar,
    RoseTree.replaceAt_cons, hv, hg]

theorem yield_doubleObject (v agent goal theme : Tree Cat W) :
    (doubleObject v agent goal theme).yield =
      agent.yield ++ (v.yield ++ (goal.yield ++ theme.yield)) := by
  simp [doubleObject, shiftedLayers]

/-- In the double object construction the goal c-commands the theme and not conversely. -/
theorem cCommands_doubleObject (v agent goal theme : Tree Cat W) :
    (doubleObject v agent goal theme).CCommands (specPos (shiftedLayers v agent goal theme) 1)
        (adjunctPos (shiftedLayers v agent goal theme) 1) ∧
      ¬ (doubleObject v agent goal theme).CCommands
        (adjunctPos (shiftedLayers v agent goal theme) 1)
        (specPos (shiftedLayers v agent goal theme) 1) :=
  cCommands_specPos_adjunctPos _ (by simp)

-- (27): in the passive the subject c-commands the *by*-phrase and not conversely.
theorem cCommands_passive (infl v patient byP : Tree Cat W) :
    (passive infl v patient byP).CCommands (.of 0) (.of 1 * (.of 1 * .of 1)) ∧
      ¬ (passive infl v patient byP).CCommands (.of 1 * (.of 1 * .of 1)) (.of 0) := by
  unfold passive
  refine ⟨?_, ?_⟩
  · simpa using RoseTree.cCommands_mul_of (p := 1) (Shell.one_mem_branching _ _) (i := 0) (j := 1)
      (by decide) (.of 1 * .of 1)
  · simpa using RoseTree.not_cCommands_mul_of_mul (p := 1) (i := 0) (j := 1) (q := .of 1 * .of 1)
      (by simpa using Shell.of_one_mem_branching _ _) (by decide) (by decide)

/-! ### The asymmetries of the two objects -/

open Examples

/-- The S-Structure of a frame. -/
def rep (v agent theme goal prep : Tree Cat W) : Frame → Tree Cat W
  | .oblique => oblique v agent theme (node .P [prep, goal])
  | .doubleObject => doubleObject v agent goal theme

/-- The position of an object in the S-Structure of a frame: in the oblique dative the theme is
the lower specifier and the goal the object of the preposition, and in the double object
construction the goal is the lower specifier and the theme the adjunct. -/
def objectPos (v agent theme goal : Tree Cat W) : Frame → Argument → GornAddress
  | .oblique, .theme => specPos (sLayers v [agent, theme]) 1
  | .oblique, .goal => pos (sLayers v [agent, theme]) 2 * .of 1
  | .doubleObject, .goal => specPos (shiftedLayers v agent goal theme) 1
  | .doubleObject, .theme => adjunctPos (shiftedLayers v agent goal theme) 1

/-- The object in the lower specifier: the theme of the oblique dative, and the goal of the
double object construction. -/
def higher : Frame → Argument
  | .oblique => .theme
  | .doubleObject => .goal

/-- The other object. -/
def other : Argument → Argument
  | .theme => .goal
  | .goal => .theme

theorem getElem?_objectPos (f : Frame) :
    (rep v agent theme goal prep f)[objectPos v agent theme goal f .theme]? = some theme ∧
      (rep v agent theme goal prep f)[objectPos v agent theme goal f .goal]? = some goal := by
  cases f <;> exact ⟨rfl, rfl⟩

theorem cCommands_objectPos_iff (f : Frame) (r : Argument) :
    (rep v agent theme goal prep f).CCommands (objectPos v agent theme goal f r)
      (objectPos v agent theme goal f (other r)) ↔ r = higher f := by
  have hd := cCommands_doubleObject v agent goal theme
  cases f <;> cases r
  · exact iff_of_true (cCommands_specPos_of_lt _ (i := 1) (j := 2) (by decide) le_rfl
      (GornAddress.le_mul_right _ _)) rfl
  · exact iff_of_false (not_cCommands_specPos_of_lt _ (i := 1) (j := 2) (by decide) le_rfl
      (GornAddress.le_mul_right _ _)) (by decide)
  · exact iff_of_false hd.2 (by decide)
  · exact iff_of_true hd.1 rfl

/-- A dependency between the two objects is acceptable exactly when the object that must
c-command the other does. -/
theorem acceptable_iff_cCommands (v agent theme goal prep : Tree Cat W) :
    ∀ e ∈ Examples.all, ∀ f ∈ Examples.frame e, ∀ r ∈ Examples.licensor e,
      (e.judgment = .acceptable ↔
        (rep v agent theme goal prep f).CCommands (objectPos v agent theme goal f r)
          (objectPos v agent theme goal f (other r))) := by
  simp only [cCommands_objectPos_iff]
  decide

example : Datum.ReadCount Examples.licensor Examples.all 24 := by decide

/-! ### Recoverability -/

/-- The roles a verb or a preposition assigns to an indirect object. -/
inductive IndirectRole where
  | beneficiary
  /-- The goal of motion along a path. -/
  | goal
  deriving DecidableEq

/-- The role *to* assigns. -/
def toRoles : Finset IndirectRole := {.goal}

/-- The roles a verb assigns to its indirect object: *send* and *promise* specify a goal, and
the verbs of contributing, with *give away* and *give out*, a beneficiary alone. -/
def roles : Examples.Verb → Finset IndirectRole
  | .send | .promise => {.goal}
  | .donate | .distribute | .contribute | .giveAway | .giveOut => {.beneficiary}

/-- A verb has the double object frame exactly when the role of *to* is among the roles it
assigns to its indirect object, so that deleting *to* is recoverable. -/
theorem acceptable_iff_recoverable :
    ∀ e ∈ Examples.all, ∀ v ∈ Examples.verb e, ∀ f ∈ Examples.frame e,
      (e.judgment = .acceptable ↔ (f = .doubleObject → toRoles ⊆ roles v)) := by
  decide

example : Datum.ReadCount Examples.verb Examples.all 14 := by decide

/-! ### *John sent a letter to Mary* and *John sent Mary a letter* -/

section Sentences

open English Morphology

abbrev word (c : Cat) (w : Word) : Tree Cat Word := .terminal c w

abbrev john := word .N Nouns.john.toWord
abbrev mary := word .N Nouns.mary.toWord
abbrev sent := word .V (Verbs.send.toWord .past)
abbrev aLetter : Tree Cat Word :=
  .node .N [word .Det Determiners.a.toWord, word .N (.mk' "letter" .NOUN)]
abbrev to_ := word .P Adpositions.to_.toWord

theorem yield_oblique :
    ((rep sent john aLetter mary to_ .oblique).yield.map (·.form)) =
      ["John", "sent", "a", "letter", "to", "Mary"] := by
  decide

theorem yield_shifted :
    ((move 0 ⟨[1, 1, 1, 0, 0]⟩ ⟨[1, 0]⟩ (move 1 ⟨[1, 1, 1, 0, 1]⟩ ⟨[1, 1, 0]⟩
      (shiftedD sent john mary aLetter))).yield.map (·.form)) =
      ["John", "sent", "Mary", "a", "letter"] := by
  decide

end Sentences

end Larson1988
