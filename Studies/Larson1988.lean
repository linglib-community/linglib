/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.Examples.Larson1988
public import Linglib.Syntax.Tree.Basic
public import Linglib.Syntax.Command.RoseTree
public import Linglib.Syntax.Cat
public import Linglib.Fragments.English.Nouns
public import Linglib.Fragments.English.Determiners
public import Linglib.Fragments.English.Verbs.Levin

/-!
# Larson (1988): On the Double Object Construction

A phrase is `[XP Spec [X′ X YP]]`: a head with one complement and one specifier. A verb with the
arguments $a_0, \dots, a_n$, the highest first, projects a stack of such phrases, `shells`. The
lowest argument is the complement of the verb and the next its specifier; each further argument
is the specifier of a shell whose head is empty and whose complement is the phrase below. At
D-Structure the verb is the lowest head, `dStructure`, and at S-Structure it has raised to the
highest, leaving a trace in each head below, `sStructure`. Whatever the heads, the argument $a_i$
c-commands $a_j$ exactly when $i < j$ (`cCommands_argPos_iff`), so when the roles of the arguments
descend the hierarchy agent > theme > goal > oblique, one argument c-commands another exactly when
its role is the higher (`cCommands_argPos_iff_role_lt`). In *John sent a letter to Mary* the theme
therefore c-commands the goal and not conversely, where a flat verb phrase has its two objects
c-command each other and a left-branching one has the second c-command the first.

PASSIVE assigns the role of a specifier to an adjunct of its sister and moves a noun phrase into
the specifier. In the lower verb phrase it is Dative Shift: the theme is adjoined to V′ and the
goal moves to the specifier, which gives the double object construction `doubleObject`, where the
goal c-commands the theme and not conversely (`cCommands_doubleObject`). In the clause it is
Passive, `passive`, where the subject c-commands the *by*-phrase and not conversely. The dative
passive *Mary was sent a letter* moves the goal of the oblique structure to the subject in one
step, `indirectPassive`. Of two objects in either frame, the one that licenses an anaphor, binds
a pronoun, moves as a *wh*-phrase, or licenses *the other* or a polarity item in the other is the
one that c-commands the other (`acceptable_iff_cCommands`).

Dative Shift deletes *to*, and the deletion is recoverable when the roles the verb assigns to its
indirect object include the role *to* assigns. A verb shifts exactly when they do
(`acceptable_iff_recoverable`).

## Implementation notes

* C-command is that of the first branching node, which the paper assumes. The categories V, V′
  and VP are one category `V`, and I, I′ and IP one category `Aux`; an empty position is a node
  without daughters.
* The absorption of *to* is not an operation on trees: the D-Structure of the double object
  construction, `shiftedD`, has the goal as a bare noun phrase.
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

open PhraseStructure PhraseStructure.Tree

variable {W : Type*}

/-! ### Projection -/

/-- The empty position of category `c`. -/
abbrev empty (c : Cat) : Tree Cat W := .node c []

/-- (76): the phrase `[XP spec [X′ head comp]]` of category `c`. -/
def xbar (c : Cat) (spec head comp : Tree Cat W) : Tree Cat W :=
  .node c [spec, .node c [head, comp]]

/-- The verb phrase of the specifiers `ss`, the highest first, over the heads `hs` and the lowest
complement `x`: each specifier with its head, over the phrase of the rest. -/
def shells : List (Tree Cat W) → List (Tree Cat W) → Tree Cat W → Tree Cat W
  | s :: ss, h :: hs, x => xbar .V s h (shells ss hs x)
  | _, _, x => x

/-- The position of the `i`th phrase of a stack of shells. -/
def spine (i : ℕ) : GornAddress := (.of 1 * .of 1) ^ i

/-- The position of the `k`th argument of a projection with `n` specifiers: the `k`th specifier,
and the complement for `k = n`. -/
def argPos (n k : ℕ) : GornAddress := if k < n then spine k * .of 0 else spine n

variable {ss hs : List (Tree Cat W)} {c : Cat} {s h x : Tree Cat W} {i j n : ℕ}

@[simp] theorem shells_cons_cons :
    shells (s :: ss) (h :: hs) x = xbar .V s h (shells ss hs x) := rfl

@[simp] theorem shells_nil_left : shells [] hs x = x := rfl

@[simp] theorem yield_xbar : (xbar c s h x).yield = s.yield ++ (h.yield ++ x.yield) := by
  simp [xbar]

theorem spine_succ (i : ℕ) : spine (i + 1) = .of 1 * .of 1 * spine i := pow_succ' _ _

theorem spine_add (i k : ℕ) : spine (i + k) = spine i * spine k := pow_add _ _ _

theorem argPos_of_lt (h : i < n) : argPos n i = spine i * .of 0 := by simp [argPos, h]

theorem getElem?_spine (x : Tree Cat W) : ∀ {i : ℕ} {ss hs : List (Tree Cat W)},
    i ≤ ss.length → i ≤ hs.length →
    (shells ss hs x)[spine i]? = some (shells (ss.drop i) (hs.drop i) x)
  | 0, _, _, _, _ => rfl
  | i + 1, s :: ss, h :: hs, hi, hj => by
    have := getElem?_spine x (i := i) (ss := ss) (hs := hs) (by simpa using hi) (by simpa using hj)
    simp only [RoseTree.getElem?_gornAddress] at this ⊢
    simp [spine_succ, xbar, this]

theorem exists_shells_drop_eq_xbar (x : Tree Cat W) (hi : i < ss.length) (hi' : i < hs.length) :
    ∃ s h y, shells (ss.drop i) (hs.drop i) x = xbar .V s h y := by
  rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hi']
  exact ⟨_, _, _, rfl⟩

theorem one_mem_branching_xbar : (1 : GornAddress) ∈ (xbar c s h x).branching := by
  simp [RoseTree.mem_branching, xbar]

theorem of_one_mem_branching_xbar : GornAddress.of 1 ∈ (xbar c s h x).branching := by
  simp [RoseTree.mem_branching, xbar]

-- The specifier of a phrase c-commands what its sister dominates, and nothing properly inside
-- the sister c-commands it.
theorem cCommands_xbar (q : GornAddress) : (xbar c s h x).CCommands (.of 0) (.of 1 * q) := by
  simpa using RoseTree.cCommands_mul_of one_mem_branching_xbar (i := 0) (j := 1) (by decide) q

theorem not_cCommands_xbar {q : GornAddress} (hq : q ≠ 1) :
    ¬ (xbar c s h x).CCommands (.of 1 * q) (.of 0) := by
  simpa using RoseTree.not_cCommands_mul_of_mul (p := 1) (i := 0) (j := 1)
    (by simpa using of_one_mem_branching_xbar (c := c) (s := s) (h := h) (x := x)) (by decide) hq

theorem exists_argPos_eq (hij : i < j) (hj : j ≤ n) :
    ∃ q, q ≠ 1 ∧ argPos n j = spine i * (.of 1 * q) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
  rw [argPos]
  split_ifs
  · exact ⟨.of 1 * spine k * .of 0, fun h ↦ by simpa using congrArg GornAddress.toList h,
      by simp only [Nat.add_assoc, spine_add, spine_succ, mul_assoc]⟩
  · obtain rfl : n = i + k + 1 := by omega
    exact ⟨.of 1 * spine k, fun h ↦ by simpa using congrArg GornAddress.toList h,
      by simp only [Nat.add_assoc, spine_add, spine_succ, mul_assoc]⟩

/-- One argument of a projection c-commands another exactly when it is the higher, whatever the
heads of the shells. -/
theorem cCommands_argPos_iff (x : Tree Cat W) (h : ss.length ≤ hs.length) (hi : i ≤ ss.length)
    (hj : j ≤ ss.length) :
    (shells ss hs x).CCommands (argPos ss.length i) (argPos ss.length j) ↔ i < j := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · obtain ⟨q, -, hq⟩ := exists_argPos_eq hij hj
    have hin : i < ss.length := hij.trans_le hj
    obtain ⟨s, h', y, hy⟩ := exists_shells_drop_eq_xbar x hin (hin.trans_le h)
    rw [hq, argPos_of_lt hin,
      RoseTree.cCommands_mul_iff (getElem?_spine x hin.le (hin.le.trans h)), hy]
    exact iff_of_true (cCommands_xbar q) hij
  · exact iff_of_false not_commands_self (lt_irrefl _)
  · obtain ⟨q, hq1, hq⟩ := exists_argPos_eq hji hi
    have hjn : j < ss.length := hji.trans_le hi
    obtain ⟨s, h', y, hy⟩ := exists_shells_drop_eq_xbar x hjn (hjn.trans_le h)
    rw [hq, argPos_of_lt hjn,
      RoseTree.cCommands_mul_iff (getElem?_spine x hjn.le (hjn.le.trans h)), hy]
    exact iff_of_false (not_cCommands_xbar hq1) hji.asymm

/-- The arguments of a projection, the highest first, embed in its positions, the order of the
arguments going to c-command. -/
def argEmbedding (x : Tree Cat W) (h : ss.length ≤ hs.length) :
    ((· < ·) : Fin (ss.length + 1) → Fin (ss.length + 1) → Prop) ↪r (shells ss hs x).CCommands where
  toFun k := argPos ss.length k
  inj' a b hab := by
    have h₁ := cCommands_argPos_iff (i := a) (j := b) x h (by omega) (by omega)
    have h₂ := cCommands_argPos_iff (i := b) (j := a) x h (by omega) (by omega)
    simp only [hab] at h₁
    simp only [← hab] at h₂
    exact Fin.ext (Nat.le_antisymm (Nat.le_of_not_lt fun hlt ↦ not_commands_self (h₂.2 hlt))
      (Nat.le_of_not_lt fun hlt ↦ not_commands_self (h₁.2 hlt)))
  map_rel_iff' := cCommands_argPos_iff x h (by omega) (by omega)

@[simp] theorem argEmbedding_apply (x : Tree Cat W) (h : ss.length ≤ hs.length)
    (k : Fin (ss.length + 1)) : argEmbedding x h k = argPos ss.length k := rfl

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

/-- (P2): when the roles of the arguments descend the hierarchy, one argument c-commands another
exactly when its role is the higher. -/
theorem cCommands_argPos_iff_role_lt (x : Tree Cat W) {role : ℕ → Role}
    (hrole : StrictAntiOn role (Set.Iic ss.length)) (h : ss.length ≤ hs.length)
    (hi : i ≤ ss.length) (hj : j ≤ ss.length) :
    (shells ss hs x).CCommands (argPos ss.length i) (argPos ss.length j) ↔ role j < role i :=
  (cCommands_argPos_iff x h hi hj).trans (hrole.lt_iff_gt hj hi).symm

/-! ### V Raising -/

/-- The D-Structure of the verb `v` with the specifiers `ss` and the complement `x`: the verb is
the lowest head, and the heads above it are empty. -/
def dStructure (v : Tree Cat W) (ss : List (Tree Cat W)) (x : Tree Cat W) : Tree Cat W :=
  shells ss (List.replicate (ss.length - 1) (empty .V) ++ [v]) x

/-- The S-Structure: the verb has raised to the highest head, and each head below is its
trace. -/
def sStructure (v : Tree Cat W) (ss : List (Tree Cat W)) (x : Tree Cat W) : Tree Cat W :=
  shells ss (v :: List.replicate (ss.length - 1) (trace 0 .V)) x

variable {v agent theme goal prep infl byP : Tree Cat W}

theorem yield_shells_replicate_trace (x : Tree Cat W) : ∀ (ss : List (Tree Cat W)) (k : ℕ),
    ss.length ≤ k → (shells ss (List.replicate k (trace 0 .V)) x).yield =
      ss.flatMap yield ++ x.yield
  | [], _, _ => by simp
  | s :: ss, k + 1, hk => by
    simp [List.replicate_succ, yield_shells_replicate_trace x ss k (by simpa using hk)]

-- Before the verb raises the arguments all but the lowest precede it: *John a letter send to
-- Mary*.
theorem yield_dStructure (v x : Tree Cat W) : ∀ {ss : List (Tree Cat W)}, ss ≠ [] →
    (dStructure v ss x).yield = ss.flatMap yield ++ (v.yield ++ x.yield)
  | [s], _ => by simp [dStructure]
  | s :: s' :: ss, _ => by
    have := yield_dStructure v x (ss := s' :: ss) (by simp)
    simp only [dStructure, List.length_cons, Nat.add_sub_cancel] at this ⊢
    simp [List.replicate_succ, this]

-- After it raises only the highest does: *John send a letter to Mary*.
theorem yield_sStructure (v s x : Tree Cat W) (ss : List (Tree Cat W)) :
    (sStructure v (s :: ss) x).yield = s.yield ++ (v.yield ++ (ss.flatMap yield ++ x.yield)) := by
  simp [sStructure, yield_shells_replicate_trace x ss ss.length le_rfl]

/-- Move α: the phrase at `src` takes the empty position `dst` and leaves the trace `i`. -/
def move (i : ℕ) (src dst : List ℕ) (t : Tree Cat W) : Tree Cat W :=
  t[src]?.elim t fun a ↦ (t.replaceAt src (trace i (Tree.cat a) : Tree Cat W)).replaceAt dst a

-- (14): the verb of a dative raises from the lower head to the upper.
theorem move_dStructure (hv : Tree.cat v = .V) :
    move 0 [1, 1, 1, 0] [1, 0] (dStructure v [agent, theme] x) =
      sStructure v [agent, theme] x := by
  simp [move, dStructure, sStructure, xbar, RoseTree.replaceAt_cons, hv]

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

/-- (80), with *to* absorbed: the D-Structure of the double object construction. The role of the
lower specifier is assigned to the theme as an adjunct of V′, and the specifier is empty. -/
def shiftedD (v agent goal theme : Tree Cat W) : Tree Cat W :=
  xbar .V agent (empty .V) (.node .V [empty .N, .adjoin .V [.node .V [v, goal], theme]])

/-- (26): the double object construction. The goal has moved to the lower specifier and the verb
has raised. -/
def doubleObject (v agent goal theme : Tree Cat W) : Tree Cat W :=
  xbar .V agent v (.node .V [goal, .adjoin .V [.node .V [.trace 0 .V, .trace 1 .N], theme]])

/-- (24): the passive. The object has moved to the subject, and the *by*-phrase is adjoined to
the verb phrase. -/
def passive (infl v patient byP : Tree Cat W) : Tree Cat W :=
  xbar .Aux patient infl (.adjoin .V [.node .V [v, .trace 1 .N], byP])

/-- (40): the dative passive. The goal has moved from the complement of the verb to the subject,
and the theme is in the lower specifier. -/
def indirectPassive (infl v goal theme : Tree Cat W) : Tree Cat W :=
  xbar .Aux goal infl (sStructure v [empty .N, theme] (.trace 1 .N))

-- (25), (26): Dative Shift is the movement of the goal to the lower specifier.
theorem move_move_shiftedD (hv : Tree.cat v = .V) (hg : Tree.cat goal = .N) :
    move 0 [1, 1, 1, 0, 0] [1, 0] (move 1 [1, 1, 1, 0, 1] [1, 1, 0] (shiftedD v agent goal theme)) =
      doubleObject v agent goal theme := by
  simp [move, shiftedD, doubleObject, xbar, RoseTree.replaceAt_cons, hv, hg]

-- (40): the dative passive is one movement of the goal out of the D-Structure of the oblique
-- dative, whose subject is empty.
theorem move_move_dStructure (hv : Tree.cat v = .V) (hg : Tree.cat goal = .N) :
    move 1 [1, 1, 1, 1, 1, 1] [0] (move 0 [1, 1, 1, 1, 1, 0] [1, 1, 1, 0]
      (xbar .Aux (empty .N) infl (dStructure v [empty .N, theme] goal))) =
      indirectPassive infl v goal theme := by
  simp [move, indirectPassive, dStructure, sStructure, xbar, RoseTree.replaceAt_cons, hv, hg]

theorem yield_doubleObject (v agent goal theme : Tree Cat W) :
    (doubleObject v agent goal theme).yield =
      agent.yield ++ (v.yield ++ (goal.yield ++ theme.yield)) := by
  simp [doubleObject]

/-- In the double object construction the goal c-commands the theme and not conversely. -/
theorem cCommands_doubleObject (v agent goal theme : Tree Cat W) :
    (doubleObject v agent goal theme).CCommands ⟨[1, 1, 0]⟩ ⟨[1, 1, 1, 1]⟩ ∧
      ¬ (doubleObject v agent goal theme).CCommands ⟨[1, 1, 1, 1]⟩ ⟨[1, 1, 0]⟩ :=
  ⟨RoseTree.cCommands_mul_of (p := ⟨[1, 1]⟩) (i := 0) (j := 1)
      (by simp [RoseTree.mem_branching, doubleObject, xbar]) (by decide) (.of 1),
    RoseTree.not_cCommands_mul_of_mul (p := ⟨[1, 1]⟩) (i := 0) (j := 1) (q := .of 1)
      (by simp [RoseTree.mem_branching, doubleObject, xbar]) (by decide) (by decide)⟩

-- (27): in the passive the subject c-commands the *by*-phrase and not conversely.
theorem cCommands_passive (infl v patient byP : Tree Cat W) :
    (passive infl v patient byP).CCommands ⟨[0]⟩ ⟨[1, 1, 1]⟩ ∧
      ¬ (passive infl v patient byP).CCommands ⟨[1, 1, 1]⟩ ⟨[0]⟩ :=
  ⟨RoseTree.cCommands_mul_of (p := 1) (i := 0) (j := 1)
      (by simp [RoseTree.mem_branching, passive, xbar]) (by decide) ⟨[1, 1]⟩,
    RoseTree.not_cCommands_mul_of_mul (p := 1) (i := 0) (j := 1) (q := ⟨[1, 1]⟩)
      (by simp [RoseTree.mem_branching, passive, xbar]) (by decide) (by decide)⟩

/-! ### The asymmetries of the two objects -/

open Examples (Frame Argument)

/-- The S-Structure of a frame. -/
def rep (v agent theme goal prep : Tree Cat W) : Frame → Tree Cat W
  | .oblique => sStructure v [agent, theme] (node .P [prep, goal])
  | .doubleObject => doubleObject v agent goal theme

/-- The position of an object in the S-Structure of a frame. -/
def pos : Frame → Argument → GornAddress
  | .oblique, .theme => ⟨[1, 1, 0]⟩
  | .oblique, .goal => ⟨[1, 1, 1, 1, 1]⟩
  | .doubleObject, .goal => ⟨[1, 1, 0]⟩
  | .doubleObject, .theme => ⟨[1, 1, 1, 1]⟩

/-- The object in the lower specifier: the theme of the oblique dative, and the goal of the
double object construction. -/
def higher : Frame → Argument
  | .oblique => .theme
  | .doubleObject => .goal

/-- The other object. -/
def other : Argument → Argument
  | .theme => .goal
  | .goal => .theme

theorem getElem?_pos (f : Frame) :
    (rep v agent theme goal prep f)[pos f .theme]? = some theme ∧
      (rep v agent theme goal prep f)[pos f .goal]? = some goal := by
  cases f <;> exact ⟨rfl, rfl⟩

theorem cCommands_pos_iff (f : Frame) (r : Argument) :
    (rep v agent theme goal prep f).CCommands (pos f r) (pos f (other r)) ↔ r = higher f := by
  have ho : (rep v agent theme goal prep .oblique).CCommands ⟨[1, 1, 0]⟩ ⟨[1, 1, 1, 1, 1]⟩ ∧
      ¬ (rep v agent theme goal prep .oblique).CCommands ⟨[1, 1, 1, 1, 1]⟩ ⟨[1, 1, 0]⟩ :=
    ⟨RoseTree.cCommands_mul_of (p := ⟨[1, 1]⟩) (i := 0) (j := 1)
        (by simp [RoseTree.mem_branching, rep, sStructure, xbar]) (by decide) ⟨[1, 1]⟩,
      RoseTree.not_cCommands_mul_of_mul (p := ⟨[1, 1]⟩) (i := 0) (j := 1) (q := ⟨[1, 1]⟩)
        (by simp [RoseTree.mem_branching, rep, sStructure, xbar]) (by decide) (by decide)⟩
  have hd := cCommands_doubleObject v agent goal theme
  cases f <;> cases r
  · exact iff_of_true ho.1 rfl
  · exact iff_of_false ho.2 (by decide)
  · exact iff_of_false hd.2 (by decide)
  · exact iff_of_true hd.1 rfl

/-- A dependency between the two objects is acceptable exactly when the object that must
c-command the other does. -/
theorem acceptable_iff_cCommands (v agent theme goal prep : Tree Cat W) :
    ∀ e ∈ Examples.all, ∀ f ∈ Examples.frame e, ∀ r ∈ Examples.licensor e,
      (e.judgment = .acceptable ↔
        (rep v agent theme goal prep f).CCommands (pos f r) (pos f (other r))) := by
  simp only [cCommands_pos_iff]
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
    ((move 0 [1, 1, 1, 0, 0] [1, 0] (move 1 [1, 1, 1, 0, 1] [1, 1, 0]
      (shiftedD sent john mary aLetter))).yield.map (·.form)) =
      ["John", "sent", "Mary", "a", "letter"] := by
  decide

end Sentences

end Larson1988
