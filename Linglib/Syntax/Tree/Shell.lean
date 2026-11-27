/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Tree.Basic
public import Linglib.Syntax.Command.RoseTree
public import Linglib.Syntax.Tree.Cat
public import Linglib.Core.Data.RoseTree.Context

/-!
# Stacks of shells

A phrase `[XP Spec [X′ X YP]]` is a head with one specifier and one complement. A shell is such a
phrase without its complement, and a stack of shells over a lowest complement is the
right-branching tree in which each shell takes the phrase of the shells below it as its
complement. These are the verb phrase shells of [larson-1988], whose heads are empty verbs, and
the Cascades of [pesetsky-1995], whose heads are prepositions.

In a stack the specifiers and the lowest complement are linearly ordered by c-command, the higher
c-commanding the lower and not conversely, and so are the heads.

## Main definitions

* `PhraseStructure.Shell`: a specifier and a head of one category, with an optional adjunct of X′.
* `PhraseStructure.Shell.stack`: the phrase of a list of shells over a lowest complement.
* `PhraseStructure.Shell.context`, `PhraseStructure.Shell.stackContext`: a shell and a stack as
  one-hole contexts, whose hole is the position of the complement.
* `PhraseStructure.Shell.argPos`, `PhraseStructure.Shell.headPos`: the positions of the arguments
  and of the heads of a stack.
* `PhraseStructure.Shell.argEmbedding`, `PhraseStructure.Shell.headEmbedding`: the arguments and
  the heads, ordered by height, embed in the positions of the stack ordered by c-command.

## Main results

* `PhraseStructure.Shell.cCommands_argPos_iff`: one argument c-commands another exactly when it is
  the higher.
* `PhraseStructure.Shell.cCommands_headPos_iff`: one head c-commands another exactly when it is the
  higher.

## Implementation notes

A stack is a context plugged with its lowest complement, `Shell.plug_stackContext`, so the
position of a phrase is the path of a context and the subtree there is found by
`RoseTree.Context.getElem?_plug_path`, without induction on the stack. C-command is that of the
first branching node. The asymmetries rest on
`PhraseStructure.commands_of_covBy_of_lt` and `PhraseStructure.not_commands_of_covBy_of_lt`, which
hold of a path in any dominance order, so they do not depend on what the specifiers, heads and
adjuncts are. A lowest head and its complement are sisters and c-command each other, so the
lowest complement is among the arguments and not compared with the heads.

## References

* [larson-1988]
* [pesetsky-1995]
-/

@[expose] public section

namespace PhraseStructure

open Tree

variable {W : Type*}

/-- A shell is a phrase without its complement: a specifier and a head of one category, and
optionally an adjunct of X′. -/
structure Shell (W : Type*) where
  /-- The category of the head. -/
  cat : Cat := .V
  /-- The specifier. -/
  spec : Tree Cat W
  /-- The head. -/
  head : Tree Cat W
  /-- The adjunct of X′. -/
  adjunct : Option (Tree Cat W) := none

namespace Shell

variable {L : Shell W} {x : Tree Cat W}

/-- X′: the head with the complement `x`, and the adjunct if there is one. -/
def bar (L : Shell W) (x : Tree Cat W) : Tree Cat W :=
  L.adjunct.elim (node L.cat [L.head, x]) fun d ↦ adjoin L.cat [node L.cat [L.head, x], d]

/-- The phrase `[XP spec [X′ head x]]`. -/
def over (L : Shell W) (x : Tree Cat W) : Tree Cat W := node L.cat [L.spec, L.bar x]

/-- The position of the complement in the phrase. -/
def compPos (L : Shell W) : GornAddress :=
  .of 1 * L.adjunct.elim (.of 1) fun _ ↦ .of 0 * .of 1

/-- The frames of a shell, from its phrase down to the hole of its complement. -/
def context (L : Shell W) : RoseTree.Context (Label Cat W) :=
  ⟨.phrase L.cat .projection, [L.spec], []⟩ ::
    ((L.adjunct.elim [] fun d ↦ [⟨.phrase L.cat .adjunction, [], [d]⟩]) ++
      [⟨.phrase L.cat .projection, [L.head], []⟩])

@[simp] theorem plug_context (L : Shell W) (x : Tree Cat W) : L.context.plug x = L.over x := by
  rcases L with ⟨c, s, h, _ | d⟩ <;> rfl

theorem path_context (L : Shell W) : L.context.path = L.compPos.toList := by
  rcases L with ⟨c, s, h, _ | d⟩ <;> rfl

theorem getElem?_compPos (L : Shell W) (x : Tree Cat W) : (L.over x)[L.compPos]? = some x := by
  rw [← plug_context, RoseTree.getElem?_gornAddress, ← path_context]
  exact RoseTree.Context.getElem?_plug_path _ _

theorem one_mem_branching (L : Shell W) (x : Tree Cat W) :
    (1 : GornAddress) ∈ (L.over x).branching := by
  simp [RoseTree.mem_branching, over]

theorem of_one_mem_branching (L : Shell W) (x : Tree Cat W) :
    GornAddress.of 1 ∈ (L.over x).branching := by
  rcases L with ⟨c, s, h, _ | d⟩ <;> simp [RoseTree.mem_branching, over, bar]

theorem of_one_lt_compPos (L : Shell W) : GornAddress.of 1 < L.compPos := by
  rcases L with ⟨c, s, h, _ | d⟩ <;>
    exact lt_of_le_of_ne (GornAddress.le_mul_right _ _) fun e ↦ by
      simpa [compPos] using congrArg GornAddress.toList e

@[simp] theorem yield_over (L : Shell W) (x : Tree Cat W) :
    (L.over x).yield =
      L.spec.yield ++ (L.head.yield ++ (x.yield ++ L.adjunct.elim [] yield)) := by
  rcases L with ⟨c, s, h, _ | d⟩ <;> simp [over, bar]


/-- The position of the lowest X′, the mother of the head and the complement. -/
def barPos (L : Shell W) : GornAddress := .of 1 * L.adjunct.elim 1 fun _ ↦ .of 0

theorem compPos_eq (L : Shell W) : L.compPos = L.barPos * .of 1 := by
  rcases L with ⟨c, s, h, _ | d⟩ <;> simp [compPos, barPos, mul_assoc]

theorem barPos_mem_branching (L : Shell W) (x : Tree Cat W) :
    L.barPos ∈ (L.over x).branching := by
  rcases L with ⟨c, s, h, _ | d⟩ <;> simp [RoseTree.mem_branching, over, bar, barPos]

theorem getElem?_barPos_mul_of_zero (L : Shell W) (x : Tree Cat W) :
    (L.over x)[L.barPos * .of 0]? = some L.head := by
  rcases L with ⟨c, s, h, _ | d⟩ <;> rfl

/-! ### Stacks of shells -/

/-- The phrase of the shells `ls`, the highest first, over the lowest complement `x`. -/
def stack (ls : List (Shell W)) (x : Tree Cat W) : Tree Cat W := ls.foldr Shell.over x

/-- The context of a stack of shells, down to the hole of the lowest complement. -/
def stackContext (ls : List (Shell W)) : RoseTree.Context (Label Cat W) := ls.flatMap context

/-- The position of the `k`th phrase of a stack of shells, and of the lowest complement for
`k` at least their number: the hole of the first `k` shells. -/
def pos (ls : List (Shell W)) (k : ℕ) : GornAddress := ⟨(stackContext (ls.take k)).path⟩

/-- The position of the `k`th specifier. -/
abbrev specPos (ls : List (Shell W)) (k : ℕ) : GornAddress := pos ls k * .of 0

/-- The position of the adjunct of the `k`th shell. -/
abbrev adjunctPos (ls : List (Shell W)) (k : ℕ) : GornAddress := pos ls k * .of 1 * .of 1

variable {ls : List (Shell W)} {i j k : ℕ}

@[simp] theorem stack_nil : stack ([] : List (Shell W)) x = x := rfl

@[simp] theorem stack_cons : stack (L :: ls) x = L.over (stack ls x) := rfl

theorem stack_append (l₁ l₂ : List (Shell W)) (x : Tree Cat W) :
    stack (l₁ ++ l₂) x = stack l₁ (stack l₂ x) := List.foldr_append

@[simp] theorem stackContext_nil : stackContext ([] : List (Shell W)) = [] := rfl

@[simp] theorem stackContext_cons : stackContext (L :: ls) = L.context ++ stackContext ls := rfl

@[simp] theorem stackContext_append (l₁ l₂ : List (Shell W)) :
    stackContext (l₁ ++ l₂) = stackContext l₁ ++ stackContext l₂ := List.flatMap_append

/-- A stack is its context with the lowest complement in the hole. -/
@[simp] theorem plug_stackContext (ls : List (Shell W)) (x : Tree Cat W) :
    (stackContext ls).plug x = stack ls x := by
  induction ls with
  | nil => rfl
  | cons L ls ih => simp [ih]

@[simp] theorem pos_zero : pos ls 0 = 1 := rfl

@[simp] theorem pos_cons_succ : pos (L :: ls) (k + 1) = L.compPos * pos ls k :=
  GornAddress.ext (by simp [pos, path_context])

/-- The position of a phrase is found by descending to a higher phrase and on from there. -/
theorem pos_add (ls : List (Shell W)) (i j : ℕ) :
    pos ls (i + j) = pos ls i * pos (ls.drop i) j :=
  GornAddress.ext (by simp [pos, List.take_add])

theorem pos_succ (hk : k < ls.length) : pos ls (k + 1) = pos ls k * ls[k].compPos := by
  rw [pos_add, List.drop_eq_getElem_cons hk, pos_cons_succ, pos_zero, mul_one]

theorem getElem?_pos (x : Tree Cat W) (ls : List (Shell W)) (k : ℕ) :
    (stack ls x)[pos ls k]? = some (stack (ls.drop k) x) := by
  have h : stack ls x = (stackContext (ls.take k)).plug (stack (ls.drop k) x) := by
    rw [plug_stackContext, ← stack_append, List.take_append_drop]
  rw [h, RoseTree.getElem?_gornAddress]
  exact RoseTree.Context.getElem?_plug_path _ _

theorem stack_drop (x : Tree Cat W) (hk : k < ls.length) :
    stack (ls.drop k) x = ls[k].over (stack (ls.drop (k + 1)) x) := by
  rw [List.drop_eq_getElem_cons hk, stack_cons]

theorem pos_mul_of_lt_succ (hk : k < ls.length) : pos ls k * .of 1 < pos ls (k + 1) := by
  rw [pos_succ hk]
  exact (GornAddress.mulLeft (pos ls k)).lt_iff_lt.2 ls[k].of_one_lt_compPos

theorem pos_mul_of_lt (hij : i < j) (hj : j ≤ ls.length) : pos ls i * .of 1 < pos ls j := by
  induction j, hij using Nat.le_induction with
  | base => exact pos_mul_of_lt_succ hj
  | succ k hk ih =>
    exact (ih (by omega)).trans
      ((GornAddress.le_mul_right _ _).trans_lt (pos_mul_of_lt_succ (by omega)))

theorem pos_mem_branching (x : Tree Cat W) (hk : k < ls.length) :
    pos ls k ∈ (stack ls x).branching := by
  have := (RoseTree.mul_mem_branching_iff (getElem?_pos x ls k) (x := 1)).2
    (stack_drop x hk ▸ Shell.one_mem_branching _ _)
  rwa [mul_one] at this

theorem pos_mul_of_mem_branching (x : Tree Cat W) (hk : k < ls.length) :
    pos ls k * .of 1 ∈ (stack ls x).branching :=
  (RoseTree.mul_mem_branching_iff (getElem?_pos x ls k)).2
    (stack_drop x hk ▸ Shell.of_one_mem_branching _ _)

-- A specifier c-commands whatever a lower phrase dominates, and nothing there c-commands it.
theorem cCommands_specPos_of_lt (x : Tree Cat W) (hij : i < j) (hj : j ≤ ls.length)
    {b : GornAddress} (hb : pos ls j ≤ b) : (stack ls x).CCommands (specPos ls i) b :=
  commands_of_covBy_of_lt (GornAddress.covBy_mul_of _ 0) (pos_mem_branching x (by omega))
    (GornAddress.lt_mul_of _ 1) (RoseTree.not_mul_of_le_mul_of _ (by decide))
    ((pos_mul_of_lt hij hj).le.trans hb)

theorem not_cCommands_specPos_of_lt (x : Tree Cat W) (hij : i < j) (hj : j ≤ ls.length)
    {b : GornAddress} (hb : pos ls j ≤ b) : ¬ (stack ls x).CCommands b (specPos ls i) :=
  not_commands_of_covBy_of_lt (GornAddress.covBy_mul_of _ 0)
    (pos_mul_of_mem_branching x (by omega)) (GornAddress.lt_mul_of _ 1)
    (RoseTree.not_mul_of_le_mul_of _ (by decide)) ((pos_mul_of_lt hij hj).trans_le hb) le_rfl

-- A map of a linear order whose order goes to c-command and back is injective.
theorem injective_of_cCommands_iff {n : ℕ} {t : Tree Cat W} {f : Fin n → GornAddress}
    (h : ∀ a b, t.CCommands (f a) (f b) ↔ a < b) : Function.Injective f := fun a b hab ↦ by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact not_commands_self (hab ▸ (h a b).2 hlt)
  · exact not_commands_self (hab ▸ (h b a).2 hlt)

/-- The position of the `k`th argument of a stack of shells: the `k`th specifier, and the lowest
complement for `k` their number. -/
def argPos (ls : List (Shell W)) (k : ℕ) : GornAddress :=
  if k < ls.length then specPos ls k else pos ls ls.length

theorem argPos_of_lt (h : k < ls.length) : argPos ls k = specPos ls k := by simp [argPos, h]

theorem pos_le_argPos (hk : k ≤ ls.length) : pos ls k ≤ argPos ls k := by
  rw [argPos]
  split_ifs
  · exact GornAddress.le_mul_right _ _
  · exact (Nat.le_antisymm hk (Nat.le_of_not_lt ‹_›)) ▸ le_rfl

/-- One argument of a projection c-commands another exactly when it is the higher, whatever the
heads of the phrases. -/
theorem cCommands_argPos_iff (ls : List (Shell W)) (x : Tree Cat W) (hi : i ≤ ls.length)
    (hj : j ≤ ls.length) : (stack ls x).CCommands (argPos ls i) (argPos ls j) ↔ i < j := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [argPos_of_lt (hij.trans_le hj)]
    exact iff_of_true (cCommands_specPos_of_lt x hij hj (pos_le_argPos hj)) hij
  · exact iff_of_false not_commands_self (lt_irrefl _)
  · rw [argPos_of_lt (hji.trans_le hi)]
    exact iff_of_false (not_cCommands_specPos_of_lt x hji hi (pos_le_argPos hi)) hji.asymm

/-- The arguments of a projection, the highest first, embed in its positions, their order going
to c-command. -/
def argEmbedding (ls : List (Shell W)) (x : Tree Cat W) :
    ((· < ·) : Fin (ls.length + 1) → Fin (ls.length + 1) → Prop) ↪r (stack ls x).CCommands where
  toFun k := argPos ls k
  inj' := injective_of_cCommands_iff fun a b ↦ cCommands_argPos_iff ls x (by omega) (by omega)
  map_rel_iff' := cCommands_argPos_iff ls x (by omega) (by omega)

@[simp] theorem argEmbedding_apply (ls : List (Shell W)) (x : Tree Cat W)
    (k : Fin (ls.length + 1)) : argEmbedding ls x k = argPos ls k := rfl

theorem getElem?_specPos (x : Tree Cat W) (hk : k < ls.length) :
    (stack ls x)[specPos ls k]? = some ls[k].spec := by
  have := getElem?_pos x ls k
  simp only [RoseTree.getElem?_gornAddress] at this ⊢
  simp [RoseTree.getElem?_append, this, stack_drop x hk, Shell.over]

theorem cCommands_specPos_adjunctPos (x : Tree Cat W) (hk : k < ls.length) :
    (stack ls x).CCommands (specPos ls k) (adjunctPos ls k) ∧
      ¬ (stack ls x).CCommands (adjunctPos ls k) (specPos ls k) :=
  ⟨RoseTree.cCommands_mul_of (pos_mem_branching x hk) (by decide) (.of 1),
    RoseTree.not_cCommands_mul_of_mul (pos_mul_of_mem_branching x hk) (by decide) (by decide)⟩

/-! ### Heads -/

/-- The position of the `k`th head. -/
def headPos : List (Shell W) → ℕ → GornAddress
  | L :: _, 0 => L.barPos * .of 0
  | L :: ls, k + 1 => L.compPos * headPos ls k
  | [], _ => 1

theorem headPos_eq : ∀ {ls : List (Shell W)} {k : ℕ} (hk : k < ls.length),
    headPos ls k = pos ls k * ls[k].barPos * .of 0
  | L :: ls, 0, _ => by simp [headPos]
  | L :: ls, k + 1, hk => by
    rw [headPos, headPos_eq (ls := ls) (by simpa using hk), pos_cons_succ]
    simp [mul_assoc]

theorem getElem?_headPos (x : Tree Cat W) (hk : k < ls.length) :
    (stack ls x)[headPos ls k]? = some ls[k].head := by
  have h₁ := getElem?_pos x ls k
  have h₂ := ls[k].getElem?_barPos_mul_of_zero (stack (ls.drop (k + 1)) x)
  rw [headPos_eq hk, mul_assoc]
  simp only [RoseTree.getElem?_gornAddress] at h₁ h₂ ⊢
  simp only [GornAddress.toList_mul, RoseTree.getElem?_append] at h₂ ⊢
  simpa [h₁, stack_drop x hk] using h₂

theorem pos_le_pos (hij : i ≤ j) (hj : j ≤ ls.length) : pos ls i ≤ pos ls j := by
  rcases hij.eq_or_lt with rfl | h
  · rfl
  · exact ((GornAddress.le_mul_right _ _).trans_lt (pos_mul_of_lt h hj)).le

theorem pos_lt_headPos (hk : k < ls.length) : pos ls k < headPos ls k := by
  rw [headPos_eq hk]
  exact (GornAddress.le_mul_right _ _).trans_lt (GornAddress.lt_mul_of _ 0)

theorem pos_mul_barPos_mem_branching (x : Tree Cat W) (hk : k < ls.length) :
    pos ls k * ls[k].barPos ∈ (stack ls x).branching :=
  (RoseTree.mul_mem_branching_iff (getElem?_pos x ls k)).2
    (stack_drop x hk ▸ Shell.barPos_mem_branching _ _)

private theorem pos_succ_eq (hk : k < ls.length) :
    pos ls (k + 1) = pos ls k * ls[k].barPos * .of 1 := by
  rw [pos_succ hk, Shell.compPos_eq, mul_assoc]

-- A head c-commands whatever a lower phrase dominates, and nothing below that phrase
-- c-commands it.
theorem cCommands_headPos_of_lt (x : Tree Cat W) (hij : i < j) (hj : j ≤ ls.length)
    {b : GornAddress} (hb : pos ls j ≤ b) : (stack ls x).CCommands (headPos ls i) b := by
  have hi : i < ls.length := by omega
  rw [headPos_eq hi]
  exact commands_of_covBy_of_lt (GornAddress.covBy_mul_of _ 0)
    (pos_mul_barPos_mem_branching x hi) (pos_succ_eq hi ▸ GornAddress.lt_mul_of _ 1)
    (pos_succ_eq hi ▸ RoseTree.not_mul_of_le_mul_of _ (by decide))
    ((pos_le_pos (by omega) hj).trans hb)

theorem not_cCommands_headPos_of_lt (x : Tree Cat W) (hij : i < j) (hj : j < ls.length)
    {b : GornAddress} (hb : pos ls j < b) : ¬ (stack ls x).CCommands b (headPos ls i) := by
  have hi : i < ls.length := by omega
  rw [headPos_eq hi]
  exact not_commands_of_covBy_of_lt (GornAddress.covBy_mul_of _ 0)
    (pos_mem_branching x (by omega)) (pos_succ_eq hi ▸ GornAddress.lt_mul_of _ 1)
    (pos_succ_eq hi ▸ RoseTree.not_mul_of_le_mul_of _ (by decide))
    ((pos_le_pos (by omega) hj.le).trans_lt hb) le_rfl

/-- One head of a stack c-commands another exactly when it is the higher. -/
theorem cCommands_headPos_iff (ls : List (Shell W)) (x : Tree Cat W) (hi : i < ls.length)
    (hj : j < ls.length) : (stack ls x).CCommands (headPos ls i) (headPos ls j) ↔ i < j := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact iff_of_true (cCommands_headPos_of_lt x hij hj.le (pos_lt_headPos hj).le) hij
  · exact iff_of_false not_commands_self (lt_irrefl _)
  · exact iff_of_false (not_cCommands_headPos_of_lt x hji hi (pos_lt_headPos hi)) hji.asymm

/-- The heads of a stack, the highest first, embed in its positions, their order going to
c-command. -/
def headEmbedding (ls : List (Shell W)) (x : Tree Cat W) :
    ((· < ·) : Fin ls.length → Fin ls.length → Prop) ↪r (stack ls x).CCommands where
  toFun k := headPos ls k
  inj' := injective_of_cCommands_iff fun a b ↦ cCommands_headPos_iff ls x a.isLt b.isLt
  map_rel_iff' := cCommands_headPos_iff ls x (Fin.isLt _) (Fin.isLt _)

@[simp] theorem headEmbedding_apply (ls : List (Shell W)) (x : Tree Cat W) (k : Fin ls.length) :
    headEmbedding ls x k = headPos ls k := rfl

end Shell

end PhraseStructure
