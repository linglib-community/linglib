/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.Examples.Collins2026
public import Linglib.Semantics.Composition.Tree
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Syntax.Minimalist.Copy.ToTree
public import Linglib.Syntax.Minimalist.Workspace.Basic

/-!
# Collins (2026): Reconstruction and the New Minimalism

In the framework of Marcolli, Chomsky and Berwick, Internal Merge replaces a tree $T$ by the moved
term $\beta$ and the contraction quotient $T/^c\beta$, then merges the two, and the quotient is what
the semantic interface receives. Its contracted leaf has no structure, so in *Pictures of himself,
John loves* the subject [does not c-command the anaphor](##no_reconstruction), though under the copy
theory of movement it does; negation likewise [loses the quantifier](##no_scope_reconstruction) it
scopes over. The quotient alters one of the two objects merged, which [MERGE leaving copies never
does](##no_tampering). Collins concludes that the framework cannot capture reconstruction. That
holds of a condition read off the final object: a condition evaluated at [some earlier
stage](##binds_at_earlier_stage) binds the anaphor with traces alone. With the copies kept, a
derivation has a reading for each choice of the chains read low: read low, [the antecedent binds the
anaphor](##binds_at_low_reading) in the fronted phrase's lower copy, and (15) has [both its scope
readings](##scope_readings) through the composition engine.

## Implementation notes

* The condition checked is the c-command half of Principle A. The coindexation is given by the
  paper's example and its local domain is the clause, and the argument turns on c-command only.
* The derivations suppress the projections the paper suppresses in its tree for the fronted
  sentence, so the fronted phrase merges with the clause directly.
* The trace leaf carries the head of the moved term, where the book's label is the term itself. The
  paper's point is that c-command does not read labels, and the definition here does not.
* That a condition at an earlier stage recovers the binding is not the paper's claim. It applies the
  derivational binding condition Cole and Hermon use, and says nothing about whether such a
  condition is available to the framework the paper criticizes.
* The reading with no chain read low is the book's contraction with a binder the book does not have.
  The low reading deletes the higher copy, which none of the book's quotients does, so the two scope
  readings are the copy theory's, not the framework's.

## References

* [collins-2026]
* [marcolli-chomsky-berwick-2025]
* [collins-stabler-2016]
* [cole-hermon-2008]
* [chomsky-1995]
-/

@[expose] public section

namespace Collins2026

open Minimalist Minimalist.Derivation Montague PhraseStructure

/-! ### Reconstruction for Principle A -/

/-- *himself*. -/
def himself : LexicalItem.Token := ⟨.of .N [] "himself", 0⟩
/-- *of*. -/
def ofP : LexicalItem.Token := ⟨.of .P [.N] "of", 1⟩
/-- *pictures*. -/
def pictures : LexicalItem.Token := ⟨.of .N [.P] "pictures", 2⟩
/-- *John*. -/
def john : LexicalItem.Token := ⟨.of .N [] "John", 3⟩
/-- *loves*. -/
def loves : LexicalItem.Token := ⟨.of .V [.N, .N] "loves", 4⟩

/-- *pictures of himself*. -/
def picturesOfHimself : LinearizedSyntacticObject :=
  .merge (.leaf pictures) (.merge (.leaf ofP) (.leaf himself))

/-- *John loves pictures of himself*. -/
def basic : Derivation := ⟨loves, [.em .right picturesOfHimself, .em .left (.leaf john)]⟩

/-- *Pictures of himself, John loves*: the object of `basic` raised by Internal Merge. -/
def fronted : Derivation := basic.append [.im picturesOfHimself.toSyntacticObject]

/-- The clause `fronted` starts from, before the object moves. -/
noncomputable def clause : SyntacticObject := basic.stageAt basic.length

/-- What the object leaves behind when it moves: the contraction quotient. -/
noncomputable def remnant : SyntacticObject :=
  clause.replace picturesOfHimself.toSyntacticObject picturesOfHimself.toSyntacticObject.headTrace

-- (14): the final stage of `fronted` is the moved phrase merged with the contraction quotient.
theorem stageAt_fronted :
    fronted.stageAt fronted.length = .merge picturesOfHimself.toSyntacticObject remnant := by
  decide +kernel

/-- The fronted sentence has the anaphor in the scope of its antecedent in the copy object, but not
in the contraction quotient the framework sends to the semantic interface: there *himself* survives
only in the moved phrase, out of reach of what the phrase left behind. -/
theorem no_reconstruction :
    fronted.BindsAtLF ↑john ↑himself ∧ ¬ fronted.BindsAtSurface ↑john ↑himself := by
  refine ⟨by decide +kernel, fun h ↦ ?_⟩
  have h' := h.cCommands_stageAt
  rw [stageAt_fronted] at h'
  exact SyntacticObject.not_cCommands_merge_of_notMem_terms (by decide +kernel) (by decide +kernel)
    (by decide +kernel) h'

/-- The replay of `fronted` succeeds and its surface binding is not empty: *John* still c-commands
*loves*, and before the object moves it c-commands the anaphor. -/
example : fronted.replay?.isSome ∧ fronted.BindsAtSurface ↑john ↑loves ∧
    basic.BindsAtSurface ↑john ↑himself := by
  decide +kernel

/-- The trace the moved phrase leaves carries its head. -/
example : picturesOfHimself.toSyntacticObject.headTrace = .traceOf pictures := by decide +kernel

-- (11), (12a)
theorem bindsAtLF_iff_judgment :
    (basic.BindsAtLF ↑john ↑himself ↔ Examples.ex_11.judgment = .acceptable) ∧
    (fronted.BindsAtLF ↑john ↑himself ↔ Examples.ex_12a.judgment = .acceptable) ∧
    ¬ fronted.BindsAtLF ↑himself ↑john := by
  decide +kernel

/-- Evaluated at some stage, binding needs no copy: `fronted` leaves a trace, and *John* c-commands
*himself* before the object moves, exactly because it does so in the copy object. -/
theorem binds_at_earlier_stage :
    fronted.BindsAtSomeStage ↑john ↑himself ∧ ¬ fronted.BindsAtSurface ↑john ↑himself :=
  ⟨(bindsAtSomeStage_iff_bindsAtLF (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)).2 no_reconstruction.1,
    no_reconstruction.2⟩

/-! ### Reconstruction for scope -/

/-- *every*. -/
def every : LexicalItem.Token := ⟨.of .D [.N] "every", 5⟩
/-- *player*. -/
def player : LexicalItem.Token := ⟨.of .N [] "player", 6⟩
/-- *didn't*. -/
def didnt : LexicalItem.Token := ⟨.of .T [.V] "didn't", 7⟩
/-- *score*. -/
def score : LexicalItem.Token := ⟨.of .V [.D] "score", 8⟩

/-- *every player*. -/
def everyPlayer : LinearizedSyntacticObject := .merge (.leaf every) (.leaf player)

/-- *Every player didn't score*: the subject raised past negation. -/
def everyDidntScore : Derivation :=
  ⟨score, [.em .left everyPlayer, .em .left (.leaf didnt), .im everyPlayer.toSyntacticObject]⟩

/-- The reading of (15) with negation over the universal needs the quantifier in the scope of
negation. It is there in the copy object of (16) and not in the contraction quotient, where only
the leaf the phrase contracted to remains under negation. -/
theorem no_scope_reconstruction :
    everyDidntScore.BindsAtLF ↑didnt everyPlayer.toSyntacticObject ∧
    ¬ everyDidntScore.BindsAtSurface ↑didnt everyPlayer.toSyntacticObject := by
  decide +kernel

/-- On the surface the quantifier scopes over negation instead. -/
example : everyDidntScore.replay?.isSome ∧
    everyDidntScore.BindsAtSurface everyPlayer.toSyntacticObject ↑didnt := by
  decide +kernel

/-! ### The readings of one derivation -/

-- (13), (14)
theorem binds_at_low_reading :
    fronted.BindsAtReading {picturesOfHimself.toSyntacticObject} ↑john ↑himself ∧
      ¬ fronted.BindsAtReading ∅ ↑john ↑himself :=
  ⟨by decide +kernel, fun h ↦ no_reconstruction.2 (bindsAtReading_empty_iff.1 h)⟩

/-- Read low, the fronted phrase is where it started: the object is that of *John loves pictures of
himself*. -/
example : fronted.lf? {picturesOfHimself.toSyntacticObject} = basic.externalize? := by
  decide +kernel

/-- The tree of (15) with the quantifier read low, in the scope of negation. -/
def lowTree : Tree Unit LexicalItem.Token :=
  .phrase () .projection [.terminal () didnt, .phrase () .projection
    [.phrase () .projection [.terminal () every, .terminal () player], .terminal () score]]

/-- The tree of (15) with the quantifier read high, over a binder and its trace. -/
def highTree : Tree Unit LexicalItem.Token :=
  .phrase () .projection [.phrase () .projection [.terminal () every, .terminal () player],
    .bind (every.id + 1) () (.phrase () .projection [.terminal () didnt,
      .phrase () .projection [.trace (every.id + 1) (), .terminal () score]])]

theorem toTree?_low :
    everyDidntScore.toTree? (·.id) {everyPlayer.toSyntacticObject} = some lowTree := by
  decide +kernel

theorem toTree?_high : everyDidntScore.toTree? (·.id) ∅ = some highTree := by
  decide +kernel

section Interpretation

variable {E : Type} (pl sc : Set E)

/-- The lexicon of (15), *every* being the determiner of the quantification substrate, for a set of
players and a set of those who scored. -/
def lex (tok : LexicalItem.Token) : Option (Denotation E Unit) :=
  if tok = every then
    some ⟨(Ty.e ⇒ Ty.t) ⇒ (Ty.e ⇒ Ty.t) ⇒ Ty.t,
      fun P Q ↦ Quantifier.Det.every {x | P x} {x | Q x}⟩
  else if tok = player then some ⟨Ty.e ⇒ Ty.t, (· ∈ pl)⟩
  else if tok = didnt then some ⟨Ty.t ⇒ Ty.t, Not⟩
  else if tok = score then some ⟨Ty.e ⇒ Ty.t, (· ∈ sc)⟩
  else none

theorem lex_every : lex pl sc every =
    some ⟨(Ty.e ⇒ Ty.t) ⇒ (Ty.e ⇒ Ty.t) ⇒ Ty.t,
      fun P Q ↦ Quantifier.Det.every {x | P x} {x | Q x}⟩ :=
  ite_eq_left rfl

theorem lex_player : lex pl sc player = some ⟨Ty.e ⇒ Ty.t, (· ∈ pl)⟩ := by
  rw [lex, ite_eq_right (by decide), ite_eq_left rfl]

theorem lex_didnt : lex pl sc didnt = some ⟨Ty.t ⇒ Ty.t, Not⟩ := by
  rw [lex, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]

theorem lex_score : lex pl sc score = some ⟨Ty.e ⇒ Ty.t, (· ∈ sc)⟩ := by
  rw [lex, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_left rfl]

/-- One derivation of (15) has both scope readings through the composition engine: read low, not
every player scored, the reading the paper describes in (16); read high, every player failed to. -/
theorem scope_readings (g : Assignment E) :
    (∃ t ∈ everyDidntScore.toTree? (·.id) {everyPlayer.toSyntacticObject},
      t.interp (lex pl sc) g = some ⟨.t, ¬ Quantifier.Det.every pl sc⟩) ∧
    (∃ t ∈ everyDidntScore.toTree? (·.id) ∅,
      t.interp (lex pl sc) g = some ⟨.t, Quantifier.Det.every pl scᶜ⟩) := by
  refine ⟨⟨lowTree, toTree?_low, ?_⟩, ⟨highTree, toTree?_high, ?_⟩⟩
  · simp [lowTree, lex_every, lex_player, lex_didnt, lex_score, Mode.combine?]
  · simp [highTree, lex_every, lex_player, lex_didnt, lex_score, Mode.combine?]
    rfl

/-- The two readings come apart when some player scored and another did not. -/
example : ¬ Quantifier.Det.every (Set.univ : Set Bool) {true} ∧
    ¬ Quantifier.Det.every (Set.univ : Set Bool) ({true} : Set Bool)ᶜ := by
  simp [Quantifier.Det.every, Set.subset_def]

end Interpretation

/-! ### No Tampering -/

/-- MERGE leaving copies keeps every term of the workspace, the clause among them. MERGE leaving the
contraction quotient loses the clause, which is the violation of No Tampering that Collins blames,
and which the workspace of Collins and Stabler does not incur. -/
theorem no_tampering :
    ({clause} : Workspace).terms ⊆
      (({clause} : Workspace).merge picturesOfHimself.toSyntacticObject clause).terms ∧
    clause ∉ (({clause} : Workspace).mergeWith (·.headTrace)
      picturesOfHimself.toSyntacticObject clause).terms :=
  ⟨Workspace.terms_subset_terms_merge, by decide +kernel⟩

end Collins2026
