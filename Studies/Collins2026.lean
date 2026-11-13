/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.Examples.Collins2026
public import Linglib.Semantics.Composition.Constituency
public import Linglib.Semantics.Composition.Rules
public import Linglib.Semantics.Composition.Sorts
public import Linglib.Semantics.Composition.PredicateAbstraction
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Syntax.Minimalist.Copy.Cut
public import Linglib.Syntax.Minimalist.Workspace.Basic
public import Linglib.Syntax.Minimalist.Workspace.Coproduct.TraceConservation

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
readings](##scope_readings) by Functional Application and abstraction. Both cut the quantifier
phrase from the
copy object, and [the low reading is no term](##scope_readings_cut) of the coproduct the book sends
to the semantic interface, which leaves a trace at every cut.

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
* The paper gives (15) no denotations: it describes the reading with negation over the quantifier
  and the copy structure (16). The determiner, negation and predicates interpreted here are the
  standard ones.
* The reading with no chain read low is the book's contraction with a binder the book does not have.
  The low reading deletes the higher copy, where the book removes only the lower one, so the two
  scope readings are the copy theory's, not the framework's.

## References

* [collins-2026]
* [marcolli-chomsky-berwick-2025]
* [collins-stabler-2016]
* [cole-hermon-2008]
* [chomsky-1995]
-/

@[expose] public section

namespace Collins2026

open Minimalist Minimalist.Derivation Interpreter PhraseStructure

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
def picturesOfHimself : PlanarSyntacticObject :=
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
def everyPlayer : PlanarSyntacticObject := .merge (.leaf every) (.leaf player)

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
  ⟨by decide +kernel, fun h ↦
    no_reconstruction.2 ((bindsAtReading_empty_iff (by decide +kernel)).1 h)⟩

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
    everyDidntScore.toTree? traceIndex {everyPlayer.toSyntacticObject} = some lowTree := by
  decide +kernel

theorem toTree?_high : everyDidntScore.toTree? traceIndex ∅ = some highTree := by
  decide +kernel

section Interpretation



variable {E : Type} (pl sc : Set E)

/-- The lexical items of (15) by type, and the trace of an index. -/
inductive Item : Ty Base → Type
  | every : Item .det
  | player : Item .et
  | didnt : Item (.t ⇒ .t)
  | score : Item .et
  | trace (n : ℕ) : Item .e

/-- The item of a token of (15), and of a trace. -/
def items : LexicalItem.Token ⊕ ℕ → List (Σ a, Item a)
  | .inl tok =>
    if tok = every then [⟨_, .every⟩]
    else if tok = player then [⟨_, .player⟩]
    else if tok = didnt then [⟨_, .didnt⟩]
    else if tok = score then [⟨_, .score⟩]
    else []
  | .inr n => [⟨_, .trace n⟩]

/-- The denotations of (15), *every* being the determiner of the quantification substrate, for a
set of players and a set of those who scored. -/
def Item.val : {a : Ty Base} → Item a → (ℕ → E) → a.Dom (Base.Dom E Unit)
  | _, .every => fun _ P Q ↦ Quantifier.Det.every {x | P x} {x | Q x}
  | _, .player => fun _ ↦ (· ∈ pl)
  | _, .didnt => fun _ ↦ Not
  | _, .score => fun _ ↦ (· ∈ sc)
  | _, .trace n => fun g ↦ g n

/-- The denotations of a tree, by Functional Application and abstraction over an index. -/
def meanings (t : Tree Unit LexicalItem.Token) :
    List (Σ a : Ty Base, (ℕ → E) → a.Dom (Base.Dom E Unit)) :=
  t.values ((typeDriven application).withAbstraction fun _ ↦ .e)
    (ManySorted.Language.withAbstraction.structure (Assignments.total (Base.Dom E Unit) fun _ ↦ .e))
    (Item.val pl sc) items

theorem meanings_lowTree :
    meanings pl sc lowTree = [⟨.t, fun _ ↦ ¬ Quantifier.Det.every pl sc⟩] :=
  rfl

theorem meanings_highTree :
    meanings pl sc highTree = [⟨.t, fun _ ↦ Quantifier.Det.every pl scᶜ⟩] :=
  rfl

/-- One derivation of (15) has both scope readings: read low, not every player scored, the
reading the paper describes in (16); read high, every player failed to. -/
theorem scope_readings :
    (∃ t ∈ everyDidntScore.toTree? traceIndex {everyPlayer.toSyntacticObject},
      meanings pl sc t = [⟨.t, fun _ ↦ ¬ Quantifier.Det.every pl sc⟩]) ∧
    (∃ t ∈ everyDidntScore.toTree? traceIndex ∅,
      meanings pl sc t = [⟨.t, fun _ ↦ Quantifier.Det.every pl scᶜ⟩]) :=
  ⟨⟨lowTree, toTree?_low, meanings_lowTree pl sc⟩,
    ⟨highTree, toTree?_high, meanings_highTree pl sc⟩⟩

/-- The two readings come apart when some player scored and another did not. -/
example : ¬ Quantifier.Det.every (Set.univ : Set Bool) {true} ∧
    ¬ Quantifier.Det.every (Set.univ : Set Bool) ({true} : Set Bool)ᶜ := by
  simp [Quantifier.Det.every, Set.subset_def]

end Interpretation

/-! ### The readings as cuts -/

open ConnesKreimer PlanarSyntacticObject.Marked in
/-- The readings of (15) both cut the quantifier phrase from the copy object. The high reading is a
term of `Δ^c`, cutting the lower copy, and the low reading a term of `Δ^d`, cutting the higher copy.
The low reading is no term of `Δ^c`, whose cuts each leave a trace. -/
theorem scope_readings_cut : ∃ c ∈ everyDidntScore.replayWithCopies?,
    let C := UnorderedTree.mk c.current.unmark.toRoseTree
    let τ := termTrace SyntacticObject.selHead
    let lowReading := UnorderedTree.mk (c.current.lf {everyPlayer.toSyntacticObject}).toRoseTree
    ({UnorderedTree.mk everyPlayer.toRoseTree}, UnorderedTree.mk c.current.contract.toRoseTree) ∈
        traceCuts τ C ∧
      ({UnorderedTree.mk everyPlayer.toRoseTree}, lowReading) ∈ deletionCuts C ∧
      ∀ F, (F, lowReading) ∉ traceCuts τ C := by
  have h : ∀ c ∈ everyDidntScore.replayWithCopies?,
      c.current.val.value.1 = none ∧ MarkedBy (termTrace SyntacticObject.selHead) c.current.val ∧
      c.current.cutForest ∅ = {everyPlayer.toRoseTree} ∧
      c.current.cutForest {everyPlayer.toSyntacticObject} = {everyPlayer.toRoseTree} ∧
      (∀ r ∈ c.current.val.subtrees, r.value.1.isSome →
        ReadLow {everyPlayer.toSyntacticObject} r) ∧
      (UnorderedTree.mk c.current.unmark.toRoseTree).numTraces = 0 ∧
      (UnorderedTree.mk (c.current.lf {everyPlayer.toSyntacticObject}).toRoseTree).numTraces = 0 ∧
      UnorderedTree.mk (c.current.lf {everyPlayer.toSyntacticObject}).toRoseTree ≠
        UnorderedTree.mk c.current.unmark.toRoseTree := by
    decide +kernel
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1
    (by decide +kernel : everyDidntScore.replayWithCopies?.isSome)
  obtain ⟨hroot, hτ, hhigh, hlow, hall, hC, hL, hne⟩ := h c hc
  refine ⟨c, hc, ?_, ?_, fun F hF ↦ hne (congrArg Prod.snd
    (eq_zero_of_mem_traceCuts _ hC hF hL))⟩
  · simpa [hhigh] using mem_traceCuts_contract c.current hroot hτ
  · simpa [hlow] using mem_deletionCuts_lf c.current _ hall

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
