module

public import Linglib.Semantics.Reference.Definiteness
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Syntax.Minimalist.Linearization.SpelloutDomain
public import Linglib.Syntax.Minimalist.SyntacticObject.Phase
public import Linglib.Syntax.Minimalist.Linearization.Spellout
public import Linglib.Syntax.Minimalist.SyntacticObject.Locality
public import Linglib.Data.Examples.ShenHuang2026
public import Linglib.Data.Examples.DaviesDubinsky2003
public import Mathlib.Data.Finset.Card

/-!
# Shen and Huang (2026): The Role of Phases and Specificity in Definite Islands

This file formalizes [shen-huang-2026]'s two-constraint theory of the definite island effect,
the degradation of a wh-dependency into a definite depiction nominal. The Phase Impenetrability
Condition (4) freezes the wh-phrase in the complement of a definite determiner ((5),
`impenetrable`) unless a verb of creation has incorporated the determiner and collapsed the
phase, after [davies-dubinsky-2003] and [boskovic-2015]; the Specificity Condition (13) forbids
binding a variable inside a specific DP from outside, whether by a moved wh-phrase or by a
question operator ([fiengo-1987], [huang-1982b], [li-1992]). A fronted wh-phrase leaves a
deleted copy in the DP, and the PIC is violated when the link between the two leaves the phase
from its interior (`Minimalist.Crosses`); a wh-phrase in situ is bound there and has one copy, so
no link and nothing for the PIC to constrain. Constraint stacking (§4.1) counts the constraints of
an account that a configuration violates (`violations`); of the accounts built from the two
constraints, only their combination predicts the observed pattern, a definite island in both
English and Mandarin with a verb-of-creation effect for fronted wh-phrases alone (`observed_iff`).
Binding escapes the PIC because it adds no ordering statement under cyclic linearization (§4.2,
`binding_linearizes`). On the LF-movement analysis of wh-in-situ (§5.2), with covert movement
subject to the PIC, an in-situ wh-phrase has a deleted copy above it whose link leaves the DP, and
no account predicts the absence of a verb-of-creation effect in Mandarin
(`not_observed_covert`).

## Implementation notes

* The experiments' effect sizes stay out of the formalization: the theory predicts the presence
  and direction of the contrasts, not their magnitude, which the paper notes differs across the
  two languages.
* Incorporation is read off the verb: a verb of creation incorporates the determiner. The
  conditions on incorporation the paper leaves open, and the information-structure rival of §5.1,
  are not formalized. The LF-movement analysis enters only in the variant with covert movement
  subject to the PIC; the paper's further point against it, that English verbs of creation still
  show a smaller definite island, is a matter of effect sizes.
* The extracted wh-phrase moves out of the DP in one step, the escape hatch at its edge being
  denied (§2.1); the verb phrase stands in for the clause.

## References

* [shen-huang-2026]
* [davies-dubinsky-2003]
* [boskovic-2015]
* [fiengo-1987]
* [huang-1982b]
* [li-1992]
* [fox-pesetsky-2005]
* [chomsky-2000]
-/

@[expose] public section

namespace ShenHuang2026

open Minimalist Minimalist.Linearization ArgumentStructure

/-- A cell of the factorial design (20), (21) fixes whether the wh-phrase is fronted, as in
English, or stays in situ, as in Mandarin; the definiteness of the object DP the wh-element sits
in, the demonstrative being specific; and whether the main verb is a verb of creation. -/
structure Config where
  fronted : Bool
  object : Definiteness
  creation : Bool
  deriving DecidableEq, Repr

/-! ### The object DP (5) -/

/-- The wh-phrase, the complement of *about*. -/
def wh : LexicalItem.Token := ⟨.of .D [] "what" true, 0⟩

/-- The preposition of the depiction nominal. -/
def about : LexicalItem.Token := ⟨.of .P [.D] "about", 1⟩

/-- The head noun, selecting the depiction PP. -/
def book : LexicalItem.Token := ⟨.of .N [.P] "book", 2⟩

/-- The demonstrative determiner of a definite object. -/
def that : LexicalItem.Token := ⟨.of .D [.N] "that", 3⟩

/-- The indefinite determiner. -/
def a : LexicalItem.Token := ⟨.of .D [.N] "a", 4⟩

/-- The main verb. -/
def verb : LexicalItem.Token := ⟨.of .V [.D], 5⟩

/-- The determiner of the object is the demonstrative when it is definite. -/
def determiner : Definiteness → LexicalItem.Token
  | .definite => that
  | .indefinite => a

/-- The object DP of (25) has the wh-phrase in the complement of the determiner. -/
def dp (o : Definiteness) : LinearizedSyntacticObject := determiner o * (book * (about * wh))

/-- The verb phrase of (25). -/
def vp (o : Definiteness) : LinearizedSyntacticObject := verb * dp o

/-- The wh-phrase lies in the domain of the determiner, so the PIC (4) freezes it in any phase the
determiner heads (5). -/
theorem impenetrable (o : Definiteness) :
    (vp o : SyntacticObject).WithinComplement (determiner o) wh := by
  cases o <;> decide

/-- The escape hatch the account denies (§2.1) is the verb phrase with the wh-phrase moved to
Spec,DP. -/
def vpEdge : LinearizedSyntacticObject := verb * (wh * (that * (book * (about * .traceOf wh))))

/-- At the edge of the phase, the wh-phrase is in the phase but outside the reach of the PIC. -/
theorem edge_not_impenetrable :
    (wh : SyntacticObject) ∈ (vpEdge : SyntacticObject).phaseEdge that := by
  decide

/-- The wh-phrase fronted out of the object DP, leaving a deleted copy in the complement of
*about*. -/
def extracted (o : Definiteness) : LinearizedSyntacticObject :=
  wh * (verb * (determiner o * (book * (about * .traceOf wh))))

/-- The LF-movement analysis of an in-situ wh-phrase ([huang-1982b], §5.2) puts a deleted copy
above the pronounced one. -/
def covert (o : Definiteness) : LinearizedSyntacticObject := .traceOf wh * vp o

/-- Covert movement leaves the string of the in-situ object. -/
example (o : Definiteness) : pfPhon (covert o) = pfPhon (vp o) := by
  cases o <;> decide

/-- The object of a cell is the wh-phrase extracted, or in situ, bound by an operator after
[li-1992]. -/
def Config.tree (c : Config) : LinearizedSyntacticObject :=
  if c.fronted then extracted c.object else vp c.object

/-- The object of a cell on the LF-movement analysis of wh-in-situ. -/
def Config.covertTree (c : Config) : LinearizedSyntacticObject :=
  if c.fronted then extracted c.object else covert c.object

/-! ### The two constraints -/

/-- On the DP phasehood account (§2.1) the demonstrative heads a phase, which a verb of creation
collapses by incorporating it. -/
def Config.phaseHead (c : Config) : Option LexicalItem.Token :=
  if c.object = .definite ∧ c.creation = false then some that else none

/-- The demonstrative-marked DP is the specific one, in [fiengo-1987]'s sense of familiar. -/
def Config.specific (c : Config) : Option SyntacticObject :=
  if c.object = .definite then some (dp c.object) else none

/-- The PIC (4) is violated in `t` when a link of the wh-phrase's chain leaves the phase that the
cell's determiner heads, from its interior. -/
def Config.ViolatesPIC (c : Config) (t : LinearizedSyntacticObject) : Prop :=
  ∃ ℓ ∈ c.phaseHead, ∃ h ∈ occurrences t ℓ, Crosses t wh h

instance (c : Config) (t : LinearizedSyntacticObject) : Decidable (c.ViolatesPIC t) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The two constraints. -/
inductive Constraint
  | pic | specificity
  deriving DecidableEq, Repr, Fintype

/-- The Phase Impenetrability Condition (4) is violated when a link of the wh-phrase's chain leaves
a phase from its interior; the Specificity Condition (13) when a variable inside a specific DP is
bound from outside, whatever the binder. -/
def Constraint.Violated : Constraint → Config → Prop
  | .pic, c => c.ViolatesPIC c.tree
  | .specificity, c => ∃ d ∈ c.specific, d.Contains wh

instance (k : Constraint) : DecidablePred k.Violated := fun _ ↦ by
  cases k <;> unfold Constraint.Violated <;> infer_instance

/-- The PIC on the links of the chain agrees with the PIC on terms: a link leaves the phase from
its interior exactly when the deleted copy, within the complement of the cell's phase head, is
inaccessible to the pronounced one under [chomsky-2000]'s condition. -/
theorem violatesPIC_iff_not_accessible (c : Config) :
    c.ViolatesPIC c.tree ↔
      ¬ (c.tree : SyntacticObject).Accessible c.phaseHead.toList .phase wh (.traceOf wh) := by
  obtain ⟨f, o, v⟩ := c
  cases f <;> cases o <;> cases v <;> decide

/-- Fronting out of a definite object under a verb that is not a verb of creation, and nothing
else, violates the PIC. -/
theorem pic_violated_iff (c : Config) :
    Constraint.Violated .pic c ↔
      c.fronted = true ∧ c.object = .definite ∧ c.creation = false := by
  obtain ⟨f, o, v⟩ := c
  cases f <;> cases o <;> cases v <;> decide

/-- On the LF-movement analysis with covert movement subject to the PIC, an in-situ wh-phrase
crosses the phase wherever a fronted one does, so the analysis predicts a definite island that a
verb of creation removes in Mandarin too (§3, §5.2), the verb-of-creation effect the Mandarin
experiment does not find (Table 2). -/
theorem violatesPIC_covertTree_iff (c : Config) :
    c.ViolatesPIC c.covertTree ↔ c.object = .definite ∧ c.creation = false := by
  obtain ⟨f, o, v⟩ := c
  cases f <;> cases o <;> cases v <;> decide

/-- A definite object, and nothing else, violates the Specificity Condition. -/
theorem specificity_violated_iff (c : Config) :
    Constraint.Violated .specificity c ↔ c.object = .definite := by
  obtain ⟨f, o, v⟩ := c
  cases f <;> cases o <;> cases v <;> decide

/-! ### Constraint stacking (§4.1) -/

/-- The number of constraints of an account that a configuration violates, the more the less
acceptable. -/
def violations (account : Finset Constraint) (c : Config) : ℕ :=
  (account.filter (·.Violated c)).card

/-- The DP phasehood account. -/
def phasehood : Finset Constraint := {.pic}

/-- The Specificity Condition account. -/
def specificity : Finset Constraint := {.specificity}

/-- The paper's proposal combines both constraints. -/
def combined : Finset Constraint := {.pic, .specificity}

/-- An indefinite object violates nothing under any account: it is neither a phase nor
specific. -/
theorem violations_indefinite (account : Finset Constraint) (fronted v : Bool) :
    violations account ⟨fronted, .indefinite, v⟩ = 0 :=
  Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun k _ ↦ by
    cases k <;> cases fronted <;> cases v <;> decide)

/-- An account predicts a definite island effect for a fronted or an in-situ wh-phrase and a verb
class when the definite object violates more of its constraints than the indefinite one. -/
def IslandEffect (account : Finset Constraint) (fronted v : Bool) : Prop :=
  violations account ⟨fronted, .indefinite, v⟩ < violations account ⟨fronted, .definite, v⟩

/-- An account predicts a verb-of-creation effect for a fronted or an in-situ wh-phrase when a
verb of creation lowers the count for a definite object; an indefinite one violates nothing
either way. -/
def VOCEffect (account : Finset Constraint) (fronted : Bool) : Prop :=
  violations account ⟨fronted, .definite, true⟩ < violations account ⟨fronted, .definite, false⟩

instance (account : Finset Constraint) (fronted v : Bool) :
    Decidable (IslandEffect account fronted v) := inferInstanceAs (Decidable (_ < _))

instance (account : Finset Constraint) (fronted : Bool) :
    Decidable (VOCEffect account fronted) :=
  inferInstanceAs (Decidable (_ < _))

/-- Experiments 1 and 2 found (Table 2) a definite island for fronted and in-situ wh-phrases under
every verb class, and a verb-of-creation effect for the fronted ones alone. -/
def Observed (account : Finset Constraint) : Prop :=
  (∀ fronted v, IslandEffect account fronted v) ∧ VOCEffect account true ∧
    ¬ VOCEffect account false

instance (account : Finset Constraint) : Decidable (Observed account) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- DP phasehood alone (Table 1) predicts an island for a fronted wh-phrase only under a verb that
is not a verb of creation, hence a verb-of-creation effect, and no island in situ. -/
theorem phasehood_predictions :
    IslandEffect phasehood true false ∧ ¬ IslandEffect phasehood true true ∧
      VOCEffect phasehood true ∧ ∀ v, ¬ IslandEffect phasehood false v := by
  decide

/-- The Specificity Condition alone (Table 1) predicts an island for fronted and in-situ
wh-phrases under every verb class, and no verb-of-creation effect. -/
theorem specificity_predictions :
    (∀ fronted v, IslandEffect specificity fronted v) ∧
      ∀ fronted, ¬ VOCEffect specificity fronted := by
  decide

/-- Of the accounts built from the two constraints, exactly the combination predicts the
observed pattern (Table 2): one constraint is not empirically adequate. -/
theorem observed_iff (account : Finset Constraint) : Observed account ↔ account = combined := by
  revert account
  decide

/-! ### The cited judgments -/

/-- The configuration an example's features record. -/
def Config.ofDatum (ex : Datum) : Option Config := do
  let f ← ex.parse? "wh" [("fronted", true), ("inSitu", false)]
  let o ← ex.parse? "object" [("definite", Definiteness.definite), ("indefinite", .indefinite)]
  let v ← ex.parse? "creation" [("yes", true), ("no", false)]
  pure ⟨f, o, v⟩

/-- In the verb-of-creation contrasts of [davies-dubinsky-2003], (52)–(54), which the paper's
Experiment 1 revisits, a non-creation verb with a definite object violates one constraint of the
combined account more than a creation verb, and the row is judged no better. -/
theorem stacking_daviesDubinsky :
    ∀ ex₁ ∈ DaviesDubinsky2003.Examples.all, ∀ ex₂ ∈ DaviesDubinsky2003.Examples.all,
      ∀ c₁ ∈ Config.ofDatum ex₁, ∀ c₂ ∈ Config.ofDatum ex₂,
        violations combined c₁ < violations combined c₂ →
          ex₂.judgment ≤ ex₁.judgment := by
  decide

/-- Constraints stack on the paper's cited judgments, since within a language an example violating
strictly more constraints of the combined account is judged no better. -/
theorem stacking : ∀ ex₁ ∈ Examples.all, ∀ ex₂ ∈ Examples.all, ex₁.language = ex₂.language →
    ∀ c₁ ∈ Config.ofDatum ex₁, ∀ c₂ ∈ Config.ofDatum ex₂,
      violations combined c₁ < violations combined c₂ →
        ex₂.judgment ≤ ex₁.judgment := by
  decide

/-! ### Binding and the PIC under cyclic linearization (§4.2) -/

/-- A terminal is a word of *What do you think Mary would eat?* (27). -/
inductive Terminal
  | what | «do» | you | think | mary | would | eat
  deriving DecidableEq, Repr

section Linearization

open Terminal

/-- Each terminal spells out its own lexical item. -/
def Terminal.token : Terminal → LexicalItem.Token
  | what => ⟨.of .D [], 11⟩
  | «do» => ⟨.of .T [], 12⟩
  | you => ⟨.of .D [], 13⟩
  | think => ⟨.of .V [], 14⟩
  | mary => ⟨.of .D [], 15⟩
  | would => ⟨.of .T [], 16⟩
  | eat => ⟨.of .V [], 17⟩

/-- A lexical item spells out at most one terminal. -/
def Terminal.ofToken? (tok : LexicalItem.Token) : Option Terminal :=
  [what, «do», you, think, mary, would, eat].find? (·.token = tok)

/-- The embedded complementizer is silent. -/
def embeddedC : LexicalItem.Token := ⟨.of .C [], 18⟩

/-- In the embedded clause *eat* merges with *what*, then *would*, *Mary* and the
complementizer. -/
def embeddedSteps : List Step :=
  [.em .right what.token, .em .left would.token, .em .left mary.token,
    .em .left embeddedC]

/-- In the matrix clause *think*, *you* and *do* merge over the embedded clause. -/
def matrixSteps : List Step :=
  [.em .left think.token, .em .left you.token, .em .left «do».token]

/-- *What* moves to the edge of the clause built so far, or stays. -/
def moveWhat (b : Bool) : List Step := if b then [.im what.token] else []

/-- In a derivation of (27) *what* stops at the edge of the embedded clause or not, and then
moves to the edge of the matrix clause or stays in situ. -/
def derivation (edge front : Bool) : Derivation :=
  ⟨eat.token, embeddedSteps ++ moveWhat edge ++ matrixSteps ++ moveWhat front⟩

/-- The embedded clause is built once *what* has stopped at its edge or not. -/
def embeddedStage (edge : Bool) : ℕ := (embeddedSteps ++ moveWhat edge).length

/-- Each clause is spelled out when it is built. -/
def schedule (edge front : Bool) : List (ℕ × ℕ) :=
  [(embeddedStage edge, embeddedStage edge),
    ((derivation edge front).length, (derivation edge front).length)]

/-- The embedded clause is spelled out with *what* first when it stops at the edge, and last when
it stays in situ (27). -/
theorem embedded_spellout (edge front : Bool) :
    ((derivation edge front).spellout (embeddedStage edge) (embeddedStage edge)).filterMap
      Terminal.ofToken? =
      if edge then [what, mary, would, eat] else [mary, would, eat, what] := by
  cases edge <;> cases front <;> decide

/-- When *what* stops at the edge of the embedded clause (27a), the order fixed there is preserved
at the matrix Spell-out and the derivation linearizes. -/
theorem edge_stop_linearizes : (derivation true true).Linearizes (schedule true true) := by
  decide

/-- When *what* stays in situ as the embedded clause is spelled out (27b), it follows *Mary* there
and precedes her at the matrix Spell-out, an ordering contradiction; this is the
cyclic-linearization content of the PIC on movement. -/
theorem phase_skip_not_linearizes : ¬ (derivation false true).Linearizes (schedule false true) := by
  decide

/-- Binding leaves the word order alone: with *what* in situ at both Spell-outs no ordering
statement is added and the derivation linearizes, so a dependency established by binding never
meets the contradiction that enforces the PIC on movement. -/
theorem binding_linearizes : (derivation false false).Linearizes (schedule false false) := by
  decide

end Linearization

/-! ### Verbs of creation in the Fragment -/

/-- The paper names as verbs of creation, after [davies-dubinsky-2003]'s verbs of creation
selecting a result nominal (*write* for a book, *tell* for a joke, *paint* for a portrait),
*compose* (3), *tell* a joke (20b), *direct* (23), *shoot*, *make* and *compose* a video or
song (footnote 12), and *write* (25b). The notion is per verb, not a Levin class: *tell* and
*shoot* belong to no class of creation in [levin-1993]. -/
def IsVerbOfCreation (v : English.Verbs.Verb) : Prop :=
  v.form ∈ ["compose", "direct", "make", "shoot", "tell", "write"]

instance : DecidablePred IsVerbOfCreation := fun v ↦ inferInstanceAs (Decidable (v.form ∈ _))

/-- The configuration of an item whose main verb is a Fragment entry. -/
def Config.ofVerb (fronted : Bool) (o : Definiteness) (v : English.Verbs.Verb) : Config :=
  ⟨fronted, o, decide (IsVerbOfCreation v)⟩

/-- In (25) *read that book about* violates both constraints and *write that book about* the
Specificity Condition alone, the residual definite island under a verb of creation. -/
theorem read_write :
    violations combined (Config.ofVerb true .definite English.Verbs.read) = 2 ∧
      violations combined (Config.ofVerb true .definite English.Verbs.write) = 1 := by
  decide

end ShenHuang2026
