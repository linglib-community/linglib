module

public import Linglib.Syntax.Tree.QuantifierRaising
public import Linglib.Semantics.Composition.Extension
public import Linglib.Semantics.Composition.Sorts
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Syntax.Cat
public import Linglib.Fragments.English.Determiners
public import Linglib.Data.Examples.Barker2027

/-!
# Barker (2027): Scope

Barker's survey takes Quantifier Raising as the general theory of scope and asks what restricts
it. The orders in which the quantifiers of *someone saw everyone* raise [give its two
readings](##Barker2027.meanings_linear_inverse), the one formal constraint is that a logical form
have a type analysis, which [raising the subject alone does
not](##Barker2027.isLogicalForm_not_coherent), and with Lift raising [derives the shifted verb of
Flexible Montague Grammar](##Barker2027.meanings_argumentRaising). Among the empirical
constraints, a tensed clause is an island for *every* and not for *each*, so [no theory that sees
a scope-taker through its readings fits both](##Barker2027.not_fits_ofReadings), while [one that
names the determiner does](##Barker2027.rows_everyIsland).

## Implementation notes

* A tree's words are determiner entries of the English fragment and other words as strings, and
  *everyone* is the determiner *every* with the noun *one*.
* A tensed clause has the category `S`; an infinitival clause is a projection of *to*, a
  particle. An adjunction to a clause is a segment of the clause, so a constituent raised to the
  edge of an island is still inside it.
* The inverse reading of a row is available when the embedded quantifier can raise to the edge of
  the sentence. The article's examples of relative and adjunct clauses, (19) and (20a), are in the
  rows and are not given trees.

* The trees of the section on theories of scope are unlabelled, as the article's are, and their
  words are a separate type from the words of the island examples: those are strings, which have
  no denotations. A logical form is interpreted by Heim and Kratzer's rules, Functional
  Application and Predicate Abstraction, which the article adopts.
* The type of each index is given with a logical form. The article reads it off the constituent
  that moved.

## TODO

* The island examples are judged by whether a constituent can raise, and their readings are
  labels of the rows. They are not the meanings of logical forms.
* That Value Raising and Argument Raising are derivable in general, of which (16) is an instance,
  is not stated: it is a simulation of one system of rules by another.
* Cooper storage, Combinatory Categorial Grammar and continuations are not formalized here, so
  that they assign the readings Quantifier Raising does is not stated.

* That an island confines a scope-taker under every sequence of steps, and not only the one step
  to the edge of the sentence, is not proved.

## References

* [barker-2027]
* [may-1985]
* [heim-kratzer-1998]
-/

@[expose] public section

namespace Barker2027

open PhraseStructure PhraseStructure.Tree English.Determiners

/-- A word is a determiner entry of the fragment or another word. -/
abbrev Word := QuantificationalDeterminer ⊕ String

/-- The determiners in a constituent. -/
def determiners (a : Tree Cat Word) : List QuantificationalDeterminer :=
  a.yield.filterMap Sum.getLeft?

/-! ### Scope by Quantifier Raising

The article's logical forms are interpreted by Function Application and Predicate Abstraction
over an arbitrary model. -/

section Composition

open Interpreter ManySorted Quantifier

/-- The words of the examples of the sections on scope ambiguity and on theories of scope. -/
inductive Lexeme
  | amy | saw | someone | everyone | mother
  deriving DecidableEq, Repr

/-- The lexical items by type: a name, a transitive verb, two generalized quantifiers and a
relational noun. -/
inductive Item : Ty Base → Type
  | amy : Item .e
  | saw : Item .eet
  | someone : Item .ett
  | everyone : Item .ett
  | mother : Item (.e ⇒ .e)

/-- The item of each word. -/
def items : Lexeme → List (Σ a, Item a)
  | .amy => [⟨_, .amy⟩]
  | .saw => [⟨_, .saw⟩]
  | .someone => [⟨_, .someone⟩]
  | .everyone => [⟨_, .everyone⟩]
  | .mother => [⟨_, .mother⟩]

/-- A model of the examples: an individual, the people, a relation of what is seen to who sees
it, and each individual's mother. -/
structure Model (E : Type) where
  /-- Amy. -/
  amy : E
  /-- The people. -/
  person : E → Prop
  /-- `saw x y`: `y` saw `x`, the object first as in the article's `saw x amy`. -/
  saw : E → E → Prop
  /-- An individual's mother. -/
  mother : E → E

variable {E : Type} (M : Model E)

/-- The denotation of an item: *someone* and *everyone* are *some* and *every* over the
people. -/
def Item.val : {a : Ty Base} → Item a → a.Dom (Base.Dom E Unit)
  | _, .amy => M.amy
  | _, .saw => M.saw
  | _, .someone => fun P ↦ Det.some M.person P
  | _, .everyone => fun P ↦ Det.every M.person P
  | _, .mother => M.mother

/-- The meanings of a logical form whose indices have the types `Γ`, by Function Application
and Predicate Abstraction. -/
def meanings (Γ : ℕ → Ty Base) (t : Tree Unit Lexeme) :
    List (Σ a : Ty Base, (∀ n, (Γ n).Dom (Base.Dom E Unit)) → a.Dom (Base.Dom E Unit)) :=
  t.interpret application (Base.Dom E Unit) Γ (fun i _ ↦ i.val M) items

/-- A logical form is coherent when it has a type analysis: each node is an instance of Function
Application or Predicate Abstraction. -/
def Coherent (Γ : ℕ → Ty Base) (t : Tree Unit Lexeme) : Prop :=
  t.derive application Γ items ≠ []

/-- Traces of individuals. -/
abbrev ind : ℕ → Ty Base := fun _ ↦ .e

/-- *Amy saw everyone*, as it is pronounced. -/
def amySawEveryone : Tree Unit Lexeme := .bin (.leaf .amy) (.bin (.leaf .saw) (.leaf .everyone))

/-- The logical form of *Amy saw everyone*: the quantifier raised to the edge of the sentence. -/
def amySawEveryoneLF : Tree Unit Lexeme := amySawEveryone.raiseOf 1 (.leaf .everyone)

theorem derive_amySawEveryoneLF :
    amySawEveryoneLF.derive application ind items =
      [⟨.t, .binary (.inl .fa) (.leaf (.word .everyone))
        (.unary (.inr (.index 1 .t)) (.binary (.inl .ba) (.leaf (.word .amy))
          (.binary (.inl .fa) (.leaf (.word .saw)) (.leaf (.trace 1)))))⟩] := rfl

theorem meanings_amySawEveryone :
    meanings M ind amySawEveryoneLF = [⟨.t, fun _ ↦ Det.every M.person fun x ↦ M.saw x M.amy⟩] :=
  rfl

theorem uninterpretable_amySawEveryone :
    amySawEveryone.Uninterpretable ((typeDriven application).withAbstraction ind)
      (Leaf.lex items ind) :=
  ⟨by decide, rfl⟩

/-- (5) *Someone saw everyone*. -/
def someoneSawEveryone : Tree Unit Lexeme :=
  .bin (.leaf .someone) (.bin (.leaf .saw) (.leaf .everyone))

/-- The logical form of the linear scoping: the object raised, and the subject over it. -/
def linear : Tree Unit Lexeme :=
  (someoneSawEveryone.raiseOf 1 (.leaf .everyone)).raiseOf 2 (.leaf .someone)

/-- The logical form of the inverse scoping: the subject raised, and the object over it. -/
def inverse : Tree Unit Lexeme :=
  (someoneSawEveryone.raiseOf 2 (.leaf .someone)).raiseOf 1 (.leaf .everyone)

/-- The relative scope of the quantifiers of (5) depends on the order in which they raise: with
*someone* raised last there is one person who saw everyone, and with *everyone* raised last
each person may have been seen by another. -/
theorem meanings_linear_inverse :
    meanings M ind linear =
        [⟨.t, fun _ ↦ Det.some M.person fun y ↦ Det.every M.person fun x ↦ M.saw x y⟩] ∧
      meanings M ind inverse =
        [⟨.t, fun _ ↦ Det.every M.person fun x ↦ Det.some M.person fun y ↦ M.saw x y⟩] :=
  ⟨rfl, rfl⟩

theorem meanings_objectRaised :
    meanings M ind (someoneSawEveryone.raiseOf 1 (.leaf .everyone)) =
      [⟨.t, fun _ ↦ Det.every M.person fun x ↦ Det.some M.person fun y ↦ M.saw x y⟩] :=
  rfl

/-- Type coherence is a constraint of its own: raising the subject of (5) alone is a step of
Quantifier Raising, and its result has no type analysis, the object still where it cannot
compose. -/
theorem isLogicalForm_not_coherent :
    IsLogicalForm ⊥ someoneSawEveryone (someoneSawEveryone.raiseOf 2 (.leaf .someone)) ∧
      ¬ Coherent ind (someoneSawEveryone.raiseOf 2 (.leaf .someone)) :=
  ⟨(IsLogicalForm.refl _).raiseOf rfl (passesNoIsland_bot _ _) 2, fun h ↦ h rfl⟩

-- §3.1.3: other modes of combination can be added, and a logical form keeps its meanings
theorem mem_interpret_withModification {Γ : ℕ → Ty Base} {t : Tree Unit Lexeme}
    {d : Σ a : Ty Base, (∀ n, (Γ n).Dom (Base.Dom E Unit)) → a.Dom (Base.Dom E Unit)}
    (hd : d ∈ meanings M Γ t) :
    d ∈ t.interpret (application.sum predicateModification) (Base.Dom E Unit) Γ
      (fun i _ ↦ i.val M) items :=
  Tree.mem_interpret_sum Γ _ items hd

/-! ### Lift and Flexible Montague Grammar

Lift (9) is a manipulation of logical forms as Quantifier Raising is: `A` becomes `[n [tₙ A]]`,
the trace of the type of a function of `A`. With it, raising derives the type shifts of Flexible
Montague Grammar. -/

/-- (9) applied to *Amy*: `[1 [t₁ Amy]]`. -/
def liftedAmy : Tree Unit Lexeme := .binder 1 (.bin (.tr 1) (.leaf .amy))

theorem meanings_liftedAmy :
    meanings M (fun _ ↦ .et) liftedAmy = [⟨.ett, fun _ P ↦ P M.amy⟩] := rfl

/-- The types of the indices of (16): the first two are of quantifier type, the others of
individuals. -/
def argumentRaisingTypes (n : ℕ) : Ty Base := if n = 1 ∨ n = 2 then .ett else .e

/-- (16) `[1 [2 [t₁ [4 [t₂ [3 [t₃ [saw t₄]]]]]]]]`, derived from *saw* by two Lifts and two steps
of raising. -/
def argumentRaising : Tree Unit Lexeme :=
  .binder 1 (.binder 2 (.bin (.tr 1) (.binder 4 (.bin (.tr 2) (.binder 3
    (.bin (.tr 3) (.bin (.leaf .saw) (.tr 4))))))))

/-- The standard interpretation of (16) is the verb of (14), *saw* with both arguments raised
and the first to combine taking scope over the second: `λQ λP. Q(λx. P(λy. saw x y))`. Argument
Raising is here a theorem of Quantifier Raising with Lift. -/
theorem meanings_argumentRaising :
    meanings M argumentRaisingTypes argumentRaising =
      [⟨.ett ⇒ .ett ⇒ .t, fun _ Q P ↦ Q fun x ↦ P fun y ↦ M.saw x y⟩] := rfl

end Composition

/-! ### Theories of islands -/

/-- The island theories that see a scope-taker through the readings of its determiners and a
subtree through its category: a subtree whose category satisfies `Q` is an island for a
constituent with a determiner whose readings satisfy `P`. -/
def ofReadings (P : Finset Quantifier.Det.Symbol → Prop) (Q : Cat → Prop)
    (a b : Tree Cat Word) : Prop :=
  (∃ d ∈ determiners a, P d.readings) ∧ Q b.cat

instance (P : Finset Quantifier.Det.Symbol → Prop) (Q : Cat → Prop) [DecidablePred P]
    [DecidablePred Q] (a b : Tree Cat Word) : Decidable (ofReadings P Q a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The classic theory: a tensed clause is an island for a universal. -/
def tensedClause : Tree Cat Word → Tree Cat Word → Prop :=
  ofReadings (.every ∈ ·) (· = .S)

instance (a b : Tree Cat Word) : Decidable (tensedClause a b) :=
  inferInstanceAs (Decidable (ofReadings _ _ a b))

/-- A tensed clause is an island for *every*, and not for *each*. -/
def everyIsland (a b : Tree Cat Word) : Prop :=
  every ∈ determiners a ∧ b.cat = .S

instance (a b : Tree Cat Word) : Decidable (everyIsland a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### The examples -/

/-- A row with its tree and the embedded quantifier. -/
structure Case where
  /-- The article's example. -/
  row : Datum
  /-- The sentence as it is pronounced. -/
  tree : Tree Cat Word
  /-- The embedded quantifier. -/
  mover : Tree Cat Word

/-- The address of the embedded quantifier in the sentence. -/
def Case.address (c : Case) : List ℕ := (c.tree.addressOf? c.mover).getD []

/-- The embedded quantifier can raise to the edge of the sentence, where it outscopes the
subject. -/
def Case.InverseScope (I : Tree Cat Word → Tree Cat Word → Prop) (c : Case) : Prop :=
  c.tree.PassesNoIsland I c.address

instance (I : Tree Cat Word → Tree Cat Word → Prop) [∀ a b, Decidable (I a b)] (c : Case) :
    Decidable (c.InverseScope I) :=
  inferInstanceAs (Decidable (c.tree.PassesNoIsland I c.address))

/-- A word that is not a determiner entry is its string. -/
local instance : Coe String Word := ⟨.inr⟩

/-- *Everyone*, the determiner *every* with *one*. -/
def everyone : Tree Cat Word := ltree% [N [Det ⟨.inl every⟩] [N "one"]]

/-- *Each speaker*. -/
def eachSpeaker : Tree Cat Word := ltree% [N [Det ⟨.inl each⟩] [N "speaker"]]

/-- (18a) *Someone asked [everyone to leave]*. -/
def ex18a : Case where
  row := Examples.ex_18a
  tree := ltree% [S [Pron "someone"] [V [V "asked"] [Neg (everyone) [Neg [Neg "to"] [V "leave"]]]]]
  mover := everyone

/-- (18b) *Someone thought [everyone left]*. -/
def ex18b : Case where
  row := Examples.ex_18b
  tree := ltree% [S [Pron "someone"] [V [V "thought"] [S (everyone) [V "left"]]]]
  mover := everyone

/-- (20b) *A student made sure that [each speaker had a ride]*. -/
def ex20b : Case where
  row := Examples.ex_20b
  tree := ltree% [S [N [Det "a"] [N "student"]]
    [V [V "made"] [Adj "sure"]
      [C [C "that"] [S (eachSpeaker) [V [V "had"] [N [Det "a"] [N "ride"]]]]]]]
  mover := eachSpeaker

/-- The examples with trees. -/
def cases : List Case := [ex18a, ex18b, ex20b]

/-! ### What the theories predict -/

theorem tensedClause_ex18 :
    ex18a.InverseScope tensedClause ∧ ¬ ex18b.InverseScope tensedClause := by
  decide

-- (18b)
theorem inverseScope_bot_ex18b : ex18b.InverseScope ⊥ :=
  passesNoIsland_bot _ _

/-- No island theory that sees a scope-taker through the readings of its determiners keeps
*everyone* in the tensed clause of (18b) and lets *each speaker* out of the tensed clause of
(20b), since *every* and *each* have one reading. -/
theorem not_fits_ofReadings (P : Finset Quantifier.Det.Symbol → Prop) (Q : Cat → Prop) :
    ¬ (¬ ex18b.InverseScope (ofReadings P Q) ∧ ex20b.InverseScope (ofReadings P Q)) := by
  rintro ⟨h18, h20⟩
  refine h18 fun a ha k hk hk0 b hb hI ↦ ?_
  obtain rfl : everyone = a := Option.some.inj ha
  obtain ⟨⟨d, hd, hP⟩, hQ⟩ := hI
  obtain rfl : d = every := by simpa [determiners, everyone] using hd
  have hP' : ∃ d ∈ determiners eachSpeaker, P d.readings :=
    ⟨each, by simp [determiners, eachSpeaker], hP⟩
  have hk3 : k < 3 := hk
  obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
  · obtain rfl := Option.some.inj hb
    exact h20 _ rfl 1 (by decide) (by decide) _ rfl ⟨hP', hQ⟩
  · obtain rfl := Option.some.inj hb
    exact h20 _ rfl 3 (by decide) (by decide) _ rfl ⟨hP', hQ⟩

/-- The theory on which a tensed clause is an island for *every* and not for *each* gives each
example its judgment: the inverse reading is acceptable exactly when the embedded quantifier
passes no island. -/
theorem rows_everyIsland : ∀ c ∈ cases,
    (c.row.readings.lookup "∀ > ∃" = some .acceptable ↔ c.InverseScope everyIsland) := by
  decide

-- (20b)
theorem isLogicalForm_ex20b :
    IsLogicalForm everyIsland ex20b.tree (ex20b.tree.raiseOf 1 eachSpeaker) :=
  (IsLogicalForm.refl _).raiseOf (p := ex20b.address) rfl (by decide) 1

end Barker2027
