module

public import Mathlib.Order.UpperLower.Closure
public import Linglib.Fragments.Buryat.Complementizers
public import Linglib.Fragments.Korean.Complementizers
public import Linglib.Syntax.Category.Verb.ArgumentFrame.Takes
public import Linglib.Data.Examples.Bondarenko2022
public import Linglib.Semantics.Composition.Interpret
public import Linglib.Semantics.Composition.Rules
public import Linglib.Semantics.Composition.Sorts
public import Linglib.Semantics.Modality.Content

/-!
# [bondarenko-2022] — Anatomy of an Attitude

Embedded clauses come in two sorts. A Cont-CP denotes a predicate of
individuals with propositional content ([kratzer-2006]), those with
CONT(x) = p ([moulton-2015]), and projects a ContP whose head is overt in Buryat (*gɘ*
'say') and Korean (*-ta*) and null in English and Russian; a Sit-CP
denotes a predicate of situations exemplifying p ([kratzer-1989]) and
lacks that layer. Content nouns take truth predicates and reject
occurrence predicates, situation nouns the reverse, and a Sit-CP is
referentially transparent where a Cont-CP is opaque. Content is fixed by
equality rather than subset or overlap, which makes CONT a function and
rules out clausal conjunction under one content individual
([bassi-bondarenko-2021]).

With verbs, a clause composes either through the verb's situation
argument by Predicate Modification or through a DP argument by Functional
Application, and the thesis's mapping claim is that bare clauses take only
the first path and nominalized clauses only the second: a bare CP is a
predicate of situations, a nominalized CP an individual, and every Θ-head
(Causer, Theme, About) wants an individual. The four combinations are trees
interpreted by Functional Application and Predicate Modification: the two
on the diagonal have one meaning each (`meanings_bareModifier`,
`meanings_nominalizedArgument`) and the other two have no derivation
(`derive_bareArgument`, `derive_nominalizedModifier`). [angelopoulos-2026]
later attacks this mapping with Greek *oti*-clauses.

The ch. 2 diagnostics and the Buryat clause shapes are checked here against
the thesis's own examples (`Bondarenko2022.Examples`); the per-language
Cont/Comp head assignments are stated over the Buryat and Korean fragment
inventories.

## Implementation notes

* Buryat *hanaxa* 'think' quantifies over doxastic alternatives in both of its frames, which
  differ in opacity and factivity; its nominalized reading, 'remember', is factive through the
  presupposition that the event its complement describes started before the thinking (§4.4.3),
  which the fragment records on the nominalized frame. The reading is veridical and the bare-CP
  reading is not (`hanaxa_isVeridical_nominalized`), so by `Doxastic.isVeridical_forall_iff`
  every denotation of the nominalized reading is veridical and some denotation of the bare-CP
  reading is not.

## References

* [bondarenko-2022]
* [kratzer-2006]
* [moulton-2015]
* [kratzer-1989]
* [bassi-bondarenko-2021]
-/

@[expose] public section

namespace Bondarenko2022

open Buryat

/-! ### Nominal sorts -/

/-- The two sorts of clause-taking noun (§2.2), content nouns (*idea*,
*claim*, *rumor*) and situation nouns (*situation*, *event*, *case*). -/
inductive NominalSort where
  | content
  | situation
  deriving DecidableEq, Fintype, Repr

/-- Combines with 'true' / 'false' / 'mistaken'. -/
def NominalSort.truthEvaluable : NominalSort → Prop
  | .content => True
  | .situation => False

/-- Combines with 'occur' / 'happen' / 'notice'. -/
def NominalSort.occurrenceCompatible : NominalSort → Prop
  | .content => False
  | .situation => True

instance : DecidablePred NominalSort.truthEvaluable
  | .content => isTrue trivial
  | .situation => isFalse id

instance : DecidablePred NominalSort.occurrenceCompatible
  | .content => isFalse id
  | .situation => isTrue trivial

/-- The predicate a co-occurrence example tests the noun against. -/
inductive Diagnostic where
  | truth
  | occurrence
  deriving DecidableEq, Repr

def parseSort : String → Option NominalSort
  | "content" => some .content
  | "situation" => some .situation
  | _ => none

def parseDiagnostic : String → Option Diagnostic
  | "truth-predicates" => some .truth
  | "occurrence-predicates" | "situation-only-predicate-notice" => some .occurrence
  | _ => none

/-- A noun of a given sort under a diagnostic predicate, with its
judgment. -/
structure CooccurrenceDatum where
  sort : NominalSort
  diagnostic : Diagnostic
  acceptable : Bool
  deriving DecidableEq, Repr

def cooccurrenceDatum (e : Datum) : Option CooccurrenceDatum := do
  let s ← parseSort (← e.paperFeatures.lookup "nounSort")
  let d ← parseDiagnostic (← e.paperFeatures.lookup "diagnostic")
  some ⟨s, d, e.judgment == Judgment.acceptable⟩

/-- The ch. 2 co-occurrence examples. -/
def cooccurrenceData : List CooccurrenceDatum := Examples.all.filterMap cooccurrenceDatum

/-- Which predicate the datum's sort should accept. -/
def Diagnostic.accepts : Diagnostic → NominalSort → Prop
  | .truth, s => s.truthEvaluable
  | .occurrence, s => s.occurrenceCompatible

instance : ∀ (d : Diagnostic) (s : NominalSort), Decidable (d.accepts s)
  | .truth, s => inferInstanceAs (Decidable s.truthEvaluable)
  | .occurrence, s => inferInstanceAs (Decidable s.occurrenceCompatible)

theorem sort_predicts_cooccurrence :
    ∀ d ∈ cooccurrenceData, d.acceptable = true ↔ d.diagnostic.accepts d.sort := by
  decide

/-! ### Equality, subset and existential content

The content function is partial: it is defined for ideas, beliefs and claims and undefined for
other individuals. On the equality semantics (7) a clause with proposition `p` holds of `x` when
`p ∈ cont x`. On the subset semantics (10) of [kratzer-2006], which the thesis rejects, and on
the existential semantics (15), it holds when `p` is necessary, or possible, along
`Modality.compatible cont`. The law (11), that the subset semantics distributes over conjunction,
is `ModalLogic.box_and`, both are monotone in `p` (`ModalLogic.box_mono`,
`ModalLogic.diamond_mono`), and a clause that holds on the equality semantics holds on the other
two, on the existential one where its proposition is consistent
(`Modality.box_compatible_of_mem`, `Modality.diamond_compatible_of_mem`). -/

section Content

open Modality ModalLogic

variable {X W : Type*} {cont : X → Option (Set W)} {x : X} {p q : Set W}

/-- On the equality semantics two clauses that hold of one individual have the same proposition,
so clauses cannot stack or conjoin under one content individual. -/
theorem eq_of_mem_cont (hp : p ∈ cont x) (hq : q ∈ cont x) : p = q :=
  Option.mem_unique hp hq

theorem mem_cont_iff_eq (hp : p ∈ cont x) : q ∈ cont x ↔ p = q :=
  ⟨eq_of_mem_cont hp, fun h ↦ h ▸ hp⟩

theorem box_compatible_not_functional :
    ¬ ∀ (cont : Unit → Option (Set Bool)) (p q : Set Bool),
      □[compatible cont] (· ∈ p) () → □[compatible cont] (· ∈ q) () → p = q :=
  fun h ↦ Bool.false_ne_true
    (h (fun _ ↦ some {true}) {true} Set.univ (box_compatible_of_mem rfl) (fun _ _ ↦ trivial) ▸
      Set.mem_univ false : false ∈ ({true} : Set Bool))

end Content

/-! ### Transparency -/

variable {S : Type*}

/-- A clause is referentially transparent at `s` when propositions agreeing at `s` are
interchangeable in it. -/
def ReferentiallyTransparentAt (clause : Set S → S → Prop) (s : S) : Prop :=
  ∀ p q : Set S, (s ∈ p ↔ s ∈ q) → (clause p s ↔ clause q s)

theorem sit_transparentAt (s : S) : ReferentiallyTransparentAt (fun p s' ↦ s' ∈ p) s :=
  fun _ _ h ↦ h

theorem mem_cont_not_transparentAt :
    ¬ ∀ (cont : Unit → Option (Set Bool)) (w : Bool),
      ReferentiallyTransparentAt (fun p _ ↦ p ∈ cont ()) w :=
  fun h ↦ Bool.false_ne_true
    (Option.some.inj ((h (fun _ ↦ some {false}) false {false} Set.univ
      ⟨fun _ ↦ trivial, fun _ ↦ rfl⟩).mp rfl) ▸ Set.mem_univ true :
        true ∈ ({false} : Set Bool)).symm

/-- A substitution triple's conclusion, with the sort of the embedded
clause and whether the thesis judges the inference valid. -/
structure SubstitutionDatum where
  sort : NominalSort
  valid : Bool
  deriving DecidableEq, Repr

def parseValidity : String → Option Bool
  | "valid" => some true
  | "invalid" => some false
  | _ => none

def substitutionDatum (e : Datum) : Option SubstitutionDatum := do
  let s ← parseSort (← e.paperFeatures.lookup "nounSort")
  let v ← parseValidity (← e.paperFeatures.lookup "inference")
  some ⟨s, v⟩

/-- The substitution-test conclusions of §2.2.3. -/
def substitutionData : List SubstitutionDatum := Examples.all.filterMap substitutionDatum

theorem substitution_valid_iff_situation :
    ∀ d ∈ substitutionData, d.valid = true ↔ d.sort = .situation := by
  decide

/-! ### Clauses as modifiers and as arguments

A verb denotes a predicate of situations, and a Θ-head (62) takes the verb's predicate and an
individual. A bare clause denotes a predicate of situations and a nominalized clause an
individual, so the two are never integrated with the verb in the same way: the types leave each
one path. -/

section Composition

open Interpreter PhraseStructure ManySorted

/-- The Θ-heads of §4.4. -/
inductive ThetaHead where
  | causer
  | theme
  | aboutAttitude
  deriving DecidableEq, Repr

/-- The words of the four combinations, by semantic type. -/
inductive Item : Ty Base → Type
  /-- A verb, a predicate of situations. -/
  | verb : Item (.s ⇒ .t)
  /-- A Θ-head, (62). -/
  | theta (θ : ThetaHead) : Item ((.s ⇒ .t) ⇒ .e ⇒ .s ⇒ .t)
  /-- A bare clause, a predicate of situations. -/
  | bareCP : Item (.s ⇒ .t)
  /-- A nominalized clause, an individual. -/
  | nominalizedCP : Item .e

/-- Functional Application and Predicate Modification. -/
abbrev grammar : Language (Ty Base) := application.sum predicateModification

variable {E S : Type} (verb : S → Prop) (role : ThetaHead → S → E) (clause : S → Prop) (x : E)

/-- The denotations of the words: a Θ-head (62) holds of a predicate of situations, an individual
and a situation of the predicate in which the individual has the head's role. -/
def Item.val : {a : Ty Base} → Item a → a.Dom (Base.Dom E S)
  | _, .verb => verb
  | _, .theta θ => fun p y s ↦ p s ∧ role θ s = y
  | _, .bareCP => clause
  | _, .nominalizedCP => x

/-- The leaf of a word. -/
def leaf {a : Ty Base} (i : Item a) : Tree Unit (Σ a, Item a) := .leaf ⟨a, i⟩

/-- A bare clause with a verb. -/
def bareModifier : Tree Unit (Σ a, Item a) := .bin (leaf .bareCP) (leaf .verb)

/-- A nominalized clause with a verb and its Θ-head, as in (61). -/
def nominalizedArgument (θ : ThetaHead) : Tree Unit (Σ a, Item a) :=
  .bin (.bin (leaf .verb) (leaf (.theta θ))) (leaf .nominalizedCP)

/-- A bare clause in the position of the argument of a Θ-head. -/
def bareArgument (θ : ThetaHead) : Tree Unit (Σ a, Item a) :=
  .bin (.bin (leaf .verb) (leaf (.theta θ))) (leaf .bareCP)

/-- A nominalized clause as the sister of a verb. -/
def nominalizedModifier : Tree Unit (Σ a, Item a) := .bin (leaf .nominalizedCP) (leaf .verb)

/-- The meanings of a tree. -/
def meanings (t : Tree Unit (Σ a, Item a)) :
    List (Σ a : Ty Base, (ℕ → E) → a.Dom (Base.Dom E S)) :=
  t.interpret grammar (Base.Dom E S) (fun _ ↦ .e) (fun i _ ↦ Item.val verb role clause x i)
    fun w ↦ [w]

-- §4.5
theorem meanings_bareModifier :
    meanings verb role clause x bareModifier = [⟨.s ⇒ .t, fun _ s ↦ clause s ∧ verb s⟩] :=
  rfl

-- (61)
theorem meanings_nominalizedArgument (θ : ThetaHead) :
    meanings verb role clause x (nominalizedArgument θ) =
      [⟨.s ⇒ .t, fun _ s ↦ verb s ∧ role θ s = x⟩] := by
  cases θ <;> rfl

/-- A bare clause saturates no Θ-head: the head with its verb wants an individual, and no rule
applies to it and a predicate of situations. -/
theorem derive_bareArgument (θ : ThetaHead) :
    (bareArgument θ).derive grammar (fun _ ↦ .e) (W := Item) (fun w ↦ [w]) = [] := by
  cases θ <;> rfl

/-- A nominalized clause does not modify a verb: no rule applies to an individual and a predicate
of situations. -/
theorem derive_nominalizedModifier :
    nominalizedModifier.derive grammar (fun _ ↦ .e) (W := Item) (fun w ↦ [w]) = [] :=
  rfl

end Composition

/-! ### The Comp head -/

/-- The Comp head (§2.3 ex. 151) holds of `x` at `s` when `x` is part of the evaluation
situation and exactly verifies `p`. -/
def compHead [Preorder S] (p : Set S) (x s : S) : Prop :=
  x ≤ s ∧ x ∈ p

theorem mem_upperClosure_of_compHead [Preorder S] {p : Set S} {x s : S}
    (h : compHead p x s) : s ∈ upperClosure p :=
  mem_upperClosure.2 ⟨x, h.2, h.1⟩

/-! ### Cont exponence -/

/-- A Cont-exponence analysis of a clause-typing inventory (ch. 4) names the
morpheme, if any, that overtly expones Cont. -/
structure ContAnalysis where
  inventory : List Complementizer
  contExponent : Option Complementizer
  contExponent_mem : ∀ c ∈ contExponent, c ∈ inventory

/-- A Cont analysis with the licenser-conditioned Comp allomorphy. -/
structure ContCompAnalysis extends ContAnalysis where
  compAllomorph : Complementizer.Licenser → Complementizer
  compAllomorph_mem : ∀ l, compAllomorph l ∈ inventory
  licenser_compAllomorph : ∀ l, (compAllomorph l).licenser = some l
  cover : ∀ c ∈ inventory, c ∈ contExponent ∨ ∃ l, compAllomorph l = c

/-- In Buryat (§4.3.1 ex. 33) *gɘ* expones Cont, participial *-Aːša* is the
Comp allomorph next to nouns, and converbial *-žA* is the one next to verbs. -/
def buryatAnalysis : ContCompAnalysis where
  inventory := complementizers
  contExponent := some ge
  contExponent_mem := by decide
  compAllomorph
    | .nominal => aasha
    | .verbal => zha
  compAllomorph_mem := by decide
  licenser_compAllomorph := by decide
  cover := by decide

/-- In Korean (§4.3.2 ex. 46) *-ta* expones Cont, and adnominal *-nun* and
adverbal *-ko* are the Comp allomorphs. -/
def koreanAnalysis : ContCompAnalysis where
  inventory := Korean.Complementizers.complementizers
  contExponent := some Korean.Complementizers.ta
  contExponent_mem := by decide
  compAllomorph
    | .nominal => Korean.Complementizers.nun
    | .verbal => Korean.Complementizers.ko
  compAllomorph_mem := by decide
  licenser_compAllomorph := by decide
  cover := by decide

theorem mem_buryatContExponent_iff :
    ∀ c ∈ complementizers,
      (c ∈ buryatAnalysis.contExponent ↔ ∀ m ∈ c.morphs, m.kind = .root) := by
  decide

/-- The clause-typers of a Buryat clause shape (§4.3.1 ex. 30–32). -/
def parseShape : String → Option (List Complementizer)
  | "bare gɘ-žɘ clause" => some [ge, zha]
  | "nominalized participial clause" => some [aasha]
  | "nominalized gɘ-participial clause" => some [ge, aasha]
  | _ => none

def parseClauseSort : String → Option NominalSort
  | "Cont-CP" => some .content
  | "Sit-CP" => some .situation
  | _ => none

/-- A Buryat embedded clause, with its typers and the sort it denotes. -/
structure ShapeDatum where
  typers : List Complementizer
  sort : NominalSort
  deriving DecidableEq, Repr

def shapeDatum (e : Datum) : Option ShapeDatum := do
  let ts ← parseShape (← e.paperFeatures.lookup "shape")
  let s ← parseClauseSort (← e.paperFeatures.lookup "clauseType")
  some ⟨ts, s⟩

/-- The Buryat clause shapes of §4.3.1. -/
def shapeData : List ShapeDatum := Examples.all.filterMap shapeDatum

theorem content_iff_contExponent_mem :
    ∀ d ∈ shapeData, ∀ c ∈ buryatAnalysis.contExponent, (d.sort = .content ↔ c ∈ d.typers) := by
  decide

-- §4.4.3
theorem hanaxa_typers :
    (ArgumentFrame.finiteClause.Takes zha ∧ ¬ ArgumentFrame.finiteClause.Takes aasha) ∧
      (nominalizedFrame.Takes aasha ∧ ¬ nominalizedFrame.Takes zha) ∧
      hanaxa.typers complementizers = [aasha, zha] := by
  decide

/-- *hanaxa* has one attitude in both of its frames, and is veridical with a nominalized
complement, 'remember', and not with a bare CP, 'think': the frames differ in factivity alone
(§4.4.3). -/
theorem hanaxa_isVeridical_nominalized :
    hanaxa.attitudeOn ArgumentFrame.finiteClause = hanaxa.attitudeOn nominalizedFrame ∧
      (∀ a ∈ hanaxa.attitudeOn nominalizedFrame,
        a.IsVeridical (hanaxa.factivityOn nominalizedFrame)) ∧
      ∀ a ∈ hanaxa.attitudeOn ArgumentFrame.finiteClause,
        ¬ a.IsVeridical (hanaxa.factivityOn ArgumentFrame.finiteClause) := by
  decide

end Bondarenko2022
