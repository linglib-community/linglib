module

public import Linglib.Semantics.Attitudes.Anchor
public import Mathlib.Order.UpperLower.Closure
public import Linglib.Fragments.Buryat.Complementizers
public import Linglib.Fragments.Korean.Complementizers
public import Linglib.Syntax.Category.Verb.ArgumentFrame.Takes
public import Linglib.Data.Examples.Bondarenko2022

/-!
# [bondarenko-2022] — Anatomy of an Attitude

Embedded clauses come in two sorts. A Cont-CP denotes a predicate of
individuals with propositional content, CONT(x) = p ([kratzer-2006],
[moulton-2015]), and projects a ContP whose head is overt in Buryat (*gɘ*
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
(Causer, Theme, About) wants an individual. [angelopoulos-2026] later
attacks this mapping with Greek *oti*-clauses.

The ch. 2 diagnostics and the Buryat clause shapes are checked here against
the thesis's own examples (`Bondarenko2022.Examples`); the per-language
Cont/Comp head assignments are stated over the Buryat and Korean fragment
inventories.
-/

@[expose] public section

namespace Bondarenko2022

open Anchor (comp)
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

/-! ### Equality, subset and existential content -/

variable {W : Type*}

/-- Existential content `CONT(x) ∩ p ≠ ∅` is the overlap semantics that the thesis
rejects in favour of equality (`comp`). Subset semantics is `ContentIndividual.entails`. -/
def ExistentialContent (xc : ContentIndividual W) (p : W → Prop) : Prop :=
  ∃ w, xc.cont w ∧ p w

theorem existentialContent_of_comp {xc : ContentIndividual W} {p : W → Prop}
    (hne : ∃ w, xc.cont w) (h : comp p xc) : ExistentialContent xc p :=
  let ⟨w, hw⟩ := hne; ⟨w, hw, h ▸ hw⟩

theorem eq_of_comp_of_comp {xc : ContentIndividual W} {p q : W → Prop}
    (hp : comp p xc) (hq : comp q xc) : p = q :=
  hp.symm.trans hq

theorem entails_not_functional :
    ¬ ∀ (xc : ContentIndividual Bool) (p q : Bool → Prop),
      xc.entails p → xc.entails q → p = q :=
  fun h => Bool.noConfusion <| (iff_of_eq (congrFun
    (h ⟨(· = true)⟩ (· = true) (fun _ => True) (fun _ hb => hb) (fun _ _ => trivial)) false)).mpr
    trivial

/-! ### Transparency -/

variable {S : Type*}

/-- A clause is referentially transparent at `s` when predicates agreeing at
`s` are interchangeable in it. -/
def ReferentiallyTransparentAt (clause : (S → Prop) → S → Prop) (s : S) : Prop :=
  ∀ p q : S → Prop, (p s ↔ q s) → (clause p s ↔ clause q s)

theorem sit_transparentAt (s : S) : ReferentiallyTransparentAt (fun p s' => p s') s :=
  fun _ _ h => h

theorem comp_not_transparentAt :
    ¬ ∀ (xc : ContentIndividual Bool) (w : Bool),
      ReferentiallyTransparentAt (fun p _ => comp p xc) w :=
  fun h => Bool.noConfusion <| (iff_of_eq (congrFun
    ((h ⟨(· = false)⟩ false (· = false) (fun _ => True) ⟨fun _ => trivial, fun _ => rfl⟩).mp rfl)
    true)).mpr trivial

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

/-! ### Clauses as arguments -/

/-- The two semantic types of an embedded clause (§4.2). -/
inductive SemType where
  | individual
  | predicate
  deriving DecidableEq, Repr

/-- Bare CPs are predicates of situations and nominalized CPs are individuals. -/
inductive ClauseType where
  | predicateOfIndividuals
  | predicateOfSituations
  deriving DecidableEq, Repr

def ClauseType.semanticType : ClauseType → SemType
  | .predicateOfIndividuals => .individual
  | .predicateOfSituations => .predicate

/-- The Θ-heads of §4.4, each demanding an individual. -/
inductive ThetaHead where
  | causer
  | theme
  | aboutAttitude
  deriving DecidableEq, Repr

/-- A clause saturates a Θ-head when its type is the individual type. -/
def saturatesTheta (ct : ClauseType) (_ : ThetaHead) : Prop :=
  ct.semanticType = .individual

instance (ct : ClauseType) (θ : ThetaHead) : Decidable (saturatesTheta ct θ) :=
  inferInstanceAs (Decidable (_ = _))

/-- Bare CPs satisfy no Θ-head (§4.4). -/
theorem bareCP_satisfies_no_theta (θ : ThetaHead) :
    ¬ saturatesTheta .predicateOfSituations θ :=
  SemType.noConfusion

theorem nominalizedCP_satisfies_every_theta (θ : ThetaHead) :
    saturatesTheta .predicateOfIndividuals θ :=
  rfl

/-- Bare CPs compose with the verb's situation argument by Predicate Modification
(§4.5), and nominalized CPs do not. -/
def composesViaPM : ClauseType → Prop
  | .predicateOfIndividuals => False
  | .predicateOfSituations => True

instance : DecidablePred composesViaPM
  | .predicateOfIndividuals => isFalse id
  | .predicateOfSituations => isTrue trivial

/-- Table 1.1's two composition paths. -/
inductive CompositionPath where
  | viaSituation
  | viaDPArgument
  deriving DecidableEq, Repr

/-- The four (clause shape, composition path) combinations. -/
inductive ClauseStructurePath where
  | bareModifier
  | bareArgument
  | nominalizedModifier
  | nominalizedArgument
  deriving DecidableEq, Repr

/-- The transparent syntax–semantics mapping (§1.1.2, ch. 4) is read off the
types, making a cell available when its clause type composes on its path. -/
def transparentSSMapping : ClauseStructurePath → Prop
  | .bareModifier => composesViaPM .predicateOfSituations
  | .bareArgument => ∃ θ, saturatesTheta .predicateOfSituations θ
  | .nominalizedModifier => composesViaPM .predicateOfIndividuals
  | .nominalizedArgument => ∃ θ, saturatesTheta .predicateOfIndividuals θ

theorem not_transparentSSMapping_bareArgument :
    ¬ transparentSSMapping .bareArgument :=
  fun ⟨θ, h⟩ => bareCP_satisfies_no_theta θ h

theorem not_transparentSSMapping_nominalizedModifier :
    ¬ transparentSSMapping .nominalizedModifier :=
  id

theorem transparentSSMapping_diagonal :
    transparentSSMapping .bareModifier ∧ transparentSSMapping .nominalizedArgument :=
  ⟨trivial, .causer, rfl⟩

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

/-- Each frame of *hanaxa* takes exactly one typer, the bare frame *-žA* and the nominalized one
*-Aːša* (§4.4.3). -/
theorem hanaxa_typers :
    (ArgumentFrame.finiteClause.Takes zha ∧ ¬ ArgumentFrame.finiteClause.Takes aasha) ∧
      (nominalizedFrame.Takes aasha ∧ ¬ nominalizedFrame.Takes zha) ∧
      hanaxa.typers complementizers = [aasha, zha] := by
  decide

theorem hanaxa_frame_conditioned_attitude :
    hanaxa.attitudeOn ArgumentFrame.finiteClause = some (.doxastic .nonVeridical) ∧
      hanaxa.attitudeOn nominalizedFrame = some (.doxastic .veridical) := by
  decide

end Bondarenko2022
