module

public import Linglib.Fragments.Guebie.ParticleVerbs
public import Linglib.Phonology.Harmony.Basic
public import Linglib.Phonology.OptimalityTheory.Correspondence.Basic
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Syntax.Minimalist.Linearization.Cyclic
public import Linglib.Syntax.Minimalist.Linearization.SpelloutDomain
public import Linglib.Syntax.Minimalist.Derivation.Remnant
public import Linglib.Data.Examples.SandeClemDabkowski2026
public import Mathlib.Data.List.Sections

/-!
# Sande, Clem and Dąbkowski (2026): Discontinuous vowel harmony in Guébie: Cyclic interleaving of syntax and phonology

This file formalizes Sande, Clem and Dąbkowski's account of discontinuous harmony. In
Guébie verb focus the particle of a particle verb fronts, yet it agrees in [ATR] with the
clause-final verb across the subject, the auxiliary and the object. The paper derives this from
local harmony followed by movement. The vP is spelled out when C merges, and it then holds the
particle and, exactly when an auxiliary keeps the verb from raising to T, the verb; harmony applies
there, and the particle keeps its value when the remnant VP that contains it fronts, as in
Koopman's analysis of predicate clefts.

Both Spell-outs are computed from the two parameters of the analysis, whether T holds an
auxiliary and whether the remnant VP fronts, and each clause's Minimalist derivation spells out
the same two snapshots. Harmony then coincides with the verb's position in v, and under Fox and
Pesetsky's cyclic linearization, which the paper adopts, nothing that ends up between the fronted
particle and the verb shares in it. The Wolof relative clauses described by Sy and by Martinović
show the same profile, the trigger moving instead of the target.

## Implementation notes

* The vP Spell-out is the vP's head and complement, the stage before the subject merges; the
  object shifts to the edge of the whole vP, standing for the VP-external position of footnote 7.
  The rows omit the tone numerals.
* The tableau ranks Sande's two constraints, ATRHARM being Agreement by Projection in Hansson's
  sense, and holds the root fixed as root control requires; with the root free the two constraints
  alone would change the root (`optimal_rootFree`).
* The verb adjoins to the head-final v by Internal Merge on the right, which merges it with the
  whole vP rather than forming a complex head.

## TODO

* The verb-doubling orders of plain verb focus, the island and successive-cyclicity diagnostics of
  §3, and the Atchan nasal harmony the paper leaves open.

## References

* [sande-clem-dabkowski-2026]
* [koopman-1997]
* [fox-pesetsky-2005]
* [sande-2019]
* [hansson-2014]
* [sy-2005]
* [martinovic-2019]
-/

@[expose] public section

namespace SandeClemDabkowski2026

open List Minimalist Linearization OptimalityTheory Guebie

/-! ### Predicate fronting and its two Spell-outs -/

/-- A terminal is an overt word of a particle-verb clause. -/
inductive Terminal
  | particle
  | subject
  | aux
  | verb
  | object
  deriving DecidableEq, Repr, Fintype

/-- A clause is fixed by the two parameters of predicate fronting, whether an auxiliary in T stops
the verb in v and whether focus fronts the remnant VP to Spec,CP. -/
structure Clause where
  hasAux : Bool
  fronted : Bool
  deriving DecidableEq, Repr, Fintype

/-- The remnant VP holds only the particle, the object having shifted out and the verb having
raised to v. -/
def remnantVP : List Terminal := [.particle]

namespace Clause

variable (c : Clause)

/-- The verb sits head-finally in v when an auxiliary in T stops it there. -/
def verbInV : List Terminal := if c.hasAux then [.verb] else []

/-- The vP Spell-out (45), (48) holds the phase head v and its complement when C merges. -/
def vP : List Terminal := remnantVP ++ c.verbInV

/-- The subject in Spec,TP precedes the auxiliary or raised verb in T and the shifted object. -/
def middle : List Terminal := [.subject, if c.hasAux then .aux else .verb, .object]

/-- In the CP Spell-out the remnant VP stays between the object and v, or fronts to Spec,CP. -/
def cP : List Terminal :=
  if c.fronted then remnantVP ++ c.middle ++ c.verbInV else c.middle ++ remnantVP ++ c.verbInV

/-- A clause is spelled out at vP and at CP. -/
def phases : List (List Terminal) := [c.vP, c.cP]

theorem vP_sublist_cP : c.vP <+ c.cP := by
  grind [vP, cP]

theorem cP_nodup : c.cP.Nodup := by
  obtain ⟨_ | _, _ | _⟩ := c <;> decide

-- §6.2
theorem consistent : Consistent c.phases :=
  consistent_of_forall_sublist (by simpa [phases] using c.vP_sublist_cP) c.cP_nodup

/-- Harmony applies when the verb is spelled out with the particle (§6.1). -/
def Harmony : Prop := Terminal.verb ∈ c.vP

instance : Decidable c.Harmony := inferInstanceAs (Decidable (_ ∈ _))

/-- Harmony applies exactly when an auxiliary keeps the verb in v, fronted or not (44). -/
theorem harmony_iff_hasAux : c.Harmony ↔ c.hasAux = true := by
  grind [Harmony, vP, verbInV, remnantVP]

theorem isInfix_vP (h : c.Harmony) : [.particle, .verb] <:+: c.vP := by
  grind [Harmony, vP, verbInV, remnantVP]

/-- Material between the particle and the verb on the surface lies outside the vP, so vP harmony
does not reach it (41). -/
theorem notMem_vP_of_between (h : c.Harmony) {x : Terminal} (h₁ : [.particle, x] <+ c.cP)
    (h₂ : [x, .verb] <+ c.cP) : x ∉ c.vP :=
  c.consistent.notMem_of_isInfix (by simp [phases]) (by simp [phases]) (c.isInfix_vP h) h₁ h₂

end Clause

/-! ### Discontinuous harmony (§7) -/

/-- Harmony is discontinuous when its trigger and target are adjacent at one Spell-out and
separated at another, in a derivation that linearizes. -/
structure Discontinuous {α : Type*} (phases : List (List α)) (a b : α) : Prop where
  consistent : Consistent phases
  adjacent : ∃ p ∈ phases, [a, b] <:+: p
  separated : ∃ q ∈ phases, ∃ x, [a, x] <+ q ∧ [x, b] <+ q

-- §7
theorem Discontinuous.exists_notMem {α : Type*} {phases : List (List α)} {a b : α}
    (h : Discontinuous phases a b) :
    ∃ p ∈ phases, [a, b] <:+: p ∧ ∃ q ∈ phases, ∃ x ∈ q, x ∉ p := by
  obtain ⟨p, hp, hab⟩ := h.adjacent
  obtain ⟨q, hq, x, h₁, h₂⟩ := h.separated
  exact ⟨p, hp, hab, q, hq, x, h₁.subset (by simp), h.consistent.notMem_of_isInfix hp hq hab h₁ h₂⟩

theorem discontinuous_partSAuxOV :
    Discontinuous (Clause.mk true true).phases .particle .verb where
  consistent := Clause.consistent _
  adjacent := ⟨(Clause.mk true true).vP, by simp [Clause.phases], Clause.isInfix_vP _ (by decide)⟩
  separated := ⟨(Clause.mk true true).cP, by simp [Clause.phases], .subject, by decide, by decide⟩

/-! ### Harmony within the vP Spell-out -/

/-- Every vowel takes part in [ATR] harmony (§5.1). -/
def atrPattern : Phonology.Harmony.Pattern Phonology.Segment Bool where
  value v := some (atr v)
  participation _ := .participating

/-- ATRHARM (47) is an Agreement by Projection constraint, violated once by an output in which a
vowel precedes a vowel of the other [ATR] value on the tier of vowels. -/
def atrHarm : Constraint (List Phonology.Segment) := .binary fun out ↦ ¬ atrPattern.Harmonic out

/-- IDENT-IO(ATR) (46) is violated once by each vowel whose [ATR] value departs from its
input. -/
def identIO (input : List Phonology.Segment) : Constraint (List Phonology.Segment) := fun out ↦
  (Correspondence.parallel input out).identViolFeature atr .lhs .rhs

/-- A revaluation of a string of vowels gives each vowel either [ATR] value. -/
def revaluations (l : List Phonology.Segment) : List (List Phonology.Segment) :=
  (l.map fun v ↦ [withATR v true, withATR v false]).sections

/-- The vP tableau ranks ATRHARM above IDENT-IO(ATR) over every revaluation of the particle,
followed by the root vowels the vP Spell-out holds. -/
def vPTableau (part : Morpheme) (root : List Phonology.Segment) :
    Tableau (List Phonology.Segment) 2 :=
  Tableau.ofList ((revaluations part.vowels).map (· ++ root)).toFinset
    [atrHarm, identIO (part.vowels ++ root)]

/-- Over the particle verbs of (10)–(12), the particle takes the root's value when the root is in
the vP Spell-out and stays faithful otherwise. -/
theorem vPTableau_optimal : ∀ pv ∈ particleVerbs,
    (vPTableau pv.particle pv.verb.vowels).optimal =
        {pv.particle.vowels.map (withATR · pv.verb.atr) ++ pv.verb.vowels} ∧
      (vPTableau pv.particle []).optimal = {pv.particle.vowels} := by
  decide +kernel

namespace Clause

variable (c : Clause) (part verb : Morpheme)

/-- The vP Spell-out holds the verb's vowels under harmony and no root vowels otherwise. -/
def rootVowels : List Phonology.Segment := if c.Harmony then verb.vowels else []

/-- The particle surfaces with the root's [ATR] value under harmony and with its own otherwise
((12), (13)). -/
def particleATR : Bool := if c.Harmony then verb.atr else part.atr

/-- In every clause the vP tableau gives each particle vowel the value harmony assigns. -/
theorem vPTableau_optimal {pv : ParticleVerb} (hpv : pv ∈ particleVerbs) :
    (vPTableau pv.particle (c.rootVowels pv.verb)).optimal =
      {pv.particle.vowels.map (withATR · (c.particleATR pv.particle pv.verb)) ++
        c.rootVowels pv.verb} := by
  obtain ⟨h₁, h₂⟩ := SandeClemDabkowski2026.vPTableau_optimal pv hpv
  unfold rootVowels particleATR
  split
  · exact h₁
  · rw [h₂, ((particleVerbs_ATRUniform pv hpv).1).map_withATR, append_nil]

end Clause

/-- This tableau ranks ATRHARM above IDENT-IO(ATR) over every revaluation of an input, the root's
vowels included. -/
def rootFreeTableau (input : List Phonology.Segment) : Tableau (List Phonology.Segment) 2 :=
  Tableau.ofList (revaluations input).toFinset [atrHarm, identIO input]

-- (12a), (10e)
theorem optimal_rootFree :
    (rootFreeTableau (jOkU.vowels ++ ni.vowels)).optimal = {[openO, upsilon, smallCapitalI]} ∧
      (rootFreeTableau (mE.vowels ++ nu.vowels)).optimal = {[e, u], [epsilon, upsilon]} := by
  decide

/-! ### The derivations -/


/-- Each terminal spells out its own lexical item. -/
def Terminal.token : Terminal → LexicalItem.Token
  | .particle => ⟨.of .P [], 1⟩
  | .subject => ⟨.of .D [], 2⟩
  | .aux => ⟨.of .T [], 3⟩
  | .verb => ⟨.of .V [], 4⟩
  | .object => ⟨.of .D [], 5⟩

/-- A lexical item spells out at most one terminal. -/
def Terminal.ofToken? (tok : LexicalItem.Token) : Option Terminal :=
  [Terminal.particle, .subject, .aux, .verb, .object].find? (·.token = tok)

/-- The light verb v is silent. -/
def v₀ : LexicalItem.Token := ⟨.of .v [], 6⟩

/-- The T a raised verb adjoins to is silent. -/
def T₀ : LexicalItem.Token := ⟨.of .T [], 7⟩

/-- The complementizer C is silent. -/
def C₀ : LexicalItem.Token := ⟨.of .C [], 8⟩

/-- The remnant VP that fronts holds the particle between the traces of the object and the
verb. -/
def remnant : LinearizedSyntacticObject :=
  {.traceOf Terminal.object.token, {.leaf Terminal.particle.token, .traceOf Terminal.verb.token}}


/-- The head and complement of the vP are built as in (31)–(34). The particle and the object
merge with the verb in a head-final VP, v merges on its right, and the verb adjoins to v on the
right. -/
def vSteps : List Step :=
  [.em .left Terminal.particle.token, .em .left Terminal.object.token,
    .em .right v₀, .im Terminal.verb.token .right]

/-- The subject merges in Spec,vP and the object shifts above the vP. -/
def edgeSteps : List Step :=
  [.em .left Terminal.subject.token, .im Terminal.object.token]

/-- The subject raises to Spec,TP and C merges. -/
def cSteps : List Step := [.im Terminal.subject.token, .em .left C₀]

/-- A clause is spelled out twice: the head and complement of its vP when C merges
(l.1255–1260), and its CP at the end of the derivation. -/
def vPSchedule (d : Derivation) : List (ℕ × ℕ) :=
  [(vSteps.length, (d.mergeStage? C₀).getD d.length), (d.length, d.length)]

namespace Clause

variable (c : Clause)

/-- Either the auxiliary merges in T, or T merges and the verb raises to it. -/
def tSteps : List Step :=
  if c.hasAux then [.em .left Terminal.aux.token]
  else [.em .left T₀, .im Terminal.verb.token]

/-- Focus fronts the remnant VP to Spec,CP. -/
def focusSteps : List Step := if c.fronted then [.im remnant.toSyntacticObject] else []

/-- A clause's derivation starts from the verb. -/
def derivation : Derivation :=
  ⟨Terminal.verb.token, vSteps ++ edgeSteps ++ c.tSteps ++ cSteps ++ c.focusSteps⟩

/-- The derivation's Spell-outs are the vP and CP snapshots. -/
theorem spellouts_eq_phases :
    (vPSchedule c.derivation).map (fun p ↦ (c.derivation.spellout p.1 p.2).filterMap
      Terminal.ofToken?) = c.phases := by
  obtain ⟨_ | _, _ | _⟩ := c <;> decide

theorem linearizes : c.derivation.Linearizes (vPSchedule c.derivation) := by
  obtain ⟨_ | _, _ | _⟩ := c <;> decide +kernel

-- §4.1
theorem isRemnantStep_derivation (h : c.fronted = true) :
    c.derivation.IsRemnantStep (c.derivation.length - 1) := by
  obtain ⟨_ | _, _ | _⟩ := c <;> simp at h <;> decide

end Clause

/-- In this variant of the fronted clause with an auxiliary, the object shifts only after C
merges. -/
def lateShift : Derivation :=
  ⟨Terminal.verb.token, vSteps ++ edgeSteps.take 1 ++ (Clause.mk true true).tSteps ++ cSteps ++
    edgeSteps.drop 1 ++ (Clause.mk true true).focusSteps⟩

-- §6.2
theorem not_linearizes_lateShift : ¬ lateShift.Linearizes (vPSchedule lateShift) := by
  decide

/-! ### The Guébie examples -/

/-- `rowsIn lang` lists the rows in the language `lang`. -/
def rowsIn (lang : String) : List Datum := Examples.all.filter (·.language == lang)

def patterns : List (String × List Terminal) :=
  [("S Aux O Part V", [.subject, .aux, .object, .particle, .verb]),
    ("S V O Part", [.subject, .verb, .object, .particle]),
    ("Part S V O", [.particle, .subject, .verb, .object]),
    ("Part S Aux O V", [.particle, .subject, .aux, .object, .verb]),
    ("S Part V O", [.subject, .particle, .verb, .object]),
    ("Part V S V O", [.particle, .verb, .subject, .verb, .object]),
    ("V S V O Part", [.verb, .subject, .verb, .object, .particle]),
    ("V S O Part", [.verb, .subject, .object, .particle]),
    ("Part S V O Part", [.particle, .subject, .verb, .object, .particle])]

def verbs : List (String × Morpheme) := [("ni", ni), ("ngwOsa", ngwOsa)]

def atrs : List (String × Bool) := [("plus", true), ("minus", false)]

theorem order_rows :
    ∀ x ∈ rowsIn "gabo1234", ∀ p ∈ x.parse? "pattern" patterns,
      (x.judgment = .acceptable ↔ ∃ c : Clause, c.cP = p) := by
  decide +kernel

theorem harmony_rows :
    ∀ x ∈ rowsIn "gabo1234", ∀ p ∈ x.parse? "pattern" patterns, ∀ v ∈ x.parse? "verb" verbs,
      ∀ c : Clause, c.cP = p →
        (∀ a ∈ x.parse? "particleATR" atrs, a = c.particleATR jOkU v) ∧
          ∀ i ∈ x.parse? "interveningATR" atrs, i ≠ c.particleATR jOkU v := by
  decide +kernel

/-! ### Wolof relative clauses (§7) -/

/-- A nominal is an overt word of a Wolof noun phrase. -/
inductive Nominal
  | noun
  | rel
  | stative
  | dem
  deriving DecidableEq, Repr

/-- The DP Spell-out (49) holds the head noun and its distal demonstrative. -/
def dP : List Nominal := [.noun, .dem]

/-- A relative clause (50) has the head noun at its left edge, then the relativizer, the stative
verb and the demonstrative. -/
def relClause : List Nominal := [.noun, .rel, .stative, .dem]

def shapes : List (String × List Nominal) := [("localDP", dP), ("relClause", relClause)]

theorem discontinuous_relClause : Discontinuous [dP, relClause] .noun .dem where
  consistent := by decide
  adjacent := ⟨dP, by simp, by simp [dP]⟩
  separated := ⟨relClause, by simp, .stative, by decide, by decide⟩

theorem wolof_rows :
    ∀ x ∈ rowsIn "nucl1347", (∀ s ∈ x.parse? "shape" shapes, Consistent [dP, s]) ∧
      ∀ h ∈ x.parse? "headATR" atrs, ∀ d ∈ x.parse? "demATR" atrs, d = h := by
  decide +kernel

end SandeClemDabkowski2026
