module

public import Linglib.Data.Examples.Collins2005
public import Linglib.Data.Examples.Gloss
public import Linglib.Syntax.Binding.Basic
public import Linglib.Syntax.Minimalist.Probe.SyntacticObject
public import Linglib.Syntax.Minimalist.Locality.Freezing
public import Linglib.Syntax.Minimalist.Derivation.Remnant
public import Linglib.Syntax.Minimalist.Derivation.Smuggling

/-!
# Collins 2005: a smuggling approach to the passive in English

The external argument of the passive is Merged in Spec,vP, as in the active, and the participle
phrase PartP moves to the specifier of a VoiceP headed by *by*, carrying the object past the
external argument so that Infl can attract it. This file builds the passive and its rivals, head
movement of the verb and no movement, as derivations, and checks the paper's examples against the
sentences they pronounce, against Infl's probe search, and against the binding conditions of
`Syntax/Binding` evaluated at the surface or at some stage of the derivation.

## Main statements

* `Collins2005.active_shares_vP`: the active and the passive share the derivation through vP (§2).
* `Collins2005.ex9_converges_iff`: only PartP movement lets Infl find the object (§5).
* `Collins2005.order_rows`: a passive is acceptable when a converging derivation pronounces it.
* `Collins2005.licensing_rows`: the c-command and binding judgments of (10) and (60)–(91).
* `Collins2005.fitsAt_rExpression_iff`: (76a) puts Principle C at the surface (§9.2).

## Implementation notes

* Part and the host X of (58) are silent `Cat.Asp` heads, V-to-Part raising (8) is not modelled,
  a PP is one leaf, and head movement re-Merges the verb at the root in place of (13).
* A PP may leave PartP (58) and a particle or a stranded preposition may not (50)–(51).
* A dependency licensed only by reconstructing PartP is marked but not starred, the `??` of (72a)
  and the `?` of (75) alike (§9.2); NPIs and *the other* do not reconstruct, for which the paper
  gives no reason. Principle B omits the local-domain and Case clauses of (83).

## TODO

* The double-object, ECM, CP, extraction and quantifier data ((53)–(57), (77), (81), (88)–(90),
  (94)–(98)), the passives of Kiswahili and Japanese, and Case checking by Voice (31)–(32).

## References

* [C. Collins, *A Smuggling Approach to the Passive in English* (2005)][collins-2005]
* [A. Barss and H. Lasnik, *A Note on Anaphora and Double Objects* (1986)][barss-lasnik-1986]
* [G. Müller, *Incomplete Category Fronting* (1998)][muller-1998]
* [J. Sabel, *Restrukturierung und Lokalität* (1996)][sabel-1996]
-/

@[expose] public section

namespace Collins2005

open Minimalist SyntacticObject

/-! ### The passive and its rival derivations (§2–§6) -/

/-- An account of what places the participle before the external argument, (11)–(14), either
PartP moving to Spec,VoiceP, the verb alone moving to Voice, or nothing moving. -/
inductive Analysis
  | partP | headMovement | inSitu
  deriving DecidableEq, Fintype, Repr

/-- The complement of the verb when the patient is in Spec,VP (17), a particle or a stranded
preposition, or a PP. -/
inductive Complement
  | particle (x : LexicalItem.Token)
  | pp (x : LexicalItem.Token)

/-- The leaf of a complement. -/
def Complement.token : Complement → LexicalItem.Token
  | .particle x | .pp x => x

/-- A transitive clause, given by its verb, its external and internal arguments, its auxiliary
and an optional complement of the verb. -/
structure Clause where
  /-- The verb, in its participial form. -/
  verb : LexicalItem.Token
  /-- The external argument, Merged in Spec,vP. -/
  agent : LexicalItem.Token
  /-- The internal argument. -/
  patient : LexicalItem.Token
  /-- The auxiliary *be*. -/
  be : LexicalItem.Token
  /-- The complement of the verb, with the patient in Spec,VP. -/
  complement : Option Complement

/-- The participle head, silent, over the VP. -/
def part₀ : LexicalItem.Token := ⟨.of .Asp [.V], 5⟩

/-- The light verb, over PartP and the external argument. -/
def v₀ : LexicalItem.Token := ⟨.of .v [.Asp, .D], 6⟩

/-- The host X of an evacuated PP (58), a second participial layer over PartP that takes the PP,
so that v selects the same category with or without evacuation. -/
def x₀ : LexicalItem.Token := ⟨.of .Asp [.Asp, .P], 8⟩

/-- Infl. -/
def infl₀ : LexicalItem.Token := ⟨.of .T [], 9⟩

/-- The auxiliary *have* of the active perfect (26). -/
def has₀ : LexicalItem.Token := ⟨.of .V [] (phonForm := "has"), 10⟩

namespace Clause

/-- The clause of the given words, its external argument silent when its word is empty. -/
def of (verb agent patient : String) (particle pp : Option String := none)
    (be : String := "was") : Clause :=
  let complement : Option Complement :=
    (particle.map fun x ↦ .particle ⟨.of .P [] (phonForm := x), 11⟩) <|>
      pp.map fun x ↦ .pp ⟨.of .P [] (phonForm := x), 11⟩
  ⟨⟨.of .V (if complement.isSome then [.P, .D] else [.D]) (phonForm := verb), 1⟩,
    ⟨.of .D [] (phonForm := agent), 2⟩, ⟨.of .D [] (phonForm := patient), 3⟩,
    ⟨.of .V [] (phonForm := be), 4⟩, complement⟩

variable (p : Clause)

/-- Voice, which takes a vP (§4), spelled out as *by* over an overt external argument and as Ø
over a silent one (47). -/
def voice : LexicalItem.Token :=
  ⟨.of .Voice [.v] (phonForm := if p.agent.item.phonForm?.isSome then "by" else ""), 7⟩

/-- The VP, the verb with its object (8) or with a complement as `{Patient, {V, X}}` (17). -/
def vpSteps : List Step :=
  match p.complement with
  | some c => [.em .right c.token, .em .left p.patient]
  | none => [.em .right p.patient]

/-- The element that leaves PartP before it fronts, the PP when `evacuate` holds (58). -/
def evacuee? (evacuate : Bool) : Option LexicalItem.Token :=
  match p.complement, evacuate with
  | some (.pp x), true => some x
  | _, _ => none

/-- The PartP at the point it fronts, over the VP, with the trace of the evacuee if there is
one. -/
def partP (evacuate : Bool) : LinearizedSyntacticObject :=
  let leaf := LinearizedSyntacticObject.leaf
  let vp : LinearizedSyntacticObject := match p.complement with
    | some c =>
        {leaf p.patient, {leaf p.verb,
          if (p.evacuee? evacuate).isSome then .traceOf c.token else leaf c.token}}
    | none => {leaf p.verb, leaf p.patient}
  {leaf part₀, vp}

/-- The evacuation of the PP to Spec,XP before PartP fronts, (58a)–(58b). -/
def evacuation (evacuate : Bool) : List Step :=
  match p.evacuee? evacuate with
  | some x => [.em .left x₀, .im x]
  | none => []

/-- The derivation through vP, the same in the active and the passive (§2). -/
def vP (evacuate : Bool) : Derivation :=
  ⟨p.verb, p.vpSteps ++ [.em .left part₀] ++ p.evacuation evacuate ++
    [.em .left v₀, .em .left p.agent]⟩

/-- The derivation through Voice Merged over vP (30). -/
def voiceP (evacuate : Bool) : Derivation := (p.vP evacuate).append [.em .left p.voice]

/-- The derivation through the fronting of an analysis, PartP to Spec,VoiceP (14), the verb to
Voice (13), or nothing. -/
def fronted (a : Analysis) (evacuate : Bool) : Derivation :=
  (p.voiceP evacuate).append <| match a with
    | .partP => [.im (p.partP evacuate)]
    | .headMovement => [.im p.verb]
    | .inSitu => []

/-- The derivation through the stage at which Infl attracts, with the auxiliary and Infl over
VoiceP. -/
def preRaising (a : Analysis) (evacuate : Bool) : Derivation :=
  (p.fronted a evacuate).append [.em .left p.be, .em .left infl₀]

/-- The passive, with the object raised to Spec,IP (22). -/
def passive (a : Analysis) (evacuate : Bool) : Derivation :=
  (p.preRaising a evacuate).append [.im p.patient]

/-- The active perfect (26), with *have* and Infl over vP and the external argument in Spec,IP. -/
def active : Derivation := (p.vP false).append [.em .left has₀, .em .left infl₀, .im p.agent]

/-- At the stage where Infl attracts, its probe finds `goal`, a D leaf among the positions it
c-commands that no other such leaf asymmetrically c-commands. -/
def InflFinds (a : Analysis) (evacuate : Bool) (goal : LexicalItem.Token) : Prop :=
  ∃ t ∈ (p.preRaising a evacuate).externalize?,
    ↑goal ∈ t.goals (t.leafProbe .D) infl₀

instance (a : Analysis) (evacuate : Bool) (goal : LexicalItem.Token) :
    Decidable (p.InflFinds a evacuate goal) := by
  unfold InflFinds; infer_instance

/-- An analysis converges when Infl's probe finds the object, so that its raising violates
neither the Minimal Link Condition nor Relativized Minimality (§5). -/
def Converges (a : Analysis) (evacuate : Bool) : Prop := p.InflFinds a evacuate p.patient

instance (a : Analysis) (evacuate : Bool) : Decidable (p.Converges a evacuate) := by
  unfold Converges; infer_instance

/-- The passive under an analysis pronounces the words `ws`. -/
def Pronounces (a : Analysis) (evacuate : Bool) (ws : List (List Char)) : Prop :=
  (p.passive a evacuate).surfacePhon.flatMap (Gloss.tokens ·) = ws

instance (a : Analysis) (evacuate : Bool) (ws : List (List Char)) :
    Decidable (p.Pronounces a evacuate ws) := by
  unfold Pronounces; infer_instance

/-- Some converging passive derivation of the clause pronounces the words `ws`. -/
def Derives (ws : List (List Char)) : Prop :=
  ∃ a evacuate, p.Pronounces a evacuate ws ∧ p.Converges a evacuate

instance (ws : List (List Char)) : Decidable (p.Derives ws) := by
  unfold Derives; infer_instance

end Clause

/-- (9), (22), (30): *The book was written by John*. -/
def ex9 : Clause := .of "written" "John" "the book"

/-- (23a), (26): *John has seen the book*. -/
def ex23 : Clause := .of "seen" "John" "the book"

/-- (45), (46): *The book was written*, a short passive with a silent external argument. -/
def ex45 : Clause := .of "written" "" "the book"

/-- (56): *The book was given to Mary by John*. -/
def ex56 : Clause := .of "given" "John" "the book" (pp := "to Mary")

theorem ex23_active :
    ex23.active.surfacePhon.flatMap (Gloss.tokens ·) = Gloss.tokens Examples.ex23a.primaryText := by
  decide

/-- The active and the passive share the derivation through vP, so the external argument is
Merged in Spec,vP in both (§2). -/
theorem active_shares_vP (p : Clause) (a : Analysis) :
    p.active.take (p.vP false).length = (p.passive a false).take (p.vP false).length := by
  simp [Clause.active, Clause.passive, Clause.preRaising, Clause.fronted, Clause.voiceP]

theorem cCommandsAt_vP_iff (p : Clause) (a : Analysis) {x y : SyntacticObject} :
    p.active.CCommandsAt (p.vP false).length x y ↔
      (p.passive a false).CCommandsAt (p.vP false).length x y := by
  rw [Derivation.CCommandsAt, Derivation.CCommandsAt, active_shares_vP]

example : ex9.active.CCommandsAt (ex9.vP false).length ex9.agent ex9.patient := by decide

/-! ### Smuggling (§5, §6) -/

theorem partP_smuggles :
    (ex9.passive .partP false).IsSmugglingStep (ex9.voiceP false).length ex9.patient
        ex9.agent ∧
      ¬ (ex9.passive .headMovement false).IsSmugglingStep (ex9.voiceP false).length
        ex9.patient ex9.agent := by
  decide

/-- Under Relativized Minimality only PartP smuggling converges, so head movement and
*The book was by John written* (9a), (36), both fail (§5). -/
theorem ex9_converges_iff (a : Analysis) : ex9.Converges a false ↔ a = .partP := by
  cases a <;> decide

/-- Smuggling brings the object level with the external argument, not past it: once PartP has
moved, Infl's probe finds both. -/
example : ex9.InflFinds .partP false ex9.agent := by decide +kernel

theorem ex9_converges_iff_not_obeysFreezing (a : Analysis) :
    ex9.Converges a false ↔ ¬ (ex9.passive a false).ObeysFreezing := by
  cases a
  · refine iff_of_true ((ex9_converges_iff _).2 rfl) ?_
    exact (show (ex9.preRaising .partP false).IsSmugglingStep (ex9.voiceP false).length
      ex9.patient ex9.agent by decide).not_obeysFreezing_append_im .left
  all_goals decide

theorem ex45_surfacePhon (a : Analysis) :
    (ex45.passive a false).surfacePhon = (ex45.passive .partP false).surfacePhon := by
  cases a <;> decide

theorem ex45_converges_iff (a : Analysis) : ex45.Converges a false ↔ a = .partP := by
  cases a <;> decide

theorem ex56_isRemnantStep :
    (ex56.passive .partP true).IsRemnantStep (ex56.voiceP true).length := by
  decide

/-! ### *By* takes a vP (§4) -/

theorem by_selects_vP :
    (Examples.ex29.judgment = .acceptable ↔
      (({LinearizedSyntacticObject.leaf ex9.voice, LinearizedSyntacticObject.leaf ex9.patient} :
        LinearizedSyntacticObject).toSyntacticObject.selHead).isSome) ∧
    ∃ q ∈ (ex9.voiceP false).externalize?, q.toSyntacticObject.selHead = some ex9.voice := by
  decide

/-! ### Word order and convergence (§3, §5, §7) -/

/-- The clause a row records. -/
def Clause.ofRow (row : Datum) : Option Clause := do
  let verb ← row.feature? "verb"
  let agent ← row.feature? "agent"
  let patient ← row.feature? "patient"
  return .of verb agent patient (row.feature? "particle") (row.feature? "pp")
    ((row.feature? "be").getD "was")

/-- The words of a row's sentence, less a final adjunct the derivations do not build when the row
records one and the sentence ends in it. -/
def clauseWords? (row : Datum) : Option (List (List Char)) :=
  let ws := Gloss.tokens row.primaryText
  match row.feature? "adjunct" with
  | none => some ws
  | some a =>
      let as := Gloss.tokens a
      if as.isSuffixOf ws then some (ws.take (ws.length - as.length)) else none

/-- A passive row's clause with the words of its sentence. -/
def passiveRow? (row : Datum) : Option (Clause × List (List Char)) := do
  guard (row.feature? "construction" = some "passive")
  return (← Clause.ofRow row, ← clauseWords? row)

/-- Each passive row is pronounced by some derivation of its clause, and is acceptable exactly
when one that pronounces it converges, so that (9a), (15b) and (18b) are pronounced only by
analyses that fail Relativized Minimality. -/
theorem order_rows :
    Datum.Checks passiveRow? (fun x ↦ .ofProp (x.1.Derives x.2)) Examples.all 8 ∧
      ∀ row ∈ Examples.all, ∀ x ∈ passiveRow? row, ∃ a ev, x.1.Pronounces a ev x.2 := by
  decide +kernel

/-! ### C-command and binding across the by-phrase (§3, §7, §9, §10) -/

/-- The positions the tests relate, the external argument and the complement of the verb. -/
inductive Position
  | external | pp
  deriving DecidableEq, Fintype, Repr

/-- The leaf at a position. -/
def Clause.at? (p : Clause) : Position → Option LexicalItem.Token
  | .external => some p.agent
  | .pp => p.complement.map Complement.token

/-- The level at which a dependency is evaluated, the surface or some stage of the derivation,
reconstruction included. -/
inductive Level
  | surface | anyStage
  deriving DecidableEq, Repr

/-- C-command at a level of `d`, at its last stage or at some stage. -/
def Level.CCommands : Level → Derivation → SyntacticObject → SyntacticObject → Prop
  | .surface, d => d.BindsAtSurface
  | .anyStage, d => d.BindsAtSomeStage

instance : ∀ (ℓ : Level) (d : Derivation), DecidableRel (ℓ.CCommands d)
  | .surface, d => fun x y ↦ inferInstanceAs (Decidable (d.BindsAtSurface x y))
  | .anyStage, d => fun x y ↦ inferInstanceAs (Decidable (d.BindsAtSomeStage x y))

/-- The binding configuration of `p` at level `ℓ` of its derivation `d`, in which one position
commands another when its leaf c-commands the other's there. -/
abbrev Level.configuration (ℓ : Level) (p : Clause) (d : Derivation) :
    Binding.Configuration Position :=
  .monoclausal p.at? fun x y ↦ ℓ.CCommands d x y

/-- The binding condition of the class `c` holds of the element at `y`, coindexed with the
element at `x`, at level `ℓ` of the derivation `d` of `p`. -/
def Level.Condition (ℓ : Level) (p : Clause) (d : Derivation) (x y : Position)
    (c : Binding.BindingClass) : Prop :=
  (ℓ.configuration p d).Condition (Binding.pair x y) ∅ y c

instance (ℓ : Level) (p : Clause) (d : Derivation) (x y : Position) (c : Binding.BindingClass) :
    Decidable (ℓ.Condition p d x y c) := by
  unfold Level.Condition; infer_instance

/-- A dependency the rows test, the binding condition of a nominal's binding class, a bound
variable, a negative polarity item, or *the other*. -/
inductive Dependency
  | condition (c : Binding.BindingClass)
  | variable | npi | other
  deriving DecidableEq, Repr

/-- A verdict of the analysis on a dependency, which is licensed at the surface, licensed only at
an earlier stage by reconstructing the fronted PartP, or not licensed. -/
inductive Verdict
  | licensed | reconstructed | excluded
  deriving DecidableEq, Repr

namespace Verdict

/-- The verdict of a condition that holds or fails. -/
def ofProp (P : Prop) [Decidable P] : Verdict := if P then .licensed else .excluded

/-- The verdict of a condition evaluated at the surface, with reconstruction to an earlier stage
as the marginal option. -/
def graded (P : Level → Prop) [DecidablePred P] : Verdict :=
  if P .surface then .licensed else if P .anyStage then .reconstructed else .excluded

/-- A verdict admits the unmarked judgment for a licensed dependency, `*` for an excluded one, and
a mark strictly between the two for a reconstructed one, reconstruction of PartP being marginally
available (§9.2). -/
def Admits : Verdict → Judgment → Prop
  | .licensed, j => j = .acceptable
  | .reconstructed, j => .ungrammatical < j ∧ j < .acceptable
  | .excluded, j => j = .ungrammatical

instance : ∀ (v : Verdict) (j : Judgment), Decidable (v.Admits j)
  | .licensed, _ => inferInstanceAs (Decidable (_ = _))
  | .reconstructed, _ => inferInstanceAs (Decidable (_ ∧ _))
  | .excluded, _ => inferInstanceAs (Decidable (_ = _))

end Verdict

/-- The verdict on the dependency of the element at `y` on the element at `x` in the derivation
`d` of `p`. Principle B applies at every stage, as the DP is Merged (83)–(84), Principle C,
negative polarity and *the other* at the surface, and an anaphor or a bound variable at the
surface or, marginally, by reconstruction (§9.1–§9.2). -/
def Dependency.verdict (dep : Dependency) (p : Clause) (d : Derivation) (x y : Position) :
    Verdict :=
  match dep with
  | .condition .pronoun => .ofProp (Level.anyStage.Condition p d x y .pronoun)
  | .condition .rExpression => .ofProp (Level.surface.Condition p d x y .rExpression)
  | .condition c => .graded fun ℓ ↦ ℓ.Condition p d x y c
  | .variable => .graded fun ℓ ↦ (ℓ.configuration p d).Bound (Binding.pair x y) y
  | .npi | .other => .ofProp ((Level.surface.configuration p d).commands x y)

/-- A licensing row's configuration. -/
structure Licensing where
  /-- The clause. -/
  clause : Clause
  /-- Whether the PP evacuated PartP. -/
  evacuated : Bool
  /-- The dependency. -/
  dependency : Dependency
  /-- The position that must, or must not, c-command. -/
  antecedent : Position
  /-- The position of the dependent element. -/
  dependent : Position

/-- The configuration a row records, the PP evacuated when that is how the PartP-movement
derivation pronounces the row's sentence. -/
def Licensing.ofRow (row : Datum) : Option Licensing := do
  guard (row.feature? "construction" = some "licensing")
  let p ← Clause.ofRow row
  let ws ← clauseWords? row
  let positions := [("external", Position.external), ("pp", .pp)]
  return ⟨p, ← [false, true].find? fun ev ↦ decide (p.Pronounces .partP ev ws),
    ← row.parse? "dependency" [("npi", Dependency.npi), ("other", .other),
      ("variable", .variable), ("reflexive", .condition .reflexive),
      ("reciprocal", .condition .reciprocal), ("pronoun", .condition .pronoun),
      ("name", .condition .rExpression)],
    ← row.parse? "antecedent" positions, ← row.parse? "dependent" positions⟩

/-- The PartP-movement derivation of the configuration, with the PP evacuated or not. -/
def Licensing.derivation (c : Licensing) : Derivation := c.clause.passive .partP c.evacuated

/-- On the rows' derivations reconstruction to a stage is binding at the copy object
(`Derivation.bindsAtSomeStage_iff_bindsAtLF`). -/
example : ∀ row ∈ Examples.all, ∀ c ∈ Licensing.ofRow row, ∀ x y : LexicalItem.Token, x ≠ y →
    (c.derivation.BindsAtSomeStage ↑x ↑y ↔ c.derivation.BindsAtLF ↑x ↑y) := by
  have h : ∀ row ∈ Examples.all, ∀ c ∈ Licensing.ofRow row, c.derivation.lexTokens.Nodup ∧
      (∀ step ∈ c.derivation.steps, step.IsMerge) ∧
      (∀ step ∈ c.derivation.steps, ∀ m ∈ step.mover?, m.val.value.isLeft) ∧
      c.derivation.replay?.isSome := by
    decide +kernel
  intro row hrow c hc x y hxy
  obtain ⟨hd, hm, hmv, hr⟩ := h row hrow c hc
  exact Derivation.bindsAtSomeStage_iff_bindsAtLF hxy hd hm hmv hr

/-- The verdict on the configuration's derivation. -/
def Licensing.verdict (c : Licensing) : Verdict :=
  c.dependency.verdict c.clause c.derivation c.antecedent c.dependent

/-- The [barss-lasnik-1986] tests (10), (60a), Principle A (72a), (74a), (91), the bound variable
(75), Principle B (80a) and Principle C (76a), (85) follow from the position of the PP. -/
theorem licensing_rows :
    (∀ row ∈ Examples.all, ∀ c ∈ Licensing.ofRow row, c.verdict.Admits row.judgment) ∧
      Datum.ReadCount Licensing.ofRow Examples.all 14 := by
  decide

/-- The rows of a binding class fit its condition evaluated at level `ℓ`, each row acceptable
exactly when the condition holds. -/
def FitsAt (cls : Binding.BindingClass) (ℓ : Level) : Prop :=
  ∀ row ∈ Examples.all, ∀ c ∈ Licensing.ofRow row, c.dependency = .condition cls →
    (row.judgment = .acceptable ↔
      ℓ.Condition c.clause c.derivation c.antecedent c.dependent cls)

instance (cls : Binding.BindingClass) (ℓ : Level) : Decidable (FitsAt cls ℓ) := by
  unfold FitsAt; infer_instance

theorem fitsAt_pronoun_iff (ℓ : Level) : FitsAt .pronoun ℓ ↔ ℓ = .anyStage := by
  cases ℓ <;> decide

/-- The name rows fit Principle C exactly at the surface, (76a) excluding obligatory
reconstruction, as the pronoun rows fit Principle B exactly at every stage
(`fitsAt_pronoun_iff`) (§9). -/
theorem fitsAt_rExpression_iff (ℓ : Level) : FitsAt .rExpression ℓ ↔ ℓ = .surface := by
  cases ℓ <;> decide

/-! ### Participle licensing (§3, (23)–(28)) -/

/-- The auxiliary over a participle, *have*, *be*, or none, as in a participial modifier. -/
inductive Auxiliary
  | have | be | bare
  deriving DecidableEq, Repr

/-- A participle clause, given by its auxiliary and whether a VoiceP is present. -/
structure Participle where
  /-- The auxiliary. -/
  auxiliary : Auxiliary
  /-- Whether a Voice head is present. -/
  voiceP : Bool

/-- A participle is licensed by exactly one of *have*, which c-selects it, and Voice, which
attracts it (24)–(25), since a participle Voice has licensed cannot also be checked by *have* and
*be* imposes nothing. -/
def Participle.Licensed (c : Participle) : Prop := Xor (c.auxiliary = .have) c.voiceP

instance (c : Participle) : Decidable c.Licensed := inferInstanceAs (Decidable (Xor _ _))

/-- The configuration a row records. -/
def Participle.ofRow (row : Datum) : Option Participle := do
  guard (row.feature? "construction" = some "participle")
  return ⟨← row.parse? "auxiliary" [("have", Auxiliary.have), ("be", .be), ("none", .bare)],
    ← row.bool? "voiceP"⟩

theorem participle_rows :
    Datum.Checks Participle.ofRow (fun c ↦ .ofProp c.Licensed) Examples.all 6 := by
  decide

end Collins2005
