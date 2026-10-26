module

public import Linglib.Data.Examples.Collins2005
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
movement of the verb and no movement, as derivations, and checks the paper's examples against
their strings, against Infl's probe search, and against the binding conditions of `Syntax/Binding`
evaluated at the surface or at some stage of the derivation.

## Main statements

* `Collins2005.active_shares_vP`: the active and the passive share the derivation through vP (§2).
* `Collins2005.rm_converges`: only PartP movement lets Infl find the object (§5).
* `Collins2005.licensing_rows`: the c-command and binding judgments of (10) and (60)–(91).
* `Collins2005.binding_levels`: Principle B holds at every stage, Principle C at the surface (§9).
* `Collins2005.participle_rows`: the auxiliary paradigm from the licensing of participles (24).

## Implementation notes

* Part is a silent `Cat.Asp` head, and V-to-Part raising (8) is not modelled. The object sits in
  Spec,VP, a PP is one leaf, the host X of (58) is a second `Cat.Asp` layer, and head movement
  re-Merges the verb's leaf at the root in place of the adjunction of (13).
* A dependency licensed only by reconstructing PartP is marked but not starred, the `??` of (72a)
  and the `?` of (75) alike (§9.2). Reconstruction licenses anaphors and bound variables only; the
  paper does not say why it leaves (10a) and (10b) starred.
* Principle B omits the local-domain and Case clauses of (83), which the monoclausal rows never
  exercise.

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
  deriving DecidableEq, Repr

/-- A transitive clause, given by its verb, its external and internal arguments, its auxiliary
and an optional third element of VP, a particle, a stranded preposition or a PP. -/
structure Clause where
  /-- The verb, in its participial form. -/
  verb : LexicalItem.Token
  /-- The external argument, Merged in Spec,vP. -/
  agent : LexicalItem.Token
  /-- The internal argument. -/
  patient : LexicalItem.Token
  /-- The auxiliary *be*. -/
  be : LexicalItem.Token
  /-- The complement of the verb when the patient is in Spec,VP (17). -/
  extra : Option LexicalItem.Token

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
def of (verb agent patient : String) (extra : Option String := none) (be : String := "was") :
    Clause :=
  ⟨⟨.of .V (if extra.isSome then [.P, .D] else [.D]) (phonForm := verb), 1⟩,
    ⟨.of .D [] (phonForm := agent), 2⟩,
    ⟨.of .D [] (phonForm := patient), 3⟩, ⟨.of .V [] (phonForm := be), 4⟩,
    extra.map fun x ↦ ⟨.of .P [] (phonForm := x), 11⟩⟩

variable (p : Clause)

/-- Voice, which takes a vP (§4), spelled out as *by* over an overt external argument and as Ø
over a silent one (47). -/
def voice : LexicalItem.Token :=
  ⟨.of .Voice [.v] (phonForm := if p.agent.item.phonForm?.isSome then "by" else ""), 7⟩

/-- The VP, the verb with its object (8) or with a third element as `{Patient, {V, X}}` (17). -/
def vpSteps : List Step :=
  match p.extra with
  | some x => [.em .right x, .em .left p.patient]
  | none => [.em .right p.patient]

/-- The PartP at the point it fronts, over the VP, with the trace of the evacuated element when
that element has left. -/
def partP (evacuate : Bool) : LinearizedSyntacticObject :=
  let leaf := LinearizedSyntacticObject.leaf
  let vp : LinearizedSyntacticObject := match p.extra with
    | some x => {leaf p.patient, {leaf p.verb, if evacuate then .traceOf x else leaf x}}
    | none => {leaf p.verb, leaf p.patient}
  {leaf part₀, vp}

/-- The evacuation of the third element to Spec,XP before PartP fronts, (58a)–(58b). -/
def evacuation (evacuate : Bool) : List Step :=
  match p.extra with
  | some x => if evacuate then [.em .left x₀, .im x] else []
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

end Clause

/-- (9), (22), (30): *The book was written by John*. -/
def ex9 : Clause := .of "written" "John" "the book"

/-- (15): *The argument was summed up by the coach*. -/
def ex15 : Clause := .of "summed" "the coach" "the argument" "up"

/-- (18): *John was spoken to by Mary*. -/
def ex18 : Clause := .of "spoken" "Mary" "John" "to"

/-- (23a), (26): *John has seen the book*. -/
def ex23 : Clause := .of "seen" "John" "the book"

/-- (45), (46): *The book was written*, a short passive with a silent external argument. -/
def ex45 : Clause := .of "written" "" "the book"

/-- (56): *The book was given to Mary by John*. -/
def ex56 : Clause := .of "given" "John" "the book" "to Mary"

theorem ex9_orders :
    (ex9.passive .partP false).surfacePhon = ["the book", "was", "written", "by", "John"] ∧
      (ex9.passive .headMovement false).surfacePhon
        = ["the book", "was", "written", "by", "John"] ∧
      (ex9.passive .inSitu false).surfacePhon
        = ["the book", "was", "by", "John", "written"] := by
  decide

theorem particle_orders :
    (ex15.passive .partP false).surfacePhon
        = ["the argument", "was", "summed", "up", "by", "the coach"] ∧
      (ex15.passive .headMovement false).surfacePhon
        = ["the argument", "was", "summed", "by", "the coach", "up"] ∧
      (ex18.passive .partP false).surfacePhon
        = ["John", "was", "spoken", "to", "by", "Mary"] ∧
      (ex18.passive .headMovement false).surfacePhon
        = ["John", "was", "spoken", "by", "Mary", "to"] := by
  decide

theorem pp_orders :
    (ex56.passive .partP false).surfacePhon
        = ["the book", "was", "given", "to Mary", "by", "John"] ∧
      (ex56.passive .partP true).surfacePhon
        = ["the book", "was", "given", "by", "John", "to Mary"] := by
  decide

theorem active_order : ex23.active.surfacePhon = ["John", "has", "seen", "the book"] := by decide

/-- The active and the passive share the derivation through vP, so the external argument is
Merged in Spec,vP in both (§2). -/
theorem active_shares_vP (p : Clause) (a : Analysis) :
    p.active.take (p.vP false).length = (p.passive a false).take (p.vP false).length := by
  simp [Clause.active, Clause.passive, Clause.preRaising, Clause.fronted, Clause.voiceP]

/-! ### Smuggling (§5, §6) -/

theorem partP_smuggles :
    (ex9.passive .partP false).IsSmugglingStep (ex9.voiceP false).length ex9.patient
        ex9.agent ∧
      ¬ (ex9.passive .headMovement false).IsSmugglingStep (ex9.voiceP false).length
        ex9.patient ex9.agent := by
  decide

/-- Under Relativized Minimality only PartP smuggling converges, so head movement and
*The book was by John written* (9a), (36), both fail (§5). -/
theorem rm_converges (a : Analysis) :
    ex9.Converges a false ↔ a = .partP := by
  cases a <;> decide

/-- Smuggling brings the object level with the external argument, not past it: once PartP has
moved, Infl's probe finds both. -/
example : ex9.InflFinds .partP false ex9.agent := by decide +kernel

theorem converges_iff_not_obeysFreezing (a : Analysis) :
    ex9.Converges a false ↔ ¬ (ex9.passive a false).ObeysFreezing := by
  cases a
  · refine iff_of_true ((rm_converges _).2 rfl) ?_
    exact (show (ex9.preRaising .partP false).IsSmugglingStep (ex9.voiceP false).length
      ex9.patient ex9.agent by decide).not_obeysFreezing_append_im .left
  all_goals decide

theorem agent_over_patient_at_vP :
    ex9.active.CCommandsAt (ex9.vP false).length ex9.agent ex9.patient ∧
      (ex9.passive .partP false).CCommandsAt (ex9.vP false).length ex9.agent ex9.patient := by
  decide

theorem short_passive (a : Analysis) :
    (ex45.passive a false).surfacePhon = ["the book", "was", "written"] ∧
      (ex45.Converges a false ↔ a = .partP) := by
  cases a <;> decide

theorem pp_remnant : (ex56.passive .partP true).IsRemnantStep (ex56.voiceP true).length := by
  decide

/-! ### *By* takes a vP (§4) -/

theorem by_selects_vP :
    (Examples.ex29.judgment = .acceptable ↔
      (({LinearizedSyntacticObject.leaf ex9.voice, LinearizedSyntacticObject.leaf ex9.patient} :
        LinearizedSyntacticObject).toSyntacticObject.selHead).isSome) ∧
    ∃ q ∈ (ex9.voiceP false).externalize?, q.toSyntacticObject.selHead = some ex9.voice := by
  decide

/-! ### The rows -/

/-- The clause a row records. -/
def Clause.ofRow (row : Datum) : Option Clause := do
  let verb ← row.feature? "verb"
  let agent ← row.feature? "agent"
  let patient ← row.feature? "patient"
  return .of verb agent patient (row.feature? "particle" <|> row.feature? "pp")

/-! ### Word order and convergence (§3, §5) -/

/-- A word-order row's configuration, its clause with the analysis that derives its string and
whether the PP evacuated. -/
structure Order where
  /-- The clause. -/
  clause : Clause
  /-- The analysis that derives the row's string. -/
  analysis : Analysis
  /-- Whether the PP evacuated PartP. -/
  evacuated : Bool

/-- The configuration a row records. -/
def Order.ofRow (row : Datum) : Option Order := do
  guard (row.feature? "construction" = some "passive")
  return ⟨← Clause.ofRow row,
    ← row.parse? "analysis"
      [("partP", .partP), ("headMovement", .headMovement), ("inSitu", .inSitu)],
    (row.bool? "evacuated").getD false⟩

theorem order_rows : Datum.Checks Order.ofRow
    (fun o ↦ .ofProp (o.clause.Converges o.analysis o.evacuated)) Examples.all 8 := by
  decide +kernel

/-! ### C-command and binding across the by-phrase (§3, §7, §9, §10) -/

/-- The positions the tests relate, the external argument and the third element of VP. -/
inductive Position
  | external | pp
  deriving DecidableEq, Fintype, Repr

/-- The leaf at a position. -/
def Clause.at? (p : Clause) : Position → Option LexicalItem.Token
  | .external => some p.agent
  | .pp => p.extra

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

open Binding in
/-- The verdict on the dependency of the element at `y` on the element at `x` in the derivation
`d` of `p`. Principle B applies at every stage, as the DP is Merged (83)–(84), Principle C,
negative polarity and *the other* at the surface, and an anaphor or a bound variable at the
surface or, marginally, by reconstruction (§9.1–§9.2). -/
def Dependency.verdict (dep : Dependency) (p : Clause) (d : Derivation) (x y : Position) :
    Verdict :=
  match dep with
  | .condition .pronoun =>
      .ofProp ((Level.anyStage.configuration p d).Condition (pair x y) ∅ y .pronoun)
  | .condition .rExpression =>
      .ofProp ((Level.surface.configuration p d).Condition (pair x y) ∅ y .rExpression)
  | .condition c => .graded fun ℓ ↦ (ℓ.configuration p d).Condition (pair x y) ∅ y c
  | .variable => .graded fun ℓ ↦ (ℓ.configuration p d).Bound (pair x y) y
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

/-- The configuration a row records. -/
def Licensing.ofRow (row : Datum) : Option Licensing := do
  guard (row.feature? "construction" = some "licensing")
  let positions := [("external", Position.external), ("pp", .pp)]
  return ⟨← Clause.ofRow row, ← row.bool? "evacuated",
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
    (row.judgment = .acceptable ↔ (ℓ.configuration c.clause c.derivation).Condition
      (Binding.pair c.antecedent c.dependent) ∅ c.dependent cls)

instance (cls : Binding.BindingClass) (ℓ : Level) : Decidable (FitsAt cls ℓ) := by
  unfold FitsAt; infer_instance

/-- The pronoun rows fit Principle B exactly at every stage (80a), (84), and the name rows fit
Principle C exactly at the surface (76a), so that B is derivational and C representational (§9). -/
theorem binding_levels (ℓ : Level) :
    (FitsAt .pronoun ℓ ↔ ℓ = .anyStage) ∧ (FitsAt .rExpression ℓ ↔ ℓ = .surface) := by
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

/-- A participle clause of (23) or (27) is acceptable exactly when its participle has one
licenser. -/
theorem participle_rows :
    Datum.Checks Participle.ofRow (fun c ↦ .ofProp c.Licensed) Examples.all 6 := by
  decide

end Collins2005
