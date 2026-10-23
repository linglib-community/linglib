module

public import Linglib.Data.Examples.Collins2005
public import Linglib.Syntax.Binding.Basic
public import Linglib.Syntax.Minimalist.Probe.SyntacticObject
public import Linglib.Syntax.Minimalist.Locality.Freezing
public import Linglib.Syntax.Minimalist.Derivation.Remnant
public import Linglib.Syntax.Minimalist.Derivation.Smuggling

/-!
# Collins 2005: a smuggling approach to the passive in English

The principles-and-parameters passive lets the suffix *-en* absorb accusative Case and the
external θ-role, so that the agent of *The book was written by John* is Merged nowhere near
where the agent of the active is Merged, against the uniformity of θ-assignment. Collins
returns to Syntactic Structures on this point: the external argument is Merged in Spec,vP in
the passive exactly as in the active, the participle head Part takes the VP and vP takes PartP,
and the verb precedes the external argument because PartP moves to the specifier of a VoiceP
headed by *by*, a head of uninterpretable features that takes a vP complement and checks the
Case that v checks in the active. That the movement is of the phrase and not of the verb's
head is shown by particles and stranded prepositions, which precede the external argument and
cannot follow it. The structure also orders the auxiliaries: *have* c-selects a participle,
Voice attracts one, and a participle must be licensed by exactly one of them, which admits
*has seen* and *was seen by* and excludes *has seen by* and *was seen*.

The movement is smuggling: the object inside PartP, which the external argument in Spec,vP
c-commands and so shields from Infl by Relativized Minimality, is carried past it, after which the
object is as close to Infl as the external argument and raises to Spec,IP. Without the movement, or
with head movement of the verb alone, the object stays behind the external argument and the passive
cannot be derived; the derivation extracts the object from a moved constituent, and the paper takes
Freezing not to hold of PartP movement. A PP that follows the by-phrase has evacuated PartP before
the remnant fronted, so the external argument c-commands it, and a PP that precedes the by-phrase
has not, so it does not: negative polarity, *each* … *the other* and Principle C line up with the
position of the PP. A reflexive or a bound variable inside the fronted PartP is bound only by
reconstruction, which the paper takes to be marginal, and Principle B applies as the external
argument is Merged, so a coindexed pronoun inside PartP is out however PartP later moves.

The passive is a `Derivation` on the syntactic-object carrier under each of the three analyses, the
surface strings are its externalizations, Relativized Minimality is the search of Infl's probe over
the positions it c-commands at the stage where it attracts, smuggling and remnant fronting are the
substrate's step predicates, and the paper's examples are the rows: `rm_converges` singles out PartP
movement, which `converges_iff_not_obeysFreezing` shows the one analysis Freezing excludes,
`licensing_rows` derives the c-command and binding judgments from surface and derivational
c-command, the binding judgments being the conditions of `Syntax/Binding` at the levels the paper
assigns them, of which the rows force Principle B's (`principleB_anyStage`), `participle_rows` the
auxiliary paradigm from the licensing principle, and `active_shares_vP` is the θ-uniformity the
analysis was built for.

## Implementation notes

* Part is `Cat.Asp`, silent, and the verb's raising to it (8) is not modelled: the participle
  is the verb's leaf. Voice is `by` with selection stack `[v]`, so a by-phrase over a DP is
  exocentric, the paper's (29). The evacuation host X of (58), AgrP or LkP for the paper, is a
  second `Cat.Asp` layer selecting PartP and the PP, so that v's selection is uniform; the
  object sits in Spec,VP rather than the paper's Spec,PartP. A PP enters as one leaf, and
  c-command of the leaf stands for c-command of the DP inside it.
* The rival analyses of (11) are the same derivation up to VoiceP: PartP movement raises the
  participle phrase, head movement re-Merges the verb's leaf at the root, standing in for the
  adjunction of (13), and the in-situ analysis raises nothing before the object moves.
  Convergence is whether the object is a closest D-goal for Infl at the stage where it raises;
  the external argument is then as close, and the Case side of the argument, which keeps it in
  place, is prose.
* Principle A and bound-variable binding are evaluated at the surface, with reconstruction to
  any stage as the degraded option; Principle B at any stage, without the local-domain and
  Case-checked clauses of (83), which the monoclausal rows never exercise; Principle C at the
  surface, as §9 argues. The principles are the framework-neutral conditions of
  `Syntax/Binding` on the two positions, under one monoclausal configuration per level.

## TODO

* The double-object (53)–(54), the ECM and CP cases of (55), (57) and (81), the Principle C
  data (76)–(77), the freezing and reciprocal data of §10 ((88)–(93)), the quantifier-raising
  data of (94)–(98), and the Kiswahili and Japanese passives of §5 are not modelled.
* The Case checking by *by* and by the null Voice of short passives (§4, §6) is stated in
  prose; nothing here derives (47).

## References

* [C. Collins, *A Smuggling Approach to the Passive in English* (2005)][collins-2005]
* [A. Barss and H. Lasnik, *A Note on Anaphora and Double Objects* (1986)][barss-lasnik-1986]
* [G. Müller, *Incomplete Category Fronting* (1998)][muller-1998]
* [J. Sabel, *Restrukturierung und Lokalität* (1996)][sabel-1996]
-/

@[expose] public section

namespace Collins2005

open Minimalist SyntacticObject

/-! ### The passive and its rival derivations (§2–§5) -/

/-- What places the participle before the external argument (§3, (11)–(14)): PartP moves to
Spec,VoiceP, the verb alone moves to Voice, or nothing moves. -/
inductive Analysis
  | partP | headMovement | inSitu
  deriving DecidableEq, Repr

/-- A transitive clause: its verb, external and internal arguments, the auxiliary of its passive,
and an optional third element of VP, one leaf: a particle, the complement of V with the object
in Spec,VP (17), or a PP, the leaf standing in for the PP the pseudo-passive strands its
preposition from. -/
structure Clause where
  /-- The verb, in its participial form. -/
  verb : LexicalItem.Token
  /-- The external argument, Merged in Spec,vP. -/
  agent : LexicalItem.Token
  /-- The internal argument. -/
  patient : LexicalItem.Token
  /-- The auxiliary *be*. -/
  be : LexicalItem.Token
  /-- A particle, stranded preposition or PP, the verb's complement with the patient in Spec,VP
  (17). -/
  extra : Option LexicalItem.Token

/-- The participle head, silent, over the VP. -/
def part₀ : LexicalItem.Token := ⟨.of .Asp [.V], 5⟩

/-- The light verb, over PartP and the external argument. -/
def v₀ : LexicalItem.Token := ⟨.of .v [.Asp, .D], 6⟩

/-- Voice, *by*, which takes a vP (§4). -/
def by₀ : LexicalItem.Token := ⟨.of .Voice [.v] (phonForm := "by"), 7⟩

/-- The host X of an evacuated PP, (58): a second participial layer over PartP that takes the
PP, so that v selects the same category with or without evacuation. -/
def x₀ : LexicalItem.Token := ⟨.of .Asp [.Asp, .P], 8⟩

/-- Infl. -/
def infl₀ : LexicalItem.Token := ⟨.of .T [], 9⟩

/-- The auxiliary *have* of the active perfect (26). -/
def has₀ : LexicalItem.Token := ⟨.of .V [] (phonForm := "has"), 10⟩

namespace Clause

/-- A clause from its words. -/
def of (verb agent patient : String) (extra : Option String := none) (be : String := "was") :
    Clause :=
  ⟨⟨.of .V (if extra.isSome then [.P, .D] else [.D]) (phonForm := verb), 1⟩,
    ⟨.of .D [] (phonForm := agent), 2⟩,
    ⟨.of .D [] (phonForm := patient), 3⟩, ⟨.of .V [] (phonForm := be), 4⟩,
    extra.map λ x => ⟨.of .P [] (phonForm := x), 11⟩⟩

variable (p : Clause)

/-- The VP: the verb and its object (8), or with a third element `{Patient, {V, X}}` (17). -/
def vpSteps : List Step :=
  match p.extra with
  | some x => [.em .right x, .em .left p.patient]
  | none => [.em .right p.patient]

/-- The PartP at the point it fronts: over the VP, with the evacuated element's trace when it
has left. -/
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

/-- The derivation through vP, the same in the active and the passive (§2): VP, PartP, the
light verb and the external argument. -/
def vP (evacuate : Bool) : Derivation :=
  ⟨p.verb, p.vpSteps ++ [.em .left part₀] ++ p.evacuation evacuate ++
    [.em .left v₀, .em .left p.agent]⟩

/-- Voice Merges over vP, (30). -/
def voiceP (evacuate : Bool) : Derivation := (p.vP evacuate).append [.em .left by₀]

/-- The three analyses: PartP to Spec,VoiceP (14), the verb to Voice (13), or nothing. -/
def fronted (a : Analysis) (evacuate : Bool) : Derivation :=
  (p.voiceP evacuate).append <| match a with
    | .partP => [.im (p.partP evacuate)]
    | .headMovement => [.im p.verb]
    | .inSitu => []

/-- The stage at which Infl attracts: the auxiliary and Infl over VoiceP. -/
def preRaising (a : Analysis) (evacuate : Bool) : Derivation :=
  (p.fronted a evacuate).append [.em .left p.be, .em .left infl₀]

/-- The passive: the object raised to Spec,IP, (22). -/
def passive (a : Analysis) (evacuate : Bool) : Derivation :=
  (p.preRaising a evacuate).append [.im p.patient]

/-- The active perfect (26): *have* and Infl over vP, and the external argument to Spec,IP. -/
def active : Derivation := (p.vP false).append [.em .left has₀, .em .left infl₀, .im p.agent]

/-- At the stage where Infl attracts, its probe finds `goal`, a D leaf among the positions it
c-commands that no other such leaf asymmetrically c-commands. -/
def InflFinds (a : Analysis) (evacuate : Bool) (goal : LexicalItem.Token) : Prop :=
  ∃ t ∈ (p.preRaising a evacuate).externalize?,
    ↑goal ∈ t.goals (t.leafProbe .D) infl₀

instance (a : Analysis) (evacuate : Bool) (goal : LexicalItem.Token) :
    Decidable (p.InflFinds a evacuate goal) := by
  unfold InflFinds; infer_instance

/-- The analysis converges: Infl's probe finds the object, so its raising violates neither the
Minimal Link Condition nor Relativized Minimality (§5). -/
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

/-- (56): *The book was given to Mary by John*. -/
def ex56 : Clause := .of "given" "John" "the book" "to Mary"

/-- (23a), (26): *John has seen the book*. -/
def ex23 : Clause := .of "seen" "John" "the book"

/-- The three analyses externalize (9b), and, for the two that do not converge, (9a). -/
theorem ex9_orders :
    (ex9.passive .partP false).surfacePhon = ["the book", "was", "written", "by", "John"] ∧
      (ex9.passive .headMovement false).surfacePhon
        = ["the book", "was", "written", "by", "John"] ∧
      (ex9.passive .inSitu false).surfacePhon
        = ["the book", "was", "by", "John", "written"] := by
  decide

/-- Particles (15) and stranded prepositions (18) tell the analyses apart: PartP movement
carries them before the external argument, head movement strands them after it. -/
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

/-- A PP pied-piped inside PartP precedes the by-phrase (56c); evacuated to Spec,XP before the
remnant fronts, it follows it (56d). -/
theorem pp_orders :
    (ex56.passive .partP false).surfacePhon
        = ["the book", "was", "given", "to Mary", "by", "John"] ∧
      (ex56.passive .partP true).surfacePhon
        = ["the book", "was", "given", "by", "John", "to Mary"] := by
  decide

/-- The active perfect (23a). -/
theorem active_order : ex23.active.surfacePhon = ["John", "has", "seen", "the book"] := by decide

/-- θ-uniformity (§2): the active and the passive share the derivation through vP, so the
external argument is Merged in Spec,vP in both. -/
theorem active_shares_vP (p : Clause) (a : Analysis) :
    p.active.take (p.vP false).length = (p.passive a false).take (p.vP false).length := by
  simp [Clause.active, Clause.passive, Clause.preRaising, Clause.fronted, Clause.voiceP]

/-! ### Smuggling (§5) -/

/-- PartP movement smuggles the object past the external argument (34), and head movement of the
verb alone does not. -/
theorem partP_smuggles :
    (ex9.passive .partP false).IsSmugglingStep (ex9.voiceP false).length ex9.patient
        ex9.agent ∧
      ¬ (ex9.passive .headMovement false).IsSmugglingStep (ex9.voiceP false).length
        ex9.patient ex9.agent := by
  decide

/-- Under Relativized Minimality (§5), only PartP smuggling converges, so *The book was by John
written* (9a) and head movement both fail. -/
theorem rm_converges (a : Analysis) :
    ex9.Converges a false ↔ a = .partP := by
  cases a <;> decide

/-- Smuggling brings the object level with the external argument, not past it: once PartP has
moved, Infl's probe finds both. -/
example : ex9.InflFinds .partP false ex9.agent := by decide +kernel

/-- The converging analysis is the one violating [muller-1998]'s Freezing (35), so Freezing is
assumed not to hold of PartP movement (fn. 25). -/
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

/-- The evacuated-PP derivation (58) fronts a remnant: PartP carries the PP's trace. -/
theorem pp_remnant : (ex56.passive .partP true).IsRemnantStep (ex56.voiceP true).length := by
  decide

/-! ### *By* takes a vP (§4) -/

/-- *By* projects over the vP of (30) but not over the DP of the by-phrase *by the book* (29). -/
theorem by_selects_vP :
    (({LinearizedSyntacticObject.leaf by₀, LinearizedSyntacticObject.leaf ex9.patient} :
      LinearizedSyntacticObject).toSyntacticObject).selHead = none ∧
    ∃ q ∈ (ex9.voiceP false).externalize?, q.toSyntacticObject.selHead = some by₀ := by
  decide

/-! ### The rows -/

def bools : List (String × Bool) := [("true", true), ("false", false)]

/-- The clause a row records. -/
def Clause.ofRow (row : Datum) : Option Clause := do
  let verb ← row.feature? "verb"
  let agent ← row.feature? "agent"
  let patient ← row.feature? "patient"
  return .of verb agent patient (row.feature? "particle" <|> row.feature? "pp")

/-! ### Word order and convergence (§3, §5) -/

/-- A word-order row's configuration: its clause, the analysis that derives its string, and
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
    (row.parse? "evacuated" bools).getD false⟩

theorem order_rows : ∀ row ∈ Examples.all, ∀ o ∈ Order.ofRow row,
    (row.judgment ≠ .ungrammatical ↔ o.clause.Converges o.analysis o.evacuated) := by
  decide +kernel

/-! ### C-command and binding across the by-phrase (§3, §7, §9, §10) -/

/-- The two positions the tests relate are the external argument and the third element of VP. -/
inductive Position
  | external | pp
  deriving DecidableEq, Fintype, Repr

/-- The leaf at a position. -/
def Clause.at? (p : Clause) : Position → Option LexicalItem.Token
  | .external => some p.agent
  | .pp => p.extra

/-- The level at which a binding condition is evaluated, the surface or any stage of the
derivation, reconstruction included. -/
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

/-- The dependencies the rows test are a negative polarity item, *the other*, a bound variable,
a reflexive, a pronoun and a name. -/
inductive Dependency
  | npi | other | variable | reflexive | pronoun | name
  deriving DecidableEq, Repr

open Binding in
/-- The judgment a dependency predicts for the element at `y`, dependent on the element at `x`,
in the derivation `d` of `p`. A reflexive meets Condition A at the surface, or only at some
stage, which the paper grades `??`, (72); a bound variable is bound at the surface, or only at
some stage, graded `?`, (75); a pronoun meets Condition B at every stage, Principle B applying as
the DP is Merged, (83)–(84) (§9.3); a name meets Condition C at the surface, without
reconstruction (§9.2); a negative polarity item and *the other* need a c-commanding licensor at
the surface. -/
def Dependency.predict (dep : Dependency) (p : Clause) (d : Derivation) (x y : Position) :
    Judgment :=
  match dep with
  | .reflexive =>
      if (Level.surface.configuration p d).Condition (pair x y) ∅ y .reflexive then .acceptable
      else if (Level.anyStage.configuration p d).Condition (pair x y) ∅ y .reflexive then
        .questionable
      else .ungrammatical
  | .variable =>
      if (Level.surface.configuration p d).Bound (pair x y) y then .acceptable
      else if (Level.anyStage.configuration p d).Bound (pair x y) y then .marginal
      else .ungrammatical
  | .pronoun =>
      if (Level.anyStage.configuration p d).Condition (pair x y) ∅ y .pronoun then .acceptable
      else .ungrammatical
  | .name =>
      if (Level.surface.configuration p d).Condition (pair x y) ∅ y .rExpression then .acceptable
      else .ungrammatical
  | _ => if (Level.surface.configuration p d).commands x y then .acceptable else .ungrammatical

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
  return ⟨← Clause.ofRow row, ← row.parse? "evacuated" bools,
    ← row.parse? "dependency" [("npi", Dependency.npi), ("other", .other), ("variable", .variable),
      ("reflexive", .reflexive), ("pronoun", .pronoun), ("name", .name)],
    ← row.parse? "antecedent" positions, ← row.parse? "dependent" positions⟩

/-- The PartP-movement derivation of the configuration, with the PP evacuated or not. -/
def Licensing.derivation (c : Licensing) : Derivation := c.clause.passive .partP c.evacuated

/-- On the rows' derivations reconstruction to a stage is binding at the copy object
(`Derivation.bindsAtSomeStage_iff_bindsAtLF`): one token c-commands another at some stage exactly
when some copy of it does. -/
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

/-- The judgment the configuration predicts on its derivation. -/
def Licensing.predict (c : Licensing) : Judgment :=
  c.dependency.predict c.clause c.derivation c.antecedent c.dependent

/-- The [barss-lasnik-1986] tests (10), Principle A (72), (74), the bound variable (75), Principle B
(80) and Principle C (85) follow from the position of the PP. -/
theorem licensing_rows : ∀ row ∈ Examples.all, ∀ c ∈ Licensing.ofRow row,
    c.predict = row.judgment := by
  decide

/-- Principle B fits the pronoun judgments exactly when it holds at every stage, since at the
surface it would admit (80a). -/
theorem principleB_anyStage (ℓ : Level) :
    (∀ row ∈ Examples.all, ∀ c ∈ Licensing.ofRow row, c.dependency = .pronoun →
      (row.judgment = .acceptable ↔ (ℓ.configuration c.clause c.derivation).Condition
        (Binding.pair c.antecedent c.dependent) ∅ c.dependent .pronoun)) ↔ ℓ = .anyStage := by
  cases ℓ <;> decide

/-! ### Participle licensing (§3, (23)–(28)) -/

/-- The auxiliary over the participle: *have*, *be*, or none, as in a participial modifier. -/
inductive Auxiliary
  | have | be | bare
  deriving DecidableEq, Repr

/-- A participle clause: its auxiliary and whether a VoiceP is present. -/
structure Participle where
  /-- The auxiliary. -/
  auxiliary : Auxiliary
  /-- Whether a Voice head is present. -/
  voiceP : Bool

/-- A participle must be licensed by exactly one of *have*, which c-selects it, and Voice, which
attracts it, (24)–(25): (24) requires one, a participle Voice has licensed cannot also be
checked by *have*, and *be* imposes nothing (§3). -/
def Participle.Licensed (c : Participle) : Prop := Xor (c.auxiliary = .have) c.voiceP

instance (c : Participle) : Decidable c.Licensed := inferInstanceAs (Decidable (Xor _ _))

/-- The configuration a row records. -/
def Participle.ofRow (row : Datum) : Option Participle := do
  guard (row.feature? "construction" = some "participle")
  return ⟨← row.parse? "auxiliary" [("have", Auxiliary.have), ("be", .be), ("none", .bare)],
    ← row.parse? "voiceP" bools⟩

/-- The auxiliary paradigm (23) and the participial modifiers (27): a participle clause is
acceptable exactly when its participle has one licenser. -/
theorem participle_rows : ∀ row ∈ Examples.all, ∀ c ∈ Participle.ofRow row,
    (row.judgment = .acceptable ↔ c.Licensed) := by
  decide

end Collins2005
