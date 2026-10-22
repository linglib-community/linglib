module

public import Mathlib.Data.Fin.VecNotation
public import Linglib.Data.Examples.ColeHermon2008
public import Linglib.Fragments.TobaBatak.Voice
public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.ThetaRole
public import Linglib.Semantics.ArgumentStructure.Valency
public import Linglib.Syntax.Binding.Basic
public import Linglib.Syntax.Minimalist.Copy.Replay
public import Linglib.Syntax.Minimalist.Linearization.ChainReduction
public import Linglib.Syntax.Minimalist.Derivation.Freezing
public import Linglib.Syntax.Minimalist.Derivation.Reconstruction
public import Linglib.Syntax.Minimalist.Derivation.Remnant
public import Linglib.Syntax.Minimalist.Copy.Chain

/-!
# Cole and Hermon 2008: VP raising in a VOS language

Toba Batak is verb-initial: the unmarked clause is V-O-S, with indirect objects and adverbials
after the subject; direct objects and passive agents cannot be extracted while subjects,
indirect objects and adverbials can; and the active subject binds a reflexive object, the
passive agent a reflexive passive subject and, on the authors' own fieldwork, the passive
subject a reflexive passive agent, while the active object cannot bind a reflexive subject. The
paper derives all three from one derivation. The verb adjoins to Voice, the indirect object and
then the subject raise out of VoiceP to specifiers of functional heads, and the remnant VoiceP
raises over them, so word order is the order of extraction.

Whatever is still inside VoiceP when it raises is frozen there, so the object and the passive
agent, which never leave, cannot be extracted. Binding requires c-command at some stage of the
derivation, so the passive agent binds from the base and the passive subject after it raises
past the agent, while the active object never c-commands the subject. Schachter and Sugamoto's
Semantic Hierarchy Condition, actor over patient over dative, licenses the passive agent but
cannot separate the passive subject as antecedent, acceptable if less usual (Table 1's Type
B), from the active object as antecedent, ill-formed for every speaker (Type C); surface
c-command fits neither VOS passive and reconstruction to the last stage before VoiceP raises
only one of them.

Surface SVO clauses raise the subject once more, past the fronted VoiceP, so they freeze the
object as VOS clauses do, against the hypothesis that VoiceP stays in place. The sides at
which Merge attaches the material inside vP change neither the derived objects nor the
surface order, which the paper takes as grounds to propose that Merge is unordered and order
a by-product of Move. English, whose passive agent is an adjunct below the patient, lets the
patient bind it but never the converse.

The derivation is a `Derivation` on the syntactic-object carrier, freezing and binding at a
stage are the substrate's `Derivation.ObeysFreezing`, `CCommandsAt` and `BindsAtSomeStage`, and the
paper's examples are the rows: `vos_remnant` says that the raised VoiceP is a remnant,
`vos_hypothesis_only` and `derivational_only` single out, among the candidate analyses of word
order and of binding, the paper's own, `Licenses.derivational` shows the paper's binding
condition the weakest of the configurational ones, `table1` derives its three grades,
`stageAt_sides` and `surface_sides` are the §6 claim over every attachment choice, and
`english_passive` the §7 contrast.

## Implementation notes

* The clause is a token of the paper's transitive frame on the carrier; the substrate's
  clause types serve other theories (Landau's inflection–complementizer pair, valency
  frames). Its slots are the two positions of
  vP, `ArgPosition`, extended by the ditransitive goal, and the paper's roles are read off
  them.
* Voice and v are separate heads (fn. 20). The carrier has no head adjunction: the verb and
  then Voice re-Merge at the VoiceP root, standing in for the two raisings of (51)–(52) that
  the paper draws as one right adjunction (53), so the raised VoiceP is
  `{Voice, {V, {t, vP}}}` rather than a complex head over vP; nothing about the DPs depends
  on the difference. The functional heads F, whether T or Asp (fn. 22), are `Cat.T`; the
  paper's unfilled XP in Spec,VoiceP is omitted.
* The replay externalizes leaf Merge only, so a goal PP enters as one leaf, as the paper
  fronts it. Wh-fronting is C's Merge and the raising of the argument to its specifier, and
  Freezing reads the movers, so the remnant, carrying the evacuees' traces, freezes only what
  stayed in it; fn. 18's caveat on extraction from moved complements is the paper's.
* Binding at a stage is decided on the replay, which forgets to the derivation's own stage; a
  stage whose replay fails c-commands nothing, and the surface-order theorems witness that
  every derivation here replays.
* The rows record their configuration in paper features; the theorems decode it into a
  schematic clause and compare the derivation's prediction with the row's judgment.

## TODO

* Adverbials ((15)–(16), (47)–(48)), which fn. 25 evacuates like the goal, the NP- and
  PP-internal antecedents of §3.6 ((30)–(34)) and the object–goal data of §3.4 ((18)–(20),
  (22)–(23)) are not modelled, since a PP is a leaf.
* Fn. 28 offers two readings of the Type A over Type B preference, a preference for
  reconstruction or the Semantic Hierarchy as a separate constraint; only the second is
  formalized.
* The paper's conditional remark that its English passive excludes Collins's smuggling
  derivation is prose; a smuggling derivation on the carrier belongs with Collins 2005.

## References

* [P. Cole and G. Hermon, *VP Raising in a VOS Language* (2008)][cole-hermon-2008]
* [S. Chung, *Properties of VOS Languages* (2006)][chung-2006]
* [P. Schachter, *Semantic-Role-Based Syntax in Toba Batak* (1984)][schachter-1984]
* [N. Sugamoto, *Reflexives in Toba Batak* (1984)][sugamoto-1984]
* [R. K. Larson, *On the Double Object Construction* (1988)][larson-1988]
* [C. Collins, *A Smuggling Approach to the Passive in English* (2005)][collins-2005]
-/

@[expose] public section

open ArgumentStructure

namespace ColeHermon2008

open Minimalist SyntacticObject

/-! ### The clause and its derivations (§4.1–§4.2) -/

/-- The slots a clause's arguments fill are the two core positions of vP, the external one the
agent's and the internal one the patient's, and the goal of a ditransitive. -/
inductive Arg
  | core (p : ArgumentStructure.ArgPosition)
  | goal
  deriving DecidableEq, Fintype, Repr

/-- The role the slot bears in the paper's clauses, the Semantic Hierarchy's actor, patient and
dative. -/
def Arg.role : Arg → ThetaRole
  | .core .external => .agent
  | .core .internal => .patient
  | .goal => .goal

/-- A transitive clause records its voice, verb, agent and patient, and the goal PP of a
ditransitive, which enters as one leaf. -/
structure Clause where
  /-- The voice, which picks the pivot. -/
  voice : Voice
  /-- The verb, the derivation's initial object. -/
  verb : LexicalItem.Token
  /-- The agent, Merged as the specifier of vP. -/
  agent : LexicalItem.Token
  /-- The patient, the verb's complement or, in a ditransitive, the specifier of VP. -/
  patient : LexicalItem.Token
  /-- The goal PP of a ditransitive, one leaf. -/
  goal : Option LexicalItem.Token

/-- The silent light verb. -/
def v₀ : LexicalItem.Token := ⟨.of .v [], 6⟩

/-- The `i`-th functional head F, for `i ≥ 1`. -/
def F (i : ℕ) : LexicalItem.Token := ⟨.of .T [], 6 + i⟩

/-- The complementizer, whose specifier a fronted wh-phrase raises to. -/
def c₀ : LexicalItem.Token := ⟨.of .C [], 0⟩

/-- The side at which each of the five base Merges attaches its item. -/
abbrev Sides := Fin 5 → Edge

namespace Clause

/-- A clause from its words, the tokens numbered verb, agent, patient and goal after the voice
head. -/
def of (voice : Voice) (verb agent patient : String) (goal : Option String := none) :
    Clause :=
  ⟨voice, ⟨.of .V [] (phonForm := verb), 2⟩, ⟨.of .N [] (phonForm := agent), 3⟩,
    ⟨.of .N [] (phonForm := patient), 4⟩,
    goal.map fun g => ⟨.of .P [] (phonForm := g), 5⟩⟩

variable (c : Clause)

/-- The voice head, *mang-* or *di-*. -/
def voiceHead : LexicalItem.Token :=
  ⟨.of .Voice [] (phonForm := Morphology.Morph.surface c.voice.marker), 1⟩

/-- The argument as a token, the goal when there is one. -/
def arg? : Arg → Option LexicalItem.Token
  | .core .external => some c.agent
  | .core .internal => some c.patient
  | .goal => c.goal

/-- The pivot is the argument the voice raises to subject position, the agent in the active and
the patient in the passive, the slot the voice selects. -/
def pivot : LexicalItem.Token :=
  if c.voice.pivot = some ArgumentFrame.Slot.external then c.agent else c.patient

/-- The paper's own trees (50) and (57) put complements on the right, and the light verb, the
agent, Voice and, in a ditransitive, the patient, [larson-1988]'s specifier of VP, on the
left. -/
def paperSides : Sides :=
  ![.right, if c.goal.isSome then .left else .right, .left, .left, .left]

/-- In the base (50), (57), `{Voice, {Agent, {v, VP}}}`, the verb takes the patient, or the goal
and then the patient, then the light verb, the agent and Voice, each Merge on the side `σ`
gives. -/
def base (σ : Sides) : List Step :=
  c.goal.toList.map (Step.em (σ 0)) ++
    [.em (σ 1) c.patient, .em (σ 2) v₀, .em (σ 3) c.agent, .em (σ 4) c.voiceHead]

/-- The verb adjoins to Voice, (51)–(52), as the verb raises and Voice raises over it. -/
def verbToVoice : List Step := [.im c.verb, .im c.voiceHead]

/-- The goal, then the pivot, raise to specifiers of F, (59)–(60), (63)–(64), (72)–(73), the
order of extraction that places the goal after the subject. -/
def evacuate : List Step :=
  (c.goal.toList.flatMap fun pp => [.em .left (F 1), .im pp]) ++ [.em .left (F 2), .im c.pivot]

/-- The remnant VoiceP that raises, (55), (61), has Voice and the verb over their traces, and
the pivot and the goal replaced by theirs. -/
def remnant : LinearizedSyntacticObject :=
  let leaf := LinearizedSyntacticObject.leaf
  let trace := LinearizedSyntacticObject.traceOf
  let stranded (tok : LexicalItem.Token) := if tok = c.pivot then trace tok else leaf tok
  let vp : LinearizedSyntacticObject := match c.goal with
    | some pp => {stranded c.patient, {trace c.verb, trace pp}}
    | none => {trace c.verb, stranded c.patient}
  {leaf c.voiceHead, {leaf c.verb, {trace c.voiceHead, {stranded c.agent, {leaf v₀, vp}}}}}

/-- `svoStage` is the derivation up to the last stage before VoiceP raises, an SVO stage, as in
(54), (60), (64), (73) and (76). -/
def svoStage (σ : Sides := c.paperSides) : Derivation :=
  ⟨c.verb, c.base σ ++ c.verbToVoice ++ c.evacuate⟩

/-- In the VOS derivation, (55), (61), (65), (74), (77), the remnant VoiceP raises over the
evacuated goal and pivot. -/
def vos (σ : Sides := c.paperSides) : Derivation :=
  (c.svoStage σ).append [.em .left (F 3), .im c.remnant]

/-- In the SVO derivation under the VOS Hypothesis, (83)–(84), the pivot raises once more, past
the fronted VoiceP. -/
def svo (σ : Sides := c.paperSides) : Derivation :=
  (c.vos σ).append [.em .left (F 4), .im c.pivot]

/-- In the SVO derivation under the SVO Hypothesis (§5), for which the paper draws no tree, the
pivot raises and VoiceP, the goal inside it, stays. -/
def svoInPlace (σ : Sides := c.paperSides) : Derivation :=
  ⟨c.verb, c.base σ ++ c.verbToVoice ++ [.em .left (F 2), .im c.pivot]⟩

/-- The marked V-O-IO-S order (14), the pivot extracted before the goal; fn. 25 derives the
adverbial (16) the same way. -/
def vois (σ : Sides := c.paperSides) : Derivation :=
  ⟨c.verb, c.base σ ++ c.verbToVoice ++ [.em .left (F 1), .im c.pivot] ++
    (c.goal.toList.flatMap fun pp => [.em .left (F 2), .im pp]) ++
    [.em .left (F 3), .im c.remnant]⟩

end Clause

/-! ### Word order (§3.1, §3.3, §4.1, §4.2, §5) -/

/-- (49) *Mang-ida si-Mary si-John* 'John saw Mary'. -/
def ex49 : Clause := .of TobaBatak.actorVoice "ida" "si-John" "si-Mary"

/-- (56) *Mang-alean buku si-John tu si-Mary* 'John gave a book to Mary'. -/
def ex56 : Clause := .of TobaBatak.actorVoice "alean" "si-John" "buku" "tu si-Mary"

/-- (13) without *sada* 'one', *Di-lean si-John buku tu si-Mary* 'The book was given to Mary by
John', and (14). -/
def ex13 : Clause := .of TobaBatak.objectVoice "lean" "si-John" "buku" "tu si-Mary"

/-- (67) *Di-ida si-Torus dirina* 'Himself was seen by Torus'. -/
def ex67 : Clause := .of TobaBatak.objectVoice "ida" "si-Torus" "dirina"

/-- (81) *Dakdanak-on mang-atuk biang-i* 'This boy hit the dog'. -/
def ex81 : Clause := .of TobaBatak.actorVoice "atuk" "dakdanak-on" "biang-i"

/-- (85) *Si-John mang-alean aha tu si-Mary* 'What did John give to Mary?'. -/
def ex85 : Clause := .of TobaBatak.actorVoice "alean" "si-John" "aha" "tu si-Mary"

/-- The monotransitive VOS clause (49) and the passive (67). -/
theorem vos_orders :
    ex49.vos.surfacePhon = ["mang-", "ida", "si-Mary", "si-John"] ∧
      ex67.vos.surfacePhon = ["di-", "ida", "si-Torus", "dirina"] := by
  decide

/-- The ditransitive V-O-S-IO clause (56), the goal evacuated before the subject. -/
theorem ex56_vosi :
    ex56.vos.surfacePhon = ["mang-", "alean", "buku", "si-John", "tu si-Mary"] := by decide

/-- The passive (13) and, with the subject evacuated first, the marked (14). -/
theorem ex13_orders :
    ex13.vos.surfacePhon = ["di-", "lean", "si-John", "buku", "tu si-Mary"] ∧
      ex13.vois.surfacePhon = ["di-", "lean", "si-John", "tu si-Mary", "buku"] := by
  decide

/-- In both orders of (81), the SVO derivation raises the subject past the fronted VoiceP. -/
theorem ex81_orders :
    ex81.vos.surfacePhon = ["mang-", "atuk", "biang-i", "dakdanak-on"] ∧
      ex81.svo.surfacePhon = ["dakdanak-on", "mang-", "atuk", "biang-i"] := by
  decide

/-- The SVO ditransitive (85), S-V-O-IO. -/
theorem ex85_svoi :
    ex85.svo.surfacePhon = ["si-John", "mang-", "alean", "aha", "tu si-Mary"] := by decide

/-- VoiceP raising is remnant movement (§4.1–§4.2): the raised VoiceP holds the traces of the
verb, Voice, the pivot and, in (56), the goal. -/
theorem vos_remnant :
    ex49.vos.IsRemnantStep (ex49.svoStage.length + 1) ∧
      ex56.vos.IsRemnantStep (ex56.svoStage.length + 1) := by
  decide

/-! ### Copies -/

/-- Under the copy theory the VOS derivation of (49) leaves its movers in place: its copy object has
three copies of the pivot, at its landing site and in both copies of the raised VoiceP, and four of
the verb, two in each VoiceP. -/
example :
    ex49.vos.copyObject?.map (fun C ↦ (C.terms.count ↑ex49.pivot, C.terms.count ↑ex49.verb)) =
      some (3, 4) := by
  decide +kernel

/-- No token of (49) is merged twice, so its externalization pronounces each once, chain reduction
deleting the other copies. -/
example : (ex49.vos.surfaceTokens : Multiset _) = ex49.vos.lexTokens :=
  Derivation.coe_surfaceTokens (by decide +kernel) (by decide +kernel)

/-- The raised remnant carries the trace of the pivot away from its pronounced copy, so in the
externalized object that trace has no antecedent: a chain read off the traces breaks under
remnant movement. -/
example :
    (ex49.vos.externalize?.map fun t ↦ (orphanTraces t).map (·.2)) = some [ex49.pivot] := by
  decide +kernel

/-! ### Every clause goes through a VOS stage (§5) -/

/-- The SVO derivation extends the VOS derivation. -/
theorem svo_take_vos (c : Clause) (σ : Sides) : (c.svo σ).take (c.vos σ).length = c.vos σ :=
  Derivation.take_length_append _ _

/-- Freezing is the same in SVO and VOS clauses: the further raising of the pivot, a leaf,
freezes nothing. -/
theorem frozen_svo_iff (c : Clause) (σ : Sides) (x : SyntacticObject) :
    (c.svo σ).Frozen x ↔ (c.vos σ).Frozen x := by
  simp [Clause.svo, Derivation.frozen_append_iff]

/-! ### The rows -/

/-- The word order of a clause. -/
inductive WordOrder
  | vos | svo
  deriving DecidableEq, Repr

/-- The two analyses of SVO clauses (§5) are that every clause passes through VOS and that
VoiceP stays in place in SVO clauses. -/
inductive OrderHypothesis
  | vosHypothesis | svoHypothesis
  deriving DecidableEq, Repr

/-- The derivation of a clause in the given order under the hypothesis. -/
def Clause.derivation (c : Clause) : OrderHypothesis → WordOrder → Derivation
  | _, .vos => c.vos
  | .vosHypothesis, .svo => c.svo
  | .svoHypothesis, .svo => c.svoInPlace

/-- The value of a row's feature, read through a table; `List.lookup` keeps key and value in
one universe. -/
def voices : List (String × Voice) :=
  [("active", TobaBatak.actorVoice), ("passive", TobaBatak.objectVoice)]
def orders : List (String × WordOrder) := [("VOS", .vos), ("SVO", .svo)]
def args : List (String × Arg) :=
  [("agent", .core .external), ("patient", .core .internal), ("goal", .goal)]

/-- Toba Batak's Glottocode. -/
def tobaBatak : Glottocode := "bata1289"

/-- English's Glottocode. -/
def english : Glottocode := "stan1293"

/-! ### Extraction (§3.2, §4, §5) -/

/-- An extraction datum's configuration is a wh-phrase in the given argument slot, fronted or
in situ, in a clause of the given voice, order and transitivity. -/
structure Extraction where
  /-- The clause's voice. -/
  voice : Voice
  /-- The clause's word order. -/
  order : WordOrder
  /-- Whether the clause has a goal PP. -/
  ditransitive : Bool
  /-- The argument slot the wh-phrase fills. -/
  extracted : Arg
  /-- Whether the wh-phrase is fronted rather than in situ. -/
  fronted : Bool

namespace Extraction

/-- A schematic clause of the configuration. -/
def clause (e : Extraction) : Clause :=
  .of e.voice "V" "Agent" "Patient" (if e.ditransitive then some "PP" else none)

/-- Under a hypothesis, a fronted wh-phrase is predicted licit exactly when its fronting to
Spec,CP obeys Freezing, and a wh-phrase in situ is unconstrained. -/
def Licit (e : Extraction) (hyp : OrderHypothesis) : Prop :=
  e.fronted → ∃ x ∈ e.clause.arg? e.extracted,
    ((e.clause.derivation hyp e.order).append [.em .left c₀, .im x]).ObeysFreezing

instance (e : Extraction) (hyp : OrderHypothesis) : Decidable (e.Licit hyp) := by
  unfold Licit; infer_instance

/-- The configuration a row records. -/
def ofRow (row : Datum) : Option Extraction := do
  guard (row.feature? "construction" = some "extraction")
  return ⟨← row.parse? "voice" voices, ← row.parse? "order" orders,
    ← row.parse? "transitivity" [("monotransitive", false), ("ditransitive", true)],
    ← row.parse? "extracted" args, ← row.parse? "wh" [("fronted", true), ("inSitu", false)]⟩

end Extraction

/-- Only the VOS Hypothesis fits the extraction data ((7)–(10), (43)–(44), (85)–(88)). The
direct object and the passive agent, frozen in the fronted VoiceP, cannot be fronted in either
order, the goal, evacuated before VoiceP raises, can, and with VoiceP in place the object of an
SVO clause would be free. -/
theorem vos_hypothesis_only (hyp : OrderHypothesis) :
    (∀ row ∈ Examples.all, ∀ e ∈ Extraction.ofRow row,
      (row.judgment ≠ .ungrammatical ↔ e.Licit hyp)) ↔ hyp = .vosHypothesis := by
  cases hyp <;> decide

/-! ### Binding (§3.4–§3.7, §4.3) -/

/-- [schachter-1984]'s Semantic Hierarchy (28a) is actor > patient > dative. A role outranks
another, the antecedency condition (28b) of [schachter-1984] and [sugamoto-1984], when it comes
earlier in the list, `[r, s].Sublist roleHierarchy`; the relation is strict, as fn. 14 reads it,
since only then does the absence of dative antecedents follow. -/
def roleHierarchy : List ThetaRole := [.agent, .patient, .goal]

/-- A binding datum's configuration is the pair of the antecedent's and the reflexive's
argument slots in a clause of the given voice and order. -/
structure Reflexivization where
  /-- The clause's voice. -/
  voice : Voice
  /-- The clause's word order. -/
  order : WordOrder
  /-- The argument slot of the antecedent. -/
  antecedent : Arg
  /-- The argument slot of the reflexive. -/
  reflexive : Arg

namespace Reflexivization

/-- A schematic clause of the configuration. -/
def clause (a : Reflexivization) : Clause := .of a.voice "V" "Agent" "Patient"

/-- The derivation of the clause, through VOS. -/
def derivation (a : Reflexivization) : Derivation := a.clause.derivation .vosHypothesis a.order

/-- The configuration a row records. -/
def ofRow (row : Datum) : Option Reflexivization := do
  guard (row.feature? "construction" = some "binding" ∧ row.language = tobaBatak)
  return ⟨← row.parse? "voice" voices, ← row.parse? "order" orders,
    ← row.parse? "antecedent" args, ← row.parse? "reflexive" args⟩

end Reflexivization

/-- The candidate binding conditions of §4.3 are c-command at the surface, at the last stage
before VoiceP raises and at some stage, and the Semantic Hierarchy Condition. -/
inductive BindingTheory
  | surface | lastSVOStage | derivational | semanticHierarchy
  deriving DecidableEq, Repr

/-- The configuration a candidate condition reads on the argument slots of one clause. The
three configurational candidates compare the slots' tokens by c-command at the surface, at the
last SVO stage or at some stage; the Semantic Hierarchy compares their roles in `roleHierarchy`. -/
def BindingTheory.configuration : BindingTheory → Reflexivization → Binding.Configuration Arg
  | .surface, a => .monoclausal a.clause.arg? fun x y ↦ a.derivation.BindsAtSurface x y
  | .lastSVOStage, a =>
      .monoclausal a.clause.arg? fun x y ↦ a.clause.svoStage.BindsAtSurface x y
  | .derivational, a => .monoclausal a.clause.arg? fun x y ↦ a.derivation.BindsAtSomeStage x y
  | .semanticHierarchy, _ => .monoclausal (some ·.role) fun r s ↦ [r, s].Sublist roleHierarchy

/-- A candidate licenses a configuration when, under the candidate's configuration, the
reflexive meets Condition A, coindexed with its antecedent alone. -/
def BindingTheory.Licenses (th : BindingTheory) (a : Reflexivization) : Prop :=
  (th.configuration a).Condition (Binding.pair a.antecedent a.reflexive) ∅ a.reflexive .reflexive

instance (th : BindingTheory) (a : Reflexivization) : Decidable (th.Licenses a) := by
  cases th <;> (unfold BindingTheory.Licenses BindingTheory.configuration; infer_instance)

/-- C-command at some stage licenses whatever c-command at the surface or at the last SVO stage
licenses, so the paper's condition is the weakest of the configurational candidates. -/
theorem BindingTheory.Licenses.derivational {th : BindingTheory} {a : Reflexivization}
    (hth : th ≠ .semanticHierarchy) (h : th.Licenses a) :
    BindingTheory.derivational.Licenses a := by
  obtain ⟨voice, order, antecedent, reflexive⟩ := a
  unfold BindingTheory.Licenses at h ⊢
  refine Binding.Configuration.condition_mono (Or.inl rfl) ?_ h
  cases th with
  | surface => exact Binding.Configuration.monoclausal_mono fun _ _ h ↦ h.bindsAtSomeStage
  | lastSVOStage =>
    refine Binding.Configuration.monoclausal_mono fun _ _ h ↦ ?_
    cases order
    · exact h.bindsAtSomeStage.append
    · exact h.bindsAtSomeStage.append.append
  | derivational => exact le_rfl
  | semanticHierarchy => exact absurd rfl hth

/-- Only c-command at some stage fits the binding data of Table 1 ((17), (21), (37), (62),
(66)–(68)). Surface c-command loses every VOS antecedent, (62) and both passive orders
(67)–(68), reconstruction to the last SVO stage loses the passive agent (67), and the Semantic
Hierarchy loses the passive subject ((37), (68)). -/
theorem derivational_only (th : BindingTheory) :
    (∀ row ∈ Examples.all, ∀ a ∈ Reflexivization.ofRow row,
      (row.judgment ≠ .ungrammatical ↔ th.Licenses a)) ↔ th = .derivational := by
  cases th <;> decide

/-- Table 1's grades. -/
inductive Grade
  | typeA | typeB | typeC
  deriving DecidableEq, Repr

/-- The grade of a configuration reads the Semantic Hierarchy Condition as an addition to
derivational binding rather than a substitute for it (§3.7). It is Type A when the antecedent
c-commands the reflexive at some stage and outranks it, Type B when it c-commands without
outranking, and Type C when it never c-commands. -/
def Reflexivization.grade (a : Reflexivization) : Grade :=
  if BindingTheory.derivational.Licenses a then
    if BindingTheory.semanticHierarchy.Licenses a then .typeA else .typeB
  else .typeC

/-- Each row has the grade Table 1 gives it. -/
theorem table1 : ∀ row ∈ Examples.all, ∀ a ∈ Reflexivization.ofRow row,
    ∀ g ∈ row.parse? "tableOne" [("A", Grade.typeA), ("B", .typeB), ("C", .typeC)],
      a.grade = g := by
  decide

/-- Stage by stage through the passive (67)–(68), (72)–(74) and (75)–(77), the agent c-commands
the patient once the verb has adjoined to Voice, stage 6, and not once the patient has raised,
the patient c-commands the agent once raised and not before, and neither does at the surface,
once VoiceP has raised. -/
theorem passive_stages :
    (ex67.vos.CCommandsAt 6 ex67.agent ex67.patient ∧
      ¬ ex67.vos.CCommandsAt ex67.svoStage.length ex67.agent ex67.patient) ∧
    (¬ ex67.vos.CCommandsAt 6 ex67.patient ex67.agent ∧
      ex67.vos.CCommandsAt ex67.svoStage.length ex67.patient ex67.agent) ∧
    (¬ ex67.vos.BindsAtSurface ex67.agent ex67.patient ∧
      ¬ ex67.vos.BindsAtSurface ex67.patient ex67.agent) := by
  decide

/-- The derivational condition is binding at the copy object: in (67) the patient c-commands the
agent at some stage exactly when some copy of the patient c-commands some copy of the agent. -/
example :
    ex67.vos.BindsAtSomeStage ↑ex67.patient ↑ex67.agent ↔
      ex67.vos.BindsAtLF ↑ex67.patient ↑ex67.agent :=
  Derivation.bindsAtSomeStage_iff_bindsAtLF (by decide) (by decide +kernel) (by decide)
    (by decide) (by decide +kernel)

/-! ### Merge is unordered (§6) -/

/-- Up to the sides of its Merges, the VOS derivation is one derivation. -/
theorem vos_leftward (c : Clause) (σ σ' : Sides) :
    (c.vos σ).leftward = (c.vos σ').leftward := by
  simp [Derivation.leftward, Derivation.append, Clause.vos, Clause.svoStage, Clause.base]

/-- The sides at which the base Merges attach change no stage of the derivation, so binding,
which reads the stages, cannot see them ((89)–(94)). -/
theorem stageAt_sides (c : Clause) (σ σ' : Sides) (n : ℕ) :
    (c.vos σ).stageAt n = (c.vos σ').stageAt n := by
  rw [← Derivation.stageAt_leftward, vos_leftward c σ σ', Derivation.stageAt_leftward]

/-- Nor can freezing, which reads the movers. -/
theorem frozen_sides (c : Clause) (σ σ' : Sides) (x : SyntacticObject) :
    (c.vos σ).Frozen x ↔ (c.vos σ').Frozen x := by
  rw [← Derivation.frozen_leftward_iff, vos_leftward c σ σ', Derivation.frozen_leftward_iff]

/-- Nor can the surface order (56), since every one of the thirty-two attachments, (57), (91)
and, up to the omitted XP, (89) among them, externalizes to V-O-S-IO. -/
theorem surface_sides (σ : Sides) :
    (ex56.vos σ).surfacePhon = ["mang-", "alean", "buku", "si-John", "tu si-Mary"] := by
  revert σ; decide +kernel

/-! ### English passives (§7) -/

def wasInjured : LexicalItem.Token := ⟨.of .V [] (phonForm := "was injured"), 21⟩
def theBoy : LexicalItem.Token := ⟨.of .N [] (phonForm := "the boy"), 22⟩
def byHimself : LexicalItem.Token := ⟨.of .P [] (phonForm := "by himself"), 23⟩

/-- In the English passive (97)–(98) of (95), the patient is [larson-1988]'s specifier of VP and
the agent an adjunct, a *by*-phrase leaf below it, with no argument in Spec,vP, since the passive
participle projects none; the patient raises to Spec,FP, Spec,TP in English. -/
def englishPassive : Derivation :=
  ⟨wasInjured,
    [.em .right byHimself, .em .left theBoy, .em .left v₀, .em .left (F 1), .im theBoy]⟩

/-- (95) externalizes. -/
theorem english_order :
    englishPassive.surfacePhon = ["the boy", "was injured", "by himself"] := by decide

/-- `englishPair?` is the pair a row's roles pick out in the English derivation, in which the
patient is the raised DP and the agent the *by*-phrase, which fills no core position. -/
def englishPair? (row : Datum) : Option (SyntacticObject × SyntacticObject) := do
  guard (row.feature? "construction" = some "binding" ∧ row.language = english)
  let slot (a : Arg) : Option SyntacticObject := match a.role with
    | .patient => some theBoy
    | .agent => some byHimself
    | _ => none
  let antecedent ← slot (← row.parse? "antecedent" args)
  let reflexive ← slot (← row.parse? "reflexive" args)
  return (antecedent, reflexive)

/-- In (95)–(96) the patient binds the agent, which never c-commands it. Raising the patient
reverses its c-command relation with the agent only when the agent is an argument above it, as
in Toba Batak; the paper remarks, without arguing it, that if this treatment of English is
right, [collins-2005]'s smuggling derivation, in which the passive agent is Merged as in the
active, cannot be maintained. -/
theorem english_passive : ∀ row ∈ Examples.all, ∀ p ∈ englishPair? row,
    (row.judgment ≠ .ungrammatical ↔ englishPassive.BindsAtSomeStage p.1 p.2) := by
  decide

end ColeHermon2008
