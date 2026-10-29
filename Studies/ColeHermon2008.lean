module

public import Mathlib.Data.Fin.VecNotation
public import Linglib.Data.Examples.ColeHermon2008
public import Linglib.Data.Examples.Gloss
public import Linglib.Fragments.TobaBatak.Voice
public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.ThetaRole
public import Linglib.Semantics.ArgumentStructure.Valency
public import Linglib.Syntax.Binding.Basic
public import Linglib.Syntax.Minimalist.Copy.Replay
public import Linglib.Syntax.Minimalist.Linearization.ChainReduction
public import Linglib.Syntax.Minimalist.Locality.Freezing
public import Linglib.Syntax.Minimalist.Derivation.Reconstruction
public import Linglib.Syntax.Minimalist.Derivation.Remnant
public import Linglib.Syntax.Minimalist.Copy.Chain
public import Linglib.Syntax.Minimalist.Label.RaisingHead
public import Studies.Collins2005

/-!
# Cole and Hermon (2008): VP Raising in a VOS Language

Toba Batak word order is the order in which constituents leave VoiceP: the verb adjoins to Voice,
the indirect object and then the subject raise to specifiers of functional heads, and the remnant
VoiceP raises over them. The derivation [pronounces the paper's VOS and SVO
clauses](##order_rows), and the sides at which Merge attaches inside vP [change none of its
stages](##stageAt_sides).
What stays inside the raised VoiceP is frozen, so [extraction from SVO clauses shows that they
too raise VoiceP](##vos_hypothesis_only). Binding is c-command at some stage of the derivation,
the only condition that [fits the reflexives of actives and passives](##derivational_only), and
it [separates the English passive from Collins's smuggling derivation](##adjunct_only).

## Implementation notes

* The slots of a clause are the two core positions of vP, `ArgPosition`, and the goal of a
  ditransitive, a PP that enters as one leaf; the paper's roles are read off the slots.
* Voice and v are separate heads (fn. 20). The carrier has no head adjunction: the verb and then
  Voice re-Merge at the VoiceP root, standing in for the two raisings of (51)–(52) that the paper
  draws as one right adjunction (53), so the raised VoiceP is `{Voice, {V, {t, vP}}}` rather than
  a complex head over vP. The functional heads F, whether T or Asp (fn. 22), are `Cat.T`, and
  the unfilled XP in Spec,VoiceP is omitted.
* A derivation is spelled out by `Morph.surface`, Voice as the prefix of its marker, which joins
  the verb after it.
* Wh-fronting is C's Merge and the raising of the argument to its specifier. Freezing reads the
  movers, so the remnant, carrying the evacuees' traces, freezes only what stayed in it; fn. 18's
  caveat on extraction from moved complements is the paper's.
* Binding at a stage is decided on the replay, which forgets to the derivation's own stage.
* The word-order rows record their words; the extraction and binding rows record their
  configuration, which the theorems decode into a schematic clause.

## Errata

* p. 159: "(28)–(39)" for (37)–(39), the passive subjects antecedent to passive agents.
* p. 190: the structure (97) is proposed for "an English passive like (96)", but it is the
  structure of (95); (99) is that of (96).
* p. 192: "(91)", twice, for (100); (91) is the unordered Toba Batak vP of §6.

## TODO

* Adverbials ((15)–(16), (47)–(48)), which fn. 25 evacuates like the goal, the NP- and
  PP-internal antecedents of §3.6 ((29)–(34)) and the object–goal data of §3.4 ((18)–(20),
  (22)–(23)) are not modelled, since a PP is a leaf.
* Fn. 28 offers two readings of the Type A over Type B preference, a preference for
  reconstruction or the Semantic Hierarchy as a separate constraint; only the second is
  formalized.
* The raising of the passive subject feeds reflexivization ((68), (76)), which the paper takes
  to show that Spec,FP is an A-position, against an A'-analysis of the corresponding Malagasy
  position ((78)–(80)); the carrier does not yet distinguish A- from A'-positions.

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

/-- The VoiceP (53), (58), (72), (75), in which the verb has adjoined to Voice, (51)–(52), as the
verb raises and Voice raises over it. -/
def voiceP (σ : Sides := c.paperSides) : Derivation :=
  ⟨c.verb, c.base σ ++ [.im c.verb, .im c.voiceHead]⟩

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
def svoStage (σ : Sides := c.paperSides) : Derivation := (c.voiceP σ).append c.evacuate

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
  (c.voiceP σ).append [.em .left (F 2), .im c.pivot]

/-- The marked V-O-IO-S order (14), the pivot extracted before the goal (p. 170); fn. 25 derives
the adverbial (16) the same way. Without a goal it is the VOS derivation. -/
def vois (σ : Sides := c.paperSides) : Derivation :=
  (c.voiceP σ).append ([.em .left (F 2), .im c.pivot] ++
    (c.goal.toList.flatMap fun pp => [.em .left (F 1), .im pp]) ++
    [.em .left (F 3), .im c.remnant])

theorem vois_eq_vos (h : c.goal = none) (σ : Sides) : c.vois σ = c.vos σ := by
  simp [vois, vos, svoStage, evacuate, h]

/-- The words a derivation of the clause pronounces: Voice spells out as the prefix of its
marker, which `Morph.surface` joins to the verb after it, and every other pronounced token as
itself. -/
def words (d : Derivation) : List (List Char) :=
  Gloss.tokens <| Morphology.Morph.surface <| d.surfaceTokens.flatMap fun t ↦
    if t = c.voiceHead then c.voice.marker else t.item.phonForm?.toList.map .root

end Clause

/-! ### Word order (§3.1, §3.3, §4.1–§4.2, §5) -/

/-- The word order of a clause, the unmarked V-O-S, the marked V-O-IO-S of (14), or S-V-O. -/
inductive WordOrder
  | vos | vois | svo
  deriving DecidableEq, Repr

/-- The two analyses of SVO clauses (§5) are that every clause passes through VOS and that
VoiceP stays in place in SVO clauses. -/
inductive OrderHypothesis
  | vosHypothesis | svoHypothesis
  deriving DecidableEq, Repr

/-- The derivation of a clause in the given order under the hypothesis. -/
def Clause.derivation (c : Clause) : OrderHypothesis → WordOrder → Derivation
  | _, .vos => c.vos
  | _, .vois => c.vois
  | .vosHypothesis, .svo => c.svo
  | .svoHypothesis, .svo => c.svoInPlace

/-- The value of a row's feature, read through a table; `List.lookup` keeps key and value in
one universe. -/
def voices : List (String × Voice) :=
  [("active", TobaBatak.actorVoice), ("passive", TobaBatak.objectVoice)]
def orders : List (String × WordOrder) := [("VOS", .vos), ("VOIS", .vois), ("SVO", .svo)]
def args : List (String × Arg) :=
  [("agent", .core .external), ("patient", .core .internal), ("goal", .goal)]

/-- Toba Batak's Glottocode. -/
def tobaBatak : Glottocode := "bata1289"

/-- English's Glottocode. -/
def english : Glottocode := "stan1293"

/-- A sentence of the word-order data is a clause and the order it is pronounced in. -/
structure Sentence where
  /-- The clause. -/
  clause : Clause
  /-- Its word order. -/
  order : WordOrder

namespace Sentence

/-- The sentence a word-order row records. -/
def ofRow (row : Datum) : Option Sentence := do
  guard (row.feature? "construction" = some "order")
  return ⟨.of (← row.parse? "voice" voices) (← row.feature? "verb") (← row.feature? "agent")
    (← row.feature? "patient") (row.feature? "goal"), ← row.parse? "order" orders⟩

/-- Under the hypothesis, the derivation of the sentence pronounces the words of `text`. -/
def Pronounces (s : Sentence) (hyp : OrderHypothesis) (text : String) : Prop :=
  s.clause.words (s.clause.derivation hyp s.order) = Gloss.tokens text

instance (s : Sentence) (hyp : OrderHypothesis) (text : String) :
    Decidable (s.Pronounces hyp text) := by
  unfold Pronounces; infer_instance

end Sentence

/-- The clauses of the word-order rows. -/
def clauses : List Clause := (Examples.all.filterMap Sentence.ofRow).map (·.clause)

/-- Under either hypothesis the derivation of each word-order row pronounces it, VOS and SVO
alike ((3)–(4), (13)–(14), (49), (56), (81)): word order cannot tell the hypotheses apart. -/
theorem order_rows (hyp : OrderHypothesis) :
    (∀ row ∈ Examples.all, ∀ s ∈ Sentence.ofRow row, s.Pronounces hyp row.primaryText) ∧
      Datum.ReadCount Sentence.ofRow Examples.all 9 := by
  cases hyp <;> decide +kernel

-- §4.1–§4.2, (55), (61)
theorem vos_remnant : ∀ c ∈ clauses,
    c.vos.IsRemnantStep (c.svoStage.length + 1) c.pivot ∧
      (∀ g ∈ c.goal, c.vos.IsRemnantStep (c.svoStage.length + 1) g) ∧
      ¬ c.vos.IsRemnantStep (c.svoStage.length + 1) c.verb ∧
      ¬ c.vos.IsRemnantStep (c.svoStage.length + 1) c.voiceHead := by
  decide +kernel

/-! ### Copies -/

/-- Under the copy theory the VOS derivation leaves its movers in place: its copy object has three
copies of the pivot, at its landing site and in both copies of the raised VoiceP, and four of the
verb, two in each VoiceP. -/
example : ∀ c ∈ clauses,
    c.vos.copyObject?.map (fun C ↦ (C.terms.count ↑c.pivot, C.terms.count ↑c.verb)) =
      some (3, 4) := by
  decide +kernel

/-- No token is merged twice, so the externalization pronounces each once, chain reduction
deleting the other copies. -/
example : ∀ c ∈ clauses, (c.vos.surfaceTokens : Multiset _) = c.vos.lexTokens := by
  have h : ∀ c ∈ clauses,
      c.vos.lexTokens.Nodup ∧ c.vos.replay?.map (·.stack) = some [] := by
    decide +kernel
  exact fun c hc ↦ Derivation.coe_surfaceTokens (h c hc).1 (h c hc).2

/-- The raised remnant carries the trace of the pivot away from its pronounced copy, so in the
externalized object that trace has no antecedent: a chain read off the traces breaks under
remnant movement. -/
example : ∀ c ∈ clauses, c.goal = none →
    (c.vos.externalize?.map fun t ↦ (orphanTraces .raising t).map (·.2)) = some [c.pivot] := by
  decide +kernel

/-! ### Every clause goes through a VOS stage (§5) -/

theorem svo_take_vos (c : Clause) (σ : Sides) : (c.svo σ).take (c.vos σ).length = c.vos σ :=
  Derivation.take_length_append _ _

theorem frozen_svo_iff (c : Clause) (σ : Sides) (x : SyntacticObject) :
    (c.svo σ).Frozen x ↔ (c.vos σ).Frozen x := by
  simp [Clause.svo, Derivation.frozen_append_iff]

/-! ### Extraction (§3.2, §4, §5) -/

/-- Where a wh-phrase is pronounced, fronted or in situ. -/
inductive WhPosition
  | fronted | inSitu
  deriving DecidableEq, Repr

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
  /-- Where the wh-phrase is pronounced. -/
  wh : WhPosition

namespace Extraction

/-- A schematic clause of the configuration. -/
def clause (e : Extraction) : Clause :=
  .of e.voice "V" "Agent" "Patient" (if e.ditransitive then some "PP" else none)

/-- Under a hypothesis, a fronted wh-phrase is predicted licit exactly when its fronting to
Spec,CP obeys Freezing, and a wh-phrase in situ is unconstrained. -/
def Licit (e : Extraction) (hyp : OrderHypothesis) : Prop :=
  e.wh = .fronted → ∃ x ∈ e.clause.arg? e.extracted,
    ((e.clause.derivation hyp e.order).append [.em .left c₀, .im x]).ObeysFreezing

instance (e : Extraction) (hyp : OrderHypothesis) : Decidable (e.Licit hyp) := by
  unfold Licit; infer_instance

/-- The configuration a row records. -/
def ofRow (row : Datum) : Option Extraction := do
  guard (row.feature? "construction" = some "extraction")
  return ⟨← row.parse? "voice" voices, ← row.parse? "order" orders,
    ← row.parse? "transitivity" [("monotransitive", false), ("ditransitive", true)],
    ← row.parse? "extracted" args,
    ← row.parse? "wh" [("fronted", WhPosition.fronted), ("inSitu", .inSitu)]⟩

end Extraction

/-- Only the VOS Hypothesis fits the extraction data ((7)–(10), (43)–(44), (85)–(88)): fronting the
object of an SVO clause is as ill formed as in a VOS clause, so SVO clauses too raise VoiceP. -/
theorem vos_hypothesis_only (hyp : OrderHypothesis) :
    (∀ e ∈ Examples.all, e.Fits Extraction.ofRow fun x ↦ .ofProp (x.Licit hyp)) ↔
      hyp = .vosHypothesis := by
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
    · rw [Reflexivization.derivation, Clause.derivation, Clause.vois_eq_vos _ rfl]
      exact h.bindsAtSomeStage.append
    · exact h.bindsAtSomeStage.append.append
  | derivational => exact le_rfl
  | semanticHierarchy => exact absurd rfl hth

/-- Only c-command at some stage fits the binding data of Table 1 ((17), (21), (37), (62), (66),
(67), (68)): the passive agent binds the passive subject before the subject raises past it, and
the subject binds the agent only after. -/
theorem derivational_only (th : BindingTheory) :
    (∀ e ∈ Examples.all, e.Fits Reflexivization.ofRow fun a ↦ .ofProp (th.Licenses a)) ↔
      th = .derivational := by
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

/-- The grade a row's Table 1 type records. -/
def tableOne? (row : Datum) : Option (Reflexivization × Grade) := do
  return (← Reflexivization.ofRow row,
    ← row.parse? "tableOne" [("A", Grade.typeA), ("B", .typeB), ("C", .typeC)])

-- Table 1
theorem table1 : (∀ row ∈ Examples.all, ∀ x ∈ tableOne? row, x.1.grade = x.2) ∧
    Datum.ReadCount tableOne? Examples.all 7 := by
  decide

-- (67), (68), (72)–(77)
theorem passive_stages : ∀ c ∈ clauses, c.voice = TobaBatak.objectVoice →
    (c.vos.CCommandsAt c.voiceP.length c.agent c.patient ∧
      ¬ c.vos.CCommandsAt c.svoStage.length c.agent c.patient) ∧
    (¬ c.vos.CCommandsAt c.voiceP.length c.patient c.agent ∧
      c.vos.CCommandsAt c.svoStage.length c.patient c.agent) ∧
    (¬ c.vos.BindsAtSurface c.agent c.patient ∧ ¬ c.vos.BindsAtSurface c.patient c.agent) := by
  decide +kernel

/-- The derivational condition is binding at the copy object: some token c-commands another at some
stage exactly when some copy of the first c-commands some copy of the second. -/
example : ∀ c ∈ clauses, ∀ x y : LexicalItem.Token, x ≠ y →
    (c.vos.BindsAtSomeStage ↑x ↑y ↔ c.vos.BindsAtLF ↑x ↑y) := by
  have h : ∀ c ∈ clauses, c.vos.lexTokens.Nodup ∧ (∀ step ∈ c.vos.steps, step.IsMerge) ∧
      (∀ step ∈ c.vos.steps, ∀ m ∈ step.mover?, m.val.value.isLeft) ∧ c.vos.replay?.isSome := by
    decide +kernel
  intro c hc x y hxy
  obtain ⟨hd, hm, hmv, hr⟩ := h c hc
  exact Derivation.bindsAtSomeStage_iff_bindsAtLF hxy hd hm hmv hr

/-! ### Merge is unordered (§6) -/

theorem vos_leftward (c : Clause) (σ σ' : Sides) :
    (c.vos σ).leftward = (c.vos σ').leftward := by
  simp [Derivation.leftward, Derivation.append, Clause.vos, Clause.svoStage, Clause.voiceP,
    Clause.base]

/-- The sides at which the base Merges attach change no stage of the derivation, so binding,
which reads the stages, cannot see them ((89)–(94)). -/
theorem stageAt_sides (c : Clause) (σ σ' : Sides) (n : ℕ) :
    (c.vos σ).stageAt n = (c.vos σ').stageAt n := by
  rw [← Derivation.stageAt_leftward, vos_leftward c σ σ', Derivation.stageAt_leftward]

theorem frozen_sides (c : Clause) (σ σ' : Sides) (x : SyntacticObject) :
    (c.vos σ).Frozen x ↔ (c.vos σ').Frozen x := by
  rw [← Derivation.frozen_leftward_iff, vos_leftward c σ σ', Derivation.frozen_leftward_iff]

-- (56), (57), (89), (91): all thirty-two attachments pronounce (56)
theorem surface_sides : ∃ s ∈ Sentence.ofRow Examples.ex56,
    ∀ σ : Sides, s.clause.words (s.clause.vos σ) = Gloss.tokens Examples.ex56.primaryText := by
  decide +kernel

/-! ### English passives (§7) -/

/-- The two analyses of the English passive: the agent an adjunct *by*-phrase below the patient,
(97)–(98), or an argument Merged in Spec,vP that the participle phrase smuggles the patient past,
as in [collins-2005]. -/
inductive EnglishAnalysis
  | adjunct | smuggling
  deriving DecidableEq, Repr

def wasInjured : LexicalItem.Token := ⟨.of .V [] (phonForm := "was injured"), 21⟩
def theBoy : LexicalItem.Token := ⟨.of .N [] (phonForm := "the boy"), 22⟩
def byHimself : LexicalItem.Token := ⟨.of .P [] (phonForm := "by himself"), 23⟩

/-- In the English passive (97)–(98) of (95), the patient is [larson-1988]'s specifier of VP and
the agent an adjunct, a *by*-phrase leaf below it, with no argument in Spec,vP, since the passive
participle projects none; the patient raises to Spec,FP, Spec,TP in English. -/
def englishPassive : Derivation :=
  ⟨wasInjured,
    [.em .right byHimself, .em .left theBoy, .em .left v₀, .em .left (F 1), .im theBoy]⟩

/-- [collins-2005]'s clause of (95), its agent *himself* Merged in Spec,vP under *by*. -/
def smugglingClause : Collins2005.Clause := .of "injured" "himself" "the boy"

namespace EnglishAnalysis

/-- The analysis's derivation of (95). -/
def derivation : EnglishAnalysis → Derivation
  | .adjunct => englishPassive
  | .smuggling => smugglingClause.passive .partP false

/-- The leaf of an argument slot in the analysis's derivation. -/
def leaf? : EnglishAnalysis → Arg → Option LexicalItem.Token
  | .adjunct, .core .internal => some theBoy
  | .adjunct, .core .external => some byHimself
  | .smuggling, .core .internal => some smugglingClause.patient
  | .smuggling, .core .external => some smugglingClause.agent
  | _, .goal => none

/-- The configuration the analysis reads on the argument slots, in which a slot commands another
when its leaf c-commands the other's at some stage. -/
def configuration (an : EnglishAnalysis) : Binding.Configuration Arg :=
  .monoclausal an.leaf? fun x y ↦ an.derivation.BindsAtSomeStage x y

/-- The analysis licenses a reflexive at the second slot antecedent to the first when the
reflexive meets Condition A, coindexed with its antecedent alone. -/
def Licenses (an : EnglishAnalysis) (p : Arg × Arg) : Prop :=
  an.configuration.Condition (Binding.pair p.1 p.2) ∅ p.2 .reflexive

instance (an : EnglishAnalysis) (p : Arg × Arg) : Decidable (an.Licenses p) := by
  unfold Licenses configuration; infer_instance

end EnglishAnalysis

/-- The antecedent and reflexive slots of an English binding row. -/
def englishPair? (row : Datum) : Option (Arg × Arg) := do
  guard (row.feature? "construction" = some "binding" ∧ row.language = english)
  return (← row.parse? "antecedent" args, ← row.parse? "reflexive" args)

-- (95), (97), (98)
theorem english_order (an : EnglishAnalysis) :
    (an.derivation.surfacePhon.flatMap Gloss.tokens).IsInfix
      (Gloss.tokens Examples.ex95.primaryText) := by
  cases an <;> decide +kernel

/-- Both analyses pronounce (95), but with binding as c-command at some stage only the adjunct
analysis fits (95)–(96): [collins-2005]'s agent c-commands the patient before the participle
phrase raises, so it would bind a reflexive passive subject, and "if our treatment of English is
correct, Collins's analysis cannot be maintained" (p. 193). -/
theorem adjunct_only (an : EnglishAnalysis) :
    (∀ e ∈ Examples.all, e.Fits englishPair? fun p ↦ .ofProp (an.Licenses p)) ↔
      an = .adjunct := by
  cases an <;> decide +kernel

end ColeHermon2008
