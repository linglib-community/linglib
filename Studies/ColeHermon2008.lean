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
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Cole and Hermon (2008): VP Raising in a VOS Language

Toba Batak word order is the order in which constituents leave VoiceP: the verb adjoins to Voice,
the indirect object and then the subject raise to specifiers of functional heads, and the remnant
VoiceP raises over them. So in every clause [only what has left VoiceP can be
extracted](##obeysFreezing_front_iff), [the patient binds the agent at some stage exactly when it
is the pivot](##bindsAtSomeStage_agent_patient), and the sides at which Merge attaches inside vP
[change no stage](##stageAt_sides). A sentence is licensed when some derivation pronounces it,
obeys Freezing and lets the antecedent bind the reflexive, and [only the VOS Hypothesis with
binding at some stage fits the judgments](##fits_iff); [the same binding rules out Collins's
smuggling passive for English](##adjunct_only).

## Implementation notes

* The slots of a clause are the two core positions of vP, `ArgPosition`, and the goal of a
  ditransitive, a PP that enters as one leaf; the paper's roles are read off the slots.
* Voice and v are separate heads (fn. 20). The carrier has no head adjunction: the verb and then
  Voice re-Merge at the VoiceP root, standing in for the two raisings of (51)–(52) that the paper
  draws as one right adjunction (53), so the raised VoiceP is `{Voice, {V, {t, vP}}}` rather than
  a complex head over vP. The two leaves are spelled out as the one word of the complex head, the
  verb with its voice's prefix. The functional heads F, whether T or Asp (fn. 22), are
  `Cat.T`, and the unfilled XP in Spec,VoiceP is omitted.
* A row records only what its translation and coindexation state: the words of its agent,
  patient and goal, and the antecedent of a reflexive, the other core argument. The verb is the
  remaining word and its prefix gives the voice, the actor voice when there is none, as on
  (21)'s *pa-ias-hon* (fn. 5); the order and the fronted argument are those of a derivation that
  pronounces the row. The focus particle *do* is set aside.
* Fronting is the Merge of C and the raising of an argument to its specifier. Freezing reads the
  movers, so the remnant, carrying the evacuees' traces, freezes only what stayed in it; fn. 18's
  caveat on extraction from moved complements is the paper's.
* Binding at a stage is decided on the replay, which forgets to the derivation's own stage.

## Errata

* p. 159: "(28)–(39)" for (37)–(39), the passive subjects antecedent to passive agents.
* p. 190: the structure (97) is proposed for "an English passive like (96)", but it is the
  structure of (95); (99) is that of (96).
* p. 162: (44) glosses *mang-atuk* 'ACT-see'; its translation and (43) have 'hit'.
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

/-- A core argument as the remnant holds it: the trace of the pivot, which has left, or the
argument itself, which has stayed. -/
def stranded (t : LexicalItem.Token) : LinearizedSyntacticObject :=
  if t = c.pivot then .traceOf t else .leaf t

/-- The remnant VoiceP that raises, (55), (61), has Voice and the verb over their traces, and
the pivot and the goal replaced by theirs. -/
def remnant : LinearizedSyntacticObject :=
  let vp : LinearizedSyntacticObject := match c.goal with
    | some pp => {c.stranded c.patient, {.traceOf c.verb, .traceOf pp}}
    | none => {.traceOf c.verb, c.stranded c.patient}
  {.leaf c.voiceHead, {.leaf c.verb, {.traceOf c.voiceHead, {c.stranded c.agent, {.leaf v₀, vp}}}}}

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

/-- The words a token spells out. The verb and Voice, the complex head of (53), are one word, the
verb with the voice's prefix, which `Morph.surface` writes; every other token is its own words. -/
def tokenWords (t : LexicalItem.Token) : List (List Char) :=
  if t = c.voiceHead then []
  else if t = c.verb then
    Gloss.tokens <| Morphology.Morph.surface <| c.voice.marker ++ [.root t.item.phonForm]
  else Gloss.tokens t.item.phonForm

/-- The words a derivation of the clause pronounces. -/
def words (d : Derivation) : List (List Char) := d.surfaceTokens.flatMap c.tokenWords

end Clause

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

/-! ### Every clause of a voice (§4)

Renaming the verb and the arguments of a clause renames its derivations, as long as the
functional heads stay fixed, so Freezing, remnant movement and c-command, all invariant under
renamings that preserve selection, depend on a clause only through its voice and whether it has a
goal, and what holds of the template of a voice holds of every clause of that voice. -/

namespace Clause

variable (c : Clause) {f : LexicalItem.Token → LexicalItem.Token}

/-- The clause with its verb and arguments renamed by `f`. -/
@[simps] def map (f : LexicalItem.Token → LexicalItem.Token) : Clause :=
  ⟨c.voice, f c.verb, f c.agent, f c.patient, c.goal.map f⟩

/-- The functional heads, which every clause of a voice shares. -/
def heads : List LexicalItem.Token := [c.voiceHead, v₀, F 1, F 2, F 3, F 4, c₀]

@[simp] theorem voiceHead_map : (c.map f).voiceHead = c.voiceHead := rfl

@[simp] theorem heads_map : (c.map f).heads = c.heads := rfl

theorem arg?_map (x : Arg) : (c.map f).arg? x = (c.arg? x).map f := by
  rcases x with (_ | _) | _ <;> rfl

theorem pivot_map : (c.map f).pivot = f c.pivot := by
  simp only [pivot, map_voice, map_agent, map_patient]
  split_ifs <;> rfl

@[simp] theorem paperSides_map : (c.map f).paperSides = c.paperSides := by
  simp [paperSides]

theorem stranded_map (hf : Function.Injective f) (t : LexicalItem.Token) :
    (c.map f).stranded (f t) = (c.stranded t).map f := by
  simp only [stranded, pivot_map, hf.eq_iff]
  split_ifs <;> simp


variable (hh : ∀ t ∈ c.heads, f t = t)
include hh

theorem voiceP_map (σ : Sides) : (c.map f).voiceP σ = (c.voiceP σ).map f := by
  have hv : f v₀ = v₀ := hh _ (by simp [heads])
  have hvh : f c.voiceHead = c.voiceHead := hh _ (by simp [heads])
  rcases c with ⟨_, _, _, _, _ | _⟩ <;>
    simp_all [voiceP, base, Derivation.map, Step.map]

theorem evacuate_map : (c.map f).evacuate = c.evacuate.map (Step.map f) := by
  have h1 : f (F 1) = F 1 := hh _ (by simp [heads])
  have h2 : f (F 2) = F 2 := hh _ (by simp [heads])
  rcases c with ⟨_, _, _, _, _ | _⟩ <;>
    simp_all [evacuate, Step.map, pivot_map]

theorem remnant_map (hf : Function.Injective f) : (c.map f).remnant = c.remnant.map f := by
  have hv : f v₀ = v₀ := hh _ (by simp [heads])
  have hvh : f c.voiceHead = c.voiceHead := hh _ (by simp [heads])
  simp only [remnant, map_goal, map_verb, map_agent, map_patient, voiceHead_map,
    stranded_map c hf]
  cases c.goal <;> simp [hv, hvh]

theorem svoStage_map (σ : Sides) : (c.map f).svoStage σ = (c.svoStage σ).map f := by
  simp [svoStage, voiceP_map c hh, evacuate_map c hh]

theorem vos_map (hf : Function.Injective f) (σ : Sides) :
    (c.map f).vos σ = (c.vos σ).map f := by
  have h3 : f (F 3) = F 3 := hh _ (by simp [heads])
  simp [vos, svoStage_map c hh, remnant_map c hh hf, Step.map, h3]

theorem svo_map (hf : Function.Injective f) (σ : Sides) :
    (c.map f).svo σ = (c.svo σ).map f := by
  have h4 : f (F 4) = F 4 := hh _ (by simp [heads])
  simp [svo, vos_map c hh hf, Step.map, h4, pivot_map]

theorem svoInPlace_map (σ : Sides) : (c.map f).svoInPlace σ = (c.svoInPlace σ).map f := by
  have h2 : f (F 2) = F 2 := hh _ (by simp [heads])
  simp [svoInPlace, voiceP_map c hh, Step.map, h2, pivot_map]

theorem vois_map (hf : Function.Injective f) (σ : Sides) :
    (c.map f).vois σ = (c.vois σ).map f := by
  have h1 : f (F 1) = F 1 := hh _ (by simp [heads])
  have h2 : f (F 2) = F 2 := hh _ (by simp [heads])
  have h3 : f (F 3) = F 3 := hh _ (by simp [heads])
  rcases c with ⟨_, _, _, _, _ | _⟩ <;>
    simp_all [vois, voiceP_map, remnant_map, Step.map, pivot_map]

theorem derivation_map (hf : Function.Injective f) (hyp : OrderHypothesis) (o : WordOrder) :
    (c.map f).derivation hyp o = (c.derivation hyp o).map f := by
  cases hyp <;> cases o <;>
    simp [derivation, vos_map c hh hf, vois_map c hh hf, svo_map c hh hf, svoInPlace_map c hh]

omit hh

/-- The template of a voice, with empty words and a goal when `g` holds. -/
def template (v : Voice) (g : Bool) : Clause := .of v "" "" "" (if g then some "" else none)

end Clause

/-- The renaming that takes the tokens of `T` to those of `c`, swapping the tokens that share an
index. -/
def Clause.renaming (T c : Clause) : Equiv.Perm LexicalItem.Token :=
  Equiv.swap T.verb c.verb * Equiv.swap T.agent c.agent * Equiv.swap T.patient c.patient *
    match T.goal, c.goal with
    | some a, some b => Equiv.swap a b
    | _, _ => 1

section Shape

variable (v : Voice) (verb agent patient : String) (goal : Option String)

local notation "T" => Clause.template v goal.isSome

local notation "C" => Clause.of v verb agent patient goal

local notation "ρ" => Clause.renaming T C

theorem of_eq_map : C = (T).map ρ := by
  rcases goal with _ | _ <;>
    simp [Clause.of, Clause.template, Clause.map, Clause.renaming, Equiv.swap_apply_of_ne_of_ne]

theorem renaming_preservesSelection : LexicalItem.Token.PreservesSelection ρ := by
  rcases goal with _ | _ <;>
    simp only [Clause.renaming, Clause.template, Clause.of, Option.map_some, Option.map_none,
      Option.isSome_some, Option.isSome_none, Equiv.Perm.coe_mul] <;>
    refine .comp (.comp (.comp ?_ ?_) ?_) ?_ <;>
    first
    | exact .id
    | exact .swap rfl rfl (by simp [LexicalItem.Token.bareTrace])
        (by simp [LexicalItem.Token.bareTrace])

theorem renaming_heads : ∀ t ∈ (T).heads, ρ t = t := by
  rcases goal with _ | _ <;>
    simp [Clause.heads, Clause.renaming, Clause.template, Clause.of, Clause.voiceHead, v₀, F, c₀,
      Equiv.swap_apply_of_ne_of_ne]

/-- Only what has left VoiceP can be extracted (§4, (61)): in every clause of a Toba Batak voice,
in every order under the VOS Hypothesis, fronting an argument obeys Freezing exactly when the
argument is the pivot or the goal. -/
theorem obeysFreezing_front_iff (hv : v = TobaBatak.actorVoice ∨ v = TobaBatak.objectVoice)
    (o : WordOrder) (x : Arg) : ∀ t ∈ (C).arg? x,
      (((C).derivation .vosHypothesis o).append [.em .left c₀, .im t]).ObeysFreezing ↔
        t = (C).pivot ∨ t ∈ (C).goal := by
  have hh := renaming_heads v verb agent patient goal
  have hf : Function.Injective ρ := Equiv.injective _
  have hc : ρ c₀ = c₀ := hh _ (by simp [Clause.heads])
  have happ (d : Derivation) (a : LexicalItem.Token) :
      (d.map ρ).append [.em .left c₀, .im ↑(ρ a)] = (d.append [.em .left c₀, .im ↑a]).map ρ := by
    simp [Step.map, hc]
  rw [of_eq_map v verb agent patient goal]
  simp only [Clause.arg?_map, Option.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Clause.derivation_map _ hh hf, happ,
    Derivation.obeysFreezing_map_iff hf, Clause.pivot_map, Clause.map_goal, hf.eq_iff]
  generalize goal.isSome = g
  clear happ hc hf hh
  rcases hv with rfl | rfl <;> cases g <;> cases o <;> rcases x with (_ | _) | _ <;>
    decide +kernel

/-- In every clause of a Toba Batak voice, in every order under either hypothesis, the agent
binds the patient at some stage, and the patient binds the agent at some stage exactly when it is
the pivot, as in the passive (§4.3, (72)–(77)). -/
theorem bindsAtSomeStage_agent_patient
    (hv : v = TobaBatak.actorVoice ∨ v = TobaBatak.objectVoice)
    (hyp : OrderHypothesis) (o : WordOrder) :
    ((C).derivation hyp o).BindsAtSomeStage (C).agent (C).patient ∧
      (((C).derivation hyp o).BindsAtSomeStage (C).patient (C).agent ↔
        (C).pivot = (C).patient) := by
  have hh := renaming_heads v verb agent patient goal
  have hf : Function.Injective ρ := Equiv.injective _
  have hsel := renaming_preservesSelection v verb agent patient goal
  have key (d : Derivation) (a b : LexicalItem.Token) :
      (d.map ρ).BindsAtSomeStage ↑(ρ a) ↑(ρ b) ↔ d.BindsAtSomeStage ↑a ↑b := by
    simpa using Derivation.bindsAtSomeStage_map_iff (d := d) (x := ↑a) (y := ↑b) hf hsel
  rw [of_eq_map v verb agent patient goal]
  simp only [Clause.derivation_map _ hh hf, Clause.map_agent, Clause.map_patient, key,
    Clause.pivot_map, hf.eq_iff]
  generalize goal.isSome = g
  clear key hsel hf hh
  rcases hv with rfl | rfl <;> cases g <;> cases hyp <;> cases o <;> decide +kernel

-- §4.1–§4.2, (55), (61)
theorem isRemnantStep_vos (hv : v = TobaBatak.actorVoice ∨ v = TobaBatak.objectVoice) :
    (C).vos.IsRemnantStep ((C).svoStage.length + 1) (C).pivot ∧
      (∀ g ∈ (C).goal, (C).vos.IsRemnantStep ((C).svoStage.length + 1) g) ∧
      ¬ (C).vos.IsRemnantStep ((C).svoStage.length + 1) (C).verb ∧
      ¬ (C).vos.IsRemnantStep ((C).svoStage.length + 1) (C).voiceHead := by
  have hh := renaming_heads v verb agent patient goal
  have hf : Function.Injective ρ := Equiv.injective _
  have key (i : ℕ) (a : LexicalItem.Token) :=
    Derivation.isRemnantStep_map_iff (d := (T).vos) (i := i) (h := a) hf
  have hvh : ρ (T).voiceHead = (T).voiceHead := hh _ (by simp [Clause.heads])
  rw [of_eq_map v verb agent patient goal]
  simp only [Clause.paperSides_map, Clause.vos_map _ hh hf, Clause.svoStage_map _ hh,
    Derivation.length_map, Clause.pivot_map, Clause.map_goal, Clause.map_verb,
    Clause.voiceHead_map, Option.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, key]
  rw [← hvh, key]
  generalize goal.isSome = g
  clear key hvh hf hh
  rcases hv with rfl | rfl <;> cases g <;> decide +kernel

-- (67), (68), (72)–(77)
theorem passive_stages (hv : v = TobaBatak.objectVoice) :
    ((C).vos.CCommandsAt (C).voiceP.length (C).agent (C).patient ∧
      ¬ (C).vos.CCommandsAt (C).svoStage.length (C).agent (C).patient) ∧
    (¬ (C).vos.CCommandsAt (C).voiceP.length (C).patient (C).agent ∧
      (C).vos.CCommandsAt (C).svoStage.length (C).patient (C).agent) ∧
    (¬ (C).vos.BindsAtSurface (C).agent (C).patient ∧
      ¬ (C).vos.BindsAtSurface (C).patient (C).agent) := by
  have hh := renaming_heads v verb agent patient goal
  have hf : Function.Injective ρ := Equiv.injective _
  have hsel := renaming_preservesSelection v verb agent patient goal
  have key (d : Derivation) (n : ℕ) (a b : LexicalItem.Token) :
      (d.map ρ).CCommandsAt n ↑(ρ a) ↑(ρ b) ↔ d.CCommandsAt n ↑a ↑b := by
    simpa using Derivation.cCommandsAt_map_iff (d := d) (n := n) (x := ↑a) (y := ↑b) hf hsel
  rw [of_eq_map v verb agent patient goal]
  simp only [Derivation.BindsAtSurface, Clause.paperSides_map, Clause.vos_map _ hh hf,
    Clause.svoStage_map _ hh, Clause.voiceP_map _ hh, Derivation.length_map, Clause.map_agent,
    Clause.map_patient, key]
  generalize goal.isSome = g
  clear key hsel hf hh
  subst hv
  cases g <;> decide +kernel

end Shape

/-! ### Sentences (§3) -/

/-- The other core argument, the patient for the agent and the agent for the patient; the goal
is its own. -/
def Arg.other : Arg → Arg
  | .core .external => .core .internal
  | .core .internal => .core .external
  | .goal => .goal

/-- The argument slots by the names the rows use. -/
def args : List (String × Arg) :=
  [("agent", .core .external), ("patient", .core .internal), ("goal", .goal)]

/-- Toba Batak's Glottocode. -/
def tobaBatak : Glottocode := .batakToba

/-- English's Glottocode. -/
def english : Glottocode := .english

/-- The words of a row's sentence, less the focus particle *do*, which no derivation builds. -/
def rowWords (row : Datum) : List (List Char) :=
  (row.glossedTokens.filter (·.2 ≠ "FOC")).flatMap (Gloss.tokens ·.1)

/-- The words of the arguments a row records. -/
def argumentWords (row : Datum) : List (List Char) :=
  ["agent", "patient", "goal"].flatMap fun k ↦ ((row.feature? k).map Gloss.tokens).getD []

/-- The voice and stem of a verb word: the Toba Batak voice whose prefix begins it, or, with no
prefix, the actor voice spelled out as nothing, as fn. 5 takes it to be on some verbs. -/
def voiceStem (w : List Char) : Voice × List Char :=
  match Gloss.split ['-'] w with
  | p :: rest =>
    match [TobaBatak.actorVoice, TobaBatak.objectVoice].find?
        (·.marker.map (·.form.toList) = [p]) with
    | some v => (v, (rest.intersperse ['-']).flatten)
    | none => (Voice.agentVoice, w)
  | [] => (Voice.agentVoice, w)

/-- A sentence is a clause, the words it is pronounced as, and the argument, if any, that
antecedes a reflexive, which is then the other core argument. -/
structure Sentence where
  /-- The clause. -/
  clause : Clause
  /-- The words. -/
  words : List (List Char)
  /-- The antecedent of the reflexive. -/
  antecedent : Option Arg

/-- An analysis of a sentence is the order its derivation takes and the argument, if any, that it
fronts to Spec,CP. -/
structure Analysis where
  /-- The order. -/
  order : WordOrder
  /-- The fronted argument. -/
  fronted : Option Arg
  deriving DecidableEq, Repr

/-- Every order with every choice of fronted argument. -/
def Analysis.all : List Analysis :=
  [WordOrder.vos, .vois, .svo].flatMap fun o ↦
    [none, some (Arg.core .external), some (.core .internal), some .goal].map (⟨o, ·⟩)

namespace Sentence

/-- The sentence of a Toba Batak row: the arguments are the words the row records for them, the
verb is the remaining word, and its prefix gives the voice. -/
def ofRow (row : Datum) : Option Sentence := do
  guard (row.language = tobaBatak)
  let [w] := (rowWords row).diff (argumentWords row) | none
  let (v, stem) := voiceStem w
  return ⟨.of v (String.ofList stem) (← row.feature? "agent") (← row.feature? "patient")
    (row.feature? "goal"), rowWords row, row.parse? "antecedent" args⟩

variable (s : Sentence) (hyp : OrderHypothesis) (a : Analysis)

/-- The derivation of the sentence under an analysis: the clause's derivation in its order and,
if an argument is fronted, the Merge of C and the argument's raising to its specifier. -/
def derivation : Derivation :=
  (s.clause.derivation hyp a.order).append <| match a.fronted.bind s.clause.arg? with
    | some t => [.em .left c₀, .im t]
    | none => []

/-- The derivation of the sentence under the analysis pronounces it. -/
def Pronounces : Prop :=
  (∀ x ∈ a.fronted, (s.clause.arg? x).isSome) ∧ s.clause.words (s.derivation hyp a) = s.words

instance : Decidable (s.Pronounces hyp a) := by
  unfold Pronounces; infer_instance

end Sentence

-- §5: some derivation pronounces each sentence under either hypothesis, ill formed or not
theorem parses (hyp : OrderHypothesis) :
    (∀ row ∈ Examples.all, ∀ s ∈ Sentence.ofRow row, ∃ a ∈ Analysis.all, s.Pronounces hyp a) ∧
      Datum.ReadCount Sentence.ofRow Examples.all 27 := by
  cases hyp <;> decide +kernel

/-! ### Binding (§3.4–§3.7, §4.3) -/

/-- [schachter-1984]'s Semantic Hierarchy (28a) is actor > patient > dative. A role outranks
another, the antecedency condition (28b) of [schachter-1984] and [sugamoto-1984], when it comes
earlier in the list, `[r, s].Sublist roleHierarchy`; the relation is strict, as fn. 14 reads it,
since only then does the absence of dative antecedents follow. -/
def roleHierarchy : List ThetaRole := [.agent, .patient, .goal]

/-- The candidate binding conditions of §4.3 are c-command at the surface, at the last stage
before VoiceP raises and at some stage, and the Semantic Hierarchy Condition. -/
inductive BindingTheory
  | surface | lastSVOStage | derivational | semanticHierarchy
  deriving DecidableEq, Repr

namespace BindingTheory

/-- The configuration a candidate reads on the argument slots of a clause derived by `d`. The
three configurational candidates compare the slots' tokens by c-command at the surface of `d`,
at the clause's last SVO stage or at some stage of `d`; the Semantic Hierarchy compares their
roles in `roleHierarchy`. -/
def configuration (c : Clause) (d : Derivation) : BindingTheory → Binding.Configuration Arg
  | .surface => .monoclausal c.arg? fun x y ↦ d.BindsAtSurface x y
  | .lastSVOStage => .monoclausal c.arg? fun x y ↦ c.svoStage.BindsAtSurface x y
  | .derivational => .monoclausal c.arg? fun x y ↦ d.BindsAtSomeStage x y
  | .semanticHierarchy => .monoclausal (some ·.role) fun r s ↦ [r, s].Sublist roleHierarchy

/-- A candidate licenses a reflexive antecedent to `x` in a clause derived by `d` when the
reflexive, the other core argument, meets Condition A, coindexed with `x` alone. -/
def Licenses (th : BindingTheory) (c : Clause) (d : Derivation) (x : Arg) : Prop :=
  (th.configuration c d).Condition (Binding.pair x x.other) ∅ x.other .reflexive

instance (th : BindingTheory) (c : Clause) (d : Derivation) (x : Arg) :
    Decidable (th.Licenses c d x) := by
  cases th <;> (unfold Licenses configuration; infer_instance)

-- p. 178: derivational binding is the weakest configurational condition
theorem Licenses.derivational {th : BindingTheory} {c : Clause} {d : Derivation} {x : Arg}
    (hth : th ≠ .semanticHierarchy) (hd : ∃ steps, d = c.svoStage.append steps)
    (h : th.Licenses c d x) : BindingTheory.derivational.Licenses c d x := by
  refine Binding.Configuration.condition_mono (Or.inl rfl) ?_ h
  cases th with
  | surface => exact Binding.Configuration.monoclausal_mono fun _ _ h ↦ h.bindsAtSomeStage
  | lastSVOStage =>
    obtain ⟨steps, rfl⟩ := hd
    exact Binding.Configuration.monoclausal_mono fun _ _ h ↦ h.bindsAtSomeStage.append
  | derivational => exact le_rfl
  | semanticHierarchy => exact absurd rfl hth

end BindingTheory

/-! ### The grammar (§4–§5) -/

/-- The grammar licenses a sentence when some derivation pronounces it, obeys Freezing, and lets
the antecedent bind the reflexive. -/
def Sentence.Licensed (s : Sentence) (hyp : OrderHypothesis) (th : BindingTheory) : Prop :=
  ∃ a ∈ Analysis.all, s.Pronounces hyp a ∧ (s.derivation hyp a).ObeysFreezing ∧
    ∀ x ∈ s.antecedent, th.Licenses s.clause (s.derivation hyp a) x

instance (s : Sentence) (hyp : OrderHypothesis) (th : BindingTheory) :
    Decidable (s.Licensed hyp th) := by
  unfold Sentence.Licensed; infer_instance

/-- The grammar fits the Toba Batak rows when it rejects exactly the sentences judged ill
formed. -/
def Fits (hyp : OrderHypothesis) (th : BindingTheory) : Prop :=
  ∀ row ∈ Examples.all, ∀ s ∈ Sentence.ofRow row,
    (row.judgment.band = .rejected ↔ ¬ s.Licensed hyp th)

instance (hyp : OrderHypothesis) (th : BindingTheory) : Decidable (Fits hyp th) := by
  unfold Fits; infer_instance

theorem not_fits {hyp : OrderHypothesis} {th : BindingTheory} {row : Datum}
    (hrow : row ∈ Examples.all)
    (h : ∃ s ∈ Sentence.ofRow row, ¬ (row.judgment.band = .rejected ↔ ¬ s.Licensed hyp th)) :
    ¬ Fits hyp th :=
  fun hf ↦ let ⟨s, hs, hn⟩ := h; hn (hf row hrow s hs)

/-- Of the two hypotheses on SVO clauses and the four binding conditions, the grammar fits the
Toba Batak rows only with the VOS Hypothesis, since fronting from an SVO clause is as ill formed
as from a VOS one ((7a), (88)), and with binding at some stage, since the passive agent binds the
passive subject before the subject raises past it and the subject binds the agent only after
((67), (68), Table 1). -/
theorem fits_iff (hyp : OrderHypothesis) (th : BindingTheory) :
    Fits hyp th ↔ hyp = .vosHypothesis ∧ th = .derivational := by
  refine ⟨fun h ↦ ?_, fun ⟨h₁, h₂⟩ ↦ h₁ ▸ h₂ ▸ by decide +kernel⟩
  have mem (row : Datum) (h : row ∈ Examples.all := by simp [Examples.all]) := h
  cases hyp with
  | svoHypothesis => exact absurd h (not_fits (mem Examples.ex7a) (by cases th <;> decide +kernel))
  | vosHypothesis =>
    cases th with
    | surface => exact absurd h (not_fits (mem Examples.ex62) (by decide +kernel))
    | lastSVOStage => exact absurd h (not_fits (mem Examples.ex67) (by decide +kernel))
    | derivational => exact ⟨rfl, rfl⟩
    | semanticHierarchy => exact absurd h (not_fits (mem Examples.ex68) (by decide +kernel))

/-- Table 1's grades. -/
inductive Grade
  | typeA | typeB | typeC
  deriving DecidableEq, Repr

/-- The grade of a sentence reads the Semantic Hierarchy Condition as an addition to
derivational binding rather than a substitute for it (§3.7). It is Type A when the sentence is
licensed with binding at some stage and with the Semantic Hierarchy, Type B when it is licensed
only with binding at some stage, and Type C when it is not licensed with binding at some
stage. -/
def Sentence.grade (s : Sentence) : Grade :=
  if s.Licensed .vosHypothesis .derivational then
    if s.Licensed .vosHypothesis .semanticHierarchy then .typeA else .typeB
  else .typeC

/-- The grade a row's Table 1 type records. -/
def tableOne? (row : Datum) : Option (Sentence × Grade) := do
  return (← Sentence.ofRow row,
    ← row.parse? "tableOne" [("A", Grade.typeA), ("B", .typeB), ("C", .typeC)])

-- Table 1
theorem table1 : (∀ row ∈ Examples.all, ∀ x ∈ tableOne? row, x.1.grade = x.2) ∧
    Datum.ReadCount tableOne? Examples.all 7 := by
  decide +kernel

/-! ### Copies -/

/-- The clauses whose derivations the paper draws: (49) in (50)–(55), (56) in (57)–(61), (67) in
(72)–(74) and (68) in (75)–(77). -/
def clauses : List Clause :=
  [Examples.ex49, Examples.ex56, Examples.ex67, Examples.ex68].filterMap fun row ↦
    (Sentence.ofRow row).map (·.clause)

example : clauses.length = 4 := by decide +kernel

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

/-! ### Every clause goes through a VOS stage (§5) -/

theorem svo_take_vos (c : Clause) (σ : Sides) : (c.svo σ).take (c.vos σ).length = c.vos σ :=
  Derivation.take_length_append _ _

theorem frozen_svo_iff (c : Clause) (σ : Sides) (x : SyntacticObject) :
    (c.svo σ).Frozen x ↔ (c.vos σ).Frozen x := by
  simp [Clause.svo, Derivation.frozen_append_iff]

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
    ∀ σ : Sides, s.clause.words (s.clause.vos σ) = s.words := by
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

/-- The analysis licenses a reflexive antecedent to `x`, the other core argument, when the
reflexive meets Condition A, coindexed with `x` alone. -/
def Licenses (an : EnglishAnalysis) (x : Arg) : Prop :=
  an.configuration.Condition (Binding.pair x x.other) ∅ x.other .reflexive

instance (an : EnglishAnalysis) (x : Arg) : Decidable (an.Licenses x) := by
  unfold Licenses configuration; infer_instance

end EnglishAnalysis

/-- The antecedent of the reflexive in an English row. -/
def englishAntecedent? (row : Datum) : Option Arg := do
  guard (row.language = english)
  row.parse? "antecedent" args

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
    (∀ e ∈ Examples.all, e.Fits englishAntecedent? fun x ↦ .ofProp (an.Licenses x)) ↔
      an = .adjunct := by
  cases an <;> decide +kernel

end ColeHermon2008
