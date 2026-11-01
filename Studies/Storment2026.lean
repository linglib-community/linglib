module

public import Linglib.Data.Examples.Storment2026
public import Linglib.Fragments.Setswana.Basic
public import Linglib.Syntax.Agreement.Bundle
public import Linglib.Syntax.Minimalist.Probe.Search
public import Studies.Collins2005
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Storment (2026): Quotative inversion as smuggling

This file derives quotative and locative inversion in English and Setswana as smuggling. A clause
is a `Derivation` in which Voice raises the VP, holding the verb and the theme, over the agent in
Spec,vP, and the theme then raises to Spec,TP; head movement of the verb is the rival analysis.
T and Voice search depth first; T's φ-probe copies by unification and may search past a defective
goal. Each of the paper's examples is paired with what the grammar generates: the position of a
dependent, licensing by T and Voice, English agreement, Setswana subject markers and the conjoint
verb form.

## Implementation notes

* The quote is outside the derivation (§3.5). A second DP sits in the VP as in (132) when it
  precedes the agent, and at the vP level when it follows, the position §2 diagnoses.
* The theme bears third person and no number (§3.1.4, §6). The agreement bundle has no noun
  class, so a Setswana marker is read off the agreement T ends with: class 17's when it values no
  number, else the agent's, by the agent's class.
* The judgments of (40) are Collins and Branigan's, which the paper disputes; the analysis
  generates its starred *advises* (`generated_ex40_sg`).

## TODO

* Parasitic gaps (62), raising (67)–(83), heavy NP shift (14), locative inversion without
  fronting (93), embedded inversion (141)–(144) and agreeing locative inversion (139)–(145).

## References

* [storment-2026]
* [storment-2025]
* [collins-branigan-1997]
* [collins-2005]
* [roberts-2010]
* [branan-erlewine-2026]
-/

@[expose] public section

namespace Storment2026

open Minimalist SyntacticObject
open Minimalist.Probe (depthFirst depth)

/-! ### The derivation (§2, §4) -/

/-- The quotative operator, the null nominal theme that a quote in the discourse binds (§3.5). -/
def op : LexicalItem.Token := ⟨.of .D [], 3⟩

/-- v, over the VP and the agent. -/
def v₀ : LexicalItem.Token := ⟨.of .v [.V, .D], 6⟩

/-- Voice, over vP, which attracts the VP and introduces no argument (§4.3). -/
def voice₀ : LexicalItem.Token := ⟨.of .Voice [.v], 7⟩

/-- T. -/
def t₀ : LexicalItem.Token := ⟨.of .T [], 8⟩

/-- What the VP holds besides the verb and the theme: a particle (117), a control clause holding
the theme (§2.2), or a second DP (132). -/
inductive Complement
  | particle (form : String)
  | control (form : String)
  | dp (form : String)
  deriving DecidableEq, Repr

/-- The token of a complement. -/
def Complement.token : Complement → LexicalItem.Token
  | particle s => ⟨.of .P [] (phonForm := s), 4⟩
  | control s => ⟨.of .V [.D] (phonForm := s), 4⟩
  | dp s => ⟨.of .D [] (phonForm := s), 4⟩

/-- What follows the agent outside the VP (§2.1, §5): a vP adjunct, a PP or an adjunct clause,
each licensing its own DPs, or a DP. -/
inductive VPExternal
  | adjunct (form : String)
  | dp (form : String)
  deriving DecidableEq, Repr

/-- The token of a VP-external element. -/
def VPExternal.token : VPExternal → LexicalItem.Token
  | adjunct s => ⟨.of .A [] (phonForm := s), 5⟩
  | dp s => ⟨.of .D [] (phonForm := s), 5⟩

/-- A clause of quotative or locative inversion. -/
structure Clause where
  /-- The verb. -/
  verb : String
  /-- The agent, merged in Spec,vP. -/
  agent : String
  /-- The agent's φ-features. -/
  agentPhi : Agreement.Bundle := ⊥
  /-- The agent's noun class, in Setswana. -/
  agentClass : Option Bantu.NounClass := none
  /-- An overt locative theme; the theme is otherwise the quotative operator. -/
  theme : Option String := none
  /-- What else the VP holds. -/
  complement : Option Complement := none
  /-- What follows the agent outside the VP. -/
  external : Option VPExternal := none

/-- What raises the verb over the agent: the VP, to Spec,VoiceP (116), or the verb alone, head
movement as in [collins-branigan-1997]. -/
inductive Analysis
  | vpMovement | headMovement
  deriving DecidableEq, Repr

namespace Clause

variable (p : Clause)

/-- The theme's token. -/
def themeTok : LexicalItem.Token := p.theme.elim op (⟨.of .D [] (phonForm := ·), 3⟩)

/-- The verb's token, selecting its complement and the theme. -/
def verbTok : LexicalItem.Token :=
  ⟨.of .V (match p.complement with
    | none => [.D]
    | some (.particle _) => [.P, .D]
    | some (.control _) => [.V]
    | some (.dp _) => [.D, .D]) (phonForm := p.verb), 1⟩

/-- The agent's token. -/
def agentTok : LexicalItem.Token := ⟨.of .D [] (phonForm := p.agent), 2⟩

/-- The tokens of the complement and the VP-external element. -/
def dependents : List LexicalItem.Token :=
  (p.complement.map (·.token)).toList ++ (p.external.map (·.token)).toList

/-- The DPs: the theme, the agent and any dependent DP. -/
def dps : List LexicalItem.Token :=
  [p.themeTok, p.agentTok] ++ p.dependents.filter (·.item.cat = .D)

/-- The steps that build the VP from the verb. -/
def vpSteps : List Step :=
  match p.complement with
  | none => [.em .right p.themeTok]
  | some c@(.control _) => [.em .right {.leaf c.token, .leaf p.themeTok}]
  | some c => [.em .right c.token, .em .left p.themeTok]

/-- The VP. -/
def vp : Option LinearizedSyntacticObject := (⟨p.verbTok, p.vpSteps⟩ : Derivation).externalize?

/-- The vP: the VP, v, the agent on the left and any VP-external element on the right. -/
def vP : Derivation :=
  ⟨p.verbTok, p.vpSteps ++ [.em .left v₀, .em .left p.agentTok] ++
    (p.external.map (.em .right ·.token)).toList⟩

/-- Voice merges over vP and raises the VP or the verb. -/
def voiceP (a : Analysis) : Derivation :=
  p.vP.append <| .em .left voice₀ :: match a with
    | .vpMovement => (p.vp.map (.im ·)).toList
    | .headMovement => [.im p.verbTok]

/-- The stage at which T probes. -/
def tStage (a : Analysis) : Derivation := (p.voiceP a).append [.em .left t₀]

/-- Inversion (122): the theme A-moves to Spec,TP. -/
def inversion (a : Analysis) : Derivation := (p.tStage a).append [.im p.themeTok]

end Clause

/-! ### Licensing and search (§4, §5) -/

/-- At a stage of `d`, the probe on `h` licenses the DP its depth-first search finds (118). -/
def Licenses (d : Derivation) (h x : LexicalItem.Token) : Prop :=
  ∃ t ∈ d.externalize?, ↑x ∈ t.goalsBy (t.leafProbe .D) h (depthFirst ·.val)

instance (d : Derivation) (h x : LexicalItem.Token) : Decidable (Licenses d h x) := by
  unfold Licenses; infer_instance

/-- The Case filter (§5): every DP is licensed by T or by Voice, each licensing the DP its search
finds, the theme and the agent (133). -/
def Clause.Licensed (p : Clause) (a : Analysis) : Prop :=
  ∀ x ∈ p.dps, Licenses (p.tStage a) t₀ x ∨ Licenses (p.voiceP a) voice₀ x

instance (p : Clause) (a : Analysis) : Decidable (p.Licensed a) := by
  unfold Clause.Licensed; infer_instance

/-- A derivation smuggles `x` past `w` via VoiceP when a step smuggles it into the specifier of a
Voice head, voice in the sense of (121), after [storment-2025]. -/
def SmugglesViaVoice (d : Derivation) (x w : SyntacticObject) : Prop :=
  ∃ i < d.length, d.IsSmugglingStep i x w ∧
    ∃ q ∈ (d.take i).externalize?, ∃ v ∈ q.toSyntacticObject.selHead, v.item.cat = .Voice

instance (d : Derivation) (x w : SyntacticObject) : Decidable (SmugglesViaVoice d x w) := by
  unfold SmugglesViaVoice; infer_instance

/-- (122): *"Hey," said John*. -/
def ex122 : Clause := { verb := "said", agent := "John" }

/-- (29a): *"Where are you going?" called out John*. -/
def ex29 : Clause := { verb := "called", agent := "John", complement := some (.particle "out") }

/-- (26a): *"Help!" tried to yell Alex*. -/
def ex26 : Clause := { verb := "tried", agent := "Alex", complement := some (.control "to yell") }

/-- (117): *"Hey!" piped up John loudly*. -/
def ex117 : Clause :=
  { verb := "piped", agent := "John", complement := some (.particle "up"),
    external := some (.adjunct "loudly") }

/-- Without smuggling the agent intervenes between T and the theme (113); moving the VP past the
agent lets T find the theme (116). -/
theorem ex122_licensed_iff (a : Analysis) : ex122.Licensed a ↔ a = .vpMovement := by
  cases a <;> decide +kernel

/-- Quotative inversion smuggles the theme past the agent via VoiceP, as the passive of
[collins-2005] smuggles its object, and head movement of the verb does not (§4.3) ((121)). -/
theorem inversion_smugglesViaVoice :
    SmugglesViaVoice (Collins2005.ex9.passive .partP false) Collins2005.ex9.patient
        Collins2005.ex9.agent ∧
      SmugglesViaVoice (ex122.inversion .vpMovement) op ex122.agentTok ∧
      ¬ SmugglesViaVoice (ex122.inversion .headMovement) op ex122.agentTok := by
  decide +kernel

/-- The quote is outside the derivation, which pronounces the verb and the agent of (122). -/
example : (ex122.inversion .vpMovement).surfacePhon = ["said", "John"] := by decide

theorem complement_orders :
    (ex29.inversion .vpMovement).surfacePhon = ["called", "out", "John"] ∧
      (ex29.inversion .headMovement).surfacePhon = ["called", "John", "out"] ∧
      (ex26.inversion .vpMovement).surfacePhon = ["tried", "to yell", "Alex"] ∧
      (ex26.inversion .headMovement).surfacePhon = ["tried", "Alex", "to yell"] := by
  decide

/-- A vP adjunct stays below with the agent (117). -/
example : (ex117.inversion .vpMovement).surfacePhon = ["piped", "up", "John", "loudly"] := by
  decide

/-- Depth-first search finds the theme alone (118), as does breadth-first search in (116) (119);
a control clause in the VP puts the theme as deep as the agent, so breadth-first search over
unordered sisters finds both, while depth-first search still finds the theme alone (p. 35). -/
theorem search_finds_theme :
    (∃ t ∈ (ex122.tStage .vpMovement).externalize?,
      t.goalsBy (t.leafProbe .D) t₀ (depthFirst ·.val) = {↑op} ∧
        t.goalsBy (t.leafProbe .D) t₀ (depth ·.val) = {↑op}) ∧
    ∃ t ∈ (ex26.tStage .vpMovement).externalize?,
      t.goalsBy (t.leafProbe .D) t₀ (depthFirst ·.val) = {↑op} ∧
        t.goalsBy (t.leafProbe .D) t₀ (depth ·.val) = {↑op, ↑ex26.agentTok} := by
  decide +kernel

/-! ### Agreement (§3.1)

T's φ-probe seeks a set of dimensions. Agree copies a goal's features to it by unification, so a
goal conflicting with what T has copied leaves it at `⊤`, the irresolvable clash of (59), and the
order of copying is idle: T ends with the join of what it agrees with. -/

open Agreement

/-- The theme's φ-features: third person, and no number or class ((50)–(53)). -/
def themePhi : Bundle := Bundle.set .person .third ⊥

/-- A goal is defective for a probe seeking `P` when the dimensions it is valued in are a proper
subset of `P`, (49) after [roberts-2010]. -/
def Defective (P : Finset Dimension) (g : Bundle) : Prop :=
  Finset.univ.filter (g · ≠ ⊥) ⊂ P

instance (P : Finset Dimension) : DecidablePred (Defective P) := fun _ ↦ by
  unfold Defective; infer_instance

@[simp] theorem not_defective_empty (g : Bundle) : ¬ Defective ∅ g := Finset.not_ssubset_empty _

/-- T's φ-probe seeking `P` copies from every goal bearing φ and halts at one not defective for
it; `phiProbe ∅` halts at the first goal bearing φ. -/
def phiProbe (P : Finset Dimension) : Probe Bundle where
  int g := g ≠ ⊥
  sat g := g ≠ ⊥ ∧ ¬ Defective P g

@[simp] theorem phiProbe_int (P : Finset Dimension) (g : Bundle) : (phiProbe P).int g ↔ g ≠ ⊥ :=
  .rfl

@[simp] theorem phiProbe_sat (P : Finset Dimension) (g : Bundle) :
    (phiProbe P).sat g ↔ g ≠ ⊥ ∧ ¬ Defective P g :=
  .rfl

/-- Defective circumvention needs a defective goal: when the first goal bearing φ that the search
finds is not defective, Agree past it agrees with the goals Agree halting there does (59). -/
theorem agreesWith_iff_of_not_defective {α β : Type*} [Finite α] [LinearOrder β]
    {φ : α → Bundle} {s : Set α} {key : α → β} {P : Finset Dimension}
    (h : ∀ g, ((phiProbe ∅).comap φ).Finds s key g → ¬ Defective P (φ g)) (a : α) :
    ((phiProbe P).comap φ).AgreesWith s key a ↔ ((phiProbe ∅).comap φ).AgreesWith s key a := by
  refine ⟨fun ⟨⟨ha, hP⟩, hi⟩ ↦ ⟨⟨ha, fun b hb hbe hlt ↦ ?_⟩, hi⟩,
    fun ⟨⟨ha, he⟩, hi⟩ ↦ ⟨⟨ha, fun b hb hbP ↦ he hb ⟨hbP.1, not_defective_empty _⟩⟩, hi⟩⟩
  obtain ⟨g, ⟨hg, hge⟩, hmin⟩ := Set.exists_min_image
    {x | x ∈ s ∧ ((phiProbe ∅).comap φ).sat x} key (Set.toFinite _) ⟨b, hb, hbe⟩
  exact hP hg ⟨hge.1, h g ⟨⟨hg, hge⟩, fun j hj _ ↦ hmin j hj⟩⟩
    ((hmin b ⟨hb, hbe⟩).trans_lt hlt)

/-- Agreement shows the agent's features or the default, third singular in English and class 17
*go* in Setswana (47). -/
inductive AgreementForm
  | default | agent
  deriving DecidableEq, Repr

/-- T spells out a value with no number as default agreement and one with number, which only the
agent supplies, as the agent's; a clash spells out nothing. -/
def spellOut : WithTop Bundle → Option AgreementForm :=
  WithTop.recTopCoe none fun b ↦ some (if b .number = ⊥ then .default else .agent)

/-- A clause is an inversion, Voice raising the VP, or noninverted, the agent raising to Spec,TP
over the theme. -/
inductive Construction
  | inversion | noninverted
  deriving DecidableEq, Repr

/-- The conjoint and disjoint forms of the Setswana verb (§3.4). -/
inductive VerbForm
  | conjoint | disjoint
  deriving DecidableEq, Repr

/-- The languages. -/
inductive Language
  | english | setswana
  deriving DecidableEq, Repr

/-- The dimensions T's φ-probe seeks: person and number in English, bare [φ] in Setswana
(§3.1.4). -/
def Language.probe : Language → Finset Dimension
  | english => {.person, .number}
  | setswana => ∅

namespace Clause

variable (p : Clause)

/-- A token's φ-features. -/
def phi (x : LexicalItem.Token) : Bundle :=
  if x = p.themeTok then themePhi else if x = p.agentTok then p.agentPhi else ⊥

/-- The φ-features at a position of `t`, those of the token there. -/
def phiAt (t : LinearizedSyntacticObject) (q : t.val.Positions) : Bundle :=
  (t.termAt q).token?.elim ⊥ p.phi

/-- The stage at which T probes. -/
def probeStage : Construction → Derivation
  | .inversion => p.tStage .vpMovement
  | .noninverted => p.vP.append [.em .left t₀]

open scoped PartialUnify in
/-- The value T ends with when its probe seeks `P`: the join of the φ-features of the goals its
depth-first search agrees with (118). -/
def value (c : Construction) (P : Finset Dimension) : WithTop Bundle :=
  ((p.probeStage c).externalize?.map fun t ↦
    (Finset.univ.filter fun q ↦ ∃ a : t.val.Positions, t.termAt a = ↑t₀ ∧
      ((phiProbe P).comap (p.phiAt t)).AgreesWith {x | t.val.CCommands a x} (depthFirst ·.val)
        q).sup fun q ↦ (p.phiAt t q : WithTop Bundle)).getD ⊤

/-- The values T may end with (59): halting at the first goal bearing φ, or searching past a
defective goal, defective circumvention, after [storment-2025]. -/
def valuations (c : Construction) (P : Finset Dimension) : Finset (WithTop Bundle) :=
  {p.value c ∅, p.value c P}

theorem valuations_empty (c : Construction) : p.valuations c ∅ = {p.value c ∅} :=
  Finset.pair_eq_singleton _

/-- The agreement T may spell out. -/
def agreement (l : Language) (c : Construction) : Finset (Option AgreementForm) :=
  (p.valuations c l.probe).image spellOut

/-- The Setswana subject marker of an agreement form in a tense: class 17's for default agreement
(47), and otherwise the agent's, by person for a speech-act participant and by class else. -/
def marker (t : UD.Tense) : AgreementForm → Option String
  | .default => (if t = .Past then Setswana.pastSubjPrefix else Setswana.subjPrefix) .cl17
  | .agent =>
    if p.agentPhi.IsSAP then
      if t = .Past then none else Setswana.subjectPrefix.realize p.agentPhi
    else p.agentClass.bind (if t = .Past then Setswana.pastSubjPrefix else Setswana.subjPrefix)

/-- The Setswana subject markers T may spell out in a tense. -/
def markers (c : Construction) (t : UD.Tense) : Finset (Option String) :=
  (p.agreement .setswana c).image (·.bind (p.marker t))

/-- The verb is disjoint when the theme, the agent and every dependent merged in the vP have left
it, the generalization of §3.4. -/
def IsDisjoint : Prop :=
  ∀ x ∈ [p.themeTok, p.agentTok] ++ p.dependents,
    ∃ m ∈ (p.inversion .vpMovement).movedItems, Contains m x

instance : Decidable p.IsDisjoint := by unfold IsDisjoint; infer_instance

end Clause

/-! ### The rows -/

/-- Where a dependent surfaces relative to the agent. -/
inductive Position
  | beforeAgent | afterAgent
  deriving DecidableEq, Repr

/-- Where the inversion of `p` puts the token `x` relative to its agent. -/
def Clause.position (p : Clause) (x : LexicalItem.Token) : Position :=
  let s := (p.inversion .vpMovement).surfaceTokens
  if s.idxOf x < s.idxOf p.agentTok then .beforeAgent else .afterAgent

/-- What a row shows: its clause, language and construction, with the position of its dependent,
its agreement, its subject marker and its verb form where it records them. -/
structure Observation where
  /-- The language. -/
  language : Language
  /-- The clause. -/
  clause : Clause
  /-- The construction. -/
  construction : Construction
  /-- Where the dependent surfaces. -/
  position : Option Position
  /-- The agreement, English verb agreement read as default or the agent's. -/
  agreement : Option AgreementForm
  /-- The Setswana subject marker and its tense. -/
  subjectMarker : Option (String × UD.Tense)
  /-- The verb form. -/
  verbForm : Option VerbForm

/-- The grammar generates what a row shows: an inversion is licensed, its dependent is where the
derivation puts it, its agreement and subject marker are ones T may spell out, and its verb form
is the one §3.4 gives. -/
def Observation.Generated (o : Observation) : Prop :=
  (o.construction = .inversion → o.clause.Licensed .vpMovement) ∧
    (∀ pos ∈ o.position, ∀ x ∈ o.clause.dependents, o.clause.position x = pos) ∧
    (∀ a ∈ o.agreement, some a ∈ o.clause.agreement o.language o.construction) ∧
    (∀ m ∈ o.subjectMarker, some m.1 ∈ o.clause.markers o.construction m.2) ∧
    ∀ f ∈ o.verbForm, (f = .disjoint ↔ o.clause.IsDisjoint)

instance (o : Observation) : Decidable o.Generated := by
  unfold Observation.Generated; infer_instance

/-- The positions. -/
def positions : List (String × Position) :=
  [("beforeAgent", .beforeAgent), ("afterAgent", .afterAgent)]

/-- A row's clause. A DP is inside the VP when it precedes the agent and outside when it follows,
the diagnostic of §2. -/
def Clause.ofRow (row : Datum) : Option Clause := do
  let agentPhi := (do
    return Bundle.personNumber
      (← row.parse? "person" [("1", Person.first), ("2", .second), ("3", .third)])
      (← row.parse? "number" [("sg", Number.singular), ("pl", .plural)])).getD ⊥
  let base : Clause :=
    { verb := ← row.feature? "verb", agent := ← row.feature? "agent", agentPhi,
      agentClass := (row.feature? "class").bind Bantu.NounClass.ofNumeral?,
      theme := row.feature? "theme" }
  match row.feature? "dependent", row.feature? "category" with
  | none, _ => return base
  | some d, some "particle" => return { base with complement := some (.particle d) }
  | some d, some "control" => return { base with complement := some (.control d) }
  | some d, some "dp" =>
    if row.feature? "position" = some "beforeAgent" then
      return { base with complement := some (.dp d) }
    else return { base with external := some (.dp d) }
  | some d, some _ => return { base with external := some (.adjunct d) }
  | some _, none => none

/-- What a row shows. -/
def Observation.ofRow (row : Datum) : Option Observation := do
  let language ← row.byLanguage [(.english, Language.english), (.tswana, .setswana)]
  let construction ← row.parse? "construction" [("qi", Construction.inversion),
    ("li", .inversion), ("preposedQuote", .noninverted), ("canonical", .noninverted)]
  let position ← match row.feature? "dependent" with
    | none => some none
    | some _ => (row.parse? "position" positions).map some
  return ⟨language, ← Clause.ofRow row, construction, position,
    row.parse? "agreement" [("default", .default), ("agent", .agent)],
    (row.feature? "subjectMarker").map
      (·, (row.parse? "tense" [("past", UD.Tense.Past)]).getD .Pres),
    row.parse? "verbForm" [("conjoint", .conjoint), ("disjoint", .disjoint)]⟩

/-- An example the paper judges is acceptable exactly when the grammar generates the position of
its dependent (§2), its agreement (§3.1), its verb form (§3.4) and, inverted, its licensing
(§5, §6). -/
theorem acceptable_iff_generated : ∀ row ∈ Examples.all, row.source.bibkey = "storment-2026" →
    ∀ o ∈ Observation.ofRow row, (row.judgment = .acceptable ↔ o.Generated) := by
  decide +kernel

theorem generated_ex40_sg : ∀ o ∈ Observation.ofRow Examples.ex40_sg, o.Generated := by
  decide +kernel

end Storment2026
