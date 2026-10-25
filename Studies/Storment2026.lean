module

public import Linglib.Data.Examples.Storment2026
public import Linglib.Syntax.Agreement.Bundle
public import Linglib.Syntax.Minimalist.Probe.Agree
public import Studies.BrananErlewine2026

/-!
# Storment (2026): Quotative inversion as smuggling

This file derives quotative and locative inversion in English and Setswana as smuggling. A clause
is a `Derivation` in which Voice raises the VP, holding the verb and the theme, over the agent in
Spec,vP, and the theme then raises to Spec,TP; head movement of the verb is the rival analysis.
T's φ-probe searches depth first, copies by unification and may search past a defective goal.
Each of the paper's examples is paired with what the grammar generates: the position of a
dependent, licensing by T and Voice, agreement and the conjoint verb form.

## Main results

* `Storment2026.ex122_licensed_iff`: only VP movement licenses the theme ((113), (116)).
* `Storment2026.search_finds_theme`: depth-first search finds the theme ((118), (119), p. 35).
* `Storment2026.agree_eq_of_not_defective`: defective circumvention needs a defective goal (59).
* `Storment2026.acceptable_iff_generated`: the examples, acceptable exactly when generated.
* `Storment2026.generated_ex40_sg`: the analysis admits the starred *advises* of (40) (§3.1.2).

## Implementation notes

* The quote is outside the derivation (§3.5). A second DP sits in the VP as in (132) when it
  precedes the agent, and at the vP level when it follows, the position §2 diagnoses.
* Agree reads T's goals in the order of the stage's leaves, the depth-first order of (118),
  since every specifier is merged on the left.
* The theme bears third person and no number (§3.1.4, §6). Noun class has no carrier, so a
  Setswana marker counts as default when T ends valued in no number.

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
open BrananErlewine2026 (Matches depthFirst depth)

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

/-- The DPs: the theme, the agent and any second DP. -/
def dps : List LexicalItem.Token :=
  [p.themeTok, p.agentTok] ++ (match p.complement with | some c@(.dp _) => [c.token] | _ => []) ++
    (match p.external with | some e@(.dp _) => [e.token] | _ => [])

end Clause

/-- At a stage of `d`, the probe on `h` licenses the DP its depth-first search finds (118). -/
def Licenses (d : Derivation) (h x : LexicalItem.Token) : Prop :=
  ∃ t ∈ d.externalize?, Matches t h depthFirst x

instance (d : Derivation) (h x : LexicalItem.Token) : Decidable (Licenses d h x) := by
  unfold Licenses; infer_instance

/-- The Case filter (§5): every DP is licensed by T or by Voice, each licensing the DP its search
finds, the theme and the agent (133). -/
def Clause.Licensed (p : Clause) (a : Analysis) : Prop :=
  ∀ x ∈ p.dps, Licenses (p.tStage a) t₀ x ∨ Licenses (p.voiceP a) voice₀ x

instance (p : Clause) (a : Analysis) : Decidable (p.Licensed a) := by
  unfold Clause.Licensed; infer_instance

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

theorem vpMovement_smuggles :
    (ex122.inversion .vpMovement).IsSmugglingStep (ex122.vP.length + 1) op ex122.agentTok ∧
      ¬ (ex122.inversion .headMovement).IsSmugglingStep (ex122.vP.length + 1) op
        ex122.agentTok := by
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

/-! ### Search (§4.2)

T's search finds the theme before the agent although neither c-commands the other. -/

/-- Depth-first search finds the theme alone (118), as does breadth-first search in (116) (119);
a control clause in the VP puts the theme as deep as the agent, so breadth-first search over
unordered sisters finds both, while depth-first search still finds the theme (p. 35). -/
theorem search_finds_theme :
    (∃ t ∈ (ex122.tStage .vpMovement).externalize?,
      Matches t t₀ depthFirst op ∧ ¬ Matches t t₀ depthFirst ex122.agentTok ∧
        Matches t t₀ depth op ∧ ¬ Matches t t₀ depth ex122.agentTok) ∧
    ∃ t ∈ (ex26.tStage .vpMovement).externalize?,
      Matches t t₀ depthFirst op ∧ ¬ Matches t t₀ depthFirst ex26.agentTok ∧
        Matches t t₀ depth op ∧ Matches t t₀ depth ex26.agentTok := by
  decide +kernel

/-! ### Agreement (§3.1)

T's φ-probe seeks a set of dimensions. Copying a goal's features to it is unification, so that a
goal conflicting with what T has copied leaves it at `⊤`, the irresolvable clash of (59). -/

open Agreement

/-- The theme's φ-features: third person, and no number or class ((50)–(53)). -/
def themePhi : Bundle := Bundle.set .person .third ⊥

/-- A goal is defective for a probe seeking `P` when the dimensions it is valued in are a proper
subset of `P`, (49) after [roberts-2010]. -/
def Defective (P : Finset Dimension) (g : Bundle) : Prop :=
  Finset.univ.filter (g · ≠ ⊥) ⊂ P

instance (P : Finset Dimension) : DecidablePred (Defective P) := fun _ ↦ by
  unfold Defective; infer_instance

theorem not_defective_empty (g : Bundle) : ¬ Defective ∅ g := Finset.not_ssubset_empty _

/-- T's φ-probe seeking `P` copies from every goal bearing φ and halts at one not defective for
it. -/
def phiProbe (P : Finset Dimension) : Probe Bundle where
  int g := g ≠ ⊥
  sat g := g ≠ ⊥ ∧ ¬ Defective P g

@[simp] theorem phiProbe_int (P : Finset Dimension) (g : Bundle) : (phiProbe P).int g ↔ g ≠ ⊥ :=
  .rfl

@[simp] theorem phiProbe_sat (P : Finset Dimension) (g : Bundle) :
    (phiProbe P).sat g ↔ g ≠ ⊥ ∧ ¬ Defective P g :=
  .rfl

open scoped PartialUnify in
/-- Agree copies a goal's features to T by unification. -/
def copy (g : Bundle) (s : WithTop Bundle) : WithTop Bundle := s ⊔ ↑g

/-- The values T may end with on the goals `gs`: Agree halting at the first goal bearing φ,
`phiProbe ∅`, or searching past a defective goal, defective circumvention ((59), after
[storment-2025]). -/
def valuations (P : Finset Dimension) (gs : List Bundle) : Finset (WithTop Bundle) :=
  {((phiProbe ∅).agree copy ⊥ gs).state, ((phiProbe P).agree copy ⊥ gs).state}

/-- Defective circumvention needs a defective goal: when the first goal bearing φ is not
defective, Agree halts there with or without it (59). -/
theorem agree_eq_of_not_defective {P : Finset Dimension} {gs : List Bundle}
    (h : ∀ g ∈ gs.find? (· ≠ ⊥), ¬ Defective P g) (s : WithTop Bundle) :
    (phiProbe P).agree copy s gs = (phiProbe ∅).agree copy s gs := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    by_cases hg : g = ⊥
    · subst hg
      simp only [List.find?_cons, ne_eq, not_true_eq_false, decide_false] at h
      simp [Probe.agree_cons, ih h]
    · have hd : ¬ Defective P g := h g (by simp [hg])
      simp [Probe.agree_cons, hg, hd, not_defective_empty]

theorem valuations_empty (gs : List Bundle) :
    valuations ∅ gs = {((phiProbe ∅).agree copy ⊥ gs).state} :=
  Finset.pair_eq_singleton _

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

/-- The stage at which T probes. -/
def probeStage : Construction → Derivation
  | .inversion => p.tStage .vpMovement
  | .noninverted => p.vP.append [.em .left t₀]

/-- T's goals in the order its search meets them. -/
def goals (c : Construction) : List Bundle := (p.probeStage c).surfaceTokens.map p.phi

/-- The agreement T may spell out. -/
def agreement (l : Language) (c : Construction) : Finset (Option AgreementForm) :=
  (valuations l.probe (p.goals c)).image spellOut

/-- The verb is disjoint when every DP and adjunct merged in the vP has left it, the
generalization of §3.4. -/
def IsDisjoint : Prop :=
  ∀ x ∈ p.dps ++ (p.external.map (·.token)).toList,
    ∃ m ∈ (p.inversion .vpMovement).movedItems, Contains m x

instance : Decidable p.IsDisjoint := by unfold IsDisjoint; infer_instance

end Clause

/-! ### The rows -/

/-- Where a dependent surfaces relative to the agent. -/
inductive Position
  | beforeAgent | afterAgent
  deriving DecidableEq, Repr

/-- Where the inversion of `p` puts `form` relative to its agent. -/
def Clause.position (p : Clause) (form : String) : Position :=
  let s := (p.inversion .vpMovement).surfacePhon
  if s.idxOf form < s.idxOf p.agent then .beforeAgent else .afterAgent

/-- What a row shows: its clause, language and construction, with the position of its dependent,
its agreement and its verb form where it records them. -/
structure Observation where
  /-- The language. -/
  language : Language
  /-- The clause. -/
  clause : Clause
  /-- The construction. -/
  construction : Construction
  /-- The dependent and where it surfaces. -/
  position : Option (String × Position)
  /-- The agreement. -/
  agreement : Option AgreementForm
  /-- The verb form. -/
  verbForm : Option VerbForm

/-- The grammar generates what a row shows: an inversion is licensed, its dependent is where the
derivation puts it, its agreement is one T may spell out, and its verb form is the one §3.4
gives. -/
def Observation.Generated (o : Observation) : Prop :=
  (o.construction = .inversion → o.clause.Licensed .vpMovement) ∧
    (∀ d ∈ o.position, o.clause.position d.1 = d.2) ∧
    (∀ a ∈ o.agreement, some a ∈ o.clause.agreement o.language o.construction) ∧
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
  let language ← [("stan1293", Language.english), ("tswa1253", .setswana)].lookup row.language
  let construction ← row.parse? "construction" [("qi", Construction.inversion),
    ("li", .inversion), ("preposedQuote", .noninverted), ("canonical", .noninverted)]
  let position ← match row.feature? "dependent" with
    | none => some none
    | some d => (row.parse? "position" positions).map fun pos ↦ some (d, pos)
  return ⟨language, ← Clause.ofRow row, construction, position,
    row.parse? "agreement" [("default", .default), ("agent", .agent)],
    row.parse? "verbForm" [("conjoint", .conjoint), ("disjoint", .disjoint)]⟩

/-- An example the paper judges is acceptable exactly when the grammar generates the position of
its dependent (§2), its agreement (§3.1), its verb form (§3.4) and, inverted, its licensing
(§5, §6). -/
theorem acceptable_iff_generated : ∀ row ∈ Examples.all, row.source.bibkey = "storment-2026" →
    ∀ o ∈ Observation.ofRow row, (row.judgment = .acceptable ↔ o.Generated) := by
  decide +kernel

/-- The analysis admits the *advises* of (40), default agreement, which [collins-branigan-1997]
star and the paper defends with (41). -/
theorem generated_ex40_sg : ∀ o ∈ Observation.ofRow Examples.ex40_sg, o.Generated := by
  decide +kernel

end Storment2026
