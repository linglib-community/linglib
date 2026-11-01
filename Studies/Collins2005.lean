module

public import Linglib.Data.Examples.Collins2005
public import Linglib.Data.Examples.Gloss
public import Linglib.Syntax.Binding.Basic
public import Linglib.Syntax.Minimalist.Probe.SyntacticObject
public import Linglib.Syntax.Minimalist.Locality.Freezing
public import Linglib.Syntax.Minimalist.Derivation.Remnant
public import Linglib.Syntax.Minimalist.Copy.ToTree
public import Linglib.Syntax.Minimalist.Derivation.Smuggling
public import Linglib.Data.Examples.Readers

/-!
# Collins 2005: a smuggling approach to the passive in English

The external argument of the passive is Merged in Spec,vP, as in the active, and the participle
phrase PartP moves to the specifier of a VoiceP headed by *by*, carrying the object past the
external argument so that Infl can attract it. This file builds the passive and its rivals, head
movement of the verb and no movement, as derivations, and checks the paper's examples against the
sentences they pronounce, against Infl's probe search, and against the binding conditions of
`Syntax/Binding` evaluated at the surface or at some stage of the derivation. What holds of the
template clause of a shape holds of every clause of that shape, since its derivations are the
template's with the tokens renamed.

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
preposition, or a PP, carrying its leaf, its word, or with `Unit` nothing but its shape. -/
inductive Complement (α : Type)
  | particle (x : α)
  | pp (x : α)
  deriving DecidableEq, Fintype, Repr

namespace Complement

variable {α β : Type}

/-- The value a complement carries. -/
@[simp] def val : Complement α → α
  | .particle x | .pp x => x

/-- The complement with its value mapped by `f`. -/
@[simp] def map (f : α → β) : Complement α → Complement β
  | .particle x => .particle (f x)
  | .pp x => .pp (f x)

@[simp] theorem val_map (f : α → β) (c : Complement α) : (c.map f).val = f c.val := by
  cases c <;> rfl

end Complement

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
  /-- Voice, which takes a vP (§4). -/
  voice : LexicalItem.Token
  /-- The complement of the verb, with the patient in Spec,VP. -/
  complement : Option (Complement LexicalItem.Token)

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

/-- The clause of the given words, its external argument silent when its word is empty and its
Voice spelled out as *by* over an overt external argument and as Ø over a silent one (47). -/
def of (verb agent patient : String) (complement : Option (Complement String) := none)
    (be : String := "was") : Clause :=
  ⟨⟨.of .V (if complement.isSome then [.P, .D] else [.D]) (phonForm := verb), 1⟩,
    ⟨.of .D [] (phonForm := agent), 2⟩, ⟨.of .D [] (phonForm := patient), 3⟩,
    ⟨.of .V [] (phonForm := be), 4⟩,
    ⟨.of .Voice [.v] (phonForm := if agent.isEmpty then "" else "by"), 7⟩,
    complement.map (·.map fun w ↦ ⟨.of .P [] (phonForm := w), 11⟩)⟩

variable (p : Clause)

/-- The clause with its tokens renamed by `f`. -/
@[simps] def map (f : LexicalItem.Token → LexicalItem.Token) : Clause :=
  ⟨f p.verb, f p.agent, f p.patient, f p.be, f p.voice, p.complement.map (·.map f)⟩

/-- The VP, the verb with its object (8) or with a complement as `{Patient, {V, X}}` (17). -/
def vpSteps : List Step :=
  match p.complement with
  | some c => [.em .right c.val, .em .left p.patient]
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
          if (p.evacuee? evacuate).isSome then .traceOf c.val else leaf c.val}}
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
def ex56 : Clause := .of "given" "John" "the book" (some (.pp "to Mary"))

theorem ex23_active :
    ex23.active.surfacePhon.flatMap (Gloss.tokens ·) = Gloss.tokens Examples.ex23a.primaryText := by
  decide

theorem active_shares_vP (p : Clause) (a : Analysis) :
    p.active.take (p.vP false).length = (p.passive a false).take (p.vP false).length := by
  simp [Clause.active, Clause.passive, Clause.preRaising, Clause.fronted, Clause.voiceP]

theorem cCommandsAt_vP_iff (p : Clause) (a : Analysis) {x y : SyntacticObject} :
    p.active.CCommandsAt (p.vP false).length x y ↔
      (p.passive a false).CCommandsAt (p.vP false).length x y := by
  rw [Derivation.CCommandsAt, Derivation.CCommandsAt, active_shares_vP]

example : ex9.active.CCommandsAt (ex9.vP false).length ex9.agent ex9.patient := by decide

/-! ### Renaming clauses

Renaming the tokens of a clause renames its derivations, as long as the heads every clause shares
stay fixed, so convergence, smuggling, Freezing and c-command, all invariant under renamings that
preserve selection, depend on a clause only through its shape. -/

/-- The heads every clause shares. -/
def heads : List LexicalItem.Token := [part₀, v₀, x₀, infl₀]

namespace Clause

variable (p : Clause) {f : LexicalItem.Token → LexicalItem.Token}

theorem partP_map (hh : ∀ t ∈ heads, f t = t) (ev : Bool) :
    (p.map f).partP ev = (p.partP ev).map f := by
  have hp : f part₀ = part₀ := hh _ (by simp [heads])
  rcases p with ⟨_, _, _, _, _, _ | (_ | _)⟩ <;> cases ev <;> simp [partP, evacuee?, hp]

theorem vP_map (hh : ∀ t ∈ heads, f t = t) (ev : Bool) : (p.map f).vP ev = (p.vP ev).map f := by
  have hp : f part₀ = part₀ := hh _ (by simp [heads])
  have hv : f v₀ = v₀ := hh _ (by simp [heads])
  have hx : f x₀ = x₀ := hh _ (by simp [heads])
  rcases p with ⟨_, _, _, _, _, _ | (_ | _)⟩ <;> cases ev <;>
    simp [vP, vpSteps, evacuation, evacuee?, Derivation.map, Step.map, hp, hv, hx]

theorem voiceP_map (hh : ∀ t ∈ heads, f t = t) (ev : Bool) :
    (p.map f).voiceP ev = (p.voiceP ev).map f := by
  simp [voiceP, vP_map p hh, Step.map]

theorem preRaising_map (hh : ∀ t ∈ heads, f t = t) (a : Analysis) (ev : Bool) :
    (p.map f).preRaising a ev = (p.preRaising a ev).map f := by
  have hi : f infl₀ = infl₀ := hh _ (by simp [heads])
  cases a <;> simp [preRaising, fronted, voiceP_map p hh, partP_map p hh, Step.map, hi]

theorem passive_map (hh : ∀ t ∈ heads, f t = t) (a : Analysis) (ev : Bool) :
    (p.map f).passive a ev = (p.passive a ev).map f := by
  simp [passive, preRaising_map p hh, Step.map]

variable (hf : Function.Injective f) (hsel : LexicalItem.Token.PreservesSelection f)
  (hh : ∀ t ∈ heads, f t = t)

include hf hsel hh in
theorem converges_map (a : Analysis) (ev : Bool) :
    (p.map f).Converges a ev ↔ p.Converges a ev := by
  have hi : f infl₀ = infl₀ := hh _ (by simp [heads])
  rw [Converges, InflFinds, Converges, InflFinds, preRaising_map p hh,
    Derivation.externalize?_map hf fun s ↦ s.selHead_map hsel]
  cases (p.preRaising a ev).externalize? with
  | none => simp
  | some t =>
    simpa [hi] using LinearizedSyntacticObject.mem_goals_leafProbe_map_iff (t := t)
      (c := .D) (h := infl₀) (x := p.patient) hf hsel.cat

include hf hsel hh in
theorem isSmugglingStep_map (a : Analysis) (ev : Bool) :
    ((p.map f).passive a ev).IsSmugglingStep ((p.map f).voiceP ev).length (p.map f).patient
        (p.map f).agent ↔
      (p.passive a ev).IsSmugglingStep (p.voiceP ev).length p.patient p.agent := by
  rw [passive_map p hh, voiceP_map p hh, Derivation.length_map]
  simpa using Derivation.isSmugglingStep_map_iff (d := p.passive a ev)
    (i := (p.voiceP ev).length) (xp := p.patient) (w := p.agent) hf hsel

include hf hh in
theorem obeysFreezing_map (a : Analysis) (ev : Bool) :
    ((p.map f).passive a ev).ObeysFreezing ↔ (p.passive a ev).ObeysFreezing := by
  rw [passive_map p hh, Derivation.obeysFreezing_map_iff hf]

include hf hh in
theorem isRemnantStep_map (a : Analysis) (ev : Bool) (t : LexicalItem.Token) :
    ((p.map f).passive a ev).IsRemnantStep ((p.map f).voiceP ev).length (f t) ↔
      (p.passive a ev).IsRemnantStep (p.voiceP ev).length t := by
  rw [passive_map p hh, voiceP_map p hh, Derivation.length_map, Derivation.isRemnantStep_map_iff hf]

end Clause

/-! ### Every clause of a shape -/

/-- The template of a shape, with empty words and a pronounced external argument. -/
def Clause.template (s : Option (Complement Unit)) : Clause :=
  .of "" "x" "" (s.map (·.map fun _ ↦ ""))

/-- The renaming that takes the tokens of `T` to those of `p`, swapping the tokens that share an
index. -/
def Clause.renaming (T p : Clause) : Equiv.Perm LexicalItem.Token :=
  Equiv.swap T.verb p.verb * Equiv.swap T.agent p.agent * Equiv.swap T.patient p.patient *
    Equiv.swap T.be p.be * Equiv.swap T.voice p.voice *
    match T.complement, p.complement with
    | some c, some c' => Equiv.swap c.val c'.val
    | _, _ => 1

section Shape

variable (verb agent patient be : String) (c : Option (Complement String))

local notation "T" => Clause.template (c.map (Complement.map fun _ ↦ ()))

local notation "σ" => Clause.renaming T (Clause.of verb agent patient c be)

theorem of_eq_map : Clause.of verb agent patient c be = (T).map σ := by
  rcases c with _ | (_ | _) <;>
    simp [Clause.of, Clause.template, Clause.map, Clause.renaming, Equiv.swap_apply_of_ne_of_ne]

theorem renaming_preservesSelection : LexicalItem.Token.PreservesSelection σ := by
  rcases c with _ | (_ | _) <;>
    simp only [Clause.renaming, Clause.template, Clause.of, Option.map_some, Option.map_none,
      Complement.map, Equiv.Perm.coe_mul] <;>
    refine .comp (.comp (.comp (.comp (.comp ?_ ?_) ?_) ?_) ?_) ?_ <;>
    first
    | exact .id
    | exact .swap rfl rfl (by simp [LexicalItem.Token.bareTrace])
        (by simp [LexicalItem.Token.bareTrace])

theorem renaming_heads : ∀ t ∈ heads, σ t = t := by
  rcases c with _ | (_ | _) <;>
    simp [heads, Clause.renaming, Clause.template, Clause.of, Complement.map, part₀, v₀, x₀,
      infl₀, Equiv.swap_apply_of_ne_of_ne]

/-! ### Smuggling (§5, §6) -/

/-- In every clause only PartP smuggling converges under Relativized Minimality, so head movement
and *The book was by John written* (9a), (36), both fail (§5). -/
theorem converges_iff (a : Analysis) (ev : Bool) :
    (Clause.of verb agent patient c be).Converges a ev ↔ a = .partP := by
  rw [of_eq_map, Clause.converges_map _ (Equiv.injective _) (renaming_preservesSelection ..)
    (renaming_heads _ _ _ _ _)]
  generalize c.map (Complement.map fun _ ↦ ()) = s
  revert s a ev
  decide +kernel

theorem isSmugglingStep_iff (a : Analysis) (ev : Bool) :
    ((Clause.of verb agent patient c be).passive a ev).IsSmugglingStep
        ((Clause.of verb agent patient c be).voiceP ev).length
        (Clause.of verb agent patient c be).patient
        (Clause.of verb agent patient c be).agent ↔ a = .partP := by
  rw [of_eq_map, Clause.isSmugglingStep_map _ (Equiv.injective _)
    (renaming_preservesSelection ..) (renaming_heads _ _ _ _ _)]
  generalize c.map (Complement.map fun _ ↦ ()) = s
  revert s a ev
  decide +kernel

theorem converges_iff_not_obeysFreezing (a : Analysis) (ev : Bool) :
    (Clause.of verb agent patient c be).Converges a ev ↔
      ¬ ((Clause.of verb agent patient c be).passive a ev).ObeysFreezing := by
  rw [of_eq_map, Clause.converges_map _ (Equiv.injective _) (renaming_preservesSelection ..)
    (renaming_heads _ _ _ _ _),
    Clause.obeysFreezing_map _ (Equiv.injective _) (renaming_heads _ _ _ _ _)]
  generalize c.map (Complement.map fun _ ↦ ()) = s
  revert s a ev
  decide +kernel

-- (58)
theorem isRemnantStep_iff (w : String) (a : Analysis) (ev : Bool) :
    ∀ x ∈ (Clause.of verb agent patient (some (.pp w)) be).complement,
      ((Clause.of verb agent patient (some (.pp w)) be).passive a ev).IsRemnantStep
          ((Clause.of verb agent patient (some (.pp w)) be).voiceP ev).length x.val ↔
        a = .partP ∧ ev = true := by
  rw [of_eq_map]
  simp only [Clause.map_complement, Option.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Complement.val_map]
  intro x hx
  rw [Clause.isRemnantStep_map _ (Equiv.injective _) (renaming_heads _ _ _ _ _)]
  simp only [Clause.template, Clause.of, Option.map_some, Complement.map, Option.mem_def,
    Option.some.injEq] at hx
  subst hx
  simp only [Option.map_some, Complement.map]
  revert a ev
  decide +kernel

end Shape

/-- Smuggling brings the object level with the external argument, not past it: once PartP has
moved, Infl's probe finds both. -/
example : ex9.InflFinds .partP false ex9.agent := by decide +kernel

theorem ex45_surfacePhon (a : Analysis) :
    (ex45.passive a false).surfacePhon = (ex45.passive .partP false).surfacePhon := by
  cases a <;> decide

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
  return .of verb agent patient
    ((row.feature? "particle").map .particle <|> (row.feature? "pp").map .pp)
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
  | .pp => p.complement.map Complement.val

/-- The level at which a dependency is evaluated, the surface or some stage of the derivation,
reconstruction included. -/
inductive Level
  | surface | anyStage
  deriving DecidableEq, Fintype, Repr

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

theorem Level.cCommands_map_iff {f : LexicalItem.Token → LexicalItem.Token}
    (hf : Function.Injective f) (hsel : LexicalItem.Token.PreservesSelection f) (ℓ : Level)
    (d : Derivation) (x y : SyntacticObject) :
    ℓ.CCommands (d.map f) (x.map f) (y.map f) ↔ ℓ.CCommands d x y := by
  cases ℓ
  · exact Derivation.bindsAtSurface_map_iff hf hsel
  · exact Derivation.bindsAtSomeStage_map_iff hf hsel

theorem Level.configuration_map {f : LexicalItem.Token → LexicalItem.Token}
    (hf : Function.Injective f) (hsel : LexicalItem.Token.PreservesSelection f) (ℓ : Level)
    (p : Clause) (d : Derivation) :
    ℓ.configuration (p.map f) (d.map f) = ℓ.configuration p d := by
  have hat (z : Position) : (p.map f).at? z = (p.at? z).map f := by
    cases z <;> rcases p with ⟨_, _, _, _, _, _ | (_ | _)⟩ <;> rfl
  simp only [Level.configuration, Binding.Configuration.monoclausal, hat]
  congr 1
  funext x y
  apply propext
  cases p.at? x <;> cases p.at? y <;>
    simp only [Option.map_some, Option.map_none, Option.mem_def, Option.some.injEq,
      exists_eq_left', reduceCtorEq, false_and, exists_false]
  rw [← map_leaf, ← map_leaf]
  exact Level.cCommands_map_iff hf hsel ℓ d _ _

section Shape

variable (verb agent patient be w : String)

/-- In every passive with a PP, the external argument commands the PP exactly when binding is
evaluated at some stage, or once the PP has left PartP (§7, §10). -/
theorem commands_external_pp_iff (ℓ : Level) (ev : Bool) :
    (ℓ.configuration (.of verb agent patient (some (.pp w)) be)
        ((Clause.of verb agent patient (some (.pp w)) be).passive .partP ev)).commands
      .external .pp ↔ ℓ = .anyStage ∨ ev = true := by
  rw [of_eq_map, Clause.passive_map _ (renaming_heads _ _ _ _ _),
    Level.configuration_map (Equiv.injective _) (renaming_preservesSelection ..)]
  simp only [Option.map_some, Complement.map]
  revert ℓ ev
  decide +kernel

theorem not_commands_pp_external (ℓ : Level) (ev : Bool) :
    ¬ (ℓ.configuration (.of verb agent patient (some (.pp w)) be)
        ((Clause.of verb agent patient (some (.pp w)) be).passive .partP ev)).commands
      .pp .external := by
  rw [of_eq_map, Clause.passive_map _ (renaming_heads _ _ _ _ _),
    Level.configuration_map (Equiv.injective _) (renaming_preservesSelection ..)]
  simp only [Option.map_some, Complement.map]
  revert ℓ ev
  decide +kernel

end Shape

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

theorem acceptable_iff_of_admits_ofProp {P : Prop} [Decidable P] {j : Judgment}
    (h : (ofProp P).Admits j) : j = .acceptable ↔ P := by
  by_cases hP : P <;> simp_all [ofProp, Admits]

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
(75), Principle B (80a) and Principle C (76a), (85) follow from the position of the PP ((60)). -/
theorem licensing_rows :
    (∀ row ∈ Examples.all, ∀ c ∈ Licensing.ofRow row, c.verdict.Admits row.judgment) ∧
      Datum.ReadCount Licensing.ofRow Examples.all 14 := by
  decide +kernel

-- (73): an anaphor or bound variable marked as reconstructed is one that the reading with no chain
-- read low does not bind and the reading deleting the highest copy of the phrase carrying it does.
-- Principle B stays on the stages: (83) is derivational, and reading it off an LF is the obligatory
-- reconstruction the paper rejects in (82).
theorem reconstructed_iff_reading :
    ∀ row ∈ Examples.all, ∀ c ∈ Licensing.ofRow row,
      (c.dependency = .condition .reflexive ∨ c.dependency = .condition .reciprocal ∨
        c.dependency = .variable) →
      ∀ x ∈ c.clause.at? c.antecedent, ∀ y ∈ c.clause.at? c.dependent,
        ∀ m ∈ c.derivation.replayWithCopies?,
          (c.verdict = .reconstructed ↔ ¬ c.derivation.BindsAtReading ∅ ↑x ↑y ∧
            c.derivation.BindsAtReading (m.current.carrying y) ↑x ↑y) := by
  decide +kernel

/-- The rows of a binding class fit its condition evaluated at level `ℓ`, each row acceptable
exactly when the condition holds. -/
def FitsAt (cls : Binding.BindingClass) (ℓ : Level) : Prop :=
  ∀ row ∈ Examples.all, ∀ c ∈ Licensing.ofRow row, c.dependency = .condition cls →
    (row.judgment = .acceptable ↔
      ℓ.Condition c.clause c.derivation c.antecedent c.dependent cls)

instance (cls : Binding.BindingClass) (ℓ : Level) : Decidable (FitsAt cls ℓ) := by
  unfold FitsAt; infer_instance

theorem not_fitsAt {cls : Binding.BindingClass} {ℓ : Level} {row : Datum}
    (hrow : row ∈ Examples.all)
    (h : ∃ c ∈ Licensing.ofRow row, c.dependency = .condition cls ∧
      ¬ (row.judgment = .acceptable ↔
        ℓ.Condition c.clause c.derivation c.antecedent c.dependent cls)) :
    ¬ FitsAt cls ℓ :=
  fun hf ↦ let ⟨c, hc, hd, hn⟩ := h; hn (hf row hrow c hc hd)

theorem fitsAt_pronoun_iff (ℓ : Level) : FitsAt .pronoun ℓ ↔ ℓ = .anyStage := by
  cases ℓ
  · exact iff_of_false (not_fitsAt (row := Examples.ex80a)
      (by simp only [Examples.all, List.mem_cons, true_or, or_true]) (by decide +kernel))
      (by decide)
  · refine iff_of_true (fun row hrow c hc hd ↦ ?_) rfl
    have h := licensing_rows.1 row hrow c hc
    rw [Licensing.verdict, hd] at h
    exact Verdict.acceptable_iff_of_admits_ofProp h

/-- The name rows fit Principle C exactly at the surface, (76a) excluding obligatory
reconstruction, as the pronoun rows fit Principle B exactly at every stage
(`fitsAt_pronoun_iff`) (§9) (§9.2). -/
theorem fitsAt_rExpression_iff (ℓ : Level) : FitsAt .rExpression ℓ ↔ ℓ = .surface := by
  cases ℓ
  · refine iff_of_true (fun row hrow c hc hd ↦ ?_) rfl
    have h := licensing_rows.1 row hrow c hc
    rw [Licensing.verdict, hd] at h
    exact Verdict.acceptable_iff_of_admits_ofProp h
  · exact iff_of_false (not_fitsAt (row := Examples.ex76a)
      (by simp only [Examples.all, List.mem_cons, true_or, or_true]) (by decide +kernel))
      (by decide)

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
