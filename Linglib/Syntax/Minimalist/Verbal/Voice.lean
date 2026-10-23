module

public import Linglib.Syntax.Minimalist.Feature.Basic
public import Linglib.Core.Order.Flat

/-!
# Voice heads

Voice introduces, or fails to introduce, the external argument of the verbal phrase it takes, as
Kratzer proposed. A head is a cell of Alexiadou and Schäfer's typology after Schäfer: thematic
Voice introduces an external-argument variable with an instruction for interpreting it, as an
agent, a causer or a holder, and expletive Voice introduces nothing; active Voice bears a
D-feature and projects a specifier, non-active Voice does not, its variable, if any,
existentially bound and implicit. The four cells are the active and non-active thematic heads,
the transitive and the passive, and the active and non-active expletive heads, the *se*-marked
anticausative and the non-active middle. Beyond its cell a head may bind the internal argument to
the external one, reflexively or reciprocally, or demote it to an oblique, the antipassive; may
check the accusative Case that v otherwise checks; and may carry Agree features.

Every property consumers read is derived from the cell: `Head.IsThematic`, `Head.AssignsTheta`,
`Head.ExternalImplicit`, `Head.IsPhasal`, and `Head.params`, the cell as a pair of `Flat Bool`
coordinates that a morpheme spelling out several heads may leave open.

## Main definitions

* `Instruction`, `Operation`, `Head`: the thematic instruction, the valency operation and the
  head.
* `Head.IsThematic`, `Head.HasD`, `Head.ExternalImplicit`, `Head.AssignsTheta`, `Head.IsPhasal`,
  `Head.ChecksCase`, `Head.DCoherent`: the predicate API.
* `agentive`, `causer`, `experiencer`, `anticausative`, `middle`, `passive`, `impersonal`,
  `reflexive`, `reciprocal`, `antipassive`: the named cells.
* `Params`, `Head.params`: the ±D/±λx cell with either coordinate left open.

## Main results

* `Head.AssignsTheta.isThematic`, `Head.IsPhasal.assignsTheta`: θ-assignment entails a thematic
  head, and phasehood entails θ-assignment.
* `canonical_dCoherent`: every named cell realizes its variable in its specifier exactly when it
  has one.
* `antipassive_not_phasal`: the antipassive is thematic and active yet not a phase.

## Implementation notes

* The passive is the thematic non-active cell, its agent implicit, with the Finnish impersonal in
  the same cell; Collins's passive Voice, which assigns no θ-role and checks Case, is statable
  here as an expletive active head with `checksCase`.
* Phasehood is that of Chomsky's v*, a θ-assigning active head, with the antipassive excepted
  because it detransitivizes. A study that separates the phase head v from Voice reads its own
  v off the Voice head below it.
* Cuervo's inchoatives have no Voice at all, and the event structure below Voice is
  `Minimalist.LittleV`.

## References

* [alexiadou-anagnostopoulou-schaefer-2015]
* [beavers-udayana-2022]
* [chomsky-2001]
* [collins-2005]
* [cuervo-2003]
* [kratzer-1996]
* [martin-schaefer-kastner-2025]
* [munoz-perez-2026]
* [schaefer-2008]
* [schaefer-2017]
* [scott-2023]
* [siloni-2012]
* [wood-2015]
-/
@[expose] public section

namespace Minimalist.Voice

/-! ### The cell -/

/-- The instruction a thematic Voice head gives for interpreting its external-argument
variable ([alexiadou-anagnostopoulou-schaefer-2015]). -/
inductive Instruction where
  | agent
  | causer
  | holder
  deriving DecidableEq, Repr

/-- What a head does to the internal argument beyond introducing an external one, binding it to
the external argument reflexively or reciprocally ([siloni-2012]) or demoting it to an oblique
([scott-2023]). -/
inductive Operation where
  | reflexive
  | reciprocal
  | antipassive
  deriving DecidableEq, Repr

/-- A Voice head, with its cell in the thematic/expletive × active/non-active typology, whether
its variable is implicit, its valency operation, and its per-construction properties. -/
structure Head where
  /-- The external-argument variable λx with its instruction, `none` for expletive Voice. -/
  thematic : Option Instruction
  /-- The head bears D and projects a specifier. -/
  hasD : Bool
  /-- The variable is existentially bound rather than saturated by a specifier DP. -/
  implicit : Bool := false
  /-- The operation on the internal argument, if any. -/
  operation : Option Operation := none
  /-- Checks the accusative Case that v otherwise checks, as [collins-2005]'s passive Voice
  does. -/
  checksCase : Bool := false
  /-- Agree-relevant features (e.g. [uOblique] for Mam *=(y)a'*). -/
  features : FeatureBundle := ⊥
  deriving DecidableEq, Repr

namespace Head

variable (v : Head)

/-! ### Predicate API -/

/-- The head is thematic when it introduces an external-argument variable, and so has
semantics. -/
def IsThematic : Prop := v.thematic.isSome = true

/-- Projects a specifier. -/
def HasD : Prop := v.hasD = true

/-- The external argument is existentially bound. -/
def ExternalImplicit : Prop := v.implicit = true

/-- Assigns a θ-role to a DP in its specifier: thematic, with its variable not implicit. -/
def AssignsTheta : Prop := v.IsThematic ∧ ¬ v.ExternalImplicit

/-- Checks Case. -/
def ChecksCase : Prop := v.checksCase = true

/-- The head is a phase head, [chomsky-2001]'s v*, when it assigns a θ-role and is active,
unless it is the antipassive, which detransitivizes. -/
def IsPhasal : Prop := v.AssignsTheta ∧ v.HasD ∧ v.operation ≠ some .antipassive

/-- A thematic head's variable is implicit exactly when the head projects no specifier, as in
[alexiadou-anagnostopoulou-schaefer-2015]'s grid; a head may diverge, and stating the divergence
makes it explicit. -/
def DCoherent : Prop := v.IsThematic → v.implicit = !v.hasD

instance : Decidable v.IsThematic := inferInstanceAs (Decidable (_ = _))
instance : Decidable v.HasD := inferInstanceAs (Decidable (_ = _))
instance : Decidable v.ExternalImplicit := inferInstanceAs (Decidable (_ = _))
instance : Decidable v.AssignsTheta := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable v.ChecksCase := inferInstanceAs (Decidable (_ = _))
instance : Decidable v.IsPhasal := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable v.DCoherent := inferInstanceAs (Decidable (_ → _))

theorem AssignsTheta.isThematic {v : Head} (h : v.AssignsTheta) : v.IsThematic := h.1

theorem IsPhasal.assignsTheta {v : Head} (h : v.IsPhasal) : v.AssignsTheta := h.1

end Head

/-! ### The underspecified cell -/

/-- The ±D/±λx cell, whether a head projects a specifier and whether it is thematic, with either
coordinate left open for a morpheme that spells out several heads
([alexiadou-anagnostopoulou-schaefer-2015], [beavers-udayana-2022]). A coordinate is a
`Flat Bool`, `⊥` when open, so cells are ordered by subsumption and are compatible (`Compat`)
when they agree wherever both are specified. -/
abbrev Params := Flat Bool × Flat Bool

/-- The cell of a head, fully specified. -/
def Head.params (v : Head) : Params := (v.hasD, v.thematic.isSome)

/-! ### The named cells -/

/-- Thematic active Voice introducing an agent, the transitive and unergative head v*. -/
def agentive : Head := { thematic := some .agent, hasD := true }

/-- Thematic active Voice introducing a causer. -/
def causer : Head := { thematic := some .causer, hasD := true }

/-- Thematic active Voice introducing a holder, the experiencer subject of a psych
causative. -/
def experiencer : Head := { thematic := some .holder, hasD := true }

/-- Expletive active Voice, with no variable and a specifier for a marker such as Romance *se*,
the marked anticausative ([munoz-perez-2026]). -/
def anticausative : Head := { thematic := none, hasD := true }

/-- Expletive non-active Voice, with neither variable nor specifier, the dispositional middle. -/
def middle : Head := { thematic := none, hasD := false }

/-- Thematic non-active Voice, its agent existentially bound and implicit, the passive. -/
def passive : Head := { thematic := some .agent, hasD := false, implicit := true }

/-- The Finnish impersonal, the same cell as the passive, with an implicit generic agent. -/
def impersonal : Head := passive

/-- Agentive Voice binding the internal argument to the agent, Romance reflexive *se*
([martin-schaefer-kastner-2025]). [wood-2015]'s Icelandic *-st* is a SpecpP clitic, not an
exponent of this head. -/
def reflexive : Head := { agentive with operation := some .reflexive }

/-- Agentive Voice putting the agent in the mutual relation with the internal argument,
[siloni-2012]'s syntactic reciprocalization. Lexically reciprocal verbs enter the syntax
symmetric and are not exponents of this head. -/
def reciprocal : Head := { agentive with operation := some .reciprocal }

/-- Agentive Voice demoting the object to an oblique, with absolutive on the agent
([scott-2023]). -/
def antipassive : Head := { agentive with operation := some .antipassive }

/-! ### Verification -/

theorem assignsTheta_cells :
    agentive.AssignsTheta ∧ causer.AssignsTheta ∧ experiencer.AssignsTheta ∧
      reflexive.AssignsTheta ∧ reciprocal.AssignsTheta ∧ antipassive.AssignsTheta ∧
      ¬ anticausative.AssignsTheta ∧ ¬ middle.AssignsTheta ∧ ¬ passive.AssignsTheta := by
  decide

theorem passive_anticausative :
    passive.IsThematic ∧ passive.ExternalImplicit ∧ ¬ anticausative.IsThematic ∧
      anticausative.HasD := by
  decide

theorem canonical_dCoherent :
    agentive.DCoherent ∧ causer.DCoherent ∧ experiencer.DCoherent ∧
      anticausative.DCoherent ∧ middle.DCoherent ∧ passive.DCoherent ∧ reflexive.DCoherent ∧
      reciprocal.DCoherent ∧ antipassive.DCoherent := by
  decide

theorem phasal_cells :
    agentive.IsPhasal ∧ causer.IsPhasal ∧ ¬ anticausative.IsPhasal ∧ ¬ middle.IsPhasal ∧
      ¬ passive.IsPhasal := by
  decide

theorem antipassive_not_phasal : antipassive.AssignsTheta ∧ ¬ antipassive.IsPhasal := by decide

end Minimalist.Voice
