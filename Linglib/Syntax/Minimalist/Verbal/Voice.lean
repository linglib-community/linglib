module

public import Linglib.Syntax.Minimalist.Feature.Basic
public import Linglib.Core.Order.Flat

/-!
# Voice heads

This file defines Voice heads, which introduce or fail to introduce the external argument of the
verbal phrase they take, as Kratzer proposed. A head is a cell of the typology of Alexiadou,
Anagnostopoulou and Schäfer: thematic Voice introduces an external-argument variable with an
instruction for interpreting it, and expletive Voice introduces none; active Voice bears a
D-feature and projects a specifier, and non-active Voice does not, its variable, if any, being
existentially bound. A head may also check the accusative Case that v otherwise checks, and carry
Agree features.

## Main definitions

* `Minimalist.Voice.Head`: a Voice head, its cell with its Case checking and features.
* `Minimalist.Voice.Head.IsThematic`, `Minimalist.Voice.Head.AssignsTheta`,
  `Minimalist.Voice.Head.IsPhasal`: the predicates on a head.
* `Minimalist.Voice.agentive`, `Minimalist.Voice.anticausative`, `Minimalist.Voice.middle`,
  `Minimalist.Voice.passive`: the named cells.
* `Minimalist.Voice.Params`: the ±D/±λx cell with either coordinate left open.

## Implementation notes

* The passive is the thematic non-active cell, its agent implicit, with the Finnish impersonal in
  the same cell. Collins's passive Voice, which assigns no θ-role and checks Case, is an expletive
  active head that checks Case.
* Reflexive, reciprocal and antipassive voices are not cells of their own: they are what a
  θ-assigning head derives with its internal argument implicit or oblique.
* Phasehood is that of Chomsky's v*, a θ-assigning active head. A study that separates the phase
  head v from Voice reads its own v off the Voice head below it.
* Cuervo's inchoatives have no Voice at all, and the event structure below Voice is
  `Minimalist.LittleV`.

## References

* [alexiadou-anagnostopoulou-schaefer-2015]
* [beavers-udayana-2022]
* [chomsky-2001]
* [collins-2005]
* [cuervo-2003]
* [kratzer-1996]
* [munoz-perez-2026]
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

/-- A Voice head, with its cell in the thematic/expletive × active/non-active typology, whether
its variable is implicit, and its per-construction properties. -/
structure Head where
  /-- The external-argument variable λx with its instruction, `none` for expletive Voice. -/
  thematic : Option Instruction
  /-- The head bears D and projects a specifier. -/
  hasD : Bool
  /-- The variable is existentially bound rather than saturated by a specifier DP. -/
  implicit : Bool := false
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

/-- The head is a phase head, [chomsky-2001]'s v*, when it assigns a θ-role and is active. -/
def IsPhasal : Prop := v.AssignsTheta ∧ v.HasD

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

end Minimalist.Voice
