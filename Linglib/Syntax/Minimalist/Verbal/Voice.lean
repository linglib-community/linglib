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
Agree features. It has a value besides its cell, active or non-active by default, which a flavor of
Voice such as the reflexive overrides. Heads are ordered by subsumption: one lies below another when
the two share their value and instruction and the other bears every D-feature, implicit variable,
Case and Agree feature it does. D is thus privative, and [a head that only lacks D does not clash
with one that has it](##Minimalist.Voice.Head.compat_iff), while two values do.

## Main definitions

* `Minimalist.Voice.Value`: the values of a Voice head.
* `Minimalist.Voice.Head`: a Voice head, its cell with its Case checking, features and value.
* `Minimalist.Voice.Head.IsThematic`, `Minimalist.Voice.Head.AssignsTheta`,
  `Minimalist.Voice.Head.IsPhasal`: the predicates on a head.
* `Minimalist.Voice.agentive`, `Minimalist.Voice.anticausative`, `Minimalist.Voice.middle`,
  `Minimalist.Voice.passive`: the named cells.
* `Minimalist.Voice.reflexive`: reflexive Voice, in the cell of `agentive` with its own value.
* `Minimalist.Voice.Params`: the ±D/±λx cell with either coordinate left open.

## Implementation notes

* The passive is the thematic non-active cell, its agent implicit, with the Finnish impersonal in
  the same cell. Collins's passive Voice, which assigns no θ-role and checks Case, is an expletive
  active head that checks Case.
* Reflexive, reciprocal and antipassive voices are not cells of their own: they are what a
  θ-assigning head derives with its internal argument implicit, oblique or absent. A reflexive flavor
  of Voice, in the cell of `agentive`, differs from it in `value` ([beslin-2026]).
* `Params` is the binary cell, for a morpheme that spells out several heads; ellipsis compares the
  order on `Head`, where D is privative.
* Phasehood is that of Chomsky's v*, a θ-assigning active head. A study that separates the phase
  head v from Voice reads its own v off the Voice head below it.
* Cuervo's inchoatives have no Voice at all, and the event structure below Voice is
  `Minimalist.LittleV`.

## References

* [alexiadou-anagnostopoulou-schaefer-2015]
* [beavers-udayana-2022]
* [beslin-2026]
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

/-- The values of a Voice head, a multivalued feature: two heads with different values clash under
ellipsis ([merchant-2013], [ranero-2021], [beslin-2026]). -/
inductive Value where
  | active
  | nonActive
  | reflexive
  | antipassive
  deriving DecidableEq, Repr

/-- A Voice head, with its cell in the thematic/expletive × active/non-active typology, whether
its variable is implicit, its per-construction properties, and its value. -/
@[ext]
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
  /-- The value, active or non-active as the head bears D unless a flavor overrides it. -/
  value : Value := if hasD then .active else .nonActive
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

/-! ### Subsumption -/

/-- One head lies below another when the two share their multivalued features and the other bears
every privative feature it does. `Bool`, ordered with `false` below `true`, is what privative
means: a D-feature, an implicit variable or Case checking is absent or present, and never clashes. -/
instance : PartialOrder Head where
  le v w := v.value = w.value ∧ v.thematic = w.thematic ∧ v.hasD ≤ w.hasD ∧
    v.implicit ≤ w.implicit ∧ v.checksCase ≤ w.checksCase ∧ v.features ≤ w.features
  le_refl _ := ⟨rfl, rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
    h₁.2.2.2.1.trans h₂.2.2.2.1, h₁.2.2.2.2.1.trans h₂.2.2.2.2.1, h₁.2.2.2.2.2.trans h₂.2.2.2.2.2⟩
  le_antisymm _ _ h₁ h₂ := Head.ext h₁.2.1 (h₁.2.2.1.antisymm h₂.2.2.1)
    (h₁.2.2.2.1.antisymm h₂.2.2.2.1) (h₁.2.2.2.2.1.antisymm h₂.2.2.2.2.1)
    (h₁.2.2.2.2.2.antisymm h₂.2.2.2.2.2) h₁.1

theorem le_iff {v w : Head} : v ≤ w ↔ v.value = w.value ∧ v.thematic = w.thematic ∧
    v.hasD ≤ w.hasD ∧ v.implicit ≤ w.implicit ∧ v.checksCase ≤ w.checksCase ∧
      v.features ≤ w.features := .rfl

/-- `v` with the privative features of `w` added and the Agree features `f`. -/
def join (v w : Head) (f : FeatureBundle) : Head :=
  { v with hasD := v.hasD ⊔ w.hasD, implicit := v.implicit ⊔ w.implicit,
           checksCase := v.checksCase ⊔ w.checksCase, features := f }

/-- Unification merges the privative features of two heads that share their multivalued ones. -/
instance : PartialUnify Head where
  unify v w :=
    if v.value = w.value ∧ v.thematic = w.thematic then
      (PartialUnify.unify v.features w.features).map (join v w)
    else ⊤
  isLUB_of_unify_eq_coe {v w c} h := by
    split_ifs at h with hm
    · cases hf : PartialUnify.unify v.features w.features with
      | top => simp [hf] at h
      | coe f =>
        obtain rfl : join v w f = c := WithTop.coe_inj.1 (by simpa [hf] using h)
        have hl := PartialUnify.isLUB_of_unify_eq_coe hf
        refine ⟨?_, fun u hu ↦ ?_⟩
        · rintro _ (rfl | rfl)
          · exact ⟨rfl, rfl, le_sup_left, le_sup_left, le_sup_left, hl.1 (Set.mem_insert _ _)⟩
          · exact ⟨hm.1.symm, hm.2.symm, le_sup_right, le_sup_right, le_sup_right,
              hl.1 (Set.mem_insert_of_mem _ rfl)⟩
        · obtain ⟨hv, hw⟩ := mem_upperBounds_pair.1 hu
          exact ⟨hv.1, hv.2.1, sup_le hv.2.2.1 hw.2.2.1, sup_le hv.2.2.2.1 hw.2.2.2.1,
            sup_le hv.2.2.2.2.1 hw.2.2.2.2.1,
            hl.2 (mem_upperBounds_pair.2 ⟨hv.2.2.2.2.2, hw.2.2.2.2.2⟩)⟩
    · exact absurd h WithTop.top_ne_coe
  unify_ne_top_of_bddAbove {v w} := by
    rintro ⟨u, hu⟩
    obtain ⟨hv, hw⟩ := mem_upperBounds_pair.1 hu
    have hf := PartialUnify.unify_ne_top_of_bddAbove (a := v.features) (b := w.features)
      ⟨u.features, mem_upperBounds_pair.2 ⟨hv.2.2.2.2.2, hw.2.2.2.2.2⟩⟩
    split_ifs with hm
    · simpa [WithTop.map_eq_top_iff] using hf
    · exact absurd ⟨hv.1.trans hw.1.symm, hv.2.1.trans hw.2.1.symm⟩ hm

/-- Two heads clash exactly when they differ in a multivalued feature or their Agree features
clash: a head that only lacks D, an implicit variable or Case checking clashes with nothing. -/
theorem compat_iff {v w : Head} : Compat v w ↔ v.value = w.value ∧ v.thematic = w.thematic ∧
    Compat v.features w.features := by
  refine ⟨fun ⟨u, hu⟩ ↦ ?_, fun ⟨h₁, h₂, b, hb⟩ ↦ ?_⟩
  · obtain ⟨hv, hw⟩ := mem_upperBounds_pair.1 hu
    exact ⟨hv.1.trans hw.1.symm, hv.2.1.trans hw.2.1.symm, .of_le hv.2.2.2.2.2 hw.2.2.2.2.2⟩
  · obtain ⟨hvb, hwb⟩ := mem_upperBounds_pair.1 hb
    exact .of_le (u := join v w b) ⟨rfl, rfl, le_sup_left, le_sup_left, le_sup_left, hvb⟩
      ⟨h₁.symm, h₂.symm, le_sup_right, le_sup_right, le_sup_right, hwb⟩

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

/-- Reflexive Voice, introducing an agent as active Voice does, with a value of its own. -/
def reflexive : Head := { agentive with value := .reflexive }

end Minimalist.Voice
