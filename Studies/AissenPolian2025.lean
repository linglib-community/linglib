module

public import Linglib.Syntax.Minimalist.Probe.SyntacticObject
public import Linglib.Syntax.Minimalist.Probe.Horizon
public import Linglib.Syntax.Minimalist.Label.RaisingHead
public import Linglib.Data.Examples.AissenPolian2025
public import Linglib.Data.Examples.Readers

/-!
# Possessor extraction and categorical subject in Tseltalan

Aissen and Polian argue that a Tseltalan possessor never Ā-subextracts: nominal opacity, a
Keine horizon at N⁰ for the wh-probe on C⁰, forces an extracted possessor to A-move first to
Spec,TP or Spec,ApplP, where Attract Closest over DPs decides whether it can — a specific
possessive's D layer, an agent, a specific subject or theme, or an occupied Spec,ApplP stops
it. Hence only non-specific possessums strand, and the possessor that reaches Spec,TP is the
ψ-subject of a categorical judgment.

Nominal opacity is the horizon setting `nominalOpacity` read through `Invisible`, the positions
behind the probe's horizon (`HorizonSetting.cut`) under the raising head index, and C⁰'s wh-probe
searches short of them (`whGoals`).
Attract Closest is `dGoals`, the positional search for D leaves on the paper's structures,
`judgment` reads the judgment type off the same search, and the paper's examples are the rows,
over which `stranding_iff`, `piedPiping_specific` and `psi_no_piedPiping` hold.

## References

* [aissen-polian-2025]
* [keine-2019]
* [kuroda-1972]
* [little-2020b]
* [polian-2013]
* [gavruseva-2000]
* [aissen-1996]
* [coon-baier-levin-2021]
* [heycock-doron-2003]
-/

@[expose] public section

namespace AissenPolian2025

open Minimalist SyntacticObject PlanarSyntacticObject

/-! ### Probes -/

/-- Nominal opacity: the wh-probe on C⁰ has every node in the extended projection of N⁰ as its
horizon, `[wh]C⁰ ⊣‖ N`. -/
def nominalOpacity : HorizonSetting := ⟨.C, some .N⟩

/-- The [EPP:D] probe on T⁰, without horizon. -/
def dProbeT : HorizonSetting := ⟨.T, none⟩

/-- The [EPP:D] probe on Appl⁰, without horizon. -/
def dProbeAppl : HorizonSetting := ⟨.Appl, none⟩

/-- The [EPP:WH] probe on D⁰ that drives pied-piping with inversion, without horizon. -/
def secondaryWh : HorizonSetting := ⟨.D, none⟩

/-- `target` is invisible in `t` to a probe with setting `p` on `probe` when an occurrence of it
lies behind its horizon for an occurrence of the probe. -/
def Invisible (p : HorizonSetting) (t : PlanarSyntacticObject)
    (probe target : SyntacticObject) : Prop :=
  ∃ a q : t.val.Positions,
    t.termAt a = probe ∧ t.termAt q = target ∧ q.val ∈ p.cut headIndex? t a.val

instance (p : HorizonSetting) (t : PlanarSyntacticObject) (probe target : SyntacticObject) :
    Decidable (Invisible p t probe target) := by
  unfold Invisible; infer_instance

theorem not_invisible_of_horizon_none (t : PlanarSyntacticObject)
    (probe target : SyntacticObject) {p : HorizonSetting} (hp : p.horizon = none) :
    ¬ Invisible p t probe target := by
  obtain ⟨head, _⟩ := p
  subst hp
  simp [Invisible]

theorem dProbe_sees_through (t : PlanarSyntacticObject) (probe target : SyntacticObject) :
    ¬ Invisible dProbeT t probe target ∧ ¬ Invisible dProbeAppl t probe target ∧
      ¬ Invisible secondaryWh t probe target :=
  ⟨not_invisible_of_horizon_none _ _ _ rfl, not_invisible_of_horizon_none _ _ _ rfl,
   not_invisible_of_horizon_none _ _ _ rfl⟩

/-! ### The structures -/

def C₀ : PlanarSyntacticObject := .leaf ⟨.of .C [.T], 1⟩
def T₀ : PlanarSyntacticObject := .leaf ⟨.of .T [.V], 2⟩
def V₀ : PlanarSyntacticObject := .leaf ⟨.of .V [.N], 3⟩
def v₀ : PlanarSyntacticObject := .leaf ⟨.of .v [.V], 4⟩
def Appl₀ : PlanarSyntacticObject := .leaf ⟨.of .Appl [.V], 5⟩
def P₀ : PlanarSyntacticObject := .leaf ⟨.of .P [.N], 6⟩
def Psr : PlanarSyntacticObject := .leaf ⟨.of .D [], 7⟩
def Psm : PlanarSyntacticObject := .leaf ⟨.of .N [], 8⟩
def D₀ : PlanarSyntacticObject := .leaf ⟨.of .D [.N], 9⟩
def Agt : PlanarSyntacticObject := .leaf ⟨.of .D [], 10⟩
def SubjD : PlanarSyntacticObject := .leaf ⟨.of .D [], 11⟩
def SubjN : PlanarSyntacticObject := .leaf ⟨.of .N [], 12⟩
def ThemeD : PlanarSyntacticObject := .leaf ⟨.of .D [], 13⟩
def ThemeN : PlanarSyntacticObject := .leaf ⟨.of .N [], 14⟩
def Pivot : PlanarSyntacticObject := .leaf ⟨.of .N [], 15⟩

/-- A non-specific possessive, `{Psr, Psm}`. -/
def PossP : PlanarSyntacticObject := {Psr, Psm}

/-- A specific possessive, `{D⁰, PossP}`. -/
def DP : PlanarSyntacticObject := {D₀, PossP}

/-- A locative PP over a non-specific possessive, `{P, PossP}`. -/
def PP : PlanarSyntacticObject := {P₀, PossP}

/-- (9c) with a non-specific possessive S_O. -/
def unaccPossP : PlanarSyntacticObject := {T₀, {V₀, PossP}}

/-- (9c) with a specific possessive S_O. -/
def unaccDP : PlanarSyntacticObject := {T₀, {V₀, DP}}

/-- (9a) with a non-specific possessive O. -/
def transPossP : PlanarSyntacticObject := {T₀, {Agt, {v₀, {V₀, PossP}}}}

/-- (29) the raising applicative under T⁰. -/
def raisingAppl : PlanarSyntacticObject := {T₀, {Agt, {v₀, {Appl₀, {V₀, PossP}}}}}

/-- (9b) with a locative PP, for a specific or a non-specific S_A. -/
def unerg (subj : PlanarSyntacticObject) : PlanarSyntacticObject :=
  {T₀, {subj, {v₀, {V₀, PP}}}}

/-- (71) theme over locative, for a specific or a non-specific theme: path verbs, locative
existentials and locative copulas. -/
def themeLoc (theme : PlanarSyntacticObject) : PlanarSyntacticObject :=
  {T₀, {V₀, {theme, PP}}}

/-- (83) the experiencer PP merged above the theme. -/
def experiencer : PlanarSyntacticObject := {T₀, {PP, {V₀, ThemeD}}}

/-- (40a) an existential with a bare pivot. -/
def existential : PlanarSyntacticObject := {T₀, {V₀, Pivot}}

/-- The clause under C⁰. -/
def cp (tp : PlanarSyntacticObject) : PlanarSyntacticObject := {C₀, tp}

/-! ### Nominal opacity -/

theorem psr_invisible_dp : Invisible nominalOpacity (cp unaccDP) C₀ Psr := by decide +kernel

theorem psr_invisible_possP : Invisible nominalOpacity (cp unaccPossP) C₀ Psr := by
  decide +kernel

theorem psr_invisible_pp : Invisible nominalOpacity (cp (themeLoc ThemeN)) C₀ Psr := by
  decide +kernel

/-- Opacity is inherited up the extended projection of N⁰, so the D⁰ of a specific possessive is
behind the horizon with the rest of the DP, while the verb outside the nominal is not. -/
theorem dp_opaque_verb_visible : Invisible nominalOpacity (cp unaccDP) C₀ D₀ ∧
    ¬ Invisible nominalOpacity (cp unaccDP) C₀ V₀ := by
  decide +kernel

/-- C⁰'s wh-probe, satisfied by the wh-possessor. -/
def whProbe (t : PlanarSyntacticObject) : Probe t.val.Positions :=
  .relativized fun q ↦ decide (t.termAt q = ↑Psr)

/-- What C⁰'s wh-probe finds, searching short of its horizon at N⁰. -/
def whGoals (t : PlanarSyntacticObject) : Finset SyntacticObject :=
  t.goalsUnder (whProbe t) C₀ (nominalOpacity.cut headIndex? t)

/-- The possessor raised to Spec,TP out of a non-specific S_O. -/
def psrRaised : PlanarSyntacticObject := {Psr, unaccPossP}

theorem wh_needs_raising : (cp unaccPossP).goals (whProbe _) C₀ = {↑Psr} ∧
    whGoals (cp unaccPossP) = ∅ ∧ whGoals (cp psrRaised) = {↑Psr} := by
  decide +kernel

/-! ### Attract Closest -/

/-- The goals an [EPP:D] probe on the head `h` of `t` can attract: the D leaves at the positions
`h` c-commands that no other such leaf asymmetrically c-commands. -/
def dGoals (t : PlanarSyntacticObject) (h : SyntacticObject) : Finset SyntacticObject :=
  t.goals (t.leafProbe .D) h

theorem unacc_possP_psr_closest : dGoals unaccPossP T₀ = {↑Psr} := by decide +kernel

theorem unacc_dp_dHead_closest : dGoals unaccDP T₀ = {↑D₀} := by decide +kernel

theorem trans_agt_closest : dGoals transPossP T₀ = {↑Agt} := by decide +kernel

theorem appl_psr_closest : dGoals raisingAppl Appl₀ = {↑Psr} := by decide +kernel

theorem unerg_specific_blocks : dGoals (unerg SubjD) T₀ = {↑SubjD} := by decide +kernel

theorem unerg_nonspecific_psr_closest : dGoals (unerg SubjN) T₀ = {↑Psr} := by decide +kernel

theorem theme_specific_blocks : dGoals (themeLoc ThemeD) T₀ = {↑ThemeD} := by decide +kernel

theorem theme_nonspecific_psr_closest : dGoals (themeLoc ThemeN) T₀ = {↑Psr} := by
  decide +kernel

theorem experiencer_both_closest : dGoals experiencer T₀ = {↑Psr, ↑ThemeD} := by decide +kernel

/-! ### Judgment type -/

/-- Categorical judgments have a subject of predication, thetic ones present a situation. -/
inductive JudgmentType
  | categorical
  | thetic
  deriving DecidableEq, Repr

/-- A clause is categorical when T⁰'s [EPP:D] probe finds a goal to raise to Spec,TP, the
ψ-subject, and thetic when it finds none. -/
def judgment (t : PlanarSyntacticObject) (h : SyntacticObject) : JudgmentType :=
  if (dGoals t h).Nonempty then .categorical else .thetic

theorem existential_thetic : judgment existential T₀ = .thetic := by decide +kernel

theorem possession_categorical : judgment unaccPossP T₀ = .categorical := by decide +kernel

/-! ### The paper's examples -/

/-- Stranding succeeds exactly when the possessum is non-specific and no DP or occupied
external position stands between the possessor and its probe (Table 4). -/
theorem stranding_iff : ∀ row ∈ Examples.all, row.feature? "strategy" = some "stranding" →
      (row.judgment = .acceptable ↔
        row.feature? "possessum" = some "nonSpecific" ∧
          row.feature? "intervener" = some "none") := by decide

theorem piedPiping_specific : ∀ row ∈ Examples.all, row.feature? "strategy" = some "piedPiping" →
      row.judgment = .acceptable → row.feature? "possessum" = some "specific" := by decide

theorem psi_no_piedPiping : ∀ row ∈ Examples.all, row.feature? "strategy" = some "piedPiping" →
      (row.feature? "construction" = some "predicativePossession" ∨
        row.feature? "construction" = some "experientialCollocation") →
      row.judgment ≠ .acceptable := by decide

end AissenPolian2025
