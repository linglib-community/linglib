module

public import Linglib.Syntax.Minimalist.Agree.Basic
public import Linglib.Syntax.Minimalist.Probe.Profile
public import Linglib.Data.Examples.AissenPolian2025

/-!
# Possessor extraction and categorical subject in Tseltalan

Aissen and Polian argue that a Tseltalan possessor never Ā-subextracts: nominal opacity, a
Keine horizon at N⁰ for the wh-probe on C⁰, forces an extracted possessor to A-move first to
Spec,TP or Spec,ApplP, where Attract Closest over DPs decides whether it can — a specific
possessive's D layer, an agent, a specific subject or theme, or an occupied Spec,ApplP stops
it. Hence only non-specific possessums strand, and the possessor that reaches Spec,TP is the
ψ-subject of a categorical judgment.

Nominal opacity is the profile `nominalOpacity` read through `Invisible`, Attract Closest is
`dGoals`, the positional search for D leaves on the paper's structures, `judgment` reads the
judgment type off the same search, and the paper's examples are the rows, over which
`stranding_iff`, `piedPiping_specific` and `psi_no_piedPiping` hold.

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

open Minimalist SyntacticObject

/-! ### Probes -/

/-- Nominal opacity: the wh-probe on C⁰ has every node in the extended projection of N⁰ as its
horizon, `[wh]C⁰ ⊣‖ N`. -/
def nominalOpacity : Probe.Profile := ⟨.C, some .N⟩

/-- The [EPP:D] probe on T⁰, without horizon. -/
def dProbeT : Probe.Profile := ⟨.T, none⟩

/-- The [EPP:D] probe on Appl⁰, without horizon. -/
def dProbeAppl : Probe.Profile := ⟨.Appl, none⟩

/-- The [EPP:WH] probe on D⁰ that drives pied-piping with inversion, without horizon. -/
def secondaryWh : Probe.Profile := ⟨.D, none⟩

/-- `target` is invisible to a probe with profile `p` sitting at `probe` when it lies behind the
profile's horizon. -/
def Invisible (p : Probe.Profile) (root probe target : SyntacticObject) : Prop :=
  ∃ h ∈ p.horizon, behindHorizonIn root probe target h

theorem invisible_iff_behindHorizon (h : Cat) (root probe target : SyntacticObject)
    {p : Probe.Profile} (hp : p.horizon = some h) :
    Invisible p root probe target ↔ behindHorizonIn root probe target h := by
  simp [Invisible, hp]

/-- A probe without horizon sees everything in its domain. -/
theorem not_invisible_of_horizon_none (root probe target : SyntacticObject) {p : Probe.Profile}
    (hp : p.horizon = none) : ¬ Invisible p root probe target := by
  simp [Invisible, hp]

theorem dProbe_sees_through (root probe target : SyntacticObject) :
    ¬ Invisible dProbeT root probe target ∧ ¬ Invisible dProbeAppl root probe target ∧
      ¬ Invisible secondaryWh root probe target :=
  ⟨not_invisible_of_horizon_none _ _ _ rfl, not_invisible_of_horizon_none _ _ _ rfl,
   not_invisible_of_horizon_none _ _ _ rfl⟩

/-! ### The structures -/

def C₀ : PlanarSyntacticObject := .leaf ⟨.of .C [], 1⟩
def T₀ : PlanarSyntacticObject := .leaf ⟨.of .T [], 2⟩
def V₀ : PlanarSyntacticObject := .leaf ⟨.of .V [], 3⟩
def v₀ : PlanarSyntacticObject := .leaf ⟨.of .v [], 4⟩
def Appl₀ : PlanarSyntacticObject := .leaf ⟨.of .Appl [], 5⟩
def P₀ : PlanarSyntacticObject := .leaf ⟨.of .P [], 6⟩
def Psr : PlanarSyntacticObject := .leaf ⟨.of .D [], 7⟩
def Psm : PlanarSyntacticObject := .leaf ⟨.of .N [], 8⟩
def D₀ : PlanarSyntacticObject := .leaf ⟨.of .D [], 9⟩
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

/-- The possessor of a specific S_O is invisible to C⁰'s wh-probe. -/
theorem psr_invisible_dp : Invisible nominalOpacity (cp unaccDP) C₀ Psr := ⟨.N, rfl, by decide⟩

/-- So is the possessor of a non-specific S_O: opacity does not depend on size. -/
theorem psr_invisible_possP : Invisible nominalOpacity (cp unaccPossP) C₀ Psr :=
  ⟨.N, rfl, by decide⟩

/-- And the possessor inside a locative PP: PP islands follow from nominal opacity. -/
theorem psr_invisible_pp : Invisible nominalOpacity (cp (themeLoc ThemeN)) C₀ Psr :=
  ⟨.N, rfl, by decide⟩

/-- The D head of a specific possessive is visible, so the whole DP can be pied-piped. -/
theorem dHead_visible :
    ¬ Invisible nominalOpacity (cp unaccDP) C₀ D₀ :=
  fun ⟨_, hh, hb⟩ => by
    simp only [nominalOpacity, Option.mem_def, Option.some.injEq] at hh
    exact absurd (hh ▸ hb) (by decide)

/-! ### Attract Closest -/

/-- The [EPP:D] probe of T⁰ and Appl⁰ on the positions of `t`, satisfied by D leaves. -/
def dProbe (t : PlanarSyntacticObject) : Probe t.val.Positions :=
  .relativized fun q ↦ decide (isLeafOf .D (t.termAt q))

/-- The goals an [EPP:D] probe on the head `h` of `t` can attract: the D leaves at the positions
`h` c-commands that no other such leaf asymmetrically c-commands. -/
def dGoals (t : PlanarSyntacticObject) (h : SyntacticObject) : Finset SyntacticObject :=
  (Finset.univ.filter fun g ↦ ∃ a, t.termAt a = h ∧
    (dProbe t).Finds {q | t.val.CCommands a q} (t.above t.branching) g).image t.termAt

/-- The possessor of a non-specific S_O is T⁰'s closest D-goal: it raises to Spec,TP and can
strand the possessum. -/
theorem unacc_possP_psr_closest : dGoals unaccPossP T₀ = {↑Psr} := by decide +kernel

/-- In a specific S_O the D layer is the closer goal: the whole DP raises and the possessor is
shielded. -/
theorem unacc_dp_dHead_closest : dGoals unaccDP T₀ = {↑D₀} := by decide +kernel

/-- The agent of a transitive is the closer goal, so the possessor of O cannot reach Spec,TP. -/
theorem trans_agt_closest : dGoals transPossP T₀ = {↑Agt} := by decide +kernel

/-- In the raising applicative the possessor of O is Appl⁰'s closest D-goal: it externalizes to
Spec,ApplP. -/
theorem appl_psr_closest : dGoals raisingAppl Appl₀ = {↑Psr} := by decide +kernel

/-- A specific unergative subject stops T⁰ before the possessor inside the locative PP. -/
theorem unerg_specific_blocks : dGoals (unerg SubjD) T₀ = {↑SubjD} := by decide +kernel

/-- A non-specific unergative subject is no DP, so the possessor is the closest goal. -/
theorem unerg_nonspecific_psr_closest : dGoals (unerg SubjN) T₀ = {↑Psr} := by decide +kernel

/-- A specific theme c-commanding the locative PP raises instead of the possessor. -/
theorem theme_specific_blocks : dGoals (themeLoc ThemeD) T₀ = {↑ThemeD} := by decide +kernel

/-- A non-specific theme lets T⁰ reach the possessor inside the PP. -/
theorem theme_nonspecific_psr_closest : dGoals (themeLoc ThemeN) T₀ = {↑Psr} := by
  decide +kernel

/-- With the experiencer PP merged above the theme, neither c-commands the other and both are
closest goals; the experiential reading requires the experiencer to raise. -/
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

/-- An existential with a bare pivot contains no DP: the clause is thetic. -/
theorem existential_thetic : judgment existential T₀ = .thetic := by decide +kernel

/-- Predicative possession is categorical, with the possessor as ψ-subject. -/
theorem possession_categorical : judgment unaccPossP T₀ = .categorical := by decide +kernel

/-! ### The paper's examples -/

/-- Stranding succeeds exactly when the possessum is non-specific and no DP or occupied
external position stands between the possessor and its probe (Table 4). -/
theorem stranding_iff : ∀ row ∈ Examples.all, row.feature? "strategy" = some "stranding" →
      (row.judgment = .acceptable ↔
        row.feature? "possessum" = some "nonSpecific" ∧
          row.feature? "intervener" = some "none") := by decide

/-- Pied-piping succeeds only with a specific possessum, since only a DP can be wh-moved. -/
theorem piedPiping_specific : ∀ row ∈ Examples.all, row.feature? "strategy" = some "piedPiping" →
      row.judgment = .acceptable → row.feature? "possessum" = some "specific" := by decide

/-- In predicative possession and experiential collocations possessor and possessum form no
constituent, so pied-piping is out. -/
theorem psi_no_piedPiping : ∀ row ∈ Examples.all, row.feature? "strategy" = some "piedPiping" →
      (row.feature? "construction" = some "predicativePossession" ∨
        row.feature? "construction" = some "experientialCollocation") →
      row.judgment ≠ .acceptable := by decide

end AissenPolian2025
