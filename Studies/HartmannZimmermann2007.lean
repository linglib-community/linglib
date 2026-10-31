module

public import Linglib.Fragments.Hausa.Focus
public import Linglib.Fragments.Hausa.TAM
public import Linglib.Core.Logic.Function.FactorsThrough
public import Linglib.Semantics.Exhaustification.Excluder
public import Linglib.Semantics.Focus.Control
public import Linglib.Syntax.Reflex
public import Linglib.Data.Examples.HartmannZimmermann2007
public import Linglib.Data.Examples.Readers

/-!
# Hartmann and Zimmermann (2007): In place — out of place? Focus strategies in Hausa

Hartmann and Zimmermann's argument that Hausa is a counterexample to two universalist claims:
that focus is always marked, and that the position of a focus determines its pragmatic
interpretation. Focus is realized in situ or ex situ, and the paper's §3.2 matrix crosses the two
strategies with four pragmatic uses, new-information, corrective, contrastive and selective,
every cell of which is licensed (`hzMatrix`); `strategy_does_not_determine_pragType` refutes the
Meaning-Structure Mapping Hypothesis of (21), the label following Vallduví and Vilkuna, stated
as a failure of `Function.FactorsThrough` on the licensed utterances, so that the Hungarian and
Hausa verdicts differ on one predicate. In-situ new-information focus carries no morphosyntactic
reflex, and the §5 pilot finds no prosodic one either, so `hausa_falsifies_UniversalBFR` refutes
the Basic Focus Rule of Selkirk; focused subjects, by contrast, always front (§2.2.2).
Exhaustivity is not structural: the particle *kawài* 'only' exhaustifies over the resolved
contrast set in either position.

## Implementation notes

The §1.2 control taxonomy of uses and its factor-through theorems live in
`Semantics/Focus/Control.lean`, and each cell's pragmatic type is computed from its controlling
context rather than tagged. Subject foci in TAMs lacking a Relative form (future, habitual,
subjunctive) are syntactically and morphologically unmarked, which the paper analyses as
string-vacuous fronting, so the licensing predicate bans in-situ subjects unconditionally and the
future subject focus of (8) is licensed yet reflex-free. The paper counts the subjunctive with the
future and the habitual, but Newman excludes it from Rel environments, and the fragment's
licensing, which is his, rejects a fronted subjunctive (`not_licensed_exSitu_subjunctive`). Which
TAMs show Relative morphology is not stipulated: a licensed fronted focus changes the TAM exactly
when the TAM does not occur in Rel environments (`Hausa.FocusConfig.pacTAM_ne_iff`), the
completive and continuous of the paper's data. The §3.3 corpus tendencies stay in prose:
answers to *wh*-questions are mostly in situ (99 against 25) and selective, corrective and
contrastive foci mostly ex situ (154 against 12), but no use is categorically excluded from
either position, and only that categorical claim is a theorem. Locators follow the authors'
prepublication manuscript of the chapter.

## TODO

* The like-for-like contrast with Hungarian: *kawài* against the exhaustification over
  `Kiss1998.alternatives` that the identificational position performs.
* §2.3 multiple foci: one ex-situ focus with in-situ foci (18a–c).
* §4 focus pied-piping and partial focus movement, and the final Ex-Situ Generalisation of their
  (47), which need a structured-meaning overlap predicate.
* §5 prosodic pilot data and §6.1 emphasis motivation are quantitative tendencies, in prose only.

## References

* [hartmann-zimmermann-2007]
* [newman-2000]
* [uhmann-1991]
* [selkirk-1995]
* [vallduvi-vilkuna-1998]
-/

@[expose] public section

namespace HartmannZimmermann2007

open Hausa
open Exhaustification Focus

/-! ## What is focused (§2.2.2) -/

/-- Hausa singles out subjects as what is focused (§2.2.2); everything else collapses to
`nonSubject`. -/
inductive Focused where
  | subject
  | nonSubject
  deriving DecidableEq, Repr, Inhabited

/-! ## Tagged focus utterances and Hausa licensing -/

/-- A `FocusConfig` tagged with its pragmatic use and focused
constituent. -/
structure FocusUtterance where
  cfg      : FocusConfig
  pragType : Use
  focused  : Focused
  deriving Repr

/-- An utterance is Hausa-licensed when it is morphosyntactically licensed
(`FocusConfig.Licensed`) and respects the §2.2.2 ban on in-situ subject focus. The ban is
unconditional, since in TAMs without a Relative form the fronting is merely invisible (p. 4),
not absent. -/
def FocusUtterance.IsHausaLicensed (u : FocusUtterance) : Prop :=
  u.cfg.Licensed ∧ (u.focused = .subject → u.cfg.strategy = .exSitu)

instance (u : FocusUtterance) : Decidable u.IsHausaLicensed :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## Controlling contexts of the §3.2 matrix

Every cell's mini-scenario has one shape: a two-point answer domain, the mentioned answer `ans`
against the contextual alternative `alt`, whose content (fish against other dishes, fifteen
against twenty Naira, behind against in front, …) lives in the cell's data row. The answer is the
singleton complete-answer predicate mapped over the F-marked `ans`, and each use's context, the
four of §1.2, resolves the squiggle on it (`ctx_resolves`). Ex-situ variants are interpreted at
the base structure (fronting is A'-movement for the paper, and alternatives do not distribute
through abstraction, so `WithAlternatives` has no `Distributive` instance). -/

/-- The two-point answer domain of a cell's mini-scenario. -/
inductive Alt | ans | alt

/-- The context controlling each use over the two-point scenario: the question or the offer of
both answers, the assertion of the alternative to be corrected, or a phrase contrasting with it.
-/
def ctx : Use → Antecedent (Set Alt)
  | .newInfo => .question {{.ans}, {.alt}}
  | .corrective => .assertion {.alt}
  | .selective => .offer {{.ans}, {.alt}}
  | .contrastive => .phrase {.alt}

/-- The focused answer of the two-point scenario. -/
def answer : WithAlternatives (Set Alt) :=
  (fun x ↦ ({x} : Set Alt)) <$> WithAlternatives.focused Alt.ans

theorem ctx_resolves (u : Use) : (ctx u).Resolves answer.ordinary answer.alternatives := by
  have hmem (x : Alt) : ({x} : Set Alt) ∈ answer.alternatives :=
    WithAlternatives.mem_alternatives_map.2 ⟨x, Set.mem_univ x, rfl⟩
  have hne : ({Alt.alt} : Set Alt) ≠ {Alt.ans} := by simp
  cases u with
  | newInfo | selective =>
    exact ⟨Set.pair_subset (hmem _) (hmem _), Or.inl rfl, {Alt.alt}, Or.inr rfl, hne⟩
  | corrective | contrastive => exact ⟨hmem _, hne⟩

/-! ## Exhaustive focus (§3.2, (32))

Exhaustivity is not structurally encoded: it is induced by focus
particles (*kawài* 'only'; *nee/cee* per the paper's fn. 3) over the
resolved contrast set, in either strategy — (32a/b) attest in-situ and
ex-situ *only BOOKS* alike. -/

/-- The exhaustified answer is the exclusion asserted by *only* over the scenario's resolved
contrast set. -/
def exhAnswer (u : Use) : Set Alt :=
  excludes (ctx u).contrastSet answer.ordinary

-- §3.2
theorem exhAnswer_eq (u : Use) : exhAnswer u = {Alt.ans} := by
  ext w
  cases u <;> cases w <;> simp [exhAnswer, excludes, ctx, answer]

/-! ## The 8-cell empirical matrix (§3.2)

Each cell's pragmatic type is *computed* from its controlling context:
the constructors take a `Focus.Antecedent`, not a tag. -/

def mkExSituUtt (tam pacTAM : TAM) (cell : Agreement.Bundle) (g : Hausa.Gender.Value)
    (hasStab : Bool) {W : Type*} (ctl : Antecedent W) (foc : Focused := .nonSubject) :
    FocusUtterance :=
  ⟨mkExSitu tam pacTAM cell (some g) hasStab, ctl.use, foc⟩

def mkInSituUtt (tam : TAM) (cell : Agreement.Bundle) (g : Hausa.Gender.Value)
    {W : Type*} (ctl : Antecedent W) (foc : Focused := .nonSubject)
    (hasStab : Bool := false) : FocusUtterance :=
  ⟨mkInSitu tam cell (some g) hasStab, ctl.use, foc⟩

/-- The first person singular PAC cell. -/
def s1 : Agreement.Bundle := .personNumber .first .singular

/-- The third person masculine singular PAC cell. -/
def s3m : Agreement.Bundle :=
  (Agreement.Bundle.personNumber .third .singular).set .gender .Masc

/-- The third person feminine singular PAC cell. -/
def s3f : Agreement.Bundle := (Agreement.Bundle.personNumber .third .singular).set .gender .Fem

/-- The impersonal PAC cell. -/
def p4 : Agreement.Bundle := impersonal

/-- Ex-situ new-information focus ((22), `Examples.ex22`). -/
def exSitu_newInfo : FocusUtterance :=
  mkExSituUtt .continuous .relContinuous1 s3f .masculine true (ctx .newInfo)

/-- Ex-situ corrective focus on a feminine subject ((24),
`Examples.ex24`). -/
def exSitu_corrective : FocusUtterance :=
  mkExSituUtt .completive .preterite s3f .feminine true (ctx .corrective) .subject

/-- Ex-situ selective focus, no stabilizer ((29), `Examples.ex29`). -/
def exSitu_selective : FocusUtterance :=
  mkExSituUtt .continuous .relContinuous1 s1 .masculine false (ctx .selective)

/-- Ex-situ contrastive focus, no stabilizer, with the impersonal *akèe* ((27),
`Examples.ex27`). -/
def exSitu_contrastive : FocusUtterance :=
  mkExSituUtt .continuous .relContinuous1 p4 .masculine false (ctx .contrastive)

/-- In-situ new-information focus ((23), `Examples.ex23`). -/
def inSitu_newInfo : FocusUtterance := mkInSituUtt .completive s1 .masculine (ctx .newInfo)

/-- In-situ corrective focus with sentence-final *nèe* ((25),
`Examples.ex25`). -/
def inSitu_corrective : FocusUtterance :=
  mkInSituUtt .future s1 .masculine (ctx .corrective) (hasStab := true)

/-- In-situ selective focus ((30), `Examples.ex30`). -/
def inSitu_selective : FocusUtterance := mkInSituUtt .future s1 .masculine (ctx .selective)

/-- In-situ contrastive focus ((26), `Examples.ex26`). -/
def inSitu_contrastive : FocusUtterance := mkInSituUtt .future s1 .masculine (ctx .contrastive)

/-- The 8-cell matrix of §3.2 crosses both strategies with all four pragmatic types. -/
def hzMatrix : List FocusUtterance :=
  [exSitu_newInfo, exSitu_corrective, exSitu_selective, exSitu_contrastive,
   inSitu_newInfo, inSitu_corrective, inSitu_selective, inSitu_contrastive]

-- §3.2
theorem all_hzMatrix_IsHausaLicensed :
    ∀ u ∈ hzMatrix, u.IsHausaLicensed := by decide

/-! ## Strategy does not determine pragmatic type (§3.2) -/

/-- On Hausa-licensed utterances `pragType` does not factor through strategy, since (22) and
(24) are both ex-situ with distinct pragmatic types. -/
theorem strategy_does_not_determine_pragType :
    ¬ Function.FactorsThrough
        (fun u : {u : FocusUtterance // u.IsHausaLicensed} ↦ u.1.pragType)
        (fun u ↦ u.1.cfg.strategy) :=
  fun h ↦ absurd (@h ⟨exSitu_newInfo, by decide⟩ ⟨exSitu_corrective, by decide⟩ rfl) (by decide)

-- (23), (25)
theorem strategy_underdetermines_pragType_inSitu :
    ¬ Function.FactorsThrough
        (fun u : {u : FocusUtterance // u.IsHausaLicensed ∧ u.cfg.strategy = .inSitu} ↦
          u.1.pragType)
        (fun u ↦ u.1.cfg.strategy) :=
  fun h ↦ absurd (@h ⟨inSitu_newInfo, by decide⟩ ⟨inSitu_corrective, by decide⟩ rfl) (by decide)

/-! ## Subject-focus generalization (§2.2.2) -/

-- §2.2.2
theorem subject_focus_only_exSitu (u : FocusUtterance)
    (h : u.IsHausaLicensed) (hSubj : u.focused = .subject) :
    u.cfg.strategy = .exSitu := h.2 hSubj

/-- The starred in-situ subject focus ((17 A2), `Examples.ex17a2`). -/
def starred_inSitu_subject : FocusUtterance :=
  mkInSituUtt .continuous s3m .masculine (ctx .newInfo) .subject

theorem starred_inSitu_subject_not_IsHausaLicensed :
    ¬ starred_inSitu_subject.IsHausaLicensed := by decide

/-- The grammatical ex-situ subject focus ((17 A1), `Examples.ex17a1`). -/
def licensed_exSitu_subject : FocusUtterance :=
  mkExSituUtt .continuous .relContinuous1 s3m .masculine true (ctx .newInfo) .subject

theorem licensed_exSitu_subject_IsHausaLicensed :
    licensed_exSitu_subject.IsHausaLicensed := by decide

/-- Subject focus in the future, which occurs in Rel environments unchanged ((8),
`Examples.ex8`), is string-vacuous fronting with no overt reflex
(`exSitu_subject_future_no_reflex`). -/
def exSitu_subject_future : FocusUtterance :=
  mkExSituUtt .future .future s3m .masculine false (ctx .newInfo) .subject

theorem exSitu_subject_future_IsHausaLicensed :
    exSitu_subject_future.IsHausaLicensed := by decide

theorem not_licensed_exSitu_subjunctive (t : TAM) (c : Agreement.Bundle)
    (g : Option Hausa.Gender.Value) (hs : Bool) : ¬ (mkExSitu .subjunctive t c g hs).Licensed :=
  fun h ↦ by simpa [mkExSitu, TAM.relCounterparts] using h.2 rfl

/-! ## Universalist Basic Focus Rule (§5, §6.2) -/

/-- The overt reflexes of a focus utterance in the shared `Reflex` vocabulary are non-vacuous
fronting (subjects front string-vacuously), the Rel form of the PAC where fronting changes the TAM,
and the stabilizer. -/
def FocusUtterance.reflexes (u : FocusUtterance) : Finset (Reflex Focused) :=
  (if u.focused = .nonSubject ∧ u.cfg.strategy = .exSitu then {.displacement u.focused}
    else ∅) ∪
  (if u.cfg.pacTAM ≠ u.cfg.tam then {.morpheme u.focused (u.cfg.pac.toList.map .free)}
    else ∅) ∪
  (if u.cfg.hasStab then
    {.morpheme u.focused [.free (stabilizer u.cfg.focusGender).form]}
  else ∅)

/-- A focus utterance has a morphosyntactic reflex when some reflex lies outside the phonological
channel. -/
def FocusUtterance.HasMorphosyntacticReflex (u : FocusUtterance) : Prop :=
  ∃ ρ ∈ u.reflexes, ρ.modality.channel ≠ .phonological

instance (u : FocusUtterance) : Decidable u.HasMorphosyntacticReflex :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The universalist claim — [selkirk-1995]'s Basic Focus Rule and its
tradition (§5, §6.2) — that every focused utterance carries some
structural reflex, weakened to morphosyntax and quantified over Hausa
utterances only. -/
def UniversalBFR : Prop :=
  ∀ u : FocusUtterance, u.IsHausaLicensed → u.HasMorphosyntacticReflex

/-- (23) is licensed and reflex-free; the §5 pilot finds no prosodic
reflex either. -/
theorem hausa_falsifies_UniversalBFR : ¬ UniversalBFR :=
  fun h ↦ absurd (h inSitu_newInfo (by decide)) (by decide)

-- (8)
theorem exSitu_subject_future_no_reflex :
    ¬ exSitu_subject_future.HasMorphosyntacticReflex := by decide

theorem hasMorphosyntacticReflex_iff (u : FocusUtterance) :
    u.HasMorphosyntacticReflex ↔ u.reflexes.Nonempty := by
  refine ⟨fun ⟨ρ, hρ, _⟩ ↦ ⟨ρ, hρ⟩, fun ⟨ρ, hρ⟩ ↦ ⟨ρ, hρ, ?_⟩⟩
  simp only [FocusUtterance.reflexes, Finset.mem_union] at hρ
  split_ifs at hρ <;> simp only [Finset.mem_singleton, Finset.notMem_empty, or_false, false_or,
    or_assoc, or_self] at hρ <;> rcases hρ with rfl | rfl | rfl <;> nofun

theorem hausa_refutes_perceptibility :
    ¬ Reflex.Perceptible fun u : {u : FocusUtterance // u.IsHausaLicensed} ↦ u.1.reflexes :=
  fun h ↦ absurd
    ((hasMorphosyntacticReflex_iff inSitu_newInfo).mpr (h ⟨inSitu_newInfo, by decide⟩))
    (by decide)

/-! ## Polar tone of *nē/cē* (§2.1) -/

/-- The rows' tone labels. -/
def toneTable : List (String × Tone.TRN) := [("H", .H), ("L", .L)]

-- (3a), (3b)
theorem stab_tone_polar :
    ∀ e ∈ [Examples.ex3a, Examples.ex3b],
      e.parse? "stab_tone" toneTable = (e.parse? "host_tone" toneTable).map polarOf := by
  decide

/-! ## Data linkage

Each cell's tags are pinned to the `paperFeatures` of its
`Data.Examples.HartmannZimmermann2007` row. -/

def strategyLabel : Strategy → String
  | .inSitu => "inSitu"
  | .exSitu => "exSitu"

def pragLabel : Use → String
  | .newInfo => "newInfo"
  | .corrective => "corrective"
  | .selective => "selective"
  | .contrastive => "contrastive"

def focusedLabel : Focused → String
  | .subject => "subject"
  | .nonSubject => "nonSubject"

def stabLabel (c : FocusConfig) : String :=
  match c.stab? with
  | some p => if p = ce then "cee" else "nee"
  | none => "none"

def cellRows :
    List (FocusUtterance × Datum) :=
  [(exSitu_newInfo, Examples.ex22), (exSitu_corrective, Examples.ex24),
   (exSitu_selective, Examples.ex29), (exSitu_contrastive, Examples.ex27),
   (inSitu_newInfo, Examples.ex23), (inSitu_corrective, Examples.ex25),
   (inSitu_selective, Examples.ex30), (inSitu_contrastive, Examples.ex26),
   (starred_inSitu_subject, Examples.ex17a2),
   (licensed_exSitu_subject, Examples.ex17a1)]

theorem cells_match_rows :
    ∀ p ∈ cellRows,
      p.2.feature? "strategy" = some (strategyLabel p.1.cfg.strategy) ∧
      p.2.feature? "pragType" = some (pragLabel p.1.pragType) ∧
      p.2.feature? "focused" = some (focusedLabel p.1.focused) ∧
      p.2.feature? "stabilizer" = some (stabLabel p.1.cfg) := by decide

-- (8)
theorem ex8_matches_row :
    Examples.ex8.feature? "strategy" = some (strategyLabel exSitu_subject_future.cfg.strategy) ∧
      Examples.ex8.feature? "focused" = some (focusedLabel exSitu_subject_future.focused) ∧
      Examples.ex8.feature? "stabilizer" = some (stabLabel exSitu_subject_future.cfg) := by
  decide

def tamLabel : TAM → String
  | .completive => "completive"
  | .preterite => "preterite"
  | .continuous => "continuous"
  | .relContinuous1 => "relContinuous1"
  | .relContinuous2 => "relContinuous2"
  | .future => "future"
  | .allative => "allative"
  | .potential => "potential"
  | .rhetorical => "rhetorical"
  | .habitual => "habitual"
  | .subjunctive => "subjunctive"

theorem tam_matches_rows :
    ∀ p ∈ [(exSitu_subject_future, Examples.ex8), (licensed_exSitu_subject, Examples.ex17a1),
      (starred_inSitu_subject, Examples.ex17a2)],
      p.2.feature? "tam" = some (tamLabel p.1.cfg.tam) := by
  decide

theorem starred_row_is_the_unlicensed_cell :
    Examples.ex17a2.judgment = .ungrammatical ∧
    ¬ starred_inSitu_subject.IsHausaLicensed := ⟨rfl, by decide⟩

end HartmannZimmermann2007
