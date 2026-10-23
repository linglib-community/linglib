module

public import Linglib.Syntax.Minimalist.Probe.Profile
public import Linglib.Syntax.Minimalist.Clause.Spine

/-!
# Keine (2020): Probes and Their Horizons

This file formalizes the horizons theory of [keine-2020] as it parameterizes probes across
languages. A probe's search terminates at its horizon category ((33)); labels are bilateral within
an extended projection, so a clause is opaque to a probe exactly when its label contains the
horizon, and Upward Entailment holds for every probe, transparency being antitone in the
extension order of clause sizes (`sizes_le`). Hindi's four clause
sizes ((168)) follow from the probes of (219), with NmlzP and CP incomparable, the one transparent
to wh-licensing and the other to Ā-movement (`hindi_table`, `nmlzP_cP_incomparable`), and the
A-Movement–Agreement Generalization ((231)) from the two probes on T⁰ sharing a horizon. English
((241)) and German ((367)), with ForceP above CP, follow the same way (`english_table`,
`german_table`), and the Itelmen ((269)) and Tsez ((271)) probes mismatch movement and
agreement in both directions (`mismatches`). Vacuity ((274)–(278)) yields the Height–Locality
Theorem ((279)), which the attested probes obey, and the default horizon ((307)) is the strictest
nonvacuous one (`hlt_location_to_horizon`, `default_horizon_strictest`). Variation is a horizon
parameter: the A-movement settings of (300) form an entailment chain (`a_movement_chain`), and
the Ban on Improper Movement (Section 6.2) with the smuggling and remnant-movement restrictions
(Section 3.4.3) is the opacity of a CP to the A-probes whose horizon it inherits
(`improper_movement`).

## Implementation notes

Labels are the bilateral labels of the substrate's `ClauseSpine`s, with the Hindi NmlzP, the
German ForceP and the Tsez TopP and ForceP defined here, and so are the probes of (219), (241),
(300) and (367); the Itelmen and Tsez probes are parameterized by their head, which (269) and
(271) leave open. Chapters 4 and 5, on CP and vP phases, are not formalized beyond the opacity
facts the tables record.

## References

* [keine-2020]
* [bobaljik-wurmbrand-2005]
* [polinsky-potsdam-2001]
-/

@[expose] public section

namespace Keine2020

open Minimalist

/-- A probe's row of a transparency table over clause sizes. -/
def row (sizes : List ClauseSpine) (p : Probe.Profile) : List Bool :=
  sizes.map fun s ↦ decide (p.TransparentTo s.label)

/-- The Hindi nominalized clause `[V, v, T, Nmlz]`, a clause type distinct from CP (Chapter 2). -/
def nmlzP : ClauseSpine := ⟨[.V, .v, .T, .Nmlz]⟩

/-- The German verb-second clause `[V, v, T, C, Force]`, projecting ForceP above CP
(Chapter 4). -/
def forceP : ClauseSpine := ⟨[.V, .v, .T, .C, .Force]⟩

/-! ### Upward Entailment -/

theorem sizes_le :
    ClauseSpine.vP ≤ .tP ∧ ClauseSpine.tP ≤ .cP ∧ ClauseSpine.tP ≤ nmlzP ∧
      ClauseSpine.cP ≤ forceP := by
  decide

/-- A language's probe settings for the four operations of the transparency tables. -/
structure LanguageProbeConfig where
  /-- The φ-agreement probe. -/
  phi : Probe.Profile
  /-- The A-movement probe. -/
  aMove : Probe.Profile
  /-- The wh-licensing probe. -/
  wh : Probe.Profile
  /-- The Ā-movement or topicalization probe. -/
  ābar : Probe.Profile
  deriving Repr

/-- The Hindi probes of (219) put A-movement and φ-agreement on T⁰ with horizon T, wh-licensing
on C⁰ with horizon C and Ā-movement on C⁰ with horizon Nmlz. -/
def LanguageProbeConfig.hindi : LanguageProbeConfig :=
  { phi := ⟨.T, some .T⟩, aMove := ⟨.T, some .T⟩, wh := ⟨.C, some .C⟩, ābar := ⟨.C, some .Nmlz⟩ }

/-- The English probes of (241), the A-probe on T⁰ with horizon C and the wh-probe on C⁰ without
horizon, Ā-movement being wh-movement. The book lists no separate φ-probe, taken here to share
the A-probe's settings. -/
def LanguageProbeConfig.english : LanguageProbeConfig :=
  { phi := ⟨.T, some .C⟩, aMove := ⟨.T, some .C⟩, wh := ⟨.C, none⟩, ābar := ⟨.C, none⟩ }

/-- The English extraposition probe of (241), on T⁰ with horizon T. -/
def englishExtr : Probe.Profile := ⟨.T, some .T⟩

/-- The Lubukusu A-probe of (300), without horizon, so that it hyperraises out of finite
clauses. -/
def lubukusuAProbe : Probe.Profile := ⟨.T, none⟩

/-- The default horizon of a probe on `X⁰` is `X` itself ((307)). -/
def defaultHorizon (probeHead : Cat) : Probe.Profile := ⟨probeHead, some probeHead⟩

/-! ### Hindi (Chapters 2 and 3) -/

/-- The four Hindi clause sizes of (168), the nominalized clause beside the finite one. -/
def hindiSizes : List ClauseSpine := [.vP, .tP, .cP, nmlzP]

/-- (168) from (219): A-movement and φ-agreement, on T⁰ with horizon T, enter only vP clauses;
wh-licensing, on C⁰ with horizon C, every clause but CP; Ā-movement, on C⁰ with horizon Nmlz,
every clause but NmlzP. -/
theorem hindi_table :
    row hindiSizes LanguageProbeConfig.hindi.aMove = [true, false, false, false] ∧
      row hindiSizes LanguageProbeConfig.hindi.phi = [true, false, false, false] ∧
      row hindiSizes LanguageProbeConfig.hindi.wh = [true, true, false, true] ∧
      row hindiSizes LanguageProbeConfig.hindi.ābar = [true, true, true, false] := by
  decide

theorem nmlzP_cP_incomparable :
    (¬ nmlzP ≤ ClauseSpine.cP ∧ ¬ ClauseSpine.cP ≤ nmlzP) ∧
      (LanguageProbeConfig.hindi.wh.TransparentTo nmlzP.label ∧
        ¬ LanguageProbeConfig.hindi.wh.TransparentTo ClauseSpine.cP.label) ∧
      (LanguageProbeConfig.hindi.ābar.TransparentTo ClauseSpine.cP.label ∧
        ¬ LanguageProbeConfig.hindi.ābar.TransparentTo nmlzP.label) ∧
      ([LanguageProbeConfig.hindi.phi, LanguageProbeConfig.hindi.wh,
        LanguageProbeConfig.hindi.ābar].map (row hindiSizes)).Nodup := by
  decide

/-- The A- and φ-probes coincide, so a clause that A-extraction has entered is transparent to
agreement, which is then obligatory, while the Ā-probe's horizon differs, and a finite clause
shows it (231). -/
theorem a_movement_agreement_generalization :
    LanguageProbeConfig.hindi.aMove = LanguageProbeConfig.hindi.phi ∧
      LanguageProbeConfig.hindi.ābar.TransparentTo ClauseSpine.cP.label ∧
      ¬ LanguageProbeConfig.hindi.phi.TransparentTo ClauseSpine.cP.label :=
  ⟨rfl, by decide, by decide⟩

/-! ### English and German (Section 3.4.2 and Chapter 4) -/

/-- The English clause sizes. -/
def englishSizes : List ClauseSpine := [.vP, .tP, .cP]

/-- (241): the A-probe, with horizon C, enters nonfinite clauses but not finite ones, the ban on
hyperraising (242); the wh-probe has no horizon; extraposition, with horizon T, leaves no clause
larger than vP. -/
theorem english_table :
    row englishSizes LanguageProbeConfig.english.aMove = [true, true, false] ∧
      row englishSizes LanguageProbeConfig.english.wh = [true, true, true] ∧
      row englishSizes englishExtr = [true, false, false] := by
  decide

/-- The German probes of (367) put scrambling on T⁰ with horizon T, relativization on C⁰ with
horizon C, wh-movement into a verb-final clause on C⁰ with horizon Force, and topicalization on
Force⁰ without a horizon. -/
def germanScr : Probe.Profile := ⟨.T, some .T⟩

def germanRel : Probe.Profile := ⟨.C, some .C⟩

def germanWh : Probe.Profile := ⟨.C, some .Force⟩

def germanTop : Probe.Profile := ⟨.Force, none⟩

/-- The German clause sizes, whose verb-second clauses project ForceP above CP. -/
def germanSizes : List ClauseSpine := [.vP, .tP, .cP, forceP]

/-- Chapter 4: the four German movements cut off at successive clause sizes. -/
theorem german_table :
    row germanSizes germanScr = [true, false, false, false] ∧
      row germanSizes germanRel = [true, true, false, false] ∧
      row germanSizes germanWh = [true, true, true, false] ∧
      row germanSizes germanTop = [true, true, true, true] := by
  decide

/-! ### Movement–agreement mismatches (Section 3.4.5) -/

/-- The Itelmen probes of (269), φ-agreement with horizon T and movement without a horizon. -/
def itelmenPhi (head : Cat) : Probe.Profile := ⟨head, some .T⟩

def itelmenMove (head : Cat) : Probe.Profile := ⟨head, none⟩

/-- The Tsez probes of (271), φ-agreement with horizon Force and movement with horizon Top. -/
def tsezPhi (head : Cat) : Probe.Profile := ⟨head, some .Force⟩

def tsezMove (head : Cat) : Probe.Profile := ⟨head, some .Top⟩

/-- The Tsez clause sizes above TP are TopP and ForceP, which requires TopP below it. -/
def tsezTopP : ClauseSpine := ⟨[.V, .v, .T, .Top]⟩

def tsezForceP : ClauseSpine := ⟨[.V, .v, .T, .Top, .Force]⟩

/-- (269), (271): movement and agreement mismatch in both directions. An Itelmen TP clause is
transparent to movement but opaque to agreement; a Tsez TopP clause is transparent to agreement
but opaque to movement, and a ForceP clause, inheriting Top, to neither. -/
theorem mismatches (head : Cat) :
    ((itelmenMove head).TransparentTo ClauseSpine.tP.label ∧
        ¬ (itelmenPhi head).TransparentTo ClauseSpine.tP.label) ∧
      ((tsezPhi head).TransparentTo tsezTopP.label ∧
        ¬ (tsezMove head).TransparentTo tsezTopP.label) ∧
      ¬ (tsezPhi head).TransparentTo tsezForceP.label ∧
        ¬ (tsezMove head).TransparentTo tsezForceP.label := by
  simp [itelmenMove, itelmenPhi, tsezPhi, tsezMove, tsezTopP, tsezForceP, ClauseSpine.tP]

/-! ### The Height–Locality Theorem (Section 3.5) -/

/-- (274)–(278): a probe on C⁰ whose horizon is a category of its sister TP terminates there and
is vacuous. -/
theorem vacuous_on_C :
    ∀ h ∈ ClauseSpine.tP, (⟨.C, some h⟩ : Probe.Profile).IsVacuous := by
  decide

/-- (279a), location to horizon: a probe on T⁰, C⁰ or Force⁰ with a horizon among the
projections below it is vacuous. -/
theorem hlt_location_to_horizon :
    (∀ h ∈ ClauseSpine.vP, (⟨.T, some h⟩ : Probe.Profile).IsVacuous) ∧
      (∀ h ∈ ClauseSpine.tP, (⟨.C, some h⟩ : Probe.Profile).IsVacuous) ∧
      ∀ h ∈ ClauseSpine.cP, (⟨.Force, some h⟩ : Probe.Profile).IsVacuous := by
  decide

/-- (279b), horizon to location: a probe with horizon T is vacuous above T⁰, and one with
horizon C above C⁰. -/
theorem hlt_horizon_to_location :
    (∀ head ∈ [Cat.C, .Force], (⟨head, some .T⟩ : Probe.Profile).IsVacuous) ∧
      (⟨.Force, some .C⟩ : Probe.Profile).IsVacuous := by
  decide

/-- The attested probes of (219), (241) and (367) are nonvacuous, as (279) requires. -/
theorem attested_nonvacuous :
    ∀ p ∈ [LanguageProbeConfig.hindi.aMove, LanguageProbeConfig.hindi.phi,
      LanguageProbeConfig.hindi.wh, LanguageProbeConfig.hindi.ābar,
      LanguageProbeConfig.english.aMove, LanguageProbeConfig.english.wh, englishExtr,
      germanScr, germanRel, germanWh, germanTop], ¬ p.IsVacuous := by
  decide

/-- (307): the default horizon of a probe on X⁰ is X, the strictest choice that is not vacuous;
the Hindi probes on T⁰, English extraposition and German scrambling take it. -/
theorem default_horizon_strictest :
    (∀ X ∈ [Cat.T, .C, .Force], ¬ (defaultHorizon X).IsVacuous) ∧
      LanguageProbeConfig.hindi.phi = defaultHorizon .T ∧
      englishExtr = defaultHorizon .T ∧
      germanScr = defaultHorizon .T :=
  ⟨by decide, rfl, rfl, rfl⟩

/-! ### Variation and improper movement (Sections 3.6, 3.4.3, 6.2) -/

/-- (300): the A-movement settings, Lubukusu without a horizon, English with C and Hindi with T,
form an entailment chain over the clauses of an extended projection, whose labels contain T
whenever they contain C. -/
theorem a_movement_chain (L : Finset Cat) (hL : Cat.C ∈ L → Cat.T ∈ L) :
    (LanguageProbeConfig.hindi.aMove.TransparentTo L →
        LanguageProbeConfig.english.aMove.TransparentTo L) ∧
      (LanguageProbeConfig.english.aMove.TransparentTo L → lubukusuAProbe.TransparentTo L) := by
  simpa [LanguageProbeConfig.hindi, LanguageProbeConfig.english, lubukusuAProbe] using mt hL

theorem improper_movement (h : Cat) (hh : h ∈ ClauseSpine.cP) :
    ¬ (⟨.T, some h⟩ : Probe.Profile).TransparentTo ClauseSpine.cP.label := by
  simpa using hh

/-- The three A-probes of (300) with a horizon are blocked by CP, and the Hindi and English
Ā-probes are not. -/
theorem improper_movement_attested :
    (∀ p ∈ [LanguageProbeConfig.hindi.aMove, LanguageProbeConfig.english.aMove, germanScr],
        ¬ p.TransparentTo ClauseSpine.cP.label) ∧
      ∀ p ∈ [LanguageProbeConfig.hindi.ābar, LanguageProbeConfig.english.wh],
        p.TransparentTo ClauseSpine.cP.label := by
  decide

end Keine2020
