module

public import Linglib.Syntax.Minimalist.Ellipsis
public import Linglib.Syntax.Minimalist.Verbal.Voice

/-!
# Merchant (2013): Voice and Ellipsis

This file formalizes Merchant's account of the uneven distribution of voice mismatches: an elided
VP may differ from its antecedent in voice under VP-ellipsis but not under sluicing, fragment
answers, gapping, stripping or pseudogapping. VP-ellipsis deletes vP, the complement of Voice, so
Voice is external to the ellipsis site and invisible to the identity condition, whereas the
clausal ellipses delete TP or more, which contains VoiceP. No argument-structure alternation,
causative, middle, dative or prepositional, survives any ellipsis, since the heads regulating them
sit at v or below and so inside every deletion domain. The paper's judgments are recorded as rows
and checked against `Ellipsis.Tolerates`, and Johnson's observation that only repetitive *again*
survives VP-ellipsis follows from the adjunction site of restitutive *again*.

## References

* [merchant-2013]
* [merchant-2004]
* [kratzer-1996]
-/

@[expose] public section

namespace Merchant2013

open Minimalist Minimalist.Voice
open Minimalist.Ellipsis

/-- Fragment answers move the remnant to Spec,CP and delete TP, the [E] position of sluicing
    ([merchant-2004]). -/
def fragmentAnswers : Ellipsis clausalSpine := ⟨.C⟩

/-- Gapping elides material containing VoiceP, with [E] at C or higher. -/
def gapping : Ellipsis clausalSpine := ⟨.C⟩

/-- Stripping, bare argument ellipsis, is a subcase of gapping. -/
def stripping : Ellipsis clausalSpine := ⟨.C⟩

/-- Pseudogapping extracts the remnant from vP and deletes a domain that includes VoiceP, with
    [E] at T or higher. -/
def pseudogapping : Ellipsis clausalSpine := ⟨.T⟩

/-- A voice mismatch datum across an ellipsis boundary. -/
structure VoiceMismatchDatum where
  description : String
  antecedentVoice : Head
  targetVoice : Head
  ellipsisType : Ellipsis clausalSpine
  grammatical : Bool
  language : String := "English"
  deriving Repr

-- § 2.1 VP-ellipsis: voice mismatches tolerated (§1.1, exx. 1–2)

/-- (1a) Active → passive under VPE.
    "The janitor must remove the trash whenever it is apparent
     that it should be ⟨removed⟩." -/
def ex1a : VoiceMismatchDatum :=
  { description := "Active → passive under VPE"
    antecedentVoice := agentive, targetVoice := passive
    ellipsisType := vpEllipsis, grammatical := true }

/-- (2a) Passive → active under VPE.
    "The system can be used by anyone who wants to ⟨use it⟩." -/
def ex2a : VoiceMismatchDatum :=
  { description := "Passive → active under VPE"
    antecedentVoice := passive, targetVoice := agentive
    ellipsisType := vpEllipsis, grammatical := true }

-- § 2.2 Sluicing: voice mismatches blocked (§1.2, exx. 5–7, 25)

/-- (5) "*Joe was murdered, but we don't know who." -/
def ex5 : VoiceMismatchDatum :=
  { description := "Sluicing: pass → act blocked"
    antecedentVoice := passive, targetVoice := agentive
    ellipsisType := sluicing, grammatical := false }

/-- (6a) German: "*Erika hat jemanden ermordet, aber sie wissen nicht, wer." -/
def ex6a : VoiceMismatchDatum :=
  { description := "German sluicing: act → pass blocked"
    antecedentVoice := agentive, targetVoice := passive
    ellipsisType := sluicing, grammatical := false, language := "German" }

/-- (25a) Greek: "*O Jannis skotose kapjon, ala δen kserume pjos." -/
def ex25a : VoiceMismatchDatum :=
  { description := "Greek sluicing: act → pass blocked (synthetic)"
    antecedentVoice := agentive, targetVoice := passive
    ellipsisType := sluicing, grammatical := false, language := "Greek" }

-- § 2.3 Fragment answers (§1.2, ex. 9)

/-- (9a) German: "Wer hat den Jungen untersucht? — *Von einer Psychologin." -/
def ex9a : VoiceMismatchDatum :=
  { description := "Fragment: act → pass blocked"
    antecedentVoice := agentive, targetVoice := passive
    ellipsisType := fragmentAnswers, grammatical := false, language := "German" }

-- § 2.4 Gapping (§1.2, ex. 10)

/-- (10a) "*Some bring roses and lilies by others." -/
def ex10a : VoiceMismatchDatum :=
  { description := "Gapping: act → pass blocked"
    antecedentVoice := agentive, targetVoice := passive
    ellipsisType := gapping, grammatical := false }

-- § 2.5 Stripping (§1.2, ex. 11)

/-- (11a) "*MAX brought the roses, not by AMY!" -/
def ex11a : VoiceMismatchDatum :=
  { description := "Stripping: act → pass blocked"
    antecedentVoice := agentive, targetVoice := passive
    ellipsisType := stripping, grammatical := false }

theorem vpe_voice_predicted :
    (ex1a.grammatical = true ↔ vpEllipsis.Tolerates .voice) ∧
    (ex2a.grammatical = true ↔ vpEllipsis.Tolerates .voice) := by decide

theorem sluicing_voice_predicted :
    (ex5.grammatical = true ↔ sluicing.Tolerates .voice) ∧
    (ex6a.grammatical = true ↔ sluicing.Tolerates .voice) ∧
    (ex25a.grammatical = true ↔ sluicing.Tolerates .voice) := by decide

theorem high_ellipsis_voice_predicted :
    (ex9a.grammatical = true ↔ fragmentAnswers.Tolerates .voice) ∧
    (ex10a.grammatical = true ↔ gapping.Tolerates .voice) ∧
    (ex11a.grammatical = true ↔ stripping.Tolerates .voice) := by decide

/-- A datum for argument structure alternation under ellipsis. -/
structure ArgStructureDatum where
  description : String
  alternationType : Mismatch
  ellipsisType : Ellipsis clausalSpine
  grammatical : Bool
  deriving Repr

-- § 4.1 Causative/inchoative (§3.3.1, exx. 30–31)

/-- (30a) "This can freeze. *Please do." -/
def ex30a : ArgStructureDatum :=
  { description := "Causative/inchoative blocked under VPE"
    alternationType := .transitivity
    ellipsisType := vpEllipsis, grammatical := false }

/-- (31a) Greek: "*Eklisan ena δromo, alla δen ksero pjos ⟨eklise⟩" -/
def ex31a : ArgStructureDatum :=
  { description := "Causative/inchoative blocked under sluicing"
    alternationType := .transitivity
    ellipsisType := sluicing, grammatical := false }

-- § 4.2 Middle (§3.3.1, exx. 35–36)

/-- (35a) "*They market ethanol well in the Midwest, but regular gas doesn't." -/
def ex35a : ArgStructureDatum :=
  { description := "Trans → middle blocked under VPE"
    alternationType := .middle
    ellipsisType := vpEllipsis, grammatical := false }

/-- (36a) "*Ethanol markets well in the Midwest, though they don't in the South." -/
def ex36a : ArgStructureDatum :=
  { description := "Middle → trans blocked under VPE"
    alternationType := .middle
    ellipsisType := vpEllipsis, grammatical := false }

-- § 4.3 Dative alternation (§3.3.2, exx. 37–39)

/-- (39a) "*They served₁ someone the meal, but I don't know to whom." -/
def ex39a : ArgStructureDatum :=
  { description := "Dative alternation blocked under sluicing"
    alternationType := .dative
    ellipsisType := sluicing, grammatical := false }

-- § 4.4 Prepositional alternation (§3.3.2, exx. 42–44)

/-- (43a) "*They embroidered something with peace signs, but I don't know
     what on ⟨they embroidered peace signs t⟩" -/
def ex43a : ArgStructureDatum :=
  { description := "Prep alternation blocked under sluicing"
    alternationType := .prepositional
    ellipsisType := sluicing, grammatical := false }

/-- (44) "*She embroiders peace signs on jackets more often than
     she does with swastikas." -/
def ex44 : ArgStructureDatum :=
  { description := "Prep alternation blocked under pseudogapping"
    alternationType := .prepositional
    ellipsisType := pseudogapping, grammatical := false }

theorem argStructure_data_predicted :
    (ex30a.grammatical = true ↔ ex30a.ellipsisType.Tolerates ex30a.alternationType) ∧
    (ex31a.grammatical = true ↔ ex31a.ellipsisType.Tolerates ex31a.alternationType) ∧
    (ex35a.grammatical = true ↔ ex35a.ellipsisType.Tolerates ex35a.alternationType) ∧
    (ex36a.grammatical = true ↔ ex36a.ellipsisType.Tolerates ex36a.alternationType) ∧
    (ex39a.grammatical = true ↔ ex39a.ellipsisType.Tolerates ex39a.alternationType) ∧
    (ex43a.grammatical = true ↔ ex43a.ellipsisType.Tolerates ex43a.alternationType) ∧
    (ex44.grammatical = true ↔ ex44.ellipsisType.Tolerates ex44.alternationType) := by
  decide

theorem v_alternations_blocked_high_ellipsis :
    ¬ sluicing.Tolerates .dative ∧
    ¬ sluicing.Tolerates .prepositional ∧
    ¬ sluicing.Tolerates .middle ∧
    ¬ vpEllipsis.Tolerates .dative ∧
    ¬ vpEllipsis.Tolerates .prepositional ∧
    ¬ vpEllipsis.Tolerates .middle ∧
    ¬ fragmentAnswers.Tolerates .dative ∧
    ¬ gapping.Tolerates .middle ∧
    ¬ pseudogapping.Tolerates .prepositional := by
  decide

theorem uneven_distribution :
    vpEllipsis.Tolerates .voice ∧
    ¬ sluicing.Tolerates .voice ∧
    ¬ fragmentAnswers.Tolerates .voice ∧
    ¬ gapping.Tolerates .voice ∧
    ¬ stripping.Tolerates .voice ∧
    ¬ pseudogapping.Tolerates .voice := by
  decide

theorem voice_uniquely_discriminates :
    -- voice DISCRIMINATES: VPE tolerates it, sluicing does not
    (vpEllipsis.Tolerates .voice ∧ ¬ sluicing.Tolerates .voice) ∧
    -- all other dimensions AGREE between VPE and sluicing
    (vpEllipsis.Tolerates .transitivity ↔
      sluicing.Tolerates .transitivity) ∧
    (vpEllipsis.Tolerates .dative ↔
      sluicing.Tolerates .dative) ∧
    (vpEllipsis.Tolerates .lexical ↔
      sluicing.Tolerates .lexical) := by
  decide

theorem no_inverse_language : sluicing.Tolerates .voice → vpEllipsis.Tolerates .voice :=
  fun h ↦ h.of_mem_below (by decide)

theorem voice_between_boundaries :
    Mismatch.voice.head = .Voice ∧
      ∀ m : Mismatch, m ≠ .voice → m.head ∈ clausalSpine.below .Voice :=
  ⟨rfl, fun m hm ↦ by cases m <;> first | exact absurd rfl hm | decide⟩

/-- Distinct active and passive Voice heads (Step 1) outside VPE's deletion domain (Step 2) make
both voice mismatches grammatical (Step 3; [kratzer-1996], [merchant-2013]). -/
theorem end_to_end_voice_chain :
    -- Step 1: Active and passive are distinct Voice flavors
    agentive ≠ passive ∧
    -- Step 2: Voice is external to VPE's deletion domain
    vpEllipsis.Tolerates .voice ∧
    -- Step 3: Empirical data matches
    ex1a.grammatical = true ∧
    ex2a.grammatical = true := by
  refine ⟨?_, by decide, rfl, rfl⟩
  intro h; cases h

/-- Under VPE only repetitive *again* survives, so VPE targets vP rather than VP (§4). -/
theorem again_confirms_vp_boundary :
    vpEllipsis.Spares AgainReading.repetitive.site ∧
      ¬ vpEllipsis.Spares AgainReading.restitutive.site := by decide

end Merchant2013
