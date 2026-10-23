module

public import Linglib.Syntax.Minimalist.Ellipsis
public import Linglib.Semantics.Root.Defs
public import Linglib.Syntax.Minimalist.Verbal.LittleV
public import Linglib.Syntax.Minimalist.Verbal.Voice

/-!
# Kalyakin (2026): VP ellipsis and argument structure alternations in Muira Dargwa

This file formalizes Kalyakin's argument that Muira Dargwa complex predicates show v-stranding
VP-ellipsis: the light verb survives while its complement, the VP containing the non-verbal root,
is elided. With [E] on v the deletion domain is smaller than that of English VP-ellipsis, so the
causative alternation, a difference in Voice over one root, is tolerated (§5) while the root must
still match, and both readings of *again* survive (§4.1), unlike English, where only the
repetitive one does. A root's position is read off its content, a state or a manner entailment in
Beavers and Koontz-Garboden's vocabulary: a root that imposes a manner on an activity attaches
to v rather than to the direct object and so lies outside the deletion domain, and antipassives
coerce a root into that position, which is why they resist ellipsis (§5). The NV-drop test shows
that the root and the argument go together, so the elided constituent is the VP (§3.6). The
paper's survey (§6) puts Persian and British *do* beside Muira Dargwa with [E] on v, and Bangla
with [E] on Voice, and finds that Persian, unlike Muira Dargwa, respects Goldberg's Verbal
Identity Requirement.

## References

* [kalyakin-2026]
* [merchant-2013]
* [toosarvandani-2009]
* [goldberg-2005]
* [kratzer-1996]
* [cuervo-2003]
* [anand-hardt-mccloskey-2021]
* [beavers-koontz-garboden-2020]
-/

@[expose] public section

namespace Kalyakin2026

open Minimalist Minimalist.Voice
open Minimalist.Ellipsis

/-! ### Mismatch predictions -/

/-- The site of a root on the clausal spine. A change-of-state root merges with the direct object, at V in
v's complement, and a manner root attaches to v, at the VP-adjunction site outside it (§2.2). -/
def rootSite : Semantics.Root.Position → ClauseSpine.Site
  | .complement => .head .V
  | .adjoined => .adjunct .V


theorem vVPE_mismatch_pattern :
    vStrandingVPE.Tolerates .voice ∧
    vStrandingVPE.Tolerates .transitivity ∧
    ¬ vStrandingVPE.Tolerates .lexical := by decide

theorem vpEllipsis_more_restrictive :
    ¬ vpEllipsis.Tolerates .transitivity ∧
    vStrandingVPE.Tolerates .transitivity := by decide

/-! ### The causative alternation under vVPE (§5)

The two alternants of a change-of-state root differ in the light verb alone, `[vDO, vBE]`
against `[vGO, vBE]` in [cuervo-2003]'s calculus, and share the VP below it. vVPE strands the
light verb and elides its complement, so the shared VP satisfies identity and the alternation is
tolerated; English VP-ellipsis deletes the vP, where v_trans ≠ v_unacc fails identity
([merchant-2013]). -/

/-- The causative alternant of a change-of-state root is a state under `vDO`. -/
def causative : List LittleV := [.vDO, .vBE]

/-- The inchoative alternant is the same state under `vGO`. -/
def inchoative : List LittleV := [.vGO, .vBE]

theorem alternants_share_vp :
    LittleV.Causative causative ∧ LittleV.Inchoative inchoative ∧
      causative.tail = inchoative.tail ∧ causative ≠ inchoative := by
  decide

theorem causative_alternation_ok_under_vVPE :
    vStrandingVPE.Tolerates .transitivity := by decide

theorem causative_alternation_blocked_english :
    ¬ vpEllipsis.Tolerates .transitivity := by decide

/-! ### Antipassive blocking -/

/-- Antipassive roots in Muira Dargwa are coerced to v-adjunction, outside vVPE's deletion domain,
    so they cannot be elided (§5). -/
theorem antipassive_blocks_vVPE : vStrandingVPE.Spares (rootSite .adjoined) := by decide

theorem change_of_state_allows_vVPE : vStrandingVPE.Deletes (rootSite .complement) := by decide

/-! ### Cross-linguistic predictions -/

theorem mismatch_hierarchy :
    -- Sluicing: blocks both voice and transitivity
    ¬ sluicing.Tolerates .voice ∧
    ¬ sluicing.Tolerates .transitivity ∧
    -- English VPE: allows voice, blocks transitivity
    vpEllipsis.Tolerates .voice ∧
    ¬ vpEllipsis.Tolerates .transitivity ∧
    -- vVPE: allows both voice and transitivity
    vStrandingVPE.Tolerates .voice ∧
    vStrandingVPE.Tolerates .transitivity := by
  decide

theorem vVPE_below_vpEllipsis :
    vStrandingVPE.ePosition ∈ clausalSpine.below vpEllipsis.ePosition := by decide

/-! ### The causative chain -/

theorem end_to_end_causative_chain :
    causative.tail = inchoative.tail ∧ causative ≠ inchoative ∧
      vStrandingVPE.Deletes (rootSite .complement) ∧ vStrandingVPE.Tolerates .transitivity := by
  decide

theorem sluicing_voice_blocked_convergent :
    ¬ sluicing.Tolerates .voice := by decide

/-! ### The *again* diagnostic -/

/-- Under vVPE both the repetitive and the restitutive *again* survive ((52a–b);
[toosarvandani-2009] (90)). -/
theorem vVPE_both_again :
    vStrandingVPE.Spares AgainReading.repetitive.site ∧
      vStrandingVPE.Spares AgainReading.restitutive.site := by decide

theorem vpEllipsis_only_repetitive :
    vpEllipsis.Spares AgainReading.repetitive.site ∧
      ¬ vpEllipsis.Spares AgainReading.restitutive.site := by decide

theorem again_distinguishes_vVPE_from_vpEllipsis :
    vStrandingVPE.Spares AgainReading.restitutive.site ∧
      ¬ vpEllipsis.Spares AgainReading.restitutive.site := by decide

/-! ### The position of a root by its content (§2.2, §4.1)

A non-verbal element is a bare root, and where it merges is fixed by its conceptual content: a
root describing the end state of a change-of-state event merges with the direct object, one
imposing a manner on an activity attaches to v. The roots of the paper's complex predicates carry
the state or manner entailment Kalyakin reads off them. -/

open Semantics

/-- *wana* of *wana AGR-arq'-* 'warm up' (3), (8), (75)–(80). -/
def wana : Root := { kinds := {.state} }

/-- *hark* of *hark AGR-arq'-* 'open', which denotes the result state of being open (52). -/
def hark : Root := { kinds := {.state} }

/-- *parʁat* of *parʁat AGR-arq'-* 'calm' (36), (69)–(71). -/
def parghat : Root := { kinds := {.state} }

/-- *dawk* of *dawk AGR-irq'-* 'repair' (84)–(86). -/
def dawk : Root := { kinds := {.state} }

/-- *taˤħ* of *taˤħ Ø-uq-* 'jump' (57). -/
def tah : Root := { kinds := {.manner} }

/-- *duc'* of *duc' Ø-uq-* 'run' (58). -/
def duc : Root := { kinds := {.manner} }

/-- *ʡimč* of *ʡimč w-ik'-* 'sneeze' (59). -/
def imc : Root := { kinds := {.manner} }

/-- The position of a root by its conceptual content. A root imposing a manner on an activity
attaches to v, one describing an end state merges with the direct object. -/
def position (r : Root) : Root.Position :=
  if .manner ∈ r.kinds then .adjoined else .complement

theorem deletes_rootSite_position_iff (r : Root) :
    vStrandingVPE.Deletes (rootSite (position r)) ↔ .manner ∉ r.kinds := by
  unfold position
  split_ifs with h
  · exact iff_of_false (by decide) (not_not.2 h)
  · exact iff_of_true (by decide) h

/-- The change-of-state roots are elided with the object, (36a) and (52). -/
theorem deletes_wana : vStrandingVPE.Deletes (rootSite (position wana)) :=
  (deletes_rootSite_position_iff _).2 (by decide)

/-- The manner roots are not, (57)–(59). -/
theorem not_deletes_tah : ¬ vStrandingVPE.Deletes (rootSite (position tah)) :=
  fun h ↦ (deletes_rootSite_position_iff _).1 h (by decide)

/-! ### The survey of verb-stranding ellipsis (§6) -/

/-- The languages with verb-stranding ellipsis the paper compares. -/
inductive Language
  | muiraDargwa
  | persian
  | bangla
  | britishEnglish
  deriving DecidableEq, Repr

/-- The ellipsis of each language. Muira Dargwa, Persian, where both readings of *again*
survive ((90), after Toosarvandani), and British *do*, which tolerates voice and
argument-structure mismatches alike ((97)–(98), after Silk), put [E] on v; Bangla puts it on
Voice, where the restitutive reading is lost (94) and adjuncts are recovered (95), the light
verb evacuating by head movement (after Haldar). -/
def Language.ellipsis : Language → Ellipsis clausalSpine
  | .bangla => vpEllipsis
  | _ => vStrandingVPE

/-- Whether the language respects Goldberg's Verbal Identity Requirement, identity of the light
verbs of antecedent and target ((92)), where the paper reports it. Persian prohibits every
light-verb mismatch (91) and Muira Dargwa tolerates them (§5). -/
def Language.respectsVIR? : Language → Option Bool
  | .persian => some true
  | .muiraDargwa => some false
  | _ => none

theorem ellipsis_eq_vStrandingVPE_iff (l : Language) :
    l.ellipsis = vStrandingVPE ↔ l ≠ .bangla := by
  cases l <;> decide

theorem persian_stricter_than_dargwa :
    Language.persian.ellipsis = Language.muiraDargwa.ellipsis ∧
      Language.persian.respectsVIR? = some true ∧
      Language.muiraDargwa.respectsVIR? = some false :=
  ⟨rfl, rfl, rfl⟩

theorem bangla_larger_domain :
    Language.muiraDargwa.ellipsis.ePosition ∈
        clausalSpine.below Language.bangla.ellipsis.ePosition ∧
      ¬ Language.bangla.ellipsis.Spares AgainReading.restitutive.site ∧
      Language.muiraDargwa.ellipsis.Spares AgainReading.restitutive.site := by
  decide

end Kalyakin2026
