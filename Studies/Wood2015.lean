module

public import Linglib.Morphology.DistributedMorphology.Locality
public import Linglib.Syntax.Case.Basic
public import Linglib.Syntax.Minimalist.Verbal.LittleV
public import Linglib.Syntax.Minimalist.Verbal.Voice
public import Linglib.Data.Examples.Wood2015

/-!
# Wood (2015): Icelandic Morphosyntax and Argument Structure

This file formalizes [wood-2015]'s account of the Icelandic clitic *-st*. It is not an exponent
of Voice: it originates in an argument position, a specifier that it fills while contributing
nothing to the semantics, and cliticizes to the verb. It may merge in a specifier that imposes
no case requirement, so in SpecVoiceP and SpecpP but not in SpecApplP, which demands dative,
nor in a direct object position (`Position.AdmitsSt`). A θ-role introduced by a head is
saturated by a DP in its specifier or passed up to the next argument-introducing head; with
*-st* in its specifier a head passes its role up, and since Voice is the highest such head, a
Voice with *-st* in its specifier must be expletive (`VoiceP.expletive_of_st`), and an agentive
vP like *murder* has no *-st* anticausative (`VoiceP.no_st_of_thematic`). An anticausative
arises in two ways, specifierless Voice or Voice with a D feature checked by *-st*
(`VoiceP.anticausative_iff`), the expletive non-active and expletive active cells of the
substrate's typology (`VoiceP.cell_of_anticausative`); with thematic Voice, *-st* can only sit
lower, in SpecpP, where p's figure role passes up to the DP in SpecVoiceP, the figure reflexive
(`st_specP_of_thematic`). The alternation therefore lives in Voice over a fixed verb, where
[cuervo-2003] puts it in v with no Voice in the inchoative (`alternation_in_voice`,
`alternation_in_v`).

The morphology follows from locality: *-ka* spells out v in the context of listed roots and
*-na* spells out specifierless Voice in the context of listed roots, which requires Voice to
be adjacent to the root at spell-out, so v must be zero (`na_only_if_v_zero`). Hence *-na* and
*-ka* never co-occur, *-na* never co-occurs with *-st*, whose Voice carries a D feature, and
*-ka* is compatible with both (`na_ka_exclusive`, `na_st_exclusive`, `voiceExponent_ka`).

## Implementation notes

The word is a `ComplexHead` over the heads v and Voice with v the only cyclic head, and the
allomorphy domain is the substrate's `SeesRoot`, adjacency across phonologically null heads.
The lists of roots for *-ka* and *-na* are parameters. Voice is a cell of `Minimalist.Voice`,
thematic when the vP is agentive, and its D feature is read from the cell. The reciprocal,
denominal, modal passive and *láta* constructions of the book's sixth chapter are recorded in
the examples.

## References

* [wood-2015]
* [cuervo-2003]
* [embick-2010]
* [schaefer-2008]
* [wood-marantz-2017]
-/

@[expose] public section

namespace Wood2015

open DistributedMorphology Minimalist

/-! ### Where *-st* merges -/

/-- The argument positions of the verb phrase. -/
inductive Position where
  | specVoice
  | specP
  | specAppl
  | directObject
  deriving DecidableEq, Repr

/-- The specifier positions of the argument-introducing heads. -/
def Position.IsSpecifier : Position → Prop
  | .specVoice | .specP | .specAppl => True
  | .directObject => False

/-- The case a position demands of what merges in it: Appl demands dative of its specifier, and
Voice and p demand no case of theirs (§5.3.2). -/
def Position.caseDemand : Position → Option Case
  | .specAppl => some .dat
  | _ => none

/-- *-st*, which bears no case, merges in a specifier position that demands no case (§5.3.2). -/
def Position.AdmitsSt (p : Position) : Prop := p.IsSpecifier ∧ p.caseDemand = none

instance : DecidablePred Position.IsSpecifier := fun p ↦ by
  cases p <;> unfold Position.IsSpecifier <;> infer_instance

instance : DecidablePred Position.AdmitsSt := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

theorem admitsSt_iff (p : Position) : p.AdmitsSt ↔ p = .specVoice ∨ p = .specP := by
  cases p <;> decide

/-! ### Voice and its specifier -/

/-- The specifier of Voice holds a DP, the clitic *-st*, or nothing, for the specifierless Voice. -/
inductive Occupant where
  | dp
  | st
  | none
  deriving DecidableEq, Repr

/-- A VoiceP has its head, a cell of the substrate's typology, thematic when the vP is agentive and
Voice introduces the agent role, and what occupies its specifier. -/
structure VoiceP where
  head : Voice.Head
  spec : Occupant
  deriving DecidableEq, Repr

namespace VoiceP

variable (V : VoiceP)

/-- The specifier is empty exactly when the head has no D feature: Voice{D} against
Voice{∅}. -/
def Coherent : Prop := V.spec = .none ↔ ¬ V.head.HasD

/-- A role introduced by the highest argument-introducing head must be saturated by a DP in
its specifier: the agent role of a thematic Voice has nowhere to be passed up to. -/
def Interpretable : Prop := V.head.IsThematic → V.spec = .dp

/-- Voice is expletive when it introduces no role. -/
def Expletive : Prop := ¬ V.head.IsThematic

/-- An anticausative projects no DP external argument. -/
def Anticausative : Prop := V.spec ≠ .dp

instance : Decidable V.Coherent := inferInstanceAs (Decidable (_ ↔ _))
instance : Decidable V.Interpretable := inferInstanceAs (Decidable (_ → _))
instance : Decidable V.Expletive := inferInstanceAs (Decidable (¬ _))
instance : Decidable V.Anticausative := inferInstanceAs (Decidable (_ ≠ _))

variable {V}

theorem expletive_of_st (h : V.Interpretable) (hs : V.spec = .st) : V.Expletive :=
  fun ht ↦ by simp [h ht] at hs

theorem expletive_of_none (h : V.Interpretable) (hs : V.spec = .none) : V.Expletive :=
  fun ht ↦ by simp [h ht] at hs

theorem no_st_of_thematic (h : V.Interpretable) (ht : V.head.IsThematic) : V.spec ≠ .st := by
  rw [h ht]; decide

theorem anticausative_iff : V.Anticausative ↔ V.spec = .none ∨ V.spec = .st := by
  cases hs : V.spec <;> simp [Anticausative, hs]

theorem expletive_of_anticausative (h : V.Interpretable) (ha : V.Anticausative) :
    V.Expletive :=
  fun ht ↦ ha (h ht)

theorem cell_of_anticausative (h : V.Interpretable) (hc : V.Coherent) :
    (V.spec = .st → V.head.params = Voice.anticausative.params) ∧
      (V.spec = .none → V.head.params = Voice.middle.params) := by
  revert h hc
  rcases V with ⟨⟨t, d⟩, s⟩
  cases s <;> cases t <;> cases d <;>
    simp [Interpretable, Coherent, Voice.Head.IsThematic, Voice.Head.HasD, Voice.Head.params,
      Voice.anticausative, Voice.middle]

end VoiceP

/-- A clause where *-st* merges: its VoiceP and the position *-st* occupies. -/
structure StClause where
  voice : VoiceP
  site : Position
  siteAdmits : site.AdmitsSt
  /-- *-st* is in SpecVoiceP exactly when it is Voice's specifier. -/
  site_voice : site = .specVoice ↔ voice.spec = .st

theorem st_specP_of_thematic (C : StClause) (h : C.voice.Interpretable)
    (ht : C.voice.head.IsThematic) : C.site = .specP := by
  rcases (admitsSt_iff C.site).mp C.siteAdmits with hv | hp
  · exact absurd (C.site_voice.mp hv) (VoiceP.no_st_of_thematic h ht)
  · exact hp

/-! ### Where the alternation lives, against [cuervo-2003]

For Wood the two alternants of *opna* share the verb, root and v, and differ in Voice alone,
thematic against expletive; for [cuervo-2003] they differ in v, `vDO` against `vGO` over the
same state, and the inchoative has no Voice to vary. The two accounts are incompatible on the
locus of the alternation, and the substrate lets each be stated. -/

theorem alternation_in_voice :
    Voice.agentive.IsThematic ∧ ¬ Voice.anticausative.IsThematic ∧
      Voice.agentive.HasD ∧ Voice.anticausative.HasD := by
  decide

theorem alternation_in_v :
    LittleV.Causative [.vDO, .vBE] ∧ LittleV.Inchoative [.vGO, .vBE] ∧
      [LittleV.vDO, .vBE].tail = [LittleV.vGO, .vBE].tail ∧
      LittleV.LicensesVoice [.vDO, .vBE] ∧ ¬ LittleV.LicensesVoice [.vGO, .vBE] := by
  decide

/-! ### The exponents of v and Voice -/

/-- Above the root the verb has v, with or without the *-ka* exponent, and Voice, with or without a
D feature. -/
inductive Head where
  | v (ka : Bool)
  | voice (hasD : Bool)
  deriving DecidableEq, Repr

/-- v is the categorizer, hence cyclic; Voice is not. -/
def Head.Cyclic : Head → Prop
  | .v _ => True
  | .voice _ => False

/-- A head is phonologically null when it has no overt exponent: v without *-ka*. Voice's
own exponent is what is being determined, so it counts as overt. -/
def Head.Null : Head → Prop
  | .v ka => ka = false
  | .voice _ => False

instance : DecidablePred Head.Cyclic := fun h ↦ by
  cases h <;> unfold Head.Cyclic <;> infer_instance

instance : DecidablePred Head.Null := fun h ↦ by cases h <;> unfold Head.Null <;> infer_instance

/-- The verb consists of a root, v, and Voice. -/
def verb (r : Root) (ka hasD : Bool) : ComplexHead Root Head := ⟨r, [.v ka, .voice hasD]⟩

/-- Voice's position in the verb. -/
def voiceIdx (r : Root) (ka hasD : Bool) : Fin (verb r ka hasD).heads.length :=
  ⟨1, by simp [verb]⟩

theorem rootLocal_voice (r : Root) (ka hasD : Bool) :
    (verb r ka hasD).RootLocal Head.Cyclic (voiceIdx r ka hasD) := by
  unfold ComplexHead.RootLocal ComplexHead.cycle
  have key : ∀ x : Fin (verb r ka hasD).heads.length,
      x ≤ voiceIdx r ka hasD ∧ Head.Cyclic (verb r ka hasD).heads[x] → (x : ℕ) = 0 := by
    rintro ⟨_ | _ | x, hx⟩ ⟨-, h₂⟩
    · rfl
    · simp [verb, Head.Cyclic] at h₂
    · simp [verb] at hx
  refine Finset.card_le_one.mpr fun a ha b hb ↦ Fin.ext ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  rw [key a ha, key b hb]

theorem seesRoot_voice_iff (r : Root) (ka hasD : Bool) :
    (verb r ka hasD).SeesRoot Head.Cyclic Head.Null (voiceIdx r ka hasD) ↔ ka = false := by
  constructor
  · exact fun h ↦ h.2 ⟨0, by simp [verb]⟩ (by simp [voiceIdx, Fin.lt_def])
  · rintro rfl
    refine ⟨rootLocal_voice r false hasD, fun k hk ↦ ?_⟩
    obtain ⟨_ | k, hk'⟩ := k
    · exact rfl
    · exact absurd (show k + 1 < 1 from hk) (by omega)

/-- v is spelled out *-ka* in the context of the listed roots. -/
def Ka (kaRoots : Set Root) (r : Root) : Prop := r ∈ kaRoots

/-- Specifierless Voice is spelled out *-na* in the context of the listed roots, which it must
see at spell-out; everywhere else Voice is the elsewhere zero. -/
def Na (naRoots : Set Root) (r : Root) (ka hasD : Bool) : Prop :=
  hasD = false ∧ r ∈ naRoots ∧
    (verb r ka hasD).SeesRoot Head.Cyclic Head.Null (voiceIdx r ka hasD)

instance (naRoots : Set Root) [DecidablePred (· ∈ naRoots)] (r : Root) (ka hasD : Bool) :
    Decidable (Na naRoots r ka hasD) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

variable {naRoots : Set Root}

theorem na_only_if_v_zero {r : Root} {ka hasD : Bool} (h : Na naRoots r ka hasD) :
    ka = false :=
  (seesRoot_voice_iff r ka hasD).mp h.2.2

theorem na_ka_exclusive {r : Root} {hasD : Bool} : ¬ Na naRoots r true hasD :=
  fun h ↦ Bool.noConfusion (na_only_if_v_zero h)

theorem na_st_exclusive {r : Root} {ka : Bool} : ¬ Na naRoots r ka true :=
  fun h ↦ Bool.noConfusion h.1

theorem na_of_listed {r : Root} (h : r ∈ naRoots) : Na naRoots r false false :=
  ⟨rfl, h, (seesRoot_voice_iff r false false).mpr rfl⟩

/-- The exponent of Voice. -/
inductive VoiceExponent where
  | na
  | zero
  deriving DecidableEq, Repr

variable (naRoots) [DecidablePred (· ∈ naRoots)]

/-- Voice is spelled out *-na* where the rule applies and by the elsewhere zero otherwise. -/
def voiceExponent (r : Root) (ka hasD : Bool) : VoiceExponent :=
  if Na naRoots r ka hasD then .na else .zero

theorem voiceExponent_ka (r : Root) (hasD : Bool) :
    voiceExponent naRoots r true hasD = .zero := by
  simp [voiceExponent, na_ka_exclusive]

theorem voiceExponent_st (r : Root) (ka : Bool) :
    voiceExponent naRoots r ka true = .zero := by
  simp [voiceExponent, na_st_exclusive]

end Wood2015
