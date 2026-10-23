module

/-!
# Matić and Nikolaeva (2018): From Polarity Focus to Salient Polarity

This file formalizes the inventory behind the argument of [matic-nikolaeva-2018] that polarity
focus is not a linguistic category pairing a form class with a denotation. What the verum-focus
tradition after [hohle-1992] has tried to pin down denotationally is, in the chapter's terms,
salient polarity, an interpretive effect conveyed by a heterogeneous and open-ended list of
structures: in the chapter's German, English, and Serbian lists, prosodic accent on auxiliaries
and finite verbs, periphrases with *tun* and *do*, fronting and inversion constructions,
discourse particles, adverbs, and discourse markers (`Structure`, `Structure.device`). The
inventory realizes every one of the chapter's devices and is covered by none of them
(`every_device_attested`, `no_device_covers`), which is the observation the chapter sets
against any account that reads salient polarity off a single form class.

## Implementation notes

The inventory is the chapter's lists (2) to (4), taken as data; the chapter's positive
proposal, that salient polarity is an inference from unrelated denotations, is not a
denotation and is not formalized, and the lists are explicitly non-exhaustive, so the
theorems are about the attested inventory rather than about the category.

## References

* [matic-nikolaeva-2018]
* [hohle-1992]
-/

@[expose] public section

namespace MaticNikolaeva2018

/-- The kinds of device the chapter finds conveying salient polarity: prosody, verbal
periphrasis, a dedicated syntactic construction or word-order configuration, a discourse
particle, an adverb, or a discourse marker. -/
inductive Device where
  | prosody
  | periphrasis
  | wordOrder
  | particle
  | adverb
  | discourseMarker
  deriving DecidableEq

/-- The structures ascribed to salient polarity in the chapter's lists for German (2), English
(3), and Serbian (4). -/
inductive Structure where
  /-- German accent on an auxiliary, modal, or complementizer, *er HAT das Buch geschrieben*. -/
  | germanAccentOnAuxiliary
  /-- German accent on the lexical finite verb, *er SCHREIBT sein Buch*. -/
  | germanAccentOnLexicalVerb
  /-- German emphatic *tun* periphrasis, *Bücher lesen tut er*. -/
  | germanEmphaticTun
  /-- German full or partial verb-phrase fronting, *Bücher gelesen hat er*. -/
  | germanVPFronting
  /-- German accented discourse particles *doch*, *schon*, *wohl*, *ja*. -/
  | germanAccentedDiscourseParticles
  /-- German discourse markers *ich schwöre*, *ehrlich*, *ungelogen*. -/
  | germanDiscourseMarkers
  /-- German adverbs *tatsächlich*, *wahrhaftig*. -/
  | germanTruthAdverbs
  /-- English accent on an auxiliary or modal, *he WILL be on time*. -/
  | englishAccentedAuxiliary
  /-- English accent on the lexical finite verb, *he READ it yesterday*. -/
  | englishAccentedLexicalVerb
  /-- English emphatic *do*-support, *she did open the door*. -/
  | englishEmphaticDo
  /-- English verb-phrase fronting, *and learn he did*. -/
  | englishVPFronting
  /-- English adverbs *really*, *definitely*. -/
  | englishAdverbs
  /-- English particles *so*, *too*, *indeed*, *he did so finish the paper*. -/
  | englishParticles
  /-- English *so*-inversion, *and so do I*. -/
  | englishSoInversion
  /-- English expletive inversion, *but will he fuck convince me*. -/
  | englishFInversion
  /-- Serbian accent on the finite verb, *ona PIŠE romane*. -/
  | serbianAccentedFiniteVerb
  /-- Serbian accented full auxiliary in place of the clitic, *on JESTE napisao tu knjigu*. -/
  | serbianAccentedAuxiliary
  /-- Serbian accented verb with postposed subject, *NAPISAĆE on tu knjigu*. -/
  | serbianAccentedVerbPostposedSubject
  /-- Serbian particles and adverbs *stvarno*, *fakat*, *baš*. -/
  | serbianParticles
  /-- Serbian discourse markers *majke mi*, *ozbiljno*. -/
  | serbianDiscourseMarkers
  deriving DecidableEq

/-- The device by which each structure conveys salient polarity. -/
def Structure.device : Structure → Device
  | .germanAccentOnAuxiliary | .germanAccentOnLexicalVerb
  | .englishAccentedAuxiliary | .englishAccentedLexicalVerb
  | .serbianAccentedFiniteVerb | .serbianAccentedAuxiliary => .prosody
  | .germanEmphaticTun | .englishEmphaticDo => .periphrasis
  | .germanVPFronting | .englishVPFronting | .englishSoInversion | .englishFInversion
  | .serbianAccentedVerbPostposedSubject => .wordOrder
  | .germanAccentedDiscourseParticles | .englishParticles | .serbianParticles => .particle
  | .germanTruthAdverbs | .englishAdverbs => .adverb
  | .germanDiscourseMarkers | .serbianDiscourseMarkers => .discourseMarker

theorem every_device_attested (d : Device) : ∃ s : Structure, s.device = d := by
  cases d
  · exact ⟨.germanAccentOnAuxiliary, rfl⟩
  · exact ⟨.germanEmphaticTun, rfl⟩
  · exact ⟨.germanVPFronting, rfl⟩
  · exact ⟨.germanAccentedDiscourseParticles, rfl⟩
  · exact ⟨.germanTruthAdverbs, rfl⟩
  · exact ⟨.germanDiscourseMarkers, rfl⟩

theorem no_device_covers (d : Device) : ∃ s : Structure, s.device ≠ d := by
  cases d
  · exact ⟨.germanEmphaticTun, by decide⟩
  all_goals exact ⟨.germanAccentOnAuxiliary, by decide⟩

end MaticNikolaeva2018
