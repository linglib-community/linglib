module

public import Linglib.Languages.Arabic.ModernStandard.Phonology
public import Linglib.Morphology.Root.Consonantal

/-!
# Arabic consonantal roots

This file defines some consonantal roots of Arabic as melodies over the consonants of
`Languages/Arabic/ModernStandard/Phonology.lean`, each named by its radicals in the
transcription of [mccarthy-1981].

## References

* [mccarthy-1981]
-/

@[expose] public section

open Morphology Phonology Arabic.ModernStandard.Phonology

namespace Arabic.ModernStandard

/-- The root ktb 'write'. -/
def ktb : ConsonantalRoot Segment := ⟨[k, t, b]⟩

/-- The root dḥrj 'roll'. -/
def «dḥrj» : ConsonantalRoot Segment := ⟨[d, ħ, r, «dʒ»]⟩

/-- The root smm 'poison', whose second and third radicals are identical. -/
def smm : ConsonantalRoot Segment := ⟨[s, m, m]⟩

/-- The root qlq, whose first and third radicals are identical. -/
def qlq : ConsonantalRoot Segment := ⟨[q, l, q]⟩

/-- The root mğnṭš of the loanword mağnaṭiiš 'magnet'. -/
def «mğnṭš» : ConsonantalRoot Segment := ⟨[m, «ʁ», n, «tˤ», «ʃ»]⟩

end Arabic.ModernStandard
