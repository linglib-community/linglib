module

public import Linglib.Fragments.Tarifit.Phonology
public import Linglib.Morphology.Root.Consonantal

/-!
# Tarifit consonantal roots

This file defines triconsonantal verb roots of Tarifit as melodies over the consonants of
`Fragments/Tarifit/Phonology.lean`, each named by its radicals and given with its simple
imperative, the CCəC form with a schwa between the second and third radicals, or with its
intensive imperative where only that is given. A gloss is given where Afkir and Zellou give one.

## References

* [afkir-zellou-2025]
-/

@[expose] public section

namespace Tarifit

open Morphology Phonology

/-- The root ðfʕ, whose simple imperative is /ðfəʕ/. -/
def «ðfʕ» : ConsonantalRoot Segment := ⟨[ð, f, «ʕ»]⟩

/-- The root ðqr, whose simple imperative /ðqər/ is 'weigh!'. -/
def ðqr : ConsonantalRoot Segment := ⟨[ð, q, r]⟩

/-- The root ʁdˤr, whose simple imperative is /ʁdˤər/. -/
def «ʁdˤr» : ConsonantalRoot Segment := ⟨[«ʁ», «dˤ», r]⟩

/-- The root ʁfr, whose simple imperative is /ʁfər/. -/
def «ʁfr» : ConsonantalRoot Segment := ⟨[«ʁ», f, r]⟩

/-- The root ʁrβ, whose simple imperative is /ʁrəβ/. -/
def «ʁrβ» : ConsonantalRoot Segment := ⟨[«ʁ», r, β]⟩

/-- The root ħmð, whose simple imperative /ħməð/ is 'thank!'. -/
def ħmð : ConsonantalRoot Segment := ⟨[ħ, m, ð]⟩

/-- The root nqr, whose simple imperative is /nqər/. -/
def nqr : ConsonantalRoot Segment := ⟨[n, q, r]⟩

/-- The root qβr, whose simple imperative is /qβər/. -/
def qβr : ConsonantalRoot Segment := ⟨[q, β, r]⟩

/-- The root qðf, whose simple imperative is /qðəf/. -/
def qðf : ConsonantalRoot Segment := ⟨[q, ð, f]⟩

/-- The root qfr, whose simple imperative is /qfər/. -/
def qfr : ConsonantalRoot Segment := ⟨[q, f, r]⟩

/-- The root qrβ, whose simple imperative is /qrəβ/. -/
def qrβ : ConsonantalRoot Segment := ⟨[q, r, β]⟩

/-- The root qrʕ, whose simple imperative /qrəʕ/ is 'rip!'. -/
def «qrʕ» : ConsonantalRoot Segment := ⟨[q, r, «ʕ»]⟩

/-- The root qtˤʕ, whose simple imperative is /qtˤəʕ/. -/
def «qtˤʕ» : ConsonantalRoot Segment := ⟨[q, «tˤ», «ʕ»]⟩

/-- The root rmð, whose simple imperative is /rməð/. -/
def rmð : ConsonantalRoot Segment := ⟨[r, m, ð]⟩

/-- The root srm, whose simple imperative is /srəm/. -/
def srm : ConsonantalRoot Segment := ⟨[s, r, m]⟩

/-- The root stˤr, whose simple imperative is /stˤər/. -/
def «stˤr» : ConsonantalRoot Segment := ⟨[s, «tˤ», r]⟩

/-- The root χrf, whose simple imperative is /χrəf/. -/
def χrf : ConsonantalRoot Segment := ⟨[χ, r, f]⟩

/-- The root ʒβð, whose simple imperative /ʒβəð/ is 'pull!'. -/
def «ʒβð» : ConsonantalRoot Segment := ⟨[«ʒ», β, ð]⟩

/-- The root ʒmð, whose simple imperative /ʒməð/ is 'freeze!'. -/
def «ʒmð» : ConsonantalRoot Segment := ⟨[«ʒ», m, ð]⟩

/-- The root ʕβð, whose simple imperative /ʕβəð/ is 'worship!'. -/
def «ʕβð» : ConsonantalRoot Segment := ⟨[«ʕ», β, ð]⟩

/-- The root ʕrm, whose simple imperative is /ʕrəm/. -/
def «ʕrm» : ConsonantalRoot Segment := ⟨[«ʕ», r, m]⟩

/-- The root ħsβ, whose simple imperative /ħsəβ/ is 'count!'. -/
def ħsβ : ConsonantalRoot Segment := ⟨[ħ, s, β]⟩

/-- The root ħzn, whose simple imperative is /ħzən/. -/
def ħzn : ConsonantalRoot Segment := ⟨[ħ, z, n]⟩

/-- The root ʃmθ, whose simple imperative is /ʃməθ/. -/
def «ʃmθ» : ConsonantalRoot Segment := ⟨[«ʃ», m, θ]⟩

/-- The root χzn, whose simple imperative is /χzən/. -/
def χzn : ConsonantalRoot Segment := ⟨[χ, z, n]⟩

/-- The root βkm, whose simple imperative is /βkəm/. -/
def βkm : ConsonantalRoot Segment := ⟨[β, k, m]⟩

/-- The root ħlm, whose simple imperative is /ħləm/. -/
def ħlm : ConsonantalRoot Segment := ⟨[ħ, l, m]⟩

/-- The root ħsn, whose simple imperative is /ħsən/. -/
def ħsn : ConsonantalRoot Segment := ⟨[ħ, s, n]⟩

/-- The root nqβ 'pick', whose simple imperative is /nqəβ/. -/
def nqβ : ConsonantalRoot Segment := ⟨[n, q, β]⟩

/-- The root qmʕ, whose simple imperative /qməʕ/ is 'suppress!'. -/
def «qmʕ» : ConsonantalRoot Segment := ⟨[q, m, «ʕ»]⟩

/-- The root sʃn, whose simple imperative /sʃən/ is 'show!'. -/
def «sʃn» : ConsonantalRoot Segment := ⟨[s, «ʃ», n]⟩

/-- The root χns 'bend down', whose simple imperative is /χnəs/. -/
def χns : ConsonantalRoot Segment := ⟨[χ, n, s]⟩

/-- The root ʒmʕ, whose simple imperative is /ʒməʕ/. -/
def «ʒmʕ» : ConsonantalRoot Segment := ⟨[«ʒ», m, «ʕ»]⟩

/-- The root sχf, whose simple imperative /sχəf/ is 'pass out!'. -/
def sχf : ConsonantalRoot Segment := ⟨[s, χ, f]⟩

/-- The root ħkm, whose simple imperative /ħkəm/ is 'judge!'. -/
def ħkm : ConsonantalRoot Segment := ⟨[ħ, k, m]⟩

/-- The root ntf, whose simple imperative /ntəf/ is 'pluck!'. -/
def ntf : ConsonantalRoot Segment := ⟨[n, t, f]⟩

/-- The root skf 'suck up', whose simple imperative is /skəf/. -/
def skf : ConsonantalRoot Segment := ⟨[s, k, f]⟩

/-- The root rsq, whose simple imperative is /rsəq/. -/
def rsq : ConsonantalRoot Segment := ⟨[r, s, q]⟩


/-- The root χðm 'work', whose simple imperative is /χðəm/. -/
def χðm : ConsonantalRoot Segment := ⟨[χ, ð, m]⟩

/-- The root fhm, whose intensive imperative /fəh:əm/ is 'understand!'. -/
def fhm : ConsonantalRoot Segment := ⟨[f, h, m]⟩

/-- The root rħm, whose intensive imperative /rəħ:əm/ is 'move back!'. -/
def rħm : ConsonantalRoot Segment := ⟨[r, ħ, m]⟩

end Tarifit
