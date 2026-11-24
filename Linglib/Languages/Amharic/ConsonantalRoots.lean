module

public import Linglib.Morphology.Root.Consonantal
public import Linglib.Languages.Amharic.Phonology

/-!
# Amharic consonantal roots

The roots of the type A verbal paradigms of [leslau-1995]'s reference grammar that
[faust-2026] discusses ((5), (12)): a regular triradical, a root whose stems have identical
final consonants, a root whose second stem consonant is palatalized, and the [a]-final and
hollow roots traditionally analysed with a nonconsonantal radical, as roots of segments. The
root identities follow [faust-2026]; [broselow-1984] analyses `wd` as √wdd and `fdj` as
biradical.

## References

* [faust-2026]
* [broselow-1984]
* [leslau-1995]
-/

@[expose] public section

open Morphology Phonology Amharic.Phonology

namespace Amharic

/-- √sbr 'break' gives [säbbär-ä] PFV.3MSG, [säbr-o] GRND and [mäsbär] INF ((5a), (12a)). -/
def sbr : ConsonantalRoot Segment := ⟨[s, b, «ɾ»]⟩

/-- √wd 'like' gives [wäddäd-ä] PFV.3MSG, [wädd-o] GRND and [mäwdäd] INF (5b). -/
def wd : ConsonantalRoot Segment := ⟨[w, d]⟩

/-- √fdj 'scorch' gives [fäʤʤ-ä] PFV.3MSG, [fäʤt-o] GRND and [mäfʤät] INF ((5c), (12b)). -/
def fdj : ConsonantalRoot Segment := ⟨[f, d, j]⟩

/-- √sma 'hear' gives [sämm-a] PFV.3MSG, [sämt-o] GRND and [mäsmat] INF (12c). -/
def sma : ConsonantalRoot Segment := ⟨[s, m, a]⟩

/-- √sam 'kiss' gives [sam-ä] PFV.3MSG, [sam-o] GRND and [mäsam] INF (12d). -/
def sam : ConsonantalRoot Segment := ⟨[s, a, m]⟩

/-- √hid 'go' gives [hed-ä] PFV.3MSG, [hed-o] GRND and [mähed] INF (12e). -/
def hid : ConsonantalRoot Segment := ⟨[h, i, d]⟩

end Amharic
