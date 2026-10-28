module

public import Linglib.Semantics.Polarity.Item
public import Linglib.Fragments.Icelandic.TemporalConnectives

/-!
# Icelandic polarity items

Polarity items of Icelandic typed by `PolarityItem`: *fyrr en*, literally 'earlier than', the
punctual *until* that needs the negation *ekki*. The sentences that attest it are rows of
`Data/Examples/Giannakidou2002.json`.

## References

* [giannakidou-2002]
-/

@[expose] public section

namespace Icelandic.PolarityItems

open PolarityItem

/-- *fyrr en*, the punctual *until*, licensed by negation. Its connective entry is
`Icelandic.TemporalConnectives.fyrrEn`. -/
def fyrrEn : PolarityItem :=
  { form := TemporalConnectives.fyrrEn.form
  , licensor := some .antiAdditive }

end Icelandic.PolarityItems
