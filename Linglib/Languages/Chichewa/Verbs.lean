module

public import Linglib.Syntax.Category.Verb.Defs

/-!
# Chichewa verbs

The verb roots *mang-* 'tie', which is transitive, and *uk-* 'wake up', which is intransitive.

## References

* [hyman-mchombo-1992]
-/

@[expose] public section

namespace Chichewa.Verbs

/-- *mang-* 'tie'. -/
def mang : Verb where
  morphs := [.root "mang"]
  valency := .ofFrame ArgumentFrame.np

/-- *uk-* 'wake up'. -/
def uk : Verb where
  morphs := [.root "uk"]
  valency := .ofFrame ArgumentFrame.intransitive

end Chichewa.Verbs
