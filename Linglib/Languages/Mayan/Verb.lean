module

public import Mathlib.Tactic.DeriveFintype

/-!
# Mayan transitive verb classes

A Mayan transitive verb is radical, with a monosyllabic root ending in a consonant or a glottal
stop, or derived, with a polysyllabic vowel-final root, and the voice and Agent Focus suffixes
of the K'ichean languages select their allomorphs by the class.

## References

* [heaton-deen-ogrady-2016]
* [mondloch-2017]
-/

@[expose] public section

namespace Mayan

/-- A transitive verb is derived, with a polysyllabic vowel-final root, or radical, with a
monosyllabic root ending in a consonant or a glottal stop. -/
inductive VerbClass where
  | derived
  | radical
  deriving DecidableEq, Repr, Fintype

end Mayan
