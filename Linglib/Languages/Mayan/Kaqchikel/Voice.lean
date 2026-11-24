module

public import Linglib.Syntax.Voice.Basic

/-!
# Kaqchikel voice

A Kaqchikel transitive verb has an active with a null suffix, an absolutive antipassive in *-Vn* and
a passive in *-V̈x*; its Agent Focus is in `Extraction.lean`.

## References

* [burukina-polinsky-2025]
-/

@[expose] public section

namespace Kaqchikel

/-- The transitive stem, with a null suffix: the active. -/
def active : Voice := Voice.active

/-- *-Vn*: the absolutive antipassive. -/
def antipassive : Voice := Voice.antipassive.marked [.suff "Vn"]

/-- *-V̈x*: the passive. -/
def passive : Voice := Voice.passive.marked [.suff "V̈x"]

/-- The antipassive is an antipassivization and the passive a passivization. -/
theorem alternationTypes : antipassive.IsAntipassivization ∧ passive.IsPassivization := by decide

end Kaqchikel
