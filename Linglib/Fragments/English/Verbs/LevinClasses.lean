module

public import Linglib.Fragments.English.Verbs.Inventory

/-!
# The Levin links of the English verbs

Each English verb entry names the record of its verb in Levin's catalogue, or states that the
catalogue does not list it. The record of a linked entry spells the entry's citation form, and
every class an entry excludes lists the verb, so that an exclusion does not outlive a correction of
the catalogue.

## References

* [levin-1993]
-/

@[expose] public section

namespace English.Verbs

/-- Every linked record spells the entry's citation form. -/
example : ∀ v ∈ verbs, ∀ e ∈ v.levin, e.form = v.form := by decide +kernel

/-- Every class an entry excludes lists its verb. -/
example : ∀ v ∈ verbs, v.levinExcluded ⊆ (v.levin.map (·.classes.toFinset)).getD ∅ := by
  decide +kernel

end English.Verbs
