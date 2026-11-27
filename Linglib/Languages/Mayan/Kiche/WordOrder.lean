module

public import Linglib.Syntax.WordOrder

/-!
# K'iche' word order

K'iche' (K'ichean Mayan) is verb-initial. Intransitive clauses are verb–subject, and transitive
clauses are verb–object–subject, the preferred order Mondloch describes, or verb–subject–object;
subject-initial orders are increasingly found under Spanish contact. Clemens and Coon survey the
derivational accounts of Mayan verb-initiality.

## References

* [clemens-coon-2018]
* [mondloch-2017]
-/

@[expose] public section

namespace Kiche

/-- The transitive clause orders, verb–object–subject preferred and verb–subject–object also
found. -/
def clauseOrders : Finset (WordOrder.Arrangement WordOrder.Constituent 3) := {.vos, .vso}

theorem verb_initial : ∀ a ∈ clauseOrders, a.IsInitial .verb := by
  decide

end Kiche
