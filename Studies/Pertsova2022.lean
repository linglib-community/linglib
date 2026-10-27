module

public import Studies.Harbour2016

/-!
# Pertsova (2022): A case for a binary feature underlying clusivity

[pertsova-2022] argues from a 270-language pronoun database that inclusive is a kind of first
person distinguished from the exclusive by a binary feature, against containment accounts in
which a privative [ADDRESSEE] makes the inclusive a superset of the exclusive. Her feature
hierarchy (4) places AUTHOR under +PARTICIPANT and ADDRESSEE under AUTHOR, so a language
activates PARTICIPANT, then AUTHOR, then ADDRESSEE, and the categories are the referent sets the
active feature values pick out (5). The hierarchy predicts which persons can be fully conflated:
activating PARTICIPANT, AUTHOR and ADDRESSEE in turn gives two, three and four persons, and
inclusive never conflates with second person, nor second with third, nor first with third (p.
402), conflation arising only from inactive features (p. 403). Against [harbour-2016] she argues
that his author bipartition, second with third against first, is doubtful for pronouns (pp.
425–426), and she grounds the priority of AUTHOR over ADDRESSEE in the privileged status of
speakers (p. 426).

## Implementation notes

The features are those of `Harbour2016.ThreeFeature` on participant sets, ADDRESSEE being
[hearer]. With no feature active the hierarchy gives the monopartition, which the paper does not
discuss; it is included as the empty initial segment. Number is not modeled, so the referent sets
of (5) appear as their participant sets, *me+other(s)* as `{speaker}`. Pertsova's argument from
ABA patterns and derived exclusives (§§2.3, 5) needs vocabulary insertion with blocking and is
not formalized.

## References

* [pertsova-2022]
* [harbour-2016]
-/

@[expose] public section

namespace Pertsova2022

open Discourse Finset Harbour2016

/-- The feature hierarchy (4): AUTHOR depends on +PARTICIPANT and ADDRESSEE on AUTHOR, so the
active features form an initial segment of participant, author, addressee. -/
def Active (F : Finset ThreeFeature) : Prop :=
  (.author ∈ F → .participant ∈ F) ∧ (.hearer ∈ F → .author ∈ F)

instance : DecidablePred Active := fun _ ↦ by unfold Active; infer_instance

/-- The active feature sets generate four person systems (p. 402). -/
theorem image_graph_active :
    (univ.filter Active).image graph =
      {graph ∅, graph {.participant}, graph {.participant, .author},
        graph {.participant, .author, .hearer}} := by
  decide

theorem card_image_graph_active : ((univ.filter Active).image graph).card = 4 := by decide

/-- Harbour's author bipartition, which [±author] alone generates, is not among them. -/
theorem graph_active_ne_authorBipartition (F : Finset ThreeFeature) (hF : Active F) :
    graph F ≠ graph {.author} := by
  revert F; decide

/-- Under active features, inclusive conflates with second person only if exclusive does, and
likewise for the other pairs (pp. 402–403). -/
theorem no_partial_conflation (F : Finset ThreeFeature) (hF : Active F) :
    ((generated F).r {.speaker, .addressee} {.addressee} →
        (generated F).r {.speaker, .addressee} {.speaker}) ∧
      ((generated F).r {.addressee} ∅ → (generated F).r {.addressee} {.speaker}) ∧
      ((generated F).r {.speaker} ∅ → (generated F).r {.speaker} {.addressee}) := by
  simp only [generated_r_iff]
  revert F; decide

-- (9), (4)
theorem admissible_authorBipartition : Admissible {.author} ∧ ¬ Active {.author} := by decide

end Pertsova2022
