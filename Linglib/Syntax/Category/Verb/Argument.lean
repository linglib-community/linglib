module

public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.ThetaRole
public import Linglib.Semantics.ArgumentStructure.Linking

/-!
# Verb arguments

The argument slots of a verb entry, read off its basic frame (`ArgumentFrame.Slot`). Role labels
are derived classifications of the slots: `Verb.thetaLabel` gives the Dowty cluster label of a
slot's entailment profile (`Verb.slotProfile?`), and the comparative S/A/P/R/T classification is
the frame's (`ArgumentFrame.argumentRole`), never a stored feature. `Verb.linkedFrame?` assembles
the basic frame and the derived labels into the verb's argument structure.

## References

* [comrie-1978]
* [dowty-1991]
* [haspelmath-2021]
-/

@[expose] public section

open ArgumentStructure

namespace Verb

variable (v : Verb)

/-- The core argument slots of the basic frame. -/
def coreSlots : List ArgumentFrame.Slot :=
  (v.valency.frames.head?.map ArgumentFrame.coreSlots).getD []

/-- `thetaLabel s` is the derived semantic-role label of the slot `s`, the cluster label of its
    entailment profile (`EntailmentProfile.toRole`). -/
def thetaLabel (s : ArgumentFrame.Slot) : Option ThetaRole :=
  (v.slotProfile? s).bind EntailmentProfile.toRole

/-- The lexical argument structure of a verb entry is its basic frame, each slot linked to the
label read off its entailment profile and required when the frame expresses it. -/
def linkedFrame? : Option LinkedFrame :=
  v.valency.frames.head?.map fun fr ↦
    { frame := fr
      roles := fr.slots.map fun s ↦
        (s, { admits := (v.thetaLabel s).toList.toFinset
              obligatory := (fr.get? s).any fun p ↦ decide p.IsExpressed }) }

end Verb
