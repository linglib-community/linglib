module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.Tactic.DeriveFintype

/-!
# Deep and surface anaphora

[hankamer-sag-1976] divide anaphoric processes into two kinds. A surface anaphor is derived by
deletion under identity with a linguistic antecedent, so its site keeps the syntactic structure of
the elided phrase: VP-ellipsis, sluicing, NP-ellipsis and argument ellipsis are surface anaphora. A
deep anaphor is a pro-form with no internal structure, interpreted as a pronoun is: null complement
anaphora, *pro*, empty nouns and *do it* are deep. This file defines the classification and its
defining property. The classification is of anaphoric processes, not nominals, and is independent
of the binding classes of `Binding.BindingClass`.

## Main definitions

* `Anaphor.Depth`: the depth of an anaphoric process, deep or surface.
* `Anaphor.Depth.HasInternalStructure`: the site of the anaphor contains syntactic structure,
  which holds of surface anaphora and of no others.

## Implementation notes

The classification is defined by internal structure alone. A framework says which of its null
sites are deep and which surface by a map into `Depth`, and proves of that map that a surface
site leaves some position unpronounced and a deep site none; the null sites of [E]-deletion in
`Syntax/Minimalist/Ellipsis.lean` have such a map. There is no class of such maps to instantiate.
The other properties Hankamer and Sag associated with depth, such as pragmatic control and the
missing-antecedent phenomenon, are tests for that structure, and a test is stated with the data
of the study that applies it.
[merchant-2013-diagnosing] keeps extraction, agreement and inverse scope as diagnostics of
ellipsis and sets pragmatic control aside, since an ellipsis can be pragmatically controlled under
limited conditions; [landau-2026] adds a test that decides depth where extraction and agreement
cannot, and `Studies/Landau2026.lean` shows when a test decides depth.

## References

* [hankamer-sag-1976]
* [merchant-2013-diagnosing]
* [landau-2026]
-/

@[expose] public section

namespace Anaphor

/-- The depth of an anaphoric process [hankamer-sag-1976]. A `surface` anaphor is derived by
deletion under identity and keeps the structure of the elided phrase; a `deep` anaphor is a
pro-form without internal structure. -/
inductive Depth where
  | deep
  | surface
  deriving DecidableEq, Repr, Fintype

namespace Depth

/-- The site of an anaphor has internal structure when the anaphor is surface: deletion leaves
the structure of the elided phrase in place, and a deep anaphor has none. -/
def HasInternalStructure (d : Depth) : Prop := d = .surface

instance : DecidablePred HasInternalStructure := fun _ ↦ inferInstanceAs (Decidable (_ = _))

end Depth

end Anaphor
