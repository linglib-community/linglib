module

public import Linglib.Semantics.Modification.Classification
public import Linglib.Semantics.Possession.Relationalizer

/-!
# Partee and Borschev (2003): Genitives, Relational Nouns, and Argument-Modifier Ambiguity

Partee and Borschev repeat their [earlier argument](##ParteeBorschev2001.readingB_ne_π) that
*Mary's former mansion* needs the free relation inside the scope of *former*, and ask whether a
modifier-only analysis could deliver it after all. *former* can target the relation part of a
relational *mansion*, which on [something that stays a mansion](##former_π_iff_of_forall) is
Reading B, but how the possessive then picks that relation remains open. The readings differ only
because the relation can change:
[when it does not, they coincide](##readingA_eq_readingB_of_constant).

## Implementation notes

The `PAST` of (50) is read as `Modifier.former` on the relation, since *former* is what applies.

## TODO

* The rest of §6, the modifier-only analysis with `Sort` and `R_GEN` (47), and the argument for
  ambiguity from ellipsis (§6.4), are not represented.
* The paper's tree (21) and its discussion of the Russian genitive are not represented.

## References

* [partee-borschev-2003]
* [partee-borschev-2001]
* [jensen-vikner-1994]
* [vikner-jensen-2002]
-/

@[expose] public section

namespace ParteeBorschev2003

open Modifier Possession

variable {I E : Type*} [LT I] {N : I → E → Prop} {R : E → I → E → Prop} {y x : E} {t : I}

/-- When the free relation does not change over time, Reading A and Reading B coincide. -/
theorem readingA_eq_readingB_of_constant (hR : ∀ t t' x, R y t x ↔ R y t' x) :
    π (former N) R y = former (π N R y) := by
  funext t x
  simp only [former_apply, π_apply₂, eq_iff_iff]
  grind

/-- On what stays an `N`, *former* on the whole relational noun (20) is *former* on its relation
part alone (50), §6.2.2. -/
theorem former_π_iff_of_forall (hN : ∀ t', N t' x) :
    former (π N R y) t x ↔ N t x ∧ former (R y) t x := by
  simp [π_apply₂, hN]

end ParteeBorschev2003
