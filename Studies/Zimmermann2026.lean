module

public import Studies.Owusu2022
public import Studies.Zimmermann2008
public import Linglib.Logic.Modal.Extensional

/-!
# Zimmermann (2026): African Lambdas I, The Nominal Domain

Zimmermann's review of formal semantic work on African languages compares two marked indefinites
in its §3.3. Akan *bí* and Hausa *wani* have nearly the same distribution, but under negation a
*wani* phrase takes either scope, (13), while a *bí* phrase takes only wide scope, (15). The
review concludes that they need different analyses, (16): a choice function skolemized to a
situation for *bí*, after Owusu, and an existential quantifier for *wani*, after Zimmermann's
earlier work. It explains the scope of *bí* by negation not being an intensional operator, so
that negation cannot shift the situation argument of the function.

## Implementation notes

* Only the comparison the review itself draws is formalized; the two analyses are consumed from
  the studies of their primary sources.
* Bare noun phrases, which take obligatory narrow scope in both languages, are outside the
  classification of (16).

## TODO

* The Ga markers *ko* and *kome* of (17) and the co-occurrence of definite and indefinite
  markers of (18).

## References

* [zimmermann-2026]
* [zimmermann-2014]
* [zimmermann-2008]
* [owusu-2022]
-/

@[expose] public section


namespace Zimmermann2026

open Quantifier Quantifier.GQ

/-- Under the existential analysis (16b), the two scopings of *wani* under negation in (13) differ
on the passenger model of [zimmermann-2008]. -/
theorem wani_scopings_diverge :
    ¬ ((¬ ∃ x : Zimmermann2008.Faasinjee, Zimmermann2008.Daura x) ↔
      GQ.some (fun _ : Zimmermann2008.Faasinjee ↦ True) (¬ Zimmermann2008.Daura ·)) :=
  fun h ↦ Zimmermann2008.wani_narrow_scope_false (h.mpr Zimmermann2008.wani_wide_scope)

/-- Under the choice-function analysis (16a), *bí* under negation, as in (15), is not the narrow
reading when the restrictor has two members. -/
theorem bi_reading_not_narrow {S E : Type*} (f : S → ChoiceFunction E) {s : S}
    {P : S → E → Prop} {a b : E} (ha : P s a) (hb : P s b) (hab : a ≠ b) :
    ¬ ∀ VP : E → Prop, ¬ VP (f s (P s)) ↔ ¬ GQ.some (P s) VP := fun h ↦
  have h' := (Owusu2022.negation_narrow_iff f ⟨a, ha⟩).mp h
  hab ((h' a ha).trans (h' b hb).symm)

/-- Under negation, the bound and free construals of the situation argument of *bí* coincide, as the
explanation of (15) requires. -/
theorem bi_negation_construals_collapse {S E : Type*}
    (f : S → ChoiceFunction E) (s₀ : S) (P : S → E → Prop) (VP : E → S → Prop) :
    (fun p s ↦ ¬ p s) (fun s ↦ VP (f s (P s)) s) s₀ ↔
      (fun p s ↦ ¬ p s) (fun s ↦ VP (f s₀ (P s₀)) s) s₀ :=
  iff_of_eq <| ModalLogic.isExtensionalAt_iff_forall_diag.mp ModalLogic.IsExtensionalAt.neg
    fun σ s ↦ VP (f σ (P σ)) s

end Zimmermann2026
