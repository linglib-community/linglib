module

public import Studies.Owusu2022
public import Studies.Zimmermann2008
public import Linglib.Semantics.Reference.Rigidity

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

public section


namespace Zimmermann2026

open Quantifier Quantifier.Det

/-- Under the existential analysis (16b), the two scopings of *wani* under negation in (13) differ
on the passenger model of [zimmermann-2008]. -/
theorem wani_scopings_diverge :
    ¬ ((¬ ∃ x : Zimmermann2008.Faasinjee, Zimmermann2008.Daura x) ↔
      Det.some Set.univ {x : Zimmermann2008.Faasinjee | ¬ Zimmermann2008.Daura x}) :=
  fun h ↦ Zimmermann2008.wani_narrow_scope_false (h.mpr Zimmermann2008.wani_wide_scope)

/-- Under the choice-function analysis (16a), *bí* under negation, as in (15), is not the narrow
reading when the restrictor has two members. -/
theorem bi_reading_not_narrow {S E : Type*} (f : S → ChoiceFunction E) {s : S}
    {P : S → Set E} {a b : E} (ha : a ∈ P s) (hb : b ∈ P s) (hab : a ≠ b) :
    ¬ ∀ VP : Set E, f s (P s) ∉ VP ↔ ¬ Det.some (P s) VP := fun h ↦ by
  have h' := (Owusu2022.negation_narrow_iff f ⟨a, ha⟩).mp h
  rw [h'] at ha hb
  exact hab ((Set.mem_singleton_iff.1 ha).trans (Set.mem_singleton_iff.1 hb).symm)

/-- Under an operator that is not intensional, such as negation, the bound and free construals of
the situation argument of *bí* (16a) coincide, so that the operator cannot shift it, as the
explanation of (15) requires (p. 7). -/
theorem bi_construals_collapse {S E : Type*} {O : (S → Prop) → S → Prop} {s₀ : S}
    (hO : IsExtensionalAt O s₀) (f : S → ChoiceFunction E) (P : S → Set E)
    (VP : E → S → Prop) :
    smallScope O VP (fun s ↦ f s (P s)) s₀ = largeScope O VP (fun s ↦ f s (P s)) s₀ :=
  (hO.largeScope_eq_smallScope VP _).symm

example {S E : Type*} (f : S → ChoiceFunction E) (s₀ : S) (P : S → Set E)
    (VP : E → S → Prop) :
    smallScope (fun p s ↦ ¬ p s) VP (fun s ↦ f s (P s)) s₀ =
      largeScope (fun p s ↦ ¬ p s) VP (fun s ↦ f s (P s)) s₀ :=
  bi_construals_collapse isExtensionalAt_not f P VP

end Zimmermann2026
