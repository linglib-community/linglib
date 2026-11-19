module

public import Linglib.Syntax.CCG.Derivation
public import Linglib.Phonology.Prosody.Intonation
public import Linglib.Core.Order.Flat
public import Mathlib.Tactic.DeriveFintype

/-!
# CCG intonation and information structure

In Steedman's account of English intonation, a pitch accent marks its word as part of the
*theme* of the utterance, what it is about, or of the *rheme*, what it says about the theme. The
marking is a feature of the word's category, called INFORMATION, and it spreads: when two
constituents combine their features are unified, an unaccented word taking on the value of its
neighbour, and a theme-marked constituent cannot combine with a rheme-marked one. The feature
of a derivation is therefore [the join of the features of its
words](##CCG.Derivation.infoFeature_le_iff), with `⊤` for a clash. It follows that [two
derivations of one string project the same feature](##CCG.Derivation.infoFeature_eq_of_yield_eq)
and that [a string with a theme accent and a rheme accent has no derivation without a
clash](##CCG.Derivation.infoFeature_eq_top_of_not_compat). Intonation does not choose among the
derivations of a phrase. It chooses how the utterance divides into phrases, each of which must
be a constituent.

## Implementation notes

[steedman-2000] treats two of the pitch accents of [pierrehumbert-1980], L+H* and H*, so the
accents are given as a function of the two values, `Info.accent`. Boundary tones are elements
of the string in the book, functions from a theme- or rheme-marked category into a phrasal
category with a third value of the feature that unifies only with itself. They are not
modelled: a boundary is represented by where an utterance is divided, and the feature has the
two values that accents assign.

## TODO

Boundaries as string elements, with the phrasal value and the unmarked theme that a boundary
closes, need INFORMATION on the categories of `CCG.Cat`.

## References

* [steedman-2000]
* [pierrehumbert-1980]
* [carpenter-1992]
-/

@[expose] public section

open Prosody

namespace CCG

/-! ### The INFORMATION feature -/

/-- The values that pitch accents give the INFORMATION feature of [steedman-2000]. -/
inductive Info where
  /-- Theme. -/
  | θ
  /-- Rheme. -/
  | ρ
  deriving Repr, DecidableEq, Fintype

/-- The INFORMATION feature is a value or unspecified, and an unspecified feature unifies with
either value. It carries the flat order of feature unification ([carpenter-1992]): unspecified
is `⊥` and the values are incomparable above it. -/
abbrev InfoFeature := Flat Info

namespace InfoFeature

/-- The theme. -/
@[match_pattern] abbrev θ : InfoFeature := Flat.some .θ

/-- The rheme. -/
@[match_pattern] abbrev ρ : InfoFeature := Flat.some .ρ

end InfoFeature

/-- The pitch accent that marks a value in [steedman-2000]: L+H* the theme and H* the rheme. -/
def Info.accent : Info → PitchAccent
  | .θ => .leading .L .H
  | .ρ => .mono .H

theorem Info.accent_injective : Function.Injective Info.accent := by decide

/-! ### Projecting the feature through a derivation -/

namespace Derivation

variable {T α : Type*} {R : RuleSystem α} {c c' : Cat α} (mark : T → InfoFeature)

/-- The INFORMATION feature a derivation projects when `mark` gives the feature of each word.
A leaf has the feature of its word and a combination the unification of its daughters'
features, `⊤` when a theme meets a rheme. -/
def infoFeature : {c : Cat α} → Derivation (fun _ ↦ T) R c → WithTop InfoFeature
  | _, .lex _ t => (mark t : InfoFeature)
  | _, .node _ d₁ d₂ => d₁.infoFeature ⊔ d₂.infoFeature

@[simp] theorem infoFeature_lex (c : Cat α) (t : T) :
    (lex (W := fun _ ↦ T) (R := R) c t).infoFeature mark = (mark t : InfoFeature) := rfl

@[simp] theorem infoFeature_node {l r : Cat α} (ru : Rule R l r c) (d₁ : Derivation (fun _ ↦ T) R l)
    (d₂ : Derivation (fun _ ↦ T) R r) :
    (node ru d₁ d₂).infoFeature mark = d₁.infoFeature mark ⊔ d₂.infoFeature mark := rfl

variable {mark}

/-- The feature of a derivation is the least bound of the features of its words. -/
theorem infoFeature_le_iff {d : Derivation (fun _ ↦ T) R c} {x : WithTop InfoFeature} :
    d.infoFeature mark ≤ x ↔ ∀ t ∈ d.yield, (mark t : WithTop InfoFeature) ≤ x := by
  induction d with
  | lex c t => simp [yield]
  | node ru d₁ d₂ ih₁ ih₂ => simp [yield, ih₁, ih₂, or_imp, forall_and]

theorem le_infoFeature {d : Derivation (fun _ ↦ T) R c} {t : T} (ht : t ∈ d.yield) :
    (mark t : WithTop InfoFeature) ≤ d.infoFeature mark :=
  infoFeature_le_iff.1 le_rfl t ht

/-- Derivations of one string project one feature, whatever their combinatory structure and
their categories. -/
theorem infoFeature_eq_of_yield_eq {d : Derivation (fun _ ↦ T) R c}
    {d' : Derivation (fun _ ↦ T) R c'} (h : d.yield = d'.yield) :
    d.infoFeature mark = d'.infoFeature mark :=
  eq_of_forall_ge_iff fun x ↦ by rw [infoFeature_le_iff, infoFeature_le_iff, h]

/-- A derivation over two words whose features do not unify clashes. -/
theorem infoFeature_eq_top_of_not_compat {d : Derivation (fun _ ↦ T) R c} {t u : T}
    (ht : t ∈ d.yield) (hu : u ∈ d.yield) (h : ¬ Compat (mark t) (mark u)) :
    d.infoFeature mark = ⊤ := by
  by_contra hd
  obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hd
  exact h (.of_le (WithTop.coe_le_coe.1 (hx ▸ le_infoFeature ht))
    (WithTop.coe_le_coe.1 (hx ▸ le_infoFeature hu)))

end Derivation

end CCG
