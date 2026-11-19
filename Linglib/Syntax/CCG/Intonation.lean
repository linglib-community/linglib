module

public import Linglib.Syntax.CCG.Derivation
public import Linglib.Phonology.Prosody.Intonation
public import Linglib.Core.Order.Flat
public import Mathlib.Tactic.DeriveFintype

/-!
# CCG intonation and information structure

Steedman integrates prosody with CCG categories through a feature INFORMATION of the whole
category, whose values are theme and rheme. A pitch accent sets the feature on the word that
bears it, a word with the null tone leaves it unspecified, and combination unifies the features
of the two daughters, so an accent's marking spreads over every constituent the word enters and
a theme accent cannot share a constituent with a rheme accent. Unification is the join of
`WithTop InfoFeature`, with `⊤` the clash, and the feature of a derivation is the join over its
leaves: it is [the least bound of the words' markings](##CCG.Derivation.infoFeature_le_iff),
so [derivations of one string project one feature](##CCG.Derivation.infoFeature_eq_of_yield_eq)
and [a string with a theme accent and a rheme accent has no unclashing
derivation](##CCG.Derivation.infoFeature_eq_top_of_not_compat). Intonation therefore cannot
choose among the derivations of one phrase; what it chooses is the division of the utterance
into phrases, each of which must be a constituent.

## Implementation notes

[steedman-2000] treats two of the pitch accents of [pierrehumbert-1980], L+H* and H*, and
`accentInfo` leaves the others unmarked. Boundary tones are elements of the string in the book,
functions from a theme- or rheme-marked category into a phrasal category with a third value of
the feature that unifies only with itself. They are not modelled: a boundary is represented by
where an utterance is divided, and the feature has the two values that accents assign.

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
open scoped PartialUnify

namespace CCG

/-! ### The INFORMATION feature -/

namespace Intonation

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

/-- The marking of a pitch accent in [steedman-2000]: L+H* marks the theme and H* the rheme.
These are the two accents the book treats. -/
def accentInfo : PitchAccent → InfoFeature
  | .leading .L .H => .θ
  | .mono .H => .ρ
  | _ => ⊥

@[simp] theorem accentInfo_leading_L_H : accentInfo (.leading .L .H) = .θ := rfl

@[simp] theorem accentInfo_mono_H : accentInfo (.mono .H) = .ρ := rfl

end Intonation

/-! ### Projecting the feature through a derivation -/

namespace Derivation

open Intonation

variable {T α : Type*} {R : RuleSystem α} {c c' : Cat α} (mark : T → InfoFeature)

/-- The INFORMATION feature a derivation projects when `mark` gives the feature of each word.
A leaf has the feature of its word and a combination the unification of its daughters'
features, `⊤` when a theme meets a rheme. -/
def infoFeature : {c : Cat α} → Derivation T R c → WithTop InfoFeature
  | _, .lex t _ => (mark t : InfoFeature)
  | _, .node _ d₁ d₂ => d₁.infoFeature ⊔ d₂.infoFeature

@[simp] theorem infoFeature_lex (t : T) (c : Cat α) :
    (lex (R := R) t c).infoFeature mark = (mark t : InfoFeature) := rfl

@[simp] theorem infoFeature_node {l r : Cat α} (ru : Rule R l r c) (d₁ : Derivation T R l)
    (d₂ : Derivation T R r) :
    (node ru d₁ d₂).infoFeature mark = d₁.infoFeature mark ⊔ d₂.infoFeature mark := rfl

variable {mark}

/-- The feature of a derivation is the least bound of the features of its words. -/
theorem infoFeature_le_iff {d : Derivation T R c} {x : WithTop InfoFeature} :
    d.infoFeature mark ≤ x ↔ ∀ t ∈ d.yield, (mark t : WithTop InfoFeature) ≤ x := by
  induction d with
  | lex t c => simp [yield]
  | node ru d₁ d₂ ih₁ ih₂ => simp [yield, ih₁, ih₂, or_imp, forall_and]

theorem le_infoFeature {d : Derivation T R c} {t : T} (ht : t ∈ d.yield) :
    (mark t : WithTop InfoFeature) ≤ d.infoFeature mark :=
  infoFeature_le_iff.1 le_rfl t ht

/-- Derivations of one string project one feature, whatever their combinatory structure and
their categories. -/
theorem infoFeature_eq_of_yield_eq {d : Derivation T R c} {d' : Derivation T R c'}
    (h : d.yield = d'.yield) : d.infoFeature mark = d'.infoFeature mark :=
  eq_of_forall_ge_iff fun x ↦ by rw [infoFeature_le_iff, infoFeature_le_iff, h]

/-- A derivation over two words whose features do not unify clashes. -/
theorem infoFeature_eq_top_of_not_compat {d : Derivation T R c} {t u : T} (ht : t ∈ d.yield)
    (hu : u ∈ d.yield) (h : ¬ Compat (mark t) (mark u)) : d.infoFeature mark = ⊤ := by
  by_contra hd
  obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hd
  exact h (.of_le (WithTop.coe_le_coe.1 (hx ▸ le_infoFeature ht))
    (WithTop.coe_le_coe.1 (hx ▸ le_infoFeature hu)))

end Derivation

end CCG
