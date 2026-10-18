module

public import Linglib.Syntax.CCG.Derivation
public import Linglib.Phonology.Prosody.Intonation
public import Linglib.Core.Order.Flat
public import Mathlib.Tactic.DeriveFintype

/-!
# CCG intonation and information structure

Steedman aligns prosodic structure with CCG derivations through an INFORMATION feature, theme or
rheme, that pitch accents mark on words and that combination unifies up the derivation. CCG's
spurious ambiguity is the engine: alternative derivations of one string are alternative
information structures, disambiguated by intonation, so "Anna married Manny" derives both
[Anna][married Manny] and, by composition, [Anna married][Manny], and the theme tune on
"ANNA married" selects the latter. Because a `ProsodicPhrase` carries a `Derivation`, only CCG
constituents can be prosodic phrases, which is Selkirk's Sense Unit Condition by construction.

## Main definitions

* `CCG.Intonation.Info`, `CCG.Intonation.InfoFeature`: the values of the INFORMATION feature,
  and the feature, a value or unmarked in the flat order.
* `CCG.Intonation.accentInfo`: the marking an accent slot contributes.
* `CCG.Derivation.infoFeature`: the feature a derivation projects under an accent assignment,
  `none` on a theme/rheme clash.
* `CCG.Intonation.Tune`, `CCG.Intonation.themeTune`, `CCG.Intonation.rhemeTune`: pitch accent
  plus terminal contour.
* `CCG.Intonation.ProsodicPhrase`, `CCG.Intonation.extractInfoStructure`: tune-marked
  constituents and the theme/rheme partition of an utterance.

## Implementation notes

The prosodic vocabulary comes from `Prosody`'s autosegmental-metrical types. Relating these
phrases to the phonology-side prosodic hierarchy (`Phonology/Prosody/Phrase`) is left to
study-level work.

## References

* [steedman-2000]
* [selkirk-1984]
* [pierrehumbert-hirschberg-1990]
* [carpenter-1992]
* [kuroda-1972]
-/

@[expose] public section

namespace CCG.Intonation

open CCG
open Prosody

/-! ### The INFORMATION feature -/

/-- The values of the INFORMATION feature of [steedman-2000]. -/
inductive Info where
  /-- Theme. -/
  | θ
  /-- Rheme. -/
  | ρ
  /-- Phrasal, after a boundary has applied. -/
  | φ
  deriving Repr, DecidableEq, Fintype

/-- The INFORMATION feature is a value or unmarked, the underspecified feature that "can unify
with either" theme or rheme. It carries the flat order of feature unification
([carpenter-1992]): unmarked is `⊥`, the values are pairwise incomparable above it, unification
is the partial join and generalization the meet. -/
abbrev InfoFeature := Flat Info

namespace InfoFeature

/-- The theme. -/
@[match_pattern] abbrev θ : InfoFeature := Flat.some .θ

/-- The rheme. -/
@[match_pattern] abbrev ρ : InfoFeature := Flat.some .ρ

/-- The phrasal feature. -/
@[match_pattern] abbrev φ : InfoFeature := Flat.some .φ

end InfoFeature

/-! ### Projecting information structure through a derivation -/

/-- The information marking an accent slot contributes. In [steedman-2000] L+H* marks the
theme and H* and H*+L the rheme, and unaccented material is unmarked. The book classes no other
accent, and the rest are grouped with the rheme here. -/
def accentInfo : Option PitchAccent → InfoFeature
  | some (.leading .L .H) => .θ
  | none => ⊥
  | some _ => .ρ

/-- An assignment of pitch accents to the tokens of a derivation, `none` for an unaccented
token. -/
def AccentAssignment (T : Type*) := T → Option PitchAccent

/-- The INFORMATION feature a derivation projects under an accent assignment. Leaves contribute
the `accentInfo` of their accent and combination unifies the daughters' features, with `none` on
a theme/rheme clash, the prosodic analogue of `Derivation.interp`'s reading of the same tree. -/
def _root_.CCG.Derivation.infoFeature {T α : Type*} {R : RuleSystem α}
    (acc : AccentAssignment T) : {c : Cat α} → Derivation T R c → Option InfoFeature
  | _, .lex f _ => some (accentInfo (acc f))
  | _, .node _ d₁ d₂ => do (← d₁.infoFeature acc).unify (← d₂.infoFeature acc)

/-! ### Tunes and prosodic phrases -/

/-- An intonational tune is a pitch accent plus a terminal contour. Of the two main tunes of
English in [steedman-2000], L+H* LH% marks the theme and H* LL% the rheme. -/
structure Tune where
  /-- The pitch accent. -/
  accent : PitchAccent
  /-- The phrase accent and boundary tone. -/
  terminal : TerminalContour
  deriving Repr, DecidableEq

/-- The theme tune, L+H* with the rise LH%. -/
def themeTune : Tune := ⟨.leading .L .H, ⟨.L, .H⟩⟩

/-- The rheme tune, H* with the fall LL%. -/
def rhemeTune : Tune := ⟨.mono .H, ⟨.L, .L⟩⟩

/-- A prosodic phrase is a tune-marked CCG constituent. Because `deriv` is a derivation, only
constituents can be phrases, the Sense Unit Condition of [selkirk-1984] by construction. -/
structure ProsodicPhrase (T : Type*) {α : Type*} (R : RuleSystem α) where
  /-- The category of the constituent. -/
  cat : Cat α
  /-- The constituent's derivation. -/
  deriv : Derivation T R cat
  /-- The tune the phrase carries. -/
  tune : Tune

/-- An information-structure analysis is a theme/rheme partition, following [steedman-2000].
The theme is what the utterance is about (the λ-abstract presupposing a QUD, marked in English by
the L+H* LH% tune per [pierrehumbert-hirschberg-1990]) and the rheme is what is asserted about it
(marked H* LL%). `theme := none` encodes an all-rheme structure, thetic in [kuroda-1972]'s sense,
with no theme constituent. -/
structure InfoStructure (P : Type*) where
  /-- The theme (λ-abstract, presupposed QUD); `none` for all-rheme
  (thetic) structures. -/
  theme : Option P
  /-- The rheme (comment, answer, assertion). -/
  rheme : P
  /-- Focused elements (evoking alternatives). -/
  foci : List P := []
  /-- Background elements (given). -/
  background : List P := []

/-- The information structure of a sequence of prosodic phrases takes the phrase with the theme
tune as theme and the phrase with the rheme tune as rheme, and a theme-less utterance is
all-rheme. It is `none` when the phrases yield no coherent partition. -/
def extractInfoStructure {T α : Type*} {R : RuleSystem α} (phrases : List (ProsodicPhrase T R)) :
    Option (InfoStructure (ProsodicPhrase T R)) :=
  let themes := phrases.filter (·.tune == themeTune)
  let rhemes := phrases.filter (·.tune == rhemeTune)
  match themes, rhemes with
  | [t], [r] => some { theme := some t, rheme := r }
  | [], [r] => some { theme := none, rheme := r }
  | _, _ => none

end CCG.Intonation
