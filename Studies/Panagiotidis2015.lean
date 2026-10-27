module

public import Linglib.Morphology.Word.Basic
public import Linglib.Syntax.Minimalist.ExtendedProjection

/-!
# Panagiotidis (2015): Categorial Features

This file formalizes Panagiotidis's theory of word class: lexical category is
not a property of roots but of the categorizer heads *n*, *v*, and *a* that category-neutral
roots merge with, as Marantz proposed, and the categorial features those heads bear are
substantive and interpretable rather than diacritic, [N] imposing a sortal perspective and
[V] a perspective extending into time on the root's concept. Nouns bear [N] only, verbs [V]
only, adjectives both, and adpositions neither, the adposition being the default categorizer
(`categorizer_features`, `isCategorizer_iff`). The functional heads of an extended projection
carry uninterpretable copies of their categorizer's features, so a category's features are
fixed by its family (`categorialFeatures_eq_iff`), and the diacritic features Chomsky proposed
in 1970 cut the categories into the same four classes (`chomsky_panagiotidis_agree`).
Category change is change of categorizer: an English root surfaces in all three categorized
classes (`RootFamily`, `all_families_tricategorial`).

## Implementation notes

The features of a category are read off its extended-projection family, since the book has
every functional head carry a copy of its categorizer's features; the substrate's `Cat.features`
reads Chomsky's features off the family the same way, so the two systems are compared as
images of the family. The book's distinction between a categorizer's interpretable features and
the copies on functional heads is not represented. The root families are the standard English
illustrations of category-neutral roots from the Distributed Morphology literature rather than
data from the book.

## References

* [panagiotidis-2015]
* [chomsky-1970]
* [marantz-1997]
-/

@[expose] public section

namespace Panagiotidis2015

open Minimalist

/-- Panagiotidis's categorial features, [N] a sortal perspective and [V] a perspective extending
into time, substantive and interpretable on a categorizer. -/
structure CategorialFeatures where
  hasN : Bool
  hasV : Bool
  deriving DecidableEq, Repr

/-- The features of a family's categorizer, where *n* bears [N], *v* bears [V], *a* both, and the
adposition, the default categorizer, neither. -/
def CategorialFeatures.ofFamily : CatFamily → CategorialFeatures
  | .nominal => ⟨true, false⟩
  | .verbal => ⟨false, true⟩
  | .adjectival => ⟨true, true⟩
  | .adpositional => ⟨false, false⟩

theorem CategorialFeatures.ofFamily_injective :
    Function.Injective CategorialFeatures.ofFamily := by
  intro a b h
  cases a <;> cases b <;> simp_all [CategorialFeatures.ofFamily]

/-- The features of a category are those of its family's categorizer, which every functional
head of the extended projection carries as an uninterpretable copy. -/
def categorialFeatures (c : Cat) : CategorialFeatures := .ofFamily c.family

/-- The categorizers are *v*, *n* and *a*; the categorized lexical heads are root-plus-categorizer
complexes. -/
def IsCategorizer : Cat → Prop
  | .v | .n | .a => True
  | _ => False

instance : DecidablePred IsCategorizer := fun c ↦ by
  cases c <;> unfold IsCategorizer <;> infer_instance

theorem isCategorizer_iff (c : Cat) : IsCategorizer c ↔ c = .v ∨ c = .n ∨ c = .a := by
  cases c <;> simp [IsCategorizer]

theorem categorizer_features :
    categorialFeatures .n = ⟨true, false⟩ ∧ categorialFeatures .v = ⟨false, true⟩ ∧
      categorialFeatures .a = ⟨true, true⟩ ∧ categorialFeatures .P = ⟨false, false⟩ := by
  decide

theorem categorialFeatures_eq_iff (c₁ c₂ : Cat) :
    categorialFeatures c₁ = categorialFeatures c₂ ↔ c₁.family = c₂.family :=
  CategorialFeatures.ofFamily_injective.eq_iff

theorem chomsky_panagiotidis_agree (c₁ c₂ : Cat) :
    categorialFeatures c₁ = categorialFeatures c₂ ↔ c₁.features = c₂.features := by
  rw [categorialFeatures_eq_iff, Cat.features_eq_iff]

/-- A categorizer merges directly with the root, the lexical head of its family. -/
theorem step_of_isCategorizer {c : Cat} (h : IsCategorizer c) : c.family.lexical.Step c := by
  cases c <;> first | decide +kernel | exact h.elim

/-- A category-neutral root with the surface words it projects across the lexical categories,
each stamped with its Universal Dependencies category ([marantz-1997]). -/
structure RootFamily where
  /-- A label for the root; roots themselves are sub-morphemic. -/
  rootLabel : String
  /-- The surface words it projects. -/
  words : List Morphology.Word

/-- The family has a surface form in category `c`. -/
def RootFamily.HasCategory (rf : RootFamily) (c : UD.UPOS) : Prop :=
  ∃ w ∈ rf.words, w.cat = c

instance (rf : RootFamily) (c : UD.UPOS) : Decidable (rf.HasCategory c) :=
  List.decidableBEx _ rf.words

/-- The root √DESTROY surfaces as destroy, destruction and destructive. -/
def destroy : RootFamily :=
  ⟨"DESTROY", [.mk' "destroy" .VERB, .mk' "destruction" .NOUN, .mk' "destructive" .ADJ]⟩

/-- The root √BEAUTY surfaces as beautify, beauty and beautiful. -/
def beauty : RootFamily :=
  ⟨"BEAUTY", [.mk' "beautify" .VERB, .mk' "beauty" .NOUN, .mk' "beautiful" .ADJ]⟩

/-- The root √CLEAR surfaces as clear, clarity and clear. -/
def clear : RootFamily :=
  ⟨"CLEAR", [.mk' "clear" .VERB, .mk' "clarity" .NOUN, .mk' "clear" .ADJ]⟩

/-- The root √PRODUCE surfaces as produce, production and productive. -/
def produce : RootFamily :=
  ⟨"PRODUCE", [.mk' "produce" .VERB, .mk' "production" .NOUN, .mk' "productive" .ADJ]⟩

/-- The root √CREATE surfaces as create, creation and creative. -/
def create : RootFamily :=
  ⟨"CREATE", [.mk' "create" .VERB, .mk' "creation" .NOUN, .mk' "creative" .ADJ]⟩

/-- The root √ACT surfaces as act, action and active. -/
def act : RootFamily := ⟨"ACT", [.mk' "act" .VERB, .mk' "action" .NOUN, .mk' "active" .ADJ]⟩

/-- The sample root families. -/
def allFamilies : List RootFamily := [destroy, beauty, clear, produce, create, act]

theorem all_families_tricategorial :
    ∀ rf ∈ allFamilies, rf.HasCategory .VERB ∧ rf.HasCategory .NOUN ∧ rf.HasCategory .ADJ := by
  decide

end Panagiotidis2015
