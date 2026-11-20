module

public import Linglib.Syntax.Minimalist.SyntacticObject.Term

/-!
# Nanosyntax: syntactic objects

A syntactic object of nanosyntax is a Minimalist syntactic object whose lexical items are single
features, an element of the free commutative magma `Minimalist.SyntacticObject F`. A feature `f`
merged with a complement `t` is `phrase f t`, the set $\{f, t\}$. A phrase whose complement is
absent, at the bottom of a sequence or after its complement has evacuated, is the singleton
$\{f\}$ of [blix-2022], written `bare f`. The phrase a feature sequence builds without movement
is its `spine`. An evacuated constituent beside the remnant it left is their Merge, a set of two
phrases, which no feature labels (`IsUnlabelled`).

The constituents of a spine that are spines on its foot are those of the initial parts of its
sequence (`spine_containsOrEq_spine_iff`), so an entry storing a spine shrinks to every smaller
size. A spine beside a remnant with another foot contains the spines on its own foot up to its
size and no larger one (`merge_spine_containsOrEq_spine_iff`).

## Implementation notes

* The free commutative magma has no singletons, so `bare f` is `phrase f trace`, the index-free
  trace standing for the absent complement. The bottom of a sequence and a phrase whose
  complement has evacuated are the same object.
* A derivation is built on planar objects, an evacuated constituent to the left of its remnant,
  since the pronunciation reads that order. `pphrase`, `pbare` and `pspine` are the planar
  counterparts, and stored objects and matching are unordered.

## References

* [blix-2022]
* [declercq-et-al-2025]
* [marcolli-chomsky-berwick-2025]
* [senturia-marcolli-2025]
-/

@[expose] public section

namespace Morphology.Nanosyntax

open Minimalist SyntacticObject

variable {F : Type}

/-- The phrase of the feature `f` over the complement `t`, the set `{f, t}`. -/
abbrev phrase (f : F) (t : SyntacticObject F) : SyntacticObject F := merge (leaf f) t

/-- The phrase of `f` with no complement, the set `{f}`. -/
abbrev bare (f : F) : SyntacticObject F := phrase f trace

/-- The phrase a feature sequence builds without evacuation, its first feature at the bottom. -/
def spine (f₀ : F) (fs : List F) : SyntacticObject F := fs.foldl (fun t f ↦ phrase f t) (bare f₀)

@[simp] theorem spine_nil (f₀ : F) : spine f₀ [] = bare f₀ := rfl

@[simp] theorem spine_concat (f₀ : F) (fs : List F) (f : F) :
    spine f₀ (fs ++ [f]) = phrase f (spine f₀ fs) := by simp [spine]

theorem exists_spine_eq_phrase (f₀ : F) (fs : List F) : ∃ f t, spine f₀ fs = phrase f t := by
  cases fs using List.reverseRecOn with
  | nil => exact ⟨f₀, trace, rfl⟩
  | append_singleton fs f => exact ⟨f, spine f₀ fs, spine_concat ..⟩

theorem spine_ne_leaf (f₀ : F) (fs : List F) (a : F) : spine f₀ fs ≠ leaf a := by
  obtain ⟨f, t, h⟩ := exists_spine_eq_phrase f₀ fs
  exact h ▸ Ne.symm (leaf_ne_merge _ _ _)

theorem spine_ne_trace (f₀ : F) (fs : List F) : spine f₀ fs ≠ (trace : SyntacticObject F) := by
  obtain ⟨f, t, h⟩ := exists_spine_eq_phrase f₀ fs
  exact h ▸ Ne.symm (trace_ne_merge _ _)

theorem phrase_eq_phrase_iff {f g : F} {t s : SyntacticObject F} (hs : ∀ a, s ≠ leaf a) :
    phrase f t = phrase g s ↔ f = g ∧ t = s := by
  rw [merge_eq_merge_iff]
  constructor
  · rintro (⟨h, rfl⟩ | ⟨h, -⟩)
    · exact ⟨leaf_inj.1 h, rfl⟩
    · exact absurd h.symm (hs f)
  · rintro ⟨rfl, rfl⟩
    exact .inl ⟨rfl, rfl⟩

theorem spine_eq_spine_iff {f₀ g₀ : F} {fs gs : List F} :
    spine f₀ fs = spine g₀ gs ↔ f₀ = g₀ ∧ fs = gs := by
  refine ⟨fun h ↦ ?_, fun ⟨h₀, h⟩ ↦ h₀ ▸ h ▸ rfl⟩
  induction fs using List.reverseRecOn generalizing gs with
  | nil =>
    cases gs using List.reverseRecOn with
    | nil => exact ⟨((phrase_eq_phrase_iff fun a ↦ (leaf_ne_trace a).symm).1 h).1, rfl⟩
    | append_singleton gs g =>
      rw [spine_nil, spine_concat, phrase_eq_phrase_iff (spine_ne_leaf g₀ gs)] at h
      exact absurd h.2.symm (spine_ne_trace g₀ gs)
  | append_singleton fs f ih =>
    cases gs using List.reverseRecOn with
    | nil =>
      rw [spine_nil, spine_concat, phrase_eq_phrase_iff fun a ↦ (leaf_ne_trace a).symm] at h
      exact absurd h.2 (spine_ne_trace f₀ fs)
    | append_singleton gs g =>
      rw [spine_concat, spine_concat, phrase_eq_phrase_iff (spine_ne_leaf g₀ gs)] at h
      obtain ⟨rfl, rfl⟩ := ih h.2
      exact ⟨rfl, by rw [h.1]⟩

theorem spine_eq_bare_iff {f₀ g₀ : F} {gs : List F} :
    spine f₀ gs = merge (leaf g₀) trace ↔ f₀ = g₀ ∧ gs = [] :=
  spine_eq_spine_iff (g₀ := g₀) (gs := [])

theorem spine_eq_phrase_spine_iff {f₀ g₀ f : F} {fs gs : List F} :
    spine f₀ gs = merge (leaf f) (spine g₀ fs) ↔ f₀ = g₀ ∧ gs = fs ++ [f] := by
  have := spine_eq_spine_iff (f₀ := f₀) (fs := gs) (g₀ := g₀) (gs := fs ++ [f])
  rwa [spine_concat] at this

theorem spine_injective (f₀ : F) : Function.Injective (spine f₀) :=
  fun _ _ h ↦ (spine_eq_spine_iff.1 h).2

/-- A spine contains the spines of the initial parts of its sequence and no other spine on its
foot. -/
theorem spine_containsOrEq_spine_iff {f₀ : F} {fs gs : List F} :
    (spine f₀ fs).ContainsOrEq (spine f₀ gs) ↔ gs <+: fs := by
  induction fs using List.reverseRecOn with
  | nil =>
    simp only [spine_nil, containsOrEq_merge, containsOrEq_leaf, containsOrEq_trace,
      spine_ne_leaf, spine_ne_trace, or_false, List.prefix_nil, spine_eq_bare_iff, true_and]
  | append_singleton fs f ih =>
    simp only [spine_concat, containsOrEq_merge, containsOrEq_leaf, spine_ne_leaf, false_or, ih,
      List.prefix_concat_iff, spine_eq_phrase_spine_iff, true_and]

theorem eq_of_spine_containsOrEq_spine {f₀ g₀ : F} {fs gs : List F}
    (h : (spine g₀ fs).ContainsOrEq (spine f₀ gs)) : f₀ = g₀ := by
  induction fs using List.reverseRecOn with
  | nil =>
    simp only [spine_nil, containsOrEq_merge, containsOrEq_leaf, containsOrEq_trace,
      spine_ne_leaf, spine_ne_trace, or_false, spine_eq_bare_iff] at h
    exact h.1
  | append_singleton fs f ih =>
    simp only [spine_concat, containsOrEq_merge, containsOrEq_leaf, spine_ne_leaf, false_or] at h
    rcases h with h | h
    · exact (spine_eq_phrase_spine_iff.1 h).1
    · exact ih h

/-- A spine beside a remnant with another foot contains the spines on its foot up to its own
size and no larger one. -/
theorem merge_spine_containsOrEq_spine_iff {f₀ g₀ : F} (h : f₀ ≠ g₀) {fs gs hs : List F} :
    (merge (spine f₀ fs) (spine g₀ hs)).ContainsOrEq (spine f₀ gs) ↔ gs <+: fs := by
  rw [containsOrEq_merge, spine_containsOrEq_spine_iff]
  refine ⟨?_, fun h ↦ .inr (.inl h)⟩
  rintro (he | h' | h')
  · obtain ⟨f, t, hf⟩ := exists_spine_eq_phrase f₀ gs
    rw [hf, merge_eq_merge_iff] at he
    rcases he with ⟨he, -⟩ | ⟨he, -⟩
    · exact absurd he.symm (spine_ne_leaf _ _ _)
    · exact absurd he.symm (spine_ne_leaf _ _ _)
  · exact h'
  · exact absurd (eq_of_spine_containsOrEq_spine h') h


/-! ### Planar objects -/

/-- The planar phrase of `f` over `t`, the feature first. -/
abbrev pphrase (f : F) (t : PlanarSyntacticObject F) : PlanarSyntacticObject F :=
  PlanarSyntacticObject.leaf f * t

/-- The planar phrase of `f` with no complement. -/
abbrev pbare (f : F) : PlanarSyntacticObject F := pphrase f PlanarSyntacticObject.trace

/-- The planar spine of a feature sequence. -/
def pspine (f₀ : F) (fs : List F) : PlanarSyntacticObject F :=
  fs.foldl (fun t f ↦ pphrase f t) (pbare f₀)

@[simp] theorem pspine_nil (f₀ : F) : pspine f₀ [] = pbare f₀ := rfl

@[simp] theorem pspine_concat (f₀ : F) (fs : List F) (f : F) :
    pspine f₀ (fs ++ [f]) = pphrase f (pspine f₀ fs) := by simp [pspine]

@[simp] theorem toSyntacticObject_pspine (f₀ : F) (fs : List F) :
    (pspine f₀ fs).toSyntacticObject = spine f₀ fs := by
  induction fs using List.reverseRecOn with
  | nil => rfl
  | append_singleton fs f ih =>
    rw [pspine_concat, spine_concat, ← ih]
    exact PlanarSyntacticObject.toSyntacticObject_merge _ _

/-- An object with two phrasal daughters, which no feature labels. -/
def IsUnlabelled (s : SyntacticObject F) : Prop := ∃ a b c d, s = merge (merge a b) (merge c d)

/-- An object with an unlabelled constituent. -/
def HasUnlabelled (s : SyntacticObject F) : Prop := ∃ u, s.ContainsOrEq u ∧ IsUnlabelled u

end Morphology.Nanosyntax
