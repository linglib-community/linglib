/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.MeasureTheory.Constructions.List
public import Linglib.Core.Probability.ConditionalProbability

/-!
# Kiegeland et al. (2026): On the Proper Treatment of Units in Surprisal Theory

[kiegeland-etal-2026] separate the unit of analysis from the alphabet of the language model. A
unit parser maps each symbol string to a string of units, and the language model over units is
the pushforward of the one over symbols along the parse. To compute it with a language model over
symbols, each unit is spelled as its underlying string followed by a separator, and the unit model
is pushed forward along the spelling. The spelling of a unit string is a prefix of the spelling of
another exactly when the unit string is a prefix of it (`encode_isPrefix_encode_iff`, the paper's
prefix identity), so the unit model's conditional prefix probabilities are the spelled model's
conditional prefix probabilities of spellings (`cond_map_encode`).

The identity depends on the separator closing each unit. Placed at the onset instead, a unit's
spelling is a prefix of the spelling of a longer unit sharing its underlying prefix, and the
prefix identity fails (`not_forall_encodeOnset_isPrefix_iff`). In the paper's two-unit example
the unit model and the completion spelling give the shorter unit prefix probability one half, the
onset spelling one (`map_parse_setOf_prefix`, `map_encode_setOf_prefix`,
`map_encodeOnset_setOf_prefix`). The
separator also carries probability of its own: a unit's conditional probability is that of its
underlying string times that of the separator after it (`cond_map_encode_singleton`), so summing
symbol surprisals over a unit's spelling omits the boundary.

## Implementation notes

* The separator is `none` in `Option Ξ`, and a unit's underlying string is given by an injective
  spelling function; the paper takes units to be strings over `Ξ`.
* The paper computes the pushforward with finite-state transducers under a regularity assumption
  on the unit inventory; the identities here hold for any unit language model, so for the
  pushforward along any deterministic unit parser, and any injective spelling.
* The paper's aggregation over regions of interest and its reading-time analyses are not
  formalized.

## References

* [kiegeland-etal-2026]
-/

@[expose] public section

namespace KiegelandEtAl2026

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

variable {U Ξ : Type*} (ξ : U → List Ξ)

/-- The spelling of a unit string: each unit's underlying string followed by the separator
`none`. -/
def encode (us : List U) : List (Option Ξ) := us.flatMap fun u ↦ (ξ u).map some ++ [none]

/-- The onset spelling: the separator before each unit's underlying string. -/
def encodeOnset (us : List U) : List (Option Ξ) := us.flatMap fun u ↦ none :: (ξ u).map some

@[simp] theorem encode_nil : encode ξ [] = [] := rfl

theorem encode_cons (u : U) (us : List U) :
    encode ξ (u :: us) = (ξ u).map some ++ none :: encode ξ us := by
  simp [encode]

theorem encode_append (us vs : List U) : encode ξ (us ++ vs) = encode ξ us ++ encode ξ vs :=
  List.flatMap_append

private theorem eq_and_isPrefix_of_block {xs ys : List Ξ} {r r' : List (Option Ξ)}
    (h : xs.map some ++ none :: r <+: ys.map some ++ none :: r') : xs = ys ∧ r <+: r' := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact ⟨rfl, (List.cons_prefix_cons.1 h).2⟩
    | cons y ys => simp at h
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons_append, List.cons_prefix_cons, Option.some.injEq] at h
      obtain ⟨rfl, h⟩ := h
      exact (ih h).imp_left (congrArg _)

variable {ξ}

/-- The prefix identity: under the completion convention, the spelling of a unit string is a
prefix of the spelling of another exactly when the unit string is a prefix of it. -/
theorem encode_isPrefix_encode_iff (hξ : Function.Injective ξ) {us vs : List U} :
    encode ξ us <+: encode ξ vs ↔ us <+: vs := by
  refine ⟨fun h ↦ ?_, fun ⟨t, ht⟩ ↦ ⟨encode ξ t, by rw [← encode_append, ht]⟩⟩
  induction us generalizing vs with
  | nil => exact List.nil_prefix
  | cons u us ih =>
    cases vs with
    | nil => simp [encode] at h
    | cons v vs =>
      rw [encode_cons, encode_cons] at h
      obtain ⟨huv, h⟩ := eq_and_isPrefix_of_block h
      exact List.cons_prefix_cons.2 ⟨hξ huv, ih h⟩

/-- The unit strings whose spelling extends the spelling of `us` are those extending `us`. -/
theorem encode_preimage_setOf_prefix (hξ : Function.Injective ξ) (us : List U) :
    encode ξ ⁻¹' {l | encode ξ us <+: l} = {l | us <+: l} := by
  ext l
  exact encode_isPrefix_encode_iff hξ

variable (ν : Measure (List U))

/-- The unit model's conditional prefix probability of a continuation is the spelled model's
conditional prefix probability of its spelling. -/
theorem cond_map_encode (hξ : Function.Injective ξ) (cs us : List U) :
    (ν.map (encode ξ))[{l | encode ξ cs ++ encode ξ us <+: l} | {l | encode ξ cs <+: l}] =
      ν[{l | cs ++ us <+: l} | {l | cs <+: l}] := by
  rw [cond_map .of_discrete .of_discrete, Measure.map_apply .of_discrete .of_discrete,
    ← encode_append, encode_preimage_setOf_prefix hξ, encode_preimage_setOf_prefix hξ]

/-- A unit's conditional probability is the conditional probability of its underlying string
times that of the separator after it. -/
theorem cond_map_encode_singleton (hξ : Function.Injective ξ) (cs : List U) (u : U) :
    ν[{l | cs ++ [u] <+: l} | {l | cs <+: l}] =
      (ν.map (encode ξ))[{l | encode ξ cs ++ (ξ u).map some <+: l} | {l | encode ξ cs <+: l}] *
        (ν.map (encode ξ))[{l | encode ξ cs ++ (ξ u).map some ++ [none] <+: l} |
          {l | encode ξ cs ++ (ξ u).map some <+: l}] := by
  rw [← cond_map_encode ν hξ, show encode ξ [u] = (ξ u).map some ++ [none] by simp [encode],
    ← List.append_assoc]
  exact (cond_mul_cond_of_subset .of_discrete .of_discrete
    (fun _ ↦ (List.prefix_append _ _).trans) fun _ ↦ (List.prefix_append _ _).trans).symm

/-! ### The two-unit example -/

/-- The paper's two units: `false` is spelled `a` and `true` is spelled `ab`. -/
def spell : Bool → List Char
  | false => ['a']
  | true => ['a', 'b']

/-- The parse of the source strings `a` and `ab` into the two units. -/
def parse (s : List Char) : List Bool :=
  if s = ['a'] then [false] else if s = ['a', 'b'] then [true] else []

/-- The source model: `a` and `ab` with probability one half each. -/
noncomputable def source : Measure (List Char) :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac ['a'] + (2⁻¹ : ℝ≥0∞) • Measure.dirac ['a', 'b']

/-- Under the onset convention the prefix identity fails, although the spelling is injective:
the onset spelling of `a` is a prefix of that of `ab`. -/
theorem not_forall_encodeOnset_isPrefix_iff :
    ¬ ∀ us vs : List Bool, encodeOnset spell us <+: encodeOnset spell vs ↔ us <+: vs :=
  fun h ↦ absurd ((h [false] [true]).1 (by decide)) (by decide)

theorem map_parse_setOf_prefix : source.map parse {l | [false] <+: l} = 2⁻¹ := by
  simp [source, parse, Measure.map_apply .of_discrete .of_discrete,
    Measure.dirac_apply' _ MeasurableSet.of_discrete]

theorem map_encode_setOf_prefix :
    (source.map parse).map (encode spell) {l | encode spell [false] <+: l} = 2⁻¹ := by
  rw [Measure.map_apply .of_discrete .of_discrete,
    encode_preimage_setOf_prefix (fun b b' h ↦ by cases b <;> cases b' <;> simp_all [spell]),
    map_parse_setOf_prefix]

theorem map_encodeOnset_setOf_prefix :
    (source.map parse).map (encodeOnset spell) {l | encodeOnset spell [false] <+: l} = 1 := by
  simp [source, parse, encodeOnset, spell, Measure.map_apply .of_discrete .of_discrete,
    Measure.dirac_apply' _ MeasurableSet.of_discrete, ENNReal.inv_two_add_inv_two]

end KiegelandEtAl2026
