module

public import Studies.Hawkins1994
public import Linglib.Data.Experiments.Sheehan2017b

/-!
# Sheehan (2017b): The Final-over-Final Condition and Processing

The final-over-final condition bans a head-final phrase over a head-initial one. Read left to
right, Hawkins's Early Immediate Constituents prefers the consistent orders of a head over a phrase
to the disharmonic ones, and the initial-over-final order to the final-over-initial one,
[each exactly when the lower head has a complement](##harmony_iff_fofc) (`ex6_to_ex9`), while the
plain ratio of constituents to words [ties the two disharmonic orders](##icToWord_disharmonic).
Polar particles and complementizers show the skew without the preference, and the model ranks the
four orders consistently with their counts [only for a lower head without a
complement](##polarityComplementizer_unexplained), where they coincide (`Hawkins1994.binary_zero`).

## Implementation notes

* The trees of (6) to (9) enter through Hawkins's Mother Node Construction (`Hawkins1994.ics`).
  The chapter's English words replace those of Hawkins's (5.3) and (5.4).
* (10) is stated for the scores. The step to cross-linguistic frequency is Hawkins's prediction
  that orders are as frequent as their scores rank them, which `polarityComplementizer_unexplained`
  states as the consistency of the ranking at a complement length with the counts.
* In Table 5.2 the complementizer is the upper head and the particle the lower one, so type C,
  an initial complementizer over a final particle, is the inverse of the final-over-final order.
* Note 1 reports that Hawkins's later account could derive the asymmetry only with a preference
  for attaching to the mother. That account reports the plain ratio of constituents to words
  (its (5.11)), which [ties the two disharmonic orders](##icToWord_disharmonic).
* Sheehan's three chapters of the book are lettered here by title (adverbs, processing, the
  head-final filter).

## TODO

* Cecchetto's account, on which a backward dependency is phrase-bound, and Sheehan's objections
  to it need a model of Agree and selection.
* The articles counterexample prints no counts, and Table 5.1 is not reproducible from WALS
  (14 and 41 languages against the printed 12 and 38).
* §§5.5–5.6, the linearization parameter set by the parser and the analogy with Onset
  Maximization, are prose.

## References

* [sheehan-2017b]
* [hawkins-1994]
* [hawkins-2004]
-/

@[expose] public section

namespace Sheehan2017b

open Hawkins1994 PhraseStructure

/-! ### Examples (6) to (9) -/

section Examples

open PhraseStructure.Tree (node terminal)

/-- (6): *go to school*. -/
def ex6 : PhraseStructure.Tree Cat String :=
  node .V [terminal .V "go", node .P [terminal .P "to", node .N [terminal .N "school"]]]

/-- (7): *school to go*. -/
def ex7 : PhraseStructure.Tree Cat String :=
  node .V [node .P [node .N [terminal .N "school"], terminal .P "to"], terminal .V "go"]

/-- (8): *go the shops to*. -/
def ex8 : PhraseStructure.Tree Cat String :=
  node .V [terminal .V "go",
    node .P [node .N [terminal .Det "the", terminal .N "shops"], terminal .P "to"]]

/-- (9): *to the shops go*. -/
def ex9 : PhraseStructure.Tree Cat String :=
  node .V [node .P [terminal .P "to", node .N [terminal .Det "the", terminal .N "shops"]],
    terminal .V "go"]

/-- (6)–(9), pp. 81–82: the verb phrases of (6) and (7) are consistent and score 100%; (8), the
verb before a postpositional phrase, scores 75%, and (9), a prepositional phrase before the
verb, 42%. -/
theorem ex6_to_ex9 :
    ics ex6 = some (binary .headInitial .headInitial 1) ∧
      ics ex7 = some (binary .headFinal .headFinal 1) ∧
      ics ex8 = some (binary .headInitial .headFinal 2) ∧
      ics ex9 = some (binary .headFinal .headInitial 2) ∧
      leftToRight (binary .headInitial .headInitial 1) = 1 ∧
      leftToRight (binary .headFinal .headFinal 1) = 1 ∧
      leftToRight (binary .headInitial .headFinal 2) = 3 / 4 ∧
      leftToRight (binary .headFinal .headInitial 2) = 5 / 12 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    leftToRight_binary_consistent _ _, leftToRight_binary_consistent _ _, ?_, ?_⟩
  · rw [leftToRight_initial_final]; norm_num
  · rw [leftToRight_final_initial]; norm_num

end Examples

/-! ### Harmony and the final-over-final condition, (10) -/

private theorem gap (m : ℕ) :
    leftToRight (binary .headInitial .headFinal m) -
      leftToRight (binary .headFinal .headInitial m) = m / (2 * (m + 1)) := by
  rw [leftToRight_initial_final, leftToRight_final_initial]
  field_simp
  ring

/-- (10), p. 83: Early Immediate Constituents prefers the consistent orders of a head over a
phrase to the initial-over-final order, and that order to the final-over-initial one, each
exactly when the lower head has a complement; the second preference is `m / (2 (m + 1))` for a
complement of `m` words. -/
theorem harmony_iff_fofc (m : ℕ) :
    (leftToRight (binary .headInitial .headFinal m) <
        leftToRight (binary .headInitial .headInitial m) ↔ 0 < m) ∧
      (leftToRight (binary .headFinal .headInitial m) <
        leftToRight (binary .headInitial .headFinal m) ↔ 0 < m) ∧
      leftToRight (binary .headInitial .headFinal m) -
        leftToRight (binary .headFinal .headInitial m) = m / (2 * (m + 1)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [leftToRight_initial_final, leftToRight_final_initial,
      leftToRight_binary_consistent]
  · have h := leftToRight_binary_lt hm .headInitial
    exact ⟨iff_of_true h.2.1 hm, iff_of_true h.1 hm, gap m⟩

-- pp. 83, 86: the skew grows with the weight of the complement
theorem gap_strictMono :
    StrictMono fun m : ℕ ↦ leftToRight (binary .headInitial .headFinal m) -
      leftToRight (binary .headFinal .headInitial m) := by
  intro a b hab
  simp only [gap]
  have hab : (a : ℚ) < b := by exact_mod_cast hab
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

-- note 1, p. 352: the plain ratio ties the two disharmonic orders
theorem icToWord_disharmonic (m : ℕ) :
    icToWord (binary .headFinal .headInitial m) = icToWord (binary .headInitial .headFinal m) := by
  rw [← icToWord_mirror, ← binary_swap]
  rfl

/-! ### Polar question particles and complementizers, Table 5.2 -/

/-- The position a head direction gives a head. -/
def position : HeadDirection → Position
  | .headInitial => .initial
  | .headFinal => .final

/-- The languages of Table 5.2 with the complementizer in direction `top` over the particle in
direction `bottom`. -/
def languages (top bottom : HeadDirection) : ℕ :=
  (polarityComplementizer (position bottom) (position top)).languages

/-- Table 5.2, p. 92: the final-over-initial order of complementizer and particle is rarer than
its mirror image, which is commoner than the consistent order with both heads initial. Early
Immediate Constituents ranks the four orders consistently with these counts only at a lower head
without a complement, where all four orders score alike. -/
theorem polarityComplementizer_unexplained :
    languages .headFinal .headInitial < languages .headInitial .headFinal ∧
      languages .headInitial .headInitial < languages .headInitial .headFinal ∧
      ∀ m, (∀ x y : HeadDirection × HeadDirection,
          leftToRight (binary x.1 x.2 m) < leftToRight (binary y.1 y.2 m) →
            languages x.1 x.2 ≤ languages y.1 y.2) ↔ m = 0 := by
  refine ⟨by decide, by decide, fun m ↦ ⟨fun h ↦ ?_, ?_⟩⟩
  · by_contra hm
    have hlt := (leftToRight_binary_lt (Nat.pos_of_ne_zero hm) .headInitial).2.1
    exact absurd (h (.headInitial, .headFinal) (.headInitial, .headInitial) hlt) (by decide)
  · rintro rfl x y hxy
    rw [binary_zero, binary_zero] at hxy
    exact absurd hxy (lt_irrefl _)

end Sheehan2017b
