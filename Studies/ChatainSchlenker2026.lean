module

public import Linglib.Data.Examples.ChatainSchlenker2026
public import Linglib.Logic.Trivalent.Flat
public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Semantics.Composition.WithAlternatives
public import Linglib.Semantics.Modification.Basic
public import Mathlib.Data.Fintype.Prod

/-!
# Chatain and Schlenker (2026): Local accommodation without covert operators

This file formalizes the argument that local accommodation is not the work of a covert node `A`,
Bochvar's assertion operator, but of Free Enrichment, which conjoins a contextual restriction `R`
in Strong Kleene with an elementary predicate. An operator whose meaning ignores context
accommodates at every argument of a λ-abstract or at none, so an elided clause would copy its
antecedent's choice. One enrichment can project at one argument and accommodate at another, and
can accommodate one of a trigger's two presuppositions while the other projects.

## Main statements

* `pointwise_projects_or_accommodates`: a context-free operator projects at every argument or
  accommodates at every argument (Table 1).
* `enrichment_projects_and_accommodates`, `semantic_parallelism`: one enrichment does both, and
  the clauses stay semantically parallel ((66)–(71)).
* `enrichment_by_definedness`: enrichment by definedness is `A` (§5.2).
* `partial_accommodation`, `partial_accommodation_rows`: enrichment by one presupposition of a
  trigger accommodates it alone ((34), (38), (39), §5.2.1).
* `projection_entails_accommodation`: in a knowledge-monotone context the projected reading
  entails the accommodated one (§4.1).

## Implementation notes

A trivalent predicate `P : E → W → SignType` is `0` where its presupposition fails. Free
Enrichment (62) is `Modifier.intersective` at `fun x w ↦ ofProp (R x w)`, written out below as
`ofProp (R x w) ⊓ P x w`. The composition rules (63) are not formalized, since the composition
engine's truth values are `Prop`, and clauses are composed by hand.

## TODO

* The syntactic half of the ellipsis argument needs LF trees with a silent `A` interpreted with
  three-valued truth, which the composition engine lacks.
* Intermediate accommodation (55), Homer's diagnostic (§4.2.1), and the constraint on Free
  Enrichment that (77) calls for (§5.2.2).

## References

* [chatain-schlenker-2026]
* [beaver-krahmer-2001]
* [bochvar-1938]
* [romoli-2011]
-/

@[expose] public section

namespace ChatainSchlenker2026

open SignType Trivalent

universe u

variable {E W : Type*}

/-! ### Operators and parallelism -/

/-- An operator applied pointwise that keeps defined values defined, such as `A`, negation or
their composite, either keeps the gap of every argument or fills the gap of every argument, so an
elided clause accommodates exactly when its antecedent does (Table 1). -/
theorem pointwise_projects_or_accommodates (f : SignType → SignType)
    (hf : ∀ a, a ≠ 0 → f a ≠ 0) (P : E → W → SignType) :
    (∀ x, gapExt (f ∘ P x) = gapExt (P x)) ∨ ∀ x, gapExt (f ∘ P x) = ∅ := by
  rcases eq_or_ne (f 0) 0 with h | h
  · refine .inl fun x ↦ Set.ext fun w ↦ ?_
    simp only [mem_gapExt, Function.comp_apply]
    exact ⟨fun h' ↦ by_contra fun hw ↦ hf _ hw h', fun hw ↦ hw ▸ h⟩
  · refine .inr fun x ↦ Set.eq_empty_of_forall_notMem fun w h' ↦ ?_
    simp only [mem_gapExt, Function.comp_apply] at h'
    by_cases hw : P x w = 0
    · exact h (hw ▸ h')
    · exact hf _ hw h'

/-! ### Free Enrichment -/

/-- Free Enrichment (62) is intersective modification by the restriction. -/
example (R : E → W → Prop) [∀ x, DecidablePred (R x)] (P : E → W → SignType) :
    Modifier.intersective (fun x w ↦ ofProp (R x w)) P = fun x w ↦ ofProp (R x w) ⊓ P x w :=
  rfl

/-- An enrichment trivial at `Y` and entailing the presupposition at `X` lets the presupposition
project at `Y` and accommodates it at `X`, so the antecedent and the elided clause of (26) can
share one λ-abstract and differ ((66)–(70)). -/
theorem enrichment_projects_and_accommodates (P : E → W → SignType) (R : E → W → Prop)
    [∀ x, DecidablePred (R x)] {X Y : E} (hY : ∀ w, R Y w) (hX : ∀ w, R X w → P X w ≠ 0) :
    gapExt (fun w ↦ ofProp (R Y w) ⊓ P Y w) = gapExt (P Y) ∧
      gapExt (fun w ↦ ofProp (R X w) ⊓ P X w) = ∅ := by
  simp only [gapExt_ofProp_inf]
  exact ⟨Set.inter_eq_right.2 fun w _ ↦ hY w,
    Set.eq_empty_of_forall_notMem fun w h ↦ hX w h.1 h.2⟩

/-- The antecedent is the shared λ-abstract at an alternative to the elided clause's focused
argument, so it lies in that clause's focus value and semantic parallelism holds ((71)). -/
theorem semantic_parallelism {E W : Type u} (P : E → W → SignType) (R : E → W → Prop)
    [∀ x, DecidablePred (R x)] (X Y : E) :
    (fun w ↦ -(ofProp (R Y w) ⊓ P Y w)) ∈
      ((fun x w ↦ -(ofProp (R x w) ⊓ P x w)) <$> WithAlternatives.focused X).alternatives := by
  rw [WithAlternatives.alternatives_map_focused]; exact ⟨Y, rfl⟩

/-- Enrichment by definedness is local accommodation by `A` (§5.2). -/
theorem enrichment_by_definedness (P : E → W → SignType) :
    (fun x w ↦ ofProp (P x w ≠ 0) ⊓ P x w) = fun x w ↦ ofProp (P x w = 1) :=
  funext fun _ ↦ funext fun _ ↦ ofProp_ne_zero_inf_self _

/-- Enrichment by `R` is the conjunction of `R` with the predicate in Middle Kleene as in Strong
Kleene, the paraphrases (75). -/
theorem enrichment_eq_meetMiddle (R : Prop) [Decidable R] (a : SignType) :
    ofProp R ⊓ a = meetMiddle (ofProp R) a :=
  (meetMiddle_eq_inf_of_left_ne_zero _ _ ofProp_ne_zero).symm

/-! ### Partial accommodation -/

/-- Enriching a trigger that presupposes `S ∩ T` by `S` accommodates `S` and leaves the
conditional presupposition that `S` implies `T` (§5.2.1), while `A` above the trigger leaves no
presupposition at all ((35), `Trivalent.gapExt_ofProp_eq_one`). -/
theorem partial_accommodation (S T : Set W) [DecidablePred (· ∈ S)] {f : W → SignType}
    (hf : ∀ w, f w ≠ 0) : gapExt (fun w ↦ ofProp (w ∈ S) ⊓ (S ∩ T).indicator f w) = S \ T := by
  ext w; by_cases hS : w ∈ S <;> by_cases hT : w ∈ T <;> simp [hS, hT, hf]

/-- A trigger with two presuppositions, *notice* (36) or *return the book to the library* (38),
over the values of its presuppositions and its assertion. -/
def trigger (w : Bool × Bool × Bool) : SignType := if w.1 ∧ w.2.1 then ofProp w.2.2 else 0

/-- The presuppositions of `trigger` under the names the examples give them. -/
def presuppositions : List (String × (Bool × Bool × Bool → Bool)) :=
  [("alive", (·.1)), ("possession", (·.1)), ("unpopular", (·.2.1)), ("ownership", (·.2.1))]

/-- Enriching the trigger by the presupposition an example's continuation denies leaves it
undefined only where that presupposition holds and the other fails ((34), (38), (39)). -/
theorem partial_accommodation_rows : ∀ row ∈ Examples.all,
    ∀ q ∈ row.parse? "accommodated" presuppositions,
    ∀ r ∈ row.parse? "projected" presuppositions,
      ∀ w, ofProp (q w) ⊓ trigger w = 0 ↔ q w ∧ ¬ r w := by
  decide +kernel

/-! ### Projection and accommodation -/

/-- In a knowledge-monotone context `C`, the reading on which the presupposition projects entails
the reading on which it is accommodated locally (§4.1). -/
theorem projection_entails_accommodation {C : SignType → SignType}
    (hC : ∀ a b, toFlat a ≤ toFlat b → toFlat (C a) ≤ toFlat (C b)) {a : SignType}
    (h : C a = 1) : C (ofProp (a = 1)) = 1 := by
  have := hC _ _ (toFlat_le_toFlat_ofProp_eq_one a)
  rw [h] at this
  exact (eq_of_toFlat_le this (by decide)).symm

/-- Ann's sentence in (26) entails its locally accommodated reading. -/
example {a : SignType} (h : -a = 1) : -ofProp (a = 1) = 1 :=
  projection_entails_accommodation (fun _ _ ↦ toFlat_neg_mono) h

end ChatainSchlenker2026
