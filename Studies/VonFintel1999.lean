module

public import Linglib.Semantics.Presupposition.Strawson
public import Linglib.Semantics.Attitudes.Preference.BestWorlds
public import Linglib.Semantics.Conditionals.Horizon
public import Linglib.Semantics.Degree.Superlative
public import Linglib.Semantics.Focus.Particles
public import Linglib.Semantics.Tense.Since
public import Linglib.Semantics.Conditionals.Restrictor
public import Linglib.Data.Examples.VonFintel1999

/-!
# von Fintel (1999): NPI licensing, Strawson entailment, and context dependency

Von Fintel defends the Fauconnier–Ladusaw theory of negative polarity licensing against four
licensers that are not downward entailing, focus *only*, the adversative attitudes, superlatives
and conditional antecedents: each is downward entailing once the inference is checked only where
the presuppositions hold. The notion is in `Semantics/Presupposition/Strawson.lean` and the
operators live with their owners, Iatridou's temporal *since* among them; this file carries the
paper's arguments around them, and its licensing judgments are the rows of
`Data/Examples/VonFintel1999.json`.

*Want* and *glad* are upward entailing in the Strawson sense, on the best-worlds semantics and on
the set comparison alike. On the best-worlds semantics wanting and believing `p` makes one glad
that `p`, which the Honda Civic scenario refutes for the set comparison. The set-comparison
*sorry* is not Strawson downward entailing, which is why the paper keeps the best-worlds one.
Of two entries for propositional *only*, the one that admits the prejacent's entailments as
alternatives is Strawson downward entailing and the one that bars them assesses no downward
inference at all; a conditional antecedent under a genuine ordering source is not downward
entailing; and a superlative inside a definite description is not even Strawson downward
entailing.

## TODO

* The shifted-context readings of §3.4 and the expansion of the modal horizon in §4.3 need
  von Fintel's later context-change operator; the static horizon semantics of (81)–(83) is
  `Conditional.horizonCounterfactual`.

## References

* [von-fintel-1999]
* [kadmon-landman-1993]
* [rooth-1992]
* [kratzer-1986]
* [von-fintel-2000]
-/

@[expose] public section

namespace VonFintel1999

open Presupposition Modality Conditional Desire.BestWorlds

variable {W ι : Type*}

/-! ### *Want* and *glad* -/

section Attitudes

variable (dox rel : W → Set W) (g : W → Set (Set W)) (p : Set W)

/-- `X` is better than `Y` when every `X`-world is strictly better than every `Y`-world under the
ordering source `A`. -/
def Better (A : Set (Set W)) (X Y : Set W) : Prop := ∀ x ∈ X, ∀ y ∈ Y, x <[A] y

open Classical in
/-- The set-comparison *glad* (52) has the presupposition of the best-worlds one and asserts that
the belief worlds are strictly better than every relevant non-`p` world. -/
noncomputable def gladBetter : W → Trivalent :=
  Trivalent.condEvent (· ∈ (Trivalent.gapExt (glad dox rel g p))ᶜ)
    (fun w ↦ Better (g w) (dox w) (rel w \ p))

/-- The set-comparison *glad* is still Strawson upward entailing in its complement (§3.3). -/
theorem isStrawsonUE_gladBetter : IsStrawsonUE (gladBetter dox rel g) :=
  .of_monotone (a := fun p w ↦ Better (g w) (dox w) (rel w \ p))
    (fun _ _ h _ hw a ha b hb ↦ hw a ha b ⟨hb.1, fun hp ↦ hb.2 (h hp)⟩)
    fun _ _ h ↦ by simp_all [gladBetter]

/-- On the best-worlds *glad*, *a wants p and believes p* entails *a is glad that p*, the
inference [kadmon-landman-1993] draw, when the modal base contains the belief worlds. -/
theorem glad_eq_true_of_want_eq_true {w : W} (hd : dox w ⊆ rel w) (hb : dox w ⊆ p)
    (hw : want rel g p w = .true) : glad dox rel g p w = .true := by
  simp [glad, hd, hb, hw]

/-- The Honda Civic scenario refutes that inference on the set-comparison *glad*. World `0` is
the actual one, where the Civic bought is a lemon, `1` is where a good Civic is bought, and `2`
where none is; the subject believes `0`, wants the good Civic, and is not glad that a Civic was
bought, since `0` is no better than `2`. -/
theorem not_gladBetter_of_want :
    ∃ (dox rel : Fin 3 → Set (Fin 3)) (g : Fin 3 → Set (Set (Fin 3))) (p : Set (Fin 3))
      (w : Fin 3), dox w ⊆ p ∧ want rel g p w = .true ∧ gladBetter dox rel g p w = .false := by
  refine ⟨fun _ ↦ {0}, fun _ ↦ Set.univ, fun _ ↦ {{1}}, {0, 1}, 0, by simp, ?_, ?_⟩
  · refine want_eq_true_iff.2 ⟨⟨⟨0, by simp⟩, ⟨2, by simp⟩⟩, ?_⟩
    simp only [Want, Set.subset_def, Preorder.mem_minimals_iff, Preorder.ofCriteria_le_iff,
      Set.mem_singleton_iff, forall_eq, Set.mem_univ, Set.mem_insert_iff]
    decide
  · simp only [gladBetter, Trivalent.condEvent_eq_false_iff]
    refine ⟨by simpa [glad] using ⟨⟨0, by simp⟩, ⟨2, by simp⟩⟩, ?_⟩
    simp only [Better, Preorder.ofCriteria_lt_iff, Preorder.ofCriteria_le_iff,
      Set.mem_singleton_iff, forall_eq, Set.mem_sdiff, Set.mem_univ, Set.mem_insert_iff]
    decide

open Classical in
/-- The set-comparison *sorry* (54) has the presupposition of *glad* and asserts that every
relevant non-`p` world is strictly better than every belief world. -/
noncomputable def regretBetter : W → Trivalent :=
  Trivalent.condEvent (· ∈ (Trivalent.gapExt (glad dox rel g p))ᶜ)
    (fun w ↦ Better (g w) (rel w \ p) (dox w))

/-- The set-comparison *sorry* is Strawson upward entailing in its complement. -/
theorem isStrawsonUE_regretBetter : IsStrawsonUE (regretBetter dox rel g) :=
  .of_monotone (a := fun p w ↦ Better (g w) (rel w \ p) (dox w))
    (fun _ _ h _ hw b hb a ha ↦ hw b ⟨hb.1, fun hp ↦ hb.2 (h hp)⟩ a ha)
    fun _ _ h ↦ by simp_all [regretBetter]

/-- The set-comparison *sorry* is not Strawson downward entailing, so it would not license; the
paper keeps the best-worlds `regret`. World `2` is the preferred one; the subject believes `0`
and is sorry about `{0, 1}` but not about `{0}`, since `1` is no better than `0`. -/
theorem not_isStrawsonDE_regretBetter :
    ¬ IsStrawsonDE (regretBetter (fun _ : Fin 3 ↦ {0}) (fun _ ↦ Set.univ) (fun _ ↦ {{2}})) :=
  fun h ↦ by
    have := h (p := {0}) (q := {0, 1}) (by simp) 0 (by
        simp only [regretBetter, Trivalent.condEvent_eq_true_iff]
        refine ⟨by simpa [glad] using ⟨⟨0, by simp⟩, ⟨2, by simp⟩⟩, ?_⟩
        simp only [Better, Preorder.ofCriteria_lt_iff, Preorder.ofCriteria_le_iff,
          Set.mem_singleton_iff, forall_eq, Set.mem_sdiff, Set.mem_univ, Set.mem_insert_iff]
        decide)
      (by simpa [regretBetter, glad] using ⟨⟨0, by simp⟩, ⟨1, by simp⟩⟩)
    simp only [regretBetter, Trivalent.condEvent_eq_true_iff, Better, Preorder.ofCriteria_lt_iff,
      Preorder.ofCriteria_le_iff, Set.mem_singleton_iff, forall_eq, Set.mem_sdiff, Set.mem_univ,
      true_and] at this
    exact absurd (this.2 1 (by decide)) (by decide)

end Attitudes

/-! ### Propositional *only*, §3.4

Of the two entries for propositional *only* von Fintel compares, (68a) presupposes the prejacent
and asserts that every true alternative is entailed by it; it is the substrate's
`Focus.only (· ⊆ ·)` (`Focus.only_subset_eq`), Strawson downward entailing
with the alternatives held fixed (`Focus.isStrawsonDE_only_subset`). (68b) bars the
prejacent's entailments from the alternatives and asserts that every true alternative is the
prejacent. -/

section Only

open Focus

variable (C : Set (Set W)) (p : Set W)

open Classical in
/-- *Only* in the entry (68b) presupposes the prejacent and that no alternative is entailed by
it, and asserts that every true alternative is the prejacent. -/
noncomputable def only68b : W → Trivalent :=
  Trivalent.condEvent (fun w ↦ w ∈ p ∧ ¬ ∃ r ∈ C, p ⊆ r) (· ∈ atMost (· = ·) C id p)

open Classical in
/-- With (68b), no downward inference within one set of alternatives can be assessed (p. 134). -/
theorem only68b_eq_undefined {q : Set W} (hp : p ∈ C) (hqp : q ⊆ p) (w : W) :
    only68b C q w = .undefined :=
  Trivalent.condEvent_eq_undefined_iff.2 fun h ↦ h.2 ⟨p, hp, hqp⟩

end Only

/-! ### Conditional antecedents under an ordering source -/

/-- With a genuine ordering source, the antecedent of Kratzer's conditional necessity is not
downward entailing (73). -/
theorem not_antitone_humanNecessity_restrict :
    ¬ Antitone fun α : Set (Fin 2) ↦
      {w | {0} ∈ humanNecessity (Background.restrict (fun _ ↦ ∅) α) (fun _ ↦ {{0}}) w} :=
  fun h ↦ by
    have := @h {1} .univ (Set.subset_univ _) 0
    simp only [humanNecessity_eq_principal_of_finite, Filter.mem_principal, Set.subset_def,
      bestWorlds, Preorder.mem_minimals_iff,
      Background.mem_accessibleWorlds, Background.restrict, Preorder.ofCriteria_le_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
      Set.mem_empty_iff_false, false_imp_iff, implies_true, and_true,
      Set.mem_ofPred_eq] at this
    revert this
    decide

/-! ### The superlative inside a definite description -/

section Description

variable {D : Type*} [Preorder D] (μ : ι → D) (C : W → Set ι) (d : D)

open Classical in
/-- *The μ-est C exceeds d* presupposes a superlative individual and asserts that every such
individual exceeds `d`. -/
noncomputable def theSuperlativeExceeds : W → Trivalent :=
  Trivalent.condEvent (fun w ↦ ∃ a, trivalentSuperlative μ C a w = .true)
    (fun w ↦ ∀ a, trivalentSuperlative μ C a w = .true → d < μ a)

/-- The definite-description superlative is not Strawson downward entailing (80). -/
theorem not_isStrawsonDE_theSuperlativeExceeds :
    ¬ IsStrawsonDE (theSuperlativeExceeds (W := Unit) (fun b : Bool ↦ if b then 3 else 5) · 4) :=
  fun h ↦ by
    have := @h (fun _ ↦ {true}) (fun _ ↦ Set.univ) (fun _ _ _ ↦ trivial) ()
    simp only [theSuperlativeExceeds, trivalentSuperlative_eq_true_iff,
      Trivalent.condEvent_eq_true_iff, Trivalent.condEvent_eq_undefined_iff, ne_eq, not_not,
      Set.mem_singleton_iff, Set.mem_univ] at this
    revert this
    decide

end Description

end VonFintel1999
