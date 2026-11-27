module

public import Mathlib.Data.Set.Function
public import Linglib.Semantics.Quantifier.Basic

/-!
# Choice functions

A choice function sends every nonempty set to one of its members; its value at the empty set is
unconstrained. Analyses of the exceptional scope of indefinites let an indefinite denote the pick
of a choice function from its restrictor and scope where the function variable is closed, and
give the function further arguments (a world, a situation, the value of a bound variable), which
makes it a family `S → ChoiceFunction E`. The values of a choice function at distinct sets are
independent (`ChoiceFunction.skolem`), so closing the variable existentially over a nonempty
restrictor gives the existential reading, and closing it above a binder gives the reading with
the existential below the binder when the restrictors differ with the bound variable. At an
empty restrictor existential closure holds whenever anything satisfies the scope
(`ChoiceFunction.exists_apply_iff`).

## Implementation notes

The function is total, as `Classical.epsilon` is, so its pick is a term and the statements about
a nonempty restrictor carry that as a hypothesis.

## References

* [reinhart-1997]
* [winter-1997]
* [kratzer-1998-pseudoscope]
* [owusu-2022]
* [mirrazi-2024]
* [stalnaker-1968]
-/

@[expose] public section

/-- A choice function sends every nonempty set to one of its members. -/
structure ChoiceFunction (E : Type*) where
  /-- The individual picked from a set. -/
  toFun : Set E → E
  /-- The pick of a nonempty set is a member of it. -/
  apply_mem' : ∀ ⦃A : Set E⦄, A.Nonempty → toFun A ∈ A

namespace ChoiceFunction

open Quantifier Function

variable {S E ι : Type*} {A B : Set E} {x : E}

instance : FunLike (ChoiceFunction E) (Set E) E where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

@[ext]
theorem ext {f g : ChoiceFunction E} (h : ∀ A, f A = g A) : f = g :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_mk (f : Set E → E) (h) : ⇑(⟨f, h⟩ : ChoiceFunction E) = f :=
  rfl

theorem apply_mem (f : ChoiceFunction E) (h : A.Nonempty) : f A ∈ A :=
  f.apply_mem' h

/-- Hilbert's `ε` is a choice function. -/
noncomputable def epsilon [Nonempty E] : ChoiceFunction E :=
  ⟨fun A ↦ Classical.epsilon (· ∈ A), fun _ h ↦ Classical.epsilon_spec h⟩

instance [Nonempty E] : Nonempty (ChoiceFunction E) :=
  ⟨epsilon⟩

theorem nonempty_iff : Nonempty (ChoiceFunction E) ↔ Nonempty E :=
  ⟨fun ⟨f⟩ ↦ ⟨f ∅⟩, fun _ ↦ inferInstance⟩

/-! ### Independence of the values -/

/-- The values of a choice function at distinct sets are independent: if every set has a choice
function whose pick from it meets a condition, one choice function meets them all. -/
theorem skolem {p : Set E → E → Prop} :
    (∀ A, ∃ f : ChoiceFunction E, p A (f A)) ↔ ∃ f : ChoiceFunction E, ∀ A, p A (f A) := by
  refine ⟨fun h ↦ ?_, fun ⟨f, hf⟩ A ↦ ⟨f, hf A⟩⟩
  choose F hF using h
  exact ⟨⟨fun A ↦ F A A, fun A hA ↦ (F A).apply_mem hA⟩, hF⟩

theorem exists_apply_eq (hx : x ∈ A) : ∃ f : ChoiceFunction E, f A = x := by
  classical
  have : Nonempty E := ⟨x⟩
  exact ⟨⟨fun B ↦ if B = A then x else epsilon B, fun B hB ↦ by
    split_ifs with h
    exacts [h ▸ hx, epsilon.apply_mem hB]⟩, ite_eq_left rfl⟩

/-- The pick from the empty set is unconstrained. -/
theorem exists_apply_empty_eq (x : E) : ∃ f : ChoiceFunction E, f ∅ = x := by
  classical
  have : Nonempty E := ⟨x⟩
  exact ⟨⟨fun B ↦ if B = ∅ then x else epsilon B, fun B hB ↦ by
    rw [ite_eq_right hB.ne_empty]; exact epsilon.apply_mem hB⟩, ite_eq_left rfl⟩

/-- A choice function can take prescribed values on a family of sets, as long as the values at
the nonempty ones are members. -/
theorem exists_eqOn {T : Set (Set E)} (g : Set E → E) (hg : ∀ A ∈ T, A.Nonempty → g A ∈ A) :
    ∃ f : ChoiceFunction E, Set.EqOn f g T := by
  refine (skolem (p := fun A y ↦ A ∈ T → y = g A)).1 fun A ↦ ?_
  rcases A.eq_empty_or_nonempty with rfl | hA
  · exact (exists_apply_empty_eq (g ∅)).imp fun _ h _ ↦ h
  · by_cases hT : A ∈ T
    · exact (exists_apply_eq (hg A hT hA)).imp fun _ h _ ↦ h
    · have : Nonempty E := hA.to_type
      exact ⟨epsilon, fun h ↦ (hT h).elim⟩

/-! ### Closure at one set -/

section One

/-- Existential closure over a nonempty restrictor is existential quantification over it. -/
theorem exists_apply_iff_of_nonempty (hA : A.Nonempty) (p : E → Prop) :
    (∃ f : ChoiceFunction E, p (f A)) ↔ ∃ x ∈ A, p x :=
  ⟨fun ⟨f, h⟩ ↦ ⟨_, f.apply_mem hA, h⟩, fun ⟨_, hx, h⟩ ↦
    let ⟨f, hf⟩ := exists_apply_eq hx; ⟨f, hf ▸ h⟩⟩

/-- Universal closure over a nonempty restrictor is universal quantification over it. -/
theorem forall_apply_iff_of_nonempty (hA : A.Nonempty) (p : E → Prop) :
    (∀ f : ChoiceFunction E, p (f A)) ↔ ∀ x ∈ A, p x :=
  ⟨fun h _ hx ↦ let ⟨f, hf⟩ := exists_apply_eq hx; hf ▸ h f, fun h f ↦ h _ (f.apply_mem hA)⟩

variable {p : E → Prop}

theorem exists_apply_empty_iff : (∃ f : ChoiceFunction E, p (f ∅)) ↔ ∃ x, p x :=
  ⟨fun ⟨_, h⟩ ↦ ⟨_, h⟩, fun ⟨x, h⟩ ↦ let ⟨f, hf⟩ := exists_apply_empty_eq x; ⟨f, hf ▸ h⟩⟩

theorem forall_apply_empty_iff : (∀ f : ChoiceFunction E, p (f ∅)) ↔ ∀ x, p x :=
  ⟨fun h x ↦ let ⟨f, hf⟩ := exists_apply_empty_eq x; hf ▸ h f, fun h _ ↦ h _⟩

/-- Existential closure with no assumption on the restrictor: over the empty set it holds as soon
as anything satisfies the scope. -/
theorem exists_apply_iff :
    (∃ f : ChoiceFunction E, p (f A)) ↔ (∃ x ∈ A, p x) ∨ A = ∅ ∧ ∃ x, p x := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp [exists_apply_empty_iff]
  · simp [exists_apply_iff_of_nonempty hA p, hA.ne_empty]

/-- Universal closure with no assumption on the restrictor: over the empty set it requires
everything to satisfy the scope. -/
theorem forall_apply_iff :
    (∀ f : ChoiceFunction E, p (f A)) ↔ (∀ x ∈ A, p x) ∧ (A = ∅ → ∀ x, p x) := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp [forall_apply_empty_iff]
  · simp [forall_apply_iff_of_nonempty hA p, hA.ne_empty]

/-- Existential closure over a nonempty restrictor is the existential reading. -/
theorem exists_apply_mem_iff (hA : A.Nonempty) :
    (∃ f : ChoiceFunction E, f A ∈ B) ↔ Det.some A B :=
  exists_apply_iff_of_nonempty hA (· ∈ B)

/-- Universal closure over a nonempty restrictor is the universal reading. -/
theorem forall_apply_mem_iff (hA : A.Nonempty) :
    (∀ f : ChoiceFunction E, f A ∈ B) ↔ Det.every A B :=
  forall_apply_iff_of_nonempty hA (· ∈ B)

/-- A choice function whose pick is in the scope witnesses the existential reading. -/
theorem some_of_apply_mem (f : ChoiceFunction E) (hA : A.Nonempty) (h : f A ∈ B) :
    Det.some A B :=
  ⟨f A, f.apply_mem hA, h⟩

/-- A choice function agrees with the existential reading on every scope exactly when its pick
is the only member of the restrictor. -/
theorem forall_apply_mem_iff_some_iff (f : ChoiceFunction E) (hA : A.Nonempty) :
    (∀ B : Set E, f A ∈ B ↔ Det.some A B) ↔ A = {f A} := by
  refine ⟨fun h ↦ Set.eq_singleton_iff_unique_mem.2 ⟨f.apply_mem hA, fun x hx ↦ ?_⟩,
    fun h B ↦ ⟨f.some_of_apply_mem hA, ?_⟩⟩
  · exact ((h {x}).2 ⟨x, hx, rfl⟩).symm
  · rintro ⟨x, hx, hB⟩
    rw [h] at hx
    exact hx ▸ hB

/-- Existential closure of two choice functions, over two nonempty restrictors, is existential
quantification over each. -/
theorem exists₂_apply_iff {A' : Set E} (hA : A.Nonempty) (hA' : A'.Nonempty)
    (p : E → E → Prop) :
    (∃ f₁ f₂ : ChoiceFunction E, p (f₁ A) (f₂ A')) ↔ ∃ x ∈ A, ∃ y ∈ A', p x y :=
  (exists_apply_iff_of_nonempty hA _).trans <| exists_congr fun x ↦ and_congr_right fun _ ↦
    exists_apply_iff_of_nonempty hA' (p x)

end One

/-! ### Scope relative to a binder -/

/-- A choice function closed above a binder scopes below it when the condition on its pick
depends on the bound variable only through the restrictor. -/
theorem exists_forall_apply_iff [Nonempty E] {R : ι → Set E} {p : ι → E → Prop}
    (hp : p.FactorsThrough R) :
    (∃ f : ChoiceFunction E, ∀ i, p i (f (R i))) ↔ ∀ i, ∃ f : ChoiceFunction E, p i (f (R i)) := by
  refine ⟨fun ⟨f, h⟩ i ↦ ⟨f, h i⟩, fun h ↦ ?_⟩
  refine (skolem (p := fun A y ↦ ∀ i, R i = A → p i y).1 fun A ↦ ?_).imp fun f hf i ↦ hf _ i rfl
  by_cases hA : ∃ i, R i = A
  · obtain ⟨i, rfl⟩ := hA
    exact (h i).imp fun f hf j hj ↦ hp hj ▸ hf
  · exact ⟨epsilon, fun i hi ↦ (hA ⟨i, hi⟩).elim⟩

/-- When distinct values of a bound variable give distinct nonempty restrictors, closing a choice
function above the binder gives the reading with the existential below it. -/
theorem exists_forall_apply_iff_of_injective [Nonempty E] {R : ι → Set E} (hR : Injective R)
    (hne : ∀ i, (R i).Nonempty) (p : ι → E → Prop) :
    (∃ f : ChoiceFunction E, ∀ i, p i (f (R i))) ↔ ∀ i, ∃ x ∈ R i, p i x :=
  (exists_forall_apply_iff (hR.factorsThrough _)).trans <|
    forall_congr' fun i ↦ exists_apply_iff_of_nonempty (hne i) (p i)

/-- Closing a family of choice functions above a binder of its index gives the reading with the
existential below the binder. -/
theorem exists_pi_apply_iff {N : S → Set E} (hN : ∀ s, (N s).Nonempty) (p : S → E → Prop) :
    (∃ F : S → ChoiceFunction E, ∀ s, p s (F s (N s))) ↔ ∀ s, ∃ x ∈ N s, p s x :=
  Classical.skolem.symm.trans <| forall_congr' fun s ↦ exists_apply_iff_of_nonempty (hN s) (p s)

/-- Universal closure of a family of choice functions is universal quantification over each
restrictor. -/
theorem forall_pi_apply_iff {N : S → Set E} (hN : ∀ s, (N s).Nonempty) (p : S → E → Prop) :
    (∀ F : S → ChoiceFunction E, ∀ s, p s (F s (N s))) ↔ ∀ s, ∀ x ∈ N s, p s x :=
  ⟨fun h s _ hx ↦ let ⟨f, hf⟩ := exists_apply_eq hx; hf ▸ h (fun _ ↦ f) s,
    fun h F s ↦ h s _ ((F s).apply_mem (hN s))⟩

end ChoiceFunction
