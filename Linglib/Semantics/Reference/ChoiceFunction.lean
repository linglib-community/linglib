module

public import Linglib.Semantics.Quantification.Basic

/-!
# Choice functions

A choice function picks a member of every nonempty property. For Reinhart and for Winter an
indefinite noun phrase denotes the value of such a function rather than an existential
quantifier, and it scopes where the function variable is bound rather than where a quantifier
would raise to. Kratzer gives the function implicit arguments, skolem indices that are bound like
pronouns, so a skolemized choice function is a family `S → ChoiceFunction E`; Mirrazi adds a world
argument that an intensional operator can bind, and Owusu feeds the same situation to the
function and to the restrictor. Closing the function variable existentially gives the existential
reading, and closing it when its index or its restrictor varies with a bound variable gives the
reading on which the indefinite scopes below the binder. Stalnaker's selection function for
conditionals is a choice function over worlds at each world, which picks the world itself from
every proposition true there (`Conditional.SelectionFunction`).

## Main definitions

* `ChoiceFunction`: the choice functions over a domain, as functions from properties to
  individuals.

## Main results

* `ChoiceFunction.exists_forall_mem_apply_eq`: a choice function can pick any prescribed values
  from a family of properties, provided those from the nonempty ones are members.
* `ChoiceFunction.some_of_apply`, `ChoiceFunction.forall_apply_iff_some_iff`: a choice function
  witnesses the existential reading, and agrees with it on every predicate only when the
  restrictor has a single member.
* `ChoiceFunction.exists_apply_iff_some`, `ChoiceFunction.forall_apply_iff_every`: quantifying
  over choice functions gives the existential and universal readings on a nonempty restrictor.
* `ChoiceFunction.exists_forall_apply_iff`: a choice function whose restrictor contains a bound
  variable takes no scope relative to the binder.
* `ChoiceFunction.exists_forall_apply_iff_of_injective`, `ChoiceFunction.exists_pi_apply_iff`:
  with distinct restrictors for distinct values of the bound variable, or with the bound variable
  as the skolem index, closing the function above the binder gives the reading with the
  existential below it.

## References

* [reinhart-1997]
* [winter-1997]
* [kratzer-1998-pseudoscope]
* [owusu-2022]
* [mirrazi-2024]
* [stalnaker-1968]
-/

@[expose] public section

/-- A choice function sends every nonempty property to one of its members. -/
structure ChoiceFunction (E : Type*) where
  /-- The individual picked from a property. -/
  toFun : (E → Prop) → E
  /-- The pick of a nonempty property satisfies it. -/
  apply_of_exists' : ∀ P : E → Prop, (∃ x, P x) → P (toFun P)

namespace ChoiceFunction

variable {S E ι : Type*}

instance : FunLike (ChoiceFunction E) (E → Prop) E where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

@[ext]
theorem ext {f g : ChoiceFunction E} (h : ∀ P, f P = g P) : f = g :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_mk (f : (E → Prop) → E) (h) : ⇑(⟨f, h⟩ : ChoiceFunction E) = f :=
  rfl

theorem apply_of_exists (f : ChoiceFunction E) {P : E → Prop} (h : ∃ x, P x) : P (f P) :=
  f.apply_of_exists' P h

/-- Hilbert's `ε` is a choice function. -/
noncomputable def epsilon [Nonempty E] : ChoiceFunction E :=
  ⟨Classical.epsilon, fun _ ↦ Classical.epsilon_spec⟩

instance [Nonempty E] : Nonempty (ChoiceFunction E) :=
  ⟨epsilon⟩

/-- A choice function can pick prescribed values from a family of properties, as long as the
values picked from the nonempty ones are members. -/
theorem exists_forall_mem_apply_eq [Nonempty E] {T : Set (E → Prop)} (g : ∀ P ∈ T, E)
    (hg : ∀ (P : E → Prop) (hP : P ∈ T), (∃ x, P x) → P (g P hP)) :
    ∃ f : ChoiceFunction E, ∀ P hP, f P = g P hP := by
  classical
  refine ⟨⟨fun P ↦ if hP : P ∈ T then g P hP else epsilon P, fun P hP ↦ ?_⟩, fun P hP ↦ ?_⟩
  · split_ifs with h
    exacts [hg P h hP, epsilon.apply_of_exists hP]
  · simp [hP]

theorem exists_apply_eq {N : E → Prop} {x : E} (hx : N x) : ∃ f : ChoiceFunction E, f N = x :=
  have : Nonempty E := ⟨x⟩
  (exists_forall_mem_apply_eq (T := {N}) (fun _ _ ↦ x) fun _ h _ ↦ h ▸ hx).imp fun _ hf ↦ hf N rfl

/-! ### The existential reading

A choice function witnesses the existential reading `GQ.some` on a nonempty restrictor, but the
two analyses are not equivalent: the existential reading asserts the existence of a witness, the
choice function commits to one, and distinct choice functions commit differently. -/

open Quantifier Quantifier.GQ

/-- A choice function whose pick satisfies the predicate witnesses the existential reading. -/
theorem some_of_apply (f : ChoiceFunction E) {N VP : E → Prop} (hN : ∃ x, N x)
    (hVP : VP (f N)) : GQ.some N VP :=
  ⟨f N, f.apply_of_exists hN, hVP⟩

/-- A choice function agrees with the existential reading on every predicate exactly when its
pick is the only member of the restrictor. -/
theorem forall_apply_iff_some_iff (f : ChoiceFunction E) {N : E → Prop} (hN : ∃ x, N x) :
    (∀ VP : E → Prop, VP (f N) ↔ GQ.some N VP) ↔ ∀ x, N x → x = f N := by
  refine ⟨fun h x hx ↦ ((h (· = x)).mpr ⟨x, hx, rfl⟩).symm, fun h VP ↦
    ⟨f.some_of_apply hN, ?_⟩⟩
  rintro ⟨x, hx, hVP⟩
  rwa [h x hx] at hVP

/-- Existential quantification over choice functions is the existential reading. -/
theorem exists_apply_iff_some {N : E → Prop} (hN : ∃ x, N x) (VP : E → Prop) :
    (∃ f : ChoiceFunction E, VP (f N)) ↔ GQ.some N VP :=
  ⟨fun ⟨f, h⟩ ↦ f.some_of_apply hN h, fun ⟨_, hx, h⟩ ↦
    let ⟨f, hfx⟩ := exists_apply_eq hx; ⟨f, hfx ▸ h⟩⟩

/-- Universal quantification over choice functions is the universal reading, on a nonempty
restrictor. -/
theorem forall_apply_iff_every {N : E → Prop} (hN : ∃ x, N x) (VP : E → Prop) :
    (∀ f : ChoiceFunction E, VP (f N)) ↔ every N VP :=
  ⟨fun h _ hx ↦ let ⟨f, hfx⟩ := exists_apply_eq hx; hfx ▸ h f,
    fun h f ↦ h _ (f.apply_of_exists hN)⟩

theorem forall_apply_iff_of_not_exists {N : E → Prop} (hN : ¬ ∃ x, N x) (VP : E → Prop) :
    (∀ f : ChoiceFunction E, VP (f N)) ↔ ∀ x, VP x := by
  refine ⟨fun h x ↦ ?_, fun h f ↦ h _⟩
  have : Nonempty E := ⟨x⟩
  obtain ⟨f, hf⟩ := exists_forall_mem_apply_eq (T := {P | ¬ ∃ y, P y}) (fun _ _ ↦ x)
    fun _ hP h ↦ (hP h).elim
  simpa [hf N hN] using h f

/-! ### Scope relative to a binder -/

/-- A choice function applied to a restrictor that contains a bound variable takes no scope
relative to the binder. Since the restrictor already varies with the variable, one choice
function can be assembled from the pointwise choices. -/
theorem exists_forall_apply_iff [Nonempty E] (R : ι → E → Prop) (VP : E → Prop) :
    (∃ f : ChoiceFunction E, ∀ i, VP (f (R i))) ↔ ∀ i, ∃ f : ChoiceFunction E, VP (f (R i)) := by
  refine ⟨fun ⟨f, h⟩ i ↦ ⟨f, h i⟩, fun h ↦ ?_⟩
  choose F hF using h
  obtain ⟨f, hf⟩ := exists_forall_mem_apply_eq (T := Set.range R) (fun P hP ↦ F hP.choose P)
    fun _ _ ↦ (F _).apply_of_exists
  refine ⟨f, fun i ↦ ?_⟩
  have hi : R i ∈ Set.range R := ⟨i, rfl⟩
  rw [hf _ hi]
  simpa [hi.choose_spec] using hF hi.choose

/-- When distinct values of a bound variable give distinct nonempty restrictors, closing a choice
function above the binder gives the reading with the existential below it, even if the predicate
also contains the variable. -/
theorem exists_forall_apply_iff_of_injective [Nonempty E] {R : ι → E → Prop}
    (hR : Function.Injective R) (hN : ∀ i, ∃ x, R i x) (VP : ι → E → Prop) :
    (∃ f : ChoiceFunction E, ∀ i, VP i (f (R i))) ↔ ∀ i, GQ.some (R i) (VP i) := by
  refine ⟨fun ⟨f, h⟩ i ↦ f.some_of_apply (hN i) (h i), fun h ↦ ?_⟩
  choose x hx hVP using h
  obtain ⟨f, hf⟩ := exists_forall_mem_apply_eq (T := Set.range R) (fun _ hP ↦ x hP.choose)
    fun _ hP _ ↦ by simpa [hP.choose_spec] using hx hP.choose
  refine ⟨f, fun i ↦ ?_⟩
  have hi : R i ∈ Set.range R := ⟨i, rfl⟩
  rw [hf _ hi, hR hi.choose_spec]
  exact hVP i

/-- Closing a skolemized choice function above a binder of its index gives the reading with the
existential below the binder. -/
theorem exists_pi_apply_iff {N : S → E → Prop} (hN : ∀ s, ∃ x, N s x) (VP : S → E → Prop) :
    (∃ F : S → ChoiceFunction E, ∀ s, VP s (F s (N s))) ↔ ∀ s, GQ.some (N s) (VP s) :=
  Classical.skolem.symm.trans <| forall_congr' fun s ↦ exists_apply_iff_some (hN s) (VP s)

end ChoiceFunction

