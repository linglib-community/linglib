module

public import Mathlib.Data.Set.Lattice.Indexed
public import Linglib.Semantics.Presupposition.LocalContext

/-!
# Barker (2022): Composing local contexts

A continuized expression takes its local context as its first argument, and continuized function
application (`Continuized.app`) hands the daughter evaluated second a context containing the
first, so local contexts are built in the composition of truth conditions. A presupposition is
satisfied when the `commitments` of the context, its upper bound over saturations less its lower
bound (`Answer`), entail it. A right conjunct's context [entails the left
conjunct](##commitments_right_conjunct), a left conjunct's has [the commitments of the initial
context](##commitments_left_conjunct), and for a sentence-final gap the commitments are [the
local context of transparency](##isLocalContext_commitments).

## Implementation notes

* `Continuized.app` takes the operation that combines the two daughters, so type-driven
  application in either direction (`Continuized.fwd`, `Continuized.bwd`) and application relative
  to an assignment are instances, and predicate abstraction is `Continuized.map`. Flip is the
  three `_lift` lemmas, which make the meanings of the form `lift a` closed under the rules.
* The entry of a presupposition trigger is a partial function whose domain condition mentions the
  commitments of its local context. Partial functions are not formalized: a trigger is an arbitrary
  continuized meaning, a derivation theorem identifies the context it is applied to, and
  satisfaction is `commitments κ ⊆ p`. The domain condition of bounded *might* is the set
  `bounded`.
* The initial context is the continuation `(c ∩ ·)` of a context set `c`.

## TODO

* For a gap that is not sentence-final the local context of transparency is included in the
  commitments (`IsLocalContext.subset_commitments`), and the inclusion is strict for a conjunct
  followed by a disjunct (`isLocalContext_and_or`, `commitments_and_or`); the paper's comparison of
  the two is for the propositional case without this restriction.
* Presuppositions in the scope of quantifiers.

## References

* [barker-2022]
* [schlenker-2009]
* [mandelkern-2019]
* [veltman-1996]
* [heim-1992]
* [barker-2002]
-/

@[expose] public section

namespace Barker2022

open Set Presupposition

universe u

variable {W E α β γ R : Type u}

/-! ### Semantic commitments -/

/-- An answer type is the type of propositions or a type of functions into an answer type. The
upper bound of a context is the least proposition that every saturation of its arguments entails,
and the lower bound the greatest proposition that entails every saturation. -/
class Answer (W : outParam (Type u)) (R : Type u) where
  /-- The least upper bound of the saturations. -/
  upper : R → Set W
  /-- The greatest lower bound of the saturations. -/
  lower : R → Set W

open Answer

instance : Answer W (Set W) := ⟨id, id⟩

instance [Answer W R] : Answer W (α → R) :=
  ⟨fun f ↦ ⋃ x, upper (f x), fun f ↦ ⋂ x, lower (f x)⟩

/-- The commitments of a context are the worlds that not every saturation of its arguments
excludes and not every saturation includes. -/
def commitments [Answer W R] (κ : R) : Set W := upper κ \ lower κ

@[simp] theorem upper_set (p : Set W) : upper p = p := rfl

@[simp] theorem lower_set (p : Set W) : lower p = p := rfl

theorem upper_fun [Answer W R] (f : α → R) : upper f = ⋃ x, upper (f x) := rfl

theorem lower_fun [Answer W R] (f : α → R) : lower f = ⋂ x, lower (f x) := rfl

section Skeleton

variable [Answer W R] {δ ε : Type u}

theorem upper_comp {g : δ → α} (hg : g.Surjective) (κ : α → R) :
    upper (fun x ↦ κ (g x)) = upper κ :=
  hg.iUnion_comp fun a ↦ upper (κ a)

theorem lower_comp {g : δ → α} (hg : g.Surjective) (κ : α → R) :
    lower (fun x ↦ κ (g x)) = lower κ :=
  hg.iInter_comp fun a ↦ lower (κ a)

-- Arguments that a context only passes on, through a map onto its domain, leave its
-- commitments unchanged.
theorem commitments_comp {g : δ → α} (hg : g.Surjective) (κ : α → R) :
    commitments (fun x ↦ κ (g x)) = commitments κ :=
  congrArg₂ (· \ ·) (upper_comp hg κ) (lower_comp hg κ)

theorem upper_comp₂ {g : δ → ε → α} (hg : ∀ a, ∃ x y, g x y = a) (κ : α → R) :
    upper (fun x y ↦ κ (g x y)) = upper κ := by
  ext w
  simp only [upper_fun, mem_iUnion]
  exact ⟨fun ⟨x, y, h⟩ ↦ ⟨_, h⟩, fun ⟨a, h⟩ ↦ let ⟨x, y, e⟩ := hg a; ⟨x, y, e ▸ h⟩⟩

theorem lower_comp₂ {g : δ → ε → α} (hg : ∀ a, ∃ x y, g x y = a) (κ : α → R) :
    lower (fun x y ↦ κ (g x y)) = lower κ := by
  ext w
  simp only [lower_fun, mem_iInter]
  exact ⟨fun h a ↦ let ⟨x, y, e⟩ := hg a; e ▸ h x y, fun h x y ↦ h _⟩

theorem commitments_comp₂ {g : δ → ε → α} (hg : ∀ a, ∃ x y, g x y = a) (κ : α → R) :
    commitments (fun x y ↦ κ (g x y)) = commitments κ :=
  congrArg₂ (· \ ·) (upper_comp₂ hg κ) (lower_comp₂ hg κ)

-- The context of a functor whose argument is still to come has the commitments of the context
-- of the whole.
theorem commitments_fwd [Nonempty α] (κ : β → R) :
    commitments (fun (f : α → β) a ↦ κ (f a)) = commitments κ :=
  commitments_comp₂ (fun b ↦ ⟨fun _ ↦ b, Classical.arbitrary α, rfl⟩) κ

-- The context of an argument whose functor is still to come has the commitments of the context
-- of the whole.
theorem commitments_bwd [Nonempty α] (κ : β → R) :
    commitments (fun a (f : α → β) ↦ κ (f a)) = commitments κ :=
  commitments_comp₂ (fun b ↦ ⟨Classical.arbitrary α, fun _ ↦ b, rfl⟩) κ

-- The context of a functor both of whose arguments are still to come has the commitments of the
-- context of the whole, as for *both* in *both eyes opened*.
theorem commitments_fwd_fwd [Nonempty α] [Nonempty β] (κ : γ → R) :
    commitments (fun (f : α → β → γ) a b ↦ κ (f a b)) = commitments κ :=
  (commitments_fwd fun (f : β → γ) b ↦ κ (f b)).trans (commitments_fwd κ)

end Skeleton

/-! ### The logical connectives -/

section Connectives

variable (p : Set W)

private theorem iUnion_id : ⋃ q : Set W, q = univ :=
  eq_univ_of_univ_subset (subset_iUnion (fun q : Set W ↦ q) univ)

private theorem iInter_id : ⋂ q : Set W, q = ∅ :=
  eq_empty_of_subset_empty (iInter_subset (fun q : Set W ↦ q) ∅)

theorem upper_and : upper (fun q ↦ p ∩ q) = p := by
  simp only [upper_fun, upper_set]
  rw [← inter_iUnion, iUnion_id, inter_univ]

theorem lower_and : lower (fun q ↦ p ∩ q) = ∅ := by
  simp only [lower_fun, lower_set]
  rw [← inter_iInter, iInter_id, inter_empty]

-- After *p and*, or in an initial context `p`, it is safe to suppose `p`.
theorem commitments_and : commitments (fun q ↦ p ∩ q) = p := by
  simp [commitments, upper_and, lower_and]

theorem upper_or : upper (fun q ↦ p ∪ q) = univ := by
  simp only [upper_fun, upper_set]
  rw [← union_iUnion, iUnion_id, union_univ]

theorem lower_or : lower (fun q ↦ p ∪ q) = p := by
  simp only [lower_fun, lower_set]
  rw [← union_iInter, iInter_id, union_empty]

-- After *p or* it is safe to suppose that `p` is false.
theorem commitments_or : commitments (fun q ↦ p ∪ q) = pᶜ := by
  simp [commitments, upper_or, lower_or, compl_eq_univ_sdiff]

-- In the consequent of the material conditional it is safe to suppose the antecedent.
theorem commitments_imp : commitments (fun q ↦ p ⇨ q) = p := by
  simpa [himp_eq, union_comm] using commitments_or pᶜ

-- Negation adds nothing to the context of its prejacent.
theorem commitments_not : commitments (fun q : Set W ↦ qᶜ) = univ :=
  (commitments_comp compl_surjective fun q : Set W ↦ q).trans <| by
    simp [commitments, upper_fun, lower_fun, iUnion_id, iInter_id]

end Connectives

/-! ### Commitments and transparency -/

/-- For a sentence-final gap of a truth-functional environment, the commitments are the least
transparent restriction. -/
theorem isLocalContext_commitments {κ : Set W → Set W} (hκ : IsTruthFunctional κ) :
    IsLocalContext univ {κ} (commitments κ) := by
  convert isLocalContext_of_isTruthFunctional (C := univ) (env := {κ}) (by simpa using hκ) using 1
  ext w
  simp only [commitments, upper_fun, lower_fun, upper_set, lower_set, mem_sdiff, mem_iUnion,
    mem_iInter, not_forall, univ_inter, mem_singleton_iff, exists_eq_left, mem_ofPred_eq, DependsAt]
  refine ⟨fun ⟨⟨q, hq⟩, q', hq'⟩ h ↦ ?_, fun h ↦ ?_⟩
  · by_cases hw : w ∈ q <;> by_cases hw' : w ∈ q'
    · exact hq' ((hκ.mem_iff_of_mem hw').2 ((hκ.mem_iff_of_mem hw).1 hq))
    · exact hq' ((hκ.mem_iff_of_notMem hw').2 (h.1 ((hκ.mem_iff_of_mem hw).1 hq)))
    · exact hq' ((hκ.mem_iff_of_mem hw').2 (h.2 ((hκ.mem_iff_of_notMem hw).1 hq)))
    · exact hq' ((hκ.mem_iff_of_notMem hw').2 ((hκ.mem_iff_of_notMem hw).1 hq))
  · by_cases hu : w ∈ κ univ
    · exact ⟨⟨_, hu⟩, ∅, fun h0 ↦ h ⟨fun _ ↦ h0, fun _ ↦ hu⟩⟩
    · exact ⟨⟨∅, by_contra fun h0 ↦ h ⟨fun hu' ↦ (hu hu').elim, fun h0' ↦ (h0 h0').elim⟩⟩, _, hu⟩

/-- For truth-functional environments, the least transparent restriction of a gap is included in
the commitments of its context. -/
theorem IsLocalContext.subset_commitments {κ : Set W → α → Set W}
    (hκ : ∀ a, IsTruthFunctional (κ · a)) {x : Set W}
    (hx : IsLocalContext univ (range fun a q ↦ κ q a) x) : x ⊆ commitments κ := by
  rw [hx.unique (isLocalContext_of_isTruthFunctional (by rintro _ ⟨a, rfl⟩; exact hκ a))]
  rintro w ⟨-, _, ⟨a, rfl⟩, hdep⟩
  simp only [commitments, upper_fun, lower_fun, upper_set, lower_set, mem_sdiff, mem_iUnion,
    mem_iInter, not_forall]
  by_cases hu : w ∈ κ univ a
  · exact ⟨⟨_, a, hu⟩, ∅, a, fun h0 ↦ hdep ⟨fun _ ↦ h0, fun _ ↦ hu⟩⟩
  · exact ⟨⟨∅, a, by_contra fun h0 ↦ hdep ⟨fun hu' ↦ (hu hu').elim, fun h0' ↦ (h0 h0').elim⟩⟩,
      _, a, hu⟩

-- In *(p and _) or c*, the least transparent restriction of the gap is `p`.
theorem isLocalContext_and_or (p : Set W) :
    IsLocalContext univ (range fun (c q : Set W) ↦ p ∩ q ∪ c) p := by
  convert isLocalContext_of_isTruthFunctional (C := univ)
    (env := range fun (c q : Set W) ↦ p ∩ q ∪ c) ?_ using 1
  · ext w
    simp only [univ_inter, mem_range, exists_exists_eq_and, DependsAt, mem_ofPred_eq, mem_union,
      mem_inter_iff, mem_univ, and_true, mem_empty_iff_false, and_false, false_or]
    exact ⟨fun h ↦ ⟨∅, by simp [h]⟩, fun ⟨c, h⟩ ↦ by_contra fun hp ↦ h (by simp [hp])⟩
  · rintro _ ⟨c, rfl⟩ w d d' h
    simp [h]

-- In *(p and _) or c*, the commitments of the context of the gap are trivial.
theorem commitments_and_or (p : Set W) :
    commitments (fun q c : Set W ↦ p ∩ q ∪ c) = univ := by
  ext w
  simp only [commitments, upper_fun, lower_fun, upper_set, lower_set, mem_sdiff, mem_iUnion,
    mem_iInter, not_forall, mem_univ, iff_true]
  exact ⟨⟨∅, univ, by simp⟩, ∅, ∅, by simp⟩

/-! ### Continuized meanings -/

/-- A continuized meaning of type `α` maps its local context, a function from a value of type `α`
to an answer of any answer type, to an answer. -/
def Continuized (W α : Type u) : Type (u + 1) := ∀ (R : Type u) [Answer W R], (α → R) → R

namespace Continuized

/-- The continuized lexical item, which applies its context to its value. -/
def lift (a : α) : Continuized W α := fun _ _ κ ↦ κ a

/-- Continuized function application, evaluating `b` and then `c`, for daughters whose values
combine by `g`. The context of `c` contains `b`, and the context of `b` only the context of the
whole. -/
def app (g : α → β → γ) (b : Continuized W α) (c : Continuized W β) : Continuized W γ :=
  fun R _ κ ↦ c R (b (β → R) fun x y ↦ κ (g x y))

/-- Symmetric continuized function application, in which the context of each daughter contains
the other. -/
def symApp (g : α → β → γ) (b : Continuized W α) (c : Continuized W β) : Continuized W γ :=
  fun R _ κ ↦ b R fun x ↦ c R fun y ↦ κ (g x y)

/-- A unary rule, such as predicate abstraction, with operation `h` on values. -/
def map (h : α → β) (b : Continuized W α) : Continuized W β := fun R _ κ ↦ b R fun x ↦ κ (h x)

/-- Application of a functor to an argument on its right. -/
abbrev fwd (f : Continuized W (α → β)) (a : Continuized W α) : Continuized W β :=
  app (fun f a ↦ f a) f a

/-- Application of a functor to an argument on its left. -/
abbrev bwd (a : Continuized W α) (f : Continuized W (α → β)) : Continuized W β :=
  app (fun a f ↦ f a) a f

@[simp] theorem app_lift (g : α → β → γ) (a : α) (b : β) :
    app g (lift a : Continuized W α) (lift b) = lift (g a b) := rfl

@[simp] theorem symApp_lift (g : α → β → γ) (a : α) (b : β) :
    symApp g (lift a : Continuized W α) (lift b) = lift (g a b) := rfl

@[simp] theorem map_lift (h : α → β) (a : α) : map h (lift a : Continuized W α) = lift (h a) := rfl

-- Simulation: a lifted proposition applied to the empty context is that proposition.
theorem lift_id (p : Set W) : lift p (Set W) id = p := rfl

end Continuized

open Continuized

/-! ### Conjunction -/

/-- Conjunction, taking the right conjunct first. -/
def conj (q p : Set W) : Set W := p ∩ q

section Conjunction

variable [Answer W R] (rain : Set W) (ann : E) (t : Continuized W (E → Set W))

-- In *it rained and Ann [knows it rained]*, the verb phrase is applied to a context that
-- contains the left conjunct.
theorem trigger_right_conjunct (κ : Set W → R) :
    bwd (lift rain) (fwd (lift conj) (bwd (lift ann) t)) R κ = t _ fun v ↦ κ (rain ∩ v ann) := rfl

/-- The commitments of the context of a verb phrase in a right conjunct, in the initial context
`c`, entail the left conjunct. -/
theorem commitments_right_conjunct (c : Set W) :
    commitments (fun v : E → Set W ↦ c ∩ (rain ∩ v ann)) = c ∩ rain := by
  rw [commitments_comp (g := fun v : E → Set W ↦ v ann) (fun q ↦ ⟨fun _ ↦ q, rfl⟩)
    (fun q ↦ c ∩ (rain ∩ q))]
  simp_rw [← inter_assoc]
  exact commitments_and _

-- In *Ann [knows it rained] and it rained*, the verb phrase is applied to a context that
-- awaits the conjunction and its right conjunct.
theorem trigger_left_conjunct (κ : Set W → R) :
    bwd (bwd (lift ann) t) (fwd (lift conj) (lift rain)) R κ =
      t _ (fun v f ↦ κ (f (v ann))) (conj rain) := rfl

/-- The context of a verb phrase in a left conjunct has the commitments of the initial context. -/
theorem commitments_left_conjunct (κ : Set W → R) :
    commitments (fun (v : E → Set W) (f : Set W → Set W) ↦ κ (f (v ann))) = commitments κ :=
  commitments_comp₂ (fun q ↦ ⟨fun _ ↦ q, id, rfl⟩) κ

-- Under symmetric application the context of a verb phrase in a left conjunct contains the
-- right conjunct.
theorem trigger_left_conjunct_symApp (κ : Set W → R) :
    symApp (fun a f ↦ f a) (symApp (fun a f ↦ f a) (lift ann) t)
        (symApp (fun f a ↦ f a) (lift conj) (lift rain)) R κ =
      t _ fun v ↦ κ (v ann ∩ rain) := rfl

end Conjunction

/-! ### Epistemic modality -/

section Might

variable (c rain : Set W)

/-- *Might* as a test: true everywhere if the prejacent is consistent with the commitments of the
local context, and false everywhere otherwise. -/
def mightTest : Continuized W (Set W → Set W) :=
  fun _ _ κ ↦ κ fun p ↦ {_w | (commitments κ ∩ p).Nonempty}

-- In *not rain and [might] rain*, the modal is applied to a context that contains the left
-- conjunct.
theorem modal_right_conjunct [Answer W R] (t : Continuized W (Set W → Set W)) (κ : Set W → R) :
    bwd (lift rainᶜ) (fwd (lift conj) (fwd t (lift rain))) R κ =
      t _ (fun f q ↦ κ (rainᶜ ∩ f q)) rain := rfl

private theorem commitments_modal_right_conjunct :
    commitments (fun (f : Set W → Set W) q ↦ c ∩ (rainᶜ ∩ f q)) = c ∩ rainᶜ := by
  rw [commitments_fwd fun q ↦ c ∩ (rainᶜ ∩ q)]
  simp_rw [← inter_assoc]
  exact commitments_and _

/-- *It isn't raining, but it might be raining* is a contradiction in every initial context. -/
theorem not_rain_and_mightTest_rain :
    bwd (lift rainᶜ) (fwd (lift conj) (fwd mightTest (lift rain))) (Set W) (c ∩ ·) = ∅ := by
  have h : commitments (fun (f : Set W → Set W) q ↦ c ∩ (rainᶜ ∩ f q)) ∩ rain = ∅ := by
    rw [commitments_modal_right_conjunct, inter_assoc, compl_inter_self, inter_empty]
  change c ∩ (rainᶜ ∩ {_w | (commitments (fun (f : Set W → Set W) q ↦ c ∩ (rainᶜ ∩ f q)) ∩
    rain).Nonempty}) = ∅
  simp [h]

-- *It might be raining, but it isn't raining* is true at the worlds of the initial context
-- without rain, if the initial context is consistent with rain.
theorem mightTest_rain_and_not_rain (h : (c ∩ rain).Nonempty) :
    bwd (fwd mightTest (lift rain)) (fwd (lift conj) (lift rainᶜ)) (Set W) (c ∩ ·) = c \ rain := by
  have hc : commitments (fun (f : Set W → Set W) q (g : Set W → Set W) ↦ c ∩ g (f q)) = c :=
    (commitments_fwd fun q (g : Set W → Set W) ↦ c ∩ g q).trans
      ((commitments_bwd fun q ↦ c ∩ q).trans (commitments_and c))
  change c ∩ ({_w | (commitments (fun (f : Set W → Set W) q (g : Set W → Set W) ↦
    c ∩ g (f q)) ∩ rain).Nonempty} ∩ rainᶜ) = c \ rain
  simp [hc, h, sdiff_eq]

/-- The domain condition of bounded *might*: if the evaluation world satisfies the commitments of
the local context, so do its epistemic alternatives. -/
def bounded (dox : W → Set W) [Answer W R] (κ : R) : Set W :=
  {w | w ∈ commitments κ → dox w ⊆ commitments κ}

-- With bounded *might*, *it isn't raining, but it might be raining* is false wherever the
-- modal is defined.
theorem not_rain_and_might_rain_of_bounded (dox : W → Set W) {w : W}
    (hw : w ∈ bounded dox fun (f : Set W → Set W) q ↦ c ∩ (rainᶜ ∩ f q)) :
    w ∉ c ∩ (rainᶜ ∩ {w | (dox w ∩ rain).Nonempty}) := by
  rintro ⟨hc, hr, w', hd, hw'⟩
  rw [bounded, commitments_modal_right_conjunct] at hw
  exact (hw ⟨hc, hr⟩ hd).2 hw'

end Might

/-! ### Attitude verbs -/

section Attitudes

variable (want : Set W → E → Set W) (dox : E → Set W)

/-- *Wants* applies its continuized complement to the context of the subject's beliefs. -/
def wants (p : Continuized W (Set W)) : Continuized W (E → Set W) :=
  fun _ _ κ ↦ κ fun x ↦ want (p (Set W) fun q ↦ q ∩ dox x) x

-- In *wants Bill [to stop smoking]*, the embedded verb phrase is applied to the context of
-- the subject's beliefs.
theorem wants_bwd [Answer W R] (bill : E) (t : Continuized W (E → Set W)) (κ : (E → Set W) → R) :
    wants want dox (bwd (lift bill) t) R κ =
      κ fun x ↦ want (t (Set W) fun v ↦ v bill ∩ dox x) x := rfl

-- The commitments of the context of the embedded verb phrase are the subject's beliefs.
theorem commitments_wants (bill x : E) :
    commitments (fun v : E → Set W ↦ v bill ∩ dox x) = dox x := by
  rw [commitments_comp (g := fun v : E → Set W ↦ v bill) (fun q ↦ ⟨fun _ ↦ q, rfl⟩)
    (fun q ↦ q ∩ dox x)]
  simp_rw [inter_comm _ (dox x)]
  exact commitments_and _

end Attitudes

/-! ### A trigger evaluated before its arguments -/

-- In *[both] eyes opened*, the determiner is applied to a context that contains neither of its
-- arguments.
theorem trigger_fwd_fwd [Answer W R] (t : Continuized W (α → β → γ)) (a : α) (b : β) (κ : γ → R) :
    fwd (fwd t (lift a)) (lift b) R κ = t _ (fun f x y ↦ κ (f x y)) a b := rfl

end Barker2022
