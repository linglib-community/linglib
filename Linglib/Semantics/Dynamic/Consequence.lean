module

public import Linglib.Core.Order.Closure
public import Linglib.Semantics.Dynamic.Update
public import Mathlib.Dynamics.FixedPoints.Defs
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Order.BoundedOrder.Lattice
public import Mathlib.Tactic.TFAE

/-!
# Consequence in dynamic semantics

A dynamic meaning is an update of information states, and a state accepts a sentence when
updating it with the sentence changes nothing, that is, when the state is a fixed point of the
update. A text updates a state sentence by sentence. [veltman-1996] distinguishes three
consequence relations between the premises of an argument and its conclusion: updating the
minimal state with the premises yields a state that accepts the conclusion (his validity₁,
`EntailsFrom ⊤`), updating any state does (validity₂, `Entails`), or every state that accepts
each premise accepts the conclusion (validity₃, `PreservesAcceptance`), which is the shape of
[yalcin-2007]'s informational consequence.

An update is additive when it meets its input with the result of updating the minimal state, so
that a static content fixes its dynamic meaning. The additive updates are exactly those
satisfying Veltman's four constraints, Strengthening, Monotony, Idempotence and Persistence,
which read in the reversed order make the update a principal closure operator. For additive
updates the three consequence relations coincide, each saying that the contents of the premises
jointly entail the content of the conclusion. In general they come apart: acceptance
preservation is monotone in the premises and entailment is monotone on the left, while
entailment from a fixed state is neither, but inserting a conclusion that it draws into the
premises changes nothing, which gives Sequential Monotony and Sequential Cut.

On sets of possibilities the additive updates are the classical ones of
`Semantics/Dynamic/Update.lean`, the static updates `CCP.up`, and entailment between static
updates is inclusion of their contents. An update with an effect, such as a partial update, is a
Kleisli arrow, and its extension along the monad's bind is an update of the kind treated here: a
state accepts the arrow exactly when the arrow returns it unchanged.

## Main definitions

* `DynamicSemantics.text`: the update of a state with a list of sentences, from the left.
* `DynamicSemantics.EntailsFrom`, `DynamicSemantics.Entails`,
  `DynamicSemantics.PreservesAcceptance`: the three consequence relations, with the scoped
  notation `ψs ⊩₁ φ`, `ψs ⊩₂ φ` and `ψs ⊩₃ φ`.
* `DynamicSemantics.IsAdditive`: the update meets its input with a fixed content.

## Main results

* `DynamicSemantics.isAdditive_iff`: additivity is Strengthening, Monotony, Idempotence and
  Persistence together.
* `DynamicSemantics.tfae_entails`: for additive updates the three consequence relations
  coincide.
* `DynamicSemantics.EntailsFrom.insert_iff`: Sequential Monotony and Sequential Cut.
* `DynamicSemantics.entailsFrom_append_self`: under Idempotence entailment is reflexive.
* `DynamicSemantics.isFixedPt_text_iff`: along updates that never add possibilities, a state
  accepts a text exactly when it accepts each of its sentences.
* `DynamicSemantics.CCP.isAdditive_iff_isClassical`, `DynamicSemantics.CCP.entails_up_iff`: on
  sets of possibilities the additive updates are the classical ones, and entailment between
  static updates is inclusion.
* `DynamicSemantics.Update.entails_image_test_iff`: a relational update entails a test exactly
  when its outputs satisfy the test's condition.
* `DynamicSemantics.isFixedPt_bind_pure_iff`: acceptance of a Kleisli arrow.

## Implementation notes

States are ordered by inclusion, as for `DynamicSemantics.CCP` and
`DynamicSemantics.OrderedInformationState`: a more informed state lies lower, the minimal state is
`⊤`, and Strengthening says that an update never adds possibilities. Veltman orients the order the
other way, with the minimal state `0` at the bottom and the sum of two states their join, and the
content is the same; on `Set` the reversed orientation would make `⊥` the absurd state `∅` rather
than the minimal one. Acceptance is `Function.IsFixedPt`, and a sentence is identified with its
update.

## References

* [F. Veltman, *Defaults in Update Semantics*][veltman-1996]
* [S. Yalcin, *Epistemic Modals*][yalcin-2007]
-/

@[expose] public section

namespace DynamicSemantics

open Function OrderDual

variable {α : Type*}

/-! ### Texts -/

/-- The update of `σ` with a text, `σ[ψ₁]⋯[ψₙ]`, applying the sentences from the left. -/
def text (ψs : List (α → α)) (σ : α) : α := ψs.foldl (fun σ ψ ↦ ψ σ) σ

@[simp] theorem text_nil (σ : α) : text [] σ = σ := rfl

@[simp] theorem text_cons (ψ : α → α) (ψs : List (α → α)) (σ : α) :
    text (ψ :: ψs) σ = text ψs (ψ σ) := rfl

@[simp] theorem text_append (ψs χs : List (α → α)) (σ : α) :
    text (ψs ++ χs) σ = text χs (text ψs σ) :=
  List.foldl_append ..

/-! ### Consequence -/

section Consequence

/-- `ψs` entails `φ` from `σ` when updating `σ` with `ψs` yields a state that accepts `φ`.
Entailment from the minimal state is Veltman's validity₁. -/
def EntailsFrom (σ : α) (ψs : List (α → α)) (φ : α → α) : Prop := IsFixedPt φ (text ψs σ)

/-- `ψs` entails `φ` when updating any state with `ψs` yields a state that accepts `φ`, Veltman's
validity₂. -/
def Entails (ψs : List (α → α)) (φ : α → α) : Prop := ∀ σ, EntailsFrom σ ψs φ

/-- Every state that accepts each of `ψs` accepts `φ`, Veltman's validity₃. -/
def PreservesAcceptance (ψs : List (α → α)) (φ : α → α) : Prop :=
  ∀ σ, (∀ ψ ∈ ψs, IsFixedPt ψ σ) → IsFixedPt φ σ

@[inherit_doc EntailsFrom]
scoped notation:50 ψs:51 " ⊩₁ " φ:51 => EntailsFrom ⊤ ψs φ

@[inherit_doc Entails]
scoped notation:50 ψs:51 " ⊩₂ " φ:51 => Entails ψs φ

@[inherit_doc PreservesAcceptance]
scoped notation:50 ψs:51 " ⊩₃ " φ:51 => PreservesAcceptance ψs φ

variable {σ : α} {ψs χs : List (α → α)} {φ f : α → α}

theorem Entails.entailsFrom (h : Entails ψs φ) (σ : α) : EntailsFrom σ ψs φ := h σ

theorem entails_singleton_iff : Entails [f] φ ↔ φ ∘ f = f :=
  ⟨fun h ↦ funext h, fun h σ ↦ congrFun h σ⟩

/-- Entailment between single premises is transitive. -/
theorem Entails.trans {g : α → α} (h₁ : Entails [f] g) (h₂ : Entails [g] φ) : Entails [f] φ :=
  fun σ ↦ show φ (f σ) = f σ by
    have e₁ : g (f σ) = f σ := h₁ σ
    rw [← e₁]
    exact h₂ (f σ)

theorem preservesAcceptance_iff :
    PreservesAcceptance ψs φ ↔ (⋂ ψ ∈ ψs, fixedPoints ψ) ⊆ fixedPoints φ := by
  simp only [PreservesAcceptance, Set.subset_def, Set.mem_iInter₂, mem_fixedPoints]

theorem PreservesAcceptance.mono (h : PreservesAcceptance ψs φ) (hsub : ψs ⊆ χs) :
    PreservesAcceptance χs φ :=
  fun σ hσ ↦ h σ fun ψ hψ ↦ hσ ψ (hsub hψ)

theorem Entails.append_left (h : Entails ψs φ) (χs : List (α → α)) : Entails (χs ++ ψs) φ :=
  fun σ ↦ by rw [EntailsFrom, text_append]; exact h _

/-- Inserting a conclusion drawn from `σ` right after its premises changes nothing. From right to
left this is Sequential Monotony, and from left to right Sequential Cut. -/
theorem EntailsFrom.insert_iff (h : EntailsFrom σ ψs φ) {θs : List (α → α)} {χ : α → α} :
    EntailsFrom σ (ψs ++ φ :: θs) χ ↔ EntailsFrom σ (ψs ++ θs) χ := by
  simp only [EntailsFrom, text_append, text_cons, h.eq]

/-- Under Idempotence entailment is reflexive: a sentence follows from any premises ending in it. -/
theorem entailsFrom_append_self (hφ : ∀ σ, IsFixedPt φ (φ σ)) : EntailsFrom σ (ψs ++ [φ]) φ := by
  simpa [EntailsFrom] using hφ _

end Consequence

/-! ### Texts of eliminative updates -/

section Eliminative

variable [PartialOrder α] {ψs : List (α → α)}

theorem text_le (h : ∀ ψ ∈ ψs, ∀ σ, ψ σ ≤ σ) (σ : α) : text ψs σ ≤ σ := by
  induction ψs generalizing σ with
  | nil => exact le_rfl
  | cons ψ ψs ih =>
    exact (ih (fun χ hχ ↦ h χ (List.mem_cons_of_mem ψ hχ)) (ψ σ)).trans (h ψ (by simp) σ)

/-- Along updates that never add possibilities, a state accepts a text exactly when it accepts
each of its sentences. -/
theorem isFixedPt_text_iff (h : ∀ ψ ∈ ψs, ∀ σ, ψ σ ≤ σ) {σ : α} :
    IsFixedPt (text ψs) σ ↔ ∀ ψ ∈ ψs, IsFixedPt ψ σ := by
  induction ψs with
  | nil => simp [IsFixedPt]
  | cons ψ ψs ih =>
    have h' : ∀ χ ∈ ψs, ∀ σ, χ σ ≤ σ := fun χ hχ ↦ h χ (List.mem_cons_of_mem ψ hχ)
    simp only [List.forall_mem_cons, ← ih h']
    refine ⟨fun hσ ↦ ?_, fun ⟨hψ, hσ⟩ ↦ by simpa [IsFixedPt, hψ.eq] using hσ⟩
    have hψ : IsFixedPt ψ σ :=
      le_antisymm (h ψ (by simp) σ) (hσ.symm.le.trans (text_le h' (ψ σ)))
    exact ⟨hψ, by simpa [IsFixedPt, hψ.eq] using hσ⟩

end Eliminative

/-! ### Additive updates -/

section Additive

variable [SemilatticeInf α] [OrderTop α] {f g φ : α → α} {ψs : List (α → α)} {σ : α}

/-- An update is *additive* when it meets its input with the update of the minimal state, so that
a static content determines it. -/
def IsAdditive (f : α → α) : Prop := ∀ σ, f σ = σ ⊓ f ⊤

theorem IsAdditive.le (hf : IsAdditive f) (σ : α) : f σ ≤ σ := (hf σ).trans_le inf_le_left

theorem IsAdditive.isFixedPt_iff (hf : IsAdditive f) : IsFixedPt f σ ↔ σ ≤ f ⊤ := by
  rw [IsFixedPt, hf σ, inf_eq_left]

theorem isAdditive_id : IsAdditive (id : α → α) := fun _ ↦ inf_top_eq _ |>.symm

theorem isAdditive_inf_right (a : α) : IsAdditive (· ⊓ a) := fun _ ↦ by simp

theorem IsAdditive.comp (hg : IsAdditive g) (hf : IsAdditive f) : IsAdditive (g ∘ f) := fun σ ↦ by
  show g (f σ) = σ ⊓ g (f ⊤)
  rw [hg (f σ), hf σ, hg (f ⊤), inf_assoc]

theorem isAdditive_text (h : ∀ ψ ∈ ψs, IsAdditive ψ) : IsAdditive (text ψs) := by
  induction ψs with
  | nil => exact isAdditive_id
  | cons ψ ψs ih => exact (ih fun χ hχ ↦ h χ (List.mem_cons_of_mem ψ hχ)).comp (h ψ (by simp))

/-- An update is additive exactly when it satisfies Strengthening, never adding possibilities,
Monotony, Idempotence, and Persistence, the states that accept it being closed downward. The four
constraints make the update a closure operator on the reversed order whose closed elements form
an upper set, and such an operator is principal. -/
theorem isAdditive_iff : IsAdditive f ↔
    (∀ σ, f σ ≤ σ) ∧ Monotone f ∧ (∀ σ, IsFixedPt f (f σ)) ∧ IsLowerSet (fixedPoints f) := by
  refine ⟨fun h ↦ ⟨h.le, fun σ τ hστ ↦ ?_, fun σ ↦ ?_, fun σ τ hτσ hσ ↦ ?_⟩,
    fun ⟨hle, hmono, hidem, hpers⟩ σ ↦ ?_⟩
  · rw [h σ, h τ]; exact inf_le_inf_right _ hστ
  · rw [IsFixedPt, h (f σ), h σ, inf_assoc, inf_idem]
  · exact h.isFixedPt_iff.2 (hτσ.trans (h.isFixedPt_iff.1 hσ))
  · let c : ClosureOperator αᵒᵈ :=
      .mk' (toDual ∘ f ∘ ofDual) hmono.dual (fun x ↦ hle (ofDual x))
        fun x ↦ (hidem (ofDual x)).symm.le
    have hc := c.eq_supRight_iff.2 fun _ _ hxy hx ↦
      c.isClosed_iff.2 (hpers hxy (c.isClosed_iff.1 hx))
    exact DFunLike.congr_fun hc (toDual σ)

/-- For additive updates the three consequence relations coincide. -/
theorem tfae_entails (hψs : ∀ ψ ∈ ψs, IsAdditive ψ) (hφ : IsAdditive φ) :
    [EntailsFrom ⊤ ψs φ, Entails ψs φ, PreservesAcceptance ψs φ].TFAE := by
  have hF := isAdditive_text hψs
  have hle : ∀ ψ ∈ ψs, ∀ σ, ψ σ ≤ σ := fun ψ hψ ↦ (hψs ψ hψ).le
  tfae_have 2 → 1 := fun h ↦ h ⊤
  tfae_have 1 → 2 := fun h σ ↦
    hφ.isFixedPt_iff.2 <| (hF σ).trans_le <| inf_le_right.trans (hφ.isFixedPt_iff.1 h)
  tfae_have 1 → 3 := fun h σ hσ ↦ hφ.isFixedPt_iff.2 <|
    (hF.isFixedPt_iff.1 ((isFixedPt_text_iff hle).2 hσ)).trans (hφ.isFixedPt_iff.1 h)
  tfae_have 3 → 1 := fun h ↦ h _ ((isFixedPt_text_iff hle).1 (hF.isFixedPt_iff.2 le_rfl))
  tfae_finish

end Additive

/-! ### Updates with effects -/

section Effects

variable {m : Type _ → Type _} [Monad m] [LawfulMonad m]

/-- A state accepts a Kleisli arrow, read as an update through the monad's bind, exactly when the
arrow returns it unchanged. -/
theorem isFixedPt_bind_pure_iff {φ : α → m α} {σ : α} :
    IsFixedPt (· >>= φ) (pure σ : m α) ↔ φ σ = pure σ := by
  rw [IsFixedPt, pure_bind]

end Effects

/-! ### Sets of possibilities -/

section CCP

variable {S : Type*} {u : CCP S} {c d s : Set S}

theorem CCP.isAdditive_up (c : Set S) : IsAdditive (CCP.up c) := fun s ↦ by simp [CCP.up]

theorem CCP.isFixedPt_up_iff : IsFixedPt (CCP.up c) s ↔ s ⊆ c := Set.inter_eq_left

/-- On sets of possibilities the additive updates are the classical ones, eliminative and
distributive. -/
theorem CCP.isAdditive_iff_isClassical : IsAdditive u ↔ u.IsClassical := by
  rw [CCP.isClassical_iff_up_down_eq]
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ CCP.isAdditive_up _⟩
  rw [show u = CCP.up (u ⊤) from funext h, CCP.down_up]

/-- Entailment between static updates is inclusion of their contents. -/
theorem CCP.entails_up_iff : Entails [CCP.up c] (CCP.up d) ↔ c ⊆ d :=
  ⟨fun h ↦ by simpa [CCP.up] using CCP.isFixedPt_up_iff.1 (h Set.univ),
    fun h _ ↦ CCP.isFixedPt_up_iff.2 (Set.inter_subset_right.trans h)⟩

/-- A relational update entails a test exactly when its outputs satisfy the test's condition. -/
theorem Update.entails_image_test_iff (R : Update S) (C : Condition S) :
    Entails [R.image] (Update.test C).image ↔ R.cod ⊆ C := by
  rw [← CCP.up_eq_image_test]
  exact ⟨fun h _ ⟨i, hi⟩ ↦ CCP.isFixedPt_up_iff.1 (h {i}) ⟨i, rfl, hi⟩,
    fun h _ ↦ CCP.isFixedPt_up_iff.2 fun _ ⟨_, _, hg⟩ ↦ h ⟨_, hg⟩⟩

end CCP

end DynamicSemantics
