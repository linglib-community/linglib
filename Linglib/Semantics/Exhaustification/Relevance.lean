module

public import Mathlib.Order.BooleanSubalgebra
public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Linglib.Semantics.Questions.Partition.Basic

/-!
# Relevance of alternatives

Fox and Katzir restrict the formal alternatives of a sentence to the contextually relevant ones,
with relevance closed under the Boolean operations. A sentence is exhaustively relevant given a
restriction when its *only*-meaning lies in the Boolean closure of the restriction, and a
restriction is allowable when it keeps the assertion and prunes nothing exhaustively relevant. A
set in the Boolean closure of a family does not separate worlds that every member of the family
treats alike (`mem_iff_of_mem_closure`), so an alternative whose *only*-meaning separates two such
worlds is not exhaustively relevant (`not_exhaustivelyRelevant_of_separates`). For a finite
family the Boolean closure is exactly the propositions that the question raised by the family
determines (`mem_closure_iff_determines`), so exhaustive relevance is the *only*-meaning being
about that question (`exhaustivelyRelevant_iff_determines`). Relevance relative
to a context set is the same notion over the subtype of the context, each proposition restricted
to it by preimage.

## Main definitions

* `Exhaustification.ExhaustivelyRelevant`, `Exhaustification.IsAllowableRestriction`

## References

* [fox-katzir-2011]
-/

@[expose] public section

namespace Exhaustification

variable {W : Type*}

/-- A sentence is exhaustively relevant given a restriction when its *only*-meaning lies in the
Boolean closure of the restriction. -/
def ExhaustivelyRelevant (A : Set (Set W)) (p : Set W) : Prop :=
  exh A p ∈ BooleanSubalgebra.closure A

/-- A restriction of the formal alternatives is allowable when it keeps the assertion and prunes
nothing exhaustively relevant. -/
def IsAllowableRestriction (F A : Set (Set W)) (S : Set W) : Prop :=
  S ∈ A ∧ ∀ p ∈ F \ A, ¬ ExhaustivelyRelevant A p

variable {A : Set (Set W)} {X p : Set W} {u v : W}

/-- A set in the Boolean closure of `A` does not separate worlds that every member of `A` treats
alike. -/
theorem mem_iff_of_mem_closure (hX : X ∈ BooleanSubalgebra.closure A)
    (h : ∀ a ∈ A, u ∈ a ↔ v ∈ a) : u ∈ X ↔ v ∈ X := by
  induction hX using BooleanSubalgebra.closure_bot_sup_induction with
  | mem a ha => exact h a ha
  | bot => exact Iff.rfl
  | sup x _ y _ hx hy => exact or_congr hx hy
  | compl x _ hx => exact not_congr hx

theorem notMem_closure_of_separates (h : ∀ a ∈ A, u ∈ a ↔ v ∈ a) (hu : u ∈ X) (hv : v ∉ X) :
    X ∉ BooleanSubalgebra.closure A :=
  fun hX ↦ hv ((mem_iff_of_mem_closure hX h).1 hu)

theorem not_exhaustivelyRelevant_of_separates (h : ∀ a ∈ A, u ∈ a ↔ v ∈ a)
    (hu : u ∈ exh A p) (hv : v ∉ exh A p) : ¬ ExhaustivelyRelevant A p :=
  notMem_closure_of_separates h hu hv

/-- A proposition in the Boolean closure of a family is determined by the question the family
raises. -/
theorem determines_of_mem_closure (hX : X ∈ BooleanSubalgebra.closure A) :
    (⨅ a ∈ A, Setoid.polar a).Determines X :=
  Setoid.determines_iff.2 fun _ _ h ↦ mem_iff_of_mem_closure hX (Setoid.iInf_mem_polar_iff.1 h)

/-- The Boolean closure of a finite family is the set of propositions that the question the
family raises determines. -/
theorem mem_closure_iff_determines (hA : A.Finite) :
    X ∈ BooleanSubalgebra.closure A ↔ (⨅ a ∈ A, Setoid.polar a).Determines X := by
  refine ⟨determines_of_mem_closure, ?_⟩
  induction A, hA using Set.Finite.induction_on generalizing X with
  | empty =>
    intro hX
    simp only [Set.mem_empty_iff_false, iInf_false, iInf_top] at hX
    rcases X.eq_empty_or_nonempty with rfl | ⟨w, hw⟩
    · exact BooleanSubalgebra.bot_mem
    · rw [Set.eq_univ_of_forall fun v ↦ (Setoid.determines_iff.1 hX w v trivial).1 hw]
      exact BooleanSubalgebra.top_mem
  | @insert b A' _ _ ih =>
    intro hX
    have hmono : BooleanSubalgebra.closure A' ≤ BooleanSubalgebra.closure (insert b A') :=
      BooleanSubalgebra.closure_mono (Set.subset_insert b A')
    have hb : b ∈ BooleanSubalgebra.closure (insert b A') :=
      BooleanSubalgebra.subset_closure (Set.mem_insert b A')
    -- each half of `X` cut by `b` is the trace of a proposition the coarser question determines
    have sat : ∀ c : Set W, (c = b ∨ c = bᶜ) →
        ∃ Y ∈ BooleanSubalgebra.closure A', Y ∩ c = X ∩ c := by
      intro c hc
      refine ⟨{v | ∃ w ∈ X ∩ c, (⨅ a ∈ A', Setoid.polar a) w v},
        ih (Setoid.determines_iff.2 fun u v huv ↦
          ⟨fun ⟨w, hw, hwu⟩ ↦ ⟨w, hw, Setoid.trans' _ hwu huv⟩,
            fun ⟨w, hw, hwv⟩ ↦ ⟨w, hw, Setoid.trans' _ hwv (Setoid.symm' _ huv)⟩⟩), ?_⟩
      ext v
      refine ⟨fun ⟨⟨w, hw, hwv⟩, hvc⟩ ↦ ⟨?_, hvc⟩, fun hv ↦ ⟨⟨v, hv, Setoid.refl' _ v⟩, hv.2⟩⟩
      refine (Setoid.determines_iff.1 hX w v (Setoid.iInf_mem_polar_iff.2 ?_)).1 hw.1
      rintro a (rfl | ha)
      · rcases hc with rfl | rfl
        · exact iff_of_true hw.2 hvc
        · exact iff_of_false hw.2 hvc
      · exact Setoid.iInf_mem_polar_iff.1 hwv a ha
    obtain ⟨Y₁, hY₁, h₁⟩ := sat b (.inl rfl)
    obtain ⟨Y₂, hY₂, h₂⟩ := sat bᶜ (.inr rfl)
    rw [show X = Y₁ ∩ b ∪ Y₂ ∩ bᶜ by
      rw [h₁, h₂, ← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ]]
    exact BooleanSubalgebra.sup_mem (BooleanSubalgebra.inf_mem (hmono hY₁) hb)
      (BooleanSubalgebra.inf_mem (hmono hY₂) (BooleanSubalgebra.compl_mem hb))

/-- Given a finite restriction, a sentence is exhaustively relevant exactly when the question
the restriction raises determines its *only*-meaning. -/
theorem exhaustivelyRelevant_iff_determines (hA : A.Finite) :
    ExhaustivelyRelevant A p ↔ (⨅ a ∈ A, Setoid.polar a).Determines (exh A p) :=
  mem_closure_iff_determines hA

/-- Exhaustifying a member of a finite set of alternatives stays in the Boolean closure of the
set. -/
theorem exhIE_mem_closure {S : Set W} (hfin : A.Finite) (hS : S ∈ A) :
    exhIE A S ∈ BooleanSubalgebra.closure A := by
  have hIE : {a | IsInnocentlyExcludable A S a}.Finite := hfin.subset fun _ ha ↦ ha.1
  have hsup : ⋃₀ {a | IsInnocentlyExcludable A S a} ∈ BooleanSubalgebra.closure A := by
    refine hIE.induction_on_subset _ (by rw [Set.sUnion_empty]; exact BooleanSubalgebra.bot_mem)
      fun {a X} ha _ _ ih ↦ ?_
    rw [Set.sUnion_insert]
    exact BooleanSubalgebra.sup_mem (BooleanSubalgebra.subset_closure ha.1) ih
  have heq : exhIE A S = S \ ⋃₀ {a | IsInnocentlyExcludable A S a} := by
    ext w
    simp only [mem_exhIE_iff, Set.mem_sdiff, Set.mem_sUnion, Set.mem_ofPred_eq, not_exists,
      not_and]
  exact heq ▸ BooleanSubalgebra.sdiff_mem (BooleanSubalgebra.subset_closure hS) hsup

end Exhaustification
