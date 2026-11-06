module

public import Linglib.Semantics.Exhaustification.Trivalent
public import Linglib.Semantics.Dynamic.Partial
public import Linglib.Logic.Trivalent.Powerset
public import Linglib.Data.Examples.WangDavidson2026
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Prod
public import Studies.George2008

/-!
# Wang & Davidson (2026): Presupposition Filtering in Disjunction

Wang and Davidson survey what fully semantic implementations of exclusive disjunction predict for
presupposition projection. Under Strong Kleene an inclusive disjunction is true when one disjunct
is, whatever the other, so a true disjunct filters the other's presupposition, whereas an
exclusive disjunction is undefined whenever a disjunct is (`Filters`, `not_filters_xor`).
Fox's bivalent exhaustification strengthens a disjunction to its exclusive reading (`exh_or`), so
once the strengthened truth conditions feed the projection computation three projection theories
agree that an exclusive disjunction projects uniformly: Strong Kleene, as Mayr and Romoli apply
it; George's deployment with concern for disappointment, `George2008.deployWithConcern₂`, which
agrees with Strong Kleene on inclusive and exclusive disjunction (`deployWithConcern₂_xor`) while filtering
conjunction only from left to right; and dynamic semantics, where each of the eight context
change potentials that Rothschild's restrictions allow for exclusive disjunction is admitted only
by a context satisfying both presuppositions (`xorCCPs_admits`). Spector and Sudo's trivalent
exhaustifiers split: weak-negation EXH¹ is undefined exactly where its prejacent is, so it leaves
projection alone, while strong-negation EXH² is undefined wherever an innocently excludable
alternative is, and for a disjunction the conjunction alternative's presupposition together with
the disjunction's is both disjuncts' (`sup_inf_ne_undefined_iff`). The theories predicting that more
exclusive readings mean less filtering are the paper's Type A; the paper's Mandarin experiment on
*huozhe* finds no such effect.

## Implementation notes

Strong Kleene exclusive disjunction is the negation of the Strong Kleene biconditional
`(aᶜ ⊔ b) ⊓ (a ⊔ bᶜ)`. The exhaustification identity is checked on the four valuations of
two atoms, the free model of a propositional identity. George's algorithm is his deployment with
concern for disappointment (`Studies/George2008`), shown equal to the rendering the paper follows.
The experiment's ratings are not formalized; its stimuli are in `Data.Examples.WangDavidson2026`.

## References

* [wang-davidson-2026]
* [fox-2007]
* [george-2008]
* [kalomoiros-schwarz-2024]
* [mayr-romoli-2016a]
* [rothschild-2011]
* [spector-sudo-2017]
-/

@[expose] public section

namespace WangDavidson2026

open Exhaustification Exhaustification.Trivalent DynamicSemantics PartialUpdate
open CCP.Partial

/-! ### Filtering by a trivalent connective -/

/-- A trivalent connective filters from left to right when a defined left argument can make the
whole defined with an undefined right argument. -/
def FiltersLR (f : Trivalent → Trivalent → Trivalent) : Prop := ∃ a, f a .undefined ≠ .undefined

/-- Filtering from right to left. -/
def FiltersRL (f : Trivalent → Trivalent → Trivalent) : Prop := ∃ b, f .undefined b ≠ .undefined

/-- A connective filters when it does so in either direction. -/
def Filters (f : Trivalent → Trivalent → Trivalent) : Prop := FiltersLR f ∨ FiltersRL f

-- Table 1
theorem filtersLR_sup : FiltersLR (· ⊔ ·) := ⟨.true, by decide⟩

theorem filtersRL_sup : FiltersRL (· ⊔ ·) := ⟨.true, by decide⟩

/-- Strong Kleene exclusive disjunction never filters (Table 2). -/
theorem not_filters_xor : ¬ Filters fun a b ↦ ((aᶜ ⊔ b) ⊓ (a ⊔ bᶜ))ᶜ := by
  unfold Filters FiltersLR FiltersRL
  decide

/-! ### Bivalent exhaustification yields exclusive disjunction -/

/-- The valuations of two atoms. -/
abbrev Val := Bool × Bool

/-- The alternatives of `p ∨ q` are `p ∨ q` itself, `p`, `q` and `p ∧ q` (3a). -/
def orAlt : Fin 4 → Set Val
  | 0 => {v | v.1 ∨ v.2}
  | 1 => {v | v.1}
  | 2 => {v | v.2}
  | 3 => {v | v.1 ∧ v.2}

instance : ∀ i, DecidablePred (· ∈ orAlt i)
  | 0 => inferInstanceAs (DecidablePred fun v : Val ↦ v.1 ∨ v.2)
  | 1 => inferInstanceAs (DecidablePred fun v : Val ↦ v.1)
  | 2 => inferInstanceAs (DecidablePred fun v : Val ↦ v.2)
  | 3 => inferInstanceAs (DecidablePred fun v : Val ↦ v.1 ∧ v.2)

-- (3b)
theorem excluded_or :
    {a | IsInnocentlyExcludable (Set.range orAlt) (orAlt 0) a} = {orAlt 3} := by
  have h : ∀ i, IsInnocentlyExcludable (Set.range orAlt) (orAlt 0) (orAlt i) ↔ i = 3 := by
    decide
  ext a
  refine ⟨fun ha ↦ ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := ha.1
    exact congrArg orAlt ((h i).1 ha)
  · rintro rfl
    exact (h 3).2 rfl

/-- Bivalent exhaustification of `p ∨ q` is `p xor q` (3c). -/
theorem exh_or : exhIE (Set.range orAlt) (orAlt 0) = {v | Xor v.1 v.2} := by
  ext v; revert v; decide

/-! ### George's algorithm -/

open George2008 (deploy₂ deployWithConcern₂)

/-- [george-2008]'s deployment with concern for disappointment is the algorithm as
[kalomoiros-schwarz-2024] render it, on every classical connective. If the left argument settles
the value, that is the value; otherwise, if some value of the right argument could make the
sentence true, the two arguments settle the value or the sentence is undefined; otherwise it is
undefined. -/
theorem deployWithConcern₂_eq (f : Bool → Bool → Bool) (a b : Trivalent) :
    deployWithConcern₂ f a b =
      if ∀ x ∈ Trivalent.toFinset a, ∀ y, f x y then .true
      else if ∀ x ∈ Trivalent.toFinset a, ∀ y, f x y = false then .false
      else if ∃ y, ∀ x ∈ Trivalent.toFinset a, f x y then deploy₂ f a b
      else .undefined := by
  revert f a b; decide

theorem deployWithConcern₂_xor :
    deployWithConcern₂ (· ^^ ·) = fun a b ↦ ((aᶜ ⊔ b) ⊓ (a ⊔ bᶜ))ᶜ := by
  funext a b; revert a b; decide

theorem filtersLR_deployWithConcern₂_and : FiltersLR (deployWithConcern₂ (· && ·)) :=
  ⟨.false, by decide⟩

theorem not_filtersRL_deployWithConcern₂_and : ¬ FiltersRL (deployWithConcern₂ (· && ·)) := by
  rintro ⟨b, h⟩; revert b; decide

theorem not_filters_deployWithConcern₂_xor : ¬ Filters (deployWithConcern₂ (· ^^ ·)) :=
  deployWithConcern₂_xor ▸ not_filters_xor

/-! ### Dynamic semantics -/

section Dynamic

variable {W : Type*} (α β : W → Trivalent) {s : Set W}

/-- Update with a proposition or with its negation. -/
def lit : Bool → (W → Trivalent) → CCP.Partial W
  | true, p => ofTrivalent p
  | false, p => CCP.Partial.neg (ofTrivalent p)

/-- The context `C[p][q]`, for `p` and `q` propositions or their negations. -/
def chain (b₁ : Bool) (p : W → Trivalent) (b₂ : Bool) (q : W → Trivalent) : CCP.Partial W :=
  seq (lit b₁ p) (lit b₂ q)

/-- The union of two updates, defined when both are. -/
def union (φ ψ : CCP.Partial W) : CCP.Partial W :=
  fun s ↦ ⟨(φ s).Dom ∧ (ψ s).Dom, fun h ↦ (φ s).get h.1 ∪ (ψ s).get h.2⟩

/-- The context minus two updates, defined when both are. -/
def diff (φ ψ : CCP.Partial W) : CCP.Partial W :=
  fun s ↦ ⟨(φ s).Dom ∧ (ψ s).Dom, fun h ↦ (s \ (φ s).get h.1) \ (ψ s).get h.2⟩

/-- The eight context change potentials for `α xor β` (Table 3). -/
def xorCCPs : List (CCP.Partial W) :=
  [union (chain true α false β) (chain true β false α),
   union (chain false α true β) (chain false β true α),
   union (chain true α false β) (chain false α true β),
   union (chain true β false α) (chain false β true α),
   diff (chain true α true β) (chain false β false α),
   diff (chain false α false β) (chain true β true α),
   diff (chain true α true β) (chain false α false β),
   diff (chain true β true α) (chain false β false α)]

theorem subset_compl_gapExt_of_split (h₁ : {w ∈ s | α w = .true} ⊆ (Trivalent.gapExt β)ᶜ)
    (h₂ : s \ {w ∈ s | α w = .true} ⊆ (Trivalent.gapExt β)ᶜ) : s ⊆ (Trivalent.gapExt β)ᶜ :=
    fun w hw ↦ by
  by_cases ha : α w = .true
  · exact h₁ ⟨hw, ha⟩
  · exact h₂ ⟨hw, fun h ↦ ha h.2⟩

theorem xorCCPs_admits :
    ∀ u ∈ xorCCPs α β, u.Admits s →
      s ⊆ (Trivalent.gapExt α)ᶜ ∧ s ⊆ (Trivalent.gapExt β)ᶜ := by
  simp only [xorCCPs, List.mem_cons, List.mem_nil_iff, or_false]
  rintro u (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
  · exact ⟨h₁, h₃⟩
  · exact ⟨h₁, h₃⟩
  · exact ⟨h₁, subset_compl_gapExt_of_split α β h₂ h₄⟩
  · exact ⟨subset_compl_gapExt_of_split β α h₂ h₄, h₁⟩
  · exact ⟨h₁, h₃⟩
  · exact ⟨h₁, h₃⟩
  · exact ⟨h₁, subset_compl_gapExt_of_split α β h₂ h₄⟩
  · exact ⟨subset_compl_gapExt_of_split β α h₂ h₄, h₁⟩

theorem exists_disj_admits_not_admits :
    ∃ α β : Bool → Trivalent, (disj (ofTrivalent α) (ofTrivalent β)).Admits Set.univ ∧
      ¬ Set.univ ⊆ (Trivalent.gapExt β)ᶜ := by
  refine ⟨fun w ↦ Trivalent.ofProp (w = true),
    fun w ↦ Trivalent.transplication (Trivalent.ofProp (w = false)) .true,
    ⟨fun _ _ ↦ by simp, ?_⟩, fun h ↦ h (Set.mem_univ true) (by simp)⟩
  rintro (_ | _) hw
  · simp
  · exact absurd ⟨trivial, by simp⟩ hw.2

end Dynamic

/-! ### Trivalent exhaustification -/

/-- Under Strong Kleene (8), the presuppositions of `α ∨ β` and `α ∧ β` together are those of both
disjuncts. -/
theorem sup_inf_ne_undefined_iff (a b : Trivalent) :
    (a ⊔ b ≠ .undefined ∧ a ⊓ b ≠ .undefined) ↔ a ≠ .undefined ∧ b ≠ .undefined := by
  revert a b; decide

/-- A bathroom disjunction on the valuations of two atoms — `bathLeft` is always defined and
`bathRight` presupposes its negation. -/
def bathLeft : Val → Trivalent := fun v ↦ .ofProp v.1

def bathRight : Val → Trivalent := fun v ↦ if v.1 then .undefined else .ofProp v.2

/-- The alternatives of the bathroom disjunction. -/
def bathAlts : Fin 3 → Val → Trivalent :=
  ![bathLeft, bathRight, fun v ↦ bathLeft v ⊓ bathRight v]

/-- The inclusive bathroom disjunction. -/
def bathOr : Val → Trivalent := fun v ↦ bathLeft v ⊔ bathRight v

theorem exh1_bathOr : exh1 bathAlts bathOr (true, false) = .true := by decide

theorem exh2_bathOr : exh2 bathAlts bathOr (true, false) = .undefined := by decide

end WangDavidson2026
