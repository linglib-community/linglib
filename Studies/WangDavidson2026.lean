module

public import Linglib.Semantics.Exhaustification.Trivalent
public import Linglib.Semantics.Dynamic.Partial
public import Linglib.Data.Examples.WangDavidson2026
public import Mathlib.Data.Fintype.Prod

/-!
# Wang & Davidson (2026): Presupposition Filtering in Disjunction

Wang and Davidson survey what fully semantic implementations of exclusive disjunction predict for
presupposition projection. Under Strong Kleene an inclusive disjunction is true when one disjunct
is, whatever the other, so a true disjunct filters the other's presupposition, whereas an
exclusive disjunction is undefined whenever a disjunct is (`Filters`, `not_filters_xor`).
Fox's bivalent exhaustification strengthens a disjunction to its exclusive reading (`exh_or`), so
once the strengthened truth conditions feed the projection computation three projection theories
agree that an exclusive disjunction projects uniformly: Strong Kleene, as Mayr and Romoli apply
it; George's algorithm, rendered as `george` over any classical connective, which agrees with
Strong Kleene on inclusive and exclusive disjunction (`george_or`, `george_xor`) while filtering
conjunction only from left to right; and dynamic semantics, where each of the eight context
change potentials that Rothschild's restrictions allow for exclusive disjunction is admitted only
by a context satisfying both presuppositions (`xorCCPs_admits`). Spector and Sudo's trivalent
exhaustifiers split: weak-negation EXH¹ is undefined exactly where its prejacent is, so it leaves
projection alone, while strong-negation EXH² is undefined wherever an innocently excludable
alternative is, and for a disjunction the conjunction alternative's presupposition together with
the disjunction's is both disjuncts' (`sup_inf_ne_zero_iff`). The theories predicting that more
exclusive readings mean less filtering are the paper's Type A; the paper's Mandarin experiment on
*huozhe* finds no such effect.

## Implementation notes

Strong Kleene exclusive disjunction is `-(a * b)`, since multiplication on `SignType` is the
Strong Kleene biconditional. The exhaustification identity is checked on the four valuations of
two atoms, the free model of a propositional identity. George's algorithm is stated as the paper
renders it, on the set of classical values a trivalent argument leaves open. The experiment's
ratings are not formalized; its stimuli are in `Data.Examples.WangDavidson2026`.

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
def FiltersLR (f : SignType → SignType → SignType) : Prop := ∃ a, f a 0 ≠ 0

/-- Filtering from right to left. -/
def FiltersRL (f : SignType → SignType → SignType) : Prop := ∃ b, f 0 b ≠ 0

/-- A connective filters when it does so in either direction. -/
def Filters (f : SignType → SignType → SignType) : Prop := FiltersLR f ∨ FiltersRL f

/-- Strong Kleene inclusive disjunction filters in both directions (Table 1). -/
theorem filtersLR_sup : FiltersLR (· ⊔ ·) := ⟨1, by decide⟩

theorem filtersRL_sup : FiltersRL (· ⊔ ·) := ⟨1, by decide⟩

/-- Strong Kleene exclusive disjunction never filters (Table 2). -/
theorem not_filters_xor : ¬ Filters fun a b ↦ -(a * b) := by
  rintro (⟨a, h⟩ | ⟨b, h⟩)
  · exact h (SignType.neg_eq_zero_iff.2 (mul_zero a))
  · exact h (SignType.neg_eq_zero_iff.2 (zero_mul b))

/-! ### Bivalent exhaustification yields exclusive disjunction -/

/-- The valuations of two atoms. -/
abbrev Val := Bool × Bool

/-- The alternatives of `p ∨ q` are `p`, `q` and `p ∧ q` (3a). -/
def orAlts : Finset (Finset Val) :=
  altsFromPreds [fun v ↦ v.1 || v.2, Prod.fst, Prod.snd, fun v ↦ v.1 && v.2]

/-- Only the conjunction is innocently excludable (3b). -/
theorem excluded_or :
    innocent.excluded orAlts (predToFinset fun v : Val ↦ v.1 || v.2)
      = {predToFinset fun v : Val ↦ v.1 && v.2} := by
  decide

/-- Bivalent exhaustification of `p ∨ q` is `p xor q` (3c). -/
theorem exh_or :
    innocent.exh orAlts (predToFinset fun v : Val ↦ v.1 || v.2)
      = predToFinset fun v : Val ↦ v.1 ^^ v.2 := by
  decide

/-! ### George's algorithm -/

/-- The classical values a trivalent value leaves open. -/
def values : SignType → Finset Bool
  | .pos => {true}
  | .neg => {false}
  | .zero => Finset.univ

/-- [george-2008]'s algorithm computes the trivalent table of a classical connective, as
[kalomoiros-schwarz-2024] render it. If the left argument settles the value, that is the value;
otherwise, if some value of the right argument could make the sentence true, the two arguments
settle the value or the sentence is undefined; otherwise it is undefined. -/
def george (f : Bool → Bool → Bool) (a b : SignType) : SignType :=
  if ∀ x ∈ values a, ∀ y, f x y then 1
  else if ∀ x ∈ values a, ∀ y, f x y = false then -1
  else if ∃ y, ∀ x ∈ values a, f x y then
    if ∀ x ∈ values a, ∀ y ∈ values b, f x y then 1
    else if ∀ x ∈ values a, ∀ y ∈ values b, f x y = false then -1
    else 0
  else 0

theorem george_or : george (· || ·) = (· ⊔ ·) := by
  funext a b; revert a b; decide

theorem george_xor : george (· ^^ ·) = fun a b ↦ -(a * b) := by
  funext a b; revert a b; decide

theorem filtersLR_george_and : FiltersLR (george (· && ·)) := ⟨-1, by decide⟩

theorem not_filtersRL_george_and : ¬ FiltersRL (george (· && ·)) := by
  rintro ⟨b, h⟩; revert b; decide

theorem not_filters_george_xor : ¬ Filters (george (· ^^ ·)) := george_xor ▸ not_filters_xor

/-! ### Dynamic semantics -/

section Dynamic

variable {W : Type*} (α β : W → SignType) {s : Set W}

/-- Update with a proposition or with its negation. -/
def lit : Bool → (W → SignType) → CCP.Partial W
  | true, p => ofTrivalent p
  | false, p => CCP.Partial.neg (ofTrivalent p)

/-- The context `C[p][q]`, for `p` and `q` propositions or their negations. -/
def chain (b₁ : Bool) (p : W → SignType) (b₂ : Bool) (q : W → SignType) : CCP.Partial W :=
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

theorem subset_support_of_split (h₁ : {w ∈ s | α w = 1} ⊆ Function.support β)
    (h₂ : s \ {w ∈ s | α w = 1} ⊆ Function.support β) : s ⊆ Function.support β := fun w hw ↦ by
  by_cases ha : α w = 1
  · exact h₁ ⟨hw, ha⟩
  · exact h₂ ⟨hw, fun h ↦ ha h.2⟩

theorem xorCCPs_admits :
    ∀ u ∈ xorCCPs α β, u.Admits s →
      s ⊆ Function.support α ∧ s ⊆ Function.support β := by
  simp only [xorCCPs, List.mem_cons, List.mem_nil_iff, or_false]
  rintro u (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
  · exact ⟨h₁, h₃⟩
  · exact ⟨h₁, h₃⟩
  · exact ⟨h₁, subset_support_of_split α β h₂ h₄⟩
  · exact ⟨subset_support_of_split β α h₂ h₄, h₁⟩
  · exact ⟨h₁, h₃⟩
  · exact ⟨h₁, h₃⟩
  · exact ⟨h₁, subset_support_of_split α β h₂ h₄⟩
  · exact ⟨subset_support_of_split β α h₂ h₄, h₁⟩

theorem exists_disj_admits_not_admits :
    ∃ α β : Bool → SignType, (disj (ofTrivalent α) (ofTrivalent β)).Admits Set.univ ∧
      ¬ Set.univ ⊆ Function.support β := by
  refine ⟨fun w ↦ SignType.ofProp (w = true), {w | w = false}.indicator 1,
    ⟨fun _ _ ↦ by simp, ?_⟩, fun h ↦ h (Set.mem_univ true) (by simp)⟩
  rintro (_ | _) hw
  · simp
  · exact absurd ⟨trivial, by simp⟩ hw.2

end Dynamic

/-! ### Trivalent exhaustification -/

/-- Under Strong Kleene (8), the presuppositions of `α ∨ β` and `α ∧ β` together are those of both
disjuncts. -/
theorem sup_inf_ne_zero_iff (a b : SignType) :
    (a ⊔ b ≠ 0 ∧ a ⊓ b ≠ 0) ↔ a ≠ 0 ∧ b ≠ 0 := by
  revert a b; decide

/-- A bathroom disjunction on the valuations of two atoms — `bathLeft` is always defined and
`bathRight` presupposes its negation. -/
def bathLeft : Val → SignType := fun v ↦ .ofProp v.1

def bathRight : Val → SignType := fun v ↦ if v.1 then 0 else .ofProp v.2

/-- The alternatives of the bathroom disjunction. -/
def bathAlts : List (Val → SignType) :=
  [bathLeft, bathRight, fun v ↦ bathLeft v ⊓ bathRight v]

/-- The inclusive bathroom disjunction. -/
def bathOr : Val → SignType := fun v ↦ bathLeft v ⊔ bathRight v

theorem exh1_bathOr : exh1 bathAlts bathOr (true, false) = 1 := by decide

theorem exh2_bathOr : exh2 bathAlts bathOr (true, false) = 0 := by decide

end WangDavidson2026
