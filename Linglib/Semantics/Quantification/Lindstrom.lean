module

public import Linglib.Core.Data.Fin.VecNotation
public import Linglib.Core.ModelTheory.Lindstrom
public import Linglib.Core.ModelTheory.Monadic
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Semantics.Quantification.NumberTree
public import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# Realizing Lindström quantifiers as determiner denotations

A determiner, a Lindström quantifier of type `⟨1,1⟩`, is an isomorphism-invariant class of
structures for the monadic language with two predicate symbols, the restrictor `pred 0` and the
scope `pred 1`. `Det.toDet` realizes it as a determiner denotation: a pair of sets `(A, B)` becomes
the structure `(α, A, B)`, and the quantifier holds of `(A, B)` when that structure is in the class.
A determiner [depends only on the sizes of the four Venn
regions](##Quantifier.Lindstrom.Det.toDet_iff_of_mk_eq) on universes of any size, and on finite
universes the realized determiners are [exactly the global denotations closed under
isomorphism](##Quantifier.Lindstrom.isom_iff_exists_toFamily).

Those defined by a sentence are the first-order definable ones, [characterized by invariance up to
a threshold](##Quantifier.Det.Family.foDefinable_iff_exists_alikeUpTo). On the tree of numbers this
is a [maturity level](##Quantifier.NumberTree.foDefinable_toFamily_iff), a line of the tree below
which truth values settle.

## References

* [barwise-cooper-1981]
* [lindstrom-1966]
* [mostowski-1957]
* [van-benthem-1984]
-/

@[expose] public section

universe u

namespace Quantifier.Lindstrom

open Quantifier.Det

open FirstOrder Language BoundedFormula
open CategoryTheory (Bundled)
open Cardinal

/-! ### The realization -/

/-- A *determiner* is a Lindström quantifier of type `⟨1,1⟩`, an iso-invariant class of
structures for the monadic language with a restrictor and a scope predicate. -/
abbrev Det := LindstromQuantifier.{0, 0, u} (Language.monadic (Fin 2))

namespace Det

/-- `Q.toDet α` holds of `(A, B)` iff the structure `(α, A, B)` is in the class `Q`. -/
def toDet (Q : Det.{u}) (α : Type u) : Quantifier.Det α :=
  fun A B ↦
    ⟦(⟨α, monadic.structure ![A, B]⟩ : Bundled.{u} (Language.monadic (Fin 2)).Structure)⟧ ∈ Q

/-- Every realized Lindström quantifier is permutation invariant, derived from its isomorphism
closure rather than stipulated on the denotation. -/
theorem realize_quantityInvariant (Q : Det.{u}) {α : Type u} :
    (Q.toDet α).QuantityInvariant := fun σ _ _ ↦
  Q.is_equiv_invariant
    ⟨monadic.structureEquiv σ (Fin.forall_fin_two.2 ⟨fun _ ↦ .rfl, fun _ ↦ .rfl⟩)⟩

/-- The global determiner denotation of a Lindström quantifier, its realization on every finite
universe. -/
def toFamily (Q : Det.{u}) : Quantifier.Det.Family.{u} := fun α _ ↦ Q.toDet α

/-- A Lindström quantifier is closed under isomorphism across universes, since isomorphic
structures are equally in its class: isomorphism closure is Lindström's own condition. -/
theorem isom_toFamily (Q : Det.{u}) : Q.toFamily.Isom := fun _ _ _ _ e _ _ ↦
  Q.is_equiv_invariant
    ⟨monadic.structureEquiv e (Fin.forall_fin_two.2 ⟨fun _ ↦ .rfl, fun _ ↦ .rfl⟩)⟩

/-- Realization carries the complement of a class to outer negation. -/
theorem toDet_compl (Q : Det.{u}) (α : Type u) : toDet Qᶜ α = (Q.toDet α)ᶜ := rfl

end Det

/-! ### The Aristotelian determiners -/

/-- The determiner *every*, defined by `∀x (U x → V x)`. -/
def everyDet : Det.{u} := .ofSentence
  (∀' (Relations.boundedFormula₁ (.pred 0) &0 ⟹ Relations.boundedFormula₁ (.pred 1) &0))

/-- The determiner *some*, defined by `∃x (U x ∧ V x)`. -/
def someDet : Det.{u} := .ofSentence
  (∃' (Relations.boundedFormula₁ (.pred 0) &0 ⊓ Relations.boundedFormula₁ (.pred 1) &0))

/-- The determiner *no*, defined by `∀x (U x → ¬ V x)`. -/
def noDet : Det.{u} := .ofSentence
  (∀' (Relations.boundedFormula₁ (.pred 0) &0 ⟹ ∼(Relations.boundedFormula₁ (.pred 1) &0)))

theorem everyDet_toDet (α : Type u) : everyDet.toDet α = (every : Quantifier.Det α) := by
  funext A B
  simp [Det.toDet, everyDet, Sentence.Realize, Formula.Realize, Fin.snoc, every]
  exact Iff.rfl

theorem someDet_toDet (α : Type u) :
    someDet.toDet α = (Quantifier.Det.some : Quantifier.Det α) := by
  funext A B
  simp [Det.toDet, someDet, Sentence.Realize, Formula.Realize, Fin.snoc, Quantifier.Det.some]
  exact Iff.rfl

theorem noDet_toDet (α : Type u) : noDet.toDet α = (no : Quantifier.Det α) := by
  funext A B
  simp [Det.toDet, noDet, Sentence.Realize, Formula.Realize, Fin.snoc, no]
  exact Iff.rfl

/-- As isomorphism-closed classes, *some* is the complement of *no*, since `∃x. Ux ∧ Vx` is the
negation of `∀x. Ux → ¬Vx`. -/
theorem someDet_eq_compl_noDet : someDet.{u} = noDetᶜ := by
  ext q
  induction q using Quotient.inductionOn with
  | _ M => simp [someDet, noDet, Sentence.Realize, Formula.Realize]

/-! ### The four regions -/

section Regions

variable {α β : Type u} {A B : Set α} {A' B' : Set β}

/-- A function of sets agrees on the cells of two pairs of sets, cut out by whether a point lies
in each set, exactly when it agrees on the four Venn regions. -/
private theorem forall_cell_iff {γ : Type*} (f : ∀ {σ : Type u}, Set σ → γ) :
    (∀ p q : Prop, f {x | (x ∈ A ↔ p) ∧ (x ∈ B ↔ q)} = f {x | (x ∈ A' ↔ p) ∧ (x ∈ B' ↔ q)}) ↔
      f (A ∩ B) = f (A' ∩ B') ∧ f (A \ B) = f (A' \ B') ∧ f (B \ A) = f (B' \ A') ∧
        f (A ∪ B)ᶜ = f (A' ∪ B')ᶜ := by
  have hAB {σ : Type u} (X Y : Set σ) : {x | x ∈ X ∧ x ∈ Y} = X ∩ Y := rfl
  have hAd {σ : Type u} (X Y : Set σ) : {x | x ∈ X ∧ x ∉ Y} = X \ Y := rfl
  have hBA {σ : Type u} (X Y : Set σ) : {x | x ∉ X ∧ x ∈ Y} = Y \ X := Set.ext fun _ ↦ and_comm
  have hO {σ : Type u} (X Y : Set σ) : {x | x ∉ X ∧ x ∉ Y} = (X ∪ Y)ᶜ := Set.ext fun _ ↦ not_or.symm
  simp only [Prop.forall, iff_true, iff_false, hAB, hAd, hBA, hO]
  tauto

private theorem preimage_unaryType (A B : Set α)
    (S : (Language.monadic (Fin 2)).Relations 1 → Prop) :
    @unaryType _ α (monadic.structure ![A, B]) ⁻¹' {S} =
      {x | (x ∈ A ↔ S (.pred 0)) ∧ (x ∈ B ↔ S (.pred 1))} :=
  Set.ext fun x ↦ (unaryType_monadic_structure_eq_iff x S).trans Fin.forall_fin_two

/-- A determiner holds of `(A, B)` according to the sizes of the four Venn regions alone, on
universes of any size. -/
theorem Det.toDet_iff_of_mk_eq (Q : Det.{u})
    (h₁ : #↥(A ∩ B) = #↥(A' ∩ B')) (h₂ : #↥(A \ B) = #↥(A' \ B'))
    (h₃ : #↥(B \ A) = #↥(B' \ A')) (h₄ : #↥(A ∪ B)ᶜ = #↥(A' ∪ B')ᶜ) :
    Q.toDet α A B ↔ Q.toDet β A' B' :=
  Q.is_equiv_invariant <| (@nonempty_equiv_iff_mk_eq _ _ α β (monadic.structure ![A, B])
    (monadic.structure ![A', B'])).2 fun S ↦ by
      rw [preimage_unaryType, preimage_unaryType]
      exact (forall_cell_iff (fun s ↦ #↥s)).2 ⟨h₁, h₂, h₃, h₄⟩ _ _

/-- The interpretation of a predicate symbol in a structure. -/
private def extension (i : Fin 2) (M : Bundled.{u} (Language.monadic (Fin 2)).Structure) : Set M :=
  {a | Structure.RelMap (L := Language.monadic (Fin 2)) (.pred i) ![a]}

/-- A global determiner denotation is closed under isomorphism exactly when it is the realization
of a Lindström quantifier. -/
theorem isom_iff_exists_toFamily {F : Quantifier.Det.Family.{u}} :
    F.Isom ↔ ∃ D : Det.{u}, D.toFamily = F := by
  refine ⟨fun hF ↦ ⟨{q | q.liftOn
    (fun M ↦ ∃ _ : Finite M, F M (extension 0 M) (extension 1 M)) ?_}, ?_⟩, ?_⟩
  · rintro M N ⟨e⟩
    refine propext ?_
    have hext (i : Fin 2) : e ⁻¹' extension i N = extension i M :=
      Set.ext fun a ↦ (congrFun (e.unaryType_apply a) (.pred i)).to_iff
    refine ⟨fun ⟨_, h⟩ ↦ ?_, fun ⟨_, h⟩ ↦ ?_⟩
    · have : Finite N := .of_equiv M e.toEquiv
      exact ⟨this, (hF e.toEquiv _ _).1 (by rwa [show ⇑e.toEquiv = ⇑e from rfl, hext, hext])⟩
    · have : Finite M := .of_equiv N e.toEquiv.symm
      exact ⟨this, by
        rw [← hext, ← hext]; exact (hF e.toEquiv _ _).2 h⟩
  · funext α _ A B
    exact propext ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨inferInstance, h⟩⟩
  · rintro ⟨D, rfl⟩
    exact D.isom_toFamily

/-- Two pairs of sets are *alike up to* `n` when each of the four Venn regions has the same size
on the two sides or at least `n` on both, van Benthem's `∼ₙ`. -/
def AlikeUpTo (n : ℕ) (A B : Set α) (A' B' : Set β) : Prop :=
  min n (A ∩ B).ncard = min n (A' ∩ B').ncard ∧ min n (A \ B).ncard = min n (A' \ B').ncard ∧
    min n (B \ A).ncard = min n (B' \ A').ncard ∧ min n (A ∪ B)ᶜ.ncard = min n (A' ∪ B')ᶜ.ncard

private theorem min_encard_eq_iff [Finite α] [Finite β] (n : ℕ) (s : Set α) (t : Set β) :
    min (n : ℕ∞) s.encard = min (n : ℕ∞) t.encard ↔ min n s.ncard = min n t.ncard := by
  rw [← s.toFinite.cast_ncard_eq, ← t.toFinite.cast_ncard_eq, ← Nat.mono_cast.map_min,
    ← Nat.mono_cast.map_min, Nat.cast_inj]

/-- Finite structures for two predicates are `n`-equivalent exactly when they are alike up to
`n`. -/
theorem elementarilyEquivalentUpTo_iff_alikeUpTo [Finite α] [Finite β] {n : ℕ} :
    @ElementarilyEquivalentUpTo _ n α β (monadic.structure ![A, B])
      (monadic.structure ![A', B']) ↔ AlikeUpTo n A B A' B' := by
  rw [elementarilyEquivalentUpTo_monadic_structure_iff, AlikeUpTo]
  simp only [← min_encard_eq_iff n]
  rw [← forall_cell_iff fun s ↦ min (n : ℕ∞) s.encard]
  simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact ⟨fun h p q ↦ h ![p, q], fun h S ↦ h (S 0) (S 1)⟩

private theorem exists_eq_structure {M : Type u} (S : (Language.monadic (Fin 2)).Structure M) :
    ∃ A B : Set M, S = monadic.structure ![A, B] := by
  refine ⟨{a | S.RelMap (.pred 0) ![a]}, {a | S.RelMap (.pred 1) ![a]}, ?_⟩
  conv_lhs => rw [monadic.eq_structure S]
  congr 1
  exact funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)

end Regions

end Quantifier.Lindstrom

namespace Quantifier

open FirstOrder Language Lindstrom

/-- A global determiner denotation is first-order definable when it is the realization of the
class of models of a sentence. -/
def Det.Family.FODefinable (F : Det.Family.{u}) : Prop :=
  ∃ φ : (Language.monadic (Fin 2)).Sentence, Lindstrom.Det.toFamily (.ofSentence φ) = F

/-- On the finite models, a global determiner denotation is first-order definable exactly when, for
some fixed `n`, it cannot tell apart pairs of sets alike up to `n` ([van-benthem-1984] Theorem
6.1). -/
theorem Det.Family.foDefinable_iff_exists_alikeUpTo {F : Det.Family.{u}} :
    F.FODefinable ↔ ∃ n, ∀ ⦃α β : Type u⦄ [Finite α] [Finite β] (A B : Set α) (A' B' : Set β),
      AlikeUpTo n A B A' B' → F α A B → F β A' B' := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨φ.quantifierRank, fun α β _ _ A B A' B' h ↦
      (elementarilyEquivalentUpTo_iff_alikeUpTo.2 h φ le_rfl).1⟩
  · rintro ⟨n, hn⟩
    obtain ⟨φ, hφ⟩ : (Language.monadic (Fin 2)).FODefinable {M | Finite M}
        {M | ∃ _ : Finite M, F M (extension 0 M) (extension 1 M)} :=
      foDefinable_iff_exists_elementarilyEquivalentUpTo.2 ⟨n, fun M _ N hN hMN ⟨_, h⟩ ↦ by
        obtain ⟨M, SM⟩ := M
        obtain ⟨N, SN⟩ := N
        obtain ⟨A, B, rfl⟩ := exists_eq_structure SM
        obtain ⟨A', B', rfl⟩ := exists_eq_structure SN
        have : Finite N := hN
        exact ⟨this, hn A B A' B' (elementarilyEquivalentUpTo_iff_alikeUpTo.1 hMN) h⟩⟩
    refine ⟨φ, funext fun α ↦ funext fun hα ↦ funext fun A ↦ funext fun B ↦ propext ?_⟩
    exact (hφ ⟨α, monadic.structure ![A, B]⟩ hα).symm.trans
      ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hα, h⟩⟩

/-- A tree of numbers is first-order definable on the finite models exactly when it reaches a
maturity level ([van-benthem-1984], reading Theorem 6.1 on the tree). -/
theorem NumberTree.foDefinable_toFamily_iff (q : NumberTree) :
    (q.toFamily : Det.Family.{u}).FODefinable ↔ ∃ n, q.MaturityLevel n := by
  rw [NumberTree.exists_maturityLevel_iff]
  rw [Det.Family.foDefinable_iff_exists_alikeUpTo]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, fun a b a' b' ha hb ↦ ?_⟩
    obtain ⟨γ, _, X, Y, h₁, h₂, h₃, h₄⟩ := NumberTree.exists_ncard_eq.{u} a b 0
    obtain ⟨γ', _, X', Y', h₁', h₂', h₃', h₄'⟩ := NumberTree.exists_ncard_eq.{u} a' b' 0
    have halike : AlikeUpTo n X Y X' Y' := by
      simp [AlikeUpTo, h₁, h₂, h₃, h₄, h₁', h₂', h₃', h₄', ha, hb]
    have halike' : AlikeUpTo n X' Y' X Y := by
      simp [AlikeUpTo, h₁, h₂, h₃, h₄, h₁', h₂', h₃', h₄', ha, hb]
    have h := hn X Y X' Y' halike
    have h' := hn X' Y' X Y halike'
    simp only [NumberTree.toFamily, NumberTree.toDet_apply, h₁, h₂, h₁', h₂'] at h h'
    exact ⟨h, h'⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, fun _ _ _ _ A B A' B' ⟨hi, hd, _⟩ ↦ (hn _ _ _ _ hd hi).1⟩

end Quantifier
