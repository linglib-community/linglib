module

public import Linglib.Semantics.Alternatives.Symmetric
public import Linglib.Semantics.Alternatives.Relevance
public import Studies.Katzir2007
public import Linglib.Semantics.Exhaustification.Basic
public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Linglib.Logic.Modal.Basic
public import Linglib.Data.Examples.FoxKatzir2011
public import Linglib.Data.Examples.Readers

/-!
# Fox and Katzir (2011): On the Characterization of Alternatives

This file formalizes [fox-katzir-2011]'s argument that the alternatives of scalar implicature
and of association with focus are one set, [katzir-2007]'s structural alternatives extended by
the salient constituents of the context (`formalAlternatives`), and that symmetry among
alternatives is broken only there: contextual restriction never keeps one of two alternatives
that partition the assertion while pruning the other. The implicature and *only* operators are
`Exhaustification.exh` against the strictly stronger and against all the alternatives; on symmetric
alternatives both are contradictory (`dominated_of_isSymmetric`), a universal operator above
the assertion removes the symmetry and both inferences arise (`mem_exh_nec`), innocent exclusion
negates neither symmetric alternative (`exhIE_eq_self_of_isSymmetric`), and a contextual set
closed under negation and conjunction keeps both or neither
(`Alternatives.IsSymmetric.mem_of_mem`). The paper's stronger condition, allowable restriction
through exhaustive relevance, forbids pruning one of two compatible disjuncts as well
(`not_isAllowableRestriction_pair`).

## Implementation notes

Sentences are propositions `Set W`, alternative sets are `Set (Set W)`, and the operators are
intersections of complements, the paper's propositional rendering of *only*. The structural
definition is the paper's simplified one, successive replacement of a sub-constituent by an
element of the substitution source (`substitutionAlternatives`), without the deletion,
contraction and same-category condition of [katzir-2007]'s `structuralAlternatives`. It is
stated without focus marking, so `formalAlternatives` contains the paper's set; its one new
clause, salient constituents, is what brings a symmetric alternative into the set
(`mem_formalAlternatives_of_salient`). Universal operators are `ModalLogic.Box` over an
accessibility relation, covering the modal and the quantificational cases alike.

## References

* [fox-katzir-2011]
* [katzir-2007]
* [kroch-1972]
* [horn-1972]
* [rooth-1985]
* [sauerland-2004]
* [fox-2007]
-/

@[expose] public section

namespace FoxKatzir2011

open Alternatives Exhaustification ModalLogic Set
open SetRel

variable {W : Type*}

/-! ### Formal alternatives -/

section Substitution

variable {α : Type*} {r : RoseTree α → RoseTree α → Prop}

/-- `Rewrites r t t'` when `t'` is `t` with one constituent `x` replaced by a `y` such that
`r x y`. -/
inductive Rewrites (r : RoseTree α → RoseTree α → Prop) : RoseTree α → RoseTree α → Prop
  | here {x y : RoseTree α} (h : r x y) : Rewrites r x y
  | child (a : α) (l₁ : List (RoseTree α)) {c c' : RoseTree α} (l₂ : List (RoseTree α))
      (h : Rewrites r c c') : Rewrites r (.node a (l₁ ++ c :: l₂)) (.node a (l₁ ++ c' :: l₂))

theorem reflTransGen_rewrites_node (a : α) (pre : List (RoseTree α)) {cs cs' : List (RoseTree α)}
    (h : List.Forall₂ (Relation.ReflTransGen (Rewrites r)) cs cs') :
    Relation.ReflTransGen (Rewrites r) (.node a (pre ++ cs)) (.node a (pre ++ cs')) := by
  induction h generalizing pre with
  | nil => exact .refl
  | @cons c c' cs cs' h _ ih =>
    refine (h.lift (fun x ↦ RoseTree.node a (pre ++ x :: cs))
      fun _ _ hx ↦ .child a pre cs hx).trans ?_
    simpa using ih (pre ++ [c'])

/-- One replacement of a sub-constituent with an element of the substitution source. -/
def Substitutes (source : Set (RoseTree α)) : RoseTree α → RoseTree α → Prop :=
  Rewrites fun _ s ↦ s ∈ source

/-- What successive replacements from the source derive from `φ`: the structures at most as
complex as `φ`. -/
def substitutionAlternatives (source : Set (RoseTree α)) (φ : RoseTree α) : Set (RoseTree α) :=
  {ψ | Relation.ReflTransGen (Substitutes source) φ ψ}

theorem self_mem_substitutionAlternatives (source : Set (RoseTree α)) (φ : RoseTree α) :
    φ ∈ substitutionAlternatives source φ :=
  Relation.ReflTransGen.refl

theorem subset_substitutionAlternatives (source : Set (RoseTree α)) (φ : RoseTree α) :
    source ⊆ substitutionAlternatives source φ :=
  fun _ h ↦ .single (.here h)

end Substitution

section Formal

open PhraseStructure Tree

variable {C V : Type*} (lex : Finset (Tree C V)) (φ : Tree C V) (salient : Finset (Tree C V))

/-- The substitution source in a context consists of the lexicon, the sub-constituents of the
sentence, and the salient constituents of the context. -/
def contextualSource : Set (Tree C V) := ↑lex ∪ {t | t ∈ φ.subtrees} ∪ ↑salient

/-- The formal alternatives in a context are whatever is at most as complex as the sentence over
the contextual substitution source. -/
def formalAlternatives : Set (Tree C V) :=
  substitutionAlternatives (contextualSource lex φ salient) φ

theorem mem_formalAlternatives_of_salient {ψ : Tree C V} (hψ : ψ ∈ salient) :
    ψ ∈ formalAlternatives lex φ salient :=
  subset_substitutionAlternatives _ _ (by simp [contextualSource, hψ])

theorem someButNotAll_mem_formalAlternatives :
    Katzir2007.someButNotAllSentence ∈ formalAlternatives Katzir2007.lexicon
      Katzir2007.someSentence {Katzir2007.someButNotAllSentence} :=
  mem_formalAlternatives_of_salient _ _ _ (Finset.mem_singleton_self _)

end Formal

/-! ### Symmetry -/

section Symmetry

variable {A : Set (Set W)} {S S₁ S₂ : Set W}

theorem dominated_of_isSymmetric (h : IsSymmetric S S₁ S₂) (h₁ : S₁ ∈ A) (h₂ : S₂ ∈ A)
    (hne₁ : S₁.Nonempty) (hne₂ : S₂.Nonempty) : Dominated A S :=
  h.union ▸ dominated_union h₁ h₂
    (fun hs ↦ let ⟨_, hw⟩ := hne₁; disjoint_left.1 h.disjoint hw (hs hw))
    (fun hs ↦ let ⟨_, hw⟩ := hne₂; disjoint_left.1 h.disjoint (hs hw) hw)

theorem not_isInnocentlyExcludable_of_isSymmetric (h : IsSymmetric S S₁ S₂)
    (hne₁ : S₁.Nonempty) : ¬ IsInnocentlyExcludable {S, S₁, S₂} S S₁ :=
  not_isInnocentlyExcludable_of_subset_union _ _ (toFinite _) (by simp) (by simp)
    h.union.symm.subset (h.symm.sdiff_eq.symm ▸ hne₁)

theorem exhIE_eq_self_of_isSymmetric (h : IsSymmetric S S₁ S₂) (hne₁ : S₁.Nonempty)
    (hne₂ : S₂.Nonempty) : exhIE {S, S₁, S₂} S = S :=
  exhIE_eq_self_of_subset_union h.union.symm.subset (h.sdiff_eq.symm ▸ hne₂)
    (h.symm.sdiff_eq.symm ▸ hne₁)

theorem exhIE_pair_eq_sdiff (h : IsSymmetric S S₁ S₂) (hne₂ : S₂.Nonempty) :
    exhIE {S, S₁} S = S₂ := by
  obtain ⟨b, hb⟩ := hne₂
  have hIE : IsInnocentlyExcludable {S, S₁} S S₁ := by
    refine .of_forall_subset_or_notMem (by simp) (h.subset_right hb)
      (disjoint_left.1 h.disjoint.symm hb) ?_
    rintro c hc
    simp only [mem_insert_iff, mem_singleton_iff] at hc
    obtain h1 | h1 := hc <;> subst c
    · exact Or.inl subset_rfl
    · exact Or.inr (disjoint_left.1 h.disjoint.symm hb)
  ext w
  rw [mem_exhIE_iff, ← h.sdiff_eq, mem_sdiff]
  refine ⟨fun ⟨hw, h'⟩ ↦ ⟨hw, h' S₁ hIE⟩, fun ⟨hw, hw₁⟩ ↦ ⟨hw, fun q hq ↦ ?_⟩⟩
  have hq1 := hq.1
  simp only [mem_insert_iff, mem_singleton_iff] at hq1
  obtain h1 | h1 := hq1 <;> subst q
  · exact (not_isInnocentlyExcludable_of_phi_subset (toFinite _) ⟨w, hw⟩ subset_rfl hq).elim
  · exact hw₁

end Symmetry

/-! ### Universal operators -/

section Universal

variable {R : SetRel W W} {S S₁ S₂ : Set W}

theorem not_isSymmetric_nec {x : W} (hx : x ∈ R.core S) (hx₁ : x ∉ R.core S₁)
    (hx₂ : x ∉ R.core S₂) : ¬ IsSymmetric (R.core S) (R.core S₁) (R.core S₂) := fun h ↦ by
  have : x ∈ R.core S₁ ∪ R.core S₂ := h.union ▸ hx
  exact this.elim hx₁ hx₂

theorem mem_exh_nec {x : W} (hx : x ∈ R.core S) (hx₁ : x ∉ R.core S₁) (hx₂ : x ∉ R.core S₂) :
    x ∈ exh {R.core S, R.core S₁, R.core S₂} (R.core S) := by
  refine ⟨hx, fun p hp hxp ↦ ?_⟩
  simp only [mem_insert_iff, mem_singleton_iff] at hp
  obtain h1 | h1 | h1 := hp <;> subst p
  · exact subset_rfl
  · exact absurd hxp hx₁
  · exact absurd hxp hx₂

end Universal

/-! ### Contextual restriction -/

section Restriction

variable {S S₁ S₂ : Set W} {F : Set (Set W)}

theorem mem_inter_of_isSymmetric (h : IsSymmetric S S₁ S₂) (R : BooleanSubalgebra (Set W))
    (hS : S ∈ R) (hF : S₂ ∈ F) (h₁ : S₁ ∈ (R : Set (Set W)) ∩ F) :
    S₂ ∈ (R : Set (Set W)) ∩ F :=
  ⟨h.mem_of_mem hS h₁.1, hF⟩

theorem not_isAllowableRestriction_pair (hS : S = S₁ ∪ S₂) (h₂₁ : ¬ S₂ ⊆ S₁) (hF : S₂ ∈ F)
    (h₂ : S₂ ∉ ({S, S₁} : Set (Set W))) : ¬ IsAllowableRestriction F {S, S₁} S := by
  rintro ⟨-, hall⟩
  refine hall S₂ ⟨hF, h₂⟩ ?_
  have hOnly : exh {S, S₁} S₂ = S \ S₁ := by
    subst hS
    ext w
    rw [mem_exh, union_sdiff_left, mem_sdiff]
    simp only [mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq]
    exact ⟨fun ⟨hw, _, h⟩ ↦ ⟨hw, fun h1 ↦ h₂₁ (h h1)⟩,
      fun ⟨hw, h⟩ ↦ ⟨hw, fun _ ↦ subset_union_right, fun h1 ↦ (h h1).elim⟩⟩
  rw [ExhaustivelyRelevant, hOnly]
  exact BooleanSubalgebra.sdiff_mem (BooleanSubalgebra.subset_closure (by simp))
    (BooleanSubalgebra.subset_closure (by simp))

end Restriction

/-! ### The data -/

/-- A sentence of the data records whether its formal alternatives contain a symmetric pair,
whether a universal operator intervenes, whether the alternatives at issue are compatible, and
whether the inference arises. -/
structure Row where
  symmetric : Bool
  universal : Bool
  compatible : Bool
  inference : Bool
  deriving DecidableEq

def yesNoTable : List (String × Bool) := [("yes", true), ("no", false)]

def Row.ofDatum (ex : Datum) : Option Row := do
  let s ← ex.parse? "symmetric" yesNoTable
  let u ← ex.parse? "universal" yesNoTable
  let c ← ex.parse? "compatible" yesNoTable
  let i ← ex.parse? "inference" yesNoTable
  pure ⟨s, u, c, i⟩

def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem rows_predicted : ∀ r ∈ rows,
    (r.inference = true ↔ r.universal = true ∨ (r.symmetric = false ∧ r.compatible = false)) := by
  decide

end FoxKatzir2011
