module

public import Linglib.Semantics.Quantifier.Counting
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Global quantifiers

A determiner has a denotation on every universe, not on one. This file defines global quantifiers
and global determiner denotations, which give a value on every finite universe, and the
conditions that tie the values on different universes together:

* isomorphism closure, `Isom`: an equivalence of universes carries the value on one to the value
  on the other;
* extension: enlarging the universe does not change the value at sets inside the smaller one;
* constancy: the two together, invariance along every embedding of universes.

We prove that the conservative constant global determiner denotations are exactly the trees of
numbers, and that they are the relativizations of the isomorphism-closed global quantifiers,
where the relativization of a quantifier evaluates it on the restrictor as the universe. We then
define the global denotations of the determiners of `Quantifier/Basic.lean` and
`Quantifier/Counting.lean`, and the determiner symbols that name them.

## Main definitions

* `Quantifier.Det.Family`, `Quantifier.Family`: global determiner denotations and global
  quantifiers.
* `Quantifier.Det.Family.Isom`, `Quantifier.Det.Family.Ext`, `Quantifier.Det.Family.Constant`:
  isomorphism closure, extension and constancy.
* `Quantifier.Family.rel`: relativization, which turns a global quantifier into a global
  determiner denotation.
* `Quantifier.NumberTree.ofFamily`, `Quantifier.NumberTree.toFamily`: the tree of a global
  determiner denotation, and the global determiner denotation of a tree.
* `Quantifier.Det.Symbol`: the determiner symbols, each denoting the global denotation of a tree.

## Main results

* `Quantifier.NumberTree.familyOrderIso`: the conservative constant global determiner
  denotations are the trees, as Boolean algebras.
* `Quantifier.Det.Family.not_apply_of_asymm`: such a denotation that is asymmetric on every
  universe is empty. On a single universe this fails.
* `Quantifier.NumberTree.relOrderIso`: relativization is an order isomorphism from the
  isomorphism-closed global quantifiers onto the conservative constant global determiner
  denotations.
* `Quantifier.Family.Isom.apply_iff`: an isomorphism-closed global quantifier holds of `B`
  according to `|Bᶜ|` and `|B|`, by the tree of its relativization.
* `Quantifier.Family.Isom.ext_iff`, `Quantifier.Family.Isom.monotone_iff`: such a quantifier
  satisfies extension if and only if that tree is cardinal, and is monotone on every universe if
  and only if that tree is scope monotone.
* `Quantifier.Det.Symbol.conservative_denote`, `Quantifier.Det.Symbol.constant_denote`: what a
  determiner symbol denotes is conservative and constant.

## Implementation notes

A type is not a subset of another type, so extension is stated for a subset `M` of a universe
`β` and the universe `↥M`. Extension therefore relates a universe only to its subtypes; it is
isomorphism closure that relates universes presented by unrelated types. The two together are
invariance along every embedding of universes, `Det.Family.Constant`, which is the condition the
theorems about global quantifiers assume.

Relativization evaluates a quantifier on the universe `↥A`, so relativizing on a subset of a
subset reaches a subtype of a subtype rather than the subset itself. Peters and Westerståhl's
identification of the relativizations with the conservative extensional determiner denotations
therefore holds here for isomorphism-closed quantifiers. Elements of one type are not elements of
another, so the global quantifiers that set theory allows to single out an element across
universes, such as the Montague lift of a fixed individual, have no counterpart among these.

## References

* [barwise-cooper-1981]
* [peters-westerstahl-2006]
* [van-benthem-1984]
* [van-benthem-1986]
* [westerstahl-2017]
-/

@[expose] public section

universe u

namespace Quantifier

/-- A global determiner denotation gives a determiner denotation on every finite universe. The
readings of a lexicon entry are drawn from these. -/
abbrev Det.Family : Type (u + 1) := ∀ (α : Type u) [Finite α], Det α

/-- The global determiner denotations form a Boolean algebra, pointwise on universes. -/
instance : BooleanAlgebra Det.Family.{u} :=
  Equiv.booleanAlgebra <|
    Equiv.piCongrRight fun α ↦ Equiv.arrowCongr Equiv.plift.symm (.refl (Det α))

namespace Det

/-! ### Global determiner denotations -/

namespace Family

variable (Q : Det.Family.{u})

/-- A global determiner denotation is conservative when it is conservative on every universe. -/
def Conservative : Prop := ∀ (α : Type u) [Finite α], (Q α).Conservative

/-- A global determiner denotation is closed under isomorphism (ISOM) when an equivalence of
universes `e : α ≃ β` carries its quantifier on `β` to its quantifier on `α`. -/
def Isom : Prop :=
  ∀ ⦃α β : Type u⦄ [Finite α] [Finite β] (e : α ≃ β) (A B : Set β),
    Q α (e ⁻¹' A) (e ⁻¹' B) ↔ Q β A B

/-- A global determiner denotation satisfies extension (EXT) when enlarging the universe does not
change it: for `A` and `B` inside `M ⊆ β`, it holds on the universe `M` exactly when it holds on
`β`. That determiner denotations satisfy it is [van-benthem-1986]'s observation. -/
def Ext : Prop :=
  ∀ ⦃β : Type u⦄ [Finite β] (M A B : Set β), A ⊆ M → B ⊆ M →
    (Q M (Subtype.val ⁻¹' A) (Subtype.val ⁻¹' B) ↔ Q β A B)

/-- A global determiner denotation is constant when it is invariant along every embedding of
universes: for `A` and `B` inside the range of `f : α ↪ β`, it holds of their preimages on `α`
exactly when it holds of them on `β`. Constancy is extension together with isomorphism closure,
an embedding being an isomorphism onto its range followed by an inclusion: the closure under
injections of [peters-westerstahl-2006], which [westerstahl-2017] proposes as the explication of
a quantifier being the same on every universe. -/
def Constant : Prop :=
  ∀ ⦃α β : Type u⦄ [Finite α] [Finite β] (f : α ↪ β) (A B : Set β),
    A ⊆ Set.range f → B ⊆ Set.range f → (Q α (f ⁻¹' A) (f ⁻¹' B) ↔ Q β A B)

variable {Q}

@[simp] theorem compl_apply (α : Type u) [Finite α] : Qᶜ α = (Q α)ᶜ := rfl

@[simp] theorem inf_apply (Q' : Det.Family.{u}) (α : Type u) [Finite α] :
    (Q ⊓ Q') α = Q α ⊓ Q' α := rfl

@[simp] theorem sup_apply (Q' : Det.Family.{u}) (α : Type u) [Finite α] :
    (Q ⊔ Q') α = Q α ⊔ Q' α := rfl

theorem le_def {Q' : Det.Family.{u}} :
    Q ≤ Q' ↔ ∀ (α : Type u) [Finite α] (A B : Set α), Q α A B → Q' α A B :=
  ⟨fun h α _ A B ↦ h α ⟨inferInstance⟩ A B, fun h α p A B ↦ @h α p.down A B⟩

/-- On a single universe, isomorphism closure is permutation invariance. -/
theorem Isom.quantityInvariant (h : Q.Isom) (α : Type u) [Finite α] :
    (Q α).QuantityInvariant :=
  fun σ ↦ h σ

end Family

end Det

/-! ### Global quantifiers and relativization -/

/-- A global quantifier gives a quantifier on every finite universe. -/
abbrev Family : Type (u + 1) := ∀ (α : Type u) [Finite α], Quantifier α

/-- The global quantifiers form a Boolean algebra, pointwise on universes. -/
instance : BooleanAlgebra Family.{u} :=
  Equiv.booleanAlgebra <|
    Equiv.piCongrRight fun α ↦ Equiv.arrowCongr Equiv.plift.symm (.refl (Quantifier α))

namespace Family

variable (Q : Family.{u})

/-- A global quantifier is closed under isomorphism when an equivalence of universes
`e : α ≃ β` carries its value on `β` to its value on `α`. -/
def Isom : Prop :=
  ∀ ⦃α β : Type u⦄ [Finite α] [Finite β] (e : α ≃ β) (B : Set β), Q α (e ⁻¹' B) ↔ Q β B

/-- A global quantifier satisfies extension when enlarging the universe does not change it: for
`B` inside `M ⊆ β`, it holds of `B` on the universe `M` exactly when it holds of `B` on `β`. -/
def Ext : Prop :=
  ∀ ⦃β : Type u⦄ [Finite β] (M B : Set β), B ⊆ M → (Q M (Subtype.val ⁻¹' B) ↔ Q β B)

/-- The relativization of a global quantifier evaluates it on the restrictor as the universe:
`Q.rel A B` holds when `Q` holds, on the universe `A`, of the part of `B` inside `A`. -/
def rel : Det.Family.{u} := fun _ _ A B ↦ Q A (Subtype.val ⁻¹' B)

variable {Q}

theorem le_def {Q' : Family.{u}} :
    Q ≤ Q' ↔ ∀ (α : Type u) [Finite α] (B : Set α), Q α B → Q' α B :=
  ⟨fun h α _ B ↦ h α ⟨inferInstance⟩ B, fun h α p B ↦ @h α p.down B⟩

end Family

namespace NumberTree

variable {q : NumberTree} {a b : ℕ}

/-! ### The tree of a global determiner denotation

A global determiner denotation that is conservative and constant, extensional and closed under
isomorphism, holds of `A` and `B` according to `|A \ B|` and `|A ∩ B|` alone, on every universe
at once, which is Peters and Westerståhl's representation of such quantifiers by binary
relations between numbers. Such denotations are exactly the trees, so every theorem about trees
is a theorem about them. -/

section Family

open Det

variable {Q : Det.Family.{u}}

/-- Constancy is extension together with isomorphism closure. -/
theorem _root_.Quantifier.Det.Family.constant_iff : Q.Constant ↔ Q.Ext ∧ Q.Isom := by
  refine ⟨fun h ↦ ⟨fun β _ M A B hA hB ↦ ?_, fun α β _ _ e A B ↦ ?_⟩, fun ⟨hE, hI⟩ ↦ ?_⟩
  · exact h (Function.Embedding.subtype (· ∈ M)) A B (by simpa using hA) (by simpa using hB)
  · exact h e.toEmbedding A B (by simp) (by simp)
  · intro α β _ _ f A B hA hB
    exact (hI (Equiv.ofInjective f f.injective) _ _).trans (hE _ A B hA hB)

theorem _root_.Quantifier.Det.Family.Constant.ext (h : Q.Constant) : Q.Ext :=
  (Det.Family.constant_iff.1 h).1

theorem _root_.Quantifier.Det.Family.Constant.isom (h : Q.Constant) : Q.Isom :=
  (Det.Family.constant_iff.1 h).2

private theorem ncard_image_sdiff {α β : Type*} {f : α → β} (hf : f.Injective) (A B : Set α) :
    (f '' A \ f '' B).ncard = (A \ B).ncard := by
  rw [← Set.image_sdiff hf, Set.ncard_image_of_injective _ hf]

private theorem ncard_image_inter {α β : Type*} {f : α → β} (hf : f.Injective) (A B : Set α) :
    (f '' A ∩ f '' B).ncard = (A ∩ B).ncard := by
  rw [← Set.image_inter hf, Set.ncard_image_of_injective _ hf]

/-- A conservative constant global determiner denotation holds of `A` and `B` on one universe
exactly when it holds of `A'` and `B'` on another with the same `|A \ B|` and `|A ∩ B|`. Both
universes embed in their sum, where permutation invariance applies. -/
theorem _root_.Quantifier.Det.Family.iff_of_ncard_eq (hC : Q.Conservative) (hK : Q.Constant)
    {α β : Type u} [Finite α] [Finite β] {A B : Set α} {A' B' : Set β}
    (hd : (A \ B).ncard = (A' \ B').ncard) (hi : (A ∩ B).ncard = (A' ∩ B').ncard) :
    Q α A B ↔ Q β A' B' := by
  have h₁ := hK (Function.Embedding.inl (α := α) (β := β)) _ _
    (Set.image_subset_range _ A) (Set.image_subset_range _ B)
  have h₂ := hK (Function.Embedding.inr (α := α) (β := β)) _ _
    (Set.image_subset_range _ A') (Set.image_subset_range _ B')
  simp only [Set.preimage_image_eq _ (Function.Embedding.injective _)] at h₁ h₂
  refine h₁.trans ((Det.iff_of_ncard_eq (hC _) (hK.isom.quantityInvariant _) ?_ ?_).trans
    h₂.symm)
  · rw [ncard_image_sdiff (Function.Embedding.injective _),
      ncard_image_sdiff (Function.Embedding.injective _), hd]
  · rw [ncard_image_inter (Function.Embedding.injective _),
      ncard_image_inter (Function.Embedding.injective _), hi]

/-- The tree of a global determiner denotation holds of `(a, b)` when the denotation holds of some
`A` and `B` on some universe with `|A \ B| = a` and `|A ∩ B| = b`. -/
def ofFamily (Q : Det.Family.{u}) : NumberTree := fun a b ↦
  ∃ (α : Type u) (_ : Finite α) (A B : Set α), (A \ B).ncard = a ∧ (A ∩ B).ncard = b ∧ Q α A B

/-- A conservative constant global determiner denotation holds of `A` and `B` exactly when its
tree holds of `|A \ B|` and `|A ∩ B|`. -/
theorem ofFamily_iff (hC : Q.Conservative) (hK : Q.Constant) (α : Type u) [Finite α]
    (A B : Set α) : ofFamily Q (A \ B).ncard (A ∩ B).ncard ↔ Q α A B :=
  ⟨fun ⟨_, _, _, _, hd, hi, h⟩ ↦ (Det.Family.iff_of_ncard_eq hC hK hd hi).1 h,
    fun h ↦ ⟨α, inferInstance, A, B, rfl, rfl, h⟩⟩

/-- The global determiner denotation of a tree is its determiner denotation on every universe. -/
def toFamily (q : NumberTree) : Det.Family.{u} := fun _ _ ↦ q.toDet

theorem conservative_toFamily (q : NumberTree) : (q.toFamily : Det.Family.{u}).Conservative :=
  fun _ _ ↦ conservative_toDet q

/-- The global determiner denotation of a tree is constant; only the restrictor need lie inside
the range of the embedding. -/
theorem constant_toFamily (q : NumberTree) : (q.toFamily : Det.Family.{u}).Constant :=
  fun _ _ _ _ f _ B hA _ ↦ toDet_preimage f.injective B hA q

/-- Some universe realizes any three sizes as `|X \ Y|`, `|X ∩ Y|` and `|Y \ X|`, with nothing
outside `X` and `Y`. -/
theorem exists_ncard_eq (a b c : ℕ) : ∃ (γ : Type u) (_ : Finite γ) (X Y : Set γ),
    (X \ Y).ncard = a ∧ (X ∩ Y).ncard = b ∧ (Y \ X).ncard = c ∧ (X ∪ Y)ᶜ = ∅ := by
  let e₁ : Fin a → ULift.{u} (Fin a ⊕ Fin b ⊕ Fin c) := fun i ↦ ⟨.inl i⟩
  let e₂ : Fin b → ULift.{u} (Fin a ⊕ Fin b ⊕ Fin c) := fun i ↦ ⟨.inr (.inl i)⟩
  let e₃ : Fin c → ULift.{u} (Fin a ⊕ Fin b ⊕ Fin c) := fun i ↦ ⟨.inr (.inr i)⟩
  have card {n : ℕ} {e : Fin n → ULift.{u} (Fin a ⊕ Fin b ⊕ Fin c)} (he : e.Injective) :
      (Set.range e).ncard = n := by
    rw [Set.ncard_range_of_injective he, Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨_, inferInstance, Set.range e₁ ∪ Set.range e₂, Set.range e₂ ∪ Set.range e₃, ?_, ?_, ?_,
    ?_⟩
  · convert card (e := e₁) fun i j h ↦ by simpa [e₁] using h using 2
    ext ⟨x | x | x⟩ <;> simp [e₁, e₂, e₃]
  · convert card (e := e₂) fun i j h ↦ by simpa [e₂] using h using 2
    ext ⟨x | x | x⟩ <;> simp [e₁, e₂, e₃]
  · convert card (e := e₃) fun i j h ↦ by simpa [e₃] using h using 2
    ext ⟨x | x | x⟩ <;> simp [e₁, e₂, e₃]
  · ext ⟨x | x | x⟩ <;> simp [e₁, e₂, e₃]

theorem ofFamily_toFamily (q : NumberTree) : ofFamily (q.toFamily : Det.Family.{u}) = q := by
  funext a b
  refine propext ⟨fun ⟨_, _, _, _, ha, hb, h⟩ ↦ ha ▸ hb ▸ h, fun h ↦ ?_⟩
  obtain ⟨γ, _, X, Y, ha, hb, -, -⟩ := exists_ncard_eq.{u} a b 0
  exact ⟨γ, inferInstance, X, Y, ha, hb, by rwa [toFamily, toDet_apply, ha, hb]⟩

theorem toFamily_ofFamily (hC : Q.Conservative) (hK : Q.Constant) :
    (ofFamily Q).toFamily = Q := by
  funext α _ A B
  exact propext (ofFamily_iff hC hK α A B)

theorem toFamily_le_toFamily_iff {q r : NumberTree} :
    (q.toFamily : Det.Family.{u}) ≤ r.toFamily ↔ q ≤ r := by
  refine ⟨fun h a b hq ↦ ?_, fun h _ _ _ _ ↦ h _ _⟩
  obtain ⟨γ, _, X, Y, ha, hb, -, -⟩ := exists_ncard_eq.{u} a b 0
  have : r.toDet X Y := h γ ⟨inferInstance⟩ X Y (show q.toDet X Y by rwa [toDet_apply, ha, hb])
  rwa [toDet_apply, ha, hb] at this

/-- The conservative constant global determiner denotations are the trees of numbers, as
Boolean algebras: the tree of a meet, join or complement is the meet, join or complement of
the trees. -/
noncomputable def familyOrderIso :
    {Q : Det.Family.{u} // Q.Conservative ∧ Q.Constant} ≃o NumberTree where
  toFun Q := ofFamily Q.1
  invFun q := ⟨q.toFamily, conservative_toFamily q, constant_toFamily q⟩
  left_inv Q := Subtype.ext (toFamily_ofFamily Q.2.1 Q.2.2)
  right_inv := ofFamily_toFamily
  map_rel_iff' {Q Q'} := by
    change ofFamily Q.1 ≤ ofFamily Q'.1 ↔ Q.1 ≤ Q'.1
    conv_rhs => rw [← toFamily_ofFamily Q.2.1 Q.2.2, ← toFamily_ofFamily Q'.2.1 Q'.2.2]
    exact toFamily_le_toFamily_iff.symm

/-- The tree of a global determiner denotation that is asymmetric on every universe is
asymmetric. -/
theorem asymmetric_ofFamily (hC : Q.Conservative) (hK : Q.Constant)
    (h : ∀ (α : Type u) [Finite α], Std.Asymm (Q α)) : (ofFamily Q).Asymmetric := by
  intro a c b hac hbc
  obtain ⟨γ, _, X, Y, ha, hb, hc, -⟩ := exists_ncard_eq.{u} a b c
  have hXY := (ofFamily_iff hC hK γ X Y).1 (by rwa [ha, hb])
  have hYX := (ofFamily_iff hC hK γ Y X).1 (by rwa [hc, Set.inter_comm, hb])
  exact Std.Asymm.asymm X Y hXY hYX

/-- No conservative constant global determiner denotation is asymmetric on every universe unless
it is empty ([van-benthem-1984], Theorem 3.2.1). On a single universe
an asymmetric conservative permutation-invariant denotation can be nonempty. -/
theorem _root_.Quantifier.Det.Family.not_apply_of_asymm (hC : Q.Conservative)
    (hK : Q.Constant) (h : ∀ (α : Type u) [Finite α], Std.Asymm (Q α)) (α : Type u) [Finite α]
    (A B : Set α) : ¬ Q α A B := by
  rw [← ofFamily_iff hC hK, (asymmetric_ofFamily hC hK h).eq_bot]
  exact id

end Family

/-! ### Relativization

A determiner restricts the universe of quantification to its restrictor, and this is what makes
it conservative and extensional: the conservative constant global determiner denotations are
exactly the relativizations of the isomorphism-closed global quantifiers, and a quantifier and
its relativization are decided by the same tree. -/

section Relativization

open Det

variable {Q : Quantifier.Family.{u}} {D : Det.Family.{u}}

/-- A relativized quantifier is conservative, since it sees only the part of the scope inside the
restrictor. -/
theorem _root_.Quantifier.Family.conservative_rel (Q : Quantifier.Family.{u}) :
    Q.rel.Conservative := fun _ _ A B ↦ by
  show Q A (Subtype.val ⁻¹' B) ↔ Q A (Subtype.val ⁻¹' (A ∩ B))
  rw [Set.preimage_inter, Subtype.coe_preimage_self, Set.univ_inter]

/-- The relativization of an isomorphism-closed quantifier is constant. -/
theorem _root_.Quantifier.Family.Isom.constant_rel (h : Q.Isom) : Q.rel.Constant := by
  intro α β _ _ f A B hA _
  refine h (Equiv.ofBijective (fun x : ↥(f ⁻¹' A) ↦ (⟨f x, x.2⟩ : ↥A)) ⟨fun x y hxy ↦
    Subtype.ext (f.injective (congrArg Subtype.val hxy)), fun y ↦ ?_⟩) (Subtype.val ⁻¹' B)
  obtain ⟨x, hx⟩ := hA y.2
  exact ⟨⟨x, show f x ∈ A from hx ▸ y.2⟩, Subtype.ext hx⟩

/-- The quantifier of a global determiner denotation at the universe: the denotation with the
whole universe as its restrictor. -/
def _root_.Quantifier.Det.Family.atUniv (D : Det.Family.{u}) : Quantifier.Family.{u} :=
  fun α _ ↦ D α Set.univ

theorem _root_.Quantifier.Det.Family.Isom.atUniv (h : D.Isom) : D.atUniv.Isom :=
  fun _ _ _ _ e B ↦ h e Set.univ B

/-- A conservative constant global determiner denotation is the relativization of its quantifier
at the universe. -/
theorem _root_.Quantifier.Det.Family.rel_atUniv (hC : D.Conservative) (hK : D.Constant) :
    D.atUniv.rel = D := by
  funext α _ A B
  refine propext ((Iff.of_eq ?_).trans ((hK (Function.Embedding.subtype (· ∈ A)) A (A ∩ B)
    (by simp) (by simp)).trans (hC α A B).symm))
  simp only [Det.Family.atUniv, Quantifier.Family.rel, Function.Embedding.coe_subtype,
    Set.preimage_inter, Subtype.coe_preimage_self, Set.univ_inter]

/-- An isomorphism-closed quantifier is the quantifier at the universe of its relativization. -/
theorem _root_.Quantifier.Family.Isom.atUniv_rel (h : Q.Isom) : Q.rel.atUniv = Q := by
  funext α _ B
  exact propext (h (Equiv.Set.univ α) B)

/-- Relativization is an order isomorphism from the isomorphism-closed global quantifiers onto the
conservative constant global determiner denotations. -/
noncomputable def relOrderIso :
    {Q : Quantifier.Family.{u} // Q.Isom} ≃o {D : Det.Family.{u} // D.Conservative ∧ D.Constant}
    where
  toFun Q := ⟨Q.1.rel, Q.1.conservative_rel, Q.2.constant_rel⟩
  invFun D := ⟨D.1.atUniv, D.2.2.isom.atUniv⟩
  left_inv Q := Subtype.ext Q.2.atUniv_rel
  right_inv D := Subtype.ext (Det.Family.rel_atUniv D.2.1 D.2.2)
  map_rel_iff' {Q Q'} := by
    change Q.1.rel ≤ Q'.1.rel ↔ Q.1 ≤ Q'.1
    rw [Det.Family.le_def, Quantifier.Family.le_def]
    refine ⟨fun h α _ B hB ↦ ?_, fun h α _ A B ↦ h A (Subtype.val ⁻¹' B)⟩
    rw [← Q'.2.atUniv_rel]
    rw [← Q.2.atUniv_rel] at hB
    exact h α Set.univ B hB

/-- An isomorphism-closed global quantifier holds of `B` according to `|Bᶜ|` and `|B|` alone, by
the tree of its relativization, so a quantifier and its relativization have the same numerical
relation. -/
theorem _root_.Quantifier.Family.Isom.apply_iff (h : Q.Isom) (α : Type u) [Finite α]
    (B : Set α) : Q α B ↔ ofFamily Q.rel Bᶜ.ncard B.ncard := by
  have key := ofFamily_iff Q.conservative_rel h.constant_rel α Set.univ B
  rw [Set.univ_inter, ← Set.compl_eq_univ_sdiff] at key
  rw [key]
  conv_lhs => rw [← h.atUniv_rel]
  rfl

/-- Some finite universe has a set with `b` members and `a` individuals outside it. -/
theorem exists_ncard_compl_eq (a b : ℕ) :
    ∃ (γ : Type u) (_ : Finite γ) (B : Set γ), Bᶜ.ncard = a ∧ B.ncard = b := by
  obtain ⟨γ, _, X, Y, ha, hb, hc, hu⟩ := exists_ncard_eq.{u} a b 0
  have hYX : Y ⊆ X := Set.sdiff_eq_empty.1 ((Set.ncard_eq_zero (Set.toFinite _)).1 hc)
  have hX : X = Set.univ := by
    rw [← Set.union_eq_left.2 hYX]; exact Set.compl_empty_iff.1 hu
  refine ⟨γ, inferInstance, Y, ?_, ?_⟩
  · rw [Set.compl_eq_univ_sdiff, ← hX]; exact ha
  · rw [← Set.inter_eq_right.2 hYX]; exact hb

/-- An isomorphism-closed global quantifier is the global determiner denotation of the tree of
its relativization, with the universe as the restrictor. -/
theorem _root_.Quantifier.Family.Isom.eq_atUniv_toFamily (h : Q.Isom) :
    Q = (ofFamily Q.rel).toFamily.atUniv := by
  rw [toFamily_ofFamily Q.conservative_rel h.constant_rel, h.atUniv_rel]

/-- An isomorphism-closed global quantifier that satisfies extension holds of a set according to
its size alone, on whatever universe. -/
theorem _root_.Quantifier.Family.Isom.iff_of_ncard_eq (h : Q.Isom) (hE : Q.Ext) {α β : Type u}
    [Finite α] [Finite β] {B : Set α} {C : Set β} (hBC : B.ncard = C.ncard) : Q α B ↔ Q β C := by
  have hB := hE B B subset_rfl
  have hC := hE C C subset_rfl
  rw [Subtype.coe_preimage_self] at hB hC
  rw [← hB, ← hC]
  obtain ⟨e⟩ : Nonempty (↥B ≃ ↥C) := Finite.card_eq.1 hBC
  simpa using h e Set.univ

/-- An isomorphism-closed global quantifier satisfies extension if and only if the tree of its
relativization is cardinal. -/
theorem _root_.Quantifier.Family.Isom.ext_iff (h : Q.Isom) :
    Q.Ext ↔ ofFamily Q.rel ∈ Set.range cardinal := by
  rw [mem_range_cardinal_iff]
  refine ⟨fun hE a b ↦ ?_, fun hq β _ M B hB ↦ ?_⟩
  · obtain ⟨γ, _, B, ha, hb⟩ := exists_ncard_compl_eq.{u} a b
    obtain ⟨γ', _, B', ha', hb'⟩ := exists_ncard_compl_eq.{u} 0 b
    calc ofFamily Q.rel a b ↔ Q γ B := by rw [h.apply_iff, ha, hb]
      _ ↔ Q γ' B' := h.iff_of_ncard_eq hE (hb.trans hb'.symm)
      _ ↔ ofFamily Q.rel 0 b := by rw [h.apply_iff, ha', hb']
  · rw [h.apply_iff, h.apply_iff, hq, hq Bᶜ.ncard,
      Set.ncard_preimage_of_injective_subset_range Subtype.val_injective (by simpa using hB)]

/-- An isomorphism-closed global quantifier is monotone on every universe if and only if the tree
of its relativization is scope monotone. -/
theorem _root_.Quantifier.Family.Isom.monotone_iff (h : Q.Isom) :
    (∀ (α : Type u) [Finite α], Monotone (Q α)) ↔ (ofFamily Q.rel).ScopeMonotone := by
  refine ⟨fun hm a b hq ↦ ?_, fun hq α _ ↦ ?_⟩
  · obtain ⟨γ, _, B, ha, hb⟩ := exists_ncard_compl_eq.{u} (a + 1) b
    obtain ⟨x, hx⟩ : Bᶜ.Nonempty := (Set.ncard_pos (Set.toFinite _)).1 (by omega)
    have hQ : Q γ (insert x B) :=
      hm γ (Set.subset_insert x B) ((h.apply_iff γ B).2 (by rwa [ha, hb]))
    have h₁ : (insert x B).ncard = b + 1 := by rw [Set.ncard_insert_of_notMem hx, hb]
    have h₂ : (insert x B)ᶜ.ncard = a := by
      have := Set.ncard_add_ncard_compl (insert x B)
      have := Set.ncard_add_ncard_compl B
      omega
    have := (h.apply_iff γ _).1 hQ
    rwa [h₁, h₂] at this
  · rw [h.eq_atUniv_toFamily]
    exact hq.toDet Set.univ

end Relativization

end NumberTree

namespace Det

variable {α : Type*} {A B : Set α} {n : ℕ}

/-! ### The families of the canonical denotations

Each canonical denotation given on every finite universe, the readings a lexicon entry draws
on. Each is the global denotation of its tree, so each is conservative, extensional and closed
under isomorphism, as Peters and Westerståhl's universal for determiners requires. -/

namespace Family

/-- `Family.every` is `every` on every finite universe. -/
def every : Family.{u} := fun _ _ ↦ Det.every
/-- `Family.some` is `Det.some` on every finite universe. -/
def some : Family.{u} := fun _ _ ↦ Det.some
/-- `Family.no` is `no` on every finite universe. -/
def no : Family.{u} := fun _ _ ↦ Det.no
/-- `Family.most` is `most` on every finite universe. -/
def most : Family.{u} := fun _ _ ↦ Det.most
/-- `Family.few` is `few` on every finite universe. -/
def few : Family.{u} := fun _ _ ↦ Det.few
/-- `Family.half` is `half` on every finite universe. -/
def half : Family.{u} := fun _ _ ↦ Det.half
/-- `Family.both` is `both` on every finite universe. -/
def both : Family.{u} := fun _ _ ↦ Det.both
/-- `Family.neither` is `neither` on every finite universe. -/
def neither : Family.{u} := fun _ _ ↦ Det.neither
/-- `Family.atLeast n` is `atLeast n` on every finite universe. -/
def atLeast (n : ℕ) : Family.{u} := fun _ _ ↦ Det.atLeast n
/-- `Family.exactly n` is `exactly n` on every finite universe. -/
def exactly (n : ℕ) : Family.{u} := fun _ _ ↦ Det.exactly n

theorem every_eq_toFamily : every.{u} = NumberTree.all.toFamily := by
  funext _ _; exact every_eq_toDet_all

theorem some_eq_toFamily : some.{u} = NumberTree.some.toFamily := by
  funext _ _; exact some_eq_toDet_some

theorem no_eq_toFamily : no.{u} = NumberTree.no.toFamily := by
  funext _ _; exact no_eq_toDet_no

theorem most_eq_toFamily : most.{u} = NumberTree.most.toFamily := rfl

theorem few_eq_toFamily : few.{u} = NumberTree.few.toFamily := rfl

theorem half_eq_toFamily : half.{u} = NumberTree.half.toFamily := rfl

theorem both_eq_toFamily : both.{u} = NumberTree.both.toFamily := rfl

theorem neither_eq_toFamily : neither.{u} = NumberTree.neither.toFamily := rfl

theorem atLeast_eq_toFamily (n : ℕ) : atLeast.{u} n = (NumberTree.atLeast n).toFamily := rfl

theorem exactly_eq_toFamily (n : ℕ) : exactly.{u} n = (NumberTree.exactly n).toFamily := rfl

theorem some_ne_every : some.{u} ≠ every.{u} := fun h ↦ by
  have := congrArg (fun d : Family.{u} ↦ d PUnit ∅ ∅) h
  simp [some, every, Det.some, Det.every] at this

theorem some_ne_no : some.{u} ≠ no.{u} := fun h ↦ by
  have := congrArg (fun d : Family.{u} ↦ d PUnit Set.univ Set.univ) h
  simp [some, no, Det.some, Det.no] at this

theorem no_ne_every : no.{u} ≠ every.{u} := fun h ↦ by
  have := congrArg (fun d : Family.{u} ↦ d PUnit Set.univ Set.univ) h
  simp [no, every, Det.no, Det.every] at this

theorem most_ne_every : most.{u} ≠ every.{u} := fun h ↦ by
  have := congrArg (fun d : Family.{u} ↦ d PUnit ∅ ∅) h
  simp [most, every, Det.every, most_apply] at this

theorem few_ne_every : few.{u} ≠ every.{u} := fun h ↦ by
  have := congrArg (fun d : Family.{u} ↦ d PUnit ∅ ∅) h
  simp [few, every, Det.every, few_apply] at this

@[simp]
theorem compl_some : some.{u}ᶜ = no.{u} := by
  funext _ _; exact Det.compl_some

@[simp]
theorem compl_no : no.{u}ᶜ = some.{u} := by
  rw [← compl_some, compl_compl]

end Family

/-! ### Determiner symbols -/

/-- A determiner symbol names one of the canonical denotations, after the basic determiner
symbols from which [barwise-cooper-1981]'s logic L(GQ) builds its quantifiers. The eight symbols
are ours: Barwise and Cooper's logical determiner symbols are *some*, *every*, *no*, *both*,
*neither*, the numerals and *the n*, their non-logical ones include *most* and *few*, and they
have no *half*; here every symbol has one denotation, the global denotation of its tree. -/
inductive Symbol where
  | every | some | no | most | few | half | both | neither
  deriving DecidableEq, Repr, Fintype

namespace Symbol

/-- The tree of numbers a symbol denotes. -/
def numberTree : Symbol → NumberTree
  | .every => NumberTree.all
  | .some => NumberTree.some
  | .no => NumberTree.no
  | .most => NumberTree.most
  | .few => NumberTree.few
  | .half => NumberTree.half
  | .both => NumberTree.both
  | .neither => NumberTree.neither

/-- A symbol denotes its canonical denotation, the global denotation of its tree
(`denote_eq_toFamily`). -/
@[simp] def denote : Symbol → Family.{u}
  | .every => Family.every
  | .some => Family.some
  | .no => Family.no
  | .most => Family.most
  | .few => Family.few
  | .half => Family.half
  | .both => Family.both
  | .neither => Family.neither

theorem denote_eq_toFamily (s : Symbol) : (s.denote : Family.{u}) = s.numberTree.toFamily := by
  cases s
  exacts [Family.every_eq_toFamily, Family.some_eq_toFamily, Family.no_eq_toFamily, rfl, rfl,
    rfl, rfl, rfl]

theorem numberTree_injective : Function.Injective numberTree := by
  intro s t h
  have h₀₀ := congrFun (congrFun h 0) 0
  have h₁₀ := congrFun (congrFun h 1) 0
  have h₀₁ := congrFun (congrFun h 0) 1
  have h₁₁ := congrFun (congrFun h 1) 1
  have h₀₂ := congrFun (congrFun h 0) 2
  have h₂₀ := congrFun (congrFun h 2) 0
  cases s <;> cases t <;> simp_all [numberTree, NumberTree.all, NumberTree.some, NumberTree.no,
    NumberTree.most, NumberTree.few, NumberTree.half, NumberTree.both, NumberTree.neither]

/-- Distinct symbols denote distinct quantifiers. -/
theorem denote_injective : Function.Injective (denote : Symbol → Family.{u}) := fun s t h ↦
  numberTree_injective <| by
    rw [← NumberTree.ofFamily_toFamily.{u} s.numberTree, ← NumberTree.ofFamily_toFamily.{u}
      t.numberTree, ← denote_eq_toFamily, ← denote_eq_toFamily, h]

theorem conservative_denote (s : Symbol) : (s.denote : Family.{u}).Conservative :=
  s.denote_eq_toFamily ▸ NumberTree.conservative_toFamily _

theorem constant_denote (s : Symbol) : (s.denote : Family.{u}).Constant :=
  s.denote_eq_toFamily ▸ NumberTree.constant_toFamily _

theorem ext_denote (s : Symbol) : (s.denote : Family.{u}).Ext := s.constant_denote.ext

theorem isom_denote (s : Symbol) : (s.denote : Family.{u}).Isom := s.constant_denote.isom

end Symbol

end Det

end Quantifier
