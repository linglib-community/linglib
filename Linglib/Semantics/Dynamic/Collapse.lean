module

public import Linglib.Semantics.Dynamic.Category
public import Linglib.Semantics.Dynamic.Update
public import Mathlib.Data.Set.Functor
public import Mathlib.CategoryTheory.Category.KleisliCat
public import Mathlib.CategoryTheory.Category.RelCat
public import Mathlib.Order.Hom.CompleteLattice

/-!
# The one-object collapse and the Kleisli reading

The descent from indexed dynamic semantics to level 0 — the relational
algebra of procedures over a single state space
([muskens-van-benthem-visser-2011]'s "Dynamic Constants as Operators in
Relational Algebra") — and the canonicity of level 0 itself. An update
curries to a Kleisli arrow `S → Set S` of the powerset monad, so
sequencing is Kleisli composition, the trivial test is
`pure`, and the image is `bind` ([charlow-2014]'s monadic view of dynamic
semantics, as theorems); the image is then an equivalence onto the
completely-join-preserving transformers (`sSupHom`), so the transformer
algebra is the suplattice completion of the relational one and the
non-distributive tests (`might`, `must`) are exactly the residue.
Categorically, `RelCat ≌ KleisliCat Set`, and the indexed tower reads
`Ctx ⥤ RelCat ≌ KleisliCat Set ↪ suplattice endomaps`, every arrow
canonical. The collapsed state space at `X` is the `X`-stratum of root
states, classified by `Possibility.domainEquiv`/`State.uniformEquiv`, and
the relational action computes the root-state CCP through that
classification (`Transition.uniformEquiv_applyState`) — the extraction
of a relational meaning from a DRT-style one, as a morphism
([visser-vermeulen-1996]).

The powerset monad is one column of the effect view of dynamic semantics
([moggi-1991], [shan-2001], [bumford-charlow-2026]): a framework's update
algebra is the Kleisli algebra of its chosen effect. Partiality is the
`Part` column (`Partial.lean`'s `seq_eq_kleisliComp`); probabilistic and
continuation-based systems choose further effects.

## Main definitions

- `Ctx.collapse`: the functor `Ctx W M V ⥤ RelCat` sending a context to
  its possibility space and a transition to its world-threaded relation.
- `imageEquiv`: `Update S ≃ sSupHom (Set S) (Set S)`.
- `relCatEquivKleisli`: `RelCat ≌ KleisliCat Set`. [UPSTREAM] candidate —
  pure category theory, absent from mathlib.

## Main results

- `Ctx.collapse_faithful`: a transition is recoverable from its collapsed
  relation; what the collapse forgets is the base-indexing of objects.
- `comp_eq_kleisliComp`, `id_eq_pure`, `image_eq_bind`: the monadic
  reading of the update algebra.
- `isDistributive_iff_map_sSup`, `imageEquiv_comp`: distributive CCPs are
  exactly the completely-join-preserving maps, and `SetRel.image`/`lower` is an
  equivalence onto them, sending sequencing to composition.

## Implementation notes

The predecessor collapsed through base-agreement classes of total
assignments — the quotient was forced because the untyped `toUpdate` sent
identities to agreement-on-`X` rather than equality. Typed transitions
are unital, so the collapse lands in `RelCat` directly, with no setoid.

## References

- [muskens-van-benthem-visser-2011], [charlow-2014]
- [moggi-1991], [shan-2001], [bumford-charlow-2026]
- [muskens-1996], [groenendijk-stokhof-1991]
-/

@[expose] public section

namespace DynamicSemantics

open CategoryTheory

/-! ### The collapse to `RelCat` -/

namespace Ctx

variable {W M V : Type*} {X Y Z : Ctx W M V}

/-- **The one-object collapse**: forget the base-indexing, sending a
context to its possibility space and a transition to its world-threaded
relation. Unital by typing — no quotient needed. -/
def collapse (W M V : Type*) : Ctx W M V ⥤ RelCat where
  obj X := W × (X.base → M)
  map {X Y} u := .ofRel {p | p.1.1 = p.2.1 ∧ u.t.rel p.1.1 p.1.2 p.2.2}
  map_id X := by
    apply RelCat.Hom.ext
    ext ⟨⟨w, e⟩, ⟨w', e'⟩⟩
    show (w = w' ∧ e = e') ↔ _
    constructor
    · rintro ⟨rfl, rfl⟩
      exact SetRel.mem_id.mpr rfl
    · intro h
      exact Prod.ext_iff.mp (SetRel.mem_id.mp h)
  map_comp {X Y Z} u v := by
    apply RelCat.Hom.ext
    ext ⟨⟨w, e⟩, ⟨w'', e''⟩⟩
    constructor
    · rintro ⟨hw, k, huk, hkv⟩
      exact SetRel.prodMk_mem_comp
        (show ((w, e), (w, k)) ∈ _ from ⟨rfl, huk⟩)
        (show ((w, k), (w'', e'')) ∈ _ from ⟨hw, hkv⟩)
    · rintro ⟨⟨w', k⟩, ⟨hw1, huk⟩, hw2, hkv⟩
      refine ⟨hw1.trans hw2, k, huk, ?_⟩
      rw [hw1]
      exact hkv

/-- The collapse is faithful: a transition is recoverable from its
world-threaded relation. What the collapse forgets is only the
base-indexing of the objects. -/
instance collapse_faithful : (collapse W M V).Faithful where
  map_injective {X Y} {u v} h := by
    have hs : ∀ (w : W) e e', u.t.rel w e e' ↔ v.t.rel w e e' := by
      intro w e e'
      have h2 : (w = w ∧ u.t.rel w e e') ↔ (w = w ∧ v.t.rel w e e') :=
        Set.ext_iff.mp (congrArg RelCat.Hom.rel h) ((w, e), (w, e'))
      exact ⟨fun hr => (h2.mp ⟨rfl, hr⟩).2, fun hr => (h2.mpr ⟨rfl, hr⟩).2⟩
    refine Hom.ext (Transition.ext ?_)
    funext w e e'
    exact propext (hs w e e')

end Ctx

/-! ### The Set-monad reading -/

open Update SetRel

attribute [local instance] Set.monad

universe u

variable {S : Type*}

/-- Sequencing is Kleisli composition for the powerset monad, an update
being the Kleisli arrow that sends a state to its image. -/
theorem comp_eq_kleisliComp (D₁ D₂ : Update S) :
    (fun i => (D₁ ○ D₂).image {i}) = (fun i => D₁.image {i}) >=> fun i => D₂.image {i} :=
  funext fun i => Set.ext fun j => by
    rw [Bind.kleisliRight, Set.bind_def, Set.mem_iUnion₂]
    simp only [SetRel.mem_image, Set.mem_singleton_iff, exists_eq_left, SetRel.mem_comp,
      exists_prop]

/-- The trivial test is `pure`. -/
theorem id_eq_pure : (fun i => (SetRel.id : Update S).image {i}) = fun i => (pure i : Set S) :=
  funext fun _ => SetRel.image_id _

/-- The relational image is `bind`, the monad's extension operator. -/
theorem image_eq_bind (R : Update S) (σ : Set S) : R.image σ = σ >>= fun i => R.image {i} :=
  Set.ext fun j => by
    rw [Set.bind_def, Set.mem_iUnion₂]
    simp only [SetRel.mem_image, Set.mem_singleton_iff, exists_eq_left, exists_prop]

/-! ### Distributivity is complete join preservation -/

/-- A CCP is distributive iff it preserves arbitrary joins of states. -/
theorem isDistributive_iff_map_sSup (φ : CCP S) :
    CCP.IsDistributive φ ↔ ∀ T : Set (Set S), φ (sSup T) = sSup (φ '' T) := by
  simp only [Set.sSup_eq_sUnion]
  constructor
  · intro h T
    ext j
    constructor
    · intro hj
      rw [h] at hj
      obtain ⟨i, ⟨t, ht, hit⟩, hji⟩ := hj
      refine ⟨φ t, ⟨t, ht, rfl⟩, ?_⟩
      rw [h t]
      exact ⟨i, hit, hji⟩
    · rintro ⟨_, ⟨t, ht, rfl⟩, hjt⟩
      rw [h t] at hjt
      obtain ⟨i, hit, hji⟩ := hjt
      rw [h]
      exact ⟨i, ⟨t, ht, hit⟩, hji⟩
  · intro h s
    have hs : s = ⋃₀ ((fun i => ({i} : Set S)) '' s) := by
      ext i
      simp
    ext j
    constructor
    · intro hj
      rw [hs, h] at hj
      obtain ⟨_, ⟨_, ⟨i, hi, rfl⟩, rfl⟩, hji⟩ := hj
      exact ⟨i, hi, hji⟩
    · rintro ⟨i, hi, hji⟩
      rw [hs, h]
      exact ⟨φ {i}, ⟨{i}, ⟨i, hi, rfl⟩, rfl⟩, hji⟩

/-- The relational algebra is exactly the completely-join-preserving
fragment of the transformer algebra: `SetRel.image`/`lower` as an equivalence
onto `sSupHom`. -/
def imageEquiv : Update S ≃ sSupHom (Set S) (Set S) where
  toFun R := ⟨R.image, (isDistributive_iff_map_sSup _).mp (image_isDistributive R)⟩
  invFun f := CCP.lower f
  left_inv := lower_image
  right_inv f := sSupHom.ext fun σ =>
    congrFun (CCP.image_lower _ ((isDistributive_iff_map_sSup _).mpr f.map_sSup')) σ

/-- The equivalence sends sequencing to composition (diagrammatic order):
the transformer monoid restricts to the relational one. -/
theorem imageEquiv_comp (D₁ D₂ : Update S) :
    (imageEquiv (D₁ ○ D₂) : Set S → Set S) =
      (imageEquiv D₂ : Set S → Set S) ∘ (imageEquiv D₁ : Set S → Set S) :=
  funext fun _ => SetRel.image_comp ..

/-! ### `RelCat ≌ KleisliCat Set` -/

/-- [UPSTREAM] Relations to Kleisli arrows of the powerset monad: curry. -/
def relCatToKleisli : RelCat.{u} ⥤ KleisliCat Set where
  obj X := X
  map f := fun x => {y | (x, y) ∈ f.rel}
  map_id X := funext fun x => by
    ext y
    show (x, y) ∈ SetRel.id ↔ y ∈ ({x} : Set X)
    simp [SetRel.id, eq_comm]
  map_comp {X Y Z} f g := funext fun x => by
    ext z
    show (x, z) ∈ SetRel.comp f.rel g.rel ↔ _
    simp only [SetRel.comp, KleisliCat.comp_def,
      Set.bind_def, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]

/-- [UPSTREAM] Kleisli arrows of the powerset monad to relations:
uncurry. -/
def kleisliToRelCat : KleisliCat Set ⥤ RelCat.{u} where
  obj X := X
  map f := .ofRel {p | p.2 ∈ f p.1}
  map_id X := by
    apply RelCat.Hom.ext
    ext ⟨x, y⟩
    show y ∈ ({x} : Set X) ↔ (x, y) ∈ SetRel.id
    simp [SetRel.id, eq_comm]
  map_comp {X Y Z} f g := by
    apply RelCat.Hom.ext
    ext ⟨x, z⟩
    simp only [KleisliCat.comp_def, Set.bind_def, Set.mem_iUnion,
      Set.mem_ofPred_eq, exists_prop]
    rfl

/-- [UPSTREAM] The category of relations is the Kleisli category of the
powerset monad. -/
def relCatEquivKleisli : RelCat.{u} ≌ KleisliCat Set :=
  CategoryTheory.Equivalence.mk relCatToKleisli kleisliToRelCat
  (NatIso.ofComponents (fun X => Iso.refl X) (by
    intro X Y f
    apply RelCat.Hom.ext
    ext ⟨x, y⟩
    simp only [relCatToKleisli, kleisliToRelCat, Functor.id_map,
      Functor.comp_map, Iso.refl_hom, RelCat.Hom.rel_comp, RelCat.Hom.rel_id]
    constructor
    · rintro ⟨b, hb, he⟩
      obtain rfl : b = y := he
      exact ⟨x, rfl, hb⟩
    · rintro ⟨b, he, hb⟩
      obtain rfl : x = b := he
      exact ⟨y, hb, rfl⟩))
  (NatIso.ofComponents (fun X => Iso.refl X) (by
    intro X Y f
    funext x
    ext y
    simp only [relCatToKleisli, kleisliToRelCat, Functor.id_map,
      Functor.comp_map, Iso.refl_hom, KleisliCat.comp_def, KleisliCat.id_def,
      Set.bind_def, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨x, rfl, hi⟩
    · rintro ⟨i, hi, hyf⟩
      obtain rfl : i = x := hi
      exact ⟨y, hyf, rfl⟩))

end DynamicSemantics
