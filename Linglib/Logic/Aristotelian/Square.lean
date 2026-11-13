module

public import Linglib.Logic.Aristotelian.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Lattice.Prod
public import Mathlib.Order.Hom.BoundedLattice
public import Mathlib.Tactic.DeriveFintype

/-!
# The square of opposition

The square of opposition, in the form Horn surveys, has four corners `A`, `E`, `I`, `O` in a
Boolean algebra, with contradictory diagonals and universals `A`, `E` that cannot both hold. A
square with these relations is [determined by its two universals](##squareRelations_iff), and in
it [`A` entails `I`](##SquareRelations.subalternAI), [`E` entails
`O`](##SquareRelations.subalternEO), and [`I` and `O` cannot both
fail](##SquareRelations.subcontrIO). Its instances for generalized quantifiers and for modals
live with those theories.

Such a square divides its algebra into three pairwise disjoint parts, `E`, `A`, and between them
the conjunction `I ⊓ O` of the two particulars: the vertices of Horn's triangle of opposition.
Horn traces this trichotomy to De Morgan and to Jespersen's tripartition into *all*, *some* and
*none*, whose middle term is neither the `I` nor the `O` corner but their conjunction; modally
the vertices are the impossible, the contingent and the necessary. The middle vertex decides how
much of the square is left: `A` and `E` are [contrary](##SquareRelations.isContrary_AE_iff), `I`
and `O` [subcontrary](##SquareRelations.isSubcontrary_IO_iff) and the two entailments
[strict](##SquareRelations.lt_AI_iff) exactly when it is not `⊥`, and when no vertex is `⊥` the
three are [pairwise contrary](##SquareRelations.pairwise_isContrary_triangle).

Read as sets of vertices, the corners form a square in `Finset Triangle`, and it is the generic
one: the squares of a Boolean algebra `α` that satisfy the relations [correspond
to](##squareRelationsEquivHom) the bounded lattice homomorphisms `Finset Triangle → α`, each
square being the image of that one.

## Implementation notes

`SquareRelations` asks only that `A` and `E` be disjoint, where Horn's contraries may also both
fail; that half is `I ⊓ O ≠ ⊥` and is left to the theorems that need it, so that a square whose
restrictor has one member, or whose modal base settles the prejacent, is still a square.

The vertices are ordered by the affirmative corners they lie in, which is the scale
*none* < *some but not all* < *all*.

## References

* [horn-2001]
-/

@[expose] public section

namespace Aristotelian

variable {F α β γ : Type*}

/-! ### The square -/

/-- A square of opposition has four corners. -/
@[ext]
structure Square (α : Type*) where
  /-- `A` is the universal affirmative corner (*every*, `□p`, `Bel p`). -/
  A : α
  /-- `E` is the universal negative corner (*no*, `□¬p`, `Bel ¬p`). -/
  E : α
  /-- `I` is the particular affirmative corner (*some*, `◇p`). -/
  I : α
  /-- `O` is the particular negative corner (*not every*, `¬□p`, `¬Bel p`). -/
  O : α

/-- The vertices of the triangle of opposition, in scale order. -/
inductive Triangle where
  /-- *None*, the universal negative `E`. -/
  | none
  /-- *Some but not all*, the conjunction of the two particulars `I` and `O`. -/
  | someNotAll
  /-- *All*, the universal affirmative `A`. -/
  | all
  deriving DecidableEq, Repr, Fintype

namespace Square

/-- The image of a square under a map of its corners. -/
@[simps]
def map (f : α → β) (sq : Square α) : Square β := ⟨f sq.A, f sq.E, f sq.I, f sq.O⟩

@[simp] theorem map_id (sq : Square α) : sq.map id = sq := rfl

@[simp] theorem map_map (g : β → γ) (f : α → β) (sq : Square α) :
    (sq.map f).map g = sq.map (g ∘ f) := rfl

/-- The inner negation of a square negates what its corners quantify over, exchanging `A` with `E`
and `I` with `O`: *not every* is *some* over the negated scope. -/
@[simps]
def inner (sq : Square α) : Square α := ⟨sq.E, sq.A, sq.O, sq.I⟩

@[simp] theorem inner_inner (sq : Square α) : sq.inner.inner = sq := rfl

theorem map_inner (f : α → β) (sq : Square α) : sq.inner.map f = (sq.map f).inner := rfl

/-- The square on two universals has their complements for particulars. -/
@[simps]
def ofUniversals [Compl α] (a e : α) : Square α := ⟨a, e, eᶜ, aᶜ⟩

/-- The element of a square at a vertex of its triangle. -/
def triangle [Min α] (sq : Square α) : Triangle → α
  | .none => sq.E
  | .someNotAll => sq.I ⊓ sq.O
  | .all => sq.A

theorem map_triangle [Min α] [Min β] [FunLike F α β] [InfHomClass F α β] (f : F) (sq : Square α)
    (t : Triangle) : (sq.map f).triangle t = f (sq.triangle t) := by
  cases t <;> simp [triangle]

end Square

/-! ### Square relations -/

variable [BooleanAlgebra α] {sq : Square α}

/-- A square over a Boolean algebra satisfies the relations of the square when both diagonals
are contradictory and the universals cannot both hold. Subalternation and subcontrariety follow
(`subalternAI`, `subalternEO`, `subcontrIO`). -/
structure SquareRelations (sq : Square α) : Prop where
  /-- `A` and `O` are contradictories. -/
  contradAO : IsCompl sq.A sq.O
  /-- `E` and `I` are contradictories. -/
  contradEI : IsCompl sq.E sq.I
  /-- `A` and `E` cannot both hold. -/
  contraryAE : Disjoint sq.A sq.E

namespace SquareRelations

theorem of_disjoint (hI : sq.I = sq.Eᶜ) (hO : sq.O = sq.Aᶜ) (h : Disjoint sq.A sq.E) :
    SquareRelations sq :=
  ⟨hO ▸ isCompl_compl, hI ▸ isCompl_compl, h⟩

/-- A square with the relations is the square on its universals. -/
theorem eq_ofUniversals (h : SquareRelations sq) : sq = .ofUniversals sq.A sq.E :=
  Square.ext rfl rfl h.contradEI.compl_eq.symm h.contradAO.compl_eq.symm

/-- `A` entails `I`. -/
theorem subalternAI (h : SquareRelations sq) : sq.A ≤ sq.I := by
  rw [h.contradEI.symm.eq_compl]
  exact le_compl_iff_disjoint_right.mpr h.contraryAE

/-- `E` entails `O`. -/
theorem subalternEO (h : SquareRelations sq) : sq.E ≤ sq.O := by
  rw [h.contradAO.symm.eq_compl]
  exact le_compl_iff_disjoint_right.mpr h.contraryAE.symm

/-- `I` and `O` cannot both fail. -/
theorem subcontrIO (h : SquareRelations sq) : Codisjoint sq.I sq.O := by
  rw [h.contradEI.symm.eq_compl, h.contradAO.symm.eq_compl, codisjoint_iff, ← compl_inf,
    disjoint_iff.mp h.contraryAE.symm, compl_bot]

/-- The relations of the square survive inner negation. -/
protected theorem inner (h : SquareRelations sq) : SquareRelations sq.inner :=
  ⟨h.contradEI, h.contradAO, h.contraryAE.symm⟩

/-- A bounded lattice homomorphism carries a square with the relations to one. -/
protected theorem map [BooleanAlgebra β] [FunLike F α β] [BoundedLatticeHomClass F α β]
    (h : SquareRelations sq) (f : F) : SquareRelations (sq.map f) :=
  ⟨h.contradAO.map f, h.contradEI.map f, h.contraryAE.map f⟩

end SquareRelations

/-- The square on two universals satisfies the relations exactly when they cannot both hold. -/
@[simp] theorem squareRelations_ofUniversals {a e : α} :
    SquareRelations (.ofUniversals a e) ↔ Disjoint a e :=
  ⟨fun h ↦ h.contraryAE, fun h ↦ .of_disjoint rfl rfl h⟩

/-- A square satisfies the relations exactly when it is the square on two universals that cannot
both hold. -/
theorem squareRelations_iff :
    SquareRelations sq ↔ Disjoint sq.A sq.E ∧ sq = .ofUniversals sq.A sq.E :=
  ⟨fun h ↦ ⟨h.contraryAE, h.eq_ofUniversals⟩,
    fun ⟨h, hsq⟩ ↦ hsq ▸ squareRelations_ofUniversals.2 h⟩

/-! ### The middle vertex -/

namespace SquareRelations

theorem inf_IO_eq (h : SquareRelations sq) : sq.I ⊓ sq.O = (sq.A ⊔ sq.E)ᶜ := by
  rw [h.contradEI.symm.eq_compl, h.contradAO.symm.eq_compl, compl_sup, inf_comm]

theorem I_sdiff_O (h : SquareRelations sq) : sq.I \ sq.O = sq.A := by
  rw [sdiff_eq, ← h.contradAO.eq_compl, inf_eq_right.2 h.subalternAI]

theorem I_sdiff_A (h : SquareRelations sq) : sq.I \ sq.A = sq.I ⊓ sq.O := by
  rw [sdiff_eq, h.contradAO.compl_eq]

theorem inf_IO_sup_A (h : SquareRelations sq) : sq.I ⊓ sq.O ⊔ sq.A = sq.I := by
  rw [← h.I_sdiff_A, sdiff_sup_cancel h.subalternAI]

theorem inf_IO_sup_E (h : SquareRelations sq) : sq.I ⊓ sq.O ⊔ sq.E = sq.O := by
  rw [inf_comm]
  exact h.inner.inf_IO_sup_A

/-- `A` entails `I` strictly exactly when the two particulars can hold together. -/
theorem lt_AI_iff (h : SquareRelations sq) : sq.A < sq.I ↔ sq.I ⊓ sq.O ≠ ⊥ := by
  rw [lt_iff_le_not_ge, and_iff_right h.subalternAI, ne_eq, ← disjoint_iff,
    ← le_compl_iff_disjoint_right, h.contradAO.symm.compl_eq]

/-- `E` entails `O` strictly exactly when the two particulars can hold together. -/
theorem lt_EO_iff (h : SquareRelations sq) : sq.E < sq.O ↔ sq.I ⊓ sq.O ≠ ⊥ := by
  rw [inf_comm]
  exact h.inner.lt_AI_iff

/-- The universals are contrary, able both to fail, exactly when the two particulars can hold
together. -/
theorem isContrary_AE_iff (h : SquareRelations sq) :
    IsContrary sq.A sq.E ↔ sq.I ⊓ sq.O ≠ ⊥ := by
  rw [isContrary_iff_lt_compl, h.contradEI.compl_eq, h.lt_AI_iff]

/-- The particulars are subcontrary exactly when they can hold together. -/
theorem isSubcontrary_IO_iff (h : SquareRelations sq) :
    IsSubcontrary sq.I sq.O ↔ sq.I ⊓ sq.O ≠ ⊥ := by
  rw [IsSubcontrary, and_iff_left h.subcontrIO, disjoint_iff]

end SquareRelations

/-! ### The corners as sets of vertices -/

namespace Triangle

/-- The corners of the square, each given as the set of vertices at which it holds. -/
def corners : Square (Finset Triangle) :=
  ⟨{.all}, {.none}, {.someNotAll, .all}, {.none, .someNotAll}⟩

/-- The element of `corners` at each vertex is that vertex's singleton. -/
theorem triangle_corners (t : Triangle) : corners.triangle t = {t} := by
  cases t <;> decide

/-- The corners as sets of vertices satisfy the relations of the square. -/
theorem squareRelations_corners : SquareRelations corners :=
  .of_disjoint (by decide) (by decide) (by decide)

/-- A vertex lies below another when the other lies in every affirmative corner that it does. -/
instance : LE Triangle :=
  ⟨fun s t ↦ (s ∈ corners.I → t ∈ corners.I) ∧ (s ∈ corners.A → t ∈ corners.A)⟩

instance : DecidableLE Triangle := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

instance : LinearOrder Triangle where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  le_total := by decide
  toDecidableLE := inferInstance

instance : BoundedOrder Triangle where
  top := .all
  le_top := by decide
  bot := .none
  bot_le := by decide

theorem bot_eq_none : (⊥ : Triangle) = .none := rfl

theorem top_eq_all : (⊤ : Triangle) = .all := rfl

/-- *Some* holds above the bottom vertex. -/
theorem mem_corners_I {t : Triangle} : t ∈ corners.I ↔ ⊥ < t := by decide +revert

/-- *All* holds at the top vertex. -/
theorem mem_corners_A {t : Triangle} : t ∈ corners.A ↔ t = ⊤ := by decide +revert

theorem mem_corners_O {t : Triangle} : t ∈ corners.O ↔ t < ⊤ := by decide +revert

theorem mem_corners_E {t : Triangle} : t ∈ corners.E ↔ t = ⊥ := by decide +revert

end Triangle

/-! ### The triangle -/

namespace SquareRelations

open Function Finset

/-- The vertices of a square are pairwise disjoint. -/
theorem pairwise_disjoint_triangle (h : SquareRelations sq) :
    Pairwise (Disjoint on sq.triangle) := by
  have hA : Disjoint sq.A (sq.I ⊓ sq.O) := by
    rw [h.inf_IO_eq]; exact disjoint_compl_right.mono_right (compl_le_compl le_sup_left)
  have hE : Disjoint sq.E (sq.I ⊓ sq.O) := by
    rw [h.inf_IO_eq]; exact disjoint_compl_right.mono_right (compl_le_compl le_sup_right)
  rintro (_ | _ | _) (_ | _ | _) hne <;> first
    | exact absurd rfl hne
    | simp only [onFun, Square.triangle]
  exacts [hE, h.contraryAE.symm, hE.symm, hA.symm, h.contraryAE, hA]

/-- The vertices of a square join to `⊤`. -/
theorem sup_triangle (h : SquareRelations sq) : univ.sup sq.triangle = ⊤ := by
  rw [show (univ : Finset Triangle) = {.none, .someNotAll, .all} by decide, sup_insert, sup_insert,
    sup_singleton]
  exact (congrArg _ h.inf_IO_sup_A).trans h.contradEI.sup_eq_top

/-- The vertices of a square none of which is `⊥` are distinct. -/
theorem triangle_injective (h : SquareRelations sq) (hne : ∀ t, sq.triangle t ≠ ⊥) :
    Injective sq.triangle := fun s t hst ↦
  by_contra fun hs ↦ hne s <| disjoint_self.1 <| by
    simpa only [onFun, ← hst] using h.pairwise_disjoint_triangle hs

/-- The vertices of a square none of which is `⊥` are pairwise contrary: any two leave room for
the third. -/
theorem pairwise_isContrary_triangle (h : SquareRelations sq) (hne : ∀ t, sq.triangle t ≠ ⊥) :
    Pairwise (IsContrary on sq.triangle) := fun s t hst ↦ by
  obtain ⟨r, hrs, hrt⟩ : ∃ r, r ≠ s ∧ r ≠ t := by decide +revert
  refine ⟨h.pairwise_disjoint_triangle hst, fun hc ↦ hne r <| disjoint_top.1 ?_⟩
  rw [← hc.eq_top]
  exact (h.pairwise_disjoint_triangle hrs).sup_right (h.pairwise_disjoint_triangle hrt)

/-- The homomorphism of a square sends a set of vertices to the join of its elements there. -/
def triangleHom (h : SquareRelations sq) : BoundedLatticeHom (Finset Triangle) α where
  toFun s := s.sup sq.triangle
  map_sup' _ _ := sup_union
  map_inf' s t := by
    refine le_antisymm (le_inf (sup_mono inter_subset_left) (sup_mono inter_subset_right)) ?_
    rw [sup_inf_sup]
    refine Finset.sup_le fun ⟨i, j⟩ hij ↦ ?_
    obtain ⟨hi, hj⟩ := mem_product.1 hij
    obtain rfl | hne := eq_or_ne i j
    · exact inf_le_left.trans (le_sup (mem_inter.2 ⟨hi, hj⟩))
    · exact (h.pairwise_disjoint_triangle hne).le_bot.trans bot_le
  map_top' := h.sup_triangle
  map_bot' := sup_empty

@[simp] theorem triangleHom_apply (h : SquareRelations sq) (s : Finset Triangle) :
    h.triangleHom s = s.sup sq.triangle := rfl

/-- A square with the relations is the image of the corners as sets of vertices. -/
theorem map_triangleHom_corners (h : SquareRelations sq) :
    Triangle.corners.map h.triangleHom = sq := by
  ext
  · exact sup_singleton
  · exact sup_singleton
  · exact (sup_insert.trans (congrArg _ sup_singleton)).trans h.inf_IO_sup_A
  · exact (sup_insert.trans (congrArg _ sup_singleton)).trans (sup_comm _ _ |>.trans h.inf_IO_sup_E)

/-- A homomorphism from sets of vertices is the homomorphism of the square it sends the corners
to. -/
theorem triangleHom_map_corners (f : BoundedLatticeHom (Finset Triangle) α) :
    (Triangle.squareRelations_corners.map f).triangleHom = f := by
  ext s
  rw [triangleHom_apply]
  conv_rhs => rw [← s.sup_singleton_eq_self, map_finset_sup]
  exact sup_congr rfl fun t _ ↦ by
    rw [Square.map_triangle, Triangle.triangle_corners, Function.comp_apply]

end SquareRelations

/-- The squares of a Boolean algebra that satisfy the relations are the images of the corners as
sets of vertices under the bounded lattice homomorphisms from `Finset Triangle`. -/
def squareRelationsEquivHom :
    {sq : Square α // SquareRelations sq} ≃ BoundedLatticeHom (Finset Triangle) α where
  toFun sq := sq.2.triangleHom
  invFun f := ⟨Triangle.corners.map f, Triangle.squareRelations_corners.map f⟩
  left_inv sq := Subtype.ext sq.2.map_triangleHom_corners
  right_inv := SquareRelations.triangleHom_map_corners

/-- A square satisfies the relations exactly when it is the image of the corners as sets of
vertices under a bounded lattice homomorphism. -/
theorem squareRelations_iff_exists_hom :
    SquareRelations sq ↔ ∃ f : BoundedLatticeHom (Finset Triangle) α, Triangle.corners.map f = sq :=
  ⟨fun h ↦ ⟨h.triangleHom, h.map_triangleHom_corners⟩,
    fun ⟨f, hf⟩ ↦ hf ▸ Triangle.squareRelations_corners.map f⟩

end Aristotelian
