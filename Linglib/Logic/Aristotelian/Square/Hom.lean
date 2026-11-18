module

public import Linglib.Logic.Aristotelian.Triangle
public import Mathlib.Data.Finset.Lattice.Prod

/-!
# Squares of opposition as homomorphisms

A square of opposition has an element at each vertex of the triangle of opposition: `E`, the
conjunction `I ⊓ O` of the particulars, and `A`. These three are [pairwise
disjoint](##Aristotelian.SquareRelations.pairwise_disjoint_triangle) and [join to
`⊤`](##Aristotelian.SquareRelations.sup_triangle), and when none is `⊥` they are [pairwise
contrary](##Aristotelian.SquareRelations.pairwise_isContrary_triangle).

The square of corners in `Finset Triangle` is therefore the generic one: the squares of a
Boolean algebra `α` that satisfy the relations [correspond
to](##Aristotelian.squareRelationsEquivHom) the bounded lattice homomorphisms
`Finset Triangle → α`, each square being the image of that one.

## References

* [horn-2001]
-/

@[expose] public section

namespace Aristotelian

variable {F α β : Type*}

/-! ### The vertices of a square -/

namespace Square

/-- The element of a square at a vertex of its triangle. -/
def triangle [Min α] (sq : Square α) : Triangle → α
  | .none => sq.E
  | .someNotAll => sq.I ⊓ sq.O
  | .all => sq.A

theorem map_triangle [Min α] [Min β] [FunLike F α β] [InfHomClass F α β] (f : F) (sq : Square α)
    (t : Triangle) : (sq.map f).triangle t = f (sq.triangle t) := by
  cases t <;> simp [triangle]

end Square

/-- The element of `corners` at each vertex is that vertex's singleton. -/
theorem Triangle.triangle_corners (t : Triangle) :
    Triangle.corners.triangle t = {t} := by
  cases t <;> decide

variable [BooleanAlgebra α] {sq : Square α}

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
  rw [Triangle.univ_eq, sup_insert, sup_insert, sup_singleton]
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
