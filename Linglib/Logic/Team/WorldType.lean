module

public import Linglib.Logic.Team.Bisimulation
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod

/-!
# World types

The world type of depth `k` of a world, over `n` atoms enumerated by `e`, records the truth values
of the atoms and, at positive depth, the set of depth `k - 1` types of the world's successors. Two
worlds have the same type exactly when they are
[`k`-bisimilar](##ModalLogic.worldType_eq_iff_worldBisim), once `e` enumerates every atom, and the
types are themselves the worlds of a [universal model](##ModalLogic.univModel). A class of pointed
team models closed under `k`-bisimilarity [reads only the types of a
team](##ModalLogic.mem_iff_types_mem_image), and its convexity and union closure pass to
[the sets of types of its members](##ModalLogic.supClosed_image_types). A proof that a team logic
is expressively complete therefore needs only a formula for each suitable family of type sets.

## References

* [aloni-anttila-yang-2024]
* [anttila-2025]
-/

@[expose] public section

namespace ModalLogic

universe u

variable {W W' : Type*} {Atom : Type*}

/-! ### World types -/

/-- A world type of depth `k` over `n` atoms gives the truth values of the atoms and, at positive
depth, the set of the depth `k - 1` types of the successors. -/
def WorldType (n : ℕ) : ℕ → Type
  | 0 => Fin n → Bool
  | k + 1 => (Fin n → Bool) × Finset (WorldType n k)

namespace WorldType

variable {n : ℕ}

instance instDecidableEq : (k : ℕ) → DecidableEq (WorldType n k)
  | 0 => inferInstanceAs (DecidableEq (Fin n → Bool))
  | k + 1 => @instDecidableEqProd _ _ _ (@Finset.decidableEq _ (instDecidableEq k))

instance instFintype : (k : ℕ) → Fintype (WorldType n k)
  | 0 => inferInstanceAs (Fintype (Fin n → Bool))
  | k + 1 => @instFintypeProd _ _ _ (@Finset.fintype _ (instFintype k))

/-- `τ.val` gives the truth values of the atoms at the type `τ`. -/
def val : {k : ℕ} → WorldType n k → Fin n → Bool
  | 0, a => a
  | _ + 1, τ => τ.1

end WorldType

variable {n : ℕ} (e : Fin n → Atom)

open scoped Classical in
/-- `worldType e M k w` is the type of depth `k` of the world `w`, over the atoms enumerated
by `e`. -/
noncomputable def worldType (M : KripkeModel W Atom) : (k : ℕ) → W → WorldType n k
  | 0, w => fun i ↦ decide (M.val (e i) w)
  | k + 1, w => (fun i ↦ decide (M.val (e i) w), (M.access w).image (worldType M k))

open scoped Classical in
theorem val_worldType (M : KripkeModel W Atom) :
    ∀ (k : ℕ) (w : W), (worldType e M k w).val = fun i ↦ decide (M.val (e i) w)
  | 0, _ | _ + 1, _ => rfl

variable {e}

/-- Two worlds have the same type exactly when they are `k`-bisimilar, once `e` enumerates every
atom. -/
theorem worldType_eq_iff_worldBisim (he : Function.Surjective e) {M : KripkeModel W Atom}
    {M' : KripkeModel W' Atom} :
    ∀ (k : ℕ) (w : W) (w' : W'), worldType e M k w = worldType e M' k w' ↔ WorldBisim k M w M' w'
  | 0, w, w' => by
    rw [worldType, worldType, funext_iff, WorldBisim]
    simp only [decide_eq_decide]
    exact (he.forall (p := fun p ↦ (M.val p w ↔ M'.val p w'))).symm
  | k + 1, w, w' => by
    rw [worldType, worldType, Prod.ext_iff, funext_iff, WorldBisim, ← Finset.coe_inj,
      Finset.coe_image, Finset.coe_image, ← Set.liftRel_iff_image_eq]
    simp only [decide_eq_decide]
    exact and_congr (he.forall (p := fun p ↦ (M.val p w ↔ M'.val p w'))).symm
      ⟨.imp (worldType_eq_iff_worldBisim he k _ _).1,
        .imp (worldType_eq_iff_worldBisim he k _ _).2⟩

/-- Two teams have the same types exactly when they are `k`-bisimilar, once `e` enumerates every
atom. -/
theorem image_worldType_eq_iff_stateBisim (he : Function.Surjective e) {k : ℕ}
    {M : KripkeModel W Atom} {M' : KripkeModel W' Atom} {s : Finset W} {s' : Finset W'} :
    s.image (worldType e M k) = s'.image (worldType e M' k) ↔ StateBisim k M s M' s' := by
  rw [← Finset.coe_inj, Finset.coe_image, Finset.coe_image, ← Set.liftRel_iff_image_eq]
  exact ⟨.imp (worldType_eq_iff_worldBisim he k _ _).1,
    .imp (worldType_eq_iff_worldBisim he k _ _).2⟩

/-- The type of a world of a disjoint union is its type in its summand. -/
theorem worldType_sum (M : KripkeModel W Atom) (M' : KripkeModel W' Atom) (k : ℕ) :
    worldType e (M.sum M') k = Sum.elim (worldType e M k) (worldType e M' k) := by
  induction k with
  | zero => funext w; cases w <;> rfl
  | succ k ih =>
    funext w
    cases w <;> exact Prod.ext rfl (by ext; simp [worldType, ih])

/-! ### The universal model -/

variable (e) in
/-- In the universal model each type is a world, whose successors are its successor types. -/
def univModel : KripkeModel (Σ k, WorldType n k) Atom where
  access
    | ⟨0, _⟩ => ∅
    | ⟨k + 1, τ⟩ => τ.2.image fun σ ↦ ⟨k, σ⟩
  val p w := ∃ i, e i = p ∧ w.2.val i = true

noncomputable instance : DecidableRel (univModel e).val := fun _ _ ↦ Classical.dec _

/-- `world k τ` is the type `τ` as a world of the universal model. -/
def WorldType.world (k : ℕ) (τ : WorldType n k) : Σ k, WorldType n k := ⟨k, τ⟩

theorem WorldType.world_injective (k : ℕ) : Function.Injective (world (n := n) k) := fun _ _ h ↦ by
  simpa [world] using h

open WorldType

theorem univModel_val (he : Function.Injective e) (i : Fin n) (w : Σ k, WorldType n k) :
    (univModel e).val (e i) w ↔ w.2.val i = true := by
  simp [univModel, he.eq_iff]

theorem univModel_access_succ {k : ℕ} (τ : WorldType n (k + 1)) :
    (univModel e).access (world (k + 1) τ) = τ.2.image (world k) := rfl

/-- In the universal model, each type is its own type. -/
theorem worldType_univModel (he : Function.Injective e) :
    ∀ (k : ℕ) (τ : WorldType n k), worldType e (univModel e) k (world k τ) = τ
  | 0, a => funext fun i ↦ by simp [worldType, univModel_val he, world, WorldType.val]
  | k + 1, τ => by
    rw [worldType, univModel_access_succ, Finset.image_image]
    refine Prod.ext (funext fun i ↦ by simp [univModel_val he, world, WorldType.val]) ?_
    simp only [Function.comp_def, worldType_univModel he k, Finset.image_id']

/-! ### The types of a team -/

variable (e) in
/-- The depth `k` types of the worlds of a pointed team model. -/
noncomputable def PointedTeam.types (k : ℕ) (p : PointedTeam.{u} Atom) : Finset (WorldType n k) :=
  p.team.image (worldType e p.model k)

variable {k : ℕ} {P : Set (PointedTeam.{u} Atom)}

/-- A class closed under `k`-bisimilarity holds of a pointed team model exactly when some member
has the same types of depth `k`. -/
theorem mem_iff_types_mem_image (he : Function.Surjective e) (hP : BisimInvariantAt k P)
    {p : PointedTeam.{u} Atom} : p ∈ P ↔ p.types e k ∈ PointedTeam.types e k '' P :=
  ⟨Set.mem_image_of_mem _, fun ⟨q, hq, h⟩ ↦ hP q hq p ((image_worldType_eq_iff_stateBisim he).1 h)⟩

/-- The type sets of a class closed under `k`-bisimilarity are convex when the class is convex in
every model: a type set between two of them is the type set of a team between two members. -/
theorem ordConnected_image_types (he : Function.Surjective e) (hP : BisimInvariantAt k P)
    (hc : Fiberwise (fun T ↦ T.OrdConnected) P) :
    (PointedTeam.types e k '' P).OrdConnected := ⟨by
  rintro _ ⟨q, hq, rfl⟩ _ ⟨⟨W, M, s₂⟩, h₂, rfl⟩ σ ⟨hqσ, hσ⟩
  obtain ⟨s, hs, rfl⟩ := Finset.subset_image_iff.1 hσ
  obtain ⟨s₁, hs₁, h₁⟩ := Finset.subset_image_iff.1 hqσ
  exact ⟨⟨W, M, s⟩,
    (hc M).out ((mem_iff_types_mem_image he hP).2 ⟨q, hq, h₁.symm⟩) h₂ ⟨hs₁, hs⟩, rfl⟩⟩

/-- The type sets of a class closed under `k`-bisimilarity are closed under union when the class is
in every model: two members embed in the disjoint union of their models, where the union of
their teams has the union of their type sets. -/
theorem supClosed_image_types (he : Function.Surjective e) (hP : BisimInvariantAt k P)
    (hs : Fiberwise (fun T ↦ SupClosed T) P) : SupClosed (PointedTeam.types e k '' P) := by
  rintro _ ⟨⟨W₁, M₁, s₁⟩, h₁, rfl⟩ _ ⟨⟨W₂, M₂, s₂⟩, h₂, rfl⟩
  have h₁' : (s₁.map .inl).image (worldType e (M₁.sum M₂) k) = s₁.image (worldType e M₁ k) := by
    ext; simp [worldType_sum]
  have h₂' : (s₂.map .inr).image (worldType e (M₁.sum M₂) k) = s₂.image (worldType e M₂ k) := by
    ext; simp [worldType_sum]
  have h : s₁.map .inl ⊔ s₂.map .inr ∈ PointedTeam.mk _ (M₁.sum M₂) ⁻¹' P :=
    hs _ ((mem_iff_types_mem_image he hP).2 ⟨_, h₁, h₁'.symm⟩)
      ((mem_iff_types_mem_image he hP).2 ⟨_, h₂, h₂'.symm⟩)
  exact ⟨_, h, by simp only [PointedTeam.types, Finset.sup_eq_union, Finset.image_union, h₁', h₂']⟩

end ModalLogic
