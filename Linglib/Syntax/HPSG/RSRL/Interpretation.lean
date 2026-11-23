module

public import Linglib.Syntax.HPSG.RSRL.Signature
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Basic.FunLike.Embedding
public import Linglib.Syntax.Feature.Structure

/-!
# RSRL interpretations

An *interpretation* of a signature over a universe `U` gives a sort to every entity, a partial
function on entities for every attribute, and a set of tuples of entities for every relation
symbol. It is in particular a partial Moore machine, with the attributes as letters and the
sorts as outputs, and following a path is reading it in this machine. The *components* of an
entity are the entities that some path reaches from it, so each entity is the root of a feature
structure (`HPSG.RSRL.Interpretation.featureStructure`).

For a path `p`, `I.SortAt u p σ` says that `p` leads from `u` to an entity of the sort `σ`, and
`I.PathEq u p q` that `p` and `q` lead from `u` to one entity. These are what the abstract
feature structure of `u` records, so they pass along any simulation of the machine at `u`
(`HPSG.RSRL.Interpretation.SortAt.of_simulatedBy`).

A *homomorphism* of interpretations keeps sorts, commutes with the attributes and preserves the
relations. It maps the components of an entity onto those of its image
(`HPSG.RSRL.Interpretation.HomClass.image_isComponentOf`). An *isomorphism* is a bijection that
does so and reflects the relations, and a bijection carries an interpretation over to an
isomorphic one (`HPSG.RSRL.Interpretation.mapEquiv`).

## Implementation notes

The universe is a parameter, not a field, as the carrier of a first-order structure is in
mathlib. The conditions that [richter-2024] builds into an interpretation are separate
predicates (`IsSortResolved`, `IsTotallyWellTyped`, `IsFull`), since a worked example often
interprets only part of a feature structure. Chains are not formalized. `Hom`, `Embedding`,
`Equiv` and `HomClass` follow their namesakes in `FirstOrder.Language`. Being a component is
being reached in the machine, the reflexive transitive closure of its transitions. The machine
outputs the sort in the dual order, in which the more specific sort is the greater.

## References

* [richter-2000]
* [richter-2024]
* [carpenter-1992]
-/

@[expose] public section

namespace HPSG.RSRL

universe u v w

/-- An interpretation of the signature `Sig` over the universe `U` gives each entity a sort, each
attribute a partial function on entities, and each relation symbol a set of tuples of entities
([richter-2024], Definition 7). -/
structure Interpretation {Srt : Type u} [PartialOrder Srt] (Sig : Signature Srt)
    (U : Type v) where
  /-- The sort of each entity. -/
  S : U → Srt
  /-- The partial function on entities that interprets each attribute. -/
  A : Sig.Attr → U → Option U
  /-- The set of argument tuples that interprets each relation symbol. -/
  R : (ρ : Sig.Rel) → Set (Fin (Sig.arity ρ) → U)

namespace Interpretation

variable {Srt : Type u} [PartialOrder Srt] {Sig : Signature Srt} {U : Type v}
  (I : Interpretation Sig U)

/-! ### The machine of an interpretation -/

/-- An interpretation as a partial Moore machine over the attributes: the transition for an
attribute is its partial function, and the output at an entity is its sort, in the order in
which the more specific sort is the greater. -/
def toPartialMoore : PartialMoore U Sig.Attr Srtᵒᵈ where
  step q α := I.A α q
  out q := OrderDual.toDual (I.S q)

/-- The feature structure of an entity, whose nodes are its components. -/
abbrev featureStructure (u : U) :
    FeatureStructure {q // I.toPartialMoore.Reaches u q} Sig.Attr Srtᵒᵈ :=
  I.toPartialMoore.featureStructure u

variable {I} {u v : U}

@[simp] theorem toPartialMoore_step (α : Sig.Attr) : I.toPartialMoore.step u α = I.A α u := rfl

/-! ### Paths -/

variable (I) in
/-- The entity that a path leads to from `u`, if every attribute along it is defined. -/
abbrev eval (u : U) (p : Path Sig) : Option U := I.toPartialMoore.evalFrom u p

theorem eval_cons (α : Sig.Attr) (p : Path Sig) :
    I.eval u (α :: p) = (I.A α u).bind (I.eval · p) := PartialMoore.evalFrom_cons ..

theorem eval_append (p q : Path Sig) : I.eval u (p ++ q) = (I.eval u p).bind (I.eval · q) :=
  PartialMoore.evalFrom_append ..

variable (I) in
/-- The path `p` leads from `u` to an entity whose sort is at least as specific as `σ`. -/
def SortAt (u : U) (p : Path Sig) (σ : Srt) : Prop := ∃ v ∈ I.eval u p, I.S v ≤ σ

variable (I) in
/-- The paths `p` and `q` lead from `u` to the same entity. -/
abbrev PathEq (u : U) (p q : Path Sig) : Prop := I.toPartialMoore.Nerode u p q

instance [DecidableLE Srt] (p : Path Sig) (σ : Srt) : Decidable (I.SortAt u p σ) :=
  Option.decidableExistsMem (p := (I.S · ≤ σ)) _

section SortAt

variable {p q : Path Sig} {σ τ : Srt} {α : Sig.Attr}

@[simp] theorem sortAt_nil : I.SortAt u [] σ ↔ I.S u ≤ σ := by simp [SortAt]

theorem sortAt_cons (h : I.A α u = some v) : I.SortAt u (α :: p) σ ↔ I.SortAt v p σ := by
  simp [SortAt, h]

theorem sortAt_append : I.SortAt u (p ++ q) σ ↔ ∃ v ∈ I.eval u p, I.SortAt v q σ := by
  rw [SortAt, eval_append]
  cases I.eval u p <;> simp [SortAt]

theorem SortAt.mono (hστ : σ ≤ τ) (h : I.SortAt u p σ) : I.SortAt u p τ :=
  let ⟨v, hv, hσ⟩ := h; ⟨v, hv, hσ.trans hστ⟩

/-- A path has values of two sorts only if the sorts have a common subsort. -/
theorem SortAt.exists_le (hσ : I.SortAt u p σ) (hτ : I.SortAt u p τ) : ∃ ρ, ρ ≤ σ ∧ ρ ≤ τ :=
  let ⟨v, hv, hvσ⟩ := hσ
  let ⟨_, hw, hwτ⟩ := hτ
  ⟨I.S v, hvσ, Option.mem_unique hv hw ▸ hwτ⟩

/-- Paths that lead to the same entity have continuations with values of the same sorts. -/
theorem PathEq.sortAt_append_iff (h : I.PathEq u p q) (r : Path Sig) :
    I.SortAt u (p ++ r) σ ↔ I.SortAt u (q ++ r) σ := by
  rw [SortAt, SortAt, eval, eval, h.evalFrom_append]

theorem PathEq.sortAt_iff (h : I.PathEq u p q) : I.SortAt u p σ ↔ I.SortAt u q σ := by
  simpa using h.sortAt_append_iff []

end SortAt

/-! ### Components -/

variable (I) in
/-- The entity `v` is a component of `u` when a sequence of attributes leads from `u` to `v`:
the machine of the interpretation reaches `v` from `u`. -/
abbrev IsComponentOf (u v : U) : Prop := I.toPartialMoore.Reaches u v

/-! ### Typing -/

variable (I) in
/-- An interpretation is sort-resolved when the sort of every entity is a species. -/
def IsSortResolved : Prop := ∀ u, IsSpecies (I.S u)

variable (I) in
/-- An interpretation is well-typed when every attribute that is defined on an entity is
appropriate to the entity's sort, with a value of the appropriate sort. -/
def IsWellTyped : Prop :=
  ∀ (α : Sig.Attr) (u v : U), I.A α u = some v → ∃ τ ∈ Sig.approp (I.S u) α, I.S v ≤ τ

variable (I) in
/-- An interpretation is totally well-typed when it is well-typed and every attribute that is
appropriate to the sort of an entity is defined on it. -/
@[mk_iff] structure IsTotallyWellTyped : Prop where
  /-- The interpretation is well-typed. -/
  isWellTyped : I.IsWellTyped
  /-- Every appropriate attribute is defined. -/
  total : ∀ (α : Sig.Attr) (u : U), (Sig.approp (I.S u) α).isSome → (I.A α u).isSome

instance [Fintype Srt] [DecidableLE Srt] [Fintype U] : Decidable I.IsSortResolved :=
  inferInstanceAs (Decidable (∀ u, IsSpecies (I.S u)))

instance [DecidableLE Srt] [Fintype U] [Fintype Sig.Attr] : Decidable I.IsWellTyped :=
  inferInstanceAs <| Decidable <| ∀ (α : Sig.Attr) (u : U),
    ∀ v ∈ I.A α u, ∃ τ ∈ Sig.approp (I.S u) α, I.S v ≤ τ

instance [DecidableLE Srt] [Fintype U] [Fintype Sig.Attr] : Decidable I.IsTotallyWellTyped :=
  decidable_of_iff _ (isTotallyWellTyped_iff I).symm

/-- In a well-typed interpretation the signature admits every path that is defined, from the
sort of the entity it starts at to the sort of the entity it reaches. -/
theorem IsWellTyped.admits (hI : I.IsWellTyped) {p : Path Sig}
    (h : I.toPartialMoore.evalFrom u p = some v) : Sig.Admits (I.S u) p (I.S v) := by
  induction p generalizing u with
  | nil => obtain rfl : u = v := by simpa using h
           rfl
  | cons α p ih =>
    rw [PartialMoore.evalFrom_cons, Option.bind_eq_some_iff] at h
    obtain ⟨w, hw, hp⟩ := h
    obtain ⟨τ, hτ, hle⟩ := hI α u w hw
    exact ⟨τ, hτ, I.S w, hle, ih hp⟩

variable (I) in
/-- An interpretation is full when the entities of every relation tuple are components of one
entity ([richter-2024], Definitions 12 and 13). -/
def IsFull : Prop :=
  ∀ (ρ : Sig.Rel), ∀ xs ∈ I.R ρ, ∃ u, ∀ i, I.IsComponentOf u (xs i)

/-- The relations of an interpretation are decidable when the signature has no relation
symbols. -/
instance [IsEmpty Sig.Rel] (ρ : Sig.Rel) : DecidablePred (· ∈ I.R ρ) := isEmptyElim ρ

/-! ### Homomorphisms -/

variable {V : Type w} {W : Type*}

/-- A homomorphism of interpretations is a map of entities that preserves sorts, commutes with
the attributes and preserves the relations. -/
structure Hom (I : Interpretation Sig U) (J : Interpretation Sig V) where
  /-- The map of entities. -/
  toFun : U → V
  /-- An entity and its image have the same sort. -/
  map_S' : ∀ u, J.S (toFun u) = I.S u
  /-- An attribute is defined on the image of an entity exactly when it is defined on the
  entity, with the image of its value as value. -/
  map_A' : ∀ α u, J.A α (toFun u) = (I.A α u).map toFun
  /-- The image of a relation tuple is a relation tuple. -/
  map_R' : ∀ ρ (xs : Fin (Sig.arity ρ) → U), xs ∈ I.R ρ → toFun ∘ xs ∈ J.R ρ

/-- An embedding of interpretations is an injective homomorphism that reflects the relations. -/
structure Embedding (I : Interpretation Sig U) (J : Interpretation Sig V) extends U ↪ V where
  /-- An entity and its image have the same sort. -/
  map_S' : ∀ u, J.S (toFun u) = I.S u
  /-- An attribute is defined on the image of an entity exactly when it is defined on the
  entity, with the image of its value as value. -/
  map_A' : ∀ α u, J.A α (toFun u) = (I.A α u).map toFun
  /-- A tuple is a relation tuple exactly when its image is. -/
  map_R' : ∀ ρ (xs : Fin (Sig.arity ρ) → U), toFun ∘ xs ∈ J.R ρ ↔ xs ∈ I.R ρ

variable {J : Interpretation Sig V} {K : Interpretation Sig W}

/-- `HomClass F I J` states that `F` is a type of homomorphisms from `I` to `J`. -/
class HomClass (F : Type*) {Srt : outParam (Type u)} [outParam (PartialOrder Srt)]
    {Sig : outParam (Signature Srt)} {U : outParam (Type v)} {V : outParam (Type w)}
    (I : outParam (Interpretation Sig U)) (J : outParam (Interpretation Sig V))
    [FunLike F U V] : Prop where
  /-- An entity and its image have the same sort. -/
  map_S (f : F) (u : U) : J.S (f u) = I.S u
  /-- An attribute is defined on the image of an entity exactly when it is defined on the
  entity, with the image of its value as value. -/
  map_A (f : F) (α : Sig.Attr) (u : U) : J.A α (f u) = (I.A α u).map f
  /-- The image of a relation tuple is a relation tuple. -/
  map_R (f : F) {ρ : Sig.Rel} {xs : Fin (Sig.arity ρ) → U} : xs ∈ I.R ρ → f ∘ xs ∈ J.R ρ

attribute [simp] HomClass.map_S HomClass.map_A

namespace HomClass

variable {F : Type*} [FunLike F U V] [HomClass F I J] (f : F)

/-- A homomorphism maps the components of an entity to components of its image. -/
theorem isComponentOf (h : I.IsComponentOf u v) : J.IsComponentOf (f u) (f v) :=
  h.lift f fun a _ ⟨α, hα⟩ ↦ ⟨α, (map_A f α a).trans (congrArg (Option.map f) hα)⟩

/-- Every component of the image of an entity is the image of one of its components. -/
theorem exists_isComponentOf_of_isComponentOf {w : V} (h : J.IsComponentOf (f u) w) :
    ∃ v, I.IsComponentOf u v ∧ f v = w := by
  induction h with
  | refl => exact ⟨u, .refl, rfl⟩
  | tail _ hα ih =>
    obtain ⟨v, hv, rfl⟩ := ih
    obtain ⟨α, hα⟩ := hα
    obtain ⟨v', hv', rfl⟩ := Option.map_eq_some_iff.1 ((map_A f α v).symm.trans hα)
    exact ⟨v', hv.tail ⟨α, hv'⟩, rfl⟩

/-- The components of the image of an entity are the images of its components. -/
theorem image_isComponentOf (u : U) :
    f '' {v | I.IsComponentOf u v} = {w | J.IsComponentOf (f u) w} :=
  Set.ext fun _ ↦ ⟨fun ⟨_, hv, hw⟩ ↦ hw ▸ isComponentOf f hv,
    fun h ↦ exists_isComponentOf_of_isComponentOf f h⟩

/-- Sort resolution passes from the target of a homomorphism to its source. -/
theorem isSortResolved (f : F) (hJ : J.IsSortResolved) : I.IsSortResolved :=
  fun u ↦ map_S f u ▸ hJ (f u)

/-- Well-typedness passes from the target of a homomorphism to its source. -/
theorem isWellTyped (f : F) (hJ : J.IsWellTyped) : I.IsWellTyped := fun α u v h ↦ by
  simpa using hJ α (f u) (f v) (by rw [map_A f, h]; rfl)

/-- Total well-typedness passes from the target of a homomorphism to its source. -/
theorem isTotallyWellTyped (f : F) (hJ : J.IsTotallyWellTyped) : I.IsTotallyWellTyped :=
  ⟨isWellTyped f hJ.isWellTyped, fun α u h ↦ by simpa using hJ.total α (f u) (by simpa using h)⟩

end HomClass

namespace Hom

instance : FunLike (Hom I J) U V where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

instance : HomClass (Hom I J) I J where
  map_S f := f.map_S'
  map_A f := f.map_A'
  map_R f := f.map_R' _ _

variable (f : Hom I J)

@[simp] theorem toFun_eq_coe : f.toFun = f := rfl

@[ext] theorem ext {f g : Hom I J} (h : ∀ u, f u = g u) : f = g := DFunLike.ext f g h

variable (I) in
/-- The identity homomorphism. -/
@[simps] protected def id : Hom I I where
  toFun := id
  map_S' _ := rfl
  map_A' _ _ := Option.map_id'.symm
  map_R' _ _ h := h

/-- The composition of two homomorphisms. -/
def comp (f' : Hom J K) (f : Hom I J) : Hom I K where
  toFun := f' ∘ f
  map_S' u := (HomClass.map_S f' _).trans (HomClass.map_S f u)
  map_A' α u := by simp [Option.map_map]
  map_R' _ _ h := HomClass.map_R f' (HomClass.map_R f h)

@[simp] theorem comp_apply (f' : Hom J K) (u : U) : f'.comp f u = f' (f u) := rfl

@[simp] theorem comp_id : f.comp (.id I) = f := rfl

@[simp] theorem id_comp : (Hom.id J).comp f = f := rfl

end Hom

namespace Embedding

instance : FunLike (Embedding I J) U V where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

instance : EmbeddingLike (Embedding I J) U V where
  injective' f := f.toEmbedding.injective

instance : HomClass (Embedding I J) I J where
  map_S f := f.map_S'
  map_A f := f.map_A'
  map_R f := (f.map_R' _ _).2

variable (f : Embedding I J)

/-- An embedding regarded as a homomorphism. -/
def toHom : Hom I J where
  toFun := f
  map_S' := HomClass.map_S f
  map_A' := HomClass.map_A f
  map_R' _ _ := HomClass.map_R f

@[simp] theorem coe_toHom : ⇑f.toHom = f := rfl

@[ext] theorem ext {f g : Embedding I J} (h : ∀ u, f u = g u) : f = g := DFunLike.ext f g h

theorem injective : Function.Injective f := f.toEmbedding.injective

/-- A tuple is a relation tuple exactly when its image under an embedding is. -/
@[simp] theorem map_R {ρ : Sig.Rel} {xs : Fin (Sig.arity ρ) → U} : f ∘ xs ∈ J.R ρ ↔ xs ∈ I.R ρ :=
  f.map_R' ρ xs

variable (I) in
/-- The identity embedding. -/
@[simps!] protected def refl : Embedding I I where
  toEmbedding := .refl U
  map_S' _ := rfl
  map_A' _ _ := Option.map_id'.symm
  map_R' _ _ := Iff.rfl

/-- The composition of two embeddings. -/
def comp (f' : Embedding J K) (f : Embedding I J) : Embedding I K where
  toEmbedding := f.toEmbedding.trans f'.toEmbedding
  map_S' u := (HomClass.map_S f' (f u)).trans (HomClass.map_S f u)
  map_A' α u := by
    change K.A α (f' (f u)) = _
    rw [HomClass.map_A f', HomClass.map_A f, Option.map_map]; rfl
  map_R' _ xs := (f'.map_R (xs := f ∘ xs)).trans f.map_R

@[simp] theorem comp_apply (f' : Embedding J K) (u : U) : f'.comp f u = f' (f u) := rfl

end Embedding

/-! ### Isomorphisms -/

/-- An isomorphism of interpretations is a bijection of entities that keeps sorts, commutes with
the attributes, and preserves and reflects the relations. -/
structure Equiv (I : Interpretation Sig U) (J : Interpretation Sig V) extends U ≃ V where
  /-- An entity and its image have the same sort. -/
  map_S' : ∀ u, J.S (toFun u) = I.S u
  /-- An attribute is defined on the image of an entity exactly when it is defined on the
  entity, with the image of its value as value. -/
  map_A' : ∀ α u, J.A α (toFun u) = (I.A α u).map toFun
  /-- A tuple is a relation tuple exactly when its image is. -/
  map_R' : ∀ ρ (xs : Fin (Sig.arity ρ) → U), toFun ∘ xs ∈ J.R ρ ↔ xs ∈ I.R ρ

namespace Equiv

/-- An isomorphism regarded as an embedding. -/
def toEmbedding (f : Equiv I J) : Embedding I J where
  toEmbedding := f.toEquiv.toEmbedding
  map_S' := f.map_S'
  map_A' := f.map_A'
  map_R' := f.map_R'

instance : FunLike (Equiv I J) U V where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨e, _, _, _⟩ := f
    obtain ⟨e', _, _, _⟩ := g
    obtain rfl : e = e' := _root_.Equiv.ext (congrFun h)
    rfl

instance : HomClass (Equiv I J) I J where
  map_S f := f.map_S'
  map_A f := f.map_A'
  map_R f := (f.map_R' _ _).2

@[simp] theorem coe_toEmbedding (f : Equiv I J) : ⇑f.toEmbedding = f := rfl

@[simp] theorem coe_toEquiv (f : Equiv I J) : ⇑f.toEquiv = f := rfl

variable (I) in
/-- The identity isomorphism. -/
protected def refl : Equiv I I where
  toEquiv := .refl U
  map_S' _ := rfl
  map_A' _ _ := Option.map_id'.symm
  map_R' _ _ := Iff.rfl

/-- The inverse of an isomorphism. -/
protected def symm (f : Equiv I J) : Equiv J I where
  toEquiv := f.toEquiv.symm
  map_S' v :=
    ((congrArg J.S (f.toEquiv.apply_symm_apply v)).symm.trans (f.map_S' _)).symm
  map_A' α v := by
    have h := f.map_A' α (f.toEquiv.symm v)
    rw [show f.toFun (f.toEquiv.symm v) = v from f.toEquiv.apply_symm_apply v] at h
    have e : f.toEquiv.symm.toFun ∘ f.toFun = id := funext f.toEquiv.symm_apply_apply
    rw [h, Option.map_map, e, Option.map_id, id]
    rfl
  map_R' ρ xs := by
    have h := f.map_R' ρ (f.toEquiv.symm ∘ xs)
    rw [show f.toFun ∘ f.toEquiv.symm ∘ xs = xs from
      funext fun i ↦ f.toEquiv.apply_symm_apply (xs i)] at h
    exact h.symm

/-- The composition of two isomorphisms. -/
protected def trans (f : Equiv I J) (f' : Equiv J K) : Equiv I K where
  toEquiv := f.toEquiv.trans f'.toEquiv
  map_S' u := (f'.map_S' (f u)).trans (f.map_S' u)
  map_A' α u := by
    change K.A α (f' (f u)) = _
    rw [HomClass.map_A f', HomClass.map_A f, Option.map_map]; rfl
  map_R' _ xs := (f'.map_R' _ (f ∘ xs)).trans (f.map_R' _ xs)

@[simp] theorem symm_apply_apply (f : Equiv I J) (u : U) : f.symm (f u) = u :=
  f.toEquiv.symm_apply_apply u

@[simp] theorem apply_symm_apply (f : Equiv I J) (v : V) : f (f.symm v) = v :=
  f.toEquiv.apply_symm_apply v

end Equiv

variable (I) in
/-- The interpretation on `V` that a bijection with the universe of `I` carries over. -/
def map (e : U ≃ V) : Interpretation Sig V where
  S v := I.S (e.symm v)
  A α v := (I.A α (e.symm v)).map e
  R ρ := {xs | e.symm ∘ xs ∈ I.R ρ}

variable (I) in
/-- A bijection is an isomorphism onto the interpretation it carries over. -/
def mapEquiv (e : U ≃ V) : Equiv I (I.map e) where
  toEquiv := e
  map_S' u := by simp [map]
  map_A' α u := by simp [map]
  map_R' ρ xs := by simp [map, ← Function.comp_assoc]

@[simp] theorem coe_mapEquiv (e : U ≃ V) : ⇑(I.mapEquiv e) = e := rfl

/-- A homomorphism is a simulation of the machine at an entity by the machine at its image. -/
theorem Hom.simulatedBy (f : Hom I J) (u : U) :
    I.toPartialMoore.SimulatedBy J.toPartialMoore u (f u) :=
  ⟨f, rfl, fun q _ ↦ OrderDual.toDual_le_toDual.2 (HomClass.map_S f q).le, fun α q q' _ hα ↦ by
    show J.A α (f q) = some (f q')
    rw [HomClass.map_A]
    exact congrArg (Option.map f) hα⟩

/-! ### Subsumption

The sorts of the values of paths and the paths that meet are what the abstract feature structure
of an entity records, so both pass from an entity to any entity whose feature structure its own
subsumes. -/

section Simulation

variable {v' : V} {p q : Path Sig} {σ : Srt}

theorem SortAt.of_simulatedBy (h : I.toPartialMoore.SimulatedBy J.toPartialMoore u v')
    (hσ : I.SortAt u p σ) : J.SortAt v' p σ := by
  obtain ⟨w, hw, hle⟩ := hσ
  obtain ⟨c, hc, hwc⟩ := (PartialMoore.simulatedBy_iff.1 h).1 p (OrderDual.toDual (I.S w))
    (congrArg (Option.map I.toPartialMoore.out) (Option.mem_def.1 hw))
  obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.1 hc
  exact ⟨w', hw', (OrderDual.toDual_le_toDual.1 hwc).trans hle⟩

theorem PathEq.of_simulatedBy (h : I.toPartialMoore.SimulatedBy J.toPartialMoore u v')
    (hpq : I.PathEq u p q) : J.PathEq v' p q :=
  (PartialMoore.simulatedBy_iff.1 h).2 p q hpq

end Simulation

end Interpretation

end HPSG.RSRL
