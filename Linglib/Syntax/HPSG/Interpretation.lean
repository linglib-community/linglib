module

public import Linglib.Syntax.HPSG.Signature
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Basic.FunLike.Embedding
public import Linglib.Syntax.Feature.Structure

/-!
# RSRL interpretations

An interpretation of an RSRL signature over a universe `U` of entities assigns a sort to every
entity, a partial function on entities to every attribute, and a set of tuples of entities to
every relation symbol. A term then denotes a partial function on entities, and the
[components](##HPSG.RSRL.Interpretation.isComponentOf_iff_exists_path) of an entity are the
entities that some path reaches from it. A homomorphism of interpretations preserves sorts,
commutes with the attributes and preserves the relations. Since attributes are functions, a
homomorphism [maps the components of an entity onto the components of its
image](##HPSG.RSRL.Interpretation.HomClass.image_isComponentOf), and it
[commutes with term denotation](##HPSG.RSRL.Interpretation.HomClass.termDenot_comp).

## Implementation notes

The universe is a parameter rather than a field, as the carrier of a first-order structure is in
mathlib, so that instances on it are found by inference. The conditions that [richter-2024]
builds into an interpretation are separate predicates, since a worked example often interprets
only the part of a feature structure that a principle mentions: `IsSortResolved` and
`IsTotallyWellTyped`, named as in [carpenter-1992], for the conditions on sorts and attributes,
and `IsFull` for the restriction of relation tuples to the components of one entity. Chains are
not formalized, so a relation tuple holds entities only. `Hom`, `Embedding` and `HomClass`
follow their namesakes in `FirstOrder.Language`, so a fact about homomorphisms is stated once
and applies to embeddings.

## References

* [richter-2000]
* [richter-2024]
* [carpenter-1992]
-/

@[expose] public section

namespace HPSG.RSRL

universe u v w

/-- An interpretation of the signature `Sig` over the universe `U`
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

/-! ### Term denotation -/

/-- The entity that a term denotes at the described entity `u` under the assignment `g`, when
every attribute along the term is defined ([richter-2024], Definition 10). -/
def termDenot (g : ℕ → U) : Term Sig → U → Option U
  | .colon, u => some u
  | .var n, _ => some (g n)
  | .feat t α, u => (termDenot g t u).bind (I.A α)

variable {I} {g g' : ℕ → U} {u v : U}

@[simp] theorem termDenot_colon : I.termDenot g .colon u = some u := rfl

@[simp] theorem termDenot_var (n : ℕ) : I.termDenot g (.var n) u = some (g n) := rfl

@[simp] theorem termDenot_feat (t : Term Sig) (α : Sig.Attr) :
    I.termDenot g (t.feat α) u = (I.termDenot g t u).bind (I.A α) := rfl

/-- A term denotation depends only on the values of the variables that occur in the term. -/
theorem termDenot_congr {t : Term Sig} (h : ∀ x ∈ t.freeVars, g x = g' x) :
    I.termDenot g t u = I.termDenot g' t u := by
  induction t with
  | colon => rfl
  | var n => simp [h n (Finset.mem_singleton_self n)]
  | feat t α ih => rw [termDenot_feat, termDenot_feat, ih h]

theorem termDenot_of_isColonFree {t : Term Sig} (ht : t.IsColonFree) (u v : U) :
    I.termDenot g t u = I.termDenot g t v := by
  induction t with
  | colon => exact ht.elim
  | var n => rfl
  | feat t α ih => rw [termDenot_feat, termDenot_feat, ih ht]

theorem termDenot_path (g g' : ℕ → U) (p : Path Sig) :
    I.termDenot g (.path p) u = I.termDenot g' (.path p) u :=
  termDenot_congr (by simp)

theorem termDenot_path_cons (α : Sig.Attr) (p : Path Sig) :
    I.termDenot g (.path (α :: p)) u = (I.A α u).bind (I.termDenot g (.path p)) := by
  induction p using List.reverseRecOn with
  | nil => simp [Term.path]
  | append_singleton p β ih =>
    rw [← List.cons_append, Term.path_concat, Term.path_concat, termDenot_feat, ih,
      Option.bind_assoc]
    rfl

theorem termDenot_path_append (p q : Path Sig) :
    I.termDenot g (.path (p ++ q)) u =
      (I.termDenot g (.path p) u).bind (I.termDenot g (.path q)) := by
  induction p generalizing u with
  | nil => rfl
  | cons α p ih =>
    rw [List.cons_append, termDenot_path_cons, termDenot_path_cons, Option.bind_assoc]
    simp only [ih]

/-! ### Components -/

variable (I) in
/-- The entity `v` is the value of some attribute at `u`. -/
def attrSucc (u v : U) : Prop := ∃ α : Sig.Attr, I.A α u = some v

instance [Fintype Sig.Attr] [DecidableEq U] : DecidableRel I.attrSucc :=
  fun _ _ ↦ by unfold attrSucc; infer_instance

variable (I) in
/-- The entity `v` is a component of `u` when a sequence of attributes leads from `u` to `v`. -/
abbrev IsComponentOf (u v : U) : Prop := Relation.ReflTransGen I.attrSucc u v

instance [Fintype U] [DecidableEq U] [Fintype Sig.Attr] (u v : U) :
    Decidable (I.IsComponentOf u v) :=
  Relation.ReflTransGen.decidable_of_fintype u v

/-- The components of `u` are the entities that some path denotes at `u`
([richter-2024], Definition 11). -/
theorem isComponentOf_iff_exists_path (g : ℕ → U) :
    I.IsComponentOf u v ↔ ∃ p : Path Sig, I.termDenot g (.path p) u = some v := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], rfl⟩
    | tail _ hα ih =>
      obtain ⟨α, hα⟩ := hα
      obtain ⟨p, hp⟩ := ih
      exact ⟨p ++ [α], by rw [Term.path_concat, termDenot_feat, hp]; exact hα⟩
  · rintro ⟨p, hp⟩
    induction p using List.reverseRecOn generalizing v with
    | nil => cases hp; exact .refl
    | append_singleton p α ih =>
      rw [Term.path_concat, termDenot_feat, Option.bind_eq_some_iff] at hp
      obtain ⟨w, hw, hα⟩ := hp
      exact (ih hw).tail ⟨α, hα⟩

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
    (h : I.termDenot g (.path p) u = some v) : Sig.Admits (I.S u) p (I.S v) := by
  induction p generalizing u with
  | nil => cases h; rfl
  | cons α p ih =>
    rw [termDenot_path_cons, Option.bind_eq_some_iff] at h
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

/-- A homomorphism commutes with term denotation. -/
theorem termDenot_comp (g : ℕ → U) (t : Term Sig) (u : U) :
    J.termDenot (f ∘ g) t (f u) = (I.termDenot g t u).map f := by
  induction t with
  | colon => rfl
  | var n => rfl
  | feat t α ih =>
    rw [termDenot_feat, termDenot_feat, ih]
    cases I.termDenot g t u <;> simp

theorem attrSucc (h : I.attrSucc u v) : J.attrSucc (f u) (f v) :=
  let ⟨α, hα⟩ := h; ⟨α, by rw [map_A f, hα]; rfl⟩

/-- A homomorphism maps the components of an entity to components of its image. -/
theorem isComponentOf (h : I.IsComponentOf u v) : J.IsComponentOf (f u) (f v) :=
  h.lift f fun _ _ ↦ attrSucc f

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

/-- An embedding is a homomorphism. -/
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

/-! ### The feature structure of an entity -/

section FeatureStructure

variable {Srt : Type u} [PartialOrder Srt] {Sig : Signature Srt} {U : Type v} {V : Type w}
  (I : Interpretation Sig U) {J : Interpretation Sig V} {u : U}

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

variable {I}

/-- Following a path from an entity is reading it in the machine of the interpretation. -/
theorem evalFrom_toPartialMoore (g : ℕ → U) (u : U) (p : Path Sig) :
    I.toPartialMoore.evalFrom u p = I.termDenot g (.path p) u := by
  induction p using List.reverseRecOn with
  | nil => rfl
  | append_singleton p α ih =>
    rw [PartialMoore.evalFrom_append_singleton, ih, Term.path_concat, termDenot_feat]
    rfl

/-- The components of an entity are the states its machine reaches from it. -/
theorem reaches_toPartialMoore_iff {q : U} :
    I.toPartialMoore.Reaches u q ↔ I.IsComponentOf u q := by
  rw [isComponentOf_iff_exists_path fun _ ↦ u]
  simp only [PartialMoore.Reaches, evalFrom_toPartialMoore fun _ ↦ u]

/-- A homomorphism, which keeps sorts and reflects attributes, is in particular a simulation:
the feature structure of an entity subsumes that of its image. -/
theorem Hom.simulatedBy (f : Hom I J) (u : U) :
    I.toPartialMoore.SimulatedBy J.toPartialMoore u (f u) :=
  ⟨f, rfl, fun q _ ↦ OrderDual.toDual_le_toDual.2 (HomClass.map_S f q).le, fun α q q' _ hα ↦ by
    show J.A α (f q) = some (f q')
    rw [HomClass.map_A]
    exact congrArg (Option.map f) hα⟩

end FeatureStructure

end Interpretation

end HPSG.RSRL
