module

public import Linglib.Core.ModelTheory.ManySorted.Basic
public import Mathlib.Tactic.Simps.Basic

/-!
# Maps between many-sorted languages

A map between two languages over the same sorts sends each symbol to a symbol with arguments of
the same shape and a result of the same sort, as `FirstOrder.Language.LHom` does for the
first-order languages of mathlib. Along a map a structure for the second language restricts to
one for the first, and a structure for the second expands one for the first when it interprets the
image of each symbol as the symbol. Each of two languages maps into their sum, whose structure
expands both, and a language with constants added is the sum of the language with a language of
constants.

## Main definitions

* `ManySorted.Language.LHom`: a map of symbols that preserves argument shape and result sort.
* `ManySorted.Language.LHom.reduct`: the structure for the first language that a structure for
  the second restricts to.
* `ManySorted.Language.LHom.IsExpansionOn`: a structure for the second language interprets the
  image of each symbol as a structure for the first interprets the symbol.
* `ManySorted.Language.constantsOn`, `ManySorted.Language.withConstants`: a language of
  constants of each sort, and a language with such constants added.

## Implementation notes

The declarations are those of `Mathlib/ModelTheory/LanguageMap.lean`, in its order and under its
names, for function symbols typed by shape and sort; the constants of a language are a family
over the sorts. Two things differ. The structures are arguments of `IsExpansionOn`, where mathlib
takes them as instances, since a language here has several structures over the same domains; the
instances of mathlib are theorems here. The notation `L[[γ]]` is not declared, its brackets being
those of nested lists and of labelled trees. And `pi_isExpansionOn` has no counterpart, the
structure on values that depend on a parameter being defined here.
-/

@[expose] public section

universe u v w x

namespace ManySorted.Language

variable {S : Type u} (L L' : Language.{u, v} S) {α : S → Type w} {D : S → Type x}

/-- A language homomorphism maps the symbols of one language to symbols of another, with
arguments of the same shape and a result of the same sort. -/
structure LHom where
  /-- The mapping of functions. -/
  onFunction : ∀ ⦃σ : Signature S⦄ ⦃t : S⦄, L.Functions σ t → L'.Functions σ t

@[inherit_doc] scoped[ManySorted] infixl:10 " →ᴸ " => ManySorted.Language.LHom

variable {L L'}

namespace LHom

variable (φ : L →ᴸ L')

/-- Pulls a structure back along a language map. -/
@[instance_reducible] def reduct (M' : L'.Structure D) : L.Structure D where
  funMap f x := M'.funMap (φ.onFunction f) x

/-- The identity language homomorphism. -/
@[simps] protected def id (L : Language.{u, v} S) : L →ᴸ L := ⟨fun _ _ ↦ id⟩

/-- The inclusion of the left factor into the sum of two languages. -/
@[simps] protected def sumInl : L →ᴸ L.sum L' := ⟨fun _ _ ↦ .inl⟩

/-- The inclusion of the right factor into the sum of two languages. -/
@[simps] protected def sumInr : L' →ᴸ L.sum L' := ⟨fun _ _ ↦ .inr⟩

variable {L'' : Language.{u, v} S}

@[ext]
protected theorem funext {F G : L →ᴸ L'} (h_fun : F.onFunction = G.onFunction) : F = G := by
  obtain ⟨Ff⟩ := F
  obtain ⟨Gf⟩ := G
  simp only [mk.injEq]
  exact h_fun

/-- The composition of two language homomorphisms. -/
@[simps] def comp (g : L' →ᴸ L'') (f : L →ᴸ L') : L →ᴸ L'' :=
  ⟨fun _ _ F ↦ g.onFunction (f.onFunction F)⟩

@[inherit_doc] scoped[ManySorted] infixl:60 " ∘ᴸ " => ManySorted.Language.LHom.comp

@[simp] theorem id_comp (F : L →ᴸ L') : LHom.id L' ∘ᴸ F = F := rfl

@[simp] theorem comp_id (F : L →ᴸ L') : F ∘ᴸ LHom.id L = F := rfl

theorem comp_assoc {L3 : Language.{u, v} S} (F : L'' →ᴸ L3) (G : L' →ᴸ L'') (H : L →ᴸ L') :
    F ∘ᴸ G ∘ᴸ H = F ∘ᴸ (G ∘ᴸ H) :=
  rfl

section SumElim

variable (ψ : L'' →ᴸ L')

/-- A language map defined on two factors of a sum. -/
protected def sumElim : L.sum L'' →ᴸ L' where
  onFunction _ _
    | .inl f => φ.onFunction f
    | .inr f => ψ.onFunction f

@[simp] theorem sumElim_onFunction_inl {σ : Signature S} {t : S} (f : L.Functions σ t) :
    (φ.sumElim ψ).onFunction (.inl f) = φ.onFunction f := rfl

@[simp] theorem sumElim_onFunction_inr {σ : Signature S} {t : S} (f : L''.Functions σ t) :
    (φ.sumElim ψ).onFunction (.inr f) = ψ.onFunction f := rfl

theorem sumElim_comp_inl : φ.sumElim ψ ∘ᴸ LHom.sumInl = φ := rfl

theorem sumElim_comp_inr : φ.sumElim ψ ∘ᴸ LHom.sumInr = ψ := rfl

theorem sumElim_inl_inr : LHom.sumInl.sumElim LHom.sumInr = LHom.id (L.sum L') :=
  LHom.funext (funext fun _ ↦ funext fun _ ↦ funext fun f ↦ by cases f <;> rfl)

theorem comp_sumElim {L3 : Language.{u, v} S} (θ : L' →ᴸ L3) :
    θ ∘ᴸ φ.sumElim ψ = (θ ∘ᴸ φ).sumElim (θ ∘ᴸ ψ) :=
  LHom.funext (funext fun _ ↦ funext fun _ ↦ funext fun f ↦ by cases f <;> rfl)

end SumElim

section SumMap

variable {L₁ L₂ : Language.{u, v} S} (ψ : L₁ →ᴸ L₂)

/-- The map between two sum-languages induced by maps on the two factors. -/
def sumMap : L.sum L₁ →ᴸ L'.sum L₂ where
  onFunction _ _
    | .inl f => .inl (φ.onFunction f)
    | .inr f => .inr (ψ.onFunction f)

@[simp] theorem sumMap_onFunction_inl {σ : Signature S} {t : S} (f : L.Functions σ t) :
    (φ.sumMap ψ).onFunction (.inl f) = .inl (φ.onFunction f) := rfl

@[simp] theorem sumMap_onFunction_inr {σ : Signature S} {t : S} (f : L₁.Functions σ t) :
    (φ.sumMap ψ).onFunction (.inr f) = .inr (ψ.onFunction f) := rfl

@[simp] theorem sumMap_comp_inl : φ.sumMap ψ ∘ᴸ LHom.sumInl = LHom.sumInl ∘ᴸ φ := rfl

@[simp] theorem sumMap_comp_inr : φ.sumMap ψ ∘ᴸ LHom.sumInr = LHom.sumInr ∘ᴸ ψ := rfl

end SumMap

/-! ### Expansions -/

/-- A language homomorphism is an expansion on a pair of structures if it commutes with the
interpretation of all symbols. -/
structure IsExpansionOn (M : L.Structure D) (M' : L'.Structure D) : Prop where
  map_onFunction : ∀ ⦃σ : Signature S⦄ ⦃t : S⦄ (f : L.Functions σ t) (x : σ.Interpret D),
    M'.funMap (φ.onFunction f) x = M.funMap f x

variable {φ}

theorem id_isExpansionOn (M : L.Structure D) : (LHom.id L).IsExpansionOn M M :=
  ⟨fun _ _ _ _ ↦ rfl⟩

theorem sumElim_isExpansionOn {ψ : L'' →ᴸ L'} {M : L.Structure D} {M' : L'.Structure D}
    {M'' : L''.Structure D} (hφ : φ.IsExpansionOn M M') (hψ : ψ.IsExpansionOn M'' M') :
    (φ.sumElim ψ).IsExpansionOn (M.sum M'') M' :=
  ⟨fun _ _ f x ↦ match f with
    | .inl f => hφ.map_onFunction f x
    | .inr f => hψ.map_onFunction f x⟩

theorem sumMap_isExpansionOn {L₁ L₂ : Language.{u, v} S} {ψ : L₁ →ᴸ L₂} {M : L.Structure D}
    {M' : L'.Structure D} {M₁ : L₁.Structure D} {M₂ : L₂.Structure D}
    (hφ : φ.IsExpansionOn M M') (hψ : ψ.IsExpansionOn M₁ M₂) :
    (φ.sumMap ψ).IsExpansionOn (M.sum M₁) (M'.sum M₂) :=
  ⟨fun _ _ f x ↦ match f with
    | .inl f => hφ.map_onFunction f x
    | .inr f => hψ.map_onFunction f x⟩

theorem sumInl_isExpansionOn (M : L.Structure D) (M' : L'.Structure D) :
    (LHom.sumInl : L →ᴸ L.sum L').IsExpansionOn M (M.sum M') :=
  ⟨fun _ _ _ _ ↦ rfl⟩

theorem sumInr_isExpansionOn (M : L.Structure D) (M' : L'.Structure D) :
    (LHom.sumInr : L' →ᴸ L.sum L').IsExpansionOn M' (M.sum M') :=
  ⟨fun _ _ _ _ ↦ rfl⟩

theorem isExpansionOn_reduct (φ : L →ᴸ L') (M' : L'.Structure D) :
    φ.IsExpansionOn (φ.reduct M') M' :=
  ⟨fun _ _ _ _ ↦ rfl⟩

/-- An expansion is one of the structures on values that depend on a parameter. -/
theorem pi_isExpansionOn {M : L.Structure D} {M' : L'.Structure D} (h : φ.IsExpansionOn M M')
    (A : Type x) : φ.IsExpansionOn (M.pi A) (M'.pi A) :=
  ⟨fun _ _ f _ ↦ funext fun _ ↦ h.map_onFunction f _⟩

end LHom

/-! ### Constants -/

section ConstantsOn

variable (γ : S → Type v)

/-- The type of functions for a language consisting only of constant symbols. -/
@[simp] def constantsOnFunc : Signature S → S → Type v
  | .nil, t => γ t
  | _, _ => PEmpty

/-- A language with constants of each sort indexed by a type. -/
@[reducible] def constantsOn : Language.{u, v} S := ⟨constantsOnFunc γ⟩

variable {γ}

/-- Gives a `constantsOn γ` structure to a family of domains by assigning each constant a
value. -/
@[instance_reducible] def constantsOn.structure (f : ∀ {s : S}, γ s → D s) :
    (constantsOn γ).Structure D where
  funMap {σ _} c _ :=
    match σ, c with
    | .nil, c => f c

@[simp] theorem constantsOn.funMap_structure (f : ∀ {s : S}, γ s → D s) {s : S} (c : γ s)
    (x : PUnit) : (constantsOn.structure (D := D) f).funMap (σ := .nil) (t := s) c x = f c := rfl

variable {γ' : S → Type v}

/-- A map between index types induces a map between constant languages. -/
def LHom.constantsOnMap (f : ∀ {s : S}, γ s → γ' s) : constantsOn γ →ᴸ constantsOn γ' where
  onFunction σ _ c :=
    match σ, c with
    | .nil, c => f c

theorem constantsOnMap_isExpansionOn {f : ∀ {s : S}, γ s → γ' s} {fγ : ∀ {s : S}, γ s → D s}
    {fγ' : ∀ {s : S}, γ' s → D s} (h : ∀ (s : S) (c : γ s), fγ' (f c) = fγ c) :
    (LHom.constantsOnMap (γ := γ) (γ' := γ') f).IsExpansionOn (D := D)
      (constantsOn.structure fγ) (constantsOn.structure fγ') :=
  ⟨fun σ _ c _ ↦ match σ, c with
    | .nil, c => h _ c⟩

end ConstantsOn

section WithConstants

variable (L) (γ : S → Type v)

/-- Extends a language with a constant of each sort for each element of a type. -/
@[reducible] def withConstants : Language.{u, v} S := L.sum (constantsOn γ)

/-- The language map adding constants. -/
def lhomWithConstants : L →ᴸ L.withConstants γ := LHom.sumInl

@[simp] theorem lhomWithConstants_onFunction {σ : Signature S} {t : S} (f : L.Functions σ t) :
    (L.lhomWithConstants γ).onFunction f = .inl f := rfl

variable {γ}

/-- The constant symbol indexed by a particular element. -/
protected def con {s : S} (c : γ s) : (L.withConstants γ).Functions .nil s := .inr c

variable {L} (γ)

/-- Adds constants to a language map. -/
def LHom.addConstants (φ : L →ᴸ L') : L.withConstants γ →ᴸ L'.withConstants γ :=
  φ.sumMap (LHom.id _)

variable (L) {γ} {γ' : S → Type v}

/-- The language map extending the constant set. -/
def lhomWithConstantsMap (f : ∀ {s : S}, γ s → γ' s) :
    L.withConstants γ →ᴸ L.withConstants γ' :=
  LHom.sumMap (LHom.id L) (LHom.constantsOnMap f)

@[simp] theorem LHom.map_constants_comp_sumInl {f : ∀ {s : S}, γ s → γ' s} :
    (L.lhomWithConstantsMap f).comp LHom.sumInl = L.lhomWithConstants γ' := rfl

/-- The structure for a language with constants that a structure for the language and values
for the constants make. -/
@[instance_reducible] def withConstantsStructure (M : L.Structure D)
    (f : ∀ {s : S}, γ s → D s) : (L.withConstants γ).Structure D :=
  M.sum (constantsOn.structure f)

theorem withConstants_expansion (M : L.Structure D) (f : ∀ {s : S}, γ s → D s) :
    (L.lhomWithConstants γ).IsExpansionOn M (L.withConstantsStructure M f) :=
  ⟨fun _ _ _ _ ↦ rfl⟩

@[simp] theorem withConstantsStructure_funMap_con (M : L.Structure D)
    (f : ∀ {s : S}, γ s → D s) {s : S} (c : γ s) (x : PUnit) :
    (L.withConstantsStructure M f).funMap (L.con c) x = f c := rfl

end WithConstants

end ManySorted.Language
