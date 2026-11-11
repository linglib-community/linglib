module

public import Linglib.Core.ModelTheory.ManySorted.Semantics
public import Mathlib.Tactic.Simps.Basic

/-!
# Maps between many-sorted languages

A map between two languages over the same sorts sends each symbol to a symbol with arguments of
the same shape and a result of the same sort, as `FirstOrder.Language.LHom` does for the
first-order languages of mathlib. Along a map a term of the first language is a term of the
second, a structure for the second restricts to one for the first, and where a structure for the
second expands one for the first, interpreting the image of each symbol as the symbol, [a term
keeps its value](##ManySorted.Language.LHom.realize_onTerm). Each of two languages maps into
their sum, whose structure expands both.

## Main definitions

* `ManySorted.Language.LHom`: a map of symbols that preserves argument shape and result sort.
* `ManySorted.Language.LHom.onTerm`: the term of the second language that a term of the first
  is.
* `ManySorted.Language.LHom.reduct`: the structure for the first language that a structure for
  the second restricts to.
* `ManySorted.Language.LHom.IsExpansionOn`: a structure for the second language interprets the
  image of each symbol as a structure for the first interprets the symbol.

## Implementation notes

The declarations are those of `Mathlib/ModelTheory/LanguageMap.lean`, in its order and under its
names, for function symbols typed by shape and sort. Two things differ. The structures are
arguments of `IsExpansionOn`, where mathlib takes them as instances, since a language here has
several structures over the same domains; the instances of mathlib are theorems here. And
`pi_isExpansionOn` has no counterpart, the structure on values that depend on a parameter being
defined here.
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

/-- The map of a language into the language with its binary symbols replaced, from a map of the
binary symbols: every other symbol is itself. -/
def withBinary {B : S → S → S → Type v} (f : ∀ {a b c : S}, L.Binary a b c → B a b c) :
    L →ᴸ L.withBinary B where
  onFunction σ _ g :=
    match σ, g with
    | .prod (.of _) (.of _), g => f g
    | .nil, g => g
    | .of _, g => g
    | .prod .nil _, g => g
    | .prod (.prod _ _) _, g => g
    | .prod (.of _) .nil, g => g
    | .prod (.of _) (.prod _ _), g => g

/-- The map between two replacements of the binary symbols of a language, from a map of the new
symbols: every other symbol is itself. -/
def mapBinary {B B' : S → S → S → Type v} (f : ∀ {a b c : S}, B a b c → B' a b c) :
    L.withBinary B →ᴸ L.withBinary B' where
  onFunction σ _ g :=
    match σ, g with
    | .prod (.of _) (.of _), g => f g
    | .nil, g => g
    | .of _, g => g
    | .prod .nil _, g => g
    | .prod (.prod _ _) _, g => g
    | .prod (.of _) .nil, g => g
    | .prod (.of _) (.prod _ _), g => g

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

/-- Replacing the binary symbols expands a structure where each new symbol means what the symbol
it replaces does. -/
theorem withBinary_isExpansionOn {B : S → S → S → Type v} {M : L.Structure D}
    {f : ∀ {a b c : S}, L.Binary a b c → B a b c}
    {binary : ∀ {a b c : S}, B a b c → D a → D b → D c}
    (h : ∀ {a b c : S} (g : L.Binary a b c) (x : D a) (y : D b),
      binary (f g) x y = M.funMap g (x, y)) :
    (LHom.withBinary (L := L) f).IsExpansionOn M (M.withBinary binary) where
  map_onFunction σ _ g x :=
    match σ, g with
    | .prod (.of _) (.of _), g => h g x.1 x.2
    | .nil, _ => rfl
    | .of _, _ => rfl
    | .prod .nil _, _ => rfl
    | .prod (.prod _ _) _, _ => rfl
    | .prod (.of _) .nil, _ => rfl
    | .prod (.of _) (.prod _ _), _ => rfl

/-- A map of the binary symbols that keeps their meanings is an expansion. -/
theorem mapBinary_isExpansionOn {B B' : S → S → S → Type v} {M : L.Structure D}
    {f : ∀ {a b c : S}, B a b c → B' a b c}
    {binary : ∀ {a b c : S}, B a b c → D a → D b → D c}
    {binary' : ∀ {a b c : S}, B' a b c → D a → D b → D c}
    (h : ∀ {a b c : S} (g : B a b c), binary' (f g) = binary g) :
    (LHom.mapBinary (L := L) f).IsExpansionOn (M.withBinary binary) (M.withBinary binary') where
  map_onFunction σ _ g x :=
    match σ, g with
    | .prod (.of _) (.of _), g => congrFun₂ (h g) x.1 x.2
    | .nil, _ => rfl
    | .of _, _ => rfl
    | .prod .nil _, _ => rfl
    | .prod (.prod _ _) _, _ => rfl
    | .prod (.of _) .nil, _ => rfl
    | .prod (.of _) (.prod _ _), _ => rfl

/-! ### Terms -/

/-- Maps a term's symbols along a language map. -/
def onTerm (φ : L →ᴸ L') : {σ : Signature S} → L.Term α σ → L'.Term α σ
  | _, .var x => .var x
  | _, .func f r => .func (φ.onFunction f) (φ.onTerm r)
  | _, .prod a b => .prod (φ.onTerm a) (φ.onTerm b)
  | _, .nil => .nil

@[simp] theorem id_onTerm {σ : Signature S} (t : L.Term α σ) : (LHom.id L).onTerm t = t := by
  induction t with
  | var x => rfl
  | func f r ih => simp only [onTerm, ih, id_onFunction, id_eq]
  | prod a b iha ihb => simp only [onTerm, iha, ihb]
  | nil => rfl

@[simp] theorem comp_onTerm (ψ : L' →ᴸ L'') (φ : L →ᴸ L') {σ : Signature S} (t : L.Term α σ) :
    (ψ ∘ᴸ φ).onTerm t = ψ.onTerm (φ.onTerm t) := by
  induction t with
  | var x => rfl
  | func f r ih => simp only [onTerm, ih, comp_onFunction]
  | prod a b iha ihb => simp only [onTerm, iha, ihb]
  | nil => rfl

@[simp] theorem realize_onTerm {M : L.Structure D} {M' : L'.Structure D}
    (h : φ.IsExpansionOn M M') (ρ : ∀ {s : S}, α s → D s) {σ : Signature S} (t : L.Term α σ) :
    (φ.onTerm t).realize M' ρ = t.realize M ρ := by
  induction t with
  | var x => rfl
  | func f r ih => simp only [onTerm, Term.realize, ih, h.map_onFunction]
  | prod a b iha ihb => simp only [onTerm, Term.realize, iha, ihb]
  | nil => rfl

end LHom

end ManySorted.Language
