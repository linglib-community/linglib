module

public import Linglib.Core.ModelTheory.ManySorted.LanguageMap

/-!
# A language along a map of sorts

A map of sorts `ι : S → S'` pulls a language over `S'` back to one over `S`, whose symbols at
sorts of `S` are the symbols of the language at their images, and pulls a structure back with it.
A map of a language over `S` into the pullback is a map of languages along `ι`, so the maps of
languages, their expansions and [the values of terms along
them](##ManySorted.Language.LHom.realize_onTerm) apply to languages over different sorts as they
stand.

## Main definitions

* `ManySorted.Signature.map`: a shape of arguments at the images of its sorts.
* `ManySorted.Language.comap`: the pullback of a language along a map of sorts.
* `ManySorted.Language.Structure.comap`: the pullback of a structure.
* `ManySorted.Language.IsBinary`: a language all of whose symbols take two arguments, with
  `ManySorted.Language.LHom.ofBinary`, a map out of one from a map of those symbols.
-/

@[expose] public section

universe u u' v w

namespace ManySorted

variable {S : Type u} {S' : Type u'} (ι : S → S')

/-- A shape of arguments at the images of its sorts. -/
def Signature.map : Signature S → Signature S'
  | .nil => .nil
  | .of s => .of (ι s)
  | .prod σ τ => .prod (σ.map) (τ.map)

/-- Arguments at the images of the sorts of a shape are arguments of the shape at the images. -/
def Signature.Interpret.toMap (D' : S' → Type w) :
    (σ : Signature S) → σ.Interpret (fun s ↦ D' (ι s)) → (σ.map ι).Interpret D'
  | .nil, x => x
  | .of _, x => x
  | .prod σ τ, x => (Signature.Interpret.toMap D' σ x.1, Signature.Interpret.toMap D' τ x.2)

namespace Language

/-- The pullback of a language along a map of sorts: its symbols with arguments of a shape and a
result of a sort are the symbols of the language at their images. -/
@[reducible] def comap (L' : Language.{u', v} S') : Language.{u, v} S where
  Functions σ t := L'.Functions (σ.map ι) (ι t)

variable {ι} {L' : Language.{u', v} S'} {D' : S' → Type w}

/-- The pullback of a structure along a map of sorts: a symbol denotes what it denotes at the
images. -/
@[instance_reducible] def Structure.comap (ι : S → S') (M' : L'.Structure D') :
    (L'.comap ι).Structure fun s ↦ D' (ι s) where
  funMap {σ _} f x := M'.funMap f (Signature.Interpret.toMap ι D' σ x)

@[simp] theorem Structure.funMap_comap_unary (M' : L'.Structure D') {a b : S}
    (f : L'.Unary (ι a) (ι b)) (x : D' (ι a)) :
    (M'.comap ι).funMap (σ := .of a) (t := b) f x = M'.funMap f x := rfl

@[simp] theorem Structure.funMap_comap_binary (M' : L'.Structure D') {a b c : S}
    (f : L'.Binary (ι a) (ι b) (ι c)) (x : D' (ι a)) (y : D' (ι b)) :
    (M'.comap ι).funMap (σ := .prod (.of a) (.of b)) (t := c) f (x, y) = M'.funMap f (x, y) :=
  rfl

/-- A language all of whose symbols take two arguments. -/
class IsBinary (L : Language.{u, v} S) : Prop where
  /-- There is no symbol of any other shape. -/
  isEmpty_of_ne (σ : Signature S) (t : S) (h : ∀ a b, σ ≠ .prod (.of a) (.of b)) :
    IsEmpty (L.Functions σ t)

instance {U : S → S → Type v} {B : S → S → S → Type v} [∀ a b, IsEmpty (U a b)] :
    (mk₂ U B).IsBinary where
  isEmpty_of_ne σ _ h :=
    match σ, h with
    | .nil, _ | .prod .nil _, _ | .prod (.prod _ _) _, _ | .prod (.of _) .nil, _
    | .prod (.of _) (.prod _ _), _ => ⟨nofun⟩
    | .of a, _ => inferInstanceAs (IsEmpty (U a _))
    | .prod (.of a) (.of b), h => absurd rfl (h a b)

instance {L₁ L₂ : Language.{u, v} S} [L₁.IsBinary] [L₂.IsBinary] : (L₁.sum L₂).IsBinary where
  isEmpty_of_ne σ t h :=
    ⟨fun
      | .inl f => (IsBinary.isEmpty_of_ne σ t h).elim f
      | .inr f => (IsBinary.isEmpty_of_ne σ t h).elim f⟩

instance {L : Language.{u, v} S} [L.IsBinary] {B : S → S → S → Type v} :
    (L.withBinary B).IsBinary where
  isEmpty_of_ne σ t h :=
    match σ, h with
    | .nil, h => IsBinary.isEmpty_of_ne (L := L) .nil t h
    | .of a, h => IsBinary.isEmpty_of_ne (L := L) (.of a) t h
    | .prod .nil τ, h => IsBinary.isEmpty_of_ne (L := L) (.prod .nil τ) t h
    | .prod (.prod σ₁ σ₂) τ, h => IsBinary.isEmpty_of_ne (L := L) (.prod (.prod σ₁ σ₂) τ) t h
    | .prod (.of a) .nil, h => IsBinary.isEmpty_of_ne (L := L) (.prod (.of a) .nil) t h
    | .prod (.of a) (.prod τ₁ τ₂), h =>
      IsBinary.isEmpty_of_ne (L := L) (.prod (.of a) (.prod τ₁ τ₂)) t h
    | .prod (.of a) (.of b), h => absurd rfl (h a b)

namespace LHom

variable {L L'' : Language.{u, v} S} {D : S → Type w}

/-- A map out of a language whose symbols all take two arguments, from a map of those symbols. -/
def ofBinary [L.IsBinary] (f : ∀ {a b c : S}, L.Binary a b c → L''.Binary a b c) : L →ᴸ L'' where
  onFunction σ t g :=
    match σ, g with
    | .prod (.of _) (.of _), g => f g
    | .nil, g => (IsBinary.isEmpty_of_ne .nil t fun _ _ h ↦ nomatch h).elim g
    | .of a, g => (IsBinary.isEmpty_of_ne (.of a) t fun _ _ h ↦ nomatch h).elim g
    | .prod .nil τ, g => (IsBinary.isEmpty_of_ne (.prod .nil τ) t fun _ _ h ↦ nomatch h).elim g
    | .prod (.prod σ₁ σ₂) τ, g =>
      (IsBinary.isEmpty_of_ne (.prod (.prod σ₁ σ₂) τ) t fun _ _ h ↦ nomatch h).elim g
    | .prod (.of a) .nil, g =>
      (IsBinary.isEmpty_of_ne (.prod (.of a) .nil) t fun _ _ h ↦ nomatch h).elim g
    | .prod (.of a) (.prod τ₁ τ₂), g =>
      (IsBinary.isEmpty_of_ne (.prod (.of a) (.prod τ₁ τ₂)) t fun _ _ h ↦ nomatch h).elim g

/-- A map out of a language of binary symbols is an expansion where it is one on them. -/
theorem ofBinary_isExpansionOn [L.IsBinary] {f : ∀ {a b c : S}, L.Binary a b c → L''.Binary a b c}
    {M : L.Structure D} {M'' : L''.Structure D}
    (h : ∀ {a b c : S} (g : L.Binary a b c) (x : D a) (y : D b),
      M''.funMap (f g) (x, y) = M.funMap g (x, y)) :
    (ofBinary f).IsExpansionOn M M'' where
  map_onFunction σ t g x :=
    match σ, g with
    | .prod (.of _) (.of _), g => h g x.1 x.2
    | .nil, g => (IsBinary.isEmpty_of_ne .nil t fun _ _ h ↦ nomatch h).elim g
    | .of a, g => (IsBinary.isEmpty_of_ne (.of a) t fun _ _ h ↦ nomatch h).elim g
    | .prod .nil τ, g => (IsBinary.isEmpty_of_ne (.prod .nil τ) t fun _ _ h ↦ nomatch h).elim g
    | .prod (.prod σ₁ σ₂) τ, g =>
      (IsBinary.isEmpty_of_ne (.prod (.prod σ₁ σ₂) τ) t fun _ _ h ↦ nomatch h).elim g
    | .prod (.of a) .nil, g =>
      (IsBinary.isEmpty_of_ne (.prod (.of a) .nil) t fun _ _ h ↦ nomatch h).elim g
    | .prod (.of a) (.prod τ₁ τ₂), g =>
      (IsBinary.isEmpty_of_ne (.prod (.of a) (.prod τ₁ τ₂)) t fun _ _ h ↦ nomatch h).elim g

variable {U : S → S → Type v} {B : S → S → S → Type v}

/-- A map out of a language of unary and binary symbols, from a map of each family. -/
def ofMk₂ (fu : ∀ {a b : S}, U a b → L''.Unary a b)
    (fb : ∀ {a b c : S}, B a b c → L''.Binary a b c) : mk₂ U B →ᴸ L'' where
  onFunction σ _ g :=
    match σ, g with
    | .of _, g => fu g
    | .prod (.of _) (.of _), g => fb g
    | .nil, g | .prod .nil _, g | .prod (.prod _ _) _, g | .prod (.of _) .nil, g
    | .prod (.of _) (.prod _ _), g => nomatch g

/-- A map out of a language of unary and binary symbols is an expansion where it is one on each
family. -/
theorem ofMk₂_isExpansionOn {fu : ∀ {a b : S}, U a b → L''.Unary a b}
    {fb : ∀ {a b c : S}, B a b c → L''.Binary a b c} {M : (mk₂ U B).Structure D}
    {M'' : L''.Structure D}
    (hu : ∀ {a b : S} (g : U a b) (x : D a), M''.funMap (fu g) x = M.funMap (σ := .of a) g x)
    (hb : ∀ {a b c : S} (g : B a b c) (x : D a) (y : D b),
      M''.funMap (fb g) (x, y) = M.funMap (σ := .prod (.of a) (.of b)) g (x, y)) :
    (ofMk₂ fu fb).IsExpansionOn M M'' where
  map_onFunction σ _ g x :=
    match σ, g with
    | .of _, g => hu g x
    | .prod (.of _) (.of _), g => hb g x.1 x.2
    | .nil, g | .prod .nil _, g | .prod (.prod _ _) _, g | .prod (.of _) .nil, g
    | .prod (.of _) (.prod _ _), g => nomatch g

end LHom

end Language

end ManySorted
