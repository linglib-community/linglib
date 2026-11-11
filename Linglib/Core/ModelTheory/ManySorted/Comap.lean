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
* `ManySorted.Language.IsBinary`: a language all of whose symbols take two arguments.
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
def Signature.Interpret.map (D' : S' → Type w) :
    (σ : Signature S) → σ.Interpret (fun s ↦ D' (ι s)) → (σ.map ι).Interpret D'
  | .nil, x => x
  | .of _, x => x
  | .prod σ τ, x => (Signature.Interpret.map D' σ x.1, Signature.Interpret.map D' τ x.2)

namespace Language

/-- The pullback of a language along a map of sorts: its symbols with arguments of a shape and a
result of a sort are the symbols of the language at their images. -/
def comap (L' : Language.{u', v} S') : Language.{u, v} S where
  Functions σ t := L'.Functions (σ.map ι) (ι t)

variable {ι} {L' : Language.{u', v} S'} {D' : S' → Type w}

/-- The pullback of a structure along a map of sorts: a symbol denotes what it denotes at the
images. -/
@[instance_reducible] def Structure.comap (ι : S → S') (M' : L'.Structure D') :
    (L'.comap ι).Structure fun s ↦ D' (ι s) where
  funMap {σ _} f x := M'.funMap f (Signature.Interpret.map ι D' σ x)

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

section

variable (L : Language.{u, v} S) [L.IsBinary] (t : S)

instance : IsEmpty (L.Functions .nil t) :=
  IsBinary.isEmpty_of_ne .nil t fun _ _ h ↦ nomatch h

instance (a : S) : IsEmpty (L.Functions (.of a) t) :=
  IsBinary.isEmpty_of_ne (.of a) t fun _ _ h ↦ nomatch h

instance (τ : Signature S) : IsEmpty (L.Functions (.prod .nil τ) t) :=
  IsBinary.isEmpty_of_ne (.prod .nil τ) t fun _ _ h ↦ nomatch h

instance (σ₁ σ₂ τ : Signature S) : IsEmpty (L.Functions (.prod (.prod σ₁ σ₂) τ) t) :=
  IsBinary.isEmpty_of_ne (.prod (.prod σ₁ σ₂) τ) t fun _ _ h ↦ nomatch h

instance (a : S) : IsEmpty (L.Functions (.prod (.of a) .nil) t) :=
  IsBinary.isEmpty_of_ne (.prod (.of a) .nil) t fun _ _ h ↦ nomatch h

instance (a : S) (τ₁ τ₂ : Signature S) :
    IsEmpty (L.Functions (.prod (.of a) (.prod τ₁ τ₂)) t) :=
  IsBinary.isEmpty_of_ne (.prod (.of a) (.prod τ₁ τ₂)) t fun _ _ h ↦ nomatch h

end

instance {B : S → S → S → Type v} : (mk₂ (fun _ _ ↦ PEmpty) B).IsBinary where
  isEmpty_of_ne σ _ h :=
    match σ, h with
    | .nil, _ | .of _, _ | .prod .nil _, _ | .prod (.prod _ _) _, _ | .prod (.of _) .nil, _
    | .prod (.of _) (.prod _ _), _ => ⟨nofun⟩
    | .prod (.of a) (.of b), h => absurd rfl (h a b)

instance {L₁ L₂ : Language.{u, v} S} [L₁.IsBinary] [L₂.IsBinary] : (L₁.sum L₂).IsBinary where
  isEmpty_of_ne σ t h :=
    ⟨fun
      | .inl f => (IsBinary.isEmpty_of_ne σ t h).elim f
      | .inr f => (IsBinary.isEmpty_of_ne σ t h).elim f⟩

end Language

end ManySorted
