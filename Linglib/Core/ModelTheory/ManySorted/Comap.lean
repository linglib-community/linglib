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

end Language

end ManySorted
