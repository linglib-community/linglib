module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.List.Basic

/-!
# Many-sorted algebraic languages and structures

A many-sorted language has function symbols typed by the sorts of their arguments and the sort of
their result, where a first-order language of mathlib has symbols of each arity. The arguments of
a symbol have a shape, a `Signature`: none, one of a sort, or a pair of shapes, and a structure
gives each symbol a function from the product of domains that its shape describes.

## Main definitions

* `ManySorted.Signature`: the shape of a symbol's arguments.
* `ManySorted.Signature.Interpret`: the arguments of a shape, over a family of domains.
* `ManySorted.Language`: function symbols by argument shape and result sort.
* `ManySorted.Language.Structure`: a function for each symbol, over a family of domains.
* `ManySorted.Language.mk₂`: the language of a family of unary and a family of binary symbols.
* `ManySorted.Language.sum`: the sum of two languages, with
  [the function a symbol of one denotes in it](##ManySorted.Language.Structure.funMap_sum_inl).
* `ManySorted.Language.Structure.pi`: the structure on values that depend on a parameter.
* `ManySorted.Language.LocallyFinite`: the symbols that take given arguments can be listed.

## Implementation notes

The definitions follow the many-sorted generalization of `FirstOrder.Language` being developed
outside mathlib, in which a shape is a binary tree of sorts read as a nested product, so that a
binary symbol takes a pair. Only function symbols are defined: a language here is what that
development calls algebraic. The domains are a parameter of a structure.
-/

@[expose] public section

universe u v w x

namespace ManySorted

/-- The shape of a symbol's arguments over sorts `S`: none, one of a sort, or a pair of shapes. -/
inductive Signature (S : Type u) where
  /-- No arguments. -/
  | nil : Signature S
  /-- One argument of a sort. -/
  | of (s : S) : Signature S
  /-- The arguments of one shape paired with those of another. -/
  | prod (σ τ : Signature S) : Signature S

variable {S : Type u}

/-- The arguments of a shape over the domains `X`: a nested product. -/
abbrev Signature.Interpret (X : S → Type w) : Signature S → Type w
  | .nil => PUnit
  | .of s => X s
  | .prod σ τ => Interpret X σ × Interpret X τ

/-- A many-sorted algebraic language over sorts `S`: the function symbols with arguments of a
given shape and a result of a given sort. -/
structure Language (S : Type u) where
  /-- The function symbols with arguments of shape `σ` and result of sort `t`. -/
  Functions : Signature S → S → Type v

/-- A structure for a language over the domains `D`: a function for each symbol. -/
class Language.Structure (L : Language.{u, v} S) (D : S → Type w) where
  /-- The function a symbol denotes. -/
  funMap {σ : Signature S} {t : S} : L.Functions σ t → σ.Interpret D → D t

namespace Language

variable {L L' : Language.{u, v} S} {D : S → Type w}

/-- The symbols of a language with one argument. -/
abbrev Unary (L : Language.{u, v} S) (a b : S) : Type v := L.Functions (.of a) b

/-- The symbols of a language with two arguments. -/
abbrev Binary (L : Language.{u, v} S) (a b c : S) : Type v :=
  L.Functions (.prod (.of a) (.of b)) c

/-! ### Languages of unary and binary symbols -/

/-- The language whose symbols are those of two families, of one argument and of two. -/
@[reducible] def mk₂ (U : S → S → Type v) (B : S → S → S → Type v) : Language.{u, v} S where
  Functions
    | .of a, b => U a b
    | .prod (.of a) (.of b), c => B a b c
    | _, _ => PEmpty

variable {U : S → S → Type v} {B : S → S → S → Type v}

/-- A structure for a language of unary and binary symbols, from a function for each. -/
@[instance_reducible] def Structure.mk₂ (unary : ∀ {a b : S}, U a b → D a → D b)
    (binary : ∀ {a b c : S}, B a b c → D a → D b → D c) : (Language.mk₂ U B).Structure D where
  funMap {σ _} f x :=
    match σ, f, x with
    | .of _, f, x => unary f x
    | .prod (.of _) (.of _), f, x => binary f x.1 x.2
    | .nil, f, _ => nomatch f
    | .prod .nil _, f, _ => nomatch f
    | .prod (.prod _ _) _, f, _ => nomatch f
    | .prod (.of _) .nil, f, _ => nomatch f
    | .prod (.of _) (.prod _ _), f, _ => nomatch f

@[simp] theorem Structure.funMap_mk₂_unary (unary : ∀ {a b : S}, U a b → D a → D b)
    (binary : ∀ {a b c : S}, B a b c → D a → D b → D c) {a b : S} (f : U a b) (x : D a) :
    (Structure.mk₂ (U := U) (B := B) (D := D) unary binary).funMap (σ := .of a) (t := b) f x =
      unary f x := rfl

@[simp] theorem Structure.funMap_mk₂_binary (unary : ∀ {a b : S}, U a b → D a → D b)
    (binary : ∀ {a b c : S}, B a b c → D a → D b → D c) {a b c : S} (f : B a b c)
    (p : D a × D b) :
    (Structure.mk₂ (U := U) (B := B) (D := D) unary binary).funMap
      (σ := .prod (.of a) (.of b)) (t := c) f p = binary f p.1 p.2 := rfl

/-! ### Replacing the binary symbols -/

/-- The language whose symbols of two arguments are those of a family, and whose other symbols
are those of `L`. -/
@[reducible] def withBinary (L : Language.{u, v} S) (B : S → S → S → Type v) :
    Language.{u, v} S where
  Functions
    | .prod (.of a) (.of b), c => B a b c
    | σ, c => L.Functions σ c

/-- A structure for a language with its binary symbols replaced, from a structure for the
language and a function for each new symbol. -/
@[instance_reducible] def Structure.withBinary {B : S → S → S → Type v} (M : L.Structure D)
    (binary : ∀ {a b c : S}, B a b c → D a → D b → D c) : (L.withBinary B).Structure D where
  funMap {σ _} f x :=
    match σ, f, x with
    | .prod (.of _) (.of _), f, x => binary f x.1 x.2
    | .nil, f, x => M.funMap f x
    | .of _, f, x => M.funMap f x
    | .prod .nil _, f, x => M.funMap f x
    | .prod (.prod _ _) _, f, x => M.funMap f x
    | .prod (.of _) .nil, f, x => M.funMap f x
    | .prod (.of _) (.prod _ _), f, x => M.funMap f x

/-! ### The sum of two languages -/

/-- A symbol of one of two languages. It is indexed by the languages, where `_root_.Sum` would
be indexed by their types of symbols, so that a statement about the symbols of any two languages
applies to two given ones whatever their types of symbols unfold to. -/
inductive Sum (L L' : Language.{u, v} S) (σ : Signature S) (t : S) : Type v
  /-- A symbol of the first language. -/
  | inl (f : L.Functions σ t) : Sum L L' σ t
  /-- A symbol of the second language. -/
  | inr (f : L'.Functions σ t) : Sum L L' σ t

/-- The sum of two languages, with the symbols of both. -/
@[reducible] protected def sum (L L' : Language.{u, v} S) : Language.{u, v} S := ⟨Sum L L'⟩

/-- A structure for the sum of two languages, from a structure for each. -/
@[instance_reducible] def Structure.sum (M : L.Structure D) (M' : L'.Structure D) :
    (L.sum L').Structure D where
  funMap f x :=
    match f with
    | .inl f => M.funMap f x
    | .inr f => M'.funMap f x

instance [M : L.Structure D] [M' : L'.Structure D] : (L.sum L').Structure D := M.sum M'

@[simp] theorem Structure.funMap_sum_inl (M : L.Structure D) (M' : L'.Structure D)
    {σ : Signature S} {t : S} (f : L.Functions σ t) (x : σ.Interpret D) :
    (M.sum M').funMap (Sum.inl f : (L.sum L').Functions σ t) x = M.funMap f x := rfl

@[simp] theorem Structure.funMap_sum_inr (M : L.Structure D) (M' : L'.Structure D)
    {σ : Signature S} {t : S} (f : L'.Functions σ t) (x : σ.Interpret D) :
    (M.sum M').funMap (Sum.inr f : (L.sum L').Functions σ t) x = M'.funMap f x := rfl

/-! ### Structures over a parameter -/

/-- The arguments of a shape at one value of a parameter. -/
def _root_.ManySorted.Signature.Interpret.app {A : Type x} :
    {σ : Signature S} → σ.Interpret (fun s ↦ A → D s) → A → σ.Interpret D
  | .nil, _, _ => ⟨⟩
  | .of _, f, g => f g
  | .prod _ _, p, g => (Signature.Interpret.app p.1 g, Signature.Interpret.app p.2 g)

@[simp] theorem _root_.ManySorted.Signature.Interpret.app_of {A : Type x} {s : S}
    (f : A → D s) (g : A) : Signature.Interpret.app (σ := .of s) f g = f g := rfl

@[simp] theorem _root_.ManySorted.Signature.Interpret.app_prod {A : Type x} {σ τ : Signature S}
    (p : (σ.prod τ).Interpret fun s ↦ A → D s) (g : A) :
    Signature.Interpret.app p g =
      (Signature.Interpret.app p.1 g, Signature.Interpret.app p.2 g) := rfl

/-- The structure on values that depend on a parameter: each symbol applies at one value of the
parameter. -/
@[instance_reducible] def Structure.pi (A : Type x) (M : L.Structure D) :
    L.Structure fun s ↦ A → D s where
  funMap f p := fun g ↦ M.funMap f (Signature.Interpret.app p g)

theorem Structure.funMap_pi {A : Type x} (M : L.Structure D) {σ : Signature S} {t : S}
    (f : L.Functions σ t) (p : σ.Interpret fun s ↦ A → D s) :
    (M.pi A).funMap f p = fun g ↦ M.funMap f (Signature.Interpret.app p g) := rfl

@[simp] theorem Structure.funMap_pi_unary {A : Type x} (M : L.Structure D) {a b : S}
    (f : L.Unary a b) (x : A → D a) :
    (M.pi A).funMap (σ := .of a) f x = fun g ↦ M.funMap f (x g) := rfl

@[simp] theorem Structure.funMap_pi_binary {A : Type x} (M : L.Structure D) {a b c : S}
    (f : L.Binary a b c) (p : (A → D a) × (A → D b)) :
    (M.pi A).funMap (σ := .prod (.of a) (.of b)) f p = fun g ↦ M.funMap f (p.1 g, p.2 g) := rfl

/-! ### Listing the symbols that apply -/

/-- A language is locally finite when the symbols that take arguments of a given shape can be
listed. -/
class LocallyFinite (L : Language.{u, v} S) where
  /-- The symbols that take arguments of shape `σ`. -/
  symbols : (σ : Signature S) → List (Σ t, L.Functions σ t)
  /-- Every symbol is listed. -/
  mem_symbols {σ : Signature S} {t : S} (f : L.Functions σ t) : ⟨t, f⟩ ∈ symbols σ

/-- A language of unary and binary symbols is locally finite when the symbols of each family
that apply can be listed. -/
@[instance_reducible] def LocallyFinite.mk₂ (us : ∀ a, List (Σ b, U a b))
    (bs : ∀ a b, List (Σ c, B a b c)) (hu : ∀ {a b} (f : U a b), ⟨b, f⟩ ∈ us a)
    (hb : ∀ {a b c} (f : B a b c), ⟨c, f⟩ ∈ bs a b) : (Language.mk₂ U B).LocallyFinite where
  symbols
    | .of a => us a
    | .prod (.of a) (.of b) => bs a b
    | _ => []
  mem_symbols {σ _} f :=
    match σ, f with
    | .of _, f => hu f
    | .prod (.of _) (.of _), f => hb f
    | .nil, f => nomatch f
    | .prod .nil _, f => nomatch f
    | .prod (.prod _ _) _, f => nomatch f
    | .prod (.of _) .nil, f => nomatch f
    | .prod (.of _) (.prod _ _), f => nomatch f

instance [L.LocallyFinite] [L'.LocallyFinite] : (L.sum L').LocallyFinite where
  symbols σ := ((LocallyFinite.symbols (L := L) σ).map fun ⟨t, f⟩ ↦ ⟨t, .inl f⟩) ++
    (LocallyFinite.symbols (L := L') σ).map fun ⟨t, f⟩ ↦ ⟨t, .inr f⟩
  mem_symbols
    | .inl f => List.mem_append_left _ (List.mem_map.2 ⟨_, LocallyFinite.mem_symbols f, rfl⟩)
    | .inr f => List.mem_append_right _ (List.mem_map.2 ⟨_, LocallyFinite.mem_symbols f, rfl⟩)

@[simp] theorem LocallyFinite.symbols_sum [L.LocallyFinite] [L'.LocallyFinite]
    (σ : Signature S) :
    LocallyFinite.symbols (L := L.sum L') σ =
      ((LocallyFinite.symbols (L := L) σ).map fun ⟨t, f⟩ ↦ ⟨t, .inl f⟩) ++
        (LocallyFinite.symbols (L := L') σ).map fun ⟨t, f⟩ ↦ ⟨t, .inr f⟩ := rfl

end Language

end ManySorted
