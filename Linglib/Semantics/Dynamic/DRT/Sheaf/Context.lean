module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Prod
public import Mathlib.ModelTheory.Basic

/-!
# Contexts, renamings, and literals

This file defines the category of *contexts* of discourse representation theory in its
sheaf-theoretic reading: a context is a finite vocabulary of relation symbols together with a
finite set of discourse referents, and a morphism is an inclusion of vocabularies with a map of
referents — a relabelling, an inclusion, or an identification of referents. Literals over a
context are signed atoms; they rename covariantly along context morphisms.

## Main definitions

* `DRT.Context`, `DRT.Context.Hom`: contexts `(L, X)` and their morphisms, a `Category`.
* `DRT.Literal`: literals `±A(x̄)` over a context, with `Literal.map` (renaming), the
  complementary literal `-l`, decidable equality and finiteness.
* `DRT.Literal.functor`: literals as a functor to types.
* `DRT.Literal.Consistent`: sets of literals containing no complementary pair.

## References

* [abramsky-sadrzadeh-2014]
* [kamp-reyle-1993]
-/

@[expose] public section

open CategoryTheory FirstOrder

namespace DRT

universe u v w

/-- A context `(L, X)` pairs a finite vocabulary of relation symbols with a finite set of
referents. -/
structure Context (L : Language.{u, v}) (V : Type w) where
  /-- The vocabulary. -/
  vocab : Finset (Σ n, L.Relations n)
  /-- The referents. -/
  vars : Finset V

variable {L : Language.{u, v}} {V : Type w}

/-- A context morphism includes the vocabulary and maps the referents. -/
structure Context.Hom (c c' : Context L V) where
  /-- The vocabulary inclusion. -/
  incl : c.vocab ⊆ c'.vocab
  /-- The referent map. -/
  map : c.vars → c'.vars

instance : Category (Context L V) where
  Hom := Context.Hom
  id c := ⟨subset_rfl, id⟩
  comp f g := ⟨f.incl.trans g.incl, g.map ∘ f.map⟩

namespace Context

variable {c c' c'' : Context L V}

@[ext] theorem hom_ext {f g : c ⟶ c'} (h : f.map = g.map) : f = g := by
  cases f; cases g; cases h; rfl

@[simp] theorem id_map (c : Context L V) : Hom.map (𝟙 c) = id := rfl

@[simp] theorem comp_map (f : c ⟶ c') (g : c' ⟶ c'') : Hom.map (f ≫ g) = g.map ∘ f.map := rfl

/-- `f.extend` acts as `f` on the source referents and as the identity elsewhere. -/
def Hom.extend [DecidableEq V] (f : c ⟶ c') (t : V) : V :=
  if h : t ∈ c.vars then f.map ⟨t, h⟩ else t

@[simp] theorem Hom.extend_coe [DecidableEq V] (f : c ⟶ c') (t : c.vars) :
    f.extend t = (f.map t : V) := by
  simp [Hom.extend]

end Context

/-- A literal over a context is a signed atomic formula `±A(x̄)`. -/
structure Literal (c : Context L V) where
  /-- The relation symbol. -/
  rel : c.vocab
  /-- The argument referents. -/
  args : Fin rel.1.1 → c.vars
  /-- The sign. -/
  pos : Bool

namespace Literal

variable {c c' c'' : Context L V}

/-- A literal is a dependent triple of a relation symbol, its arguments and a sign. -/
def equivSigma (c : Context L V) : Literal c ≃ Σ r : c.vocab, (Fin r.1.1 → c.vars) × Bool where
  toFun l := ⟨l.rel, l.args, l.pos⟩
  invFun l := ⟨l.1, l.2.1, l.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `l.map f` renames the arguments of `l` along `f`. -/
def map (f : c ⟶ c') (l : Literal c) : Literal c' :=
  ⟨⟨l.rel.1, f.incl l.rel.2⟩, f.map ∘ l.args, l.pos⟩

@[simp] theorem map_id (l : Literal c) : l.map (𝟙 c) = l := rfl

@[simp] theorem map_comp (f : c ⟶ c') (g : c' ⟶ c'') (l : Literal c) :
    l.map (f ≫ g) = (l.map f).map g := rfl

theorem map_injective {f : c ⟶ c'} (hf : Function.Injective f.map) :
    Function.Injective (map f) := by
  rintro ⟨⟨r, hr⟩, a, p⟩ ⟨⟨r', hr'⟩, a', p'⟩ h
  obtain ⟨h₁, h₂, rfl⟩ := Literal.mk.inj h
  obtain rfl := Subtype.mk.inj h₁
  cases funext fun i => hf (congrFun (eq_of_heq h₂) i)
  rfl

/-- The complement `-l` flips the sign of `l`. -/
instance : InvolutiveNeg (Literal c) where
  neg l := ⟨l.rel, l.args, !l.pos⟩
  neg_neg l := by cases l; simp

@[simp] theorem pos_neg (l : Literal c) : (-l).pos = !l.pos := rfl

theorem neg_ne_self (l : Literal c) : -l ≠ l := fun h => by
  simpa using congrArg Literal.pos h

@[simp] theorem neg_map (f : c ⟶ c') (l : Literal c) : -(l.map f) = (-l).map f := rfl

variable (L V) in
/-- Renaming makes literals a functor to types. -/
def functor : Context L V ⥤ Type (max v w) where
  obj := Literal
  map f := TypeCat.ofHom (map f)

@[simp] theorem functor_map (f : c ⟶ c') (l : Literal c) : (functor L V).map f l = l.map f :=
  rfl

/-- A set of literals is consistent when it contains no literal together with its complement. -/
def Consistent (s : Finset (Literal c)) : Prop := ∀ l ∈ s, -l ∉ s

theorem Consistent.mono {s t : Finset (Literal c)} (h : s ⊆ t) (ht : Consistent t) :
    Consistent s :=
  fun l hl hn => ht l (h hl) (h hn)

end Literal

variable [DecidableEq V] [∀ n, DecidableEq (L.Relations n)]

-- Compared through non-dependent data, which kernel `decide` evaluates on enumerated literals.
instance (c : Context L V) : DecidableEq (Literal c) := fun l l' =>
  decidable_of_iff (l.rel.1 = l'.rel.1 ∧ List.ofFn l.args = List.ofFn l'.args ∧ l.pos = l'.pos) (by
    constructor
    · rintro ⟨h₁, h₂, h₃⟩
      obtain ⟨⟨r, hr⟩, a, p⟩ := l
      obtain ⟨⟨r', hr'⟩, a', p'⟩ := l'
      obtain rfl : r = r' := h₁
      obtain rfl := List.ofFn_injective h₂
      obtain rfl := h₃
      rfl
    · rintro rfl; exact ⟨rfl, rfl, rfl⟩)

instance (c : Context L V) : Fintype (Literal c) := Fintype.ofEquiv _ (Literal.equivSigma c).symm

instance {c : Context L V} (s : Finset (Literal c)) : Decidable (Literal.Consistent s) :=
  inferInstanceAs (Decidable (∀ l ∈ s, -l ∉ s))

end DRT
