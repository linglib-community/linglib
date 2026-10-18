/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Image

/-!
# Meanings with alternatives

A meaning in alternative semantics is a pair: an ordinary denotation, and a set of alternatives
that focus features and operators manipulate while leaving the ordinary denotation alone.
`WithAlternatives` is that pair. It is the product of the identity monad and the set monad, so the
two-dimensional recursion of alternative semantics is `<$>` and `<*>` of a lawful `Monad`, and the
two dimensions are its two monad morphisms. The monad lives in one universe; binary composition
across universes is `WithAlternatives.map₂`, the same composition with `Set.image2` as its
alternatives.

## Main definitions

* `WithAlternatives` — an ordinary value together with the alternatives it evokes
* `WithAlternatives.unfeatured`, `WithAlternatives.focused` — the meanings of an unfocused and
  of an F-marked expression, evoking only their own value and every value respectively
* `WithAlternatives.WellFormed` — the containment constraint: the alternatives include the
  ordinary value
* `WithAlternatives.Given` — the alternatives have collapsed to a singleton
* `WithAlternatives.map₂` — binary composition, alternatives composed pointwise

## Main results

* `ordinary_seq`, `mem_alternatives_seq` — the two dimensions of Hamblin composition
* `alternatives_seq` — the alternatives of an application are those of the `Set` applicative
* `Given.alternatives_seq` — a Given function contributes only its ordinary value
* `nontrivial_alternatives_map₂_left`, `nontrivial_alternatives_map₂_right` — a daughter evoking
  two alternatives makes her mother evoke two, so the mother is not Given

## References

* [rooth-1985]
* [rooth-1992]
* [kratzer-selkirk-2020]
-/

@[expose] public section

/-- An ordinary denotation together with the alternatives the expression evokes
([rooth-1992]). -/
@[ext]
structure WithAlternatives (α : Type*) where
  /-- The denotation the expression would have with no focus on it. -/
  ordinary : α
  /-- The alternatives, which by Rooth's containment constraint include the ordinary value — see
  `WellFormed`, kept a predicate rather than a field so that the composition engine below is a
  `Monad`. -/
  alternatives : Set α

/-- The meaning `unfeatured x` of an expression bearing no focus feature has ordinary value `x`
and evokes only `{x}`. -/
def WithAlternatives.unfeatured {α : Type*} (x : α) : WithAlternatives α :=
  { ordinary := x, alternatives := {x} }

@[simp] theorem WithAlternatives.unfeatured_ordinary {α : Type*} (x : α) :
    (WithAlternatives.unfeatured x).ordinary = x := rfl

@[simp] theorem WithAlternatives.unfeatured_alternatives {α : Type*} (x : α) :
    (WithAlternatives.unfeatured x).alternatives = {x} := rfl

/-- The meaning of an F-marked expression whose alternatives are its whole type: `focused x`
has ordinary value `x` and evokes every value ([rooth-1992]'s focus semantic value of a
constant). -/
def WithAlternatives.focused {α : Type*} (x : α) : WithAlternatives α :=
  { ordinary := x, alternatives := Set.univ }

@[simp] theorem WithAlternatives.focused_ordinary {α : Type*} (x : α) :
    (WithAlternatives.focused x).ordinary = x := rfl

@[simp] theorem WithAlternatives.focused_alternatives {α : Type*} (x : α) :
    (WithAlternatives.focused x).alternatives = Set.univ := rfl

/-! ### The composition engine

Alternative semantics composes pointwise: the ordinary values apply to each other while the
alternatives collect applications of alternative functions to alternative arguments (Hamblin
functional application). `pure` is `unfeatured` and `<$>`/`<*>` are the recursive clauses of the
two-dimensional semantics. -/

namespace WithAlternatives

universe u
variable {α β : Type u}

instance : Monad WithAlternatives where
  pure := unfeatured
  bind m f := ⟨(f m.ordinary).ordinary, ⋃ a ∈ m.alternatives, (f a).alternatives⟩

instance : LawfulMonad WithAlternatives := LawfulMonad.mk'
  (id_map := fun m => by
    cases m; simp [Functor.map, unfeatured])
  (pure_bind := fun x f => by
    simp [bind, pure, unfeatured])
  (bind_assoc := fun m f g => by
    cases m; simp [bind])

/-- The ordinary dimension is a monad morphism onto `Id`. -/
@[simp] theorem ordinary_pure (x : α) : (pure x : WithAlternatives α).ordinary = x := rfl

@[simp] theorem ordinary_bind (m : WithAlternatives α) (f : α → WithAlternatives β) :
    (m >>= f).ordinary = (f m.ordinary).ordinary := rfl

@[simp] theorem ordinary_map (f : α → β) (m : WithAlternatives α) :
    (f <$> m).ordinary = f m.ordinary := rfl

@[simp] theorem ordinary_seq (mf : WithAlternatives (α → β)) (ma : WithAlternatives α) :
    (mf <*> ma).ordinary = mf.ordinary ma.ordinary := rfl

/-- The alternatives of `f <$> m` are the images of `m`'s alternatives. -/
@[simp] theorem mem_alternatives_map {f : α → β} {m : WithAlternatives α} {b : β} :
    b ∈ (f <$> m).alternatives ↔ ∃ a ∈ m.alternatives, f a = b := by
  simp [Functor.map, unfeatured, eq_comm]

/-- In Hamblin functional application alternative functions apply to alternative arguments. -/
@[simp] theorem mem_alternatives_seq {mf : WithAlternatives (α → β)} {ma : WithAlternatives α}
    {b : β} :
    b ∈ (mf <*> ma).alternatives ↔ ∃ g ∈ mf.alternatives, ∃ a ∈ ma.alternatives, g a = b := by
  simp [Seq.seq, unfeatured, eq_comm]

/-- Mapping over an F-marked constituent evokes the whole range of the function. -/
theorem alternatives_map_focused (f : α → β) (x : α) :
    (f <$> focused x).alternatives = Set.range f := by
  ext b; simp [focused]

/-! ### The alternatives as a morphism into the `Set` applicative

With the laws above these exhibit the monad as a span `Id ⟵ WithAlternatives ⟶ Set`: ordinary
denotation and alternative set are its two structure-preserving projections. -/

theorem alternatives_pure (a : α) : (pure a : WithAlternatives α).alternatives = {a} := by
  ext b; simp [pure, unfeatured]

theorem alternatives_seq (mf : WithAlternatives (α → β)) (ma : WithAlternatives α) :
    (mf <*> ma).alternatives = mf.alternatives.seq ma.alternatives := by
  ext b; simp only [mem_alternatives_seq, Set.mem_seq_iff]

theorem alternatives_bind (m : WithAlternatives α) (f : α → WithAlternatives β) :
    (m >>= f).alternatives = {b | ∃ a ∈ m.alternatives, b ∈ (f a).alternatives} := by
  ext b; simp [Bind.bind, bind]

/-- Rooth's containment constraint says that the alternatives contain the ordinary value. -/
def WellFormed (m : WithAlternatives α) : Prop := m.ordinary ∈ m.alternatives

theorem WellFormed.unfeatured (x : α) :
    (WithAlternatives.unfeatured x).WellFormed := rfl

theorem WellFormed.focused (x : α) : (WithAlternatives.focused x).WellFormed := Set.mem_univ x

/-- Composition preserves well-formedness. -/
theorem WellFormed.bind {m : WithAlternatives α} {f : α → WithAlternatives β}
    (hm : m.WellFormed) (hf : ∀ a, (f a).WellFormed) :
    (m >>= f).WellFormed :=
  Set.mem_biUnion hm (hf _)

theorem WellFormed.map {f : α → β} {m : WithAlternatives α} (hm : m.WellFormed) :
    (f <$> m).WellFormed :=
  hm.bind fun a => WellFormed.unfeatured (f a)

/-! ### Givenness -/

/-- A meaning is Given with respect to `a` when its alternatives have collapsed to `{a}`. -/
def Given (m : WithAlternatives α) (a : α) : Prop := m.alternatives = {a}

/-- Unfeatured meanings are Given with respect to their value. -/
theorem Given.unfeatured (x : α) : (unfeatured x).Given x :=
  unfeatured_alternatives x

/-- A Given function collapses Hamblin composition to application on the argument's alternatives:
deaccented material contributes exactly its ordinary value. -/
theorem Given.alternatives_seq {mf : WithAlternatives (α → β)} {f : α → β}
    (h : mf.Given f) (ma : WithAlternatives α) :
    (mf <*> ma).alternatives = f '' ma.alternatives := by
  ext b
  simp only [mem_alternatives_seq, Set.mem_image]
  constructor
  · rintro ⟨g, hg, a, ha, rfl⟩
    obtain rfl := Set.mem_singleton_iff.mp (h ▸ hg)
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨f, h ▸ rfl, a, ha, rfl⟩

end WithAlternatives

/-! ### Binary composition -/

namespace WithAlternatives

variable {α β γ : Type*} {f : α → β → γ} {a : WithAlternatives α} {b : WithAlternatives β}

/-- A meaning whose alternatives are nontrivial is Given with respect to nothing. -/
theorem not_given_of_nontrivial {m : WithAlternatives α} (h : m.alternatives.Nontrivial)
    (x : α) : ¬ m.Given x :=
  h.ne_singleton

/-- Binary composition by `f` composes the ordinary values, and its alternatives are the
compositions of an alternative of each daughter. -/
def map₂ (f : α → β → γ) (a : WithAlternatives α) (b : WithAlternatives β) :
    WithAlternatives γ :=
  ⟨f a.ordinary b.ordinary, Set.image2 f a.alternatives b.alternatives⟩

@[simp] theorem ordinary_map₂ (f : α → β → γ) (a : WithAlternatives α) (b : WithAlternatives β) :
    (map₂ f a b).ordinary = f a.ordinary b.ordinary := rfl

@[simp] theorem alternatives_map₂ (f : α → β → γ) (a : WithAlternatives α)
    (b : WithAlternatives β) :
    (map₂ f a b).alternatives = Set.image2 f a.alternatives b.alternatives := rfl

theorem WellFormed.map₂ (ha : a.WellFormed) (hb : b.WellFormed) : (map₂ f a b).WellFormed :=
  Set.mem_image2_of_mem ha hb

/-- A daughter evoking two alternatives makes her mother evoke two, when the composition is
injective in her and her sister evokes something. -/
theorem nontrivial_alternatives_map₂_left (hf : ∀ y, Function.Injective (f · y))
    (ha : a.alternatives.Nontrivial) (hb : b.alternatives.Nonempty) :
    (map₂ f a b).alternatives.Nontrivial :=
  let ⟨_, hy⟩ := hb
  (ha.image (hf _)).mono (Set.image_subset_image2_left hy)

theorem nontrivial_alternatives_map₂_right (hf : ∀ x, Function.Injective (f x))
    (ha : a.alternatives.Nonempty) (hb : b.alternatives.Nontrivial) :
    (map₂ f a b).alternatives.Nontrivial :=
  let ⟨_, hx⟩ := ha
  (hb.image (hf _)).mono (Set.image_subset_image2_right hx)

universe u in
/-- Within a universe, binary composition is the monad's `f <$> a <*> b`. -/
theorem map₂_eq_seq {α β γ : Type u} (f : α → β → γ) (a : WithAlternatives α)
    (b : WithAlternatives β) : map₂ f a b = f <$> a <*> b := by
  refine WithAlternatives.ext rfl (Set.ext fun c ↦ ?_)
  simp only [alternatives_map₂, Set.mem_image2, mem_alternatives_seq, mem_alternatives_map]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, y, hy, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, y, hy, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩

end WithAlternatives
