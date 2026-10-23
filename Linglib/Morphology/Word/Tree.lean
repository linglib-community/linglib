/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Morph

/-!
# Word-internal structure

A `Word.Tree M` records how a word is built from material in `M`, with one constructor for each of
Booij's morphological operations: affixation on either side, infixation, circumfixation,
compounding, reduplication and conversion. Linearization forgets the structure; attaching affixes
to a root in order records the affixes and their order.

## Main definitions

* `Morphology.Word.Tree`: the tree of a word's formation.
* `Morphology.Word.Tree.toList`: the material of a tree in surface order.
* `Morphology.Word.Tree.IsConcatenative`: the tree is built by concatenation alone, so `toList`
  is the word's segmentation.
* `Morphology.Word.Tree.attachAll`, `Morphology.Word.Tree.attachMorphs`: attachment of affixes to
  a root, and of morphs on the sides their kinds give.

## Main results

* `Morphology.Word.Tree.toList_attachAll`: the affixes of each side surface outward from the root
  in the order they were attached.
* `Morphology.Word.Tree.attachAll_injective`: attachment records the affixes and their order.

## References

* [booij-2012]
-/

@[expose] public section

namespace Morphology.Word

/-! ### The reduplication index -/

/-- The type of a reduplication step. -/
inductive Tree.RedupType where
  /-- Copies the entire base (Javanese *omaha* → *omaha-omaha* "various
  houses"). -/
  | total
  /-- Copies a prosodic template (Javanese *tamu* → *tətamu* "to visit"). -/
  | partialCopy
  deriving DecidableEq, Repr

/-! ### The tree -/

/-- A tree of word-formation operations over material in `M`. -/
inductive Tree (M : Type*) where
  /-- A leaf, carrying a single element. -/
  | root : M → Tree M
  /-- Attach an affix before the base. -/
  | prefixed : M → Tree M → Tree M
  /-- Attach an affix after the base. -/
  | suffixed : Tree M → M → Tree M
  /-- Insert an affix within the base (Khmu *s⟨m⟩ka:t* "roughen"). -/
  | infixed : Tree M → M → Tree M
  /-- Wrap the base with a prefix and a suffix (German *Ge-sing-e* "singing"). -/
  | circumfixed : M → Tree M → M → Tree M
  /-- Join two stems (*bottle* + *factory*). -/
  | compound : Tree M → Tree M → Tree M
  /-- Total or partial reduplication. -/
  | reduplicated : Tree.RedupType → Tree M → Tree M
  /-- Convert without added material (noun *chain* → verb *to chain*). -/
  | converted : Tree M → Tree M
  deriving Repr

namespace Tree

variable {M : Type*}

/-! ### Linearization -/

/-- The material of the tree, in surface order on the concatenative
fragment; an infix follows its base and reduplicative copies contribute
nothing. -/
def toList : Tree M → List M
  | .root m => [m]
  | .prefixed afx base => afx :: base.toList
  | .suffixed base afx => base.toList ++ [afx]
  | .infixed base afx => base.toList ++ [afx]
  | .circumfixed pre base suf => pre :: base.toList ++ [suf]
  | .compound left right => left.toList ++ right.toList
  | .reduplicated _ base => base.toList
  | .converted base => base.toList

/-- `IsConcatenative t` asserts that `t` is built by concatenation alone —
no infixation, circumfixation, or reduplication — so `toList` is the word's
segmentation. -/
def IsConcatenative : Tree M → Prop
  | .root _ => True
  | .prefixed _ b => b.IsConcatenative
  | .suffixed b _ => b.IsConcatenative
  | .compound l r => l.IsConcatenative ∧ r.IsConcatenative
  | .converted b => b.IsConcatenative
  | .infixed .. => False
  | .circumfixed .. => False
  | .reduplicated .. => False

instance decIsConcatenative : (t : Tree M) → Decidable t.IsConcatenative
  | .root _ => .isTrue trivial
  | .prefixed _ b | .suffixed b _ | .converted b => decIsConcatenative b
  | .compound l r => @instDecidableAnd _ _ (decIsConcatenative l) (decIsConcatenative r)
  | .infixed .. | .circumfixed .. | .reduplicated .. => .isFalse id

/-! ### Attachment by side -/

/-- Attach an affix on a side of its host. -/
def attach (side : Morph.Side) (afx : M) (t : Tree M) : Tree M :=
  match side with
  | .before => .prefixed afx t
  | .after => .suffixed t afx

@[simp] theorem attach_before (afx : M) (t : Tree M) : t.attach .before afx = .prefixed afx t := rfl

@[simp] theorem attach_after (afx : M) (t : Tree M) : t.attach .after afx = .suffixed t afx := rfl

theorem attach_inj {s s' : Morph.Side} {afx afx' : M} {t t' : Tree M} :
    t.attach s afx = t'.attach s' afx' ↔ s = s' ∧ afx = afx' ∧ t = t' := by
  cases s <;> cases s' <;> simp [and_comm]

theorem attach_ne_root (side : Morph.Side) (afx : M) (t : Tree M) (m : M) :
    t.attach side afx ≠ root m := by
  cases side <;> simp

/-- Attach affixes to a root in order, innermost first. -/
def attachAll (root : M) (affixes : List (Morph.Side × M)) : Tree M :=
  affixes.foldl (fun t p ↦ t.attach p.1 p.2) (.root root)

@[simp] theorem attachAll_nil (root : M) : attachAll root [] = .root root := rfl

theorem attachAll_concat (root : M) (affixes : List (Morph.Side × M)) (p : Morph.Side × M) :
    attachAll root (affixes ++ [p]) = (attachAll root affixes).attach p.1 p.2 :=
  List.foldl_concat ..

theorem attachAll_injective (root : M) : Function.Injective (attachAll root) := by
  intro l₁ l₂ h
  induction l₁ using List.reverseRecOn generalizing l₂ with
  | nil =>
    induction l₂ using List.reverseRecOn with
    | nil => rfl
    | append_singleton _ p _ => exact absurd h.symm (by rw [attachAll_concat]; apply attach_ne_root)
  | append_singleton l₁ p ih =>
    induction l₂ using List.reverseRecOn with
    | nil => exact absurd h (by rw [attachAll_concat]; apply attach_ne_root)
    | append_singleton l₂ q _ =>
      rw [attachAll_concat, attachAll_concat, attach_inj] at h
      rw [ih h.2.2, Prod.ext h.1 h.2.1]

theorem toList_foldl_attach (t : Tree M) : ∀ affixes : List (Morph.Side × M),
    (affixes.foldl (fun t p ↦ t.attach p.1 p.2) t).toList =
      ((affixes.filter (·.1 = .before)).map (·.2)).reverse ++ t.toList ++
        (affixes.filter (·.1 = .after)).map (·.2)
  | [] => by simp
  | ⟨s, a⟩ :: rest => by
    rw [List.foldl_cons, toList_foldl_attach (t.attach s a) rest]
    cases s <;> simp [toList]

theorem toList_attachAll (root : M) (affixes : List (Morph.Side × M)) :
    (attachAll root affixes).toList =
      ((affixes.filter (·.1 = .before)).map (·.2)).reverse ++
        root :: (affixes.filter (·.1 = .after)).map (·.2) := by
  rw [attachAll, toList_foldl_attach]; simp [toList]

theorem isConcatenative_foldl_attach {t : Tree M} (ht : t.IsConcatenative) :
    ∀ affixes : List (Morph.Side × M),
      (affixes.foldl (fun t p ↦ t.attach p.1 p.2) t).IsConcatenative
  | [] => ht
  | ⟨s, a⟩ :: rest => by
    rw [List.foldl_cons]
    exact isConcatenative_foldl_attach (by cases s <;> exact ht) rest

theorem isConcatenative_attachAll (root : M) (affixes : List (Morph.Side × M)) :
    (attachAll root affixes).IsConcatenative :=
  isConcatenative_foldl_attach (show (Tree.root root).IsConcatenative from trivial) affixes

/-! ### Attachment of morphs -/

/-- Attach morphs to a root in order, each on the side its kind gives; a morph bound on no
side, an infix or a free form, is not attached. -/
def attachMorphs (root : Morph) (ms : List Morph) : Tree Morph :=
  attachAll root (ms.filterMap fun m ↦ (m.kind.side?).map (·, m))

theorem attachMorphs_injOn (root : Morph) :
    Set.InjOn (attachMorphs root) {ms | ∀ m ∈ ms, m.kind.side?.isSome} := by
  intro l₁ h₁ l₂ h₂ h
  have key : ∀ l : List Morph, (∀ m ∈ l, m.kind.side?.isSome) →
      (l.filterMap fun m ↦ (m.kind.side?).map (·, m)) =
        l.map fun m ↦ ((m.kind.side?).getD .before, m) := by
    intro l hl
    rw [← List.filterMap_eq_map]
    exact List.filterMap_congr fun m hm ↦ by
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (hl m hm)
      simp [hs]
  have := attachAll_injective root
    (by simpa only [attachMorphs, key l₁ h₁, key l₂ h₂] using h)
  exact List.map_injective_iff.mpr (fun m m' hmm ↦ (Prod.ext_iff.mp hmm).2) this

end Tree

end Morphology.Word
