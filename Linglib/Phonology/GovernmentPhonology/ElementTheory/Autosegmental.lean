/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.GovernmentPhonology.ElementTheory.Basic
public import Linglib.Phonology.Autosegmental.KripkeModel.Spread
public import Linglib.Phonology.Autosegmental.Skeleton
public import Mathlib.Data.Fintype.Sum

/-!
# Autosegmental representations of elements

In Element Theory the melody of a segment is a set of elements, and each element has a tier of
its own, called its line. A position of the skeleton is linked to a root node, and the root node
is linked to a token on the line of each element of the melody. The tiers form a tree: the
skeleton, the tier of root nodes below it, and the lines below that.

We define a `Position` as a slot of the skeleton with the melodic expression of its root node,
if it has a root node. Its representation `ofPosition` has the slot, the root node, and one
token for each element of the expression, labelled head or dependent. The representation
`ofForm w` of a list of positions `w` is the concatenation of the representations of its
positions.

The melody of a position on a tier is the list of tokens that the position dominates there. In
`ofForm w` the melody of position `k` is the list of its own tokens (`melody_ofForm`). It
contains a root node if and only if the position has one (`mem_melody_rootNode_ofForm_iff`), and
a token of the element `e` if and only if the expression of the position contains `e`
(`exists_mem_melody_line_ofForm_iff`). The lines of `ofForm w` do not cross
(`noCrossing_ofForm`).

Spreading the element `e` from position `m` to position `n` links the root node of `n` to the
token of `e` at `m`, and delinks it from its own token of `e`. This is `spread w e m n`. Its
lines do not cross if and only if no position strictly between `m` and `n` has `e`
(`noCrossing_spread_iff`). The melody of each position is its melody in the form where position
`n` has `e` with the status that `e` has at `m` (`mem_melody_spread_iff`). If positions `m` and
`n` both have `e`, each position has tokens of the same elements as before
(`exists_mem_melody_spread_iff`).

## Implementation notes

A position with a root node and no element is distinct from a position with no root node.
[harris-1994] distinguishes a stable schwa from an empty nucleus in this way, and [faust-2025] a
weak vowel from an empty one.

Each element has its own line directly below the root node. [harris-1994] places class nodes
between the root node and the lines, and [kaye-lowenstamm-vergnaud-1985] let two elements that
cannot combine share a line. Neither is represented here.

Government and licensing relate positions of the skeleton to each other. They are not
association lines and are not part of this representation.

## References

* [kaye-lowenstamm-vergnaud-1985]
* [harris-1994]
* [backley-2011]
* [faust-2025]
-/

@[expose] public section

open Autosegmental

namespace ElementTheory

/-- The status of an element in a melodic expression: head or dependent. -/
inductive Status where
  | head
  | dependent
  deriving DecidableEq, Repr

/-- The status of the element `e` in the expression `m`: head if `e` is a head of `m`, and dependent
otherwise. -/
def MR.status (m : MR) (e : Element) : Status := if e ∈ m.heads then .head else .dependent

/-- `m₂.adopt m₁ e` is the expression `m₂` with the element `e` added, as a head if `e` is a head of
`m₁` and as a dependent otherwise. -/
def MR.adopt (m₂ m₁ : MR) (e : Element) : MR where
  elements := insert e m₂.elements
  heads := if e ∈ m₁.heads then insert e m₂.heads else m₂.heads.erase e
  heads_subset := by
    split_ifs
    · exact Finset.insert_subset_insert e m₂.heads_subset
    · exact (Finset.erase_subset e _).trans (m₂.heads_subset.trans (Finset.subset_insert e _))

theorem MR.mem_elements_adopt {m₂ m₁ : MR} {e e' : Element} :
    e' ∈ (m₂.adopt m₁ e).elements ↔ e' = e ∨ e' ∈ m₂.elements :=
  Finset.mem_insert

theorem MR.status_adopt_self (m₂ m₁ : MR) (e : Element) :
    (m₂.adopt m₁ e).status e = m₁.status e := by
  unfold MR.status MR.adopt
  by_cases h : e ∈ m₁.heads <;> simp [h]

theorem MR.status_adopt_of_ne (m₂ m₁ : MR) {e e' : Element} (h : e' ≠ e) :
    (m₂.adopt m₁ e).status e' = m₂.status e' := by
  unfold MR.status MR.adopt
  by_cases h1 : e ∈ m₁.heads <;> simp [h1, h]

/-! ### The tiers -/

/-- The tiers of a representation of elements: the skeleton, the tier of root nodes, and one line
for each element. -/
inductive Tier where
  | skeleton
  | rootNode
  | line (e : Element)
  deriving DecidableEq, Fintype

/-- The tier above a tier: the tier of root nodes above each line, and the skeleton above the root
nodes. -/
def Tier.parent : Tier → Tier
  | .line _ => .rootNode
  | _ => .skeleton

/-- The tree of tiers, with the skeleton as its root. -/
def tiers : ParentTree Tier :=
  .ofIterate Tier.parent .skeleton 2 (by rintro (_ | _ | _) <;> rfl)

@[simp] theorem tiers_root : tiers.root = .skeleton := rfl

@[simp] theorem tiers_parent (t : Tier) : tiers.parent t = t.parent := rfl

theorem iterate_parent_ne_line {t : Tier} (ht : ∀ e, t ≠ .line e) :
    ∀ (n : ℕ) (e : Element), Tier.parent^[n] t ≠ .line e
  | 0, e => ht e
  | n + 1, e => by
    rw [Function.iterate_succ_apply]
    exact iterate_parent_ne_line (by cases t <;> simp [Tier.parent]) n e

/-- A tier lies at or below the line of `e` in the tree of tiers if and only if it is that line. -/
theorem tiers_le_line_iff {e : Element} {t : Tier} :
    tiers.toPartialOrder.le (.line e) t ↔ t = .line e := by
  refine ⟨fun ⟨n, hn⟩ ↦ ?_, fun h ↦ h ▸ ⟨0, rfl⟩⟩
  cases n with
  | zero => exact hn
  | succ n =>
    rw [tiers, ParentTree.ofIterate, Function.iterate_succ_apply] at hn
    exact absurd hn (iterate_parent_ne_line (by cases t <;> simp [Tier.parent]) n e)

/-- The alphabet of each tier: slots on the skeleton, a single symbol on the tier of root nodes, and
head or dependent on each line. -/
abbrev Tiers : Tier → Type
  | .skeleton => Slot
  | .rootNode => Unit
  | .line _ => Status

instance : ∀ t, DecidableEq (Tiers t)
  | .skeleton => inferInstanceAs (DecidableEq Slot)
  | .rootNode => inferInstanceAs (DecidableEq Unit)
  | .line _ => inferInstanceAs (DecidableEq Status)

/-! ### Positions and forms -/

/-- A position of the skeleton: a slot, and the melodic expression of its root node if it has one.
-/
structure Position where
  /-- The slot, consonantal or vocalic. -/
  slot : Slot
  /-- The melodic expression of the root node of the position. -/
  melody : Option MR := none

/-- The tokens of a position on each tier: its slot on the skeleton, its root node if it has one,
and on the line of each element of its expression the status of that element. -/
def Position.word (p : Position) : ∀ t, List (Tiers t)
  | .skeleton => [p.slot]
  | .rootNode => if p.melody.isSome then [()] else []
  | .line e =>
    match p.melody with
    | some m => if e ∈ m.elements then [m.status e] else []
    | none => []

/-- The representation of a position: its tokens, with a line from each token to the token on the
tier above. -/
def ofPosition (p : Position) : AR Tiers :=
  AR.fromRel p.word fun t' t _ _ ↦ t.parent = t' ∧ t ≠ .skeleton

/-- The representation of a list of positions: the concatenation of the representations of its
positions. -/
def ofForm (w : List Position) : AR Tiers := (w.map ofPosition).prod

/-- `ofForm` as a monoid homomorphism from the free monoid on positions. -/
def ofFormHom : FreeMonoid Position →* AR Tiers := FreeMonoid.lift ofPosition

@[simp] theorem ofFormHom_ofList (w : List Position) :
    ofFormHom (FreeMonoid.ofList w) = ofForm w :=
  FreeMonoid.lift_ofList _ _

variable {p : Position} {w : List Position} {e : Element} {s : Status} {k m n : ℕ}

@[simp] theorem word_ofPosition (p : Position) : (ofPosition p).word = p.word := rfl

theorem Position.length_word_le_one (p : Position) : ∀ t, (p.word t).length ≤ 1
  | .skeleton => le_rfl
  | .rootNode => by
    show (if p.melody.isSome then [()] else []).length ≤ 1
    split_ifs <;> simp
  | .line e => by
    rcases h : p.melody with _ | m <;> simp only [Position.word, h]
    · simp
    · split_ifs <;> simp

theorem Position.word_line_ne_nil_iff :
    p.word (.line e) ≠ [] ↔ ∃ m ∈ p.melody, e ∈ m.elements := by
  rcases h : p.melody with _ | m <;> simp [Position.word, h]

theorem Position.word_rootNode_ne_nil_iff : p.word .rootNode ≠ [] ↔ p.melody.isSome := by
  rcases h : p.melody with _ | m <;> simp [Position.word, h]

theorem noCrossing_ofPosition (p : Position) : (ofPosition p).NoCrossing :=
  fun t' _ ↦ AR.isNonCrossing_lines_iff.2 fun q _ q' _ _ h₂ hlt ↦ by
    have h : q' < (p.word t').length := h₂.lt_left
    have := p.length_word_le_one t'
    omega

/-- The lines of the representation of a form do not cross. -/
theorem noCrossing_ofForm (w : List Position) : (ofForm w).NoCrossing :=
  AR.NoCrossing.prod fun X hX ↦ by
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hX
    exact noCrossing_ofPosition p

/-- In the representation of a position, the tokens on a tier and on the tier above are linked if
and only if the position has a token on the lower tier. -/
theorem link_ofPosition_parent_iff {t : Tier} (ht : t ≠ .skeleton) :
    (ofPosition p).Link t.parent t 0 0 ↔ p.word t ≠ [] := by
  rw [ofPosition, AR.link_fromRel]
  cases t with
  | skeleton => exact absurd rfl ht
  | rootNode => simp [Tier.parent, Position.word, List.length_pos_iff]
  | line e =>
    rcases h : p.melody with _ | m <;>
      simp [Tier.parent, Position.word, h, List.length_pos_iff]

theorem dominates_ofPosition {t : Tier} (h : p.word t ≠ []) :
    (ofPosition p).Dominates tiers 0 t 0 := by
  have hcard : 1 < Fintype.card Tier := Fintype.one_lt_card_iff.2 ⟨.skeleton, .rootNode, by decide⟩
  have hroot : p.word .rootNode ≠ [] → ((Tier.rootNode, 0) : Tier × ℕ) ∈
      (ofPosition p).descendants tiers 1 (.skeleton, 0) := fun hr ↦
    AR.mem_descendants_succ_of_mem_children (AR.mem_descendants_self 0 _)
      (AR.mem_children.2 ⟨rfl, by decide, (link_ofPosition_parent_iff (by decide)).2 hr⟩)
  cases t with
  | skeleton => exact AR.mem_descendants_self _ _
  | rootNode => exact AR.descendants_mono (by omega) _ (hroot h)
  | line e =>
    have hr : p.word .rootNode ≠ [] := by
      obtain ⟨m, hm, -⟩ := Position.word_line_ne_nil_iff.1 h
      exact Position.word_rootNode_ne_nil_iff.2 (by simp [Option.mem_def.1 hm])
    exact AR.descendants_mono hcard _ (AR.mem_descendants_succ_of_mem_children (hroot hr)
      (AR.mem_children.2 ⟨rfl, by simp, (link_ofPosition_parent_iff (by simp)).2 h⟩))

/-- The melody of a position on a tier is the list of its tokens on that tier. -/
theorem melody_ofPosition (p : Position) (t : Tier) :
    (ofPosition p).melody tiers 0 t = p.word t := by
  have hlen := p.length_word_le_one t
  rcases hw : p.word t with _ | ⟨c, _ | ⟨d, l⟩⟩
  · simp [AR.melody, hw]
  · have hd : (ofPosition p).Dominates tiers 0 t 0 := dominates_ofPosition (by simp [hw])
    simp [AR.melody, hw, hd]
  · simp [hw] at hlen

/-- The melody of position `k` of a form on a tier is the list of tokens of that position on the
tier. -/
theorem melody_ofForm (hk : k < w.length) (t : Tier) :
    (ofForm w).melody tiers k t = w[k].word t :=
  (AR.melody_prod_map tiers ofPosition (fun _ ↦ rfl) hk).trans (melody_ofPosition _ _)

theorem mem_melody_ofForm_iff {t : Tier} {b : Tiers t} :
    b ∈ (ofForm w).melody tiers k t ↔ ∃ hk : k < w.length, b ∈ w[k].word t :=
  (AR.mem_melody_prod_map tiers ofPosition fun _ ↦ rfl).trans
    (exists_congr fun _ ↦ by rw [melody_ofPosition])

/-- The melody of position `k` of a form contains a root node if and only if the position has one.
-/
theorem mem_melody_rootNode_ofForm_iff :
    () ∈ (ofForm w).melody tiers k .rootNode ↔ ∃ p ∈ w[k]?, p.melody.isSome := by
  refine (mem_melody_ofForm_iff (t := .rootNode) (b := ())).trans ?_
  simp only [List.getElem?_eq_some_iff, Option.mem_def]
  constructor
  · rintro ⟨hk, h⟩
    exact ⟨_, ⟨hk, rfl⟩, Position.word_rootNode_ne_nil_iff.1 (List.ne_nil_of_mem h)⟩
  · rintro ⟨_, ⟨hk, rfl⟩, h⟩
    exact ⟨hk, by simp [Position.word, h]⟩

/-- The melody of position `k` of a form contains a token of the element `e` if and only if the
expression of the position contains `e`. -/
theorem exists_mem_melody_line_ofForm_iff :
    (∃ s, s ∈ (ofForm w).melody tiers k (.line e)) ↔
      ∃ p ∈ w[k]?, ∃ m ∈ p.melody, e ∈ m.elements := by
  refine (exists_congr fun s ↦ mem_melody_ofForm_iff (t := .line e) (b := s)).trans ?_
  simp only [List.getElem?_eq_some_iff, Option.mem_def]
  constructor
  · rintro ⟨s, hk, h⟩
    exact ⟨_, ⟨hk, rfl⟩, Position.word_line_ne_nil_iff.1 (List.ne_nil_of_mem h)⟩
  · rintro ⟨_, ⟨hk, rfl⟩, m, hm, he⟩
    exact ⟨m.status e, hk, by simp [Position.word, hm, he]⟩

/-! ### Spreading -/

/-- `spread w e m n` is the representation of `w` with the element `e` spread from position `m` to
position `n`: the root node of `n` is linked to the token of `e` at `m` and delinked from its own
token of `e`. -/
def spread (w : List Position) (e : Element) (m n : ℕ) : AR Tiers :=
  AR.spreadTier tiers ofPosition w (.line e) m n

/-- The lines of `spread w e m n` do not cross if and only if no position strictly between `m` and
`n` has `e`. -/
theorem noCrossing_spread_iff (hm : m < w.length) (hn : n < w.length)
    (he : ∃ m₁ ∈ w[m].melody, e ∈ m₁.elements) (hr : w[n].melody.isSome) :
    (spread w e m n).NoCrossing ↔
      ∀ k (hk : k < w.length), k ∈ Set.uIoo m n → ∀ m' ∈ w[k].melody, e ∉ m'.elements := by
  refine (AR.noCrossing_spreadTier_iff (T := tiers) (g₀ := ofPosition) (j := .line e)
    (by simp) (fun p ↦ p.length_word_le_one (tiers.parent (.line e)))
    (fun p ↦ p.length_word_le_one (.line e)) hm hn
    (Position.word_line_ne_nil_iff.2 he) (Position.word_rootNode_ne_nil_iff.2 hr)
    (noCrossing_ofForm w)).trans ?_
  refine forall₃_congr fun k hk _ ↦ ?_
  rw [tiers_parent, link_ofPosition_parent_iff (by simp), not_not]
  refine ⟨fun h m' hm' he' ↦ Position.word_line_ne_nil_iff.2 ⟨m', hm', he'⟩ h, fun h ↦ ?_⟩
  by_contra hne
  obtain ⟨m', hm', he'⟩ := Position.word_line_ne_nil_iff.1 hne
  exact h m' hm' he'

/-- After `e` spreads from `m` to `n`, the melody of each position is its melody in the form where
position `n` has `e` with the status that `e` has at `m`. -/
theorem mem_melody_spread_iff (hm : m < w.length) (hn : n < w.length) {m₁ m₂ : MR}
    (h₁ : w[m].melody = some m₁) (he : e ∈ m₁.elements) (h₂ : w[n].melody = some m₂)
    {t : Tier} {b : Tiers t} :
    b ∈ (spread w e m n).melody tiers k t ↔
      b ∈ (ofForm (w.set n ⟨w[n].slot, some (m₂.adopt m₁ e)⟩)).melody tiers k t := by
  refine AR.mem_melody_spreadTier_iff ofPosition (by simp)
    (fun p t ↦ p.length_word_le_one t) (fun _ ↦ rfl) ?_ hm hn ?_ ?_ ?_ ?_
  · intro p t ht
    rw [tiers_parent, link_ofPosition_parent_iff (by simpa using ht), word_ofPosition]
  · exact Position.word_line_ne_nil_iff.2 ⟨m₁, h₁, he⟩
  · exact Position.word_rootNode_ne_nil_iff.2 (by simp [h₂])
  · intro t ht
    obtain rfl := tiers_le_line_iff.1 ht
    simp [Position.word, h₁, he, MR.mem_elements_adopt, MR.status_adopt_self]
  · rintro (_ | _ | e') ht
    · rfl
    · simp [Position.word, h₂]
    · have hne : e' ≠ e := fun h ↦ ht (tiers_le_line_iff.2 (h ▸ rfl))
      simp [Position.word, h₂, MR.mem_elements_adopt, hne, MR.status_adopt_of_ne _ _ hne]

/-- If positions `m` and `n` both have `e`, then after `e` spreads from `m` to `n` each position has
tokens of the same elements as before. -/
theorem exists_mem_melody_spread_iff (hm : m < w.length) (hn : n < w.length) {m₁ m₂ : MR}
    (h₁ : w[m].melody = some m₁) (he : e ∈ m₁.elements) (h₂ : w[n].melody = some m₂)
    (he' : e ∈ m₂.elements) {e' : Element} :
    (∃ s, s ∈ (spread w e m n).melody tiers k (.line e')) ↔
      ∃ s, s ∈ (ofForm w).melody tiers k (.line e') := by
  rw [exists_congr fun s ↦ mem_melody_spread_iff (t := .line e') (b := s) hm hn h₁ he h₂,
    exists_mem_melody_line_ofForm_iff, exists_mem_melody_line_ofForm_iff]
  by_cases hk : n = k
  · subst hk
    simp only [List.getElem?_set_self hn, List.getElem?_eq_getElem hn, Option.mem_def,
      Option.some.injEq, exists_eq_left', h₂, MR.mem_elements_adopt]
    exact ⟨fun h ↦ h.elim (· ▸ he') id, .inr⟩
  · rw [List.getElem?_set_ne hk]

/-- After `e` spreads from `m` to `n`, position `n` has `e` with the status that `e` has at `m`. -/
theorem mem_melody_spread_self_iff (hm : m < w.length) (hn : n < w.length) {m₁ m₂ : MR}
    (h₁ : w[m].melody = some m₁) (he : e ∈ m₁.elements) (h₂ : w[n].melody = some m₂) :
    s ∈ (spread w e m n).melody tiers n (.line e) ↔ s = m₁.status e := by
  rw [mem_melody_spread_iff hm hn h₁ he h₂, mem_melody_ofForm_iff]
  simp [hn, Position.word, MR.mem_elements_adopt, MR.status_adopt_self]

end ElementTheory
