/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.GovernmentPhonology.ElementTheory.Basic
public import Linglib.Phonology.Autosegmental.KripkeModel
public import Linglib.Phonology.Autosegmental.Skeleton
public import Mathlib.Data.Fintype.Sum

/-!
# Elements on their lines

In Element Theory each element lies on a line of its own, and a position of the skeleton is
associated with a root node, which is associated with the elements of its melodic expression. An
element under a vocalic position is a vowel, and the same element under a consonantal position is
a glide. A position may have a root node with no element, which is the neutral vowel, or no root
node at all, which is an empty position.

We define `Position`, a slot with the melodic expression of its root node if it has one, and
`ofPosition`, its autosegmental representation along the tree `tiers`: the slot, a root node
under it, and under that a token, a head or a dependent, on the line of each element of the
expression. A form is a word of positions; `ofForm` concatenates their representations, as the
monoid homomorphism `ofFormHom` does on the free monoid, and its lines do not cross
(`noCrossing_ofForm`). A position of a form reads a root node exactly when it has one
(`reads_rootNode_ofForm_iff`) and an element exactly when its expression contains it
(`reads_line_ofForm_iff`).

Spreading is a change of lines. `spread w e m n` makes position `n` share the token of `e` of
position `m`, by `Autosegmental.AR.spreadTier`: the root node of `n` is delinked from its own
token of `e` and linked to that of `m`. It crosses no line exactly when no position strictly
between the two has `e` (`noCrossing_spread_iff`). The result reads as the form in which position
`n` has `e` in the status it has at `m` (`reads_spread_iff`), so where both positions have `e` no
position's elements change (`exists_reads_spread_iff`): sharing a token reads as copying it.

## Implementation notes

The root node distinguishes a position associated with an expression that has no element from a
position associated with nothing, as [harris-1994] distinguishes a stable schwa from an empty
nucleus and [faust-2025] a weak vowel from an empty one. [harris-1994] groups the elements under
class nodes between the root node and the lines, and [kaye-lowenstamm-vergnaud-1985] let two
elements that cannot combine share a line; here each element has its own line directly under the
root node. Government and licensing, which relate positions of the skeleton to one another, are
not lines and are not represented here.

## References

* [kaye-lowenstamm-vergnaud-1985]
* [harris-1994]
* [backley-2011]
* [faust-2025]
-/

@[expose] public section

open Autosegmental

namespace ElementTheory

/-- A token of an element is the head of its expression or a dependent. -/
inductive Status where
  | head
  | dependent
  deriving DecidableEq, Repr

/-- The status of the element `e` in the expression `m`. -/
def MR.status (m : MR) (e : Element) : Status := if e ∈ m.heads then .head else .dependent

/-- `m₂.adopt m₁ e` is the expression `m₂` with the element `e` in the status it has in `m₁`. -/
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

/-- The tiers of a representation of elements: the skeleton, the root nodes, and the line of each
element. -/
inductive Tier where
  | skeleton
  | rootNode
  | line (e : Element)
  deriving DecidableEq, Fintype

/-- The tier a tier hangs from: a line from the root nodes, and the root nodes from the
skeleton. -/
def Tier.parent : Tier → Tier
  | .line _ => .rootNode
  | _ => .skeleton

/-- The tree of tiers. -/
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

/-- Only a line itself lies at or below it in the tree of tiers. -/
theorem tiers_le_line_iff {e : Element} {t : Tier} :
    tiers.toPartialOrder.le (.line e) t ↔ t = .line e := by
  refine ⟨fun ⟨n, hn⟩ ↦ ?_, fun h ↦ h ▸ ⟨0, rfl⟩⟩
  cases n with
  | zero => exact hn
  | succ n =>
    rw [tiers, ParentTree.ofIterate, Function.iterate_succ_apply] at hn
    exact absurd hn (iterate_parent_ne_line (by cases t <;> simp [Tier.parent]) n e)

/-- The alphabets of a representation of elements: slots on the skeleton, root nodes, and a
status on the line of each element. -/
abbrev Tiers : Tier → Type
  | .skeleton => Slot
  | .rootNode => Unit
  | .line _ => Status

instance : ∀ t, DecidableEq (Tiers t)
  | .skeleton => inferInstanceAs (DecidableEq Slot)
  | .rootNode => inferInstanceAs (DecidableEq Unit)
  | .line _ => inferInstanceAs (DecidableEq Status)

/-! ### Positions and forms -/

/-- A position of the skeleton, with the melodic expression of its root node if it has one. -/
structure Position where
  /-- The slot, consonantal or vocalic. -/
  slot : Slot
  /-- The melodic expression of the root node of the position. -/
  melody : Option MR := none

/-- The tokens of a position on each tier: its slot, its root node, and on the line of each
element of its expression the status of the element. -/
def Position.word (p : Position) : ∀ t, List (Tiers t)
  | .skeleton => [p.slot]
  | .rootNode => if p.melody.isSome then [()] else []
  | .line e =>
    match p.melody with
    | some m => if e ∈ m.elements then [m.status e] else []
    | none => []

/-- The representation of a position: its tokens, each linked to the token of the tier its own
hangs from. -/
def ofPosition (p : Position) : AR Tiers :=
  AR.fromRel p.word fun t' t _ _ ↦ t.parent = t' ∧ t ≠ .skeleton

/-- The representation of a form, those of its positions in order. -/
def ofForm (w : List Position) : AR Tiers := (w.map ofPosition).prod

/-- `ofForm` as a monoid homomorphism out of the free monoid on the positions. -/
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

/-- The lines of a form do not cross. -/
theorem noCrossing_ofForm (w : List Position) : (ofForm w).NoCrossing :=
  AR.NoCrossing.prod fun X hX ↦ by
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hX
    exact noCrossing_ofPosition p

/-- A token of a position is linked to the token of the tier its own hangs from. -/
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

/-- A position reads on a tier the token it has there. -/
theorem reads_ofPosition_iff {t : Tier} {b : Tiers t} :
    (ofPosition p).Reads tiers 0 t b ↔ p.word t = [b] := by
  constructor
  · rintro ⟨q, hq, -, hb⟩
    have hlen := p.length_word_le_one t
    rw [word_ofPosition] at hq hb
    rcases hw : p.word t with _ | ⟨c, _ | ⟨d, l⟩⟩
    · simp [hw] at hq
    · obtain rfl : q = 0 := by simpa [hw] using hq
      simpa [hw] using hb
    · simp [hw] at hlen
  · intro h
    exact ⟨0, by simp [h], dominates_ofPosition (by simp [h]), by simp [h]⟩

/-- Position `k` of a form reads on a tier the token it has there. -/
theorem reads_ofForm_iff {t : Tier} {b : Tiers t} :
    (ofForm w).Reads tiers k t b ↔ ∃ hk : k < w.length, w[k].word t = [b] :=
  (AR.reads_prod_map tiers ofPosition fun _ ↦ rfl).trans
    (exists_congr fun _ ↦ reads_ofPosition_iff)

/-- Position `k` of a form reads a root node exactly when it has one. -/
theorem reads_rootNode_ofForm_iff :
    (ofForm w).Reads tiers k .rootNode () ↔ ∃ p ∈ w[k]?, p.melody.isSome := by
  simp only [reads_ofForm_iff, List.getElem?_eq_some_iff, Option.mem_def]
  constructor
  · rintro ⟨hk, h⟩
    exact ⟨_, ⟨hk, rfl⟩, Position.word_rootNode_ne_nil_iff.1 (by simp [h])⟩
  · rintro ⟨_, ⟨hk, rfl⟩, h⟩
    exact ⟨hk, by simp [Position.word, h]⟩

/-- Position `k` of a form reads an element exactly when its expression contains it. -/
theorem reads_line_ofForm_iff :
    (∃ s, (ofForm w).Reads tiers k (.line e) s) ↔
      ∃ p ∈ w[k]?, ∃ m ∈ p.melody, e ∈ m.elements := by
  simp only [reads_ofForm_iff, List.getElem?_eq_some_iff, Option.mem_def]
  constructor
  · rintro ⟨s, hk, h⟩
    exact ⟨_, ⟨hk, rfl⟩, Position.word_line_ne_nil_iff.1 (by simp [h])⟩
  · rintro ⟨_, ⟨hk, rfl⟩, m, hm, he⟩
    exact ⟨m.status e, hk, by simp [Position.word, hm, he]⟩

/-! ### Spreading -/

/-- `spread w e m n` makes position `n` share the token of `e` of position `m`: the root node of
`n` is delinked from its own token of `e` and linked to that of `m`. -/
def spread (w : List Position) (e : Element) (m n : ℕ) : AR Tiers :=
  AR.spreadTier tiers ofPosition w (.line e) m n

/-- Spreading an element from one position to another crosses no line exactly when no position
strictly between them has the element. -/
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

/-- Spreading an element reads as giving the target position the element in the
status it has at the source: sharing a token reads as copying it. -/
theorem reads_spread_iff (hm : m < w.length) (hn : n < w.length) {m₁ m₂ : MR}
    (h₁ : w[m].melody = some m₁) (he : e ∈ m₁.elements) (h₂ : w[n].melody = some m₂)
    {t : Tier} {b : Tiers t} :
    (spread w e m n).Reads tiers k t b ↔
      (ofForm (w.set n ⟨w[n].slot, some (m₂.adopt m₁ e)⟩)).Reads tiers k t b := by
  refine AR.reads_spreadTier_iff ofPosition (by simp)
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

/-- Where both positions have the element, spreading it changes no position's elements: the shared
token stands for both. -/
theorem exists_reads_spread_iff (hm : m < w.length) (hn : n < w.length) {m₁ m₂ : MR}
    (h₁ : w[m].melody = some m₁) (he : e ∈ m₁.elements) (h₂ : w[n].melody = some m₂)
    (he' : e ∈ m₂.elements) {e' : Element} :
    (∃ s, (spread w e m n).Reads tiers k (.line e') s) ↔
      ∃ s, (ofForm w).Reads tiers k (.line e') s := by
  rw [exists_congr fun s ↦ reads_spread_iff (t := .line e') (b := s) hm hn h₁ he h₂,
    reads_line_ofForm_iff, reads_line_ofForm_iff]
  by_cases hk : n = k
  · subst hk
    simp only [List.getElem?_set_self hn, List.getElem?_eq_getElem hn, Option.mem_def,
      Option.some.injEq, exists_eq_left', h₂, MR.mem_elements_adopt]
    exact ⟨fun h ↦ h.elim (· ▸ he') id, .inr⟩
  · rw [List.getElem?_set_ne hk]

/-- After spreading the target position reads the element in the status it has at the source. -/
theorem reads_spread_self_iff (hm : m < w.length) (hn : n < w.length) {m₁ m₂ : MR}
    (h₁ : w[m].melody = some m₁) (he : e ∈ m₁.elements) (h₂ : w[n].melody = some m₂) :
    (spread w e m n).Reads tiers n (.line e) s ↔ s = m₁.status e := by
  rw [reads_spread_iff hm hn h₁ he h₂, reads_ofForm_iff]
  simp [hn, Position.word, MR.mem_elements_adopt, MR.status_adopt_self, eq_comm]

end ElementTheory
