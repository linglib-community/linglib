/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Prosody.Mora
public import Linglib.Phonology.Prosody.Structure

/-!
# The structure of a moraic form

A moraic form denotes a prosodic structure. Its nodes are its words, syllables, morae and
segments; a node dominates what its lines reach, in one step or several; and one node precedes
another when it stands at an earlier slot and neither dominates the other, provided both are
prosodic nodes or both are segments. A mora stranded by the loss of its segment therefore keeps
its place among the syllables and morae, as in the derivations of [hayes-1989], and has no place
among the segments until a line gives it one.

On this structure the ban on crossing lines is `Prosody.Structure.NoCrossing`, and the two
asymmetries that [hayes-1989] derives from the ban are instances of it: a stranded mora
[cannot be filled across an onset](##Prosody.MoraicForm.not_noCrossing_linkMora_of_onset) from
the syllable to its right, and it
[cannot be filled across a moraic coda](##Prosody.MoraicForm.not_noCrossing_linkMora_of_coda)
from the nucleus to its left.

## Implementation notes

Precedence between a prosodic node and a segment is not given. The drawings of [hayes-1989]
place a mora freed by Glide Formation to the left of the onset of the following syllable, though
the vowel it came from stood to the right of that onset, so a stranded mora is ordered among the
prosodic nodes alone. A geminate, one segment under two syllables, has two mothers and does not
cross: `NoCrossing` forbids a segment of the later node from preceding a segment of the earlier
one, and a shared segment precedes nothing it is equal to.

## References

* [hayes-1989]
* [bird-klein-1990]
-/

@[expose] public section

namespace Prosody

namespace MoraicForm

/-- The tiers of a moraic form. -/
inductive Tier
  | segment | mora | syllable | word
  deriving DecidableEq, Repr

/-- The rank of a tier, the segments lowest. -/
def Tier.toNat : Tier → ℕ
  | .segment => 0 | .mora => 1 | .syllable => 2 | .word => 3

/-- A node of a moraic form: a word or a syllable named by its slot, a mora, or the segment at a
slot. -/
inductive Node
  | word (w : ℕ)
  | syllable (s : ℕ)
  | mora (m : Mora)
  | segment (i : ℕ)
  deriving DecidableEq, Repr

namespace Node

/-- The tier of a node. -/
def tier : Node → Tier
  | word _ => .word | syllable _ => .syllable | mora _ => .mora | segment _ => .segment

/-- The slot at which a node stands. -/
def slot : Node → ℕ
  | word w => w | syllable s => s | mora m => m.slot | segment i => i

/-- A node is prosodic when it is not a segment. -/
def IsProsodic (a : Node) : Prop := a.tier ≠ .segment

instance (a : Node) : Decidable a.IsProsodic := inferInstanceAs (Decidable (_ ≠ _))

end Node

variable {α : Type*} (X : MoraicForm α)

/-- The nodes present in a form. -/
def Mem : Node → Prop
  | .word w => w ∈ X.words
  | .syllable s => s ∈ X.syllables
  | .mora m => m ∈ X.morae
  | .segment i => i ∈ X.slots

/-- The lines of a form: one node immediately dominates another. -/
def Link : Node → Node → Prop
  | .word w, .syllable s => (w, s) ∈ X.wordSyllable
  | .syllable s, .mora m => (s, m) ∈ X.syllableMora
  | .word w, .segment i => (w, i) ∈ X.wordSegment
  | .syllable s, .segment i => (s, i) ∈ X.syllableSegment
  | .mora m, .segment i => (m, i) ∈ X.moraSegment
  | _, _ => False

variable {X}

theorem Link.tier_lt {a b : Node} (h : X.Link a b) : b.tier.toNat < a.tier.toNat := by
  cases a <;> cases b <;> first | exact h.elim | simp [Node.tier, Tier.toNat]

variable (X) in
/-- One node dominates another when lines lead from it down to the other. -/
def Dom : Node → Node → Prop := Relation.ReflTransGen X.Link

theorem Dom.eq_or_tier_lt {a b : Node} (h : X.Dom a b) : a = b ∨ b.tier.toNat < a.tier.toNat := by
  induction h with
  | refl => exact .inl rfl
  | tail _ hbc ih =>
    rcases ih with rfl | ih
    · exact .inr hbc.tier_lt
    · exact .inr (hbc.tier_lt.trans ih)

theorem Dom.antisymm {a b : Node} (hab : X.Dom a b) (hba : X.Dom b a) : a = b := by
  rcases hab.eq_or_tier_lt with rfl | h₁
  · rfl
  · rcases hba.eq_or_tier_lt with rfl | h₂
    · rfl
    · exact absurd h₁ (Nat.lt_asymm h₂)

/-- No line starts at a segment, so a segment dominates only itself. -/
theorem Dom.eq_of_segment {i : ℕ} {b : Node} (h : X.Dom (.segment i) b) : b = .segment i := by
  rcases h.eq_or_tier_lt with rfl | h
  · rfl
  · exact absurd h (Nat.not_lt_zero _)

/-- Morae stand on one tier, so one dominates another only if they are the same. -/
theorem Dom.eq_of_mora {m m' : Mora} (h : X.Dom (.mora m) (.mora m')) : m = m' := by
  rcases h.eq_or_tier_lt with e | h
  · exact Node.mora.inj e
  · exact absurd h (Nat.lt_irrefl _)

variable (X)

/-- The prosodic structure of a moraic form. Dominance is the closure of its lines, and a node
precedes another at a later slot when neither dominates the other and both are prosodic or both
are segments. -/
def toStructure : Structure Tier where
  Node := {a : Node // X.Mem a}
  dominance :=
    { le := fun a b ↦ X.Dom a.val b.val
      le_refl := fun _ ↦ Relation.ReflTransGen.refl
      le_trans := fun _ _ _ ↦ Relation.ReflTransGen.trans
      le_antisymm := fun _ _ hab hba ↦ Subtype.ext (hab.antisymm hba) }
  Precedes a b := (a.val.IsProsodic ↔ b.val.IsProsodic) ∧ a.val.slot < b.val.slot ∧
    ¬X.Dom a.val b.val ∧ ¬X.Dom b.val a.val
  label a := a.val.tier

variable {X}

theorem toStructure_le_iff {a b : X.toStructure.Node} : a ≤ b ↔ X.Dom a.val b.val := Iff.rfl

theorem toStructure_lt_of_link {a b : X.toStructure.Node} (h : X.Link a.val b.val) : a < b :=
  lt_of_le_of_ne (Relation.ReflTransGen.single h) fun e ↦
    absurd h.tier_lt (e ▸ Nat.lt_irrefl _)

/-- Two segments at different slots stand in precedence. -/
theorem toStructure_precedes_segment {i j : ℕ} (hi : X.Mem (.segment i)) (hj : X.Mem (.segment j))
    (hij : i < j) : X.toStructure.Precedes ⟨.segment i, hi⟩ ⟨.segment j, hj⟩ :=
  ⟨Iff.rfl, hij, fun h ↦ hij.ne (Node.segment.inj (Dom.eq_of_segment h)).symm,
    fun h ↦ hij.ne (Node.segment.inj (Dom.eq_of_segment h))⟩

/-! ### The asymmetries of compensatory lengthening -/

variable {m : Mora} {v c : ℕ}

/-- **The vowel-loss asymmetry** ([hayes-1989]): a mora standing to the left of a syllable that
does not dominate it cannot be linked to that syllable's nucleus across its onset. The mora
precedes the syllable, and the onset, which the syllable dominates, precedes the nucleus, which
the mora would dominate. -/
theorem not_noCrossing_linkMora_of_onset (hc : (v, c) ∈ X.syllableSegment) (hm : m ∈ X.morae)
    (hv : v ∈ X.syllables) (hvs : v ∈ X.slots) (hcs : c ∈ X.slots) (hmv : m.slot < v)
    (hcv : c < v) (hdom : (v, m) ∉ X.syllableMora) :
    ¬(X.linkMora m v).toStructure.NoCrossing := fun h ↦ by
  have hnd : ¬(X.linkMora m v).Dom (.syllable v) (.mora m) := fun hd ↦ by
    rcases Relation.ReflTransGen.cases_head hd with e | ⟨b, hb, hbm⟩
    · exact absurd e nofun
    · cases b with
      | mora m' => exact hdom (Dom.eq_of_mora hbm ▸ hb)
      | segment i => exact absurd (Dom.eq_of_segment hbm) nofun
      | word _ => exact hb.elim
      | syllable _ => exact hb.elim
  have hnd' : ¬(X.linkMora m v).Dom (.mora m) (.syllable v) := fun hd ↦ by
    rcases hd.eq_or_tier_lt with e | ht
    · exact absurd e nofun
    · exact absurd ht (by simp [Node.tier, Tier.toNat])
  refine h (a := ⟨.mora m, hm⟩) (a' := ⟨.syllable v, hv⟩) (b := ⟨.segment v, hvs⟩)
    (b' := ⟨.segment c, hcs⟩) ⟨by simp [Node.IsProsodic, Node.tier], hmv, hnd', hnd⟩ ?_ ?_ ?_
  · exact toStructure_lt_of_link (X := X.linkMora m v) (Finset.mem_insert_self _ _)
  · exact toStructure_lt_of_link (X := X.linkMora m v) (a := ⟨.syllable v, hv⟩)
      (b := ⟨.segment c, hcs⟩) hc
  · exact toStructure_precedes_segment (X := X.linkMora m v) hcs hvs hcv

/-- **No lengthening across a moraic coda** ([hayes-1989]): a mora standing to the right of a
coda's mora cannot be linked to the nucleus to the left of the coda. The coda's mora precedes
it, and the nucleus, which it would dominate, precedes the coda. -/
theorem not_noCrossing_linkMora_of_coda (hc : (Mora.of c, c) ∈ X.moraSegment)
    (hm : m ∈ X.morae) (hcm : Mora.of c ∈ X.morae) (hvs : v ∈ X.slots) (hcs : c ∈ X.slots)
    (hvc : v < c) (hcm' : c < m.slot) : ¬(X.linkMora m v).toStructure.NoCrossing := fun h ↦ by
  have hne : Mora.of c ≠ m := fun e ↦ (e ▸ hcm').false
  refine h (a := ⟨.mora (.of c), hcm⟩) (a' := ⟨.mora m, hm⟩) (b := ⟨.segment c, hcs⟩)
    (b' := ⟨.segment v, hvs⟩) ⟨Iff.rfl, hcm', fun hd ↦ hne (Dom.eq_of_mora hd),
      fun hd ↦ hne (Dom.eq_of_mora hd).symm⟩ ?_ ?_ ?_
  · exact toStructure_lt_of_link (X := X.linkMora m v) (a := ⟨.mora (.of c), hcm⟩)
      (b := ⟨.segment c, hcs⟩) (Finset.mem_insert_of_mem hc)
  · exact toStructure_lt_of_link (X := X.linkMora m v) (Finset.mem_insert_self _ _)
  · exact toStructure_precedes_segment (X := X.linkMora m v) hvs hcs hvc

end MoraicForm

end Prosody
