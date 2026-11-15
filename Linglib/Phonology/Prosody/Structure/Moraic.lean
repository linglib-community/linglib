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
from the nucleus to its left. The condition is
[decided from the lines of the form](##Prosody.MoraicForm.toStructure_noCrossing_iff), and it
[differs from
`MoraicForm.NoCrossing`](##Prosody.MoraicForm.exists_noCrossing_toStructure_not_noCrossing) on a
consonant linked to its syllable after a later mora.

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

section Decidable

open Finset

variable (X)

/-! ### Dominance, decided -/

/-- The nodes a node is linked to below it. -/
def linked : Node → Finset Node
  | .word w => (X.wordSyllable.filter (·.1 = w)).image (fun p ↦ .syllable p.2) ∪
      (X.wordSegment.filter (·.1 = w)).image (fun p ↦ .segment p.2)
  | .syllable s => (X.syllableMora.filter (·.1 = s)).image (fun p ↦ .mora p.2) ∪
      (X.syllableSegment.filter (·.1 = s)).image (fun p ↦ .segment p.2)
  | .mora m => (X.moraSegment.filter (·.1 = m)).image (fun p ↦ .segment p.2)
  | .segment _ => ∅

/-- The nodes reached from a node by at most `n` lines down. -/
def reach : ℕ → Node → Finset Node
  | 0, a => {a}
  | n + 1, a => insert a ((X.linked a).biUnion (reach n))

/-- The nodes a node dominates. A line lowers the tier, so three lines reach every one. -/
def dominated (a : Node) : Finset Node := X.reach 3 a

variable {X}

@[simp] theorem mem_linked {a b : Node} : b ∈ X.linked a ↔ X.Link a b := by
  cases a <;> cases b <;> simp [linked, Link]

theorem Tier.toNat_le_three (t : Tier) : t.toNat ≤ 3 := by
  cases t <;> decide

theorem dom_of_mem_reach {n : ℕ} {a b : Node} (h : b ∈ X.reach n a) : X.Dom a b := by
  induction n generalizing a with
  | zero => exact (mem_singleton.1 h) ▸ Relation.ReflTransGen.refl
  | succ n ih =>
    rcases mem_insert.1 h with rfl | h
    · exact Relation.ReflTransGen.refl
    · obtain ⟨c, hc, hb⟩ := mem_biUnion.1 h
      exact .head (mem_linked.1 hc) (ih hb)

theorem mem_reach_of_dom {a b : Node} (h : X.Dom a b) {n : ℕ} (hn : a.tier.toNat ≤ n) :
    b ∈ X.reach n a := by
  induction h using Relation.ReflTransGen.head_induction_on generalizing n with
  | refl => cases n <;> simp [reach]
  | head hac _ ih =>
    cases n with
    | zero => exact absurd (hac.tier_lt.trans_le hn) (Nat.not_lt_zero _)
    | succ n => exact mem_insert_of_mem (mem_biUnion.2
        ⟨_, mem_linked.2 hac, ih (Nat.lt_succ_iff.1 (hac.tier_lt.trans_le hn))⟩)

@[simp] theorem mem_dominated {a b : Node} : b ∈ X.dominated a ↔ X.Dom a b :=
  ⟨dom_of_mem_reach, fun h ↦ mem_reach_of_dom h a.tier.toNat_le_three⟩

variable (X) in
instance : DecidableRel X.Dom := fun _ _ ↦ decidable_of_iff _ mem_dominated

/-! #### Dominance tier by tier -/

theorem Node.exists {P : Node → Prop} : (∃ a, P a) ↔ (∃ w, P (.word w)) ∨
    (∃ s, P (.syllable s)) ∨ (∃ m, P (.mora m)) ∨ ∃ i, P (.segment i) := by
  refine ⟨fun ⟨a, h⟩ ↦ ?_, ?_⟩
  · cases a
    exacts [.inl ⟨_, h⟩, .inr (.inl ⟨_, h⟩), .inr (.inr (.inl ⟨_, h⟩)), .inr (.inr (.inr ⟨_, h⟩))]
  · rintro (⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩) <;> exact ⟨_, h⟩

/-- A node dominates itself and what its linked dominate. -/
theorem dom_iff {a b : Node} : X.Dom a b ↔ b = a ∨ ∃ c, X.Link a c ∧ X.Dom c b := by
  rw [Dom, Relation.ReflTransGen.cases_head_iff, eq_comm]

/-- A segment dominates only itself. -/
@[simp] theorem dom_segment_iff {i : ℕ} {b : Node} : X.Dom (.segment i) b ↔ b = .segment i :=
  ⟨Dom.eq_of_segment, fun h ↦ h ▸ Relation.ReflTransGen.refl⟩

/-- A mora dominates itself and the segments it is linked to. -/
@[simp] theorem dom_mora_iff {m : Mora} {b : Node} :
    X.Dom (.mora m) b ↔ b = .mora m ∨ ∃ i, (m, i) ∈ X.moraSegment ∧ b = .segment i := by
  rw [dom_iff]
  simp [Node.exists, Link]

/-- A syllable dominates itself, what its morae dominate, and the segments it is linked to. -/
@[simp] theorem dom_syllable_iff {s : ℕ} {b : Node} :
    X.Dom (.syllable s) b ↔ b = .syllable s ∨
      (∃ m, (s, m) ∈ X.syllableMora ∧ X.Dom (.mora m) b) ∨
        ∃ i, (s, i) ∈ X.syllableSegment ∧ b = .segment i := by
  rw [dom_iff]
  simp only [Node.exists, Link, false_and, exists_false, false_or, dom_segment_iff]

/-- A word dominates itself, what its syllables dominate, and the segments it is linked to. -/
@[simp] theorem dom_word_iff {w : ℕ} {b : Node} :
    X.Dom (.word w) b ↔ b = .word w ∨
      (∃ s, (w, s) ∈ X.wordSyllable ∧ X.Dom (.syllable s) b) ∨
        ∃ i, (w, i) ∈ X.wordSegment ∧ b = .segment i := by
  rw [dom_iff]
  simp only [Node.exists, Link, false_and, exists_false, false_or, dom_segment_iff]

/-- Only a prosodic node properly dominates anything. -/
theorem Dom.isProsodic {a b : Node} (h : X.Dom a b) (hne : a ≠ b) : a.IsProsodic := by
  cases a with
  | segment i => exact absurd h.eq_of_segment.symm hne
  | _ => nofun

/-! ### No Crossing, decided -/

variable (X)

instance : DecidablePred X.Mem
  | .word w => inferInstanceAs (Decidable (w ∈ X.words))
  | .syllable s => inferInstanceAs (Decidable (s ∈ X.syllables))
  | .mora m => inferInstanceAs (Decidable (m ∈ X.morae))
  | .segment i => inferInstanceAs (Decidable (i ∈ X.slots))

/-- Precedence on the nodes of a form, as in `toStructure`: a node precedes another at a later
slot when neither dominates the other and both are prosodic or both are segments. -/
def Precedes (a b : Node) : Prop :=
  (a.IsProsodic ↔ b.IsProsodic) ∧ a.slot < b.slot ∧ ¬X.Dom a b ∧ ¬X.Dom b a

instance : DecidableRel X.Precedes := fun a b ↦
  inferInstanceAs (Decidable ((a.IsProsodic ↔ b.IsProsodic) ∧ a.slot < b.slot ∧ ¬X.Dom a b ∧
    ¬X.Dom b a))

/-- The prosodic nodes of a form: its words, syllables and morae. -/
def prosodicNodes : Finset Node :=
  X.words.image .word ∪ X.syllables.image .syllable ∪ X.morae.image .mora

variable {X}

theorem toStructure_precedes_iff {a b : X.toStructure.Node} :
    X.toStructure.Precedes a b ↔ X.Precedes a.val b.val := Iff.rfl

@[simp] theorem mem_prosodicNodes {a : Node} : a ∈ X.prosodicNodes ↔ X.Mem a ∧ a.IsProsodic := by
  cases a <;> simp [prosodicNodes, Mem, Node.IsProsodic, Node.tier]

theorem toStructure_lt_iff {a b : X.toStructure.Node} : a < b ↔ X.Dom a.val b.val ∧ a.val ≠ b.val :=
  lt_iff_le_and_ne.trans (and_congr_right' Subtype.ext_iff.not)

/-- No Crossing on the structure of a form ranges over pairs of prosodic nodes and the nodes
present that each properly dominates. -/
theorem toStructure_noCrossing_iff : X.toStructure.NoCrossing ↔
    ∀ a ∈ X.prosodicNodes, ∀ a' ∈ X.prosodicNodes, X.Precedes a a' →
      ∀ b ∈ (X.dominated a).erase a, ∀ b' ∈ (X.dominated a').erase a',
        X.Mem b → X.Mem b' → ¬X.Precedes b' b := by
  simp only [mem_prosodicNodes, mem_erase, mem_dominated]
  refine ⟨fun h a ha a' ha' hp b hb b' hb' hbm hbm' ↦ ?_, fun h a a' b b' hp hab hab' ↦ ?_⟩
  · exact h (a := ⟨a, ha.1⟩) (a' := ⟨a', ha'.1⟩) (b := ⟨b, hbm⟩) (b' := ⟨b', hbm'⟩) hp
      (toStructure_lt_iff.2 ⟨hb.2, hb.1.symm⟩) (toStructure_lt_iff.2 ⟨hb'.2, hb'.1.symm⟩)
  · rw [toStructure_lt_iff] at hab hab'
    exact h a.val ⟨a.2, hab.1.isProsodic hab.2⟩ a'.val ⟨a'.2, hab'.1.isProsodic hab'.2⟩ hp
      b.val ⟨hab.2.symm, hab.1⟩ b'.val ⟨hab'.2.symm, hab'.1⟩ b.2 b'.2

instance : Decidable X.toStructure.NoCrossing := decidable_of_iff _ toStructure_noCrossing_iff.symm

/-- The two conditions differ off the forms of [hayes-1989]: a consonant linked to its syllable
after a mora headed later than the nucleus crosses nothing on the prosodic structure, and counts
as a crossing for `MoraicForm.NoCrossing`, which sets a syllable and its own morae on one row
of slots. -/
theorem exists_noCrossing_toStructure_not_noCrossing :
    ∃ X : MoraicForm ℕ, X.WellFormed ∧ X.toStructure.NoCrossing ∧ ¬X.NoCrossing :=
  ⟨ofLines [0, 1, 2, 3] (syllableMora := {(1, .of 1), (1, .of 2)})
    (syllableSegment := {(1, 0), (1, 3)}) (moraSegment := {(.of 1, 1), (.of 2, 2)}), by decide⟩

end Decidable

end MoraicForm

end Prosody
