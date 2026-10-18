/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Relation.ReflTransGen
public import Linglib.Morphology.Morphotactics.CVTemplate
public import Linglib.Phonology.Autosegmental.Melody
public import Linglib.Phonology.RuleInteraction

/-!
# Laoide-Kemp (2026): Strict modularity at the morphosyntax-phonology interface

Laoide-Kemp analyses the Irish historic-tense particle *d'*, which appears before vowel-initial
and lenited *f*-initial verbs but not before other consonants ((11)). Its exponent is a floating
`d` followed by the lenition-inducing bundle `{L}` on the melodic tier, inserted in every
environment over a strict-CV skeleton ((18)). A floating object docks on the slot immediately to
its right when that slot suits it: `{L}` on a consonant, deleting the segmental content of an *f*,
and `d` on a segmentally empty C-slot before a filled V-slot. These processes apply whenever their
conditions are met (§4.2), and an empty CV unit at the left edge of a word, her representation of
the past-tense impersonal, blocks both (§6.2).

## Main definitions

* `historic`: the historic-tense marker, a floating `d` before `{L}`.
* `CanDock`, `dock`: when and how a floating object docks.
* `Step`, `IsSurface`, `surfaces`: one docking, a candidate where none applies, and the surface
  forms a candidate derives.

## Main results

* `surfaces_nonempty`: every candidate derives a surface form.
* `card_surfaces_historic`, `historic_bog`, `historic_ól`, `historic_fág`: each form of Figure 1
  has one surface form, with `d` pronounced before *ól* and *fág* but not before *bog*.
* `lenition_feeds_linking`, `not_linking_feeds_lenition`: lenition feeds the linking of `d` and
  not conversely, so the order of the two processes is intrinsic.
* `isFloating_of_emptyCV`: whatever the stem, after an empty CV unit neither `d` nor `{L}` docks.

## Implementation notes

The segments are written orthographically, as in the paper's CV diagrams. The slot immediately to
the right of a melodic object is the first slot after every slot linked to an object before it,
the left edge of its window under the No-Crossing Constraint (`leftIndices`). Once `d` is linked,
the slot to the right of `{L}` is the following V-slot, so `{L}` never acts on `d`, the consequence
of melodic order that §4.2 draws. `{L}` docking is a line from `{L}` to the slot of the consonant
it acts on, and of its effects only the deletion of *f* is modelled, which leaves the C-slot, as
Gussmann argues; Ní Chiosáin's evidence that lexical palatalization sits on such a slot is not
modelled. The condition on `d` applies to every floating segment, as §4.3 extends it to the
prothetic consonants. The phonology is defined for any type of sponsoring morpheme, so it cannot
consult the morphosyntax, which is Bermúdez-Otero's strict modularity. The suffix of the
impersonal forms is not modelled.

## TODO

Model the infrasegmental-government domains of Figure 2, after Scheer, which license `d` before
lenited *fl-* and *fr-* clusters ((12)), and the Munster forms of Table 3, where the floating `d`
accompanies `{L}` after every lenition-triggering particle.

## References

* [laoide-kemp-2026]
* [bermudez-otero-2012]
* [lowenstamm-1996]
* [gussmann-1986]
* [ni-chiosain-1991]
* [scheer-1998]
-/

@[expose] public section

namespace LaoideKemp2026

open Autosegmental Relation RuleInteraction
open Morphology (CVSlot)

/-! ### Representations -/

/-- The segments of the paper's examples, written orthographically as in its CV diagrams. -/
inductive Segment
  | á | b | d | f | g | l | o | ó
  deriving DecidableEq, Repr

/-- An object of the melodic tier is a segment or the lenition-inducing bundle `{L}`, whose
content the paper leaves open. -/
inductive Autosegment
  /-- A segment. -/
  | seg (s : Segment)
  /-- The lenition-inducing bundle `{L}`. -/
  | L
  deriving DecidableEq, Repr

section Exponents

variable {M : Type*} (m : M)

/-- The historic-tense marker ((18)) is a floating `d` followed by `{L}`, with no skeleton. -/
def historic : Autosegmental.Form CVSlot Autosegment M := .melody m [.seg .d, .L] [] ∅

/-- An empty CV unit, the left edge of a word that resists mutation (§6.2). -/
def emptyCV : Autosegmental.Form CVSlot Autosegment M := .melody m [] [.C, .V] ∅

variable {m} (s : Autosegmental.Form CVSlot Autosegment M)

/-- The floating `d` of a historic-tense form. -/
def d : Fin (historic m * s).upper.length := ⟨0, by simp [historic]⟩

/-- The bundle `{L}` of a historic-tense form. -/
def L : Fin (historic m * s).upper.length := ⟨1, by simp [historic]⟩

end Exponents

/-! ### Docking -/

section Docking

variable {M : Type*} {u : Autosegmental.Form CVSlot Autosegment M} (c : Candidate u)

/-- Slot `i` hosts a segment on the surface. -/
def HostsSegment (i : Fin u.lower.length) : Prop := ∃ k, (k, i) ∈ c.links ∧ u.upper[k].value ≠ .L

instance (i : Fin u.lower.length) : Decidable (HostsSegment c i) :=
  inferInstanceAs (Decidable (∃ _, _ ∧ _))

/-- The slot immediately to the right of object `k` is the first slot after every slot linked to
an object before it. -/
def nextSlot (k : Fin u.upper.length) : ℕ := (leftIndices c.links k).sup (·.val + 1)

/-- A docking site for `{L}` is a C-slot hosting the consonant it acts on, and for a segment a
segmentally empty C-slot directly followed by a V-slot hosting a segment. -/
def IsDockingSite : Autosegment → Fin u.lower.length → Prop
  | .L, i => u.lower[i].value = .C ∧ HostsSegment c i
  | .seg _, i => u.lower[i].value = .C ∧ ¬ HostsSegment c i ∧
      ∃ i' : Fin u.lower.length, i'.val = i.val + 1 ∧ u.lower[i'].value = .V ∧ HostsSegment c i'

instance : ∀ a i, Decidable (IsDockingSite c a i)
  | .L, _ => inferInstanceAs (Decidable (_ ∧ _))
  | .seg _, _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

variable {c} in
theorem IsDockingSite.isC {i : Fin u.lower.length} : ∀ {a}, IsDockingSite c a i →
    u.lower[i].value = .C
  | .L, h | .seg _, h => h.1

/-- Object `k` can dock when it is floating and the slot immediately to its right is a docking
site for it. -/
def CanDock (k : Fin u.upper.length) : Prop :=
  c.IsFloating k ∧
    ∃ i : Fin u.lower.length, i.val = nextSlot c k ∧ IsDockingSite c u.upper[k].value i

instance (k : Fin u.upper.length) : Decidable (CanDock c k) :=
  inferInstanceAs (Decidable (_ ∧ ∃ _, _))

/-- The *f* on slot `i`, whose segmental content `{L}` deletes (§2.2). -/
def fOn (i : Fin u.lower.length) : Option (Fin u.upper.length) :=
  (c.linksTo i).find? (u.upper[·].value = .seg .f)

/-- Object `k` docks on the slot immediately to its right; `{L}` docking on an *f* deletes its
segmental content and leaves the slot. -/
def dock (k : Fin u.upper.length) : Candidate u :=
  if h : nextSlot c k < u.lower.length then
    let i : Fin u.lower.length := ⟨nextSlot c k, h⟩
    if u.upper[k].value = .L then
      (fOn c i).elim (c.insertLink k i) (c.insertLink k i).deleteTierElem
    else c.insertLink k i
  else c

/-- A step docks one floating object where it can. -/
inductive Step : Candidate u → Candidate u → Prop
  | dock {c : Candidate u} {k : Fin u.upper.length} :
      CanDock c k → Step c (LaoideKemp2026.dock c k)

/-- A surface form is a candidate where no object can dock. -/
def IsSurface : Prop := ∀ k, ¬ CanDock c k

instance : Decidable (IsSurface c) := inferInstanceAs (Decidable (∀ _, _))

variable {c} {c' : Candidate u} {k j : Fin u.upper.length}

theorem mem_links_of_fOn_eq_some {i : Fin u.lower.length} (h : fOn c i = some j) :
    (j, i) ∈ c.links :=
  Candidate.mem_linksTo.1 (List.mem_of_find?_eq_some h)

theorem isSurface_iff_forall_not_step : IsSurface c ↔ ∀ c', ¬ Step c c' :=
  ⟨fun h _ hs ↦ by cases hs with | dock hk => exact h _ hk, fun h _ hk ↦ h _ (.dock hk)⟩

theorem isFloating_of_isFloating_dock (hk : CanDock c k) (h : (dock c k).IsFloating j) :
    j ≠ k ∧ c.IsFloating j := by
  obtain ⟨-, i, hi, -⟩ := hk
  have hlt : nextSlot c k < u.lower.length := hi ▸ i.isLt
  simp only [dock, hlt, dite_true] at h
  split_ifs at h
  · revert h
    rcases fOn c ⟨nextSlot c k, hlt⟩ with _ | j' <;> simp_all
  · simp_all

variable (c) in
/-- The number of floating objects. -/
def floatingCount : ℕ := (Finset.univ.filter c.IsFloating).card

/-- Each step docks a floating object and floats none. -/
theorem Step.floatingCount_lt (h : Step c c') : floatingCount c' < floatingCount c := by
  obtain ⟨hk⟩ := h
  refine Finset.card_lt_card <| (Finset.ssubset_iff_of_subset fun j hj ↦ ?_).2
    ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, hk.1⟩, fun h ↦ ?_⟩
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
      (isFloating_of_isFloating_dock hk (Finset.mem_filter.1 hj).2).2⟩
  · exact (isFloating_of_isFloating_dock hk (Finset.mem_filter.1 h).2).1 rfl

variable (c) in
/-- The candidates one step away. -/
def steps : Finset (Candidate u) := (Finset.univ.filter (CanDock c)).image (dock c)

theorem mem_steps : c' ∈ steps c ↔ Step c c' := by
  simp only [steps, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨_, hk, h⟩ ↦ h ▸ .dock hk, fun ⟨hk⟩ ↦ ⟨_, hk, rfl⟩⟩

variable (c) in
/-- The candidates a candidate derives, by as many rounds of steps as it has floating objects. -/
def derived : Finset (Candidate u) :=
  (ReflTransGen.closeStep steps)^[floatingCount c] {c}

theorem mem_derived : c' ∈ derived c ↔ ReflTransGen Step c c' := by
  rw [derived, ReflTransGen.mem_iterate_closeStep_iff
    (fun _ _ h ↦ (mem_steps.1 h).floatingCount_lt) le_rfl]
  simp only [mem_steps]

variable (c) in
/-- The surface forms a candidate derives. -/
def surfaces : Finset (Candidate u) := (derived c).filter IsSurface

theorem mem_surfaces : c' ∈ surfaces c ↔ ReflTransGen Step c c' ∧ IsSurface c' := by
  rw [surfaces, Finset.mem_filter, mem_derived]

variable (c) in
/-- Every candidate derives a surface form. -/
theorem surfaces_nonempty : (surfaces c).Nonempty := by
  induction h : floatingCount c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    by_cases hs : IsSurface c
    · exact ⟨c, mem_surfaces.2 ⟨.refl, hs⟩⟩
    · obtain ⟨k, hk⟩ := not_forall_not.1 hs
      obtain ⟨c', hc'⟩ := ih _ (h ▸ (Step.dock hk).floatingCount_lt) _ rfl
      exact ⟨c', mem_surfaces.2 ⟨.head (.dock hk) (mem_surfaces.1 hc').1, (mem_surfaces.1 hc').2⟩⟩

end Docking

/-! ### The empty CV unit

An empty CV unit is no docking site for anything: `{L}` finds no consonant on its C-slot, and a
segment finds its V-slot empty. So the same structure blocks both lenition and the linking of `d`
(§6.2). -/

section EmptyCV

variable {M : Type*} {u : Autosegmental.Form CVSlot Autosegment M} {c c' : Candidate u}
  {k j : Fin u.upper.length}

theorem not_isDockingSite_of_emptyCV {i i' : Fin u.lower.length} (hi' : i'.val = i.val + 1)
    (hc : ¬ HostsSegment c i) (hv : ¬ HostsSegment c i') : ∀ a, ¬ IsDockingSite c a i
  | .L, h => hc h.2
  | .seg _, ⟨_, _, _, hi'', _, h⟩ => hv (Fin.ext (hi'.trans hi''.symm) ▸ h)

theorem links_dock_subset (hk : CanDock c k) :
    ∃ i : Fin u.lower.length, i.val = nextSlot c k ∧ (dock c k).links ⊆ insert (k, i) c.links := by
  obtain ⟨-, i, hi, -⟩ := hk
  have hlt : nextSlot c k < u.lower.length := hi ▸ i.isLt
  refine ⟨i, hi, ?_⟩
  obtain rfl : i = ⟨nextSlot c k, hlt⟩ := Fin.ext hi
  simp only [dock, hlt, dite_true]
  split_ifs
  · rcases fOn c ⟨nextSlot c k, hlt⟩ with _ | j'
    exacts [Finset.Subset.refl _, Candidate.links_deleteTierElem_subset]
  · exact Finset.Subset.refl _

theorem isFloating_dock (hk : CanDock c k) (hj : c.IsFloating j) (hjk : j ≠ k) :
    (dock c k).IsFloating j := by
  obtain ⟨-, i, hi, -⟩ := hk
  have hlt : nextSlot c k < u.lower.length := hi ▸ i.isLt
  simp only [dock, hlt, dite_true]
  split_ifs
  · rcases hf : fOn c ⟨nextSlot c k, hlt⟩ with _ | j'
    · exact Candidate.isFloating_insertLink.2 ⟨hjk, hj⟩
    refine Candidate.isFloating_deleteTierElem.2 ⟨?_, Candidate.isFloating_insertLink.2 ⟨hjk, hj⟩⟩
    rintro rfl
    exact hj.2 (Candidate.isLinked_iff.2 ⟨_, mem_links_of_fOn_eq_some hf⟩)
  · exact Candidate.isFloating_insertLink.2 ⟨hjk, hj⟩

variable {m m' : M} {s : Autosegmental.Form CVSlot Autosegment M}

private theorem two_le_of_mem_links {p} (hp : p ∈ (historic m * (emptyCV m' * s)).links) :
    2 ≤ p.1.val ∧ 2 ≤ p.2.val := by
  rcases Form.mem_links_concat.1 hp with ⟨q, hq, -⟩ | ⟨q, hq, h₁, h₂⟩
  · exact absurd (Form.mem_links_melody.1 hq) (Finset.notMem_empty _)
  rcases Form.mem_links_concat.1 hq with ⟨r, hr, -⟩ | ⟨r, hr, h₃, h₄⟩
  · exact absurd (Form.mem_links_melody.1 hr) (Finset.notMem_empty _)
  simp only [historic, emptyCV, Form.melody_upper, Form.melody_lower, List.length_map,
    List.length_cons, List.length_nil] at h₁ h₂ h₄
  omega

/-- In a historic-tense form over an empty CV unit, `d` and `{L}` float and the unit hosts no
segment. -/
private def Blocked (c : Candidate (historic m * (emptyCV m' * s))) : Prop :=
  c.IsFloating (d _) ∧ c.IsFloating (L _) ∧ ∀ i : Fin _, i.val < 2 → ¬ HostsSegment c i

private theorem nextSlot_eq_zero {c : Candidate (historic m * (emptyCV m' * s))} (h : Blocked c)
    {k : Fin _} (hk : k.val < 2) : nextSlot c k = 0 := by
  refine Finset.sup_eq_bot_iff _ _ |>.2 fun x hx ↦ ?_
  obtain ⟨n, hn, hnx⟩ := mem_leftIndices.1 hx
  obtain rfl : n = d s := Fin.ext (by simp only [d]; have := Fin.lt_def.1 hn; omega)
  exact absurd (Candidate.isLinked_iff.2 ⟨_, hnx⟩) h.1.2

private theorem two_le_of_canDock {c : Candidate (historic m * (emptyCV m' * s))} (h : Blocked c)
    {k : Fin _} (hk : CanDock c k) : 2 ≤ k.val ∧ 2 ≤ nextSlot c k := by
  have hlen : 1 < (historic m * (emptyCV m' * s)).lower.length := by
    simp [historic, emptyCV]
  obtain ⟨-, i, hi, hs⟩ := hk
  have hi0 : i.val ≠ 0 := fun h0 ↦ not_isDockingSite_of_emptyCV (i' := ⟨1, hlen⟩) (by simp [h0])
    (h.2.2 _ (by omega)) (h.2.2 _ (by simp)) _ hs
  have hi1 : i.val ≠ 1 := fun h1 ↦ by
    obtain rfl : i = ⟨1, hlen⟩ := Fin.ext h1
    have hV : (historic m * (emptyCV m' * s)).lower[(⟨1, hlen⟩ : Fin _)].value = .V := rfl
    exact absurd (hs.isC.symm.trans hV) (by decide)
  refine ⟨Nat.le_of_not_lt fun hk2 ↦ hi0 ?_, by omega⟩
  rw [hi, nextSlot_eq_zero h hk2]

private theorem blocked_input : Blocked (.input (historic m * (emptyCV m' * s))) := by
  refine ⟨⟨Finset.notMem_empty _, ?_⟩, ⟨Finset.notMem_empty _, ?_⟩, ?_⟩
  · rintro ⟨p, hp, hpd⟩
    exact absurd (two_le_of_mem_links hp).1 (by rw [hpd]; show ¬ 2 ≤ 0; omega)
  · rintro ⟨p, hp, hpL⟩
    exact absurd (two_le_of_mem_links hp).1 (by rw [hpL]; show ¬ 2 ≤ 1; omega)
  · rintro i hi ⟨k, hk, -⟩
    have := (two_le_of_mem_links hk).2
    dsimp only at this
    omega

private theorem Blocked.step {c c' : Candidate (historic m * (emptyCV m' * s))} (h : Blocked c)
    (hs : Step c c') : Blocked c' := by
  obtain ⟨hk⟩ := hs
  obtain ⟨hk2, hi2⟩ := two_le_of_canDock h hk
  obtain ⟨i, hi, hsub⟩ := links_dock_subset hk
  refine ⟨isFloating_dock hk h.1 fun he ↦ ?_, isFloating_dock hk h.2.1 fun he ↦ ?_,
    fun i₀ hi₀ ⟨k', hk', hval⟩ ↦ ?_⟩
  · exact absurd hk2 (by rw [← he]; show ¬ 2 ≤ 0; omega)
  · exact absurd hk2 (by rw [← he]; show ¬ 2 ≤ 1; omega)
  · rcases Finset.mem_insert.1 (hsub hk') with he | he
    · have := congrArg (·.2.val) he
      simp only at this
      omega
    · exact h.2.2 i₀ hi₀ ⟨k', he, hval⟩

/-- Whatever the stem, in a historic-tense form whose stem begins with an empty CV unit, `d` and
`{L}` float in every candidate derived: the form is neither lenited nor preceded by *d'*
(Figure 5, §6.2). -/
theorem isFloating_of_emptyCV {c : Candidate (historic m * (emptyCV m' * s))}
    (hc : ReflTransGen Step (.input _) c) : c.IsFloating (d _) ∧ c.IsFloating (L _) := by
  have : Blocked c := by
    induction hc with
    | refl => exact blocked_input
    | tail _ hs ih => exact ih.step hs
  exact ⟨this.1, this.2.1⟩

end EmptyCV

/-! ### The forms of Figures 1 and 5 -/

/-- The morphemes that sponsor the paper's forms. -/
inductive Morpheme
  /-- A verb root. -/
  | root
  /-- The historic-tense exponent ((18)). -/
  | hist
  /-- The past-tense impersonal exponent (§6.2). -/
  | pstImpers
  deriving DecidableEq, Repr

/-- A form of the paper, sponsored by its morphemes. -/
abbrev Form := Autosegmental.Form CVSlot Autosegment Morpheme

/-- *bog* 'move', consonant-initial (Figure 1a). -/
def bog : Form :=
  .melody .root [.seg .b, .seg .o, .seg .g] [.C, .V, .C, .V] {(0, 0), (1, 1), (2, 2)}

/-- *ól* 'drink', vowel-initial: its first C-slot is empty (Figure 1b). -/
def ól : Form := .melody .root [.seg .ó, .seg .l] [.C, .V, .C, .V] {(0, 1), (1, 2)}

/-- *fág* 'leave', *f*-initial (Figure 1c). -/
def fág : Form :=
  .melody .root [.seg .f, .seg .á, .seg .g] [.C, .V, .C, .V] {(0, 0), (1, 1), (2, 2)}

/-- Each historic-tense form of Figure 1 has exactly one surface form. -/
theorem card_surfaces_historic :
    ∀ s ∈ [bog, ól, fág], (surfaces (.input (historic Morpheme.hist * s))).card = 1 := by
  decide

/-- In Figure 1a, *bog* → *bhog*, `{L}` docks on *b*, which fills the C-slot, so `d` cannot link
((11c)). -/
theorem historic_bog : ∀ c ∈ surfaces (.input (historic Morpheme.hist * bog)),
    c.IsFloating (d bog) ∧ c.IsLinked (L bog) := by
  decide

/-- In Figure 1b, *ól* → *d' ól*, the C-slot is empty, so `{L}` finds nothing to dock on and `d`
links ((11a)). -/
theorem historic_ól : ∀ c ∈ surfaces (.input (historic Morpheme.hist * ól)),
    c.IsLinked (d ól) ∧ c.IsFloating (L ól) := by
  decide

/-- In Figure 1c, *fág* → *d' fhág*, `{L}` deletes the *f*, leaving its C-slot empty, and `d`
links ((11b)). -/
theorem historic_fág : ∀ c ∈ surfaces (.input (historic Morpheme.hist * fág)),
    c.IsLinked (d fág) ∧ c.IsLinked (L fág) ∧ ⟨2, by decide⟩ ∈ c.deleted := by
  decide

/-- Lenition feeds the linking of `d` before *fág*, since `d` cannot link until `{L}` has deleted
the *f* (§4.2). -/
theorem lenition_feeds_linking : Feeds (fun k c ↦ dock c k) (fun k c ↦ CanDock c k) (L fág) (d fág)
    (.input (historic Morpheme.hist * fág)) := by
  decide

/-- The linking of `d` does not feed lenition before *ól*, since `{L}` never acts on `d`, which
precedes it on the melodic tier; the form is *d' ól*, not *dh' ól* (§4.2). -/
theorem not_linking_feeds_lenition : ¬ Feeds (fun k c ↦ dock c k) (fun k c ↦ CanDock c k)
    (d ól) (L ól) (.input (historic Morpheme.hist * ól)) := by
  decide

/-- In Figure 5 the past-tense impersonals *bogadh*, *óladh* and *fágadh* are neither lenited
nor preceded by *d'* ((27)). -/
theorem historic_pstImpers : ∀ s ∈ [bog, ól, fág],
    ∀ c ∈ surfaces (.input (historic Morpheme.hist * (emptyCV Morpheme.pstImpers * s))),
      c.IsFloating (d _) ∧ c.IsFloating (L _) :=
  fun _ _ _ hc ↦ isFloating_of_emptyCV (mem_surfaces.1 hc).1

end LaoideKemp2026
