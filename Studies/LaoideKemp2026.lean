/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Relation.ReflTransGen
public import Linglib.Phonology.Autosegmental.Skeleton
public import Linglib.Phonology.Autosegmental.Melody
public import Linglib.Phonology.RuleInteraction
public import Linglib.Phonology.StrictCV.Skeleton
public import Mathlib.Tactic.DeriveFintype

/-!
# Laoide-Kemp (2026): Strict modularity at the morphosyntax-phonology interface

Laoide-Kemp analyses the Irish historic-tense particle *d'*, which appears before vowel-initial
and lenited *f*-initial verbs but not before other consonants ((11)). Its exponent is a floating
`d` followed by the lenition-inducing bundle `{L}` on the melodic tier, inserted in every
environment over a strict-CV skeleton ((18)). A floating object docks on the slot immediately to
its right when that slot suits it: `{L}` on a consonant, deleting the segmental content of an *f*,
and `d` on a segmentally empty C-slot before a filled V-slot. These processes apply whenever their
conditions are met (§4.2), and an empty CV unit at the left edge of a word, her representation of
the past-tense impersonal, blocks both (§6.2). The rival morphosyntactic analysis of §5 spells
out `{L}` as a prefix and *d'* afterwards; it fails on the past-tense impersonals.

## Main definitions

* `floating`, `historic`, `lenition`: an exponent of floating material, the historic-tense marker
  `(d){L}`, and the bundle `{L}` alone.
* `CanDock`, `dock`: when and how a floating object docks.
* `Step`, `IsSurface`, `surfaces`: one docking, a candidate where none applies, and the surface
  forms a candidate derives; `Realizes`, an object linked on the surface.

## Main results

* `surfaces_nonempty`: every candidate derives a surface form.
* `historic_bog`, `historic_ól`, `historic_fág`: in the one surface form of each form of
  Figure 1, `d` is pronounced before *ól* and *fág* but not before *bog*.
* `lenition_feeds_linking`, `not_linking_feeds_lenition`: lenition feeds the linking of `d` and
  not conversely, so the order of the two processes is intrinsic.
* `historic_freagair`, `historic_rith`: `d` links before lenited *fr-*, whose emptied C-slot stays
  in a domain of infrasegmental government, and not before *r-* (Figure 2).
* `isFloating_of_emptyCV`: whatever the stem, no object of a floating exponent docks before an
  empty CV unit; `conditional_impersonals`, the same resistance after the trigger *má*.
* `beginsWithEmptyC_iff_realizes_d`, `beginsWithEmptyC_pstImpers`, `beginsWithEmptyC_of_emptyCV`:
  the morphosyntactic analysis agrees on (11) and inserts *d'* before a past-tense impersonal.
* `munster_iff_historic`: in Munster the floating `d` after a particle has the same distribution.
* `prothesis`: a floating consonant without `{L}` links before a vowel-initial word only.

## Implementation notes

The segments are written orthographically, as in the paper's CV diagrams. The words of Figure 1
are given in full and the others by their first CV unit, as Figure 2 draws *rith*. The slot
immediately to the right of a melodic object is the first slot after every slot linked to an
object before it, the left edge of its window under the No-Crossing Constraint (`leftIndices`).
Once `d` is linked, the slot to the right of `{L}` is the following V-slot, so `{L}` never acts on
`d`, the consequence of melodic order that §4.2 draws. `{L}` docking is a line from `{L}` to the
slot of the consonant it acts on, and of its effects only the deletion of *f* is modelled, which
leaves the C-slot, as Gussmann argues. The palatalization such a slot keeps, a lexical property of
the following word as Ní Chiosáin shows, is not modelled. The condition on `d` applies to every
floating segment, as §4.3 extends it to the prothetic consonants; of the masculine article only
its floating `t` is modelled. Whether a nucleus is enclosed in a domain of infrasegmental
government is Strict CV's notion, after Scheer; the domains are read off the underlying form,
since "the IG domain structure remains intact, even after the initial f has been deleted", and a
liquid may govern an obstruent before it. The phonology is defined for any type of sponsoring
morpheme, so it cannot consult the morphosyntax, which is Bermúdez-Otero's strict modularity.
Suffixes are not modelled, and Munster *dh'* is written `d`, as the paper writes it.

## TODO

Prove the distribution of `d` for every stem, not only for the paper's verbs.

## References

* [laoide-kemp-2026]
* [bermudez-otero-2012]
* [lowenstamm-1996]
* [gussmann-1986]
* [ni-chiosain-1991]
* [scheer-1998]
* [scheer-2004]
-/

@[expose] public section

namespace LaoideKemp2026

open Autosegmental Relation RuleInteraction
open scoped Finset

/-! ### Representations -/

/-- The segments of the paper's examples, written orthographically as in its CV diagrams. -/
inductive Segment
  | a | á | b | d | ea | f | g | i | í | l | m | n | o | ó | r | t
  deriving DecidableEq, Repr, Fintype

/-- An object of the melodic tier is a segment or the lenition-inducing bundle `{L}`, whose
content the paper leaves open. -/
inductive Autosegment
  /-- A segment. -/
  | seg (s : Segment)
  /-- The lenition-inducing bundle `{L}`. -/
  | L
  deriving DecidableEq, Repr

/-- The segments, as against the bundle `{L}`. -/
def Autosegment.IsSegment : Autosegment → Prop
  | .seg _ => True
  | .L => False

instance : DecidablePred Autosegment.IsSegment
  | .seg _ => isTrue trivial
  | .L => isFalse id

theorem Autosegment.isSegment_iff {a : Autosegment} : a.IsSegment ↔ ∃ s, a = .seg s := by
  cases a <;> simp [Autosegment.IsSegment]

/-- A liquid may govern an obstruent before it, as in the clusters *fr-* and *fl-* of (12) and
*dr-* and *gl-* of §4.1, where the governing onset hosts *r* or *l* and the governed one an
obstruent. -/
def MayGovern (governor governee : List Autosegment) : Prop :=
  (.seg .r ∈ governor ∨ .seg .l ∈ governor) ∧ ∃ s ∈ [Segment.b, .d, .f, .g, .t], .seg s ∈ governee

instance (governor governee : List Autosegment) : Decidable (MayGovern governor governee) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A form of the paper is a melodic tier of `Autosegment`s over a strict-CV skeleton, each object
and slot sponsored by a morpheme in `M`. -/
abbrev Form (M : Type*) := Autosegmental.Form Slot Autosegment M

section Exponents

variable {M : Type*} (m : M)

/-- An exponent of floating material has objects on the melodic tier and no skeleton. -/
abbrev floating (objs : List Autosegment) : Form M :=
  .melody m objs [] ∅

/-- The historic-tense marker ((18)) is a floating `d` followed by `{L}`. -/
abbrev historic : Form M := floating m [.seg .d, .L]

/-- The bundle `{L}` alone, at the right edge of a trigger word ((3)) or as the historic-tense
prefix of the morphosyntactic analysis ((22)). -/
abbrev lenition : Form M := floating m [.L]

/-- A prothetic consonant is a floating segment with no `{L}` (§4.3). -/
abbrev prothetic (s : Segment) : Form M := floating m [.seg s]

/-- An empty CV unit, the left edge of a word that resists mutation (§6.2). -/
def emptyCV : Form M := .melody m [] [.C, .V] ∅

variable {m} (s : Form M)

/-- The floating `d` of a historic-tense form. -/
def d : Fin (historic m * s).upper.length := ⟨0, by simp⟩

/-- The bundle `{L}` of a historic-tense form. -/
def bundle : Fin (historic m * s).upper.length := ⟨1, by simp⟩

end Exponents

/-! ### Docking -/

section Docking

variable {M : Type*} {u : Form M} (c : Candidate u)

/-- Slot `i` hosts a segment on the surface. -/
def HostsSegment (i : Fin u.lower.length) : Prop :=
  ∃ k s, (k, i) ∈ c.links ∧ u.upper[k].value = .seg s

instance (i : Fin u.lower.length) : Decidable (HostsSegment c i) :=
  inferInstanceAs (Decidable (∃ _ _, _ ∧ _))

/-- The slot immediately to the right of object `k` is the first slot after every slot linked to
an object before it. -/
def nextSlot (k : Fin u.upper.length) : Option (Fin u.lower.length) :=
  Fin.find? fun i ↦ ∀ j ∈ leftIndices c.links k, j < i

variable (u) in
/-- The units whose onsets contract infrasegmental government are those of the form itself, a
structure that "remains intact, even after the initial f has been deleted" (§4.1). -/
def domains : Finset (Fin (StrictCV.units u)) := StrictCV.clusters (.input u) MayGovern

/-- A docking site for `{L}` is a C-slot hosting the consonant it acts on, and for a segment a
segmentally empty C-slot whose nucleus hosts a segment or is enclosed in a domain of
infrasegmental government (§4.1). -/
def IsDockingSite : Autosegment → Fin u.lower.length → Prop
  | .L, i => u.lower[i].value = .C ∧ HostsSegment c i
  | .seg _, i => u.lower[i].value = .C ∧ ¬ HostsSegment c i ∧
      ∃ j, StrictCV.onset u j = i ∧ (HostsSegment c (StrictCV.nucleus u j) ∨
        StrictCV.Enclosed (StrictCV.nucleusOf c Autosegment.IsSegment (domains u) j)
          ((StrictCV.surface c Autosegment.IsSegment (domains u)).drop (j + 1)))

instance : ∀ a i, Decidable (IsDockingSite c a i)
  | .L, _ => inferInstanceAs (Decidable (_ ∧ _))
  | .seg _, _ => inferInstanceAs (Decidable (_ ∧ _ ∧ ∃ _, _))

variable {c} in
theorem IsDockingSite.isC {i : Fin u.lower.length} : ∀ {a}, IsDockingSite c a i →
    u.lower[i].value = .C
  | .L, h | .seg _, h => h.1

/-- Object `k` can dock when it is floating and the slot immediately to its right is a docking
site for it. -/
def CanDock (k : Fin u.upper.length) : Prop :=
  c.IsFloating k ∧ ∃ i ∈ nextSlot c k, IsDockingSite c u.upper[k].value i

instance (k : Fin u.upper.length) : Decidable (CanDock c k) :=
  inferInstanceAs (Decidable (_ ∧ ∃ _ ∈ _, _))

/-- The *f* on slot `i`, whose segmental content `{L}` deletes (§2.2). -/
def fOn (i : Fin u.lower.length) : Option (Fin u.upper.length) :=
  (c.linksTo i).find? (u.upper[·].value = .seg .f)

/-- Object `k` docks on the slot immediately to its right; `{L}` docking on an *f* deletes its
segmental content and leaves the slot. -/
def dock (k : Fin u.upper.length) : Candidate u :=
  match nextSlot c k with
  | some i =>
    if u.upper[k].value = .L then
      (fOn c i).elim (c.insertLink k i) (c.insertLink k i).deleteTierElem
    else c.insertLink k i
  | none => c

/-- A step docks one floating object where it can. -/
inductive Step : Candidate u → Candidate u → Prop
  | dock {c : Candidate u} {k : Fin u.upper.length} :
      CanDock c k → Step c (LaoideKemp2026.dock c k)

/-- A surface form is a candidate where no object can dock. -/
def IsSurface : Prop := ∀ k, ¬ CanDock c k

instance : Decidable (IsSurface c) := inferInstanceAs (Decidable (∀ _, _))

/-- A candidate realizes `a` when an object of value `a` is linked on the surface; a floating
object is not pronounced. -/
def Realizes (a : Autosegment) : Prop := ∃ k, u.upper[k].value = a ∧ c.IsLinked k

instance (a : Autosegment) : Decidable (Realizes c a) := inferInstanceAs (Decidable (∃ _, _ ∧ _))

/-- A candidate begins with an empty consonantal slot, the context in which the morphosyntactic
analysis spells out the historic-tense particle as *d* ((23)). -/
def BeginsWithEmptyC : Prop :=
  ∃ i : Fin u.lower.length, i.val = 0 ∧ u.lower[i].value = .C ∧ ¬ HostsSegment c i

instance : Decidable (BeginsWithEmptyC c) := inferInstanceAs (Decidable (∃ _, _ ∧ _ ∧ _))

variable {c} {c' : Candidate u} {k j : Fin u.upper.length}

theorem mem_links_of_fOn_eq_some {i : Fin u.lower.length} (h : fOn c i = some j) :
    (j, i) ∈ c.links :=
  Candidate.mem_linksTo.1 (List.mem_of_find?_eq_some h)

theorem isSurface_iff_forall_not_step : IsSurface c ↔ ∀ c', ¬ Step c c' :=
  ⟨fun h _ hs ↦ by cases hs with | dock hk => exact h _ hk, fun h _ hk ↦ h _ (.dock hk)⟩

theorem isFloating_dock (hk : CanDock c k) : (dock c k).IsFloating j ↔ j ≠ k ∧ c.IsFloating j := by
  obtain ⟨-, i, hi : nextSlot c k = some i, -⟩ := hk
  simp only [dock, hi]
  split_ifs
  · rcases hf : fOn c i with _ | j'
    · exact Candidate.isFloating_insertLink
    have hj' : ¬ c.IsFloating j' :=
      fun h ↦ h.2 (Candidate.isLinked_iff.2 ⟨_, mem_links_of_fOn_eq_some hf⟩)
    simp only [Option.elim, Candidate.isFloating_deleteTierElem, Candidate.isFloating_insertLink]
    exact ⟨fun h ↦ h.2, fun ⟨hjk, hj⟩ ↦ ⟨fun he ↦ hj' (he ▸ hj), hjk, hj⟩⟩
  · exact Candidate.isFloating_insertLink

theorem links_dock_subset {i : Fin u.lower.length} (hi : nextSlot c k = some i) :
    (dock c k).links ⊆ insert (k, i) c.links := by
  simp only [dock, hi]
  split_ifs
  · rcases fOn c i with _ | j'
    exacts [Finset.Subset.refl _, Candidate.links_deleteTierElem_subset]
  · exact Finset.Subset.refl _

theorem val_eq_zero_of_mem_nextSlot (h : leftIndices c.links k = ∅) {i : Fin u.lower.length}
    (hi : i ∈ nextSlot c k) : i.val = 0 := by
  by_contra h0
  have := (Fin.find?_eq_some_iff.1 hi).2 ⟨0, by omega⟩ (Fin.lt_def.2 (by simp only; omega))
  simp [h] at this

variable (c) in
/-- The number of floating objects. -/
def floatingCount : ℕ := #{k | c.IsFloating k}

theorem Step.floatingCount_lt (h : Step c c') : floatingCount c' < floatingCount c := by
  obtain ⟨hk⟩ := h
  refine Finset.card_lt_card <| (Finset.ssubset_iff_of_subset fun j hj ↦ ?_).2
    ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, hk.1⟩, fun h ↦ ?_⟩
  · exact Finset.mem_filter.2
      ⟨Finset.mem_univ _, ((isFloating_dock hk).1 (Finset.mem_filter.1 hj).2).2⟩
  · exact ((isFloating_dock hk).1 (Finset.mem_filter.1 h).2).1 rfl

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

theorem wellFounded_flip_step : WellFounded (flip (Step (u := u))) :=
  Subrelation.wf (fun h ↦ h.floatingCount_lt) (InvImage.wf floatingCount wellFounded_lt)

variable (c) in
/-- Every candidate derives a surface form. -/
theorem surfaces_nonempty : (surfaces c).Nonempty := by
  obtain ⟨b, hb, hmin⟩ := wellFounded_flip_step.has_min {b | ReflTransGen Step c b} ⟨c, .refl⟩
  exact ⟨b, mem_surfaces.2 ⟨hb, isSurface_iff_forall_not_step.2 fun b' h ↦ hmin b' (hb.tail h) h⟩⟩

end Docking

/-! ### The empty CV unit

An empty CV unit is no docking site for anything: `{L}` finds no consonant on its C-slot, and a
segment finds its V-slot empty. So no object of a floating exponent ever docks before it, and the
same structure blocks both lenition and the linking of `d` (§6.2). -/

section EmptyCV

variable {M : Type*} {u : Form M} {c : Candidate u}

theorem not_isDockingSite_onset {j : Fin (StrictCV.units u)}
    (hc : ¬ HostsSegment c (StrictCV.onset u j)) (hv : ¬ HostsSegment c (StrictCV.nucleus u j))
    (hcl : j ∉ domains u) :
    ∀ a, ¬ IsDockingSite c a (StrictCV.onset u j)
  | .L, h => hc h.2
  | .seg _, ⟨_, _, j', hj', h⟩ => by
    obtain rfl : j' = j := Fin.ext (by
      have := congrArg Fin.val hj'
      simp only [StrictCV.onset] at this
      omega)
    rcases h with h | h
    · exact hv h
    · exact hcl (by simpa [StrictCV.nucleusOf] using h.cluster_eq_true)

variable {m m' : M} {objs : List Autosegment} {s : Form M}
  {c c' : Candidate (floating m objs * (emptyCV m' * s))}

private theorem le_of_mem_links {p} (hp : p ∈ (floating m objs * (emptyCV m' * s)).links) :
    objs.length ≤ p.1.val ∧ 2 ≤ p.2.val := by
  rcases Form.mem_links_concat.1 hp with ⟨q, hq, -⟩ | ⟨q, hq, h₁, h₂⟩
  · exact absurd (Form.mem_links_melody.1 hq) (Finset.notMem_empty _)
  rcases Form.mem_links_concat.1 hq with ⟨r, hr, -⟩ | ⟨r, hr, h₃, h₄⟩
  · exact absurd (Form.mem_links_melody.1 hr) (Finset.notMem_empty _)
  simp only [floating, emptyCV, Form.melody_upper, Form.melody_lower, List.length_map,
    List.length_cons, List.length_nil] at h₁ h₂ h₄
  omega

private theorem zero_notMem_domains
    (h0 : 0 < StrictCV.units (floating m objs * (emptyCV m' * s))) :
    (⟨0, h0⟩ : Fin _) ∉ domains (floating m objs * (emptyCV m' * s)) := by
  simp only [domains, StrictCV.clusters, Finset.mem_filter, Finset.mem_univ, true_and, not_exists,
    not_and]
  rintro k - ⟨-, s', -, hs'⟩
  obtain ⟨k', hk', -⟩ := Candidate.mem_tierValues.1 hs'
  have := (le_of_mem_links hk').2
  simp [StrictCV.onset] at this

/-- Before an empty CV unit, the objects of a floating exponent float and the unit hosts no
segment. -/
private def Blocked (c : Candidate (floating m objs * (emptyCV m' * s))) : Prop :=
  (∀ k : Fin _, k.val < objs.length → c.IsFloating k) ∧
    ∀ i : Fin _, i.val < 2 → ¬ HostsSegment c i

private theorem leftIndices_eq_empty (h : Blocked c) {k : Fin _} (hk : k.val < objs.length) :
    leftIndices c.links k = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun x hx ↦ ?_
  obtain ⟨n, hn, hnx⟩ := mem_leftIndices.1 hx
  exact (h.1 n (by have := Fin.lt_def.1 hn; omega)).2 (Candidate.isLinked_iff.2 ⟨_, hnx⟩)

private theorem le_of_canDock (h : Blocked c) {k : Fin _} (hk : CanDock c k) :
    objs.length ≤ k.val ∧ ∀ i ∈ nextSlot c k, 2 ≤ i.val := by
  have hlen : 1 < (floating m objs * (emptyCV m' * s)).lower.length := by simp [emptyCV]
  obtain ⟨-, i, hi, hs⟩ := hk
  have hi0 : i.val ≠ 0 := fun h0 ↦ by
    have hu : 0 < StrictCV.units (floating m objs * (emptyCV m' * s)) := by
      simp only [StrictCV.units, Form.mul_eq_concat, Form.concat_lower, floating, emptyCV,
        Form.melody_lower, List.map_nil, List.map_cons, List.nil_append, List.length_cons,
        List.cons_append]
      omega
    obtain rfl : i = StrictCV.onset _ ⟨0, hu⟩ := Fin.ext (by simp [StrictCV.onset, h0])
    exact not_isDockingSite_onset (h.2 _ (by simp only [StrictCV.onset]; omega))
      (h.2 _ (by simp only [StrictCV.nucleus]; omega)) (zero_notMem_domains hu) _ hs
  have hi1 : i.val ≠ 1 := fun h1 ↦ by
    obtain rfl : i = ⟨1, hlen⟩ := Fin.ext h1
    nomatch hs.isC
  refine ⟨Nat.le_of_not_lt fun hk2 ↦ hi0 ?_, fun i' hi' ↦ ?_⟩
  · exact val_eq_zero_of_mem_nextSlot (leftIndices_eq_empty h hk2) hi
  · obtain rfl := Option.mem_unique hi hi'
    omega

private theorem blocked_input : Blocked (.input (floating m objs * (emptyCV m' * s))) := by
  refine ⟨fun k hk ↦ ⟨Finset.notMem_empty _, ?_⟩, ?_⟩
  · rintro ⟨p, hp, rfl⟩
    exact absurd (le_of_mem_links hp).1 (by omega)
  · rintro i hi ⟨k, -, hk, -⟩
    have := (le_of_mem_links hk).2
    dsimp only at this
    omega

private theorem Blocked.step (h : Blocked c) (hs : Step c c') : Blocked c' := by
  obtain ⟨hk⟩ := hs
  obtain ⟨hk2, hi2⟩ := le_of_canDock h hk
  obtain ⟨i, hi, -⟩ := hk.2
  have hsub := links_dock_subset hi
  have hi2 := hi2 i hi
  refine ⟨fun j hj ↦ (isFloating_dock hk).2 ⟨fun he ↦ ?_, h.1 j hj⟩,
    fun i₀ hi₀ ⟨k', s', hk', hval⟩ ↦ ?_⟩
  · rw [he] at hj
    omega
  · rcases Finset.mem_insert.1 (hsub hk') with he | he
    · have := congrArg (·.2.val) he
      simp only at this
      omega
    · exact h.2 i₀ hi₀ ⟨k', s', he, hval⟩

private theorem blocked (hc : ReflTransGen Step (.input _) c) : Blocked c := by
  induction hc with
  | refl => exact blocked_input
  | tail _ hs ih => exact ih.step hs

/-- Whatever the stem, no object of a floating exponent docks before an empty CV unit, in any
candidate derived (§6.2). -/
theorem isFloating_of_emptyCV (hc : ReflTransGen Step (.input _) c) {k : Fin _}
    (hk : k.val < objs.length) : c.IsFloating k :=
  (blocked hc).1 k hk

theorem not_hostsSegment_of_emptyCV (hc : ReflTransGen Step (.input _) c) {i : Fin _}
    (hi : i.val < 2) : ¬ HostsSegment c i :=
  (blocked hc).2 i hi

/-- Whatever the stem, a form that begins with an empty CV unit begins with an empty consonantal
slot in every candidate derived, so under the morphosyntactic analysis it would take *d'*. -/
theorem beginsWithEmptyC_of_emptyCV (hc : ReflTransGen Step (.input _) c) : BeginsWithEmptyC c :=
  ⟨⟨0, by simp [emptyCV]⟩, rfl, rfl, not_hostsSegment_of_emptyCV hc (by simp)⟩

end EmptyCV

/-! ### The forms -/

/-- The morphemes that sponsor the paper's forms. -/
inductive Morpheme
  /-- A verb or noun root. -/
  | root
  /-- The historic-tense exponent ((18)). -/
  | hist
  /-- The past-tense impersonal exponent (§6.2). -/
  | pstImpers
  /-- The negative particle *ní*. -/
  | neg
  /-- The conditional particle *má*. -/
  | cond
  /-- The masculine definite article *an*. -/
  | art
  deriving DecidableEq, Repr

/-- *bog* 'move', consonant-initial (Figure 1a). -/
def bog : Form Morpheme :=
  .melody .root [.seg .b, .seg .o, .seg .g] [.C, .V, .C, .V] {(0, 0), (1, 1), (2, 2)}

/-- The vowel-initial *ól* 'drink', whose first C-slot is empty (Figure 1b). -/
def ól : Form Morpheme := .melody .root [.seg .ó, .seg .l] [.C, .V, .C, .V] {(0, 1), (1, 2)}

/-- *fág* 'leave', *f*-initial (Figure 1c). -/
def fág : Form Morpheme :=
  .melody .root [.seg .f, .seg .á, .seg .g] [.C, .V, .C, .V] {(0, 0), (1, 1), (2, 2)}

/-- *freagair* 'answer', with the initial cluster *fr-* (Figure 2b). -/
def freagair : Form Morpheme :=
  .melody .root [.seg .f, .seg .r, .seg .ea] [.C, .V, .C, .V] {(0, 0), (1, 2), (2, 3)}

/-- *rith* 'run', *r*-initial (Figure 2a). -/
def rith : Form Morpheme := .melody .root [.seg .r, .seg .i] [.C, .V] {(0, 0), (1, 1)}

/-- *imigh* 'go away', vowel-initial (Table 2). -/
def imigh : Form Morpheme := .melody .root [.seg .i] [.C, .V] {(0, 1)}

/-- *fás* 'grow', *f*-initial (Table 2). -/
def fás : Form Morpheme := .melody .root [.seg .f, .seg .á] [.C, .V] {(0, 0), (1, 1)}

/-- *fan* 'stay', *f*-initial (Table 2). -/
def fan : Form Morpheme := .melody .root [.seg .f, .seg .a] [.C, .V] {(0, 0), (1, 1)}

/-- *athair* 'father', vowel-initial ((19)). -/
def athair : Form Morpheme := .melody .root [.seg .a] [.C, .V] {(0, 1)}

/-- *fear* 'man', *f*-initial (fn. 10). -/
def fear : Form Morpheme := .melody .root [.seg .f, .seg .ea] [.C, .V] {(0, 0), (1, 1)}

/-- A particle whose consonant and vowel fill one CV unit. -/
def particle (m : Morpheme) (consonant vowel : Segment) : Form Morpheme :=
  .melody m [.seg consonant, .seg vowel] [.C, .V] {(0, 0), (1, 1)}

/-- The negative particle *ní*, with `{L}` at its right edge ((3)). -/
def ní : Form Morpheme := particle .neg .n .í * lenition Morpheme.neg

/-- The conditional particle *má*, with `{L}` at its right edge ((26)). -/
def má : Form Morpheme := particle .cond .m .á * lenition Morpheme.cond

/-- Munster *ní*, where the floating `d` accompanies `{L}` (Table 3). -/
def níMunster : Form Morpheme := particle .neg .n .í * historic Morpheme.neg

/-- Munster *má*, where the floating `d` accompanies `{L}` (Table 3). -/
def máMunster : Form Morpheme := particle .cond .m .á * historic Morpheme.cond

/-! ### Figure 1 -/

/-- Each historic-tense form of Figure 1 has exactly one surface form. -/
theorem card_surfaces_historic :
    ∀ s ∈ [bog, ól, fág], (surfaces (.input (historic Morpheme.hist * s))).card = 1 := by
  decide

/-- In Figure 1a, *bog* → *bhog*, `{L}` docks on *b*, which fills the C-slot, so `d` cannot link
((11c)). -/
theorem historic_bog : ∀ c ∈ surfaces (.input (historic Morpheme.hist * bog)),
    ¬ Realizes c (.seg .d) ∧ Realizes c .L := by
  decide

/-- In Figure 1b, *ól* → *d' ól*, the C-slot is empty, so `{L}` finds nothing to dock on and `d`
links ((11a)). -/
theorem historic_ól : ∀ c ∈ surfaces (.input (historic Morpheme.hist * ól)),
    Realizes c (.seg .d) ∧ ¬ Realizes c .L := by
  decide

/-- In Figure 1c, *fág* → *d' fhág*, `{L}` deletes the *f*, leaving its C-slot empty, and `d`
links ((11b)). -/
theorem historic_fág : ∀ c ∈ surfaces (.input (historic Morpheme.hist * fág)),
    Realizes c (.seg .d) ∧ Realizes c .L ∧ ¬ Realizes c (.seg .f) := by
  decide

/-- Lenition feeds the linking of `d` before *fág*, since `d` cannot link until `{L}` has deleted
the *f* (§4.2). -/
theorem lenition_feeds_linking : Feeds (fun k c ↦ dock c k) (fun k c ↦ CanDock c k)
    (bundle fág) (d fág) (.input (historic Morpheme.hist * fág)) := by
  decide

/-- The linking of `d` does not feed lenition before *ól*, since `{L}` never acts on `d`, which
precedes it on the melodic tier; the form is *d' ól*, not *dh' ól* (§4.2). -/
theorem not_linking_feeds_lenition : ¬ Feeds (fun k c ↦ dock c k) (fun k c ↦ CanDock c k)
    (d ól) (bundle ól) (.input (historic Morpheme.hist * ól)) := by
  decide

/-! ### Figure 2 -/

/-- In Figure 2b, *freagair* → *d' fhreagair*, `{L}` deletes the *f*, and `d` links to the
emptied C-slot, which an empty V-slot follows but which stays in the domain of infrasegmental
government that *r* contracts with it ((12b)). -/
theorem historic_freagair : ∀ c ∈ surfaces (.input (historic Morpheme.hist * freagair)),
    Realizes c (.seg .d) ∧ Realizes c .L ∧ ¬ Realizes c (.seg .f) := by
  decide

/-- In Figure 2a, *rith* → *rith*, `{L}` docks on the *r*, which fills the C-slot, so `d` cannot
link ((13b)). Both forms begin with *r* on the surface, and only the one derived from an
*f*-initial verb has *d'* (§3). -/
theorem historic_rith : ∀ c ∈ surfaces (.input (historic Morpheme.hist * rith)),
    ¬ Realizes c (.seg .d) ∧ Realizes c .L := by
  decide

/-- The forms of Figures 1, 2 and 5 are strict CV forms. -/
theorem isStrict_forms : ∀ s ∈ [bog, ól, fág, freagair, rith],
    StrictCV.IsStrict (historic Morpheme.hist * s) ∧
      StrictCV.IsStrict (historic Morpheme.hist * (emptyCV Morpheme.pstImpers * s)) := by
  decide

/-! ### Figure 5 and the past-tense impersonal -/

/-- In Figure 5 the past-tense impersonals *bogadh*, *óladh* and *fágadh* are neither lenited
nor preceded by *d'* ((27)). -/
theorem historic_pstImpers : ∀ s ∈ [bog, ól, fág],
    ∀ c ∈ surfaces (.input (historic Morpheme.hist * (emptyCV Morpheme.pstImpers * s))),
      c.IsFloating (d _) ∧ c.IsFloating (bundle _) :=
  fun _ _ _ hc ↦ ⟨isFloating_of_emptyCV (mem_surfaces.1 hc).1 (by simp [d]),
    isFloating_of_emptyCV (mem_surfaces.1 hc).1 (by simp [bundle])⟩

/-- After the conditional particle a present-tense impersonal is lenited, *má bhogtar*, and a
past-tense one is not, *má bogadh*. The past-tense impersonal resists lenition from any source,
not only that of historic tense ((26), §6.2). -/
theorem conditional_impersonals : (∀ c ∈ surfaces (.input (má * bog)), Realizes c .L) ∧
    ∀ c ∈ surfaces (.input (má * (emptyCV Morpheme.pstImpers * bog))), ¬ Realizes c .L := by
  decide

/-! ### The morphosyntactic analysis (§5)

The alternative spells out `{L}` as a prefix on the verb ((22)) and, once the verb has been
processed, the historic-tense particle as *d* before an empty consonantal slot and as nothing
elsewhere ((23)). -/

/-- On the verbs of (11) the two analyses agree. Processed with the prefix `{L}`, a verb begins
with an empty consonantal slot exactly where the historic-tense marker's `d` is pronounced
(§5.2). -/
theorem beginsWithEmptyC_iff_realizes_d : ∀ v ∈ [bog, ól, fág],
    (∀ c ∈ surfaces (.input (lenition Morpheme.hist * v)), BeginsWithEmptyC c) ↔
      ∀ c ∈ surfaces (.input (historic Morpheme.hist * v)), Realizes c (.seg .d) := by
  decide

/-- The morphosyntactic analysis predicts *d'* before the vowel-initial past-tense impersonal
alone, since such a verb resists lenition, and unlenited only a vowel-initial verb begins with an
empty consonantal slot. (27) has *d'* before none of them (§6.2). With the empty CV unit instead,
every past-tense impersonal would take *d'* (`beginsWithEmptyC_of_emptyCV`). -/
theorem beginsWithEmptyC_pstImpers : BeginsWithEmptyC (.input ól) ∧
    ¬ BeginsWithEmptyC (.input fág) ∧ ¬ BeginsWithEmptyC (.input bog) := by
  decide

/-! ### Munster (§6.1) -/

/-- In Munster the floating `d` accompanies `{L}` after a lenition-triggering particle and is
pronounced exactly where it is after the historic-tense marker, before a vowel-initial or
lenited *f*-initial verb (Table 3). -/
theorem munster_iff_historic : ∀ v ∈ [bog, ól, fág],
    (∀ c ∈ surfaces (.input (níMunster * v)), Realizes c (.seg .d)) ↔
      ∀ c ∈ surfaces (.input (historic Morpheme.hist * v)), Realizes c (.seg .d) := by
  decide

/-- In Table 2, Standard *ní fhásann* lenites without *d'*, and Munster has *dh' imigh*,
*ní dh' fhásann* and *má dh' fhanann*. -/
theorem table2 : (∀ c ∈ surfaces (.input (ní * fás)), ¬ Realizes c (.seg .d) ∧ Realizes c .L) ∧
    (∀ c ∈ surfaces (.input (historic Morpheme.hist * imigh)), Realizes c (.seg .d)) ∧
    (∀ c ∈ surfaces (.input (níMunster * fás)), Realizes c (.seg .d) ∧ Realizes c .L) ∧
    ∀ c ∈ surfaces (.input (máMunster * fan)), Realizes c (.seg .d) ∧ Realizes c .L := by
  decide

/-! ### Prothesis (§4.3) -/

/-- Without `{L}`, a floating consonant links before a vowel-initial word but not before an
*f*-initial one, giving *an t-athair* but *an fear*, not *an t-fear*. After the historic-tense
marker an *f*-initial verb patterns with a vowel-initial one (`historic_fág`), since `{L}` deletes
the *f*. Radical *f* patterns with consonants and mutated *f* with vowels (fn. 10). -/
theorem prothesis :
    (∀ c ∈ surfaces (.input (prothetic Morpheme.art .t * athair)), Realizes c (.seg .t)) ∧
      ∀ c ∈ surfaces (.input (prothetic Morpheme.art .t * fear)), ¬ Realizes c (.seg .t) := by
  decide

end LaoideKemp2026
