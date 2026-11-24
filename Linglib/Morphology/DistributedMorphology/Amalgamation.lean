/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.DistributedMorphology.MorphosyntacticWord
public import Linglib.Core.Data.List.Sublist
public import Mathlib.Data.List.Pairwise

/-!
# Amalgamation

Amalgamation forms morphosyntactic words after the syntax, in the account of Harizanov and
Gribanova, from the heads of an extended projection listed bottom-up. A
head specified [M:+] Raises: it adjoins to the next head up. A head specified [M:−] Lowers: it
adjoins to the nearest head below. A complex takes on the feature of the head it has adjoined to,
and may amalgamate again. The heads are considered from the bottom of the spine up, and a
derivation in which a feature demands an operation that has no target does not converge.

## Main definitions

* `DistributedMorphology.Amalgamation.Direction`, `Terminal`: the [M] feature and a head bearing
  it.
* `DistributedMorphology.Amalgamation.amalgamateSpine`: the words amalgamation forms on a spine.
* `DistributedMorphology.Amalgamation.moveToRoot`: a second occurrence of a head at the top of
  the spine, left by syntactic movement before amalgamation.
* `DistributedMorphology.Amalgamation.PronouncedFrom`: the word containing a head is pronounced at
  a position or above.

## Main results

* `DistributedMorphology.Amalgamation.flatMap_heads_amalgamateSpine`: the words partition the
  spine in order.
* `DistributedMorphology.Amalgamation.heads_infix_of_mem_amalgamateSpine`: every word is a
  contiguous stretch of the spine.
* `DistributedMorphology.Amalgamation.site_eq_of_append`: heads added above a spine do not change
  where the words formed below are pronounced.
* `DistributedMorphology.Amalgamation.amalgamateSpine_raising_lowering`: with the heads below a
  position Raising and the heads above it Lowering, the spine is one word pronounced there.

## Implementation notes

Within this file `MWd`, Embick and Noyer's abbreviation, stands for
`DistributedMorphology.MorphosyntacticWord`.

## References

* [harizanov-gribanova-2019]
* [embick-noyer-2001]
-/

@[expose] public section

namespace DistributedMorphology.Amalgamation

@[inherit_doc] local notation "MWd" => MorphosyntacticWord

open FreeMagma

/-- The direction of amalgamation that the [M] feature of a head demands. A head with [M:+]
Raises into the next head up and a head with [M:−] Lowers into the nearest head below. -/
inductive Direction
  | raising | lowering
  deriving DecidableEq, Repr

variable {H : Type*}

/-- A head of the spine with the [M] feature its lexical item is specified for. -/
structure Terminal (H : Type*) where
  /-- The head. -/
  head : H
  /-- The [M] feature, absent on a head that does not amalgamate. -/
  m : Option Direction
  deriving DecidableEq, Repr

/-- Bottom-up amalgamation. `below` lists the complex heads already formed, nearest first,
`pending` is the complex head that has Raised and awaits the next head up, and `above` lists the
heads still to be considered, lowest first. A Raising head adjoins to the next head up, whose
[M] feature the complex takes on, a Lowering head adjoins to the nearest complex head below, and
a demanded operation with no target is a derivation that does not converge. -/
def amalgamate : List (MWd H) → Option (FreeMagma H) → List (Terminal H) →
    Option (List (MWd H))
  | below, none, [] => some below
  | _, some _, [] => none
  | below, pending, a :: above =>
    let complex := pending.elim (of a.head) (· * of a.head)
    match a.m, below with
    | none, below => amalgamate (⟨a.head, complex⟩ :: below) none above
    | some .raising, below => amalgamate below (some complex) above
    | some .lowering, [] => none
    | some .lowering, b :: below =>
      amalgamate (⟨b.site, b.bracketing * complex⟩ :: below) none above

/-- The complex heads that amalgamation forms on a spine, lowest first, or `none` when the
postsyntactic derivation does not converge. -/
def amalgamateSpine (spine : List (Terminal H)) : Option (List (MWd H)) :=
  (amalgamate [] none spine).map List.reverse

/-- Syntactic movement of the head `y` to the root, which precedes amalgamation, gives `y` a
second occurrence at the top of the spine. -/
def moveToRoot (spine : List (Terminal H)) (y : H) : List (Terminal H) := spine ++ [⟨y, none⟩]

private theorem flatMap_heads_amalgamate {below : List (MWd H)}
    {pending : Option (FreeMagma H)} {above : List (Terminal H)} {out : List (MWd H)}
    (h : amalgamate below pending above = some out) :
    out.reverse.flatMap MorphosyntacticWord.heads =
      below.reverse.flatMap MorphosyntacticWord.heads ++
        pending.elim [] (fun x ↦ (toFreeSemigroup x).toFreeMonoid.toList) ++
        above.map (·.head) := by
  induction above generalizing below pending out with
  | nil => cases pending <;> simp_all [amalgamate]
  | cons a above ih =>
    rcases ha : a.m with _ | _ | _ <;> cases below <;> cases pending <;>
      simp only [amalgamate, ha] at h <;>
      first | simpa [List.append_assoc, MorphosyntacticWord.heads] using ih h | simp at h

/-- The complex heads partition the spine in the order of syntactic composition: the affixes of
a complex head mirror that order, and no head gains or loses an occurrence. -/
theorem flatMap_heads_amalgamateSpine {spine : List (Terminal H)} {out : List (MWd H)}
    (h : amalgamateSpine spine = some out) :
    out.flatMap MorphosyntacticWord.heads = spine.map (·.head) := by
  obtain ⟨out', h', rfl⟩ := Option.map_eq_some_iff.mp h
  simpa using flatMap_heads_amalgamate h'

theorem heads_infix_of_mem_amalgamateSpine {spine : List (Terminal H)} {out : List (MWd H)}
    (h : amalgamateSpine spine = some out) {a : MWd H} (ha : a ∈ out) :
    a.heads <:+: spine.map (·.head) :=
  flatMap_heads_amalgamateSpine h ▸ List.infix_of_mem_flatten (List.mem_map_of_mem ha)

theorem mem_of_mem_amalgamateSpine_of_nodup [DecidableEq H] {spine : List (Terminal H)}
    {out : List (MWd H)} (h : amalgamateSpine spine = some out)
    (hnd : (spine.map (·.head)).Nodup) {a : MWd H} (ha : a ∈ out) {x y z : H}
    (hx : x ∈ a.heads) (hy : y ∈ a.heads) (hz : z ∈ spine.map (·.head))
    (hxz : (spine.map (·.head)).idxOf x ≤ (spine.map (·.head)).idxOf z)
    (hzy : (spine.map (·.head)).idxOf z ≤ (spine.map (·.head)).idxOf y) :
    z ∈ a.heads :=
  (heads_infix_of_mem_amalgamateSpine h ha).mem_of_idxOf_le_of_le hnd hx hy hz hxz hzy

theorem amalgamate_append {below : List (MWd H)} {pending : Option (FreeMagma H)}
    {above : List (Terminal H)} {out : List (MWd H)} (extra : List (Terminal H))
    (h : amalgamate below pending above = some out) :
    amalgamate below pending (above ++ extra) = amalgamate out none extra := by
  induction above generalizing below pending out with
  | nil => cases pending <;> simp_all [amalgamate]
  | cons a above ih =>
    rcases ha : a.m with _ | _ | _ <;> cases below <;>
      simp only [List.cons_append, amalgamate, ha] at h ⊢ <;> first | exact ih h | simp at h

theorem amalgamateSpine_moveToRoot {spine : List (Terminal H)} {out : List (MWd H)} (y : H)
    (h : amalgamateSpine spine = some out) :
    amalgamateSpine (moveToRoot spine y) = some (out ++ [⟨y, of y⟩]) := by
  obtain ⟨out', h', rfl⟩ := Option.map_eq_some_iff.mp h
  rw [amalgamateSpine, moveToRoot, amalgamate_append _ h']
  cases out' <;> simp [amalgamate]

private theorem exists_site_eq_of_amalgamate {below : List (MWd H)}
    {pending : Option (FreeMagma H)} {extra : List (Terminal H)} {res : List (MWd H)}
    (h : amalgamate below pending extra = some res) {b : MWd H} (hb : b ∈ below) :
    ∃ r ∈ res, r.site = b.site ∧ b.heads <+: r.heads := by
  induction extra generalizing below pending res b with
  | nil =>
    cases pending with
    | none =>
      obtain rfl : below = res := by simpa [amalgamate] using h
      exact ⟨b, hb, rfl, List.prefix_rfl⟩
    | some _ => simp [amalgamate] at h
  | cons a extra ih =>
    rcases below with _ | ⟨b₀, bs⟩
    · simp at hb
    rcases ha : a.m with _ | _ | _ <;> simp only [amalgamate, ha] at h
    · exact ih h (List.mem_cons_of_mem _ hb)
    · exact ih h hb
    · rcases List.mem_cons.mp hb with rfl | hb
      · obtain ⟨r, hr, hs, hm⟩ := ih h (List.mem_cons_self ..)
        exact ⟨r, hr, hs, (List.prefix_append _ _).trans
          (by simpa [MorphosyntacticWord.heads] using hm)⟩
      · exact ih h (List.mem_cons_of_mem _ hb)

theorem exists_site_eq_of_append {spine extra : List (Terminal H)} {out out' : List (MWd H)}
    (h : amalgamateSpine spine = some out) (h' : amalgamateSpine (spine ++ extra) = some out')
    {a : MWd H} (ha : a ∈ out) : ∃ a' ∈ out', a'.site = a.site ∧ a.heads <+: a'.heads := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h'
  rw [amalgamate_append extra hr] at hr'
  simpa using exists_site_eq_of_amalgamate hr' (List.mem_reverse.mp ha)

theorem site_eq_of_append {spine extra : List (Terminal H)} {out out' : List (MWd H)}
    (h : amalgamateSpine spine = some out) (h' : amalgamateSpine (spine ++ extra) = some out')
    (hnd : ((spine ++ extra).map (·.head)).Nodup) {a a' : MWd H} (ha : a ∈ out)
    (ha' : a' ∈ out') {x : H} (hx : x ∈ a.heads) (hx' : x ∈ a'.heads) : a'.site = a.site := by
  obtain ⟨b, hb, hs, hm⟩ := exists_site_eq_of_append h h' ha
  rw [← flatMap_heads_amalgamateSpine h', List.nodup_flatMap] at hnd
  by_contra hne
  have : Std.Symm (Function.onFun List.Disjoint (MorphosyntacticWord.heads (H := H))) :=
    ⟨fun _ _ hd _ h₁ h₂ ↦ hd h₂ h₁⟩
  exact hnd.2.forall hb ha' (fun hba ↦ hne (hba ▸ hs)) (hm.subset hx) hx'

private theorem amalgamate_raising (below : List (MWd H)) (pending : Option (FreeMagma H))
    (lo : List H) (above : List (Terminal H)) :
    amalgamate below pending (lo.map (Terminal.mk · (some .raising)) ++ above) =
      amalgamate below (lo.foldl (fun p h ↦ some (p.elim (of h) (· * of h))) pending) above := by
  induction lo generalizing pending with
  | nil => rfl
  | cons h lo ih => cases below <;> simpa [amalgamate] using ih _

private theorem amalgamate_none (below : List (MWd H)) (pending : Option (FreeMagma H))
    (s : H) (above : List (Terminal H)) :
    amalgamate below pending (⟨s, none⟩ :: above) =
      amalgamate (⟨s, pending.elim (of s) (· * of s)⟩ :: below) none above := by
  cases pending <;> cases below <;> rfl

private theorem amalgamate_lowering (b : MWd H) (below : List (MWd H)) (hi : List H) :
    amalgamate (b :: below) none (hi.map (Terminal.mk · (some .lowering))) =
      some (⟨b.site, hi.foldl (· * of ·) b.bracketing⟩ :: below) := by
  induction hi generalizing b with
  | nil => rfl
  | cons h hi ih => simpa [amalgamate] using ih _

private theorem foldl_raising (p : FreeMagma H) (lo : List H) :
    lo.foldl (fun p h ↦ some (p.elim (of h) (· * of h))) (some p) =
      some (lo.foldl (· * of ·) p) := by
  induction lo generalizing p with
  | nil => rfl
  | cons h lo ih => simpa using ih _

/-- The complex head of a spine can sit at any of its heads. With the heads below Raising and
the heads above Lowering, all the heads form one complex head there, each added to the complex
head of the heads below it. -/
theorem amalgamateSpine_raising_lowering {lo hi rest : List H} {s b : H}
    (h : lo ++ s :: hi = b :: rest) :
    amalgamateSpine (lo.map (Terminal.mk · (some .raising)) ++ ⟨s, none⟩ ::
        hi.map (Terminal.mk · (some .lowering))) =
      some [⟨s, rest.foldl (· * of ·) (of b)⟩] := by
  rw [amalgamateSpine, amalgamate_raising, amalgamate_none, amalgamate_lowering]
  cases lo with
  | nil =>
    obtain ⟨rfl, rfl⟩ : s = b ∧ hi = rest := by simpa using h
    rfl
  | cons l lo =>
    obtain ⟨rfl, rfl⟩ : l = b ∧ lo ++ s :: hi = rest := by simpa using h
    simp [foldl_raising]

/-- Chain Reduction pronounces the highest occurrence of a head, and a complex head formed at
one occurrence of a moved head belongs to all of them. `PronouncedFrom spine h x` says that the
complex head containing `h` is thereby pronounced in the position of `x` or above it. -/
def PronouncedFrom [DecidableEq H] (spine : List (Terminal H)) (h x : H) : Prop :=
  ∃ out ∈ amalgamateSpine spine, ∃ a ∈ out,
    h ∈ a.heads ∧ a.site ∈ (spine.map (·.head)).dropWhile (· ≠ x)

instance [DecidableEq H] (spine : List (Terminal H)) (h x : H) :
    Decidable (PronouncedFrom spine h x) :=
  inferInstanceAs (Decidable (∃ out ∈ amalgamateSpine spine, _))

end DistributedMorphology.Amalgamation
