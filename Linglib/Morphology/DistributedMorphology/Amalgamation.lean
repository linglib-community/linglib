/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.DistributedMorphology.MorphosyntacticWord
public import Linglib.Syntax.Spine.Occurrence
public import Linglib.Core.Data.List.Sublist
public import Mathlib.Data.List.Pairwise

/-!
# Amalgamation

Amalgamation forms morphosyntactic words after the syntax, in the account of Harizanov and
Gribanova, from the heads of an extended projection listed bottom-up. A
head specified [M:+] Raises: it adjoins to the next head up. A head specified [M:−] Lowers: it
adjoins to the nearest head below. A complex takes on the feature of the head it has adjoined to,
and may amalgamateAux again. The heads are considered from the bottom of the spine up, and a
derivation in which a feature demands an operation that has no target does not converge.

## Main definitions

All in the namespace `DistributedMorphology`.

* `Amalgamation.Direction`, `Amalgamation.Terminal`: the [M] feature and a head bearing it.
* `amalgamate`: the words amalgamation forms on a spine.
* `Amalgamation.moveToRoot`: a second occurrence of a head at the top of the spine, left by
  syntactic movement before amalgamation.
* `Amalgamation.PronouncedFrom`: after Chain Reduction, the word containing a head is pronounced at
  the lowest occurrence of another head or above it.

## Main results

* `flatMap_heads_amalgamate`: the words partition the spine in order.
* `heads_infix_of_mem_amalgamate`: every word is a contiguous stretch of the spine.
* `site_mem_heads_of_mem_amalgamate`: every word is pronounced at one of its own heads.
* `isContiguous_hosts_of_amalgamate`: on a spine without repeated heads, the hosting of
  amalgamation is contiguous.
* `site_eq_of_amalgamate_append`: heads added above a spine do not change where the words formed
  below are pronounced.
* `amalgamate_raising_lowering`: with the heads below a position Raising and the heads above it
  Lowering, the spine is one word pronounced there.

## Implementation notes

Within this file `MWd`, Embick and Noyer's abbreviation, stands for
`DistributedMorphology.MorphosyntacticWord`.

## References

* [harizanov-gribanova-2019]
* [embick-noyer-2001]
-/

@[expose] public section

namespace DistributedMorphology

@[inherit_doc] local notation "MWd" => MorphosyntacticWord

open FreeMagma

namespace Amalgamation

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
  /-- The [M] feature, absent on a head that does not amalgamateAux. -/
  m : Option Direction
  deriving DecidableEq, Repr

end Amalgamation

open Amalgamation

variable {H : Type*}

/-- Bottom-up amalgamation. `below` lists the complex heads already formed, nearest first,
`pending` is the complex head that has Raised and awaits the next head up, and `above` lists the
heads still to be considered, lowest first. A Raising head adjoins to the next head up, whose
[M] feature the complex takes on, a Lowering head adjoins to the nearest complex head below, and
a demanded operation with no target is a derivation that does not converge. -/
def amalgamateAux : List (MWd H) → Option (FreeMagma H) → List (Terminal H) →
    Option (List (MWd H))
  | below, none, [] => some below
  | _, some _, [] => none
  | below, pending, a :: above =>
    let complex := pending.elim (of a.head) (· * of a.head)
    match a.m, below with
    | none, below => amalgamateAux (⟨a.head, complex⟩ :: below) none above
    | some .raising, below => amalgamateAux below (some complex) above
    | some .lowering, [] => none
    | some .lowering, b :: below =>
      amalgamateAux (⟨b.site, b.bracketing * complex⟩ :: below) none above

/-- The complex heads that amalgamation forms on a spine, lowest first, or `none` when the
postsyntactic derivation does not converge. -/
def amalgamate (spine : Spine (Terminal H)) : Option (List (MWd H)) :=
  (amalgamateAux [] none spine.heads).map List.reverse

/-- Syntactic movement of the head `y` to the root, which precedes amalgamation, gives `y` a
second occurrence at the top of the spine. -/
def Amalgamation.moveToRoot (spine : Spine (Terminal H)) (y : H) : Spine (Terminal H) :=
  spine.append [⟨y, none⟩]

private theorem flatMap_heads_amalgamateAux {below : List (MWd H)}
    {pending : Option (FreeMagma H)} {above : List (Terminal H)} {out : List (MWd H)}
    (h : amalgamateAux below pending above = some out) :
    out.reverse.flatMap MorphosyntacticWord.heads =
      below.reverse.flatMap MorphosyntacticWord.heads ++
        pending.elim [] (fun x ↦ (toFreeSemigroup x).toFreeMonoid.toList) ++
        above.map (·.head) := by
  induction above generalizing below pending out with
  | nil => cases pending <;> simp_all [amalgamateAux]
  | cons a above ih =>
    rcases ha : a.m with _ | _ | _ <;> cases below <;> cases pending <;>
      simp only [amalgamateAux, ha] at h <;>
      first | simpa [List.append_assoc, MorphosyntacticWord.heads] using ih h | simp at h

/-- The complex heads partition the spine in the order of syntactic composition: the affixes of
a complex head mirror that order, and no head gains or loses an occurrence. -/
theorem flatMap_heads_amalgamate {spine : Spine (Terminal H)} {out : List (MWd H)}
    (h : amalgamate spine = some out) :
    out.flatMap MorphosyntacticWord.heads = (spine.map (·.head)).heads := by
  obtain ⟨out', h', rfl⟩ := Option.map_eq_some_iff.mp h
  simpa using flatMap_heads_amalgamateAux h'

theorem heads_infix_of_mem_amalgamate {spine : Spine (Terminal H)} {out : List (MWd H)}
    (h : amalgamate spine = some out) {a : MWd H} (ha : a ∈ out) :
    a.heads <:+: (spine.map (·.head)).heads :=
  flatMap_heads_amalgamate h ▸ List.infix_of_mem_flatten (List.mem_map_of_mem ha)

theorem mem_of_mem_amalgamate_of_nodup [DecidableEq H] {spine : Spine (Terminal H)}
    {out : List (MWd H)} (h : amalgamate spine = some out)
    (hnd : (spine.map (·.head)).heads.Nodup) {a : MWd H} (ha : a ∈ out) {x y z : H}
    (hx : x ∈ a.heads) (hy : y ∈ a.heads) (hz : z ∈ (spine.map (·.head)).heads)
    (hxz : (spine.map (·.head)).heads.idxOf x ≤ (spine.map (·.head)).heads.idxOf z)
    (hzy : (spine.map (·.head)).heads.idxOf z ≤ (spine.map (·.head)).heads.idxOf y) :
    z ∈ a.heads :=
  (heads_infix_of_mem_amalgamate h ha).mem_of_idxOf_le_of_le hnd hx hy hz hxz hzy

theorem amalgamateAux_append {below : List (MWd H)} {pending : Option (FreeMagma H)}
    {above : List (Terminal H)} {out : List (MWd H)} (extra : List (Terminal H))
    (h : amalgamateAux below pending above = some out) :
    amalgamateAux below pending (above ++ extra) = amalgamateAux out none extra := by
  induction above generalizing below pending out with
  | nil => cases pending <;> simp_all [amalgamateAux]
  | cons a above ih =>
    rcases ha : a.m with _ | _ | _ <;> cases below <;>
      simp only [List.cons_append, amalgamateAux, ha] at h ⊢ <;> first | exact ih h | simp at h

theorem amalgamate_moveToRoot {spine : Spine (Terminal H)} {out : List (MWd H)} (y : H)
    (h : amalgamate spine = some out) :
    amalgamate (moveToRoot spine y) = some (out ++ [⟨y, of y⟩]) := by
  obtain ⟨out', h', rfl⟩ := Option.map_eq_some_iff.mp h
  rw [amalgamate, moveToRoot, Spine.heads_append, amalgamateAux_append _ h']
  cases out' <;> simp [amalgamateAux]

private theorem exists_site_eq_of_amalgamateAux {below : List (MWd H)}
    {pending : Option (FreeMagma H)} {extra : List (Terminal H)} {res : List (MWd H)}
    (h : amalgamateAux below pending extra = some res) {b : MWd H} (hb : b ∈ below) :
    ∃ r ∈ res, r.site = b.site ∧ b.heads <+: r.heads := by
  induction extra generalizing below pending res b with
  | nil =>
    cases pending with
    | none =>
      obtain rfl : below = res := by simpa [amalgamateAux] using h
      exact ⟨b, hb, rfl, List.prefix_rfl⟩
    | some _ => simp [amalgamateAux] at h
  | cons a extra ih =>
    rcases below with _ | ⟨b₀, bs⟩
    · simp at hb
    rcases ha : a.m with _ | _ | _ <;> simp only [amalgamateAux, ha] at h
    · exact ih h (List.mem_cons_of_mem _ hb)
    · exact ih h hb
    · rcases List.mem_cons.mp hb with rfl | hb
      · obtain ⟨r, hr, hs, hm⟩ := ih h (List.mem_cons_self ..)
        exact ⟨r, hr, hs, (List.prefix_append _ _).trans
          (by simpa [MorphosyntacticWord.heads] using hm)⟩
      · exact ih h (List.mem_cons_of_mem _ hb)

theorem exists_site_eq_of_amalgamate_append {spine : Spine (Terminal H)} {extra : List (Terminal H)}
    {out out' : List (MWd H)}
    (h : amalgamate spine = some out) (h' : amalgamate (spine.append extra) = some out')
    {a : MWd H} (ha : a ∈ out) : ∃ a' ∈ out', a'.site = a.site ∧ a.heads <+: a'.heads := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h'
  rw [Spine.heads_append, amalgamateAux_append extra hr] at hr'
  simpa using exists_site_eq_of_amalgamateAux hr' (List.mem_reverse.mp ha)

theorem site_eq_of_amalgamate_append {spine : Spine (Terminal H)} {extra : List (Terminal H)}
    {out out' : List (MWd H)}
    (h : amalgamate spine = some out) (h' : amalgamate (spine.append extra) = some out')
    (hnd : ((spine.append extra).map (·.head)).heads.Nodup) {a a' : MWd H} (ha : a ∈ out)
    (ha' : a' ∈ out') {x : H} (hx : x ∈ a.heads) (hx' : x ∈ a'.heads) : a'.site = a.site := by
  obtain ⟨b, hb, hs, hm⟩ := exists_site_eq_of_amalgamate_append h h' ha
  rw [← flatMap_heads_amalgamate h', List.nodup_flatMap] at hnd
  by_contra hne
  have : Std.Symm (Function.onFun List.Disjoint (MorphosyntacticWord.heads (H := H))) :=
    ⟨fun _ _ hd _ h₁ h₂ ↦ hd h₂ h₁⟩
  exact hnd.2.forall hb ha' (fun hba ↦ hne (hba ▸ hs)) (hm.subset hx) hx'

private theorem amalgamateAux_raising (below : List (MWd H)) (pending : Option (FreeMagma H))
    (lo : List H) (above : List (Terminal H)) :
    amalgamateAux below pending (lo.map (Terminal.mk · (some .raising)) ++ above) =
      amalgamateAux below (lo.foldl (fun p h ↦ some (p.elim (of h) (· * of h))) pending) above := by
  induction lo generalizing pending with
  | nil => rfl
  | cons h lo ih => cases below <;> simpa [amalgamateAux] using ih _

private theorem amalgamateAux_none (below : List (MWd H)) (pending : Option (FreeMagma H))
    (s : H) (above : List (Terminal H)) :
    amalgamateAux below pending (⟨s, none⟩ :: above) =
      amalgamateAux (⟨s, pending.elim (of s) (· * of s)⟩ :: below) none above := by
  cases pending <;> cases below <;> rfl

private theorem amalgamateAux_lowering (b : MWd H) (below : List (MWd H)) (hi : List H) :
    amalgamateAux (b :: below) none (hi.map (Terminal.mk · (some .lowering))) =
      some (⟨b.site, hi.foldl (· * of ·) b.bracketing⟩ :: below) := by
  induction hi generalizing b with
  | nil => rfl
  | cons h hi ih => simpa [amalgamateAux] using ih _

private theorem foldl_raising (p : FreeMagma H) (lo : List H) :
    lo.foldl (fun p h ↦ some (p.elim (of h) (· * of h))) (some p) =
      some (lo.foldl (· * of ·) p) := by
  induction lo generalizing p with
  | nil => rfl
  | cons h lo ih => simpa using ih _

/-- The complex head of a spine can sit at any of its heads. With the heads below Raising and
the heads above Lowering, all the heads form one complex head there, each added to the complex
head of the heads below it. -/
theorem amalgamate_raising_lowering {lo hi rest : List H} {s b : H}
    (h : lo ++ s :: hi = b :: rest) :
    amalgamate ⟨lo.map (Terminal.mk · (some .raising)) ++ ⟨s, none⟩ ::
        hi.map (Terminal.mk · (some .lowering))⟩ =
      some [⟨s, rest.foldl (· * of ·) (of b)⟩] := by
  rw [amalgamate, amalgamateAux_raising, amalgamateAux_none, amalgamateAux_lowering]
  cases lo with
  | nil =>
    obtain ⟨rfl, rfl⟩ : s = b ∧ hi = rest := by simpa using h
    rfl
  | cons l lo =>
    obtain ⟨rfl, rfl⟩ : l = b ∧ lo ++ s :: hi = rest := by simpa using h
    simp [foldl_raising]

private theorem site_mem_heads_of_amalgamateAux {below : List (MWd H)}
    {pending : Option (FreeMagma H)} {above : List (Terminal H)}
    {out : List (MWd H)} (h : amalgamateAux below pending above = some out)
    (hb : ∀ b ∈ below, b.site ∈ b.heads) : ∀ a ∈ out, a.site ∈ a.heads := by
  induction above generalizing below pending out with
  | nil => cases pending <;> simp_all [amalgamateAux]
  | cons a above ih =>
    rcases ha : a.m with _ | _ | _ <;> rcases below with _ | ⟨b, below⟩ <;> cases pending <;>
      simp only [amalgamateAux, ha] at h <;>
      first | exact ih h (by simp_all [MorphosyntacticWord.heads]) | simp at h

/-- Every word of amalgamation is pronounced at one of its own heads. -/
theorem site_mem_heads_of_mem_amalgamate {spine : Spine (Terminal H)}
    {out : List (MWd H)} (h : amalgamate spine = some out)
    {a : MWd H} (ha : a ∈ out) : a.site ∈ a.heads := by
  obtain ⟨out', h', rfl⟩ := Option.map_eq_some_iff.mp h
  exact site_mem_heads_of_amalgamateAux h' (by simp) a (List.mem_reverse.mp ha)

/-- On a spine without repeated heads, the hosting of amalgamation is contiguous. -/
theorem isContiguous_hosts_of_amalgamate {spine : Spine (Terminal H)}
    {out : List (MWd H)} (h : amalgamate spine = some out)
    (hnd : (spine.map (·.head)).heads.Nodup) : IsContiguous (MorphosyntacticWord.hosts out).get :=
  MorphosyntacticWord.isContiguous_hosts (fun _ ha ↦ site_mem_heads_of_mem_amalgamate h ha)
    (flatMap_heads_amalgamate h ▸ hnd)

theorem length_hosts_of_amalgamate {spine : Spine (Terminal H)}
    {out : List (MWd H)} (h : amalgamate spine = some out) :
    (MorphosyntacticWord.hosts out).length = spine.heads.length := by
  rw [MorphosyntacticWord.length_hosts, flatMap_heads_amalgamate h, Spine.heads_map,
    List.length_map]

/-- A complex head belongs to the head it is formed at, in all of that head's occurrences, and
Chain Reduction pronounces the highest of them, `Spine.highest`. `PronouncedFrom ts h x` says
that the complex head containing `h` is thereby pronounced at the lowest occurrence of `x` or
above it. -/
def Amalgamation.PronouncedFrom [DecidableEq H] (ts : Spine (Terminal H)) (h x : H) : Prop :=
  ∃ out ∈ amalgamate ts, ∃ a ∈ out, h ∈ a.heads ∧
    ∃ p ∈ (ts.map Terminal.head).highest a.site, ∃ q ∈ (ts.map Terminal.head).lowest x, q ≤ p

instance [DecidableEq H] (ts : Spine (Terminal H)) (h x : H) :
    Decidable (PronouncedFrom ts h x) :=
  inferInstanceAs (Decidable (∃ out ∈ amalgamate ts, _))

end DistributedMorphology
