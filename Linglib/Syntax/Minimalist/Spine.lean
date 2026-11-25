/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.ExtendedProjection
public import Linglib.Syntax.Spine.Label

/-!
# Spines of extended projections

A spine of categories is an extended projection in Grimshaw's sense when each head extends the
one below it. Keine observes that category features project bilaterally within an extended
projection, so the label of a spine is the set of heads it projects. A functional head inherits
the categories of its complement, and a lexical head starts an extended projection of its own.
The extended projection at the top of a spine is what its heads project in turn, from the bottom
up.

## Main definitions

* `Spine.IsExtendedProjection`: a spine each of whose heads extends the one below it.
* `Spine.Inherits`, `Spine.project`: category inheritance, and the spine of the phrase a head
  projects over a complement.
* `Spine.extendedProjection`: the extended projection at the top of a spine.
* `Spine.vP`, `Spine.tP`, `Spine.cP`: the clause sizes of the verbal extended projection.

## Main results

* `Spine.IsExtendedProjection.pairwise`: in an extended projection every head extends each head
  below it.
* `Spine.IsExtendedProjection.project`: projecting a head over an extended projection gives one.

## References

* [grimshaw-2005]
* [keine-2020]
* [deal-2026]
-/

@[expose] public section

namespace Spine

open Minimalist

variable {s t : Spine Cat} {c d : Cat} {l : List Cat}

/-! ### Extended projections -/

/-- A spine is an extended projection when each head extends the one below it, so that its heads
are of one family. -/
def IsExtendedProjection (s : Spine Cat) : Prop := s.heads.IsChain Cat.ExtendsTo

instance (s : Spine Cat) : Decidable s.IsExtendedProjection :=
  inferInstanceAs (Decidable (List.IsChain _ _))

/-- In an extended projection every head extends each head below it. -/
theorem IsExtendedProjection.pairwise (h : s.IsExtendedProjection) :
    s.heads.Pairwise Cat.ExtendsTo :=
  List.isChain_iff_pairwise.1 h

/-- In an extended projection a head lies in the complement of another or extends it. -/
theorem IsExtendedProjection.mem_below_or_extendsTo (hs : s.IsExtendedProjection) (hc : c ∈ s)
    (hd : d ∈ s) : d ∈ s.below c ∨ c.ExtendsTo d :=
  mem_below_or_rel hs.pairwise hc hd

/-- In an extended projection a head extends every head in its complement. -/
theorem IsExtendedProjection.extendsTo_of_mem_below (hs : s.IsExtendedProjection) (hc : c ∈ s)
    (hd : d ∈ s.below c) : d.ExtendsTo c :=
  rel_of_mem_below hs.pairwise hc hd

/-! ### Category inheritance -/

/-- A head of category `c` inherits the categories of a complement with spine `s` when it is
functional and the highest head of `s` extends to it; a lexical head starts an extended projection
of its own. -/
def Inherits (s : Spine Cat) (c : Cat) : Prop :=
  c ≠ c.family.lexical ∧ ∃ d ∈ s.heads.getLast?, d.ExtendsTo c

instance : Decidable (s.Inherits c) := inferInstanceAs (Decidable (_ ∧ _))

/-- The spine of the phrase a head of category `c` projects over a complement with spine `s`: the
complement's heads, where the head inherits them, and `c`. -/
def project (s : Spine Cat) (c : Cat) : Spine Cat :=
  ⟨(if s.Inherits c then s.heads else []) ++ [c]⟩

theorem mem_project_self (s : Spine Cat) (c : Cat) : c ∈ s.project c := by simp [project]

theorem le_project (h : s.Inherits c) : s ≤ s.project c :=
  le_iff_forall_mem.2 fun d hd ↦ by simp [project, h, mem_def.1 hd]

/-- The complement of a head in the phrase it projects over a complement it inherits from is that
complement. -/
theorem below_project (hi : s.Inherits c) (hc : c ∉ s) : (s.project c).below c = s := by
  have h : s.heads.takeWhile (· != c) = s.heads :=
    List.takeWhile_eq_self_iff.2 fun x hx ↦ bne_iff_ne.2 fun hxc ↦ hc (hxc ▸ hx)
  cases s
  simp only [below, project, hi, ite_true, List.takeWhile_append, mk.injEq] at h ⊢
  simp [h]

theorem IsExtendedProjection.project (hs : s.IsExtendedProjection) (c : Cat) :
    (s.project c).IsExtendedProjection := by
  unfold Spine.project IsExtendedProjection
  split
  next h =>
    obtain ⟨d, hd, hdc⟩ := h.2
    exact hs.append (.singleton _) fun e he b hb ↦ by
      obtain rfl : e = d := Option.some.inj (he.symm.trans hd)
      obtain rfl : _ = b := by simpa using hb
      exact hdc
  next => exact .singleton _

/-! ### The extended projection at the top of a spine -/

/-- The extended projection at the top of a spine: each head in turn, from the bottom up, projects
over the heads below it that it inherits. -/
def extendedProjection (s : Spine Cat) : Spine Cat := s.heads.foldl project ⟨[]⟩

@[simp] theorem extendedProjection_nil : (⟨[]⟩ : Spine Cat).extendedProjection = ⟨[]⟩ := rfl

@[simp] theorem extendedProjection_mk_append_singleton (l : List Cat) (c : Cat) :
    (⟨l ++ [c]⟩ : Spine Cat).extendedProjection = (⟨l⟩ : Spine Cat).extendedProjection.project c := by
  simp [extendedProjection]

theorem extendedProjection_append_singleton (s : Spine Cat) (c : Cat) :
    (s.append [c]).extendedProjection = s.extendedProjection.project c :=
  extendedProjection_mk_append_singleton s.heads c

theorem isExtendedProjection_extendedProjection (s : Spine Cat) :
    s.extendedProjection.IsExtendedProjection := by
  obtain ⟨l⟩ := s
  induction l using List.reverseRecOn with
  | nil => exact .nil
  | append_singleton l c ih => simpa using ih.project c

/-! ### Clause sizes -/

/-- The vP-sized clause `[V, v]`, the small nonfinite clause. -/
def vP : Spine Cat := ⟨[.V, .v]⟩

/-- The TP-sized clause `[V, v, T]`, the large nonfinite clause. -/
def tP : Spine Cat := ⟨[.V, .v, .T]⟩

/-- The CP-sized clause `[V, v, T, C]`, the finite clause. -/
def cP : Spine Cat := ⟨[.V, .v, .T, .C]⟩

@[simp] theorem tP_below_T : tP.below .T = vP := by decide

@[simp] theorem cP_below_T : cP.below .T = vP := by decide

@[simp] theorem cP_below_C : cP.below .C = tP := by decide

theorem vP_le_tP : vP ≤ tP := by decide

theorem tP_le_cP : tP ≤ cP := by decide

theorem cP_isExtendedProjection : cP.IsExtendedProjection := by decide +kernel

end Spine
