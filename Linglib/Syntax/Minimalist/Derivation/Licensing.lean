/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Label.Head
public import Linglib.Syntax.Minimalist.Derivation.Replay

/-!
# Licensing a derivation

A licensing of Merge, a morphism of magmas from the syntactic objects into a magma with zero,
judges an object, `0` being the failure of Merge. A derivation is licensed, `Derivation.LicensedBy`,
when every stage is in the licensing's domain, the object under construction and every copy
extracted from it. A licensing that judges only the derived object misses what its stages held: a
moved item leaves a trace, so whether it was merged before it was saturated shows only at the
stages before it moved. Stages are read off the replay, so licensing decides, and [licensing at a
stage is licensing of the derivation's own
stage](##Minimalist.Derivation.LicensedAt.map_stageAt_ne_zero). A licensing reads the derivation
with its own heads: a moved phrase leaves the trace of the item the licensing takes to head it.
Two licensings related by a morphism that preserves zero and heads read a derivation the coarser
one licenses alike, so [the finer one licenses it too](##Minimalist.Derivation.LicensedBy.of_comp).

## Implementation notes

* The zero of the target absorbs, so that a licensing licenses the terms of what it licenses; the
  raising states of `Label/RaisingHead.lean`, whose zero does not, are not such a target.
-/

@[expose] public section

namespace Minimalist.Derivation

variable {β : Type*} [MulZeroClass β] [Head β] (φ : SyntacticObject →ₙ* β) {d : Derivation}
  {n : ℕ}

omit [Head β] in
/-- A licensing licenses the terms of an object it licenses. -/
theorem _root_.Minimalist.SyntacticObject.map_ne_zero_of_mem_terms {x y : SyntacticObject}
    (h : y ∈ x.terms) (hx : φ x ≠ 0) : φ y ≠ 0 := by
  induction x using SyntacticObject.ind with
  | leaf a | trace | traceOf a => exact Multiset.mem_singleton.1 h ▸ hx
  | merge l r ihl ihr =>
    rw [SyntacticObject.terms_merge, Multiset.mem_cons, Multiset.mem_add] at h
    have hlr := ne_zero_and_ne_zero_of_mul (show φ l * φ r ≠ 0 from map_mul φ l r ▸ hx)
    rcases h with rfl | h | h
    exacts [hx, ihl h hlr.1, ihr h hlr.2]

/-- `φ` licenses stage `n` of `d`: the ordered configuration the replay reaches after `n` steps,
its movers leaving the traces of their heads under `φ`, is in its domain, the object and every
copy on the stack. -/
def LicensedAt (d : Derivation) (n : ℕ) : Prop :=
  ∃ c ∈ (d.take n).replay? (head ∘ φ), ∀ x ∈ c.current :: c.stack, φ x.toSyntacticObject ≠ 0

instance [DecidableEq β] (d : Derivation) (n : ℕ) : Decidable (d.LicensedAt φ n) :=
  inferInstanceAs (Decidable (∃ c ∈ (d.take n).replay? (head ∘ φ), _))

/-- The stage licensing looks at is the derivation's own. -/
theorem LicensedAt.map_stageAt_ne_zero (h : d.LicensedAt φ n) :
    φ (d.stageAt n (head ∘ φ)) ≠ 0 := by
  obtain ⟨c, hc, hall⟩ := h
  rw [stageAt, final, ← (d.take n).replay?_faithful hc, Cfg.map_current]
  exact hall c.current List.mem_cons_self

/-- `φ` licenses `d` when it licenses every stage. -/
def LicensedBy (d : Derivation) : Prop := ∀ n ≤ d.length, d.LicensedAt φ n

instance [DecidableEq β] (d : Derivation) : Decidable (d.LicensedBy φ) :=
  inferInstanceAs (Decidable (∀ n ≤ d.length, _))

/-! ### Comparing licensings -/

variable {γ : Type*} [MulZeroClass γ] [Head γ] (π : β →ₙ* γ)

/-- Through the stages that `π.comp φ` licenses, `φ` and `π.comp φ` replay a derivation alike when
`π` preserves the heads of what it does not send to zero. -/
theorem replay?_take_comp (hπ : ∀ x, π x ≠ 0 → head (π x) = head x) :
    ∀ n ≤ d.length, (∀ k < n, d.LicensedAt (π.comp φ) k) →
      (d.take n).replay? (head ∘ φ) = (d.take n).replay? (head ∘ π.comp φ)
  | 0, _, _ => by simp [replay?, take]
  | n + 1, hn, h => by
    obtain ⟨step, hstep⟩ : ∃ step, d.steps[n]? = some step :=
      ⟨d.steps[n], List.getElem?_eq_getElem hn⟩
    obtain ⟨c, hc, hall⟩ := h n n.lt_succ_self
    rw [take_succ hstep, replay?_append_singleton, replay?_append_singleton,
      replay?_take_comp hπ n (n.le_succ.trans hn) fun k hk ↦ h k (hk.trans n.lt_succ_self),
      Option.mem_def.1 hc]
    exact step.replay?_congr c fun m _ hm ↦ (hπ (φ m) <|
      SyntacticObject.map_ne_zero_of_mem_terms (π.comp φ) hm (hall _ List.mem_cons_self)).symm

/-- A licensing licenses the derivations that its composite with a morphism preserving zero and
heads licenses: a coarser licensing's derivations are the finer one's. -/
theorem LicensedBy.of_comp (h0 : π 0 = 0) (hπ : ∀ x, π x ≠ 0 → head (π x) = head x)
    (h : d.LicensedBy (π.comp φ)) : d.LicensedBy φ := fun n hn ↦ by
  obtain ⟨c, hc, hall⟩ := h n hn
  rw [← replay?_take_comp φ π hπ n hn fun k hk ↦ h k (hk.le.trans hn)] at hc
  exact ⟨c, hc, fun x hx hx0 ↦ hall x hx (by rw [MulHom.comp_apply, hx0, h0])⟩

end Minimalist.Derivation
