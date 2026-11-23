module

public import Mathlib.Data.PFun
public import Mathlib.Data.Set.Image

/-!
# Co-propositional questions

In Ginzburg's theory of dialogue, KoS, a question is a propositional abstract: a partial function
`q : R →. P` from records to propositions, defined on the records of its domain. A polar question
`p?` is the constant function `PFun.pure p`, any record being of the empty record type, and a
wh-question is `PFun.res f s`, the abstract `f` on the records in `s`.

Two questions are co-propositional when some record makes them the same proposition,
`∃ r, q₀ r = q₁ r` with both sides defined. The relation is symmetric, and holds of a question
and itself exactly when its domain is inhabited; it is not transitive, since `q` may share one
record with `q₀` and another with `q₁`.

## Main definitions

* `Gameboard.Copropositional`: two questions take the same value at some record.

## Main results

* `Gameboard.copropositional_iff_graph`: two questions are co-propositional iff their graphs
  meet.
* `Gameboard.copropositional_pure_left`: `p?` is co-propositional with `q` iff `p` is a value of
  `q`, so a correction is co-propositional with the question it instantiates.
* `Gameboard.copropositional_res_res`: two wh-questions are co-propositional iff their abstracts
  agree at a record of both domains.
* `Gameboard.copropositional_res_res_self`: two restrictions of one abstract are co-propositional
  iff their domains meet, so a question differing from another only in its domain is
  co-propositional with it.

## References

* [ginzburg-fernandez-schlangen-2014]
* [ginzburg-2012]
-/

@[expose] public section

namespace Gameboard

variable {R P : Type*} {q q₀ q₁ : R →. P} {f g : R → P} {s t : Set R} {p p' : P}

/-- Two questions are co-propositional when some record makes them the same proposition
([ginzburg-fernandez-schlangen-2014] (34b)). -/
def Copropositional (q₀ q₁ : R →. P) : Prop :=
  ∃ r, ∃ p ∈ q₀ r, p ∈ q₁ r

theorem copropositional_iff_graph : Copropositional q₀ q₁ ↔ (q₀.graph ∩ q₁.graph).Nonempty :=
  ⟨fun ⟨r, p, h₀, h₁⟩ ↦ ⟨(r, p), h₀, h₁⟩, fun ⟨⟨r, p⟩, h₀, h₁⟩ ↦ ⟨r, p, h₀, h₁⟩⟩

@[symm]
theorem Copropositional.symm (h : Copropositional q₀ q₁) : Copropositional q₁ q₀ :=
  let ⟨r, p, h₀, h₁⟩ := h
  ⟨r, p, h₁, h₀⟩

theorem copropositional_comm : Copropositional q₀ q₁ ↔ Copropositional q₁ q₀ :=
  ⟨.symm, .symm⟩

/-- A question is co-propositional with itself exactly when it is defined somewhere. -/
theorem copropositional_self : Copropositional q q ↔ q.Dom.Nonempty := by
  simp [Copropositional, Set.Nonempty]

/-- Co-propositional questions have a record in common. -/
theorem Copropositional.dom_inter_nonempty (h : Copropositional q₀ q₁) :
    (q₀.Dom ∩ q₁.Dom).Nonempty :=
  let ⟨r, p, h₀, h₁⟩ := h
  ⟨r, (q₀.mem_dom r).2 ⟨p, h₀⟩, (q₁.mem_dom r).2 ⟨p, h₁⟩⟩

/-- A polar question `p?` is co-propositional with `q` iff `p` instantiates `q`. -/
theorem copropositional_pure_left : Copropositional (PFun.pure p) q ↔ p ∈ q.ran := by
  simp [Copropositional, PFun.pure, PFun.ran]

theorem copropositional_pure_right : Copropositional q (PFun.pure p) ↔ p ∈ q.ran :=
  copropositional_comm.trans copropositional_pure_left

theorem copropositional_pure_pure :
    Copropositional (PFun.pure p : R →. P) (PFun.pure p') ↔ Nonempty R ∧ p = p' := by
  simp [Copropositional, PFun.pure, eq_comm]

/-- Two wh-questions are co-propositional iff their abstracts agree at a record of both
domains. -/
theorem copropositional_res_res :
    Copropositional (PFun.res f s) (PFun.res g t) ↔ ∃ r ∈ s ∩ t, f r = g r := by
  simp only [Copropositional, PFun.mem_res, Set.mem_inter_iff]
  exact ⟨fun ⟨r, _, ⟨hs, rfl⟩, ht, hg⟩ ↦ ⟨r, ⟨hs, ht⟩, hg.symm⟩,
    fun ⟨r, ⟨hs, ht⟩, h⟩ ↦ ⟨r, f r, ⟨hs, rfl⟩, ht, h.symm⟩⟩

/-- Two restrictions of one abstract are co-propositional iff their domains meet. -/
theorem copropositional_res_res_self :
    Copropositional (PFun.res f s) (PFun.res f t) ↔ (s ∩ t).Nonempty := by
  simp [copropositional_res_res, Set.Nonempty]

/-- A polar question `p?` is co-propositional with a wh-question iff `p` is the value of its
abstract at a record of its domain. -/
theorem copropositional_pure_res : Copropositional (PFun.pure p) (PFun.res f s) ↔ p ∈ f '' s := by
  simp [copropositional_pure_left, PFun.ran, PFun.mem_res]

/-- For an injective abstract, `(f r)?` is co-propositional with the wh-question on `s` iff `r`
is in `s`. -/
theorem copropositional_pure_res_of_injective (hf : Function.Injective f) {r : R} :
    Copropositional (PFun.pure (f r)) (PFun.res f s) ↔ r ∈ s := by
  rw [copropositional_pure_res, hf.mem_set_image]

end Gameboard
