module

public import Linglib.Logic.Team.Inquisitive
public import Mathlib.Tactic.DeriveFintype

/-!
# Ciardelli (2022): Inquisitive Logic: Consequence and Inference in the Realm of Questions

This file formalizes the preview of inquisitive modal logic that closes Ciardelli's book. Applied
to a question, the Kripke modality `□` yields a statement, and knowing whether `p` comes out as
[knowing that `p` or knowing that `¬p`](##nec_polarQ). The properly inquisitive modality `⊞`
quantifies over the states that settle an agent's issues, and after Ciardelli and Roelofsen the
agent wonders about `μ` when $\neg\Box\mu \wedge \boxplus\mu$. Of the book's three inquisitive
states, one [wonders whether `p`](##fig81b_wonders), and there `⊞` [does not distribute over
inquisitive disjunction](##fig81b_ent_polarQ_not_disj). [Questions add no statements to
InqB](##Inquisitive.truthConditional_iff_support_cl_eq) and [none under `□`](##nec_eq_classical),
but `⊞?p` is a statement that [no `\\/`-free formula expresses](##ent_polarQ_ne_classical).

## Implementation notes

* A world of the book's figure is the set of atoms true at it, and its inquisitive states are the
  same at every world, since the figure draws them for an arbitrary world.
* The two models separating `⊞?p` from the classical formulas have two worlds and make every atom
  true at one of them, so the separation holds over any set of atoms.

## TODO

* Knowing who (3-c) and the failure of $\boxplus\exists xPx \equiv \exists x\boxplus Px$ need the
  predicate logic InqBQ.

## References

* [I. Ciardelli, *Inquisitive Logic: Consequence and Inference in the Realm of Questions*
  (2022)][ciardelli-2022]
* [I. Ciardelli and F. Roelofsen, *Inquisitive dynamic epistemic logic*
  (2015)][ciardelli-roelofsen-2015]
-/

@[expose] public section

namespace Ciardelli2022

open Inquisitive

/-! ### Knowing whether and wondering -/

variable {W A : Type*} [DecidableEq W] (M : Model W A) (φ : Formula A)

/-- Knowing whether `φ` is knowing that `φ` or knowing that `¬φ`, (3-b), p. 251. -/
theorem nec_polarQ :
    support M (.nec φ.polarQ) = support M ((Formula.nec φ).disj (.nec φ.neg)) :=
  support_nec_inqDisj M φ φ.neg

/-- The agent wonders about `μ` when `¬□μ ∧ ⊞μ` ([ciardelli-roelofsen-2015]), p. 256. -/
abbrev wonders (μ : Formula A) : Formula A := (Formula.nec μ).neg.conj (.ent μ)

/-! ### Three inquisitive states (Fig. 8.1) -/

inductive Atom
  | p | q
  deriving DecidableEq, Fintype

/-- `p` as a formula. -/
abbrev p : Formula Atom := .atom .p

/-- `q` as a formula. -/
abbrev q : Formula Atom := .atom .q

/-- `model inq` is the Fig. 8.1 model with inquisitive states `inq`. As in the book (p. 255),
`w_pq` is the world where `p` and `q` are both true, `w_p¬q` the world where only `p` is, and so
on, so a world is the set of atoms true at it. -/
abbrev model (inq : Finset Atom → Finset (Finset (Finset Atom))) :
    Model (Finset Atom) Atom :=
  ⟨inq, fun a w ↦ a ∈ w⟩

/-- In Fig. 8.1a, `Σ(w) = {{w_pq, w_p¬q}}↓`, so the agent knows that `p` and has no open issue. -/
abbrev fig81a : Model (Finset Atom) Atom :=
  model fun _ ↦ ({{.p, .q}, {.p}} : Finset (Finset Atom)).powerset

/-- In Fig. 8.1b, `Σ(w) = {{w_pq, w_p¬q}, {w_¬pq, w_¬p¬q}}↓`, so the agent knows nothing and is
interested in whether `p`. -/
abbrev fig81b : Model (Finset Atom) Atom :=
  model fun _ ↦ ({{.p, .q}, {.p}} : Finset (Finset Atom)).powerset ∪
    ({{.q}, ∅} : Finset (Finset Atom)).powerset

/-- In Fig. 8.1c, `Σ(w) = {{w_pq, w_¬pq}, {w_p¬q, w_¬p¬q}}↓`, so the agent knows nothing and is
interested in whether `q`. -/
abbrev fig81c : Model (Finset Atom) Atom :=
  model fun _ ↦ ({{.p, .q}, {.q}} : Finset (Finset Atom)).powerset ∪
    ({{.p}, ∅} : Finset (Finset Atom)).powerset

-- p. 255 and p. 256
theorem fig81a_knows : ∀ w, {w} ∈ support fig81a (.nec p) ∧
    {w} ∈ support fig81a (.nec p.polarQ) ∧ {w} ∉ support fig81a (.nec q.polarQ) := by
  decide

/-- In Fig. 8.1b the agent wonders whether `p`, p. 256. -/
theorem fig81b_wonders : ∀ w, {w} ∈ support fig81b (wonders p.polarQ) := by decide

-- p. 255 and p. 256
theorem fig81c_neither : ∀ w,
    {w} ∈ support fig81c ((Formula.nec p.polarQ).neg.conj (Formula.ent p.polarQ).neg) ∧
      {w} ∈ support fig81c (wonders q.polarQ) := by
  decide

-- p. 255
theorem fig81a_not_wonders (μ : Formula Atom) (w : Finset Atom) :
    {w} ∉ support fig81a (wonders μ) := fun h ↦
  (singleton_mem_support_neg _ _ _).1 h.1 <|
    support_ent_eq_nec_of_access_mem fig81a μ (by decide) ▸ h.2

/-- Unlike `□`, `⊞` does not distribute over inquisitive disjunction: in Fig. 8.1b `⊞?p` holds
but `⊞p ∨ ⊞¬p` does not, p. 257. -/
theorem fig81b_ent_polarQ_not_disj :
    ∀ w, {w} ∈ support fig81b (.ent p.polarQ) ∧
      {w} ∉ support fig81b ((Formula.ent p).disj (.ent p.neg)) := by
  decide

/-! ### Statements formed from questions -/

-- Example 3.6.4
example : p.polarQ.resolutions = [p, p.neg] := rfl

-- Example 3.6.6
example : (p.polarQ.impl q.polarQ).resolutions.length = 4 := rfl

-- (3-b): the resolution of knowing whether
example : (Formula.nec p.polarQ).resolutions = [(Formula.nec p).disj (.nec p.neg)] := rfl

/-- In the language with `□` alone every formula `□φ` is equivalent to a formula of standard
modal logic, the disjunction of `□α` over the resolutions `α` of `φ`, p. 253. -/
theorem nec_eq_classical (h : φ.IsEntFree) :
    ∃ α : Formula A, α.IsClassical ∧
      ∀ {W : Type*} [DecidableEq W] (M : Model W A), support M (.nec φ) = support M α :=
  ⟨_, Formula.isClassical_of_mem_resolutions (φ := .nec φ) h (List.mem_singleton_self _),
    fun M ↦ SetLike.ext fun s ↦ by
      simp [mem_support_iff_exists_mem_resolutions M (.nec φ), Formula.resolutions]⟩

/-- `⊞?p` is a statement that no `\\/`-free formula expresses: an agent who wonders whether `p`
and one who knows as little and wonders about nothing agree on every classical formula but not on
`⊞?p`, p. 256. -/
theorem ent_polarQ_ne_classical {Atom : Type*} (a : Atom) {α : Formula Atom}
    (hα : α.IsClassical) :
    ∃ M : Model Bool Atom, support M α ≠ support M (.ent (Formula.atom a).polarQ) := by
  by_contra! h
  let M₁ : Model Bool Atom := ⟨fun _ ↦ {{true}, {false}}, fun _ w ↦ w⟩
  let M₂ : Model Bool Atom := ⟨fun _ ↦ {{true, false}}, fun _ w ↦ w⟩
  have e := (h M₁).symm.trans <|
    (support_eq_of_isClassical (M := M₁) (M' := M₂) rfl (funext fun _ ↦ rfl) hα).trans (h M₂)
  have h₁ : {true} ∈ support M₁ (.ent (Formula.atom a).polarQ) := by
    simp [M₁, Finset.subset_singleton_iff]
  have h₂ : {true} ∉ support M₂ (.ent (Formula.atom a).polarQ) := by
    simp only [M₂, mem_support_ent, mem_support_inqDisj, mem_support_atom, mem_support_neg]
    decide
  exact h₂ (e ▸ h₁)

end Ciardelli2022
