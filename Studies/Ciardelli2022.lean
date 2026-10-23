module

public import Linglib.Logic.Team.Inquisitive
public import Mathlib.Tactic.DeriveFintype

/-!
# Ciardelli (2022): Inquisitive Logic: Consequence and Inference in the Realm of Questions

This file formalizes the illustrations of inquisitive modal logic in the last chapter of
[ciardelli-2022]. The Kripke modality `□` applied to a question is a statement, so that knowing
whether `p` amounts to knowing that `p` or knowing that `¬p` (`nec_polarQ`). The properly
inquisitive modality `⊞`, supported when every state related to each world supports its argument,
coincides with `□` on statements, and on questions it expresses Ciardelli and Roelofsen's
wondering, `¬□μ ∧ ⊞μ`.

In the three inquisitive states of Fig. 8.1 the agent knows whether `p`, wonders whether `p`, and
does neither (`fig81a_knows`, `fig81b_wonders`, `fig81c_neither`), and the second shows that `⊞`,
unlike `□`, does not distribute over inquisitive disjunction (`fig81b_ent_polarQ_not_disj`).

## References

* [I. Ciardelli, *Inquisitive Logic: Consequence and Inference in the Realm of Questions*
  (2022)][ciardelli-2022]
* [I. Ciardelli and F. Roelofsen, *Inquisitive dynamic epistemic logic*
  (2015)][ciardelli-roelofsen-2015]
-/

@[expose] public section

namespace Ciardelli2022

open Inquisitive

/-! ### Knowing whether (§8.2) -/

variable {W A : Type*} [DecidableEq W] (M : Model W A) (φ : Formula A)

/-- Knowing whether `φ` is knowing that `φ` or knowing that `¬φ` (3b), the polar instance of
`support_nec_inqDisj`. -/
theorem nec_polarQ :
    support M (.nec φ.polarQ) = support M ((Formula.nec φ).disj (.nec φ.neg)) :=
  support_nec_inqDisj M φ φ.neg

/-- The agent wonders about `μ` when `¬□μ ∧ ⊞μ` ([ciardelli-roelofsen-2015]; §8.3). -/
abbrev wonders (μ : Formula A) : Formula A := (Formula.nec μ).neg.conj (.ent μ)

/-! ### Fig. 8.1: knowing, wondering and neither (§8.3) -/

inductive Atom
  | p | q
  deriving DecidableEq, Fintype

/-- `p` as a formula. -/
abbrev p : Formula Atom := .atom .p

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

theorem fig81a_knows :
    ∀ w, {w} ∈ support fig81a (.nec p) ∧ {w} ∈ support fig81a (.nec p.polarQ) := by
  decide

theorem fig81b_wonders : ∀ w, {w} ∈ support fig81b (wonders p.polarQ) := by decide

theorem fig81c_neither :
    ∀ w, {w} ∈ support fig81c ((Formula.nec p.polarQ).neg.conj (Formula.ent p.polarQ).neg) := by
  decide

theorem fig81b_ent_polarQ_not_disj :
    ∀ w, {w} ∈ support fig81b (.ent p.polarQ) ∧
      {w} ∉ support fig81b ((Formula.ent p).disj (.ent p.neg)) := by
  decide

end Ciardelli2022
