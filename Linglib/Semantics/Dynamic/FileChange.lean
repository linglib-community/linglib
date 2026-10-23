module

public import Linglib.Semantics.Dynamic.Partial
public import Linglib.Semantics.Dynamic.State

/-!
# File change semantics

This file defines file change potentials, the meanings of sentences in Heim's file change
semantics. A file records what a discourse has established so far: it keeps a card for each
individual that has been mentioned, and a sequence of individuals satisfies the file when,
read card by card, it fits every entry. Uttering a sentence changes the file. It filters out
the sequences the sentence rules out and opens a card for each individual the sentence
introduces, and the meaning of the sentence is the function from files to files that its
utterance brings about.

A file is an information state (`State`) whose points are the sequences and whose
established cards are the referents every point defines. The dissertation's files, which
distinguish only finitely many cards, are the states uniform at a set of cards. A file change
potential is a partial function on states. It is undefined at a file that fails the
sentence's felicity conditions, so presupposition is definedness: the Novelty Condition on an
indefinite requires its card to be new to the file, and the Familiarity Condition on a
definite requires the card to be present. Sequencing is composition of partial functions.

The assertive update by an atomic sentence merges the file with the sentence's proposition
state. At the cards the file already has the merge filters the sequences, and at new cards it
extends each sequence by every value, which is Heim's atomic rule read point by point. Every
update only adds information, so it is eliminative in the informativeness order, Heim's
Principle (A) as `PartialUpdate.IsEliminative`, and a card, once established, is never lost.
Negation keeps the sequences that no extension carries into the scope's update, which traps the
referents introduced inside the scope. On a uniform file negation is set difference, as in the
later propositional presentation of the theory.

## Main definitions

* `FCP`: file change potentials, partial updates of information states.
* `FCP.ofState`: the assertive update by a state, merging the file with it.
* `FCP.atomVar`: the update by an atomic predicate at a card.
* `FCP.atomW`: the update by an atomic predicate on the world alone.
* `FCP.neg`, `FCP.cond`: negation as non-subsistence, and the conditional as `¬(φ ∧ ¬ψ)`.
* `FCP.indef`: the indefinite, guarded by the Novelty Condition.
* `FCP.def_`: the definite, guarded by the Familiarity Condition and its descriptive content.
* `FCP.trueIn`: truth of a sentence with respect to a file, as consistency of the updated file.

## Main results

* `FCP.ofState_mul`: updating by two states in sequence is updating by their merge.
* `FCP.semiconj_ofState`: up to informational equivalence, assertion is additive.
* `FCP.atomVar_eq`: the atom extends the file along its card and filters by its predicate.
* `FCP.atomVar_eq_of_familiar`, `FCP.atomVar_eq_of_novel`: at an established card the atom
  filters, and at a new card it is random assignment followed by filtering.
* `FCP.admits_indef`, `FCP.admits_def_`: the felicity conditions are definedness.
* `FCP.isEliminative_ofState`, `FCP.isEliminative_neg`, `PartialUpdate.IsEliminative.indef`: every
  clause only adds information.
* `PartialUpdate.IsEliminative.familiar`: an established card stays established.
* `FCP.neg_eq_partial_neg`: on a uniform file, negation is set difference.

## References

* [heim-1982], [heim-1983], [heim-1991]
* [kamp-vangenabith-reyle-2011]
-/

@[expose] public section

open DynamicSemantics

/-- A file change potential ([heim-1982]): a partial update of referential
information states. Partiality is presupposition (`PartialUpdate.Admits`); Heim numbers her
cards, `V := ℕ`. -/
abbrev FCP (W V M : Type*) := PartialUpdate (State W V M)

namespace FCP

variable {W V M : Type*} {A B F F' : State W V M} {φ ψ : FCP W V M} {x : V}

/-! ### Assertive update -/

/-- Assertive update by a state: the file merges with it. Each point of the
file pairs with every compatible point of `A`, filtering where their domains
overlap and extending where `A` defines more. The update is total;
appropriateness lives on `indef` and `def_`. -/
def ofState (A : State W V M) : FCP W V M := fun F : State W V M ↦ Part.some (F * A)

@[simp] theorem ofState_apply : ofState A F = Part.some (F * A) := rfl

theorem mem_ofState : F' ∈ ofState A F ↔ F' = F * A := Part.mem_some_iff

theorem ofState_one : ofState (1 : State W V M) = PFun.id _ := funext fun _ ↦ by simp

/-- Assertive update is the regular action of the merge monoid: updating by
`A` and then by `B` is updating by `A * B`. -/
theorem ofState_mul : ofState (A * B) = (ofState A).seq (ofState B) :=
  funext fun _ ↦ by simp [PartialUpdate.seq, PFun.comp_apply, mul_assoc]

theorem ofState_le (h : F' ∈ ofState A F) : F' ≤ F := mem_ofState.mp h ▸ State.mul_le_left

/-- Up to informational equivalence, assertion is additive in the sense of
`Semantics/Dynamic/Consequence.lean`: on the upper sets of possibilities it meets the file with
the content of `A` (`isAdditive_inf_right`). Merging need not be literally idempotent, since two
compatible points of a file merge into a third, so literal fixed points of assertion are finer
than informational acceptance. -/
theorem semiconj_ofState (A : State W V M) :
    Function.Semiconj
      (OrderDual.toDual ∘ upperClosure : State W V M → (UpperSet (Possibility W V (Flat M)))ᵒᵈ)
      (· * A) (· ⊓ OrderDual.toDual (upperClosure A)) :=
  fun _ ↦ congrArg OrderDual.toDual State.upperClosure_mul

/-! ### Atoms -/

/-- An atomic predicate on the world: merge with its proposition at the empty
stratum. -/
def atomW (pred : W → Prop) : FCP W V M :=
  ofState {q ∈ (State.stratum ∅ : State W V M) | pred q.world}

/-- An atomic predicate at card `x`: merge with its proposition state at the
stratum `{x}`. -/
def atomVar (pred : M → Prop) (x : V) : FCP W V M := ofState (State.atomAt x fun _ ↦ pred)

theorem atomW_eq (pred : W → Prop) : atomW pred F = Part.some {p ∈ F | pred p.world} := by
  rw [atomW, ofState_apply, State.mul_eq_sep_of_uniformAt fun _ h ↦ h.1, State.mul_stratum_empty]
  congr 1
  ext r
  refine and_congr_right fun _ ↦ ?_
  show ((Possibility.restrict ∅ r).domain = ∅ ∧ pred r.world) ↔ pred r.world
  rw [Possibility.domain_restrict, Set.empty_inter]
  exact and_iff_right rfl

/-- The card atom extends the file along its card, then filters by its
predicate: the satisfaction clause and the domain clause of [heim-1982]'s
atomic rule, per point. -/
theorem atomVar_eq (pred : M → Prop) (x : V) :
    atomVar pred x F =
      Part.some {p ∈ F * State.stratum {x} | ∃ m : M, p.assignment x = ↑m ∧ pred m} := by
  rw [atomVar, ofState_apply, State.mul_atomAt]

/-- At an established card the atom filters. -/
theorem atomVar_eq_of_familiar (pred : M → Prop) (hfam : State.Familiar F x) :
    atomVar pred x F = Part.some {p ∈ F | ∃ m : M, p.assignment x = ↑m ∧ pred m} := by
  rw [atomVar_eq, hfam.mul_stratum_singleton]

/-- At a novel card the atom is random assignment followed by filtering, so
the indefinite adds only the Novelty guard. -/
theorem atomVar_eq_of_novel [DecidableEq V] (pred : M → Prop) (hnov : State.Novel F x) :
    atomVar pred x F =
      Part.some {p ∈ F.randomAssign x | ∃ m : M, p.assignment x = ↑m ∧ pred m} := by
  rw [atomVar_eq, hnov.mul_stratum_singleton]

/-! ### Connectives and felicity conditions -/

/-- Negation keeps the points of `F` that do not subsist in the scope's
update: no extension of the point verifies the scope, so referents
introduced inside it are trapped. Undefined when the scope is. -/
def neg (φ : FCP W V M) : FCP W V M :=
  fun F : State W V M ↦ (φ F).map fun F' ↦ {p ∈ F | p ∉ lowerClosure F'}

/-- The conditional is the negated conjunction `¬(φ ∧ ¬ψ)`. -/
def cond (φ ψ : FCP W V M) : FCP W V M := neg (φ.seq (neg ψ))

/-- An indefinite at card `x`: defined only if `x` is novel (the Novelty
Condition), then random assignment at `x` followed by the body. Indefinites
do not quantify; they open a card. [heim-1991] later derives novelty from
Maximize Presupposition rather than stipulating it. -/
def indef [DecidableEq V] (x : V) (body : FCP W V M) : FCP W V M :=
  fun F : State W V M ↦ Part.assert (State.Novel F x) fun _ ↦ body (F.randomAssign x)

/-- A definite at card `x` with descriptive content `N`: defined only if `x`
is established and the file supports its content (the Extended
Novelty-Familiarity-Condition), and then changes nothing. -/
def def_ (x : V) (N : FCP W V M) : FCP W V M :=
  fun F : State W V M ↦
    Part.assert (State.Familiar F x ∧ N.supports F) fun _ ↦ Part.some F

@[simp] theorem admits_neg : (neg φ).Admits F ↔ φ.Admits F := Iff.rfl

theorem admits_cond :
    (cond φ ψ).Admits F ↔ ∃ h : φ.Admits F, ψ.Admits ((φ F).get h) := Iff.rfl

/-- The Novelty Condition is definedness. -/
theorem admits_indef [DecidableEq V] (body : FCP W V M) :
    (indef x body).Admits F ↔ ∃ _ : State.Novel F x, (body (F.randomAssign x)).Dom :=
  Iff.rfl

theorem indef_apply [DecidableEq V] (body : FCP W V M) (h : State.Novel F x) :
    indef x body F = body (F.randomAssign x) := Part.assert_pos h

/-- The Extended Familiarity Condition is definedness. -/
theorem admits_def_ (N : FCP W V M) :
    (def_ x N).Admits F ↔ State.Familiar F x ∧ N.supports F :=
  ⟨fun ⟨h, _⟩ ↦ h, fun h ↦ ⟨h, trivial⟩⟩

theorem def_apply (N : FCP W V M) (h : State.Familiar F x ∧ N.supports F) :
    def_ x N F = Part.some F := Part.assert_pos h

theorem subset_of_mem_neg (h : F' ∈ neg φ F) : F' ⊆ F := by
  obtain ⟨_, -, rfl⟩ := (Part.mem_map_iff _).mp h
  exact fun _ hp ↦ hp.1

/-! ### Principle (A)

Every defined update only adds information: it descends in informativeness. On a uniform stratum
this is set shrinking (`State.UniformAt.le_iff_subset`); at a novel card an update extends rather
than shrinks. -/

theorem isEliminative_ofState (A : State W V M) : (ofState A).IsEliminative :=
  fun _ _ ↦ ofState_le

theorem isEliminative_neg (φ : FCP W V M) : (neg φ).IsEliminative :=
  fun _ _ h ↦ State.le_of_subset (subset_of_mem_neg h)

theorem isEliminative_cond (φ ψ : FCP W V M) : (cond φ ψ).IsEliminative :=
  isEliminative_neg _

theorem _root_.DynamicSemantics.PartialUpdate.IsEliminative.indef [DecidableEq V]
    {body : FCP W V M} (h : body.IsEliminative) (x : V) : (indef x body).IsEliminative :=
  fun _ _ hF' ↦
  let ⟨hn, hF'⟩ := Part.mem_assert_iff.mp hF'
  (h _ _ hF').trans (State.randomAssign_le hn)

theorem isEliminative_def_ (x : V) (N : FCP W V M) : (def_ x N).IsEliminative :=
  fun _ _ hF' ↦ let ⟨_, hF'⟩ := Part.mem_assert_iff.mp hF'; le_of_eq (Part.mem_some_iff.mp hF')

theorem _root_.DynamicSemantics.PartialUpdate.IsEliminative.eq_empty_of_mem
    (h : φ.IsEliminative) (hF' : F' ∈ φ ∅) : F' = ∅ :=
  State.eq_empty_of_le_bot (h ∅ F' hF')

/-- A card, once established, stays established. -/
theorem _root_.DynamicSemantics.PartialUpdate.IsEliminative.familiar (h : φ.IsEliminative)
    (hx : State.Familiar F x) (hF' : F' ∈ φ F) : State.Familiar F' x :=
  hx.of_le (h F F' hF')

/-! ### Truth -/

/-- The truth criterion (C): `φ` is true with respect to `F` iff `F + φ` is
defined and consistent. Existential quantification is built into truth, so
indefinites need no existential closure. -/
def trueIn (F : State W V M) (φ : FCP W V M) : Prop := ∃ F' ∈ φ F, F'.Nonempty

theorem trueIn_admits (h : trueIn F φ) : φ.Admits F :=
  let ⟨F', hF', _⟩ := h
  Part.dom_iff_mem.mpr ⟨F', hF'⟩

theorem trueIn_of_supports (hsup : φ.supports F) (hcons : F.Nonempty) :
    trueIn F φ :=
  ⟨F, hsup, hcons⟩

/-! ### The uniform shadow -/

/-- On a uniform stratum, non-subsistence negation is [heim-1983]'s
set-difference negation (`CCP.Partial.neg`): with every referent shared, a
point subsists in the update exactly when it survives into it. -/
theorem neg_eq_partial_neg [DecidableEq V] {X : Finset V} (hF : State.UniformAt X F)
    (hφ : ∀ F' ∈ φ F, State.UniformAt X F') :
    neg φ F = CCP.Partial.neg φ F := by
  refine Part.ext' Iff.rfl fun h₁ h₂ ↦ ?_
  show ({p ∈ (F : Set (Possibility W V (Flat M))) | p ∉ lowerClosure ((φ F).get h₁)} : Set _) =
    (F : Set (Possibility W V (Flat M))) \ (φ F).get h₁
  ext p
  exact and_congr_right fun hp ↦ not_congr
    ((hφ _ (Part.get_mem _)).mem_lowerClosure (hF p hp))

end FCP
