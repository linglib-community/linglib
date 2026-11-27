module

public import Linglib.Discourse.Commitment.Space.Semantics
public import Linglib.Discourse.Table.Basic

/-!
# Krifka (2015): Bias in Commitment Space Semantics

A *commitment space development* is the record of a conversation: the commitment spaces it has
passed through, each with the participant whose move led to it. An act extends the record with
the space the act leads to. A *rejection* extends it with the space before the last move.

An assertion of `φ` by `s` is two acts by `s`: the update by `s`'s commitment to `φ`, and then
the update by `φ` itself. A bipolar question put to `a` proposes `a`'s commitment to `φ` or to
`φᶜ`, and a monopolar question proposes `a`'s commitment to `φ` alone. The responses *yes* and
*no* are the updates by `a`'s commitment to `φ` and to `φᶜ`.

The three responses with *no* behave differently when no rejection comes first. After a bipolar
question, *no* leads to the space that the assertion of `φᶜ` would lead to by itself. After a
monopolar question, *no* leads to states that contain `a`'s commitments to `φ` and to `φᶜ`; if
`a`'s commitment relation is serial, no world belongs to all the propositions of such a state.
After an assertion, *no* leads to states that contain `φ` and `a`'s commitment to `φᶜ`; at a
world that belongs to all the propositions of such a state, none of the worlds accessible for
`a` does. If a rejection comes first, *no* after an assertion leads to the space with `s`'s
commitment to `φ` and `a`'s commitment to `φᶜ`, without `φ`.

A Table determines a commitment space whose states are filters. Its root is the common ground of
the Table, and its other members are the filters that refine the common ground and contain an
answer of every item. Placing an item on the Table is then the question whose proposals are the
answers of the item, and for an empty Table, moving a proposition to the common ground is the
update by that proposition.

## Implementation notes

A development stores its first space and its moves, the most recent first. Rejecting a
development with fewer than two moves returns to the first space.

The acts of a development are stated on states that are sets of propositions. The commitment
space of a Table has filters as states, and a filter with more information is smaller, so its
states carry the dual order.

The update by `φ` in an assertion is defined on every space. The results do not assume that the
space admits it.

## TODO

* A question with high negation proposes that `a` not be committed to `φ`. It is weaker than the
  question that proposes `a`'s commitment to `φᶜ`. This is proved for states that are filters. It
  fails for states that are sets of propositions, where a state can contain `a ⊢[O] φᶜ` without
  containing `(a ⊢[O] φ)ᶜ`, and the high-negation question is not defined as an act of a
  development.
* The acceptability of questions by contextual evidence, the response *I don't know*, alternative
  and constituent questions, and question tags are not formalized, and the examples are not in
  `Data/Examples`.
* The commitment space of a Table does not represent the discourse commitments of the
  participants. Moving a proposition to the common ground is related to the update only for an
  empty Table.

## References

* [krifka-2015]
* [cohen-krifka-2014]
* [farkas-bruce-2010]
-/

@[expose] public section

namespace Krifka2015

open Commitment Commitment.Space ModalLogic Filter OrderDual
open scoped SetRel

/-- (8)–(9): A **commitment space development** records the commitment spaces a conversation has
passed through, each with the participant whose move led to it. -/
structure Development (P S : Type*) [LE S] where
  /-- The space the record starts from. -/
  initial : Space S
  /-- The moves made, the most recent first, each with its actor and the space it led to. -/
  moves : List (P × Space S)

namespace Development

section

variable {P S : Type*} [LE S] (D : Development P S) (a b : P) (f : Space S → Space S)

/-- The **current** space of a development is the space its last move led to. -/
def current : Space S := (D.moves.head?.map Prod.snd).getD D.initial

/-- The **previous** space of a development is the space before its last move. -/
def previous : Space S := (D.moves.tail.head?.map Prod.snd).getD D.initial

/-- (9): An **act** by `a` extends a development with the space the act leads to from the current
space. -/
def act : Development P S := ⟨D.initial, (a, f D.current) :: D.moves⟩

/-- (10): A **rejection** by `a` extends a development with its previous space. -/
def reject : Development P S := ⟨D.initial, (a, D.previous) :: D.moves⟩

@[simp] theorem current_act : (D.act a f).current = f D.current := rfl

@[simp] theorem previous_act : (D.act a f).previous = D.current := rfl

@[simp] theorem current_reject : (D.reject a).current = D.previous := rfl

end

variable {P W : Type*} (O : P → SetRel W W) (D : Development P (Set (Set W))) (s a : P)
  (φ : Set W) {d : Set (Set W)}

/-- (19): The **assertion** of `φ` by `s` is the update by `s`'s commitment to `φ` followed by the
update by `φ`. -/
def assertion : Development P (Set (Set W)) :=
  (D.act s (·.assert O s φ)).act s (·.update {φ})

/-- (20): The response **yes** by `a` is the update by `a`'s commitment to `φ`. -/
def yes : Development P (Set (Set W)) := D.act a (·.assert O a φ)

/-- (20): The response **no** by `a` is the update by `a`'s commitment to `φᶜ`. -/
def no : Development P (Set (Set W)) := D.act a (·.assert O a φᶜ)

/-- (23): The **bipolar question** by `s` to `a` proposes `a`'s commitment to `φ` or to `φᶜ`. -/
def bipolar : Development P (Set (Set W)) := D.act s (·.bipolarQuestion O a φ)

/-- (27): The **monopolar question** by `s` to `a` proposes `a`'s commitment to `φ`. -/
def monopolar : Development P (Set (Set W)) := D.act s (·.monopolarQuestion O a φ)

/-- (22): After an assertion of `φ` by `s`, a rejection and the response *no* by `a` lead to the
space with `s`'s commitment to `φ` and `a`'s commitment to `φᶜ`, without `φ`. -/
theorem current_no_reject_assertion :
    (((D.assertion O s φ).reject a).no O a φ).current =
      (D.current.assert O s φ).assert O a φᶜ := rfl

-- (22), the state the rejection avoids
theorem mem_of_mem_current_no_assertion (hd : d ∈ ((D.assertion O s φ).no O a φ).current) :
    φ ∈ d ∧ (a ⊢[O] φᶜ) ∈ d :=
  ⟨Set.singleton_subset_iff.1 <|
      (le_root_update _ _).trans (root_le_of_mem_update _ hd),
    committed_mem_of_mem_assert _ O a φᶜ hd⟩

/-- After an assertion of `φ` and the response *no* by `a` with no rejection, at a world that
belongs to every proposition of a resulting state, no world accessible for `a` belongs to every
proposition of that state. -/
theorem notMem_sInter_of_mem_current_no_assertion
    (hd : d ∈ ((D.assertion O s φ).no O a φ).current) {w v : W} (hw : w ∈ ⋂₀ d)
    (hwv : w ~[O a] v) : v ∉ ⋂₀ d := fun hv ↦
  let ⟨hφ, hc⟩ := D.mem_of_mem_current_no_assertion O s a φ hd
  hw _ hc hwv (hv _ hφ)

-- (28b), the state the rejection avoids
theorem mem_of_mem_current_no_monopolar (h : (a ⊢[O] φᶜ) ∉ D.current.root)
    (hd : d ∈ ((D.monopolar O s a φ).no O a φ).current) :
    (a ⊢[O] φ) ∈ d ∧ (a ⊢[O] φᶜ) ∈ d := by
  refine ⟨?_, committed_mem_of_mem_assert _ O a φᶜ hd⟩
  have key : ∀ x ∈ D.current.monopolarQuestion O a φ, {a ⊢[O] φᶜ} ≤ x → (a ⊢[O] φ) ∈ x := by
    intro x hx hk
    rcases (mem_monopolarQuestion _ O a φ).1 hx with rfl | ⟨-, hx⟩
    · exact absurd (hk rfl) h
    · exact hx
  rcases hd with rfl | hd
  · exact Set.mem_sInter.2 fun x hx ↦ key x hx.1 hx.2
  · exact key d hd.1 hd.2

/-- (28): After a monopolar question on `φ` and the response *no* by `a` with no rejection, if `a`'s
commitment relation is serial and `a` was not already committed to `φᶜ`, no world belongs to every
proposition of a resulting state. -/
theorem sInter_eq_empty_of_mem_current_no_monopolar [IsSerial (O a)]
    (h : (a ⊢[O] φᶜ) ∉ D.current.root) (hd : d ∈ ((D.monopolar O s a φ).no O a φ).current) :
    ⋂₀ d = ∅ :=
  let ⟨h₁, h₂⟩ := D.mem_of_mem_current_no_monopolar O s a φ h hd
  Set.eq_empty_of_forall_notMem fun _ hw ↦
    Set.disjoint_left.1 disjoint_committed_compl (hw _ h₁) (hw _ h₂)

/-- (24): After a bipolar question on `φ`, the response *no* by `a` leads to the space that `a`'s
commitment to `φᶜ` alone leads to. -/
theorem current_no_bipolar :
    ((D.bipolar O s a φ).no O a φ).current = D.current.assert O a φᶜ :=
  update_question_of_mem _ (.inr rfl)

-- (24a)
theorem current_yes_bipolar :
    ((D.bipolar O s a φ).yes O a φ).current = D.current.assert O a φ :=
  update_question_of_mem _ (.inl rfl)

-- (28a)
theorem current_yes_monopolar :
    ((D.monopolar O s a φ).yes O a φ).current = D.current.assert O a φ :=
  update_question_of_mem _ rfl

end Development

/-! ### The commitment space of a Table -/

section Table

variable {A W I : Type*} (K : Table A W I) (ans : I → Set (Set W)) (a : A) (p : Set W) (i : I)
  {d : (Filter W)ᵒᵈ}

/-- The **commitment space** of a Table has the common ground as its root and, as its other members,
the filters that refine the common ground and contain an answer of every item on the stack. -/
def toSpace : Space (Filter W)ᵒᵈ :=
  (Space.Ici (toDual K.commonGround)).restrict
    {g | ∀ i ∈ K.stack, ∃ q ∈ ans i, q ∈ ofDual g}

@[simp] theorem root_toSpace : (toSpace K ans).root = toDual K.commonGround := rfl

theorem mem_toSpace : d ∈ toSpace K ans ↔ d = toDual K.commonGround ∨
    ofDual d ≤ K.commonGround ∧ ∀ i ∈ K.stack, ∃ q ∈ ans i, q ∈ ofDual d := Iff.rfl

theorem exists_toDual_principal_le_iff (H : Set (Set W)) :
    (∃ k ∈ (fun q ↦ toDual (𝓟 q)) '' H, k ≤ d) ↔ ∃ q ∈ H, q ∈ ofDual d := by
  simp only [Set.mem_image, exists_exists_and_eq_and]
  exact exists_congr fun q ↦ and_congr_right fun _ ↦ le_principal_iff

/-- Placing an item on the Table is the question whose proposals are the answers of the item. -/
theorem toSpace_push :
    toSpace (K.push i) ans = (toSpace K ans).question ((fun q ↦ toDual (𝓟 q)) '' ans i) := by
  ext d
  rw [Space.mem_question, exists_toDual_principal_le_iff, mem_toSpace, mem_toSpace,
    Table.stack_push, List.forall_mem_cons, root_toSpace, Table.commonGround_push]
  tauto

@[simp] theorem toSpace_commit : toSpace (K.commit a p) ans = toSpace K ans := rfl

variable {K ans} in
-- making a joint commitment common ground is the update by its content
theorem toSpace_settle_of_stack_eq_nil (hK : K.stack = []) :
    toSpace (K.settle ans p) ans = (toSpace K ans).update (toDual (𝓟 p)) := by
  have hs : (K.settle ans p).stack = [] := Table.stack_settle_of_stack_eq_nil ans p hK
  have hmem : toDual (𝓟 p) ⊔ (toSpace K ans).root ∈ toSpace K ans :=
    (mem_toSpace K ans).2 (.inr ⟨inf_le_right, by simp [hK]⟩)
  ext d
  rw [Space.mem_update, Space.root_update_of_mem _ hmem, mem_toSpace, mem_toSpace, hs, hK]
  simp only [List.not_mem_nil, false_imp_iff, implies_true, and_true, Table.commonGround_settle,
    root_toSpace]
  constructor
  · rintro (rfl | h)
    · exact .inl (by rw [← toDual_inf, inf_comm])
    · exact .inr ⟨.inr (h.trans inf_le_left), toDual_le.2 (h.trans inf_le_right)⟩
  · rintro (rfl | ⟨hd, h⟩)
    · exact .inl (by rw [← toDual_inf, inf_comm])
    · exact .inr (le_inf (hd.elim (fun e ↦ e ▸ le_rfl) id) (toDual_le.1 h))

variable {K ans} in
-- the space is the root with everything below a projected common ground
theorem toDual_mem_toSpace_iff {g : Filter W} (hg : g ≠ ⊥) :
    toDual g ∈ toSpace K ans ↔ g = K.commonGround ∨ ∃ f ∈ K.projectedSet ans, g ≤ f := by
  rw [mem_toSpace, Table.exists_le_mem_projectedSet_iff hg]
  rfl

variable (K : Table A W (Set (Set W))) (b : A)

-- the assertion of the Table is a monopolar question on its content, with the commitment apart
theorem toSpace_assert :
    toSpace (K.assert a p) id = (toSpace K id).question {toDual (𝓟 p)} := by
  rw [Table.assert, toSpace_push, id, Set.image_singleton, toSpace_commit]

-- a negative answer to a polar question leads where the assertion alone would
theorem toSpace_assert_compl_polarQuestion :
    toSpace ((K.polarQuestion p).assert b pᶜ) id = toSpace (K.assert b pᶜ) id := by
  ext d
  simp only [mem_toSpace, Table.stack_assert, Table.stack_polarQuestion, List.forall_mem_cons,
    Table.commonGround_assert, Table.commonGround_polarQuestion, id, Set.mem_singleton_iff,
    Set.mem_insert_iff, exists_eq_left, exists_eq_or_imp]
  tauto

end Table

/-! ### Negation in questions -/

-- Figure 14, on states closed under consequence
theorem question_committed_compl_le {κ W : Type*} (O : κ → SetRel W W) (a : κ) (φ : Set W)
    [IsSerial (O a)] (C : Space (Filter W)ᵒᵈ) :
    C.question {toDual (𝓟 (a ⊢[O] φᶜ))} ≤ C.question {toDual (𝓟 (a ⊢[O] φ)ᶜ)} := by
  intro d hd
  rcases (Space.mem_question _).1 hd with rfl | ⟨hd, p, rfl, hle⟩
  · exact Space.root_mem _
  · exact (Space.mem_question _).2 (.inr ⟨hd, _, rfl, le_trans (toDual_le_toDual.2
      (principal_mono.2 (Set.subset_compl_iff_disjoint_left.2 disjoint_committed_compl))) hle⟩)

end Krifka2015
