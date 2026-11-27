module

public import Linglib.Discourse.Commitment.Space.Semantics
public import Linglib.Discourse.Table.Basic

/-!
# Krifka (2015): Bias in Commitment Space Semantics

A conversation is recorded as a commitment space development, the sequence of commitment spaces
its moves have led through, each with its actor. An act extends the record with the space it
leads to, and a rejection extends it with the space before the last move. An assertion of `φ` by
`s` is two acts: `s`'s commitment `s ⊢[O] φ`, and then `φ` itself, which the addressee may
reject. A polar question put to `a` is a meta-speech act that keeps the root and proposes `a`'s
commitment to `φ`, alone in a monopolar question and beside `a`'s commitment to `φᶜ` in a bipolar
one. The responses *yes* and *no* are `a`'s assertions of `φ` and of `φᶜ`.

The responses differ in whether they need a rejection first. A *no* to a bipolar question leads
where the bare assertion of `φᶜ` would. A *no* to a monopolar question leads to states that hold
`a`'s commitments to `φ` and to `φᶜ`, which no world satisfies when `a`'s commitments are
consistent. A *no* to an assertion leads to states that hold `φ` and `a`'s commitment to `φᶜ`, at
whose worlds `a`'s commitments exclude every world of the state. After a rejection, the *no* to
an assertion leaves `s`'s commitment to `φ` beside `a`'s commitment to `φᶜ`, without `φ`.

The last stage of a development corresponds to the Table of Farkas and Bruce. A Table presents a
commitment space whose root is its common ground and whose continuations are the bodies of
information that refine the common ground and entail an answer of every item on the Table; besides
the root, these are the bodies of information below a projected common ground. Placing an item on
the Table is then the question that proposes each complete answer of the item, so the assertion of
the Table is a monopolar question on its content with the speaker's commitment recorded apart, and
in a stable context the operation that makes a joint commitment common ground is the update by its
content.

## Implementation notes

* The commitment space of a Table has filters as states, where the acts of the paper are stated on
  sets of propositions. A filter is a set of propositions closed under consequence, and with more
  information it is smaller, so the states are ordered by the dual order.

* A development records its initial space and its moves, the most recent first. The rejection of a
  development with fewer than two moves returns to the initial space.
* The paper calls a state that holds `φ` and `a`'s commitment to `φᶜ` incoherent without defining
  the term. What is proved of such a state is that at each of its worlds no world `a`'s
  commitments leave open is a world of the state.
* The content `φ` of an assertion is added by the general update of a commitment space, which
  is defined on every space; the theorems hold whether or not the space admits the update.

## TODO

* The high-negation question proposes that `a` not be committed to `φ`. That it is weaker than the
  low-negation question, which proposes `a`'s commitment to `φᶜ`, is proved for states closed
  under consequence. On sets of propositions, where the acts of a development are stated, a state
  that contains `a ⊢[O] φᶜ` need not contain the weaker proposition `(a ⊢[O] φ)ᶜ`, and the
  high-negation question is not defined as an act of a development.
* The acceptability of questions with no, low and high negation by contextual evidence, the
  response *I don't know*, alternative and constituent questions, and question tags are not
  formalized, and the paper's examples are not in `Data/Examples`.
* The commitment space of a Table does not represent the discourse commitments of the
  participants, which the paper places in the state as propositions, and making a joint
  commitment common ground is related to the update only for a stable context.

## References

* [M. Krifka, *Bias in Commitment Space Semantics: Declarative Questions, Negated Questions,
  and Question Tags* (2015)][krifka-2015]
* [A. Cohen and M. Krifka, *Superlative quantifiers and meta-speech acts*
  (2014)][cohen-krifka-2014]
* [D. F. Farkas and K. B. Bruce, *On Reacting to Assertions and Polar Questions*
  (2010)][farkas-bruce-2010]
-/

@[expose] public section

namespace Krifka2015

open Commitment Commitment.Space ModalLogic Filter OrderDual
open scoped SetRel

/-- (8)–(9): A commitment space development records the spaces a conversation has led through,
each with the participant whose move led to it. -/
structure Development (P S : Type*) [LE S] where
  /-- The commitment space the record starts from. -/
  initial : Space S
  /-- The moves made, the most recent first, each with its actor and the space it led to. -/
  moves : List (P × Space S)

namespace Development

section

variable {P S : Type*} [LE S] (D : Development P S) (a b : P) (f : Space S → Space S)

/-- The space the last move led to. -/
def current : Space S := (D.moves.head?.map Prod.snd).getD D.initial

/-- The space before the last move. -/
def previous : Space S := (D.moves.tail.head?.map Prod.snd).getD D.initial

/-- (9): An act by `a` extends the record with the space the act leads to. -/
def act : Development P S := ⟨D.initial, (a, f D.current) :: D.moves⟩

/-- (10): A rejection by `a` extends the record with the space before the last move. -/
def reject : Development P S := ⟨D.initial, (a, D.previous) :: D.moves⟩

@[simp] theorem current_act : (D.act a f).current = f D.current := rfl

@[simp] theorem previous_act : (D.act a f).previous = D.current := rfl

@[simp] theorem current_reject : (D.reject a).current = D.previous := rfl

end

variable {P W : Type*} (O : P → SetRel W W) (D : Development P (Set (Set W))) (s a : P)
  (φ : Set W) {d : Set (Set W)}

/-- (19): In an assertion `s` commits to `φ`, and then `φ` itself is added. -/
def assertion : Development P (Set (Set W)) :=
  (D.act s (·.assert O s φ)).act s (·.update {φ})

/-- (20): *Yes* is `a`'s assertion of `φ`. -/
def yes : Development P (Set (Set W)) := D.act a (·.assert O a φ)

/-- (20): *No* is `a`'s assertion of `φᶜ`. -/
def no : Development P (Set (Set W)) := D.act a (·.assert O a φᶜ)

/-- (23): A bipolar question by `s` proposes `a`'s commitment to `φ` or to `φᶜ`. -/
def bipolar : Development P (Set (Set W)) := D.act s (·.bipolarQuestion O a φ)

/-- (27): A monopolar question by `s` proposes `a`'s commitment to `φ`. -/
def monopolar : Development P (Set (Set W)) := D.act s (·.monopolarQuestion O a φ)

/-- (22): After a rejection, a *no* to an assertion leaves the speaker's commitment to the content
beside the addressee's commitment to its negation, without the content. -/
theorem current_no_reject_assertion :
    (((D.assertion O s φ).reject a).no O a φ).current =
      (D.current.assert O s φ).assert O a φᶜ := rfl

-- (22), the state the rejection avoids
theorem mem_of_mem_current_no_assertion (hd : d ∈ ((D.assertion O s φ).no O a φ).current) :
    φ ∈ d ∧ (a ⊢[O] φᶜ) ∈ d :=
  ⟨Set.singleton_subset_iff.1 <|
      (le_root_update _ _).trans (root_le_of_mem_update _ hd),
    committed_mem_of_mem_assert _ O a φᶜ hd⟩

/-- Without a rejection, a *no* to an assertion leads to states at whose worlds the addressee's
commitments leave open no world of the state. -/
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

/-- (28): Without a rejection, a *no* to a monopolar question leads to states that no world
satisfies, when the addressee's commitments are consistent and the answer is new. -/
theorem sInter_eq_empty_of_mem_current_no_monopolar [IsSerial (O a)]
    (h : (a ⊢[O] φᶜ) ∉ D.current.root) (hd : d ∈ ((D.monopolar O s a φ).no O a φ).current) :
    ⋂₀ d = ∅ :=
  let ⟨h₁, h₂⟩ := D.mem_of_mem_current_no_monopolar O s a φ h hd
  Set.eq_empty_of_forall_notMem fun _ hw ↦
    Set.disjoint_left.1 disjoint_committed_compl (hw _ h₁) (hw _ h₂)

/-- (24): A *no* to a bipolar question leads where the assertion alone would. -/
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

/-- The commitment space a Table presents has the common ground as its root and, as
continuations, the bodies of information that refine the common ground and entail an answer of
every item on the Table. Its states are filters, ordered so that a state with more information is
higher. -/
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

/-- Placing an item on the Table is the question that proposes each of its complete answers. -/
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
