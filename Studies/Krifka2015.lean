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
information that refine the common ground and decide every issue on the Table; besides the root,
these are the bodies of information below a projected common ground. Placing an issue on the Table
is then the question that proposes each complete answer of the issue, so the assertion of the
Table is a monopolar question on its content with the speaker's commitment recorded apart, and in
a stable context the operation that makes a joint commitment common ground is the update by its
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
  under consequence; the acts of a development are stated on sets of propositions, where a state
  that contains `a ⊢[O] φᶜ` need not contain the weaker proposition `(a ⊢[O] φ)ᶜ`.
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
open Inquisitive Inquisitive.Proposition
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

theorem current_reject_act : ((D.act a f).reject b).current = D.current := rfl

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

/-- (39): A high-negation question by `s` proposes that `a` not be committed to `φ`. -/
def highNegation : Development P (Set (Set W)) := D.act s (·.question {{(a ⊢[O] φ)ᶜ}})

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

variable {A W : Type*} (K : Table A W) (a : A) (p : Set W) (P : Proposition (Set W))
  {d : (Filter W)ᵒᵈ}

/-- The commitment space a Table presents has the common ground as its root and, as
continuations, the bodies of information that refine the common ground and decide every issue on
the Table. Its states are filters, ordered so that a state with more information is higher. -/
def toSpace : Space (Filter W)ᵒᵈ :=
  (Space.Ici (toDual K.commonGround)).restrict {g | ∀ P ∈ K.stack, P.DecidedBy (ofDual g)}

@[simp] theorem root_toSpace : (toSpace K).root = toDual K.commonGround := rfl

theorem mem_toSpace : d ∈ toSpace K ↔ d = toDual K.commonGround ∨
    ofDual d ≤ K.commonGround ∧ ∀ P ∈ K.stack, P.DecidedBy (ofDual d) := Iff.rfl

theorem exists_toDual_principal_le_iff :
    (∃ k ∈ (fun q ↦ toDual (𝓟 q)) '' alt P, k ≤ d) ↔ P.DecidedBy (ofDual d) := by
  simp only [Set.mem_image, exists_exists_and_eq_and, DecidedBy]
  exact exists_congr fun q ↦ and_congr_right fun _ ↦ le_principal_iff

/-- Placing an issue on the Table is the question that proposes each of its complete answers. -/
theorem toSpace_push :
    toSpace (K.push P) = (toSpace K).question ((fun q ↦ toDual (𝓟 q)) '' alt P) := by
  ext d
  rw [Space.mem_question, exists_toDual_principal_le_iff, mem_toSpace, mem_toSpace,
    Table.stack_push, List.forall_mem_cons, root_toSpace, Table.commonGround_push]
  tauto

@[simp] theorem toSpace_commit : toSpace (K.commit a p) = toSpace K := rfl

-- the assertion of the Table is a monopolar question on its content, with the commitment apart
theorem toSpace_assert : toSpace (K.assert a p) = (toSpace K).question {toDual (𝓟 p)} := by
  rw [Table.assert, toSpace_push, alt_ofSet, Set.image_singleton, toSpace_commit]

-- a negative answer to a polar question leads where the assertion alone would
theorem toSpace_assert_compl_polarQuestion (b : A) :
    toSpace ((K.polarQuestion p).assert b pᶜ) = toSpace (K.assert b pᶜ) := by
  ext d
  simp only [mem_toSpace, Table.stack_assert, Table.stack_polarQuestion, List.forall_mem_cons,
    decidedBy_ofSet, decidedBy_polar, Table.commonGround_assert, Table.commonGround_polarQuestion]
  tauto

variable {K} in
-- making a joint commitment common ground is the update by its content
theorem toSpace_settle_of_isStable (hK : K.IsStable) :
    toSpace (K.settle p) = (toSpace K).update (toDual (𝓟 p)) := by
  have hs : (K.settle p).stack = [] := Table.isStable_settle_of_isStable p hK
  have hk : K.stack = [] := hK
  have hmem : toDual (𝓟 p) ⊔ (toSpace K).root ∈ toSpace K :=
    (mem_toSpace K).2 (.inr ⟨inf_le_right, by simp [hk]⟩)
  ext d
  rw [Space.mem_update, Space.root_update_of_mem _ hmem, mem_toSpace, mem_toSpace, hs, hk]
  simp only [List.not_mem_nil, false_imp_iff, implies_true, and_true, Table.commonGround_settle,
    root_toSpace]
  constructor
  · rintro (rfl | h)
    · exact .inl (by rw [← toDual_inf, inf_comm])
    · exact .inr ⟨.inr (h.trans inf_le_left), toDual_le.2 (h.trans inf_le_right)⟩
  · rintro (rfl | ⟨hd, h⟩)
    · exact .inl (by rw [← toDual_inf, inf_comm])
    · exact .inr (le_inf (hd.elim (fun e ↦ e ▸ le_rfl) id) (toDual_le.1 h))

variable {K} in
-- the space is the root with everything below a projected common ground
theorem toDual_mem_toSpace_iff {g : Filter W} (hg : g ≠ ⊥) :
    toDual g ∈ toSpace K ↔ g = K.commonGround ∨ ∃ f ∈ K.projectedSet, g ≤ f := by
  rw [mem_toSpace, Table.exists_le_mem_projectedSet_iff hg]
  rfl

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
