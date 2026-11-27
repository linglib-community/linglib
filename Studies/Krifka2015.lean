module

public import Linglib.Discourse.Commitment.Space.Semantics

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

## Implementation notes

* A development records its initial space and its moves, the most recent first. The rejection of a
  development with fewer than two moves returns to the initial space.
* The paper calls a state that holds `φ` and `a`'s commitment to `φᶜ` incoherent without defining
  the term. What is proved of such a state is that at each of its worlds no world `a`'s
  commitments leave open is a world of the state.
* The content `φ` of an assertion is added by the general update of a commitment space, which
  is defined on every space; the theorems hold whether or not the space admits the update.

## TODO

* The high-negation question proposes that `a` not be committed to `φ`. Its being weaker than the
  low-negation question, which proposes `a`'s commitment to `φᶜ`, needs states closed under
  consequence: a set of propositions that contains `a ⊢[O] φᶜ` need not contain the weaker
  proposition `(a ⊢[O] φ)ᶜ`.
* The acceptability of questions with no, low and high negation by contextual evidence, the
  response *I don't know*, alternative and constituent questions, and question tags are not
  formalized, and the paper's examples are not in `Data/Examples`.
* The paper relates the last stage of a development to the Table of Farkas and Bruce. No map from
  developments to Tables is defined; the Table's counterpart of the bipolar result is that a
  negative answer to a polar question projects what the assertion alone would.

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

open Commitment Commitment.Space ModalLogic
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

end Krifka2015
