module

public import Linglib.Discourse.Commitment.Proposition
public import Linglib.Discourse.Commitment.Space.Basic
public import Linglib.Discourse.Table.Basic

/-!
# Krifka (2015): Bias in Commitment Space Semantics

A *commitment state* is a filter on the set of worlds: the propositions the participants are
committed to, closed under consequence. A state with more commitments is a smaller filter, so the
states carry the dual order. For a proposition `q`, the state `stateOf q` consists of the
consequences of `q`. A commitment space is a set of states with a least element, and the acts of
this file are operations on commitment spaces.

A *commitment space development* is the record of a conversation: the commitment spaces it has
passed through, each with the participant whose move led to it. An act extends the record with
the space the act leads to. A *rejection* extends it with the space before the last move.

An assertion of `φ` by `s` is two acts by `s`: the update by `s`'s commitment to `φ`, and then
the update by `φ`. A bipolar question put to `a` proposes `a`'s commitment to `φ` or to `φᶜ`, a
monopolar question proposes `a`'s commitment to `φ` alone, and a question with high negation
proposes that `a` not be committed to `φ`. The responses *yes* and *no* are the updates by `a`'s
commitment to `φ` and to `φᶜ`.

The responses with *no* behave differently when no rejection comes first. After a bipolar
question, *no* leads to the space that the update alone leads to. After a monopolar question,
*no* leads only to the inconsistent state, if `a`'s commitment relation is serial. After an
assertion, *no* leads to states that contain `φ` and `a`'s commitment to `φᶜ`. The question with
high negation is weaker than the monopolar question on `φᶜ`.

An act *projects the commitment* of `k` on `φ` when every state it leads to, other than the root
it started from, contains `k`'s commitment to `φ` or to `φᶜ`. An assertion by `l` and a bipolar
question put to `l` both project the commitment of `l`. In the space of all states they project
the commitment of no one else, provided no participant's commitment to `φ` or to `φᶜ` entails
another's.

A Table determines a commitment space on the same states. Its root is the common ground of the
Table, and its other members are the filters that refine the common ground and contain an answer
of every item. Placing an item on the Table is then the question whose proposals are the states
of its answers. So a polar question of the Table on `p` and a bipolar question put to `a` are the
same operation, with the proposals `p` and `pᶜ` in the first case and `a`'s commitments to `φ`
and to `φᶜ` in the second. For an empty Table, moving a proposition to the common ground is the
update by that proposition.

## Implementation notes

In the source a commitment state is a set of propositions. Here it is the filter the set
generates. The comparison of the questions with low and high negation holds for filters and fails
for sets of propositions, where a state can contain `a ⊢[O] φᶜ` without containing the weaker
proposition `(a ⊢[O] φ)ᶜ`.

A development stores its first space and its moves, the most recent first. Rejecting a
development with fewer than two moves returns to the first space.

The update by `φ` in an assertion is defined on every space. The results do not assume that the
space admits it.

An index pairs a fact with a commitment set for each participant. Over indices no participant's
commitment to a fact or to its negation entails another's, which shows that the condition on
projected commitments can be met.

## TODO

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

/-! ### Commitment states -/

section State

variable {W : Type*} {q r : Set W} {d : (Filter W)ᵒᵈ}

/-- The **state of** `q` is the commitment state of the propositions that follow from `q`. -/
def stateOf (q : Set W) : (Filter W)ᵒᵈ := toDual (𝓟 q)

theorem stateOf_le : stateOf q ≤ d ↔ q ∈ ofDual d := le_principal_iff

theorem stateOf_le_stateOf : stateOf q ≤ stateOf r ↔ r ⊆ q := principal_mono

theorem stateOf_eq_toDual_top : stateOf q = toDual ⊤ ↔ q = Set.univ := by
  rw [stateOf, toDual_inj, ← principal_univ, principal_eq_iff_eq]

end State

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

variable {P W : Type*} (O : P → SetRel W W) (D : Development P (Filter W)ᵒᵈ) (s a : P)
  (φ : Set W) {d : (Filter W)ᵒᵈ}

/-- (19): The **assertion** of `φ` by `s` is the update by `s`'s commitment to `φ` followed by the
update by `φ`. -/
def assertion : Development P (Filter W)ᵒᵈ :=
  (D.act s (·.update (stateOf (s ⊢[O] φ)))).act s (·.update (stateOf φ))

/-- (20): The response **yes** by `a` is the update by `a`'s commitment to `φ`. -/
def yes : Development P (Filter W)ᵒᵈ := D.act a (·.update (stateOf (a ⊢[O] φ)))

/-- (20): The response **no** by `a` is the update by `a`'s commitment to `φᶜ`. -/
def no : Development P (Filter W)ᵒᵈ := D.act a (·.update (stateOf (a ⊢[O] φᶜ)))

/-- (23): The **bipolar question** by `s` to `a` proposes `a`'s commitment to `φ` or to `φᶜ`. -/
def bipolar : Development P (Filter W)ᵒᵈ :=
  D.act s (·.question {stateOf (a ⊢[O] φ), stateOf (a ⊢[O] φᶜ)})

/-- (27): The **monopolar question** by `s` to `a` proposes `a`'s commitment to `φ`. -/
def monopolar : Development P (Filter W)ᵒᵈ := D.act s (·.question {stateOf (a ⊢[O] φ)})

/-- (39): The question with **high negation** by `s` to `a` proposes that `a` not be committed to
`φ`. -/
def highNegation : Development P (Filter W)ᵒᵈ := D.act s (·.question {stateOf (a ⊢[O] φ)ᶜ})

-- (22), with the rejection
theorem current_no_reject_assertion :
    (((D.assertion O s φ).reject a).no O a φ).current =
      (D.current.update (stateOf (s ⊢[O] φ))).update (stateOf (a ⊢[O] φᶜ)) := rfl

/-- (22): After an assertion of `φ` and the response *no* by `a` with no rejection, every resulting
state contains `φ` and `a`'s commitment to `φᶜ`. -/
theorem mem_of_mem_current_no_assertion (hd : d ∈ ((D.assertion O s φ).no O a φ).current) :
    φ ∈ ofDual d ∧ (a ⊢[O] φᶜ) ∈ ofDual d :=
  ⟨stateOf_le.1 ((le_root_update _ _).trans (root_le_of_mem_update _ hd)),
    stateOf_le.1 (le_of_mem_update _ hd)⟩

-- (28b), the commitment the question proposed
theorem stateOf_committed_le_of_mem_current_no_monopolar
    (h : (a ⊢[O] φᶜ) ∉ ofDual D.current.root)
    (hd : d ∈ ((D.monopolar O s a φ).no O a φ).current) : stateOf (a ⊢[O] φ) ≤ d := by
  have key : ∀ x ∈ D.current.question {stateOf (a ⊢[O] φ)},
      stateOf (a ⊢[O] φᶜ) ≤ x → stateOf (a ⊢[O] φ) ≤ x := by
    intro x hx hk
    rcases (mem_question _).1 hx with rfl | ⟨-, p, rfl, hp⟩
    · exact absurd (stateOf_le.1 hk) h
    · exact hp
  rcases hd with rfl | hd
  · exact le_sInf fun x hx ↦ key x hx.1 hx.2
  · exact key d hd.1 hd.2

/-- (28): After a monopolar question on `φ` and the response *no* by `a` with no rejection, if
`a`'s commitment relation is serial and `a` was not already committed to `φᶜ`, every resulting
state is inconsistent. -/
theorem eq_bot_of_mem_current_no_monopolar [IsSerial (O a)]
    (h : (a ⊢[O] φᶜ) ∉ ofDual D.current.root)
    (hd : d ∈ ((D.monopolar O s a φ).no O a φ).current) : ofDual d = ⊥ :=
  empty_mem_iff_bot.1 <| (disjoint_committed_compl (O := O) (k := a) (φ := φ)).inter_eq ▸ inter_mem
    (stateOf_le.1 (D.stateOf_committed_le_of_mem_current_no_monopolar O s a φ h hd))
    (stateOf_le.1 (le_of_mem_update _ hd))

/-- (24): After a bipolar question on `φ`, the response *no* by `a` leads to the space that the
update by `a`'s commitment to `φᶜ` alone leads to. -/
theorem current_no_bipolar :
    ((D.bipolar O s a φ).no O a φ).current = D.current.update (stateOf (a ⊢[O] φᶜ)) :=
  update_question_of_mem _ (.inr rfl)

-- (24a)
theorem current_yes_bipolar :
    ((D.bipolar O s a φ).yes O a φ).current = D.current.update (stateOf (a ⊢[O] φ)) :=
  update_question_of_mem _ (.inl rfl)

-- (28a)
theorem current_yes_monopolar :
    ((D.monopolar O s a φ).yes O a φ).current = D.current.update (stateOf (a ⊢[O] φ)) :=
  update_question_of_mem _ rfl

-- Figure 14: the question with high negation is weaker than the monopolar question on `φᶜ`
theorem current_monopolar_compl_le_current_highNegation [IsSerial (O a)] :
    (D.monopolar O s a φᶜ).current ≤ (D.highNegation O s a φ).current := by
  intro d hd
  rcases (mem_question _).1 hd with rfl | ⟨hd, p, rfl, hle⟩
  · exact root_mem _
  · exact (mem_question _).2 (.inr ⟨hd, _, rfl, le_trans (stateOf_le_stateOf.2
      (Set.subset_compl_iff_disjoint_left.2 disjoint_committed_compl)) hle⟩)

end Development

/-! ### The participant whose commitment an act projects -/

section Projects

variable {κ W : Type*} (C : Space (Filter W)ᵒᵈ) (O : κ → SetRel W W) (k l : κ) (φ : Set W)

/-- (30): An act that takes `C` to `D` **projects the commitment** of `k` on `φ` when every member
of `D` other than the root of `C` contains `k ⊢[O] φ` or `k ⊢[O] φᶜ`. -/
def ProjectsCommitment (D : Space (Filter W)ᵒᵈ) : Prop :=
  ∀ d ∈ D, d ≠ C.root → stateOf (k ⊢[O] φ) ≤ d ∨ stateOf (k ⊢[O] φᶜ) ≤ d

theorem projectsCommitment_update :
    ProjectsCommitment C O k φ (C.update (stateOf (k ⊢[O] φ))) := fun _ hd _ ↦
  .inl (le_of_mem_update _ hd)

theorem projectsCommitment_question :
    ProjectsCommitment C O k φ (C.question {stateOf (k ⊢[O] φ), stateOf (k ⊢[O] φᶜ)}) := by
  intro d hd hne
  obtain ⟨-, p, hp, hle⟩ := ((mem_question _).1 hd).resolve_left hne
  rcases Set.mem_insert_iff.1 hp with rfl | hp
  · exact .inl hle
  · exact .inr (Set.mem_singleton_iff.1 hp ▸ hle)

variable {O k l φ}

/-- In the space of all states, if no participant's commitment to `φ` or to `φᶜ` entails
another's and `l`'s commitment to `φ` is not trivial, an assertion by `l` projects the commitment
of `k` exactly when `k = l`, and so does a bipolar question put to `l`. -/
theorem projectsCommitment_Ici_iff
    (hO : ∀ ⦃k l : κ⦄ ⦃b b' : Bool⦄, (l ⊢[O] (bif b then φ else φᶜ)) ⊆
      (k ⊢[O] (bif b' then φ else φᶜ)) → k = l ∧ b = b')
    (hl : (l ⊢[O] φ) ≠ Set.univ) :
    (ProjectsCommitment (Space.Ici (toDual ⊤)) O k φ
        ((Space.Ici (toDual ⊤)).update (stateOf (l ⊢[O] φ))) ↔ k = l) ∧
      (ProjectsCommitment (Space.Ici (toDual ⊤)) O k φ
        ((Space.Ici (toDual ⊤)).question {stateOf (l ⊢[O] φ), stateOf (l ⊢[O] φᶜ)}) ↔
          k = l) := by
  have hne : stateOf (l ⊢[O] φ) ≠ (Space.Ici (toDual (⊤ : Filter W))).root := fun e ↦
    hl (stateOf_eq_toDual_top.1 e)
  have hmem : stateOf (l ⊢[O] φ) ∈ Space.Ici (toDual (⊤ : Filter W)) :=
    show (toDual ⊤ : (Filter W)ᵒᵈ) ≤ toDual (𝓟 (l ⊢[O] φ)) from toDual_le_toDual.2 le_top
  have key : stateOf (k ⊢[O] φ) ≤ stateOf (l ⊢[O] φ) ∨
      stateOf (k ⊢[O] φᶜ) ≤ stateOf (l ⊢[O] φ) → k = l := by
    rintro (h | h)
    · exact (hO (b := true) (b' := true) (stateOf_le_stateOf.1 h)).1
    · exact (hO (b := true) (b' := false) (stateOf_le_stateOf.1 h)).1
  refine ⟨⟨fun h ↦ key (h _ (.inr ⟨hmem, Set.mem_Ici.2 le_rfl⟩) hne), ?_⟩,
    ⟨fun h ↦ key (h _ ((mem_question _).2 (.inr ⟨hmem, _, .inl rfl, le_rfl⟩)) hne), ?_⟩⟩
  · rintro rfl
    exact projectsCommitment_update _ O k φ
  · rintro rfl
    exact projectsCommitment_question _ O k φ

end Projects

/-! ### A model in which commitments vary -/

/-- An **index** is a fact together with a nonempty commitment set for each participant. -/
structure Index (κ F : Type*) where
  /-- The fact at the index. -/
  fact : F
  /-- The facts compatible with what `k` is committed to. -/
  commitmentSet : κ → Set F
  commitmentSet_nonempty : ∀ k, (commitmentSet k).Nonempty

namespace Index

variable {κ F : Type*} {k l : κ}

/-- The **accessibility** of `k` relates an index to the indices with the same commitment sets whose
fact belongs to the commitment set of `k`. -/
def access : κ → SetRel (Index κ F) (Index κ F) :=
  fun k ↦ {p | p.2.fact ∈ p.1.commitmentSet k ∧ p.2.commitmentSet = p.1.commitmentSet}

theorem committed_access_preimage (φ : Set F) :
    (k ⊢[access] (fact ⁻¹' φ)) = {w : Index κ F | w.commitmentSet k ⊆ φ} :=
  Set.ext fun w ↦ ⟨fun h x hx ↦ h (b := ⟨x, w.commitmentSet, w.commitmentSet_nonempty⟩) ⟨hx, rfl⟩,
    fun h _ hv ↦ h hv.1⟩

-- over indices, no participant's commitment to a fact or its negation entails another's
theorem eq_of_committed_access_subset [DecidableEq κ] ⦃k l : κ⦄ ⦃b b' : Bool⦄
    (h : (l ⊢[access (F := Bool)] (bif b then fact ⁻¹' {true} else (fact ⁻¹' {true})ᶜ)) ⊆
      (k ⊢[access] (bif b' then fact ⁻¹' {true} else (fact ⁻¹' {true})ᶜ))) :
    k = l ∧ b = b' := by
  have hX (b : Bool) : (bif b then fact ⁻¹' {true} else (fact ⁻¹' {true})ᶜ :
      Set (Index κ Bool)) = fact ⁻¹' {b} := by
    cases b <;> ext <;> simp
  simp only [hX, committed_access_preimage] at h
  let w : Index κ Bool :=
    ⟨b, fun q ↦ if q = l then {b} else Set.univ, fun q ↦ by split_ifs <;> simp⟩
  have hw : w.commitmentSet k ⊆ {b'} := h (show w.commitmentSet l ⊆ {b} by simp [w])
  by_cases hk : k = l
  · subst hk
    exact ⟨rfl, by simpa [w] using hw⟩
  · exact absurd (hw (show (!b') ∈ w.commitmentSet k by simp [w, hk])) (by simp)

theorem committed_access_ne_univ :
    (l ⊢[access (F := Bool)] (fact ⁻¹' {true})) ≠ Set.univ := fun e ↦ by
  rw [committed_access_preimage] at e
  have h := (Set.ext_iff.1 e ⟨true, fun _ ↦ Set.univ, fun _ ↦ ⟨true, trivial⟩⟩).2 trivial
  exact absurd (h (Set.mem_univ false)) (by simp)

end Index

-- over indices, a bipolar question put to one participant does not project the other's commitment
example : ¬ ProjectsCommitment (Space.Ici (toDual ⊤)) (Index.access (F := Bool)) false
    (Index.fact ⁻¹' {true}) ((Space.Ici (toDual ⊤)).question
      {stateOf (true ⊢[Index.access] (Index.fact ⁻¹' {true})),
        stateOf (true ⊢[Index.access] (Index.fact ⁻¹' {true})ᶜ)}) := fun h ↦
  absurd ((projectsCommitment_Ici_iff Index.eq_of_committed_access_subset
    Index.committed_access_ne_univ).2.1 h) (by decide)

/-! ### The commitment space of a Table -/

section Table

variable {A W I : Type*} (K : Table A W I) (ans : I → Set (Set W)) (a : A) (p : Set W) (i : I)
  {d : (Filter W)ᵒᵈ}

/-- The **commitment space** of a Table has the common ground as its root and, as its other
members, the filters that refine the common ground and contain an answer of every item on the
stack. -/
def toSpace : Space (Filter W)ᵒᵈ :=
  (Space.Ici (toDual K.commonGround)).restrict
    {g | ∀ i ∈ K.stack, ∃ q ∈ ans i, q ∈ ofDual g}

@[simp] theorem root_toSpace : (toSpace K ans).root = toDual K.commonGround := rfl

theorem mem_toSpace : d ∈ toSpace K ans ↔ d = toDual K.commonGround ∨
    ofDual d ≤ K.commonGround ∧ ∀ i ∈ K.stack, ∃ q ∈ ans i, q ∈ ofDual d := Iff.rfl

theorem exists_stateOf_le_iff (H : Set (Set W)) :
    (∃ k ∈ stateOf '' H, k ≤ d) ↔ ∃ q ∈ H, q ∈ ofDual d := by
  simp only [Set.mem_image, exists_exists_and_eq_and]
  exact exists_congr fun q ↦ and_congr_right fun _ ↦ stateOf_le

/-- Placing an item on the Table is the question whose proposals are the states of the answers of
the item. -/
theorem toSpace_push :
    toSpace (K.push i) ans = (toSpace K ans).question (stateOf '' ans i) := by
  ext d
  rw [Space.mem_question, exists_stateOf_le_iff, mem_toSpace, mem_toSpace,
    Table.stack_push, List.forall_mem_cons, root_toSpace, Table.commonGround_push]
  tauto

@[simp] theorem toSpace_commit : toSpace (K.commit a p) ans = toSpace K ans := rfl

theorem toSpace_map {J : Type*} (g : I → J) (ans : J → Set (Set W)) :
    toSpace (K.map g) ans = toSpace K (ans ∘ g) := by
  ext d
  simp [mem_toSpace]

variable {K ans} in
-- making a joint commitment common ground is the update by its content
theorem toSpace_settle_of_stack_eq_nil (hK : K.stack = []) :
    toSpace (K.settle ans p) ans = (toSpace K ans).update (stateOf p) := by
  have hs : (K.settle ans p).stack = [] := Table.stack_settle_of_stack_eq_nil ans p hK
  have hmem : stateOf p ⊔ (toSpace K ans).root ∈ toSpace K ans :=
    (mem_toSpace K ans).2 (.inr ⟨inf_le_right, by simp [hK]⟩)
  ext d
  rw [Space.mem_update, Space.root_update_of_mem _ hmem, mem_toSpace, mem_toSpace, hs, hK]
  simp only [List.not_mem_nil, false_imp_iff, implies_true, and_true, Table.commonGround_settle,
    root_toSpace, stateOf]
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
    toSpace (K.assert a p) id = (toSpace K id).question {stateOf p} := by
  rw [Table.assert, toSpace_push, id, Set.image_singleton, toSpace_commit]

-- the polar question of the Table is a question with the proposals `p` and `pᶜ`
theorem toSpace_polarQuestion :
    toSpace (K.polarQuestion p) id = (toSpace K id).question {stateOf p, stateOf pᶜ} := by
  rw [Table.polarQuestion, toSpace_push, id, Set.image_pair]

-- a negative answer to a polar question leads where the assertion alone would
theorem toSpace_assert_compl_polarQuestion :
    toSpace ((K.polarQuestion p).assert b pᶜ) id = toSpace (K.assert b pᶜ) id := by
  ext d
  simp only [mem_toSpace, Table.stack_assert, Table.stack_polarQuestion, List.forall_mem_cons,
    Table.commonGround_assert, Table.commonGround_polarQuestion, id, Set.mem_singleton_iff,
    Set.mem_insert_iff, exists_eq_left, exists_eq_or_imp]
  tauto

end Table

end Krifka2015
