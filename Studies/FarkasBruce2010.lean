module

public import Linglib.Discourse.Bias
public import Linglib.Discourse.Table.Basic

/-!
# Farkas & Bruce (2010): On Reacting to Assertions and Polar Questions

An item on the Table is the set of complete answers of a sentence: `{p}` for a declarative with
content `p` and `{p, pᶜ}` for the polar interrogative. A default assertion commits its author to
`p` and places `{p}` on the Table; a default polar question places `{p, pᶜ}` and commits no one.
Both raise the issue of the same sentence radical, and the responses to them overlap: a response
commits its author to the radical's content or to its negation. The two differ in the context they
leave. Every
common ground an assertion projects contains its content, so a response that commits its author
to the negation projects nothing consistent and leaves the conversation in crisis. A polar
question projects a common ground for each answer, so the same response projects what the
assertion of the negation would project by itself.

Confirmation by every participant makes the content a joint commitment, which then enters the
common ground and leaves the commitment lists; in a stable context the common ground reached is
the one the assertion projected, and no participant's total discourse commitment changes. After a
denial the participants may agree to disagree, which removes both items from the Table and keeps
both commitments: the common ground is as it was, and the two commitment lists are jointly
inconsistent.

## Implementation notes

* A conversation is in crisis when its common ground is inconsistent or every member of its
  projected set is. With the projected set derived from the Table, the first clause follows from
  the second.
* The total discourse commitment of a participant is the filter that the participant's commitment
  list generates, met with the common ground.
* A proposition is decided relative to a common ground when it or its negation follows, which is
  that the common ground has a nonzero bias on it.
* Agreeing to disagree requires a denial on top of the assertion it denies. The operation removes
  the two topmost items and does not check the precondition.

## TODO

* Confirming, reversing and responding moves, the relative polarity features and the polarity
  particles are defined by the sentence radical on top of the Table, which an item that is only
  a denotation does not record. The rows of `Data/Examples/FarkasBruce2010` are not paired with a
  prediction.
* The common-ground increasing operation is triggered inside any move that completes a joint
  commitment; here it is a separate operation.

## References

* [farkas-bruce-2010]
-/

@[expose] public section

namespace FarkasBruce2010

open Commitment Commitment.Table Filter
open scoped SetRel

variable {A W : Type*} (K : Table A W (Set (Set W))) (a b : A) (p : Set W) {f : Filter W}

/-! ### What assertions and polar questions project -/

variable {K p} in
-- (8)
theorem projectedSet_assert_of_stack_eq_nil (hK : K.stack = []) (hp : K.commonGround ⊓ 𝓟 p ≠ ⊥) :
    (K.assert a p).projectedSet id = {K.commonGround ⊓ 𝓟 p} := by
  rw [projectedSet_assert, projectedSet_of_stack_eq_nil hK]
  exact project_singleton hp

variable {K p} in
-- (11)
theorem projectedSet_polarQuestion_of_stack_eq_nil (hK : K.stack = [])
    (hp : K.commonGround ⊓ 𝓟 p ≠ ⊥) (hnp : K.commonGround ⊓ 𝓟 pᶜ ≠ ⊥) :
    (K.polarQuestion p).projectedSet id = {K.commonGround ⊓ 𝓟 p, K.commonGround ⊓ 𝓟 pᶜ} := by
  rw [projectedSet_polarQuestion, projectedSet_of_stack_eq_nil hK]
  exact project_pair hp hnp

variable {K a p} in
theorem mem_of_mem_projectedSet_assert (h : f ∈ (K.assert a p).projectedSet id) : p ∈ f :=
  let ⟨_, hq, hf⟩ := exists_mem_of_mem_project h
  Set.mem_singleton_iff.1 hq ▸ hf

variable {K a p} in
-- an assertion is categorically biased in favour of its content
theorem bias_eq_one_of_mem_projectedSet_assert (h : f ∈ (K.assert a p).projectedSet id) :
    f.bias p = 1 :=
  Filter.bias_eq_one_iff.2 (mem_of_mem_projectedSet_assert h)

variable {K p} in
-- the radical of a polar question is decided in each projected common ground
theorem bias_ne_zero_of_mem_projectedSet_polarQuestion
    (h : f ∈ (K.polarQuestion p).projectedSet id) : f.bias p ≠ 0 := fun h0 ↦ by
  obtain ⟨q, hq, hf⟩ := exists_mem_of_mem_project h
  rcases Set.mem_insert_iff.1 hq with rfl | hq
  · exact (Filter.bias_eq_zero_iff.1 h0).1 hf
  · exact (Filter.bias_eq_zero_iff.1 h0).2 (Set.mem_singleton_iff.1 hq ▸ hf)

/-! ### Confirmation -/

-- (17) after (16)
theorem settle_assert_self : (K.assert a p).settle id p = K.settle id p :=
  (settle_push_of_exists_mem (ans := id) (i := {p})
    ⟨p, Set.mem_singleton p, mem_inf_of_right (mem_principal_self p)⟩).trans
    (settle_commit_self K id a p)

theorem settle_polarQuestion_self : (K.polarQuestion p).settle id p = K.settle id p :=
  settle_push_of_exists_mem (ans := id) (i := {p, pᶜ})
    ⟨p, Set.mem_insert _ _, mem_inf_of_right (mem_principal_self p)⟩

variable {K p} in
/-- In a stable context, making an asserted proposition common ground reaches the common ground
the assertion projected. -/
theorem commonGround_settle_mem_projectedSet_assert (hK : K.stack = [])
    (hp : K.commonGround ⊓ 𝓟 p ≠ ⊥) :
    (K.settle id p).commonGround ∈ (K.assert a p).projectedSet id :=
  projectedSet_assert_of_stack_eq_nil a hK hp ▸ rfl

/-! ### Crisis -/

/-- A conversation is in crisis when its common ground or every projected common ground is
inconsistent. -/
def InCrisis : Prop := K.commonGround = ⊥ ∨ ∀ f ∈ K.projectedSet id, f = ⊥

theorem inCrisis_iff : InCrisis K ↔ ∀ f ∈ K.projectedSet id, f = ⊥ :=
  or_iff_right_of_imp fun hcg _ hf ↦
    le_bot_iff.1 ((le_commonGround_of_mem_projectedSet hf).trans_eq hcg)

variable {K} in
-- footnote 17
theorem inCrisis_iff_projectedSet_eq_empty (h : K.stack ≠ []) :
    InCrisis K ↔ K.projectedSet id = ∅ := by
  obtain ⟨_ | ⟨H, T⟩, C, cg⟩ := K
  · exact absurd rfl h
  · rw [inCrisis_iff, Set.eq_empty_iff_forall_notMem]
    exact forall_congr' fun f ↦ ⟨fun hf hmem ↦ bot_notMem_project (hf hmem ▸ hmem),
      fun hf hmem ↦ absurd hmem hf⟩

-- (21)
theorem projectedSet_assert_assert_compl :
    ((K.assert a p).assert b pᶜ).projectedSet id = ∅ :=
  Set.eq_empty_of_forall_notMem fun f hf ↦ by
    obtain ⟨⟨g, hg, q, hq, rfl⟩, hne⟩ := mem_project.1 hf
    rw [Set.mem_singleton_iff.1 hq] at hne
    exact hne (inf_principal_eq_bot.2 <| by
      rw [compl_compl]
      exact mem_of_mem_projectedSet_assert (K := K) (a := a) hg)

/-- A denied assertion leaves the conversation in crisis. -/
theorem inCrisis_assert_assert_compl : InCrisis ((K.assert a p).assert b pᶜ) :=
  (inCrisis_iff _).2 fun f hf ↦
    absurd (projectedSet_assert_assert_compl K a b p ▸ hf) (Set.notMem_empty f)

-- (24)
theorem projectedSet_assert_polarQuestion :
    ((K.polarQuestion p).assert b p).projectedSet id = (K.assert b p).projectedSet id := by
  change project (project (K.projectedSet id) {p, pᶜ}) {p} = project (K.projectedSet id) {p}
  rw [project_right_comm, project_pair_compl_of_forall_mem fun f hf ↦
      let ⟨_, hq, h⟩ := exists_mem_of_mem_project hf
      Set.mem_singleton_iff.1 hq ▸ h,
    Set.sdiff_singleton_eq_self bot_notMem_project]

-- (28)
theorem projectedSet_assert_compl_polarQuestion :
    ((K.polarQuestion p).assert b pᶜ).projectedSet id = (K.assert b pᶜ).projectedSet id := by
  rw [← polarQuestion_compl, projectedSet_assert_polarQuestion]

/-- A negative answer to a polar question leaves the conversation in crisis only if the assertion
alone would. -/
theorem inCrisis_assert_compl_polarQuestion_iff :
    InCrisis ((K.polarQuestion p).assert b pᶜ) ↔ InCrisis (K.assert b pᶜ) := by
  rw [inCrisis_iff, inCrisis_iff, projectedSet_assert_compl_polarQuestion]

/-! ### Total commitments and agreeing to disagree -/

private theorem generate_insert (S : Set (Set W)) (q : Set W) :
    Filter.generate (insert q S) = Filter.generate S ⊓ 𝓟 q := by
  rw [Set.insert_eq, Filter.generate_union, Filter.generate_singleton, inf_comm]

/-- The total discourse commitment of `a` is the body of information that `a`'s discourse
commitments generate together with the common ground. -/
def totalCommitment : Filter W := Filter.generate (K.commitments.contents a) ⊓ K.commonGround

theorem totalCommitment_commit_self :
    totalCommitment (K.commit a p) a = totalCommitment K a ⊓ 𝓟 p := by
  unfold totalCommitment
  rw [commitments_commit, State.contents_insert_self, generate_insert, commonGround_commit,
    inf_right_comm]

theorem totalCommitment_settle :
    totalCommitment (K.settle id p) a = totalCommitment K a ⊓ 𝓟 p := by
  have key : Filter.generate (K.commitments.contents a \ {p}) ⊓ 𝓟 p =
      Filter.generate (K.commitments.contents a) ⊓ 𝓟 p := by
    rw [← generate_insert, ← generate_insert, Set.insert_sdiff_singleton]
  unfold totalCommitment
  rw [contents_commitments_settle, commonGround_settle, inf_left_comm, key, inf_left_comm,
    inf_assoc]

variable {K a p} in
/-- Making a proposition common ground leaves the total discourse commitment of a participant
committed to it as it was. -/
theorem totalCommitment_settle_of_mem (h : p ∈ K.commitments.contents a) :
    totalCommitment (K.settle id p) a = totalCommitment K a :=
  (totalCommitment_settle K a p).trans <| inf_eq_left.2 <| le_principal_iff.2 <|
    mem_inf_of_left (Filter.GenerateSets.basic h)

/-- (23): Agreeing to disagree removes the denial and the assertion it denies from the Table. -/
def agreeToDisagree : Table A W (Set (Set W)) := { K with stack := K.stack.tail.tail }

theorem agreeToDisagree_assert_assert (q : Set W) :
    agreeToDisagree ((K.assert a p).assert b q) = (K.commit a p).commit b q := rfl

/-- After agreeing to disagree the common ground is as it was before the assertion and its
denial, and the discourse commitments of the two parties are jointly inconsistent. -/
theorem agreeToDisagree_assert_assert_compl :
    (agreeToDisagree ((K.assert a p).assert b pᶜ)).commonGround = K.commonGround ∧
      Filter.generate ((agreeToDisagree ((K.assert a p).assert b pᶜ)).commitments.contents a) ⊓
        Filter.generate ((agreeToDisagree ((K.assert a p).assert b pᶜ)).commitments.contents b)
          = ⊥ :=
  ⟨rfl, Filter.empty_mem_iff_bot.1 <| Set.inter_compl_self p ▸ inter_mem_inf
    (Filter.GenerateSets.basic (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    (Filter.GenerateSets.basic (Set.mem_insert _ _))⟩

end FarkasBruce2010
