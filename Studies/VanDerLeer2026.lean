module

public import Linglib.Discourse.Commitment.Space
public import Linglib.Discourse.Commitment.Frame

/-!
# van der Leer 2026: Speech Act Logic

Van der Leer's Speech Act Logic is a propositional dynamic logic of speech acts over the
commitment states of `Commitment.Frame`, in which belief `B_a` and commitment `C_{a,b}` are
modal operators. An assertion is the update `c⌈π⌉_{a,b}` that creates a commitment, Krifka's
performative update, which Sincerity and Competence pass on to beliefs, so that common belief
and commitment stay apart, as Bary demands. The projected discourse is a commitment space in
the sense of Cohen and Krifka, a root state together with its cooperative continuations, which
the speech acts transform. An assertion narrows the root and keeps the continuations in which
the addressee confirms, a question keeps the root and the continuations in which the addressee
answers, and a denegation removes the continuations the denegated act reaches. Cooperativity,
admissibility and possibility of a speech act are the three levels of the thesis's hierarchy of
discourse expectations, in which a cooperative act is admissible and every act is possible, but
not conversely.

## Main statements

* `committed_assert`, `committed_update`: an assertion commits the speaker, and a commitment at
  the root survives every later speech act.
* `root_update_belief`: no speech act changes a belief relation of the root, so Sincerity and
  Competence pass a commitment on to beliefs within a state (Theorem 26) but not across an update.
* `committed_believes_of_sincere`, `exists_committed_believes_not_committed`: under Sincerity a
  commitment entails a commitment to the corresponding belief, but not conversely, so Krifka's
  "The buffet is open" is stronger than "I believe the buffet is open".
* `admissible_of_cooperative`, `exists_admissible_not_cooperative`: cooperative speech acts are
  admissible, and not conversely.
* `cooperative_assert_of_not_committed`, `not_cooperative_assert_compl`: after an assertion,
  the addressee's confirming it is cooperative and denying it is not.

## Implementation notes

Propositions are world-sets, so the thesis's side condition that a proposition be
`C_{a,b}`-free holds vacuously, the antecedent of a conditional act holds at the root iff it is
`Set.univ`, and the `⊨_SAL` claims — for every space `C`, member `c` and world — are stated at
the root, `C_c` (Definition 13) being again a space with root `c`. Theorem 32, possibility, is
the totality of `update`.

## TODO

* Theorem 36, the cooperativity of answering a question, and speech act entailment
  (Definition 11) as a relation between acts.
* Report to the author: the witness for Theorem 27(2), `O_{a,b} = B_a ∪ {(w, w)}`, is not
  Euclidean (`buffet` replaces it); Theorem 31(1) needs `a ≠ b`, since for `a = b` the
  confirming assertion is redundant; and the well-definedness of the assertion update, called
  easy, needs the root case of `le_restrictCommitment_of_mem`.
* Report to the author: Competence (Definition 5) quantifies over all pairs of agents and so
  forces one shared belief relation (`Frame.competent_iff`). The assertion update of Definition 10
  is Definition 4, not the sincere update of Definition 6, so an assertion leaves a sincere root
  sincere only if the speaker already believed its content (`Frame.sincere_restrictCommitment_iff`),
  and no speech act changes a belief (`root_update_belief`). The informative update 2 holds in
  sincere, competent states, but no speech act brings it about.

## References

* [T. van der Leer, *Commitments, beliefs and expectations in conversation*
  (2026)][van-der-leer-2026]
* [C. Bary, *Speech acts, common ground and commitments* (2025)][bary-2025]
* [M. Krifka, *Performative updates and the modeling of speech acts* (2024)][krifka-2024a]
* [M. Krifka, *Structure and interpretation of declarative sentences* (2024)][krifka-2024b]
* [A. Cohen and M. Krifka, *Superlative quantifiers and meta-speech acts*
  (2014)][cohen-krifka-2014]
* [M. Krifka, *Bias in Commitment Space Semantics: Declarative Questions, Negated Questions,
  and Question Tags* (2015)][krifka-2015]
-/

@[expose] public section

namespace VanDerLeer2026

open Commitment
open ModalLogic (IsSerial IsEuclidean box_D box_four box_five box_restrict not_box box_iUnion)
open scoped ModalLogic
open SetRel
open Relation (ReflGen)

variable {W A : Type*}

/-! ### Beliefs and commitments -/

section States

variable (c : Frame W A) (a b : A) (π : Set W) (w : W)

theorem committed_committed (h : c.Committed a b π w) :
    c.Committed a b {v | c.Committed a b π v} w :=
  box_four h

theorem committed_not_committed (h : ¬ c.Committed a b π w) :
    c.Committed a b {v | ¬ c.Committed a b π v} w :=
  fun v hv ↦ not_box.2 (box_five (not_box.1 h) v hv)

theorem not_believes_empty : ¬ c.Believes a ∅ w :=
  fun h ↦ let ⟨_, _, hv⟩ := box_D h; hv

/-- `π` is mutually believed at `w` when it holds at every world some agent's belief reaches (§2.2).
-/
def MutuallyBelieved : Prop :=
  □[⋃ a, c.belief a] (· ∈ π) w

theorem mutuallyBelieved_iff : MutuallyBelieved c π w ↔ ∀ a, c.Believes a π w :=
  box_iUnion _

/-- `π` is mutually committed to at `w` when it holds at every world some commitment relation
reaches (§2.2). -/
def MutuallyCommitted : Prop :=
  □[⋃ k, c.commitment k] (· ∈ π) w

theorem mutuallyCommitted_iff : MutuallyCommitted c π w ↔ ∀ a b, c.Committed a b π w :=
  (box_iUnion _).trans Prod.forall

/-- The sincere update `c⌈π⌉^sin_{a,b}` is `c⌈π⌉_{a,b}` with `a`'s belief narrowed to the new
`O_{a,b}`-edges (Definition 6). It is partial, and `h` keeps the narrowed belief serial (footnote
18). -/
def sincereRestrict
    (h : ∀ w, ∃ v, w ~[c.belief a] v ∧ w ~[c.commitment (a, b)] v ∧ v ∈ π) : Frame W A where
  belief x := {p | p ∈ c.belief x ∧ (x = a → p ∈ (c.restrictCommitment a b π).commitment (a, b))}
  commitment := (c.restrictCommitment a b π).commitment
  belief_kd45 x :=
    { serial := fun w ↦ by
        by_cases hx : x = a
        · subst hx
          obtain ⟨v, hb, hc, hv⟩ := h w
          exact ⟨v, hb, fun _ ↦ ⟨hc, fun _ ↦ hv⟩⟩
        · obtain ⟨v, hv⟩ := IsSerial.serial (R := c.belief x) w
          exact ⟨v, hv, fun h' ↦ absurd h' hx⟩
      trans := fun _ _ _ h₁ h₂ ↦
        ⟨(c.belief x).trans h₁.1 h₂.1,
          fun hx ↦ ((c.restrictCommitment a b π).commitment (a, b)).trans (h₁.2 hx) (h₂.2 hx)⟩
      eucl := fun _ _ _ h₁ h₂ ↦
        ⟨IsEuclidean.eucl _ _ _ h₁.1 h₂.1,
          fun hx ↦ IsEuclidean.eucl _ _ _ (h₁.2 hx) (h₂.2 hx)⟩ }
  commitment_k45 := (c.restrictCommitment a b π).commitment_k45

variable {c a b π}

/-- The sincere update preserves Sincerity — the reason Definition 6 exists. -/
theorem sincere_sincereRestrict (hs : c.Sincere)
    (h : ∀ w, ∃ v, w ~[c.belief a] v ∧ w ~[c.commitment (a, b)] v ∧ v ∈ π) :
    (sincereRestrict c a b π h).Sincere := by
  rintro x y _ ⟨hb, hx⟩
  by_cases hxa : x = a
  · subst hxa
    by_cases hyb : y = b
    · subst hyb
      exact hx rfl
    · exact ⟨hs _ _ hb, fun h ↦ absurd (Prod.mk.inj h).2 hyb⟩
  · exact ⟨hs _ _ hb, fun h ↦ absurd (Prod.mk.inj h).1 hxa⟩

theorem believes_sincereRestrict
    (h : ∀ w, ∃ v, w ~[c.belief a] v ∧ w ~[c.commitment (a, b)] v ∧ v ∈ π) :
    (sincereRestrict c a b π h).Believes a π w :=
  fun _ hv ↦ (hv.2 rfl).2 rfl

/-- Definition 4 alone need not preserve Sincerity. -/
theorem exists_sincere_not_sincere_restrictCommitment :
    ∃ (c : Frame Bool Unit) (π : Set Bool),
      c.Sincere ∧ ¬ (c.restrictCommitment () () π).Sincere :=
  ⟨default, {true}, fun _ _ _ _ ↦ trivial,
    fun h ↦ Bool.false_ne_true ((@h () () (true, false) trivial).2 rfl)⟩

/-- Under Sincerity, `C_{a,b} π → C_{a,b} B_a π` (Theorem 27(1)). -/
theorem committed_believes_of_sincere {w : W} (hs : c.Sincere) (h : c.Committed a b π w) :
    c.Committed a b {v | c.Believes a π v} w :=
  fun _ hwv u hvu ↦ h u ((c.commitment (a, b)).trans hwv (hs a b hvu))

/-- Both agents believe only `true`, at either world, and are committed to nothing. The state is
sincere, and at `false` it satisfies `C_{a,b} B_a {true}` but not `C_{a,b} {true}`. -/
def buffet : Frame Bool Bool where
  belief _ := {p | p.2 = true}
  commitment _ := .univ
  belief_kd45 _ := { serial := fun _ ↦ ⟨true, rfl⟩
                     trans := fun _ _ _ _ h ↦ h
                     eucl := fun _ _ _ _ h ↦ h }
  commitment_k45 _ := {}

/-- `C_{a,b} B_a π → C_{a,b} π` is not valid over sincere states (Theorem 27(2)). -/
theorem exists_committed_believes_not_committed :
    ∃ (c : Frame Bool Bool) (a b : Bool) (π : Set Bool) (w : Bool),
      c.Sincere ∧ c.Committed a b {v | c.Believes a π v} w ∧ ¬ c.Committed a b π w :=
  ⟨buffet, true, false, {true}, false, fun _ _ _ _ ↦ trivial, fun _ _ _ hu ↦ hu,
    fun h ↦ Bool.false_ne_true (h false trivial)⟩

end States

/-! ### Commitment spaces -/

/-- `c ⊏ c'` says that `c'` is a cooperative continuation of `c` (Definition 7), in which beliefs
and commitments narrow, every commitment relation of `c'` is non-empty, and some commitment relation
narrows strictly. -/
structure CooperativeContinuation (c c' : Frame W A) : Prop where
  belief_le : ∀ a, c'.belief a ≤ c.belief a
  commitment_le : ∀ k, c'.commitment k ≤ c.commitment k
  commitment_nonempty : ∀ k, ∃ w v, w ~[c'.commitment k] v
  commitment_lt : ∃ k w v, w ~[c.commitment k] v ∧ ¬ w ~[c'.commitment k] v

@[inherit_doc] scoped infix:50 " ⊏ " => CooperativeContinuation

/-- `c ⊑ c'` says that `c = c'` or `c ⊏ c'`. -/
scoped infix:50 " ⊑ " => ReflGen CooperativeContinuation

namespace CooperativeContinuation

variable {c c' d : Frame W A}

theorem ne (h : c ⊏ c') : c ≠ c' :=
  fun e ↦ let ⟨_, _, _, h₁, h₂⟩ := h.commitment_lt; h₂ (e ▸ h₁)

theorem of_le (h : c ⊏ c') (hb : ∀ a, c.belief a ≤ d.belief a)
    (hc : ∀ k, c.commitment k ≤ d.commitment k) : d ⊏ c' where
  belief_le a := (h.belief_le a).trans (hb a)
  commitment_le k := (h.commitment_le k).trans (hc k)
  commitment_nonempty := h.commitment_nonempty
  commitment_lt :=
    let ⟨k, w, v, h₁, h₂⟩ := h.commitment_lt; ⟨k, w, v, hc k h₁, h₂⟩

theorem of_restrictCommitment {a b : A} {π : Set W} (h : c.restrictCommitment a b π ⊏ c') :
    c ⊏ c' :=
  h.of_le (fun _ ↦ le_rfl) (c.restrictCommitment_commitment_le a b π)

instance : IsTrans (Frame W A) CooperativeContinuation where
  trans _ _ _ h₁ h₂ := h₂.of_le h₁.belief_le h₁.commitment_le

end CooperativeContinuation

section Order

variable {c c' : Frame W A}

theorem commitment_le_of_le (h : c ⊑ c') (k : A × A) : c'.commitment k ≤ c.commitment k := by
  rcases h with _ | h
  · exact le_rfl
  · exact h.commitment_le k

theorem eq_of_le_of_le (h : c ⊑ c') (h' : c' ⊑ c) : c = c' := by
  rcases h with _ | h
  · rfl
  · rcases h' with _ | h'
    · rfl
    · exact absurd rfl (_root_.trans h h').ne

end Order

/-- The cooperative-continuation order on states, with `⊑` as `≤` and `⊏` as `<`. A commitment space
(Definition 8) is then a `Commitment.Space (Frame W A)`. -/
scoped instance : PartialOrder (Frame W A) where
  le c c' := c ⊑ c'
  lt c c' := c ⊏ c'
  le_refl _ := ReflGen.refl
  le_trans _ _ _ := trans_of (ReflGen CooperativeContinuation)
  le_antisymm _ _ := eq_of_le_of_le
  lt_iff_le_not_ge c c' :=
    ⟨fun h ↦ ⟨.single h, fun h' ↦ h.ne (eq_of_le_of_le (.single h) h')⟩,
      fun ⟨h, h'⟩ ↦ by
        rcases h with _ | h
        · exact absurd ReflGen.refl h'
        · exact h⟩

variable (C : Space (Frame W A)) {c : Frame W A} (a b : A) (π : Set W) (w : W)

theorem le_restrictCommitment_of_mem {x : Frame W A} {d e : A} {σ : Set W}
    (hmem : x.restrictCommitment d e σ ∈ C)
    (hroot : x.restrictCommitment d e σ = C.root → x.restrictCommitment d e σ = x) :
    x ⊑ x.restrictCommitment d e σ := by
  by_cases heq : x.restrictCommitment d e σ = x
  · rw [heq]
  refine ReflGen.single ⟨fun _ ↦ le_rfl, x.restrictCommitment_commitment_le d e σ, ?_, ?_⟩
  · rcases (Relation.reflGen_iff _ _ _).1 (C.root_le hmem) with h | h
    · exact absurd (hroot h) heq
    · exact h.commitment_nonempty
  · by_contra hcon
    push Not at hcon
    exact heq (Frame.ext rfl (funext fun k ↦ Set.ext fun p ↦
      ⟨(x.restrictCommitment_commitment_le d e σ k ·), hcon k p.1 p.2⟩))

/-- In `C[assert_{a,b}(π)]` the root commits `a` to `π` towards `b`, and the continuations are the
members of `C` above the state in which `b` has confirmed (Definition 10). -/
def assert : Space (Frame W A) where
  carrier := insert (C.root.restrictCommitment a b π)
    {c ∈ C | (C.root.restrictCommitment a b π).restrictCommitment b a π ⊑ c}
  root := C.root.restrictCommitment a b π
  isLeast' := ⟨Set.mem_insert _ _, by
    rintro c (rfl | ⟨hc, h⟩)
    · rfl
    rcases (Relation.reflGen_iff _ _ _).1 h with rfl | h
    · refine le_restrictCommitment_of_mem C hc fun hroot ↦ ?_
      exact hroot.trans
        ((C.root.restrictCommitment_restrictCommitment_eq_self_iff a b π π b a).1 hroot).1.symm
    · exact ReflGen.single h.of_restrictCommitment⟩

/-- In `C[question_{a,b}(π)]` the root is kept, and the continuations are the members of `C` in
which `b` has answered `π` or `¬π` (Definition 19). -/
def question : Space (Frame W A) :=
  C.restrict
    (Set.Ici (C.root.restrictCommitment b a π) ∪ Set.Ici (C.root.restrictCommitment b a πᶜ))


/-- `V_{a,b}` holds when `a`'s commitment relation towards `b` is empty, so that `a` is committed to
a contradiction (Definition 16). -/
def Violation (c : Frame W A) (a b : A) : Prop :=
  ∀ w v, ¬ w ~[c.commitment (a, b)] v

/-- The language of actions has assertion, polar question, the empty act `⊖`, denegation `∼α`,
composition `α;β`, and the conditional `π ↪ α/β` (Definition 20). -/
inductive SpeechAct (W A : Type*)
  | assert (a b : A) (π : Set W)
  | question (a b : A) (π : Set W)
  | empty
  | denegate (α : SpeechAct W A)
  | seq (α β : SpeechAct W A)
  | cond (π : Set W) (α β : SpeechAct W A)

variable (C : Space (Frame W A)) (a b : A) (π τ : Set W) (w : W) (α : SpeechAct W A)

open scoped Classical in
/-- `C[α]` (Definitions 10, 19, 21–24). The denegation `C[∼α]` removes the states of `C[α]` and
keeps the root; the conditional tests its antecedent at the root, where a world-set holds iff it
is `Set.univ`. -/
noncomputable def update : SpeechAct W A → Space (Frame W A) → Space (Frame W A)
  | .assert a b π, C => assert C a b π
  | .question a b π, C => question C a b π
  | .empty, C => C
  | .denegate α, C => C.denegate (update α C)
  | .seq α β, C => update β (update α C)
  | .cond π α β, C => if π = Set.univ then update α C else update β C

@[simp] theorem update_assert : update (.assert a b π) C = assert C a b π := rfl
@[simp] theorem update_question : update (.question a b π) C = question C a b π := rfl
@[simp] theorem update_empty : update .empty C = C := rfl
@[simp] theorem update_denegate : update (.denegate α) C = C.denegate (update α C) := rfl
@[simp] theorem update_seq (β : SpeechAct W A) :
    update (.seq α β) C = update β (update α C) := rfl
@[simp] theorem root_assert : (assert C a b π).root = C.root.restrictCommitment a b π := rfl
@[simp] theorem root_question : (question C a b π).root = C.root := rfl

/-- No speech act enlarges a commitment relation of the root (Lemma 28). -/
theorem root_update_commitment_le :
    (update α C).root.commitment (a, b) ≤ C.root.commitment (a, b) := by
  induction α generalizing C with
  | assert x y π => exact C.root.restrictCommitment_commitment_le x y π (a, b)
  | question => exact le_rfl
  | empty => exact le_rfl
  | denegate => exact le_rfl
  | seq α β ihα ihβ => exact (ihβ _).trans (ihα C)
  | cond π α β ihα ihβ =>
    simp only [update]
    split_ifs
    exacts [ihα C, ihβ C]

/-- No speech act changes a belief relation of the root, since assertion is Definition 4, which
leaves beliefs alone, and every other act keeps the root. -/
@[simp] theorem root_update_belief : (update α C).root.belief = C.root.belief := by
  induction α generalizing C with
  | assert => rfl
  | question => rfl
  | empty => rfl
  | denegate => rfl
  | seq α β ihα ihβ => exact (ihβ _).trans (ihα C)
  | cond π α β ihα ihβ =>
    simp only [update]
    split_ifs
    exacts [ihα C, ihβ C]

/-- A commitment at the root survives every speech act (Theorem 30). -/
theorem committed_update (h : C.root.Committed a b π w) : (update α C).root.Committed a b π w :=
  box_restrict _ (root_update_commitment_le C a b α) w h

/-- After `assert_{a,b}(π)`, `a` is committed towards `b` to `π` (Theorem 25). -/
theorem committed_assert : (update (.assert a b π) C).root.Committed a b π w :=
  C.root.committed_restrictCommitment a b π w

theorem believes_committed_assert (x : A) :
    (update (.assert a b π) C).root.Believes x
      {v | (update (.assert a b π) C).root.Committed a b π v} w :=
  fun _ _ ↦ C.root.committed_restrictCommitment a b π _

theorem committed_committed_assert (x y : A) :
    (update (.assert a b π) C).root.Committed x y
      {v | (update (.assert a b π) C).root.Committed a b π v} w :=
  fun _ _ ↦ C.root.committed_restrictCommitment a b π _

/-- Asserting `π` entails asserting any consequence `τ` (Theorem 29). -/
theorem assert_assert_of_subset (h : π ⊆ τ) :
    update (.assert a b τ) (update (.assert a b π) C) = update (.assert a b π) C := by
  have hroot : (C.root.restrictCommitment a b π).restrictCommitment a b τ =
      C.root.restrictCommitment a b π := by
    rw [Frame.restrictCommitment_restrictCommitment, Set.inter_eq_left.2 h]
  refine Space.ext fun c ↦ ?_
  simp only [update, assert, hroot, Space.mem_mk, Set.mem_insert_iff, Set.mem_ofPred_eq]
  refine ⟨fun hc ↦ hc.elim Or.inl And.left, fun hc ↦ ?_⟩
  rcases hc with rfl | ⟨hc, hle⟩
  · exact Or.inl rfl
  refine Or.inr ⟨Or.inr ⟨hc, hle⟩, ?_⟩
  rcases (Relation.reflGen_iff _ _ _).1 hle with rfl | hlt
  · have hx : ((C.root.restrictCommitment a b π).restrictCommitment b a τ).restrictCommitment
        b a π = (C.root.restrictCommitment a b π).restrictCommitment b a π := by
      rw [Frame.restrictCommitment_restrictCommitment, Set.inter_eq_right.2 h]
    rw [← hx] at hc ⊢
    refine le_restrictCommitment_of_mem C hc fun e ↦ ?_
    rw [hx] at e ⊢
    obtain ⟨h₁, h₂⟩ :=
      (C.root.restrictCommitment_restrictCommitment_eq_self_iff a b π π b a).1 e
    rw [h₁, h₂, (C.root.restrictCommitment_eq_self b a τ).2
      fun w v hv ↦ h ((C.root.restrictCommitment_eq_self b a π).1 h₂ w v hv)]
  · exact ReflGen.single (hlt.of_le (fun _ ↦ le_rfl)
      ((C.root.restrictCommitment a b π).restrictCommitment_mono b a π τ h))

/-! ### Possibility, admissibility, cooperativity -/

/-- `α` is admissible in `C` when performing it violates no commitment (Definition 17). Every speech
act is *possible* (Theorem 32), since `update` is total. -/
def Admissible : Prop :=
  ∀ x y, ¬ Violation (update α C).root x y

/-- `α` is cooperative in `C` when it is not redundant and its result lies below a cooperative
continuation of the root (Definition 15). -/
def Cooperative : Prop :=
  update α C ≠ C ∧ ∃ c ∈ C, C.root ⊏ c ∧ (update α C).root ⊑ c

/-- Inadmissibility of contradictions (Theorem 33). -/
theorem violation_assert_empty : Violation (update (.assert a b ∅) C).root a b :=
  fun _ _ h ↦ h.2 rfl

/-- Cooperative speech acts are admissible (Theorem 34(1)). -/
theorem admissible_of_cooperative (h : Cooperative C α) : Admissible C α := by
  obtain ⟨-, c, -, hlt, hle⟩ := h
  intro x y hV
  obtain ⟨w, v, hwv⟩ := hlt.commitment_nonempty (x, y)
  exact hV w v (commitment_le_of_le hle (x, y) hwv)

/-- Admissible speech acts need not be cooperative, since nothing is cooperative in a space without
continuations (Theorem 34(3)). -/
theorem exists_admissible_not_cooperative :
    ∃ (C : Space (Frame Bool Unit)) (α : SpeechAct Bool Unit),
      Admissible C α ∧ ¬ Cooperative C α :=
  ⟨{default}, .assert () () {true}, fun _ _ h ↦ h false true ⟨trivial, fun _ ↦ rfl⟩,
    fun ⟨_, _, hc, hlt, _⟩ ↦ hlt.ne hc.symm⟩

/-- After `assert_{a,b}(π)`, `b` denying `π` is not cooperative (Theorem 31(2)). -/
theorem not_cooperative_assert_compl :
    ¬ Cooperative (update (.assert a b π) C) (.assert b a πᶜ) := by
  rintro ⟨-, c, hc, hlt, hle⟩
  rcases hc with rfl | ⟨-, hc⟩
  · exact hlt.ne rfl
  obtain ⟨w, v, hwv⟩ := hlt.commitment_nonempty (b, a)
  exact (commitment_le_of_le hle (b, a) hwv).2 rfl
    ((commitment_le_of_le hc (b, a) hwv).2 rfl)

/-- After `assert_{a,b}(π)`, `b` confirming `π` is cooperative, provided the confirmed state is
projected in `C` and `b` was not yet committed to `π` (Theorem 31(1)). The thesis omits `a ≠ b`; for
`a = b` the confirmation is redundant. -/
theorem cooperative_assert_of_not_committed [Nonempty W] (hab : a ≠ b)
    (hmem : (C.root.restrictCommitment a b π).restrictCommitment b a π ∈ C)
    (h : ∀ w, ¬ C.root.Committed b a π w) :
    Cooperative (update (.assert a b π) C) (.assert b a π) := by
  obtain ⟨w⟩ := ‹Nonempty W›
  have h' := h w
  simp only [Frame.Committed, ModalLogic.Box, not_forall] at h'
  obtain ⟨v, hwv, hvπ⟩ := h'
  have h₁ : w ~[(C.root.restrictCommitment a b π).commitment (b, a)] v := by
    rwa [C.root.restrictCommitment_other a b π fun e ↦ hab (Prod.mk.inj e).2]
  have h₂ :
      ¬ w ~[((C.root.restrictCommitment a b π).restrictCommitment b a π).commitment (b, a)] v :=
    fun e ↦ hvπ (e.2 rfl)
  refine ⟨fun e ↦ h₂ ((congrArg (fun D ↦ (w, v) ∈ D.root.commitment (b, a)) e).mpr h₁),
    _, Set.mem_insert_of_mem _ ⟨hmem, ReflGen.refl⟩,
    ⟨fun _ ↦ le_rfl, (C.root.restrictCommitment a b π).restrictCommitment_commitment_le b a π,
      ?_, (b, a), w, v, h₁, h₂⟩, ReflGen.refl⟩
  rcases (Relation.reflGen_iff _ _ _).1 (show C.root ⊑ _ from C.root_le hmem) with e | hlt
  · exact absurd ((congrArg (fun s ↦ (w, v) ∈ s.commitment (b, a)) e).mpr hwv) h₂
  · exact hlt.commitment_nonempty

/-- `b` asserting `π` entails `a` having asked whether `π` (Theorem 35). -/
theorem question_assert :
    update (.question a b π) (update (.assert b a π) C) = update (.assert b a π) C := by
  refine Space.ext fun c ↦ ?_
  simp only [update, question, Space.mem_restrict, root_assert,
    Frame.restrictCommitment_restrictCommitment, Set.inter_self, Set.mem_union, Set.mem_Ici]
  refine ⟨fun hc ↦ ?_, fun hc ↦ Or.inr ⟨hc, Or.inl ((assert C b a π).root_le hc)⟩⟩
  rcases hc with rfl | ⟨hc, -⟩
  exacts [(assert C b a π).root_mem, hc]


end VanDerLeer2026
