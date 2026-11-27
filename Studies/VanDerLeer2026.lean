module

public import Linglib.Discourse.Commitment.Space.Semantics
public import Linglib.Discourse.Commitment.Frame
public import Studies.Yamada2012

/-!
# van der Leer 2026: Speech Act Logic

Van der Leer's Speech Act Logic is a propositional dynamic logic of speech acts over the
commitment states of `Commitment.Frame`, with belief $B_a$ and commitment $C_{a,b}$ as modal
operators. A proposition is given by its truth set in each state, since the truth of
$C_{a,b}\pi$ changes when the commitments do, and it is $C_{a,b}$-free when that set does not
depend on $O_{a,b}$. An assertion is Krifka's performative update:
[it commits the speaker to a $C_{a,b}$-free content](##commits_assert), a commitment that
[Sincerity passes on to belief](##committed_believes_of_sincere) and that
[survives every later act](##commits_update) when the content mentions no commitment. The
acts transform a commitment space in the sense of Cohen and Krifka, a root state with its
cooperative continuations, and of the thesis's three levels of discourse expectation
[a cooperative act is admissible](##admissible_of_cooperative) and every act possible, but
[not conversely](##exists_admissible_not_cooperative). After an assertion
[the addressee's confirmation is cooperative](##cooperative_assert_of_not_committed) and
[the denial is not](##not_cooperative_assert_compl).

## Implementation notes

* The basic language is embedded by its semantics: a proposition is a function from states to
  world-sets, an atom a constant one, and negation and conjunction the pointwise complement and
  meet. `IsFree a b π` holds of every formula in which $C_{a,b}$ does not occur, by
  `isFree_const`, `IsFree.compl`, `IsFree.inf`, `IsFree.believes` and `IsFree.commits`.
* The $\models_{SAL}$ claims, for every space $C$, member $c$ and world, are stated at the root,
  $C_c$ (Definition 13) being again a space with root $c$. Theorem 32, possibility, is the
  totality of `update`.
* Theorem 30 is stated for a content free of every commitment operator, since
  [an act may change a commitment the content
  mentions](##exists_isFree_commits_not_commits_update). Theorems 29, 31 and 35 carry the
  freeness that Definition 10 uses, whose confirmation is evaluated at the new root.
* A state is a model of Yamada's logic of propositional commitments, in which
  [the update is the act of asserting](##toModel_restrictCommitment) and
  [his formulas free of an agent's commitments are free here](##isFree_realize).
* Theorem 31(1) assumes $a \ne b$, and Theorem 36(1) that the answerer has no violation at the
  root. The second part of Theorem 36 is not stated: in the space of all states
  [the questioner's own assertion is cooperative](##exists_cooperative_assert_question_self).

## TODO

* Truth at a state other than the root, through the restriction $C_c$, and the language of
  Definition 12 as formulas.

## References

* [T. van der Leer, *Commitments, beliefs and expectations in conversation*
  (2026)][van-der-leer-2026]
* [T. Yamada, *Dynamic Logic of Propositional Commitments* (2012)][yamada-2012]
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
open ModalLogic (IsSerial IsEuclidean box_D box_four box_five box_le_box_left not_box box_iUnion)
open scoped ModalLogic
open SetRel

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

-- Definition 6
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

-- Definition 4
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

-- Theorem 27(2)
theorem exists_committed_believes_not_committed :
    ∃ (c : Frame Bool Bool) (a b : Bool) (π : Set Bool) (w : Bool),
      c.Sincere ∧ c.Committed a b {v | c.Believes a π v} w ∧ ¬ c.Committed a b π w :=
  ⟨buffet, true, false, {true}, false, fun _ _ _ _ ↦ trivial, fun _ _ _ hu ↦ hu,
    fun h ↦ Bool.false_ne_true (h false trivial)⟩

end States

/-! ### The basic language -/

section Language

variable (a b : A) (π τ : Frame W A → Set W)

/-- `B_a π`, by its truth set in each state (Definition 3). -/
def believes : Frame W A → Set W := fun c ↦ {w | c.Believes a (π c) w}

/-- `C_{a,b} π`, by its truth set in each state (Definition 3). -/
def commits : Frame W A → Set W := fun c ↦ {w | c.Committed a b (π c) w}

/-- `π` is `C_{a,b}`-free when its truth set does not depend on `O_{a,b}`. -/
def IsFree : Prop :=
  ∀ ⦃c c' : Frame W A⦄, c.belief = c'.belief →
    (∀ k, k ≠ (a, b) → c.commitment k = c'.commitment k) → π c = π c'

variable {a b π τ}

theorem isFree_const (s : Set W) : IsFree a b fun _ : Frame W A ↦ s := fun _ _ _ _ ↦ rfl

theorem IsFree.compl (h : IsFree a b π) : IsFree a b πᶜ :=
  fun _ _ hb hc ↦ congrArg (·ᶜ) (h hb hc)

theorem IsFree.inf (h : IsFree a b π) (h' : IsFree a b τ) : IsFree a b (π ⊓ τ) :=
  fun _ _ hb hc ↦ congrArg₂ (· ⊓ ·) (h hb hc) (h' hb hc)

theorem IsFree.believes (h : IsFree a b π) (x : A) : IsFree a b (believes x π) :=
  fun c c' hb hc ↦ by simp only [VanDerLeer2026.believes, Frame.Believes, hb, h hb hc]

theorem IsFree.commits (h : IsFree a b π) {x y : A} (hxy : (x, y) ≠ (a, b)) :
    IsFree a b (commits x y π) :=
  fun c c' hb hc ↦ by simp only [VanDerLeer2026.commits, Frame.Committed, hc _ hxy, h hb hc]

theorem IsFree.apply_restrictCommitment (h : IsFree a b π) (c : Frame W A) (σ : Set W) :
    π (c.restrictCommitment a b σ) = π c :=
  h rfl fun _ hk ↦ c.restrictCommitment_other a b σ hk

end Language

/-! ### Commitment spaces -/

/-- `c'` is a cooperative continuation of `c` (Definition 7) when beliefs narrow, the commitment
relations narrow and one of them strictly, and no commitment relation of `c'` is empty. -/
structure CooperativeContinuation (c c' : Frame W A) : Prop where
  belief_le : c'.belief ≤ c.belief
  commitment_lt : c'.commitment < c.commitment
  commitment_nonempty : ∀ k, (c'.commitment k).Nonempty

instance : IsStrictOrder (Frame W A) CooperativeContinuation where
  irrefl _ h := lt_irrefl _ h.commitment_lt
  trans _ _ _ h₁ h₂ :=
    ⟨h₂.belief_le.trans h₁.belief_le, h₂.commitment_lt.trans h₁.commitment_lt,
      h₂.commitment_nonempty⟩

/-- States are ordered by cooperative continuation, `c < c'` being `c ⊏ c'` and `c ≤ c'` being
`c ⊑ c'`. A commitment space (Definition 8) is then a `Commitment.Space (Frame W A)`. -/
scoped instance : PartialOrder (Frame W A) := partialOrderOfSO CooperativeContinuation

section Order

variable {c c' d : Frame W A}

theorem lt_iff : c < c' ↔ CooperativeContinuation c c' := .rfl

theorem le_iff : c ≤ c' ↔ c = c' ∨ c < c' := .rfl

theorem commitment_antitone : Antitone (Frame.commitment : Frame W A → A × A → SetRel W W) :=
  fun _ _ h ↦ h.elim (fun e ↦ e ▸ le_rfl) fun h ↦ h.commitment_lt.le

theorem lt_of_lt_of_relations_le (h : c < c') (hb : c.belief ≤ d.belief)
    (hc : c.commitment ≤ d.commitment) : d < c' :=
  ⟨(lt_iff.1 h).belief_le.trans hb, (lt_iff.1 h).commitment_lt.trans_le hc,
    (lt_iff.1 h).commitment_nonempty⟩

theorem lt_of_restrictCommitment_lt {a b : A} {σ : Set W} (h : c.restrictCommitment a b σ < c') :
    c < c' :=
  lt_of_lt_of_relations_le h le_rfl (c.restrictCommitment_commitment_le a b σ)

theorem lt_restrictCommitment_iff {a b : A} {σ : Set W} :
    c < c.restrictCommitment a b σ ↔
      (¬ ∀ w, c.Committed a b σ w) ∧ ∀ k, ((c.restrictCommitment a b σ).commitment k).Nonempty :=
  ⟨fun h ↦ ⟨fun hc ↦ h.ne ((c.restrictCommitment_eq_self a b σ).2 hc).symm,
      (lt_iff.1 h).commitment_nonempty⟩,
    fun h ↦ ⟨le_rfl, lt_of_le_of_ne (c.restrictCommitment_commitment_le a b σ) fun e ↦
      h.1 ((c.restrictCommitment_eq_self a b σ).1 (Frame.ext rfl e)), h.2⟩⟩

theorem default_lt_iff :
    default < c ↔
      c.commitment ≠ (default : Frame W A).commitment ∧ ∀ k, (c.commitment k).Nonempty :=
  ⟨fun h ↦ ⟨(lt_iff.1 h).commitment_lt.ne, (lt_iff.1 h).commitment_nonempty⟩,
    fun h ↦ ⟨fun _ ↦ Set.subset_univ _, lt_of_le_of_ne (fun _ ↦ Set.subset_univ _) h.1, h.2⟩⟩

end Order

/-- `V_{a,b}` holds when `a`'s commitment relation towards `b` is empty, so that `a` is committed to
a contradiction (Definition 16). -/
def Violation (c : Frame W A) (a b : A) : Prop :=
  c.commitment (a, b) = ∅

variable (C : Space (Frame W A)) {c : Frame W A} (a b : A) (π τ : Frame W A → Set W) (w : W)

theorem not_violation_of_mem (hc : c ∈ C) (hne : c ≠ C.root) : ¬ Violation c a b :=
  (((C.root_le hc).resolve_left (Ne.symm hne)).commitment_nonempty (a, b)).ne_empty

theorem le_restrictCommitment_of_mem {x : Frame W A} {d e : A} {σ : Set W}
    (hmem : x.restrictCommitment d e σ ∈ C)
    (hroot : x.restrictCommitment d e σ = C.root → x.restrictCommitment d e σ = x) :
    x ≤ x.restrictCommitment d e σ := by
  by_cases heq : x.restrictCommitment d e σ = x
  · rw [heq]
  exact .inr (lt_restrictCommitment_iff.2 ⟨fun h ↦ heq ((x.restrictCommitment_eq_self d e σ).2 h),
    fun k ↦ Set.nonempty_iff_ne_empty.2
      (not_violation_of_mem C k.1 k.2 hmem fun h ↦ heq (hroot h))⟩)

/-- In `C[assert_{a,b}(π)]` the root commits `a` to `π` towards `b`, and the continuations are the
members of `C` above the state in which `b` has confirmed (Definition 10). -/
def assert : Space (Frame W A) where
  carrier := insert (C.root.restrictCommitment a b (π C.root))
    {c ∈ C | (C.root.restrictCommitment a b (π C.root)).restrictCommitment b a
      (π (C.root.restrictCommitment a b (π C.root))) ≤ c}
  root := C.root.restrictCommitment a b (π C.root)
  isLeast' := ⟨Set.mem_insert _ _, by
    rintro c (rfl | ⟨hc, rfl | h⟩)
    · rfl
    · exact le_restrictCommitment_of_mem C hc fun hroot ↦ hroot.trans
        ((C.root.restrictCommitment_restrictCommitment_eq_self_iff a b _ _ b a).1 hroot).1.symm
    · exact .inr (lt_of_restrictCommitment_lt h)⟩

/-- In `C[question_{a,b}(π)]` the root is kept, and the continuations are the members of `C` in
which `b` has answered `π` or `¬π` (Definition 19). -/
def question : Space (Frame W A) :=
  C.question
    {C.root.restrictCommitment b a (π C.root), C.root.restrictCommitment b a (π C.root)ᶜ}

/-- The language of actions has assertion, polar question, the empty act `⊖`, denegation `∼α`,
composition `α;β`, and the conditional `π ↪ α/β` (Definition 20). -/
inductive SpeechAct (W A : Type*)
  | assert (a b : A) (π : Frame W A → Set W)
  | question (a b : A) (π : Frame W A → Set W)
  | empty
  | denegate (α : SpeechAct W A)
  | seq (α β : SpeechAct W A)
  | cond (π : Frame W A → Set W) (α β : SpeechAct W A)

variable (α β : SpeechAct W A)

open scoped Classical in
/-- `C[α]` (Definitions 10, 19, 21–24). The denegation `C[∼α]` removes the states of `C[α]` and
keeps the root, and the conditional tests whether its antecedent holds throughout the root. -/
noncomputable def update : SpeechAct W A → Space (Frame W A) → Space (Frame W A)
  | .assert a b π, C => assert C a b π
  | .question a b π, C => question C a b π
  | .empty, C => C
  | .denegate α, C => C.denegate (update α C)
  | .seq α β, C => update β (update α C)
  | .cond π α β, C => if π C.root = Set.univ then update α C else update β C

@[simp] theorem update_assert : update (.assert a b π) C = assert C a b π := rfl
@[simp] theorem update_question : update (.question a b π) C = question C a b π := rfl
@[simp] theorem update_empty : update .empty C = C := rfl
@[simp] theorem update_denegate : update (.denegate α) C = C.denegate (update α C) := rfl
@[simp] theorem update_seq : update (.seq α β) C = update β (update α C) := rfl
@[simp] theorem root_assert :
    (assert C a b π).root = C.root.restrictCommitment a b (π C.root) := rfl
@[simp] theorem root_question : (question C a b π).root = C.root := rfl

/-- `α ⊳ β`: performing `β` after `α` changes nothing (Definition 11, a sequence `α₁, …, αₙ` being
the composition `α₁; …; αₙ`). -/
def Entails : Prop :=
  ∀ C, update β (update α C) = update α C

@[inherit_doc] scoped infix:50 " ⊳ " => Entails

-- Lemma 28
theorem root_update_commitment_le : (update α C).root.commitment ≤ C.root.commitment := by
  induction α generalizing C with
  | assert x y π => exact C.root.restrictCommitment_commitment_le x y _
  | question => exact le_rfl
  | empty => exact le_rfl
  | denegate => exact le_rfl
  | seq α β ihα ihβ => exact (ihβ _).trans (ihα C)
  | cond π α β ihα ihβ =>
    simp only [update]
    split_ifs
    exacts [ihα C, ihβ C]

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

variable {π τ}

theorem apply_root_update (hπ : ∀ x y, IsFree x y π) : π (update α C).root = π C.root := by
  induction α generalizing C with
  | assert x y σ => exact (hπ x y).apply_restrictCommitment _ _
  | question => rfl
  | empty => rfl
  | denegate => rfl
  | seq α β ihα ihβ => exact (ihβ _).trans (ihα C)
  | cond σ α β ihα ihβ =>
    simp only [update]
    split_ifs
    exacts [ihα C, ihβ C]

/-- A commitment to a proposition free of every commitment operator survives every speech act
(Theorem 30). -/
theorem commits_update (hπ : ∀ x y, IsFree x y π) (h : w ∈ commits a b π C.root) :
    w ∈ commits a b π (update α C).root := by
  simp only [commits, Set.mem_ofPred_eq, apply_root_update C α hπ] at h ⊢
  exact box_le_box_left (root_update_commitment_le C α (a, b)) _ w h

-- Theorem 30 for a `C_{a,b}`-free proposition that mentions another commitment: at the state
-- where every world is accessible, `a` is committed to `¬C_{b,b} {true}` until `b` asserts `{true}`
theorem exists_isFree_commits_not_commits_update :
    ∃ (C : Space (Frame Bool Bool)) (a b : Bool) (π : Frame Bool Bool → Set Bool)
      (α : SpeechAct Bool Bool) (w : Bool),
      IsFree a b π ∧ w ∈ commits a b π C.root ∧ w ∉ commits a b π (update α C).root := by
  refine ⟨{default}, false, false, (commits true true fun _ ↦ {true})ᶜ,
    .assert true true fun _ ↦ {true}, true,
    ((isFree_const _).commits (by decide)).compl,
    fun _ _ h ↦ Bool.false_ne_true (h false trivial),
    fun h ↦ ?_⟩
  exact h true ⟨trivial, fun e ↦ absurd (Prod.mk.inj e).1 (by decide)⟩ fun _ hv ↦ hv.2 rfl

/-- After `assert_{a,b}(π)`, `a` is committed towards `b` to `π` at every world, for `π` free of
`C_{a,b}` (Theorem 25). -/
theorem commits_assert (hπ : IsFree a b π) :
    commits a b π (update (.assert a b π) C).root = Set.univ :=
  Set.eq_univ_of_forall fun w ↦ by
    simp only [commits, update_assert, root_assert, hπ.apply_restrictCommitment]
    exact C.root.committed_restrictCommitment a b _ w

-- Theorem 25 without freeness: after `assert_{a,b}(p ∧ ¬C_{a,b} p)` the speaker is committed to
-- `p`, so to no proposition entailing `¬C_{a,b} p`
theorem exists_commits_assert_eq_empty :
    ∃ (C : Space (Frame Bool Unit)) (π : Frame Bool Unit → Set Bool),
      commits () () π (update (.assert () () π) C).root = ∅ := by
  refine ⟨{default}, (fun _ ↦ {true}) ⊓ (commits () () fun _ ↦ {true})ᶜ,
    Set.eq_empty_of_forall_notMem fun w h ↦ ?_⟩
  have hπ : ((fun _ ↦ {true}) ⊓ (commits () () fun _ ↦ {true})ᶜ)
      (default : Frame Bool Unit) = {true} :=
    Set.ext fun v ↦ ⟨And.left, fun hv ↦ ⟨hv, fun h ↦ Bool.false_ne_true (h false trivial)⟩⟩
  simp only [update_assert, root_assert, Space.root_singleton, hπ] at h
  exact (h true ⟨trivial, fun _ ↦ rfl⟩).2 fun _ hv ↦ hv.2 rfl

-- p. 29: the commitment an assertion creates is mutually believed
theorem mutuallyBelieved_commits_assert (hπ : IsFree a b π) :
    MutuallyBelieved (update (.assert a b π) C).root
      (commits a b π (update (.assert a b π) C).root) w := by
  rw [commits_assert C a b hπ]
  exact fun _ _ ↦ trivial

theorem mutuallyCommitted_commits_assert (hπ : IsFree a b π) :
    MutuallyCommitted (update (.assert a b π) C).root
      (commits a b π (update (.assert a b π) C).root) w := by
  rw [commits_assert C a b hπ]
  exact fun _ _ ↦ trivial

-- Theorem 29
theorem entails_assert_assert (hπ : IsFree a b π) (hτ : IsFree a b τ) (h : π ≤ τ) :
    SpeechAct.assert a b π ⊳ .assert a b τ := by
  intro C
  have hπ' := hπ.apply_restrictCommitment C.root (π C.root)
  have hτ' := hτ.apply_restrictCommitment C.root (π C.root)
  have h := h C.root
  have hroot : (C.root.restrictCommitment a b (π C.root)).restrictCommitment a b (τ C.root) =
      C.root.restrictCommitment a b (π C.root) := by
    rw [Frame.restrictCommitment_restrictCommitment, Set.inter_eq_left.2 h]
  refine Space.ext fun c ↦ ?_
  simp only [update, assert, hπ', hτ', hroot, Space.mem_mk, Set.mem_insert_iff,
    Set.mem_ofPred_eq]
  refine ⟨fun hc ↦ hc.elim Or.inl And.left, fun hc ↦ ?_⟩
  rcases hc with rfl | ⟨hc, hle⟩
  · exact Or.inl rfl
  refine Or.inr ⟨Or.inr ⟨hc, hle⟩, ?_⟩
  rcases hle with rfl | hlt
  · have hx : ((C.root.restrictCommitment a b (π C.root)).restrictCommitment b a
        (τ C.root)).restrictCommitment b a (π C.root) =
          (C.root.restrictCommitment a b (π C.root)).restrictCommitment b a (π C.root) := by
      rw [Frame.restrictCommitment_restrictCommitment, Set.inter_eq_right.2 h]
    rw [← hx] at hc ⊢
    refine le_restrictCommitment_of_mem C hc fun e ↦ ?_
    rw [hx] at e ⊢
    obtain ⟨h₁, h₂⟩ :=
      (C.root.restrictCommitment_restrictCommitment_eq_self_iff a b (π C.root) (π C.root) b a).1 e
    rw [h₁, h₂, (C.root.restrictCommitment_eq_self b a (τ C.root)).2
      fun w v hv ↦ h ((C.root.restrictCommitment_eq_self b a (π C.root)).1 h₂ w v hv)]
  · exact .inr (lt_of_lt_of_relations_le hlt le_rfl
      ((C.root.restrictCommitment a b (π C.root)).restrictCommitment_mono b a (π C.root)
        (τ C.root) h))

/-! ### Possibility, admissibility, cooperativity -/

variable (π)

/-- `α` is admissible in `C` when performing it violates no commitment (Definition 17). Every speech
act is *possible* (Theorem 32), since `update` is total. -/
def Admissible : Prop :=
  ∀ x y, ¬ Violation (update α C).root x y

/-- `α` is cooperative in `C` when it is not redundant and its result lies below a cooperative
continuation of the root (Definition 15). -/
def Cooperative : Prop :=
  update α C ≠ C ∧ ∃ c ∈ C, C.root < c ∧ (update α C).root ≤ c

-- Theorem 33
theorem violation_assert_inf_compl : Violation (update (.assert a b (π ⊓ πᶜ)) C).root a b :=
  Set.eq_empty_of_forall_notMem fun _ h ↦ (h.2 rfl).2 (h.2 rfl).1

-- Theorem 34(4)
theorem not_admissible_assert_inf_compl : ¬ Admissible C (.assert a b (π ⊓ πᶜ)) :=
  fun h ↦ h a b (violation_assert_inf_compl C a b π)

/-- Cooperative speech acts are admissible (Theorem 34(1)). -/
theorem admissible_of_cooperative (h : Cooperative C α) : Admissible C α := by
  obtain ⟨-, c, -, hlt, hle⟩ := h
  exact fun x y ↦ (((lt_iff.1 hlt).commitment_nonempty (x, y)).mono
    (commitment_antitone hle (x, y))).ne_empty

-- Theorem 34(3): nothing is cooperative in a space without continuations
theorem exists_admissible_not_cooperative :
    ∃ (C : Space (Frame Bool Unit)) (α : SpeechAct Bool Unit),
      Admissible C α ∧ ¬ Cooperative C α :=
  ⟨{default}, .assert () () fun _ ↦ {true},
    fun _ _ h ↦ Set.notMem_empty (false, true) (h ▸ ⟨trivial, fun _ ↦ rfl⟩),
    fun ⟨_, _, hc, hlt, _⟩ ↦ hlt.ne hc.symm⟩

-- Theorem 31(2)
theorem not_cooperative_assert_compl :
    ¬ Cooperative (update (.assert a b π) C) (.assert b a πᶜ) := by
  rintro ⟨-, c, hc, hlt, hle⟩
  rcases hc with rfl | ⟨-, hc⟩
  · exact lt_irrefl _ hlt
  obtain ⟨⟨w, v⟩, hwv⟩ := (lt_iff.1 hlt).commitment_nonempty (b, a)
  exact (commitment_antitone hle (b, a) hwv).2 rfl
    ((commitment_antitone hc (b, a) hwv).2 rfl)

variable {π}

/-- After `assert_{a,b}(π)`, `b` confirming `π` is cooperative, provided the confirmed state is
projected in `C` and `b` was not yet committed to `π` (Theorem 31(1)), and `a ≠ b`, without which
the confirmation is redundant. -/
theorem cooperative_assert_of_not_committed [Nonempty W] (hπ : IsFree a b π) (hab : a ≠ b)
    (hmem : (C.root.restrictCommitment a b (π C.root)).restrictCommitment b a (π C.root) ∈ C)
    (h : commits b a π C.root = ∅) :
    Cooperative (update (.assert a b π) C) (.assert b a π) := by
  obtain ⟨w⟩ := ‹Nonempty W›
  have hπ' := hπ.apply_restrictCommitment C.root (π C.root)
  have h' : w ∉ commits b a π C.root := h ▸ Set.notMem_empty w
  simp only [commits, Set.mem_ofPred_eq, Frame.Committed, ModalLogic.Box, not_forall] at h'
  obtain ⟨v, hwv, hvπ⟩ := h'
  have h₁ : w ~[(C.root.restrictCommitment a b (π C.root)).commitment (b, a)] v := by
    rwa [C.root.restrictCommitment_other a b (π C.root) fun e ↦ hab (Prod.mk.inj e).2]
  have h₂ : ¬ w ~[((C.root.restrictCommitment a b (π C.root)).restrictCommitment b a
      (π C.root)).commitment (b, a)] v :=
    fun e ↦ hvπ (e.2 rfl)
  have hr : (update (.assert b a π) (update (.assert a b π) C)).root =
      (C.root.restrictCommitment a b (π C.root)).restrictCommitment b a (π C.root) := by
    simp only [update_assert, root_assert, hπ']
  refine ⟨fun e ↦ h₂ ?_, _, Set.mem_insert_of_mem _ ⟨hmem, by rw [hπ']⟩,
    ⟨le_rfl, lt_of_le_of_ne (fun k ↦ (C.root.restrictCommitment a b
      (π C.root)).restrictCommitment_commitment_le b a (π C.root) k) fun e ↦ h₂ ?_,
      fun k ↦ Set.nonempty_iff_ne_empty.2 (not_violation_of_mem C k.1 k.2 hmem fun e ↦ h₂ ?_)⟩,
    hr.le⟩
  · rw [← hr, e]
    exact h₁
  · rw [e]
    exact h₁
  · rw [e]
    exact hwv

-- Theorem 31(1) in the space of all states above the one where every world is accessible
example : Cooperative (update (.assert false true fun _ ↦ {true}) (Space.Ici default))
    (.assert true false fun _ : Frame Bool Bool ↦ {true}) := by
  have hne : (((default : Frame Bool Bool).restrictCommitment false true {true}).restrictCommitment
      true false {true}).commitment ≠ (default : Frame Bool Bool).commitment := fun e ↦ by
    have h : ((false, false) : Bool × Bool) ∈ (((default : Frame Bool Bool).restrictCommitment
        false true {true}).restrictCommitment true false {true}).commitment (false, true) := by
      rw [e]
      trivial
    exact Bool.false_ne_true (h.1.2 rfl)
  have hk : ∀ k, ((((default : Frame Bool Bool).restrictCommitment false true
      {true}).restrictCommitment true false {true}).commitment k).Nonempty :=
    fun k ↦ ⟨(true, true), ⟨trivial, fun _ ↦ rfl⟩, fun _ ↦ rfl⟩
  exact cooperative_assert_of_not_committed _ _ _ (isFree_const _) (by decide)
    (le_of_lt (default_lt_iff.2 ⟨hne, hk⟩))
    (Set.eq_empty_of_forall_notMem fun w h ↦ Bool.false_ne_true (h false trivial))

-- Theorem 31(1) at `a = b`, by Theorem 29
theorem not_cooperative_assert_self (hπ : IsFree a a π) :
    ¬ Cooperative (update (.assert a a π) C) (.assert a a π) :=
  fun h ↦ h.1 (entails_assert_assert a a hπ hπ le_rfl C)

/-! ### Questions and answers -/

-- Theorem 35
theorem entails_assert_question (hπ : IsFree b a π) :
    SpeechAct.assert b a π ⊳ .question a b π := fun C ↦
  Space.question_eq_self _ ⟨_, Set.mem_insert _ _, by
    simp only [update_assert, root_assert, hπ.apply_restrictCommitment,
      Frame.restrictCommitment_restrictCommitment, Set.inter_self, le_refl]⟩

theorem entails_assert_compl_question (hπ : IsFree b a π) :
    SpeechAct.assert b a πᶜ ⊳ .question a b π := fun C ↦
  Space.question_eq_self _ ⟨_, Set.mem_insert_of_mem _ rfl, by
    simp only [update_assert, root_assert, hπ.apply_restrictCommitment, Pi.compl_apply,
      Frame.restrictCommitment_restrictCommitment, Set.inter_self, le_refl]⟩

variable {a b}

theorem root_lt_restrictCommitment_of_mem {σ : Set W} (hV : ¬ Violation C.root b a)
    (h₁ : C.root.restrictCommitment b a σ ∈ C) (h₂ : C.root.restrictCommitment b a σᶜ ∈ C) :
    C.root < C.root.restrictCommitment b a σ := by
  refine (C.root_le h₁).resolve_left fun e ↦ ?_
  have h : (C.root.restrictCommitment b a σᶜ).commitment (b, a) = ∅ :=
    Set.eq_empty_of_forall_notMem fun p hp ↦ hp.2 rfl
      ((show p ∈ (C.root.restrictCommitment b a σ).commitment (b, a) from e ▸ hp.1).2 rfl)
  exact not_violation_of_mem C b a h₂ (fun e' ↦ hV (e' ▸ h)) h

variable (a b π)

-- Theorem 36(1)
theorem cooperative_assert_question (hV : ¬ Violation C.root b a)
    (h₁ : C.root.restrictCommitment b a (π C.root) ∈ C)
    (h₂ : C.root.restrictCommitment b a (π C.root)ᶜ ∈ C) :
    Cooperative (update (.question a b π) C) (.assert b a π) := by
  have hlt := root_lt_restrictCommitment_of_mem C hV h₁ h₂
  exact ⟨fun e ↦ hlt.ne' (congrArg Space.root e), _,
    .inr ⟨h₁, _, Set.mem_insert _ _, le_rfl⟩, hlt, le_rfl⟩

-- Theorem 36(1), the negative answer
theorem cooperative_assert_compl_question (hV : ¬ Violation C.root b a)
    (h₁ : C.root.restrictCommitment b a (π C.root) ∈ C)
    (h₂ : C.root.restrictCommitment b a (π C.root)ᶜ ∈ C) :
    Cooperative (update (.question a b π) C) (.assert b a πᶜ) := by
  have hlt := root_lt_restrictCommitment_of_mem C hV h₂ (by rwa [compl_compl])
  exact ⟨fun e ↦ hlt.ne' (congrArg Space.root e), _,
    .inr ⟨h₂, _, Set.mem_insert_of_mem _ rfl, le_rfl⟩, hlt, le_rfl⟩

-- Theorem 36(2): in the space of all states, where the questioner `a` is committed to neither
-- answer, `a`'s own assertion of `π` after the question lies below the state in which both
-- participants are committed to `π`
theorem exists_cooperative_assert_question_self :
    ∃ (C : Space (Frame Bool Bool)) (a b : Bool) (π : Frame Bool Bool → Set Bool),
      C.root.restrictCommitment b a (π C.root) ∈ C ∧
        C.root.restrictCommitment b a (π C.root)ᶜ ∈ C ∧
        commits a b π C.root = ∅ ∧ commits a b πᶜ C.root = ∅ ∧
        Cooperative (update (.question a b π) C) (.assert a b π) := by
  let D : Frame Bool Bool := default
  have h₁ : D < D.restrictCommitment true false {true} :=
    lt_restrictCommitment_iff.2 ⟨fun h ↦ Bool.false_ne_true (h false false trivial),
      fun _ ↦ ⟨(true, true), trivial, fun _ ↦ rfl⟩⟩
  have h₂ : D < D.restrictCommitment true false {true}ᶜ :=
    lt_restrictCommitment_iff.2 ⟨fun h ↦ h true true trivial rfl,
      fun _ ↦ ⟨(false, false), trivial, fun _ ↦ Bool.false_ne_true⟩⟩
  have h₃ : D < D.restrictCommitment false true {true} :=
    lt_restrictCommitment_iff.2 ⟨fun h ↦ Bool.false_ne_true (h false false trivial),
      fun _ ↦ ⟨(true, true), trivial, fun _ ↦ rfl⟩⟩
  have h₄ : D.restrictCommitment true false {true} <
      (D.restrictCommitment true false {true}).restrictCommitment false true {true} :=
    lt_restrictCommitment_iff.2 ⟨fun h ↦ Bool.false_ne_true
        (h false false ⟨trivial, fun e ↦ absurd (Prod.mk.inj e).1 (by decide)⟩),
      fun _ ↦ ⟨(true, true), ⟨trivial, fun _ ↦ rfl⟩, fun _ ↦ rfl⟩⟩
  have h₅ : D.restrictCommitment false true {true} <
      (D.restrictCommitment false true {true}).restrictCommitment true false {true} :=
    lt_restrictCommitment_iff.2 ⟨fun h ↦ Bool.false_ne_true
        (h false false ⟨trivial, fun e ↦ absurd (Prod.mk.inj e).1 (by decide)⟩),
      fun _ ↦ ⟨(true, true), ⟨trivial, fun _ ↦ rfl⟩, fun _ ↦ rfl⟩⟩
  refine ⟨Space.Ici D, false, true, fun _ ↦ {true}, h₁.le, h₂.le,
    Set.eq_empty_of_forall_notMem fun _ h ↦ Bool.false_ne_true (h false trivial),
    Set.eq_empty_of_forall_notMem fun _ h ↦ h true trivial rfl,
    fun e ↦ h₃.ne' (congrArg Space.root e), _,
    .inr ⟨(h₁.trans h₄).le, _, Set.mem_insert _ _, h₄.le⟩, h₁.trans h₄, ?_⟩
  rw [Frame.restrictCommitment_comm]
  exact h₅.le

/-! ### Yamada's acts of asserting -/

section Yamada

open Yamada2012

variable {P : Type*} (c : Frame W A) (val : P → Set W) (a b : A) (σ : Set W)

/-- A state as a model of [yamada-2012]'s logic whose agents are the ordered pairs, with one
commitment relation for both kinds of commitment. -/
def toModel : Model W P (A × A) where
  acc k := c.commitment k.1
  conceded_subset _ := subset_rfl
  val := val

-- Definition 4 is the act of asserting
theorem toModel_restrictCommitment :
    toModel (c.restrictCommitment a b σ) val = (toModel c val).assert (a, b) σ := by
  simp only [toModel, Model.assert, Model.mk.injEq, and_true]
  funext ⟨k, kind⟩
  ext p
  cases kind <;> simp [Prod.ext_iff]

variable {a b}

-- a formula in which the pair's commitments do not occur is `C_{a,b}`-free
theorem isFree_realize {φ : Formula P (A × A)} (h : φ.IFree (a, b)) :
    IsFree a b fun c : Frame W A ↦ φ.realize (toModel c val) := by
  intro c c' hb hc
  induction φ with
  | top | atom => rfl
  | neg φ ih => exact congrArg (·ᶜ) (ih h)
  | and φ ψ ihφ ihψ => exact congrArg₂ (· ∩ ·) (ihφ h.1) (ihψ h.2)
  | cmt k j φ ih =>
    simp only [Formula.realize, toModel] at ih ⊢
    rw [ih h.2]
    simp only [hc j h.1]
  | afterAssert | afterConcede => exact h.elim

end Yamada

end VanDerLeer2026
