module

public import Linglib.Logic.Modal.Basic
public import Linglib.Discourse.Commitment.Sincerity

/-!
# Belief–commitment frames

The multi-relational Kripke frame of [van-der-leer-2026] (Definition 2): per-agent belief
accessibility `B_a`, KD45, and pair-indexed commitment accessibility `O_{a,b}`, K45 — transitive
and Euclidean but not serial, so that an agent may be committed to a contradiction. Belief
`B_a π` and commitment `C_{a,b} π` are `ModalLogic.Box` along these relations, and what `a` is
committed to towards `b` at a world is a commitment state of `Commitment.Basic`.

## Main definitions

* `Commitment.Frame W A`: the frame.
* `Frame.Believes`, `Frame.Committed`: `B_a`, `C_{a,b}`.
* `Frame.restrictCommitment`: the update `c⌈π⌉_{a,b}` (Definition 4), `O_{a,b}` restricted to
  `π`-targets, everything else unchanged.
* `Frame.Sincere`, `Frame.Competent`: the frame conditions of Definition 5, after
  [asher-lascarides-2003].
* `Frame.toState`: the commitments of `a` towards `b` at `w`, as a commitment state.

## Main results

* `Frame.committed_restrictCommitment`: the performative update, `c⌈π⌉_{a,b} ⊨ C_{a,b} π`.
* `Frame.Sincere.believes_of_committed_of_competent`: Theorem 26, commitment passes to the
  speaker's belief under Sincerity and on to the addressee's under Competence.
* `Frame.sincere_restrictCommitment_iff`: the update keeps Sincerity iff the speaker already
  believed `π` everywhere.
* `Frame.competent_iff`: Competence holds iff all agents share one belief relation.
* `Frame.slate_toState_restrictCommitment`: on commitment states the update is the insertion of
  `commit a π`.
* `Frame.sincere_iff_forall_sincere_toState`: Sincerity of a frame is `Commitment.Sincere` of
  every projected commitment state, relative to belief.

## Implementation notes

Propositions are world-sets, so the valuation of Definition 2 is absorbed into them and every
proposition is `C_{a,b}`-free in the thesis's sense. Definition 2's non-empty set of worlds is a
hypothesis of the theorems that need it.

## References

* [T. van der Leer, *Commitments, beliefs and expectations in conversation*
  (2026)][van-der-leer-2026]
* [N. Asher and A. Lascarides, *Logics of Conversation* (2003)][asher-lascarides-2003]
-/

@[expose] public section

namespace Commitment

open ModalLogic (IsKD45Frame IsK45Frame IsEuclidean)
open scoped ModalLogic SetRel Filter

variable {W A : Type*}

/-- The belief–commitment frame of [van-der-leer-2026] (Definition 2, there a *commitment
state*): KD45 belief per agent and K45 commitment per ordered agent pair. -/
@[ext]
structure Frame (W A : Type*) where
  /-- `a`'s doxastic accessibility. -/
  belief : A → SetRel W W
  /-- `w ~[commitment a b] v`: at `w`, `v` satisfies everything `a` is committed towards `b`
  to. -/
  commitment : A → A → SetRel W W
  belief_kd45 : ∀ a, IsKD45Frame (belief a)
  commitment_k45 : ∀ a b, IsK45Frame (commitment a b)

namespace Frame

variable (c : Frame W A) (a b : A) (π τ : Set W) (w : W)

instance (a : A) : IsKD45Frame (c.belief a) := c.belief_kd45 a

instance (a b : A) : IsK45Frame (c.commitment a b) := c.commitment_k45 a b

/-- Every world is accessible from every world. -/
instance : Inhabited (Frame W A) :=
  ⟨{ belief _ := .univ
     commitment _ _ := .univ
     belief_kd45 _ := {}
     commitment_k45 _ _ := {} }⟩

/-- `c⌈π⌉_{a,b}` ([van-der-leer-2026] Definition 4): `O_{a,b}` restricted to `π`-targets,
`O_{a,b} ∩ {(w, v) | v ∈ π}`; the other relations are unchanged. -/
def restrictCommitment : Frame W A where
  belief := c.belief
  commitment a' b' := {p | p ∈ c.commitment a' b' ∧ (a' = a ∧ b' = b → p.2 ∈ π)}
  belief_kd45 := c.belief_kd45
  commitment_k45 a' b' :=
    { trans := fun _ _ _ h₁ h₂ ↦ ⟨(c.commitment a' b').trans h₁.1 h₂.1, h₂.2⟩
      eucl := fun _ _ _ h₁ h₂ ↦ ⟨IsEuclidean.eucl _ _ _ h₁.1 h₂.1, h₂.2⟩ }

@[simp] theorem restrictCommitment_belief : (c.restrictCommitment a b π).belief = c.belief := rfl

@[simp] theorem restrictCommitment_self (v : W) :
    w ~[(c.restrictCommitment a b π).commitment a b] v ↔ w ~[c.commitment a b] v ∧ v ∈ π := by
  simp [restrictCommitment]

@[simp] theorem restrictCommitment_other {a' b' : A} (h : ¬ (a' = a ∧ b' = b)) (v : W) :
    w ~[(c.restrictCommitment a b π).commitment a' b'] v ↔ w ~[c.commitment a' b'] v :=
  ⟨And.left, fun hc ↦ ⟨hc, (absurd · h)⟩⟩

theorem restrictCommitment_commitment_le (a' b' : A) :
    (c.restrictCommitment a b π).commitment a' b' ⊆ c.commitment a' b' :=
  fun _ h ↦ h.1

theorem restrictCommitment_restrictCommitment :
    (c.restrictCommitment a b π).restrictCommitment a b τ = c.restrictCommitment a b (π ∩ τ) := by
  refine Frame.ext rfl (funext fun a' ↦ funext fun b' ↦ Set.ext fun _ ↦ ?_)
  simp only [restrictCommitment, Set.mem_inter_iff, Set.mem_ofPred_eq]
  tauto

theorem restrictCommitment_mono (h : π ⊆ τ) (a' b' : A) :
    (c.restrictCommitment a b π).commitment a' b' ⊆ (c.restrictCommitment a b τ).commitment a' b' :=
  fun _ hv ↦ ⟨hv.1, fun hab ↦ h (hv.2 hab)⟩

/-! ### Modal operators -/

/-- `a` believes `π` at `w`: `π` holds at every `B_a`-accessible world
([van-der-leer-2026] Definition 3). -/
def Believes : Prop :=
  □[c.belief a] (· ∈ π) w

/-- `a` is committed towards `b` to `π` at `w`: `π` holds at every `O_{a,b}`-accessible world
([van-der-leer-2026] Definition 3). -/
def Committed : Prop :=
  □[c.commitment a b] (· ∈ π) w

/-- The performative update ([van-der-leer-2026] Theorem 25 at the level of states):
`c⌈π⌉_{a,b} ⊨ C_{a,b} π`. -/
theorem committed_restrictCommitment : (c.restrictCommitment a b π).Committed a b π w :=
  fun _ h ↦ h.2 ⟨rfl, rfl⟩

theorem restrictCommitment_eq_self : c.restrictCommitment a b π = c ↔ ∀ w, c.Committed a b π w := by
  constructor
  · intro h w v hv
    rw [← h] at hv
    exact hv.2 ⟨rfl, rfl⟩
  · intro h
    refine Frame.ext rfl (funext fun a' ↦ funext fun b' ↦ Set.ext fun ⟨w, v⟩ ↦ ?_)
    exact ⟨And.left, fun hc ↦ ⟨hc, fun ⟨ha, hb⟩ ↦ by subst ha hb; exact h w _ hc⟩⟩

theorem restrictCommitment_restrictCommitment_eq_self_iff (a' b' : A) :
    (c.restrictCommitment a b π).restrictCommitment a' b' τ = c ↔
      c.restrictCommitment a b π = c ∧ c.restrictCommitment a' b' τ = c := by
  simp only [restrictCommitment_eq_self]
  refine ⟨fun h ↦ ⟨fun w v hv ↦ ?_, fun w v hv ↦ ?_⟩, fun h ↦ ?_⟩
  · rw [← h] at hv
    exact hv.1.2 ⟨rfl, rfl⟩
  · rw [← h] at hv
    exact hv.2 ⟨rfl, rfl⟩
  · rw [(c.restrictCommitment_eq_self a b π).2 h.1, (c.restrictCommitment_eq_self a' b' τ).2 h.2]

/-! ### Frame conditions linking belief and commitment -/

/-- **Sincerity** ([van-der-leer-2026] Definition 5): for every agent pair, belief is contained in
commitment, so that an agent believes what it is committed to. -/
def Sincere : Prop :=
  ∀ x y, c.belief x ⊆ c.commitment x y

/-- **Competence** ([van-der-leer-2026] Definition 5): for every pair `(x, y)`, `y`'s
belief-accessible worlds are `x`-accessible too, so that `y` believes what `x` believes. -/
def Competent : Prop :=
  ∀ x y, c.belief y ⊆ c.belief x

variable {c a b π w}

/-- Under Sincerity, commitment entails belief ([van-der-leer-2026] Theorem 26(1)). -/
theorem Sincere.believes_of_committed (h : c.Sincere) : c.Committed a b π w → c.Believes a π w :=
  fun hcom v hbel ↦ hcom v (h a b hbel)

/-- Under Competence, `a`'s belief entails `b`'s ([van-der-leer-2026] Theorem 26(2)). -/
theorem Competent.believes_of_believes (h : c.Competent) : c.Believes a π w → c.Believes b π w :=
  fun hbel v hbelB ↦ hbel v (h a b hbelB)

/-- Under Sincerity and Competence, `a`'s commitment towards `b` entails `b`'s belief: the
informative update ([van-der-leer-2026] Theorem 26(3)). -/
theorem Sincere.believes_of_committed_of_competent (hsin : c.Sincere) (hcomp : c.Competent) :
    c.Committed a b π w → c.Believes b π w :=
  fun hcom ↦ hcomp.believes_of_believes (hsin.believes_of_committed hcom)

theorem sincere_restrictCommitment_iff :
    (c.restrictCommitment a b π).Sincere ↔ c.Sincere ∧ ∀ w, c.Believes a π w := by
  refine ⟨fun h ↦ ⟨fun x y ↦ (h x y).trans (c.restrictCommitment_commitment_le a b π x y),
    fun w ↦ h.believes_of_committed (c.committed_restrictCommitment a b π w)⟩, ?_⟩
  rintro ⟨hs, hb⟩ x y p hp
  exact ⟨hs x y hp, by rintro ⟨rfl, rfl⟩; exact hb p.1 p.2 hp⟩

/-- Competence relates every pair of agents in both directions, so it holds iff all agents share
one belief relation. -/
theorem competent_iff : c.Competent ↔ ∀ x y, c.belief x = c.belief y :=
  ⟨fun h x y ↦ (h y x).antisymm (h x y), fun h x y ↦ (h x y).superset⟩

/-! ### Projection onto commitment states -/

variable (c a b π w)

/-- The commitments of `a` towards `b` at `w`, as a commitment state: `a` commits to every
proposition true at all `O_{a,b}`-successors of `w`. -/
def toState : State A W := (commit a ·) '' {π | c.Committed a b π w}

theorem contents_toState : contents (c.toState a b w) = {π | c.Committed a b π w} :=
  (contents_image_commit a id _).trans (Set.image_id _)

theorem slate_toState : slate (c.toState a b w) = 𝓟 {v | w ~[c.commitment a b] v} := by
  rw [slate, contents_toState]
  exact (Filter.giGenerate W).l_u_eq (𝓟 _)

theorem contextSet_toState : contextSet (c.toState a b w) = {v | w ~[c.commitment a b] v} := by
  rw [← ker_slate, slate_toState, Filter.ker_principal]

/-- On commitment states, `c⌈π⌉_{a,b}` adds the commitment `commit a π`. -/
theorem slate_toState_restrictCommitment :
    slate ((c.restrictCommitment a b π).toState a b w) =
      slate (insert (commit a π) (c.toState a b w)) := by
  rw [slate_insert_of_commit rfl, slate_toState, slate_toState, Filter.inf_principal]
  congr 1
  ext
  simp

variable {c}

theorem sincere_iff_forall_sincere_toState :
    c.Sincere ↔
      ∀ x y w, Commitment.Sincere (fun _ a v ↦ {π | c.Believes a π v}) (c.toState x y w) w :=
  ⟨fun hs _ _ _ _ ⟨_, hπ, e⟩ _ ↦ e ▸ hs.believes_of_committed hπ,
    fun h x y p hp ↦ h x y p.1 _ ⟨{v | p.1 ~[c.commitment x y] v}, fun _ ↦ id, rfl⟩ rfl p.2 hp⟩

end Frame

end Commitment
