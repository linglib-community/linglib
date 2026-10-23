module

public import Mathlib.Data.Set.Basic
public import Linglib.Logic.Modal.Defs
public import Linglib.Logic.Modal.Basic
public import Linglib.Logic.Modal.Epistemic
public import Linglib.Discourse.Commitment.Basic

/-!
# Belief–commitment frames

The multi-relational Kripke frame of [van-der-leer-2026] (Definition 2): per-agent belief
accessibility `B_a`, the KD45 doxastic frame of [hintikka-1962], and pair-indexed commitment
accessibility `O_{a,b}`, K45 — transitive and Euclidean but not serial, so that an agent may be
committed to a contradiction. Belief `B_a π` and commitment `C_{a,b} π` are `ModalLogic.Box`
along these relations. Propositions are world-sets, so the valuation of Definition 2 is absorbed
into them and every proposition is `C_{a,b}`-free in the thesis's sense.

## Main definitions

* `Commitment.Frame W A` — the frame.
* `Frame.Believes`, `Frame.Committed` — `B_a`, `C_{a,b}`.
* `Frame.restrictCommitment` — the update `c⌈π⌉_{a,b}` (Definition 4): `O_{a,b}` restricted to
  `π`-targets, everything else unchanged.
* `Frame.Sincere`, `Frame.Competent` — the frame conditions of Definition 5, after
  [asher-lascarides-2003]: belief is contained in commitment; the addressee's belief is
  contained in the speaker's.

## Main results

* `Frame.committed_restrictCommitment` — the performative update, `c⌈π⌉_{a,b} ⊨ C_{a,b} π`.
* `Frame.Sincere.believes_of_committed`, `Frame.Competent.believes_of_believes`,
  `Frame.Sincere.believes_of_committed_of_competent` — Theorem 26: commitment transfers to
  the speaker's belief under Sincerity and on to the addressee's under Competence, the
  informative update.
* `Frame.restrictCommitment_eq_self` — the update is idle iff the commitment already holds
  globally.
* `Frame.mem_slate_iff` — the propositions `a` is committed to towards `b` at `w` form the
  principal filter of the `O_{a,b}`-successors, the projection onto the commitment sets of
  `Commitment.Basic`.

## References

* [T. van der Leer, *Commitments, beliefs and expectations in conversation*
  (2026)][van-der-leer-2026]
* [J. Hintikka, *Knowledge and Belief: An Introduction to the Logic of the Two Notions*
  (1962)][hintikka-1962]
* [N. Asher and A. Lascarides, *Logics of Conversation* (2003)][asher-lascarides-2003]
-/

@[expose] public section

namespace Commitment

open ModalLogic (IsKD45Frame IsK45Frame IsEuclidean)
open scoped ModalLogic SetRel

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
    { trans := fun _ _ _ h₁ h₂ => ⟨(c.commitment a' b').trans h₁.1 h₂.1, h₂.2⟩
      eucl := fun _ _ _ h₁ h₂ => ⟨IsEuclidean.eucl _ _ _ h₁.1 h₂.1, h₂.2⟩ }

@[simp] theorem restrictCommitment_belief : (c.restrictCommitment a b π).belief = c.belief := rfl

@[simp] theorem restrictCommitment_self (v : W) :
    w ~[(c.restrictCommitment a b π).commitment a b] v ↔ w ~[c.commitment a b] v ∧ v ∈ π := by
  simp [restrictCommitment]

@[simp] theorem restrictCommitment_other {a' b' : A} (h : ¬ (a' = a ∧ b' = b)) (v : W) :
    w ~[(c.restrictCommitment a b π).commitment a' b'] v ↔ w ~[c.commitment a' b'] v :=
  ⟨And.left, fun hc => ⟨hc, (absurd · h)⟩⟩

theorem restrictCommitment_commitment_le (a' b' : A) :
    (c.restrictCommitment a b π).commitment a' b' ⊆ c.commitment a' b' :=
  fun _ h => h.1

theorem restrictCommitment_restrictCommitment :
    (c.restrictCommitment a b π).restrictCommitment a b τ = c.restrictCommitment a b (π ∩ τ) := by
  refine Frame.ext rfl (funext fun a' => funext fun b' => Set.ext fun _ => ?_)
  simp only [restrictCommitment, Set.mem_inter_iff, Set.mem_ofPred_eq]
  tauto

theorem restrictCommitment_mono (h : π ⊆ τ) (a' b' : A) :
    (c.restrictCommitment a b π).commitment a' b' ⊆ (c.restrictCommitment a b τ).commitment a' b' :=
  fun _ hv => ⟨hv.1, fun hab => h (hv.2 hab)⟩

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
  fun _ h => h.2 ⟨rfl, rfl⟩

theorem restrictCommitment_eq_self : c.restrictCommitment a b π = c ↔ ∀ w, c.Committed a b π w := by
  constructor
  · intro h w v hv
    rw [← h] at hv
    exact hv.2 ⟨rfl, rfl⟩
  · intro h
    refine Frame.ext rfl (funext fun a' => funext fun b' => Set.ext fun ⟨w, v⟩ => ?_)
    exact ⟨And.left, fun hc => ⟨hc, fun ⟨ha, hb⟩ => by subst ha hb; exact h w _ hc⟩⟩

theorem restrictCommitment_restrictCommitment_eq_self_iff (a' b' : A) :
    (c.restrictCommitment a b π).restrictCommitment a' b' τ = c ↔
      c.restrictCommitment a b π = c ∧ c.restrictCommitment a' b' τ = c := by
  simp only [restrictCommitment_eq_self]
  refine ⟨fun h => ⟨fun w v hv => ?_, fun w v hv => ?_⟩, fun h => ?_⟩
  · rw [← h] at hv
    exact hv.1.2 ⟨rfl, rfl⟩
  · rw [← h] at hv
    exact hv.2 ⟨rfl, rfl⟩
  · rw [(c.restrictCommitment_eq_self a b π).2 h.1, (c.restrictCommitment_eq_self a' b' τ).2 h.2]

/-! ### Projection onto commitment sets -/

/-- What `a` is committed to towards `b` at `w`: the principal filter of the `O_{a,b}`-successors
of `w`. -/
def slate (c : Frame W A) (a b : A) (w : W) : Filter W :=
  Filter.principal {v | w ~[c.commitment a b] v}

theorem mem_slate_iff : π ∈ c.slate a b w ↔ c.Committed a b π w := Filter.mem_principal

/-! ### Frame conditions linking belief and commitment -/

/-- **Sincerity** ([van-der-leer-2026] Definition 5, after [asher-lascarides-2003]): for every
agent pair, belief is contained in commitment. -/
def Sincere : Prop :=
  ∀ x y, c.belief x ⊆ c.commitment x y

/-- **Competence** ([van-der-leer-2026] Definition 5, after [asher-lascarides-2003]): for every
pair `(x, y)`, `y`'s belief-accessible worlds are `x`-accessible too. -/
def Competent : Prop :=
  ∀ x y, c.belief y ⊆ c.belief x

variable {c a b π w}

/-- Under Sincerity, commitment entails belief ([van-der-leer-2026] Theorem 26(1)). -/
theorem Sincere.believes_of_committed (h : c.Sincere) : c.Committed a b π w → c.Believes a π w :=
  fun hcom v hbel => hcom v (h a b hbel)

/-- Under Competence, `a`'s belief entails `b`'s ([van-der-leer-2026] Theorem 26(2)). -/
theorem Competent.believes_of_believes (h : c.Competent) : c.Believes a π w → c.Believes b π w :=
  fun hbel v hbelB => hbel v (h a b hbelB)

/-- Under Sincerity and Competence, `a`'s commitment towards `b` entails `b`'s belief: the
informative update ([van-der-leer-2026] Theorem 26(3)). -/
theorem Sincere.believes_of_committed_of_competent (hsin : c.Sincere) (hcomp : c.Competent) :
    c.Committed a b π w → c.Believes b π w :=
  fun hcom => hcomp.believes_of_believes (hsin.believes_of_committed hcom)

end Frame

end Commitment
