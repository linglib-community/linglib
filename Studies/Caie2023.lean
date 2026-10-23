module

public import Linglib.Discourse.CommonGround

/-!
# Caie 2023: disjunctive context updating

This file formalizes the account of conversational updating in [caie-2023]. On the orthodox
account ([stalnaker-1978]) each world in the context set fixes a unique compositional context
([kaplan-1989]) that interprets an assertion there, and updating proceeds by diagonalization:
eliminate a world exactly when the proposition the assertion expresses at it is false there.
Caie argues that a discourse like *Sarah has two pairs of socks. Tim likes both of them. Both of
them are matching.* refutes the uniqueness assumption. Its first sentence leaves matching and
mixed pairings of Sarah's four socks equally available, and the discourse conveys Tim's
preference only because the second sentence narrows the pairings that interpret the third.
Dropping uniqueness, a world survives when *some* available context makes the assertion true,
and the contexts available to an assertion are those that made its predecessor true.

Both accounts update by asserting a diagonal proposition, so the revision is to the proposition
asserted rather than to the update rule: `diagonal` evaluates the semantics at each world's
chosen context, `disjunctiveDiagonal` quantifies existentially over the contexts available
there.

## Main definitions

* `diagonal`, `disjunctiveDiagonal` — the propositions Standard and Disjunctive Updating assert
* `prune` — Contextual Pruning: the contexts an assertion leaves to its successor
* `fragments`, `updateFragments` — the ⟨context, world⟩ pairs and their filtration
* `run` — a discourse, each assertion pruning the next
* `Charitable` — Uniform Charity, the context shift Standard Updating needs

## Main results

* `fragments_prune` — one filtration of the fragment set updates and prunes at once
* `run_eq_inter` — a discourse updates on the conjunction of its sentences under one context
* `prune_singleton` — a unique interpretation is passed on to the next assertion
* `run_timLikesMatching`, `run_timDislikesMixed` — either discourse leaves exactly the worlds
  where the Facts hold, so Safe Information holds of both
* `preservation_drops_fact_world`, `charity_not_safe` — the two horns of the dilemma facing
  Standard Updating

## References

* [caie-2023]
* [stalnaker-1978]
* [kaplan-1989]
* [krifka-2009]
* [barker-2002-vagueness]
* [barker-2013]
-/

@[expose] public section

namespace Caie2023

open Filter Set HasAssertion HasCommonGround

variable {C W : Type*} (cs : Set W) (interp : W → C) (I : W → Set C) (sem : C → W → Prop)

/-! ### The propositions the two accounts assert -/

/-- The proposition Standard Updating asserts ([stalnaker-1978]): a world belongs to it when the
assertion is true there under the unique compositional context that interprets it there. -/
def diagonal : Set W := {w | sem (interp w) w}

/-- The proposition Disjunctive Multi-Context Updating asserts: a world belongs to it when the
assertion is true there under some context available there, so a world is eliminated only when
the disjunction of the propositions the assertion expresses at it is false there. -/
def disjunctiveDiagonal : Set W := {w | ∃ c ∈ I w, sem c w}

theorem contextSet_assert_disjunctiveDiagonal :
    contextSet (assert (𝓟 cs) (disjunctiveDiagonal I sem)) = cs ∩ disjunctiveDiagonal I sem := by
  simp [contextSet]

theorem disjunctiveDiagonal_singleton :
    disjunctiveDiagonal (fun w => {interp w}) sem = diagonal interp sem := by
  ext w; simp [disjunctiveDiagonal, diagonal]

theorem diagonal_subset_disjunctiveDiagonal (h : ∀ w, interp w ∈ I w) :
    diagonal interp sem ⊆ disjunctiveDiagonal I sem :=
  fun w hw => ⟨interp w, h w, hw⟩

/-- Uniform Charity ([caie-2023] §2.2): where some compositional context makes an assertion true
at a world, the context that interprets it there is one that does. -/
def Charitable : Prop := ∀ w, (∃ c, sem c w) → sem (interp w) w

theorem inter_diagonal_of_charitable (hch : Charitable interp sem) (h : ∀ w ∈ cs, ∃ c, sem c w) :
    cs ∩ diagonal interp sem = cs :=
  inter_eq_left.2 fun w hw => hch w (h w hw)

/-! ### Contextual pruning -/

/-- Contextual Pruning ([caie-2023] §3): the contexts that interpret the next assertion at a
world are those that made this one true there. -/
def prune : W → Set C := fun w => {c ∈ I w | sem c w}

theorem prune_nonempty_iff (w : W) :
    (prune I sem w).Nonempty ↔ w ∈ disjunctiveDiagonal I sem := Iff.rfl

/-- Generalized Preservation ([caie-2023] §3): a context that uniquely interprets an assertion
at a world the assertion does not eliminate uniquely interprets the next assertion there. -/
theorem prune_singleton (w : W) (c₀ : C) (h : I w = {c₀}) (htrue : sem c₀ w) :
    prune I sem w = {c₀} := by
  ext c; simp [prune, h, and_iff_left_of_imp (fun hc : c = c₀ => hc ▸ htrue)]

/-! ### Context fragments -/

/-- The fragmentation of a context set: the ⟨compositional context, world⟩ pairs whose world is
in the context set and whose context interprets the assertion there. Conversational states of
this shape are those of [barker-2002-vagueness] and [barker-2013], where the non-world component
fixes the delineation of a gradable adjective. -/
def fragments : Set (C × W) := {f | f.2 ∈ cs ∧ f.1 ∈ I f.2}

/-- Updating a set of context fragments: drop every fragment whose context makes the assertion
false at its world. -/
def updateFragments (X : Set (C × W)) : Set (C × W) := {f ∈ X | sem f.1 f.2}

theorem fragments_prune :
    fragments (cs ∩ disjunctiveDiagonal I sem) (prune I sem)
      = updateFragments sem (fragments cs I) := by
  ext ⟨c, w⟩
  exact ⟨fun ⟨⟨hcs, _⟩, hc, hs⟩ => ⟨⟨hcs, hc⟩, hs⟩,
    fun ⟨⟨hcs, hc⟩, hs⟩ => ⟨⟨hcs, c, hc, hs⟩, hc, hs⟩⟩

theorem snd_image_updateFragments :
    Prod.snd '' updateFragments sem (fragments cs I) = cs ∩ disjunctiveDiagonal I sem := by
  ext w
  exact ⟨fun ⟨_, ⟨⟨hcs, hc⟩, hs⟩, hw⟩ => hw ▸ ⟨hcs, _, hc, hs⟩,
    fun ⟨hcs, c, hc, hs⟩ => ⟨⟨c, w⟩, ⟨⟨hcs, hc⟩, hs⟩, rfl⟩⟩

/-! ### Discourses -/

/-- A discourse: each assertion updates the context set and prunes the contexts available to its
successor. The worlds where an assertion does not occur are taken to have been eliminated
before it is evaluated, as they are in the paper. -/
def run : Set W → (W → Set C) → List (C → W → Prop) → Set W
  | cs, _, [] => cs
  | cs, I, sem :: rest => run (cs ∩ disjunctiveDiagonal I sem) (prune I sem) rest

theorem run_eq_inter (ss : List (C → W → Prop)) (h : ∀ w ∈ cs, (I w).Nonempty) :
    run cs I ss = cs ∩ disjunctiveDiagonal I fun c w => ∀ s ∈ ss, s c w := by
  induction ss generalizing cs I with
  | nil =>
    ext w
    exact ⟨fun hw => ⟨hw, (h w hw).imp fun _ hc => ⟨hc, by simp⟩⟩, And.left⟩
  | cons s rest ih =>
    rw [run, ih _ _ fun w hw => prune_nonempty_iff I s w |>.2 hw.2]
    ext w
    refine ⟨fun ⟨⟨hcs, _⟩, c, ⟨hc, hs⟩, hrest⟩ => ⟨hcs, c, hc, by simpa using ⟨hs, hrest⟩⟩,
      fun ⟨hcs, c, hc, hall⟩ => ?_⟩
    have hs := hall s List.mem_cons_self
    exact ⟨⟨hcs, c, hc, hs⟩, c, ⟨hc, hs⟩, fun t ht => hall t (List.mem_cons_of_mem _ ht)⟩

/-! ### Sarah's socks -/

/-- The two kinds of pairing of Sarah's four socks: two striped or two solid (matching), or one
striped and one solid (mixed). A dressing intension puts the pairings of one kind in the domain
of quantification of the configurational predicate *pair of socks* ([krifka-2009]), and Tim
likes the pairs of one kind and dislikes those of the other, so a compositional context and a
world of the reduced model are each a `Pairing`. -/
inductive Pairing | matching | mixed
  deriving DecidableEq

namespace SarahsSocks

/-- (1) *Sarah has two pairs of socks*: true under every dressing intension, since each puts
exactly two non-overlapping pairings in the domain, and so uninformative. -/
def hasTwoPairs : Pairing → Pairing → Prop := fun _ _ => True

/-- (2) *Tim likes both of them*: true when the pairings in the domain are of the kind Tim
likes. -/
def likesBoth (c w : Pairing) : Prop := c = w

/-- (3) *Both of them are matching*: true under a matching dressing intension, whatever Tim's
preferences. -/
def bothMatching (c : Pairing) (_ : Pairing) : Prop := c = .matching

/-- (4) *Tim dislikes both of them*: true when the pairings in the domain are of the kind Tim
dislikes. -/
def dislikesBoth (c w : Pairing) : Prop := c ≠ w

/-- (5) *Both of them are mixed*. -/
def bothMixed (c : Pairing) (_ : Pairing) : Prop := c = .mixed

/-- Initial Context ([caie-2023] §3): the presuppositions are symmetric between the two kinds of
pairing, so both intensions interpret (1) at every world. -/
def initial : Pairing → Set Pairing := fun _ => univ

/-- The Facts: Tim likes matching pairs of socks and dislikes mixed ones. -/
def facts : Set Pairing := {w | likesBoth .matching w}

/-- Tim Likes Matching: (1), (2), (3). -/
def timLikesMatching : List (Pairing → Pairing → Prop) := [hasTwoPairs, likesBoth, bothMatching]

/-- Tim Dislikes Mixed: (1), (4), (5). -/
def timDislikesMixed : List (Pairing → Pairing → Prop) := [hasTwoPairs, dislikesBoth, bothMixed]

/-- Safe Information for Tim Likes Matching: the discourse leaves exactly the worlds where the
Facts hold, so it conveys Tim's preference (condition (i)) and eliminates no world where it
holds (condition (ii)). -/
theorem run_timLikesMatching : run univ initial timLikesMatching = facts := by
  rw [run_eq_inter univ initial timLikesMatching fun w _ => ⟨.matching, mem_univ _⟩]
  ext w
  cases w <;>
    simp [timLikesMatching, disjunctiveDiagonal, initial, facts, hasTwoPairs, likesBoth,
      bothMatching]

/-- Safe Information for Tim Dislikes Mixed: the discourse that says the opposite of each of
(2) and (3) leaves the same worlds. -/
theorem run_timDislikesMixed : run univ initial timDislikesMixed = facts := by
  rw [run_eq_inter univ initial timDislikesMixed fun w _ => ⟨.matching, mem_univ _⟩]
  ext w
  cases w <;>
    simp [timDislikesMixed, disjunctiveDiagonal, initial, facts, hasTwoPairs, dislikesBoth,
      bothMixed, likesBoth]

/-! ### Why Standard Updating fails -/

/-- Minimal Symmetry gives the two discourses a compositional context that interprets their
common first sentence in both, and Preservation carries it to the second sentence of each. No
dressing intension makes both (2) and (4) true where the Facts hold, so one of the discourses
eliminates a world where they do: Safe Information (ii) fails. -/
theorem preservation_drops_fact_world (c : Pairing) :
    ¬(facts ⊆ diagonal (fun _ => c) likesBoth ∧ facts ⊆ diagonal (fun _ => c) dislikesBoth) :=
  fun ⟨h₁, h₂⟩ => h₂ rfl (h₁ rfl)

theorem exists_true_intension (w : Pairing) :
    (∃ c, likesBoth c w) ∧ (∃ c, dislikesBoth c w) ∧ (∃ c, bothMatching c w) ∧
      (∃ c, bothMixed c w) := by
  cases w
  · exact ⟨⟨_, rfl⟩, ⟨.mixed, by simp [dislikesBoth]⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · exact ⟨⟨_, rfl⟩, ⟨.matching, by simp [dislikesBoth]⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- Avoiding the first horn by letting the context shift between sentences costs the second:
under Uniform Charity (2) and (3) are each interpreted so as to come out true, neither
eliminates anything, and the worlds where Tim likes mixed pairs survive the discourse. Safe
Information (i) fails. -/
theorem charity_not_safe (interp₂ interp₃ : Pairing → Pairing)
    (h₂ : Charitable interp₂ likesBoth) (h₃ : Charitable interp₃ bothMatching) :
    ¬((univ ∩ diagonal interp₂ likesBoth) ∩ diagonal interp₃ bothMatching ⊆ facts) := by
  rw [inter_diagonal_of_charitable _ _ _ h₂ fun w _ => (exists_true_intension w).1,
    inter_diagonal_of_charitable _ _ _ h₃ fun w _ => (exists_true_intension w).2.2.1]
  intro h
  simpa [facts, likesBoth] using h (mem_univ .mixed)

end SarahsSocks

end Caie2023
