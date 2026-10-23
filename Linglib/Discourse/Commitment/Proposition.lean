module

public import Linglib.Core.Relation.SetRel
public import Linglib.Logic.Modal.Basic
public import Linglib.Discourse.Commitment.Basic

/-!
# Commitment propositions

In Krifka's account a commitment is itself a proposition, so `k⊢φ` holds at the worlds where `k`
vouches for `φ`. Over an accessibility `O k` for each holder `k` it is the core of `φ`, the worlds
all of whose `O k`-successors are `φ`-worlds. It is closed under consequence and conjunction, its
complement is the refusal `¬k⊢φ`, and a common ground can contain it without containing `φ`.
Asserting `φ` is the performative update that makes `k⊢φ` hold everywhere. Public commitment sets
give the accessibilities that do not depend on the world, and a commitment state of
`Commitment.Basic` projects onto them. Indices that pair a fact with every holder's commitment set
are the canonical model in which commitments vary from world to world.

## Main definitions

* `Commitment.committed O k φ`: `k⊢φ`.
* `Commitment.perform O k φ`: the performative update by `k`'s commitment to `φ`.
* `Commitment.ofSets P`: the accessibility of the public commitment sets `P`.
* `Commitment.Index κ F`: a fact with a non-empty commitment set for each holder, with its
  accessibility `Commitment.Index.access`.

## Main results

* `Commitment.committed_perform_self`: after the performative update `k⊢φ` holds everywhere.
* `Commitment.committed_iInter`: a commitment to each of a family of propositions is a commitment
  to their conjunction.
* `Commitment.disjoint_committed_compl`: a holder whose commitments are consistent is not
  committed to both `φ` and `¬φ`, so `k⊢¬φ` entails the refusal `¬k⊢φ`.
* `Commitment.committed_ofSets`: a public commitment holds everywhere or nowhere.
* `Commitment.ofSets_commitmentSet_insert`: adding a commitment to a commitment state is the
  performative update of its commitment sets.

## References

* [M. Krifka, *Bias in Commitment Space Semantics: Declarative Questions, Negated Questions,
  and Question Tags* (2015)][krifka-2015]
* [M. Krifka, *Performative updates and the modeling of speech acts* (2024)][krifka-2024a]
* [T. van der Leer, *Commitments, beliefs and expectations in conversation*
  (2026)][van-der-leer-2026]
-/

@[expose] public section

namespace Commitment

open ModalLogic (IsSerial IsEuclidean IsK45Frame)
open scoped SetRel

variable {κ W : Type*} (O : κ → SetRel W W) (k : κ) (φ ψ : Set W)

/-- The proposition `k⊢φ` holds at the worlds all of whose `O k`-successors are `φ`-worlds, where
`k` is committed to `φ`. -/
def committed : Set W := (O k).core φ

/-- The performative update by `k`'s commitment to `φ` keeps the `φ`-successors of `O k` and
leaves every other accessibility unchanged ([van-der-leer-2026] Definition 4). -/
def perform : κ → SetRel W W := fun k' ↦ {p | p ∈ O k' ∧ (k' = k → p.2 ∈ φ)}

variable {O k φ ψ} {k' : κ}

@[simp] theorem mem_committed {w : W} : w ∈ committed O k φ ↔ ∀ ⦃v⦄, w ~[O k] v → v ∈ φ := .rfl

theorem committed_mono (h : φ ⊆ ψ) : committed O k φ ⊆ committed O k ψ :=
  SetRel.core_subset_core h

theorem committed_inter : committed O k (φ ∩ ψ) = committed O k φ ∩ committed O k ψ :=
  SetRel.core_inter _ _ _

@[simp] theorem committed_univ : committed O k Set.univ = Set.univ := SetRel.core_univ

theorem committed_iInter {ι : Sort*} (φ : ι → Set W) :
    committed O k (⋂ i, φ i) = ⋂ i, committed O k (φ i) := by
  ext
  simp only [mem_committed, Set.mem_iInter]
  exact ⟨fun h i _ hv ↦ h hv i, fun h _ hv i ↦ h i hv⟩

theorem disjoint_committed_compl [IsSerial (O k)] :
    Disjoint (committed O k φ) (committed O k φᶜ) :=
  Set.disjoint_left.2 fun w h h' ↦
    let ⟨_, hv⟩ := IsSerial.serial (R := O k) w
    h' hv (h hv)

@[simp] theorem mem_perform {p : W × W} :
    p ∈ perform O k φ k' ↔ p ∈ O k' ∧ (k' = k → p.2 ∈ φ) := .rfl

theorem perform_subset (k' : κ) : perform O k φ k' ⊆ O k' := fun _ h ↦ h.1

theorem perform_of_ne (h : k' ≠ k) : perform O k φ k' = O k' :=
  Set.ext fun _ ↦ ⟨And.left, fun hp ↦ ⟨hp, (absurd · h)⟩⟩

@[simp] theorem committed_perform_self : committed (perform O k φ) k φ = Set.univ :=
  Set.eq_univ_of_forall fun _ _ h ↦ h.2 rfl

theorem perform_mono (h : φ ⊆ ψ) (k' : κ) : perform O k φ k' ⊆ perform O k ψ k' :=
  fun _ hp ↦ ⟨hp.1, fun e ↦ h (hp.2 e)⟩

theorem perform_perform : perform (perform O k φ) k ψ = perform O k (φ ∩ ψ) :=
  funext fun _ ↦ Set.ext fun _ ↦ by
    simp only [mem_perform, Set.mem_inter_iff]
    tauto

theorem perform_eq_self_iff : perform O k φ = O ↔ committed O k φ = Set.univ := by
  refine ⟨fun h ↦ by rw [← committed_perform_self (O := O), h], fun h ↦ ?_⟩
  funext k'
  refine Set.ext fun p ↦ ⟨And.left, fun hp ↦ ⟨hp, fun e ↦ ?_⟩⟩
  subst e
  exact Set.eq_univ_iff_forall.1 h p.1 hp

instance [IsK45Frame (O k')] : IsK45Frame (perform O k φ k') where
  trans _ _ _ h₁ h₂ := ⟨(O k').trans h₁.1 h₂.1, h₂.2⟩
  eucl _ _ _ h₁ h₂ := ⟨IsEuclidean.eucl _ _ _ h₁.1 h₂.1, h₂.2⟩

/-! ### Public commitment sets -/

variable (P : κ → Set W)

/-- From every world, the accessibility of the public commitment sets `P` reaches exactly the
worlds compatible with `k`'s commitments. -/
def ofSets : κ → SetRel W W := fun k ↦ SetRel.ofSuccessors fun _ ↦ P k

instance : IsK45Frame (ofSets P k) where
  trans _ _ _ _ h := h
  eucl _ _ _ _ h := h

theorem committed_ofSets : committed (ofSets P) k φ = {_w | P k ⊆ φ} := rfl

theorem perform_ofSets : perform (ofSets P) k φ = ofSets fun k' ↦ {v ∈ P k' | k' = k → v ∈ φ} :=
  rfl

theorem ofSets_commitmentSet_insert (K : State κ W) (k : κ) (φ : Set W) :
    ofSets (insert (k, φ) K).commitmentSet = perform (ofSets K.commitmentSet) k φ := by
  rw [perform_ofSets]
  congr 1
  funext k'
  by_cases h : k' = k
  · subst h
    rw [State.commitmentSet_insert_self]
    ext
    simp [and_comm]
  · rw [State.commitmentSet_insert_of_ne h]
    ext
    simp [h]

/-! ### Indices -/

/-- An index fixes a fact and, for each holder, the non-empty set of facts its commitments leave
open. -/
structure Index (κ F : Type*) where
  /-- The fact at the index. -/
  fact : F
  /-- The facts left open by `k`'s commitments. -/
  commitmentSet : κ → Set F
  commitmentSet_nonempty : ∀ k, (commitmentSet k).Nonempty

namespace Index

variable {F : Type*}

/-- From an index, `k` reaches the indices with the same commitment sets whose fact is left open
by `k`'s commitments. -/
def access : κ → SetRel (Index κ F) (Index κ F) :=
  fun k ↦ {p | p.2.fact ∈ p.1.commitmentSet k ∧ p.2.commitmentSet = p.1.commitmentSet}

instance : IsSerial (access (F := F) k) where
  serial w := ⟨⟨(w.commitmentSet_nonempty k).some, w.commitmentSet, w.commitmentSet_nonempty⟩,
    (w.commitmentSet_nonempty k).some_mem, rfl⟩

instance : IsK45Frame (access (F := F) k) where
  trans _ _ _ h₁ h₂ := ⟨h₁.2 ▸ h₂.1, h₂.2.trans h₁.2⟩
  eucl _ _ _ h₁ h₂ := ⟨h₁.2 ▸ h₂.1, h₂.2.trans h₁.2.symm⟩

theorem committed_access_preimage (φ : Set F) :
    committed access k (fact ⁻¹' φ) = {w : Index κ F | w.commitmentSet k ⊆ φ} :=
  Set.ext fun w ↦ ⟨fun h x hx ↦ h (b := ⟨x, w.commitmentSet, w.commitmentSet_nonempty⟩) ⟨hx, rfl⟩,
    fun h _ hv ↦ h hv.1⟩

end Index

end Commitment
