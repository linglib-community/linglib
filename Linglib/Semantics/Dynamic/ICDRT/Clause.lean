module

public import Linglib.Core.Data.Set.Monad
public import Linglib.Semantics.Dynamic.ICDRT
public import Mathlib.Order.Minimal

/-!
# Clauses of intensional CDRT

A clause is a computation in `StateT (State W E) Set` that returns its local context: from an input
state, the pairs of a context in which it holds and an output state. Maximization keeps the runs
whose context is maximal, so the truth conditions of the operators compose
(`Clause.HasTruthSet`) with no reference to the names of the drefs that store the contexts.
Hofmann's fragment writes each operator as a DRS that reads its context from a register;
`Clause.drs` is that reading, and each operator is its DRS (`drs_not`, `drs_connective`,
`drs_believed`, `dec_eq`) with maximization over the values of the register (`maxInput`).

## Implementation notes

`W` and `E` share a universe, as `StateT` requires. `Clause.dec` is the relation between states that
an assertion induces, and it reads the commitment set from the input.

## References

* [hofmann-2025]
-/

@[expose] public section

attribute [local instance] Set.monad

universe u

namespace ICDRT

open DynamicSemantics
open DynamicSemantics.Update (test box Fixes mem_box_singleton_comp)
open SetRel

variable {W E : Type u} {i j k : State W E} {s t : Set W} {R S : E → W → Prop} {v v' : IVar}
  {φ φ' φ'' r r' : PVar}

/-! ### Clauses -/

/-- A clause, of type `wt`, computes its local context: from an input state, the pairs of a context
in which it holds and an output state. -/
abbrev Clause (W E : Type u) := StateT (State W E) Set (Set W)

/-- Any context that entails `c`, with no change of state. -/
def within (c : Set W) : Clause W E := fun i ↦ {p | p.1 ⊆ c ∧ p.2 = i}

/-- Store a context in a propositional dref. -/
def record (φ : PVar) (s : Set W) : StateT (State W E) Set PUnit :=
  fun i ↦ {(PUnit.unit, i.updateProp φ s)}

/-- A common noun or intransitive verb holds in a context where its argument satisfies it
([hofmann-2025] App. C (15)). -/
def commonNoun (R : E → W → Prop) (v : IVar) : Clause W E :=
  fun i ↦ within (sat R (i.indiv v)) i

/-- The indefinite introduces its dref with a referent at exactly the worlds of the context, in
which its restrictor and its scope hold ([hofmann-2025] App. C (16)). -/
def indefinite (v : IVar) (P P' : IVar → Clause W E) : Clause W E :=
  fun i ↦ {p | ∃ e k, p.1 = e.Dom ∧ (p.1, k) ∈ P v (i.updateIndiv v e) ∧ p ∈ P' v k}

/-- A pronoun passes its index to the predicate ([hofmann-2025] App. C (17)). -/
def pronoun (v : IVar) (P : IVar → Clause W E) : Clause W E := P v

/-- A proper name introduces a dref equal to its constant ([hofmann-2025] App. C (14)). -/
def properName (a : E) (v : IVar) (P : IVar → Clause W E) : Clause W E :=
  fun i ↦ P v (i.updateIndiv v (PFun.lift fun _ ↦ a))

namespace Clause

/-- Maximization keeps the runs whose context is maximal among the contexts of the clause. -/
def maximal (P : Clause W E) : Clause W E :=
  fun i ↦ {p ∈ P i | Maximal (fun s ↦ ∃ j, (s, j) ∈ P i) p.1}

/-- Negation stores the prejacent's context and returns its complement
([hofmann-2025] App. C (18a)). -/
def not (P : Clause W E) (φ' : PVar) : Clause W E :=
  show StateT (State W E) Set (Set W) from do
    let s ← P.maximal
    record φ' s
    pure sᶜ

/-- A binary connective stores the context of each operand and relates its own to them by the
static function `f` ([hofmann-2025] App. C (18b), (18c)). -/
def connective (f : Set W → Set W → Set W) (P Q : Clause W E) (φ' φ'' : PVar) : Clause W E :=
  show StateT (State W E) Set (Set W) from do
    let s ← P.maximal
    record φ' s
    let t ← Q.maximal
    record φ'' t
    pure (f s t)

/-- Disjunction's context is the union of the contexts of its disjuncts (App. C (18b)). -/
abbrev or (P Q : Clause W E) (φ' φ'' : PVar) : Clause W E := connective (· ∪ ·) P Q φ' φ''

/-- The conditional's context is the union of the antecedent's complement and the consequent's
context (App. C (18c)). -/
abbrev ifThen (P Q : Clause W E) (φ' φ'' : PVar) : Clause W E :=
  connective (fun s t ↦ sᶜ ∪ t) P Q φ' φ''

/-- An attitude verb stores its complement's context and holds where the subject's doxastic state
entails it ([hofmann-2025] App. C (18e), fn. 14). -/
def believed (dox : E → W → Set W) (P : Clause W E) (φ' : PVar) (v : IVar) : Clause W E :=
  show StateT (State W E) Set (Set W) from do
    let i ← get
    let s ← P.maximal
    record φ' s
    within (sat (fun a w ↦ dox a w ⊆ s) (i.indiv v))

/-- A veridical attitude's context, moreover, entails its complement's ([hofmann-2025] §2.4). -/
def knows (dox : E → W → Set W) (P : Clause W E) (φ' : PVar) (v : IVar) : Clause W E :=
  show StateT (State W E) Set (Set W) from do
    let i ← get
    let s ← P.maximal
    record φ' s
    within (s ∩ sat (fun a w ↦ dox a w ⊆ s) (i.indiv v))

/-- The declarative stores the maximal context of the clause, which the speaker's commitments
entail ([hofmann-2025] (20a), App. C (19)). -/
def dec (P : Clause W E) (r φ : PVar) : Update (State W E) :=
  {p | ∃ s k, (s, k) ∈ P.maximal p.1 ∧ p.1.prop r ⊆ s ∧ p.2 = k.updateProp φ s}

end Clause

/-! ### Truth sets -/

variable {P Q : Clause W E} {T : State W E → Set W} {f : Set W → Set W → Set W}
  {dox : E → W → Set W}

/-- A clause has truth set `T` if `T` is its greatest context. -/
def Clause.HasTruthSet (P : Clause W E) (T : State W E → Set W) : Prop :=
  ∀ i, IsGreatest {s | ∃ j, (s, j) ∈ P i} (T i)

theorem Clause.HasTruthSet.mem_maximal (hP : P.HasTruthSet T) :
    (s, j) ∈ P.maximal i ↔ s = T i ∧ (T i, j) ∈ P i := by
  have h : Maximal (fun s ↦ ∃ j, (s, j) ∈ P i) s ↔ s = T i := (hP i).maximal_iff
  simp only [Clause.maximal, Set.mem_ofPred_eq, h]
  exact ⟨fun ⟨hj, hs⟩ ↦ ⟨hs, hs ▸ hj⟩, fun ⟨hs, hj⟩ ↦ ⟨hs ▸ hj, hs⟩⟩

theorem Clause.mem_dec : i ~[P.dec r φ] j ↔ ∃ s k, (s, k) ∈ P.maximal i ∧ i.prop r ⊆ s ∧
    j = k.updateProp φ s := Iff.rfl

theorem Clause.HasTruthSet.mem_dec (hP : P.HasTruthSet T) :
    i ~[P.dec r φ] j ↔ i.prop r ⊆ T i ∧ ∃ k, (T i, k) ∈ P i ∧ j = k.updateProp φ (T i) := by
  simp only [Clause.mem_dec, hP.mem_maximal]
  exact ⟨fun ⟨_, k, ⟨rfl, hk⟩, hr, hj⟩ ↦ ⟨hr, k, hk, hj⟩,
    fun ⟨hr, k, hk, hj⟩ ↦ ⟨_, k, ⟨rfl, hk⟩, hr, hj⟩⟩

theorem Clause.HasTruthSet.mem_dom_dec (hP : P.HasTruthSet T) :
    i ∈ (P.dec r φ).dom ↔ i.prop r ⊆ T i := by
  simp only [SetRel.mem_dom, hP.mem_dec]
  refine ⟨fun ⟨_, h, _⟩ ↦ h, fun h ↦ ?_⟩
  obtain ⟨k, hk⟩ := (hP i).1
  exact ⟨_, h, k, hk, rfl⟩

theorem mem_within {c : Set W} : (s, j) ∈ (within c : Clause W E) i ↔ s ⊆ c ∧ j = i := Iff.rfl

theorem Clause.mem_not : (s, j) ∈ P.not φ' i ↔
    ∃ t k, (t, k) ∈ P.maximal i ∧ s = tᶜ ∧ j = k.updateProp φ' t := by
  simp [Clause.not, record, and_left_comm]

theorem Clause.mem_connective : (s, j) ∈ Clause.connective f P Q φ' φ'' i ↔
    ∃ t k, (t, k) ∈ P.maximal i ∧ ∃ u l, (u, l) ∈ Q.maximal (k.updateProp φ' t) ∧ s = f t u ∧
      j = l.updateProp φ'' u := by
  simp [Clause.connective, record]

theorem Clause.mem_believed : (s, j) ∈ Clause.believed dox P φ' v i ↔
    ∃ t k, (t, k) ∈ P.maximal i ∧ s ⊆ sat (fun a w ↦ dox a w ⊆ t) (i.indiv v) ∧
      j = k.updateProp φ' t := by
  simp [Clause.believed, record, within, get, getThe, MonadStateOf.get, StateT.get]

theorem Clause.mem_knows : (s, j) ∈ Clause.knows dox P φ' v i ↔
    ∃ t k, (t, k) ∈ P.maximal i ∧ s ⊆ t ∩ sat (fun a w ↦ dox a w ⊆ t) (i.indiv v) ∧
      j = k.updateProp φ' t := by
  simp [Clause.knows, record, within, get, getThe, MonadStateOf.get, StateT.get]

theorem Clause.HasTruthSet.not (hP : P.HasTruthSet T) : (P.not φ').HasTruthSet fun i ↦ (T i)ᶜ :=
  fun i ↦ by
    refine ⟨?_, fun s ⟨j, hj⟩ ↦ ?_⟩
    · obtain ⟨j, hj⟩ := (hP i).1
      exact ⟨_, Clause.mem_not.mpr ⟨_, j, hP.mem_maximal.mpr ⟨rfl, hj⟩, rfl, rfl⟩⟩
    · obtain ⟨t, k, ht, rfl, -⟩ := Clause.mem_not.mp hj
      rw [(hP.mem_maximal.mp ht).1]

theorem Clause.HasTruthSet.mem_maximal_not (hP : P.HasTruthSet T) :
    (s, j) ∈ (P.not φ').maximal i ↔ s = (T i)ᶜ ∧
      ∃ k, (T i, k) ∈ P i ∧ j = k.updateProp φ' (T i) := by
  rw [(hP.not (φ' := φ')).mem_maximal, Clause.mem_not]
  simp only [hP.mem_maximal]
  exact ⟨fun ⟨hs, _, k, ⟨rfl, hk⟩, _, hj⟩ ↦ ⟨hs, k, hk, hj⟩,
    fun ⟨hs, k, hk, hj⟩ ↦ ⟨hs, _, k, ⟨rfl, hk⟩, rfl, hj⟩⟩

/-! ### Existentials and pronouns -/

/-- *There is an `R`* ([hofmann-2025] (24)) is the indefinite with a vacuous scope (fn. 8). -/
def existential (R : E → W → Prop) (v : IVar) : Clause W E :=
  indefinite v (commonNoun R) fun _ ↦ within Set.univ

/-- *It is `S`* ([hofmann-2025] (30)) is the pronoun with the predicate. -/
def it (S : E → W → Prop) (v : IVar) : Clause W E := pronoun v (commonNoun S)

theorem mem_existential :
    (s, j) ∈ existential R v i ↔ ∃ e, IsWitness R s e ∧ j = i.updateIndiv v e := by
  simp only [existential, indefinite, commonNoun, Set.mem_ofPred_eq, mem_within, IsWitness]
  constructor
  · rintro ⟨e, k, hd, ⟨hs, rfl⟩, -, rfl⟩
    exact ⟨e, ⟨hd, by simpa using hs⟩, rfl⟩
  · rintro ⟨e, ⟨hd, hs⟩, rfl⟩
    exact ⟨e, _, hd, ⟨by simpa using hs, rfl⟩, Set.subset_univ _, rfl⟩

theorem mem_it : (s, j) ∈ it S v i ↔ s ⊆ sat S (i.indiv v) ∧ j = i := Iff.rfl

theorem hasTruthSet_existential : (existential R v).HasTruthSet fun _ ↦ witnessed R := fun i ↦ by
  refine ⟨?_, fun s ⟨j, hj⟩ ↦ ?_⟩
  · obtain ⟨e, he, -⟩ := exists_isWitness_sat (subset_refl (witnessed R)) ⊤
    exact ⟨_, mem_existential.mpr ⟨e, he, rfl⟩⟩
  · obtain ⟨e, he, -⟩ := mem_existential.mp hj
    exact he.subset_witnessed

theorem hasTruthSet_it : (it S v).HasTruthSet fun i ↦ sat S (i.indiv v) := fun i ↦
  ⟨⟨i, mem_it.mpr ⟨subset_rfl, rfl⟩⟩, fun _ ⟨_, h⟩ ↦ (mem_it.mp h).1⟩

theorem mem_dec_existential :
    i ~[(existential R v).dec r φ] j ↔ i.prop r ⊆ witnessed R ∧
      ∃ e, IsWitness R (witnessed R) e ∧ j = (i.updateIndiv v e).updateProp φ (witnessed R) := by
  simp [hasTruthSet_existential.mem_dec, mem_existential]

theorem mem_dec_not_existential :
    i ~[((existential R v).not φ').dec r φ] j ↔ i.prop r ⊆ (witnessed R)ᶜ ∧
      ∃ e, IsWitness R (witnessed R) e ∧
        j = ((i.updateIndiv v e).updateProp φ' (witnessed R)).updateProp φ (witnessed R)ᶜ := by
  simp [hasTruthSet_existential.not.mem_dec, Clause.mem_not, hasTruthSet_existential.mem_maximal,
    mem_existential, and_left_comm]

theorem mem_dec_not_not_existential :
    i ~[(((existential R v).not φ'').not φ').dec r φ] j ↔ i.prop r ⊆ witnessed R ∧
      ∃ e, IsWitness R (witnessed R) e ∧ j = (((i.updateIndiv v e).updateProp φ''
        (witnessed R)).updateProp φ' (witnessed R)ᶜ).updateProp φ (witnessed R) := by
  have hP := hasTruthSet_existential (R := R) (v := v)
  simp [hP.not.not.mem_dec, Clause.mem_not, hP.not.mem_maximal, hP.mem_maximal, mem_existential,
    and_left_comm]

theorem mem_dec_it :
    i ~[(it S v).dec r φ] j ↔ i.prop r ⊆ sat S (i.indiv v) ∧
      j = i.updateProp φ (sat S (i.indiv v)) := by
  simp [hasTruthSet_it.mem_dec, mem_it]

/-! ### Connectives over a pronoun -/

section Connective

variable {A : Set W} {g : State W E → (W →. E) → State W E}

theorem mem_connective_it
    (hP : ∀ {i t k}, (t, k) ∈ P.maximal i ↔ t = A ∧ ∃ e, IsWitness R (witnessed R) e ∧ k = g i e)
    (hg : ∀ i e, (g i e).indiv v = e) :
    (s, j) ∈ Clause.connective f P (it S v) φ φ'' i ↔ ∃ e, IsWitness R (witnessed R) e ∧
      s = f A (sat S e) ∧ j = ((g i e).updateProp φ A).updateProp φ'' (sat S e) := by
  simp only [Clause.mem_connective, hP, hasTruthSet_it.mem_maximal, mem_it, State.updateProp_indiv]
  constructor
  · rintro ⟨_, _, ⟨rfl, e, he, rfl⟩, _, _, ⟨hu, -, rfl⟩, rfl, rfl⟩
    rw [hg] at hu
    subst hu
    exact ⟨e, he, rfl, rfl⟩
  · rintro ⟨e, he, rfl, rfl⟩
    exact ⟨_, g i e, ⟨rfl, e, he, rfl⟩, sat S e, _, ⟨by rw [hg], by rw [hg], rfl⟩, rfl, rfl⟩

theorem hasTruthSet_connective_it
    (hP : ∀ {i t k}, (t, k) ∈ P.maximal i ↔ t = A ∧ ∃ e, IsWitness R (witnessed R) e ∧ k = g i e)
    (hg : ∀ i e, (g i e).indiv v = e) (hf : Monotone (f A)) :
    (Clause.connective f P (it S v) φ φ'').HasTruthSet fun _ ↦ f A (witnessed (R ⊓ S)) := fun i ↦ by
  refine ⟨?_, fun s ⟨j, hj⟩ ↦ ?_⟩
  · obtain ⟨e, he, h⟩ := exists_isWitness_sat_eq R S
    exact ⟨_, (mem_connective_it hP hg).mpr ⟨e, he, by rw [h], rfl⟩⟩
  · obtain ⟨e, he, rfl, -⟩ := (mem_connective_it hP hg).mp hj
    exact hf (he.sat_subset.trans Set.inter_subset_right)

end Connective

theorem mem_maximal_existential : (s, j) ∈ (existential R v).maximal i ↔ s = witnessed R ∧
    ∃ e, IsWitness R (witnessed R) e ∧ j = i.updateIndiv v e := by
  rw [hasTruthSet_existential.mem_maximal, mem_existential]

theorem mem_maximal_not_existential : (s, j) ∈ ((existential R v).not φ').maximal i ↔
    s = (witnessed R)ᶜ ∧ ∃ e, IsWitness R (witnessed R) e ∧
      j = (i.updateIndiv v e).updateProp φ' (witnessed R) := by
  simp [hasTruthSet_existential.mem_maximal_not, mem_existential]

/-! ### Attitudes -/

variable {a : E}

/-- *`a` believes it is `S`* (52). -/
abbrev believes (a : E) (dox : E → W → Set W) (S : E → W → Prop) (v v' : IVar) (φ' : PVar) :
    Clause W E :=
  properName a v' (Clause.believed dox (it S v) φ')

theorem mem_believes (hv : v ≠ v') : (s, j) ∈ believes a dox S v v' φ' i ↔
    s ⊆ {w | dox a w ⊆ sat S (i.indiv v)} ∧
      j = (i.updateIndiv v' (PFun.lift fun _ ↦ a)).updateProp φ' (sat S (i.indiv v)) := by
  have hυ : (i.updateIndiv v' (PFun.lift fun _ ↦ a)).indiv v = i.indiv v :=
    State.updateIndiv_indiv_of_ne _ hv _
  simp only [properName, Clause.mem_believed, hasTruthSet_it.mem_maximal, mem_it, hυ,
    State.updateIndiv_indiv_self, sat_lift_const]
  constructor
  · rintro ⟨_, _, ⟨rfl, -, rfl⟩, hs, rfl⟩
    exact ⟨hs, rfl⟩
  · rintro ⟨hs, rfl⟩
    exact ⟨_, _, ⟨rfl, subset_rfl, rfl⟩, hs, rfl⟩

theorem hasTruthSet_believes (hv : v ≠ v') :
    (believes a dox S v v' φ').HasTruthSet fun i ↦ {w | dox a w ⊆ sat S (i.indiv v)} := fun _ ↦
  ⟨⟨_, (mem_believes hv).mpr ⟨subset_rfl, rfl⟩⟩, fun _ ⟨_, h⟩ ↦ ((mem_believes hv).mp h).1⟩

theorem mem_dec_believes (hv : v ≠ v') :
    i ~[(believes a dox S v v' φ').dec r φ] j ↔ i.prop r ⊆ {w | dox a w ⊆ sat S (i.indiv v)} ∧
      j = ((i.updateIndiv v' (PFun.lift fun _ ↦ a)).updateProp φ' (sat S (i.indiv v))).updateProp φ
        {w | dox a w ⊆ sat S (i.indiv v)} := by
  simp [(hasTruthSet_believes hv).mem_dec, mem_believes hv]

/-! ### Clauses as DRSs -/

section DRS

variable {D : Update (State W E)}

/-- Maximization (40), with its comparison class repaired, runs `D` at the inputs whose value of `φ`
is maximal among the values at which `D` succeeds. -/
def maxInput (φ : PVar) (D : Update (State W E)) : Update (State W E) :=
  test {i | Maximal (fun s ↦ i.updateProp φ s ∈ D.dom) (i.prop φ)} ○ D

theorem mem_maxInput :
    i ~[maxInput φ D] j ↔ Maximal (fun s ↦ i.updateProp φ s ∈ D.dom) (i.prop φ) ∧ i ~[D] j :=
  Update.mem_test_comp

theorem maxInput_subset (φ : PVar) (D : Update (State W E)) : maxInput φ D ⊆ D :=
  fun _ h ↦ (mem_maxInput.mp h).2

/-- The clause as the paper writes it, reading its context from the register `φ`. -/
def Clause.drs (P : Clause W E) (φ : PVar) : Update (State W E) := {p | (p.1.prop φ, p.2) ∈ P p.1}

/-- A clause neither reads nor writes the register `φ`. -/
def Clause.Frame (P : Clause W E) (φ : PVar) : Prop :=
  ∀ i t s k, (s, k) ∈ P (i.updateProp φ t) ↔ ∃ k', (s, k') ∈ P i ∧ k = k'.updateProp φ t

theorem frame_existential : (existential R v).Frame φ := fun i t s k ↦ by
  simp only [mem_existential, State.updateProp_updateIndiv]
  exact ⟨fun ⟨e, he, hk⟩ ↦ ⟨_, ⟨e, he, rfl⟩, hk⟩, fun ⟨_, ⟨e, he, rfl⟩, hk⟩ ↦ ⟨e, he, hk⟩⟩

theorem Clause.Frame.maximal (hP : P.Frame φ) : P.maximal.Frame φ := fun i t s k ↦ by
  have hd : (fun s ↦ ∃ j, (s, j) ∈ P (i.updateProp φ t)) = fun s ↦ ∃ j, (s, j) ∈ P i := by
    funext s
    simp only [hP i t s]
    exact propext ⟨fun ⟨_, k, hk, _⟩ ↦ ⟨k, hk⟩, fun ⟨k, hk⟩ ↦ ⟨_, k, hk, rfl⟩⟩
  simp only [Clause.maximal, Set.mem_ofPred_eq, hd, hP i t s k]
  exact ⟨fun ⟨⟨k', hk, h⟩, hm⟩ ↦ ⟨k', ⟨hk, hm⟩, h⟩, fun ⟨k', ⟨hk, hm⟩, h⟩ ↦ ⟨⟨k', hk, h⟩, hm⟩⟩

theorem Clause.Frame.not (hP : P.Frame φ) (hφ : φ ≠ φ') : (P.not φ').Frame φ := fun i t s k ↦ by
  simp only [Clause.mem_not, hP.maximal i t]
  constructor
  · rintro ⟨u, _, ⟨l, hl, rfl⟩, rfl, rfl⟩
    exact ⟨_, ⟨u, l, hl, rfl, rfl⟩, State.updateProp_comm _ hφ _ _⟩
  · rintro ⟨_, ⟨u, l, hl, rfl, rfl⟩, rfl⟩
    exact ⟨u, _, ⟨l, hl, rfl⟩, rfl, State.updateProp_comm _ hφ.symm _ _⟩

theorem mem_updateProp_maxInput_drs (hP : P.Frame φ) :
    i.updateProp φ s ~[maxInput φ (P.drs φ)] j ↔
      ∃ k, (s, k) ∈ P.maximal i ∧ j = k.updateProp φ s := by
  have hm {s : Set W} {j : State W E} : i.updateProp φ s ~[P.drs φ] j ↔
      ∃ k, (s, k) ∈ P i ∧ j = k.updateProp φ s := by
    show ((i.updateProp φ s).prop φ, j) ∈ P _ ↔ _
    rw [State.updateProp_prop_self, hP]
  have hd : (fun t ↦ i.updateProp φ t ∈ (P.drs φ).dom) = fun s ↦ ∃ k, (s, k) ∈ P i :=
    funext fun t ↦ propext ⟨fun ⟨_, h⟩ ↦ (hm.mp h).imp fun _ h ↦ h.1,
      fun ⟨k, h⟩ ↦ ⟨_, hm.mpr ⟨k, h, rfl⟩⟩⟩
  simp only [mem_maxInput, State.updateProp_updateProp_self, State.updateProp_prop_self, hd, hm,
    Clause.maximal, Set.mem_ofPred_eq]
  exact ⟨fun ⟨hmax, k, hk, hj⟩ ↦ ⟨k, ⟨hk, hmax⟩, hj⟩, fun ⟨k, ⟨hk, hmax⟩, hj⟩ ↦ ⟨hmax, k, hk, hj⟩⟩

theorem mem_box_comp_maxInput_drs (hP : P.Frame φ') {C : Condition (State W E)} :
    i ~[box {φ'} C ○ maxInput φ' (P.drs φ')] j ↔
      ∃ s k, (s, k) ∈ P.maximal i ∧ i.updateProp φ' s ∈ C ∧ j = k.updateProp φ' s := by
  rw [mem_box_singleton_comp]
  simp only [extend_pvar, mem_updateProp_maxInput_drs hP]
  exact ⟨fun ⟨s, hC, k, hk, hj⟩ ↦ ⟨s, k, hk, hC, hj⟩, fun ⟨s, k, hk, hC, hj⟩ ↦ ⟨s, hC, k, hk, hj⟩⟩

-- [hofmann-2025] App. C (14)
theorem drs_properName {a : E} {P : IVar → Clause W E} :
    (properName a v P).drs φ = box {v} {j | j.indiv v = PFun.lift fun _ ↦ a} ○ (P v).drs φ := by
  ext ⟨i, j⟩
  rw [mem_box_singleton_comp]
  constructor
  · intro h
    exact ⟨_, by simp, h⟩
  · rintro ⟨e, he, h⟩
    obtain rfl : e = PFun.lift fun _ ↦ a := by simpa using he
    exact h

-- [hofmann-2025] App. C (15), (17)
theorem drs_commonNoun : (commonNoun R v).drs φ = test (predication R φ v) := by
  ext ⟨i, j⟩
  simp only [Clause.drs, commonNoun, Set.mem_ofPred_eq, mem_within, Update.mem_test,
    mem_predication]
  exact ⟨fun ⟨h, hj⟩ ↦ ⟨hj.symm, hj ▸ h⟩, fun ⟨hj, h⟩ ↦ ⟨hj ▸ h, hj.symm⟩⟩

-- [hofmann-2025] App. C (16), where the restrictor leaves the context alone
theorem drs_indefinite {P P' : IVar → Clause W E}
    (hP : ∀ i, ∀ p ∈ P v i, p.2.prop φ = i.prop φ) :
    (indefinite v P P').drs φ = relUpdate φ v ○ (P v).drs φ ○ (P' v).drs φ := by
  ext ⟨i, j⟩
  constructor
  · rintro ⟨e, k, hd, hk, hj⟩
    refine ⟨k, ⟨_, updateIndiv_mem_relUpdate hd, by simpa [Clause.drs] using hk⟩, ?_⟩
    have := hP _ _ hk
    simp only [State.updateIndiv_prop] at this
    simpa [Clause.drs, this] using hj
  · rintro ⟨k, ⟨_, hl, hk⟩, hj⟩
    obtain ⟨⟨e, rfl⟩, hd⟩ := mem_relUpdate.mp hl
    have hk' : (i.prop φ, k) ∈ P v (i.updateIndiv v e) := by simpa [Clause.drs] using hk
    have := hP _ _ hk'
    simp only [State.updateIndiv_prop] at this
    exact ⟨e, k, by simpa using hd, hk', by simpa [Clause.drs, this] using hj⟩

-- [hofmann-2025] App. C (24)
theorem drs_existential : (existential R v).drs φ = relUpdate φ v ○ test (predication R φ v) := by
  ext ⟨i, j⟩
  simp only [Clause.drs, Set.mem_ofPred_eq, mem_existential, IsWitness]
  constructor
  · rintro ⟨e, ⟨hd, hs⟩, rfl⟩
    exact ⟨_, updateIndiv_mem_relUpdate hd, rfl, by simpa using hs⟩
  · rintro ⟨k, hk, rfl, hp⟩
    obtain ⟨⟨e, rfl⟩, hdom⟩ := mem_relUpdate.mp hk
    exact ⟨e, ⟨by simpa using hdom, by simpa using hp⟩, rfl⟩

-- [hofmann-2025] App. C (18a)
theorem drs_not (hφ : φ ≠ φ') (hP : P.Frame φ') :
    (P.not φ').drs φ = box {φ'} (eqCompl φ φ') ○ maxInput φ' (P.drs φ') := by
  ext ⟨i, j⟩
  rw [mem_box_comp_maxInput_drs hP]
  simp only [Clause.drs, Set.mem_ofPred_eq, Clause.mem_not, mem_eqCompl,
    State.updateProp_prop_of_ne _ hφ, State.updateProp_prop_self]

-- [hofmann-2025] App. C (18b), (18c)
theorem drs_connective (h₁ : φ ≠ φ') (h₂ : φ ≠ φ'') (h₃ : φ' ≠ φ'') (hP : P.Frame φ')
    (hP' : P.Frame φ'') (hQ : Q.Frame φ'') :
    (Clause.connective f P Q φ' φ'').drs φ =
      box {φ', φ''} {j | j.prop φ = f (j.prop φ') (j.prop φ'')} ○ maxInput φ' (P.drs φ') ○
        maxInput φ'' (Q.drs φ'') := by
  ext ⟨i, j⟩
  rw [comp_assoc, mem_box_pair_comp]
  simp only [Clause.drs, Set.mem_ofPred_eq, Clause.mem_connective]
  simp only [State.updateProp_prop_of_ne _ h₂, State.updateProp_prop_of_ne _ h₁,
    State.updateProp_prop_self, State.updateProp_prop_of_ne _ h₃]
  have hrun {t u : Set W} {m : State W E} :
      (i.updateProp φ' t).updateProp φ'' u ~[maxInput φ' (P.drs φ')] m ↔
        ∃ k, (t, k) ∈ P.maximal i ∧ m = (k.updateProp φ' t).updateProp φ'' u := by
    rw [State.updateProp_comm _ h₃, mem_updateProp_maxInput_drs hP]
    simp only [hP'.maximal i u t]
    exact ⟨fun ⟨_, ⟨k, hk, rfl⟩, hm⟩ ↦ ⟨k, hk, hm.trans (State.updateProp_comm _ h₃.symm _ _)⟩,
      fun ⟨k, hk, hm⟩ ↦ ⟨_, ⟨k, hk, rfl⟩, hm.trans (State.updateProp_comm _ h₃ _ _)⟩⟩
  constructor
  · rintro ⟨t, k, hk, u, l, hl, hs, rfl⟩
    exact ⟨t, u, hs, _, hrun.mpr ⟨k, hk, rfl⟩,
      (mem_updateProp_maxInput_drs hQ).mpr ⟨l, hl, rfl⟩⟩
  · rintro ⟨t, u, hs, m, hm, hj⟩
    obtain ⟨k, hk, rfl⟩ := hrun.mp hm
    obtain ⟨l, hl, rfl⟩ := (mem_updateProp_maxInput_drs hQ).mp hj
    exact ⟨t, k, hk, u, l, hl, hs, rfl⟩

/-- The relation `believe_φ(υ, φ')` of fn. 14: at each world of `φ`, the doxastic state of the
referent of `υ` entails `φ'`. -/
def believe (dox : E → W → Set W) (φ : PVar) (v : IVar) (φ' : PVar) : Condition (State W E) :=
  {i | i.prop φ ⊆ sat (fun a w ↦ dox a w ⊆ i.prop φ') (i.indiv v)}

-- [hofmann-2025] App. C (18e)
theorem drs_believed (hφ : φ ≠ φ') (hP : P.Frame φ') :
    (Clause.believed dox P φ' v).drs φ =
      box {φ'} (believe dox φ v φ') ○ maxInput φ' (P.drs φ') := by
  ext ⟨i, j⟩
  rw [mem_box_comp_maxInput_drs hP]
  simp only [Clause.drs, Set.mem_ofPred_eq, Clause.mem_believed, believe,
    State.updateProp_prop_of_ne _ hφ, State.updateProp_prop_self, State.updateProp_indiv]

-- [hofmann-2025] App. C (19)
theorem dec_eq (hr : r ≠ φ) (hP : P.Frame φ) :
    P.dec r φ = box {φ} (incl r φ) ○ maxInput φ (P.drs φ) := by
  ext ⟨i, j⟩
  rw [mem_box_comp_maxInput_drs hP, Clause.mem_dec]
  simp only [mem_incl, State.updateProp_prop_of_ne _ hr, State.updateProp_prop_self]

-- [hofmann-2025] (41): the fragment's update differs from the printed one only in the maximization
theorem dec_not_existential_eq (hr : r ≠ φ) (hφ : φ ≠ φ') :
    ((existential R v).not φ').dec r φ = box {φ} (incl r φ) ○ maxInput φ (box {φ'} (eqCompl φ φ') ○
      maxInput φ' (relUpdate φ' v ○ test (predication R φ' v))) := by
  rw [dec_eq hr (frame_existential.not hφ), drs_not hφ frame_existential, drs_existential]

end DRS

-- an assertion leaves alone a register that its clause leaves alone
theorem Clause.fixes_dec (hr : r' ≠ φ) (hP : ∀ i, ∀ p ∈ P i, p.2.prop r' = i.prop r') :
    Fixes r' (P.dec r φ) := by
  rintro i _ ⟨s, k, hk, -, rfl⟩
  simpa [State.updateProp_prop_of_ne _ hr] using hP i _ hk.1

end ICDRT
