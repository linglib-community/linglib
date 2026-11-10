module

public import Linglib.Core.Data.Set.Monad
public import Linglib.Logic.Assignment
public import Linglib.Semantics.Dynamic.Update
public import Mathlib.Data.PFun
public import Mathlib.Order.Minimal

/-!
# Intensional CDRT

Muskens's compositional DRT with intensional discourse referents, in Hofmann's formulation of the
flat update of Stone and Brasoveanu. An individual dref is an individual concept, a partial function
from worlds to individuals that has a referent only at the worlds of its local context. A clause is
a computation in `StateT ((ℕ → (W →. E))) Set` that returns its local context: from an input
assignment, the pairs of a context in which it holds and an output assignment. Maximization keeps
the runs whose context is maximal, so the truth conditions of the operators compose
(`Clause.HasTruthSet`). Flat update is the theorem that [negation keeps the drefs of its
prejacent](##ICDRT.Clause.Introduces.not), which gives [one law for any antecedent followed by any
update](##ICDRT.Clause.Introduces.mem_comp).

## Implementation notes

The universal falsifier ⋆ is undefinedness of the partial function. Hofmann's fragment stores each
context in a propositional dref, read only in the scope of the operator introducing it; here the
scope returns it to that operator as a value, so the state holds just the individual drefs and an
assertion takes its commitment set as an argument. `IsWitness` has Hofmann's biconditional relative
update; Stone's has only the implication from the context to a referent. `W` and `E` share a
universe in `Clause`, as `StateT` requires.

## References

* [muskens-1996]
* [stone-1999]
* [brasoveanu-2007]
* [hofmann-2025]
-/

@[expose] public section

attribute [local instance] Set.monad

universe u

namespace ICDRT

open DynamicSemantics SetRel

/-- `g[v ↦ e]` is the assignment sending `v` to `e` and agreeing with `g` elsewhere. -/
scoped notation:max g "[" v " ↦ " e "]" => Function.update g v e

/-! ### Individual concepts and witnesses -/

section Witnesses

variable {W E : Type*} {R S : E → W → Prop} {s : Set W} {e : W →. E}

/-- The worlds where the referent of an individual concept satisfies `R`. ⋆ satisfies no relation
([hofmann-2025] fn. 9), so predication entails that the referent exists ((28), (29)):
`sat_subset_dom`. -/
def sat (R : E → W → Prop) (e : W →. E) : Set W := {w | ∃ a ∈ e w, R a w}

theorem sat_subset_dom (R : E → W → Prop) (e : W →. E) : sat R e ⊆ e.Dom :=
  fun _ ⟨_, ha, _⟩ ↦ Part.dom_iff_mem.2 ⟨_, ha⟩

@[simp] theorem sat_lift_const (R : E → W → Prop) (a : E) :
    sat R (PFun.lift fun _ : W ↦ a) = {w | R a w} := by
  ext w
  simp [sat, PFun.lift]

/-- The worlds where some individual satisfies `R`. -/
def witnessed (R : E → W → Prop) : Set W := {w | ∃ a, R a w}

/-- `e` is a possible value of the dref of an indefinite with restrictor `R` in the local context
`s`: it refers at exactly the `s`-worlds (25), and to an `R` (27). -/
def IsWitness (R : E → W → Prop) (s : Set W) (e : W →. E) : Prop :=
  s = e.Dom ∧ s ⊆ sat R e

theorem witnessed_inf_subset_left : witnessed (R ⊓ S) ⊆ witnessed R :=
  fun _ ⟨a, hR, _⟩ ↦ ⟨a, hR⟩

theorem IsWitness.subset_witnessed (h : IsWitness R s e) : s ⊆ witnessed R :=
  fun _ hw ↦ let ⟨a, _, hR⟩ := h.2 hw; ⟨a, hR⟩

theorem IsWitness.rel {w : W} {a : E} (h : IsWitness R s e) (ha : a ∈ e w) : R a w :=
  let ⟨_, hb, hR⟩ := h.2 (h.1 ▸ Part.dom_iff_mem.2 ⟨a, ha⟩)
  Part.mem_unique ha hb ▸ hR

theorem IsWitness.sat_subset (h : IsWitness R s e) :
    sat S e ⊆ s ∩ witnessed (R ⊓ S) :=
  fun _ ⟨a, ha, hS⟩ ↦ ⟨h.1 ▸ sat_subset_dom S e ⟨a, ha, hS⟩, a, h.rel ha, hS⟩

/-- A witness can choose an `S` wherever some `R` is one. -/
theorem exists_isWitness_sat_eq (R S : E → W → Prop) :
    ∃ e, IsWitness R (witnessed R) e ∧ sat S e = witnessed (R ⊓ S) := by
  have h (w : W) (hw : w ∈ witnessed R) : ∃ a, R a w ∧ (w ∈ witnessed (R ⊓ S) → S a w) := by
    by_cases hc : w ∈ witnessed (R ⊓ S)
    · exact hc.imp fun a ha ↦ ⟨ha.1, fun _ ↦ ha.2⟩
    · exact hw.imp fun a ha ↦ ⟨ha, hc.elim⟩
  choose f hR hS using h
  have hW : IsWitness R (witnessed R) fun w ↦ ⟨w ∈ witnessed R, f w⟩ :=
    ⟨rfl, fun w hw ↦ ⟨_, ⟨hw, rfl⟩, hR w hw⟩⟩
  exact ⟨_, hW, (hW.sat_subset.trans Set.inter_subset_right).antisymm fun w hc ↦
    ⟨_, ⟨witnessed_inf_subset_left hc, rfl⟩, hS w _ hc⟩⟩

theorem exists_isWitness_subset_sat_iff :
    (∃ e, IsWitness R (witnessed R) e ∧ s ⊆ sat S e) ↔ s ⊆ witnessed (R ⊓ S) := by
  refine ⟨fun ⟨e, he, hs⟩ ↦ hs.trans (he.sat_subset.trans Set.inter_subset_right), fun hs ↦ ?_⟩
  obtain ⟨e, he, h⟩ := exists_isWitness_sat_eq R S
  exact ⟨e, he, h ▸ hs⟩

end Witnesses

variable {W E : Type u} {g h : ℕ → (W →. E)} {s dc dc' A : Set W} {R S : E → W → Prop}
  {v v' : ℕ} {a : E} {dox : E → W → Set W}

/-! ### Clauses -/

/-- A clause, of type `wt`, computes its local context: from an input assignment, the pairs of a
context in which it holds and an output assignment. -/
abbrev Clause (W E : Type u) := StateT ((ℕ → (W →. E))) Set (Set W)

/-- Any context that entails `c`, with no change of assignment. -/
def within (c : Set W) : Clause W E := fun g ↦ {p | p.1 ⊆ c ∧ p.2 = g}

/-- A common noun or intransitive verb holds in a context where its argument satisfies it
([hofmann-2025] App. C (15)). -/
def commonNoun (R : E → W → Prop) (v : ℕ) : Clause W E := fun g ↦ within (sat R (g v)) g

/-- The indefinite introduces its dref with a referent at exactly the worlds of the context, in
which its restrictor and its scope hold ([hofmann-2025] App. C (16)). -/
def indefinite (v : ℕ) (P P' : ℕ → Clause W E) : Clause W E :=
  fun g ↦ {p | ∃ e k, p.1 = e.Dom ∧ (p.1, k) ∈ P v g[v ↦ e] ∧ p ∈ P' v k}

/-- A proper name introduces a dref equal to its constant ([hofmann-2025] App. C (14)). -/
def properName (a : E) (v : ℕ) (P : ℕ → Clause W E) : Clause W E :=
  fun g ↦ P v g[v ↦ PFun.lift fun _ ↦ a]

/-- *There is an `R`* ([hofmann-2025] (24)) is the indefinite with a vacuous scope (fn. 8). -/
def existential (R : E → W → Prop) (v : ℕ) : Clause W E :=
  indefinite v (commonNoun R) fun _ ↦ within Set.univ

/-- *It is `S`* ([hofmann-2025] (30)) is the predicate at the pronoun's index (App. C (17)). -/
def it (S : E → W → Prop) (v : ℕ) : Clause W E := commonNoun S v

namespace Clause

/-- Maximization keeps the runs whose context is maximal among the contexts of the clause. -/
def maximal (P : Clause W E) : Clause W E :=
  fun g ↦ {p ∈ P g | Maximal (· ∈ SetRel.dom (P g)) p.1}

/-- Negation returns the complement of the prejacent's context ([hofmann-2025] App. C (18a)). -/
def not (P : Clause W E) : Clause W E := (compl <$> P.maximal : StateT _ Set _)

/-- A binary connective relates its context to those of its operands by the static function `f`
([hofmann-2025] App. C (18b), (18c)). -/
def connective (f : Set W → Set W → Set W) (P Q : Clause W E) : Clause W E :=
  (f <$> P.maximal <*> Q.maximal : StateT _ Set _)

/-- Disjunction's context is the union of the contexts of its disjuncts (App. C (18b)). -/
abbrev or (P Q : Clause W E) : Clause W E := connective (· ∪ ·) P Q

/-- The conditional's context is the union of the antecedent's complement and the consequent's
context (App. C (18c)). -/
abbrev ifThen (P Q : Clause W E) : Clause W E := connective (fun s t ↦ sᶜ ∪ t) P Q

/-- An attitude verb holds where the subject's doxastic state entails its complement's context
([hofmann-2025] App. C (18e), fn. 14). -/
def believed (dox : E → W → Set W) (P : Clause W E) (v : ℕ) : Clause W E :=
  fun g ↦ {p | ∃ t, (t, p.2) ∈ P.maximal g ∧ p.1 ⊆ sat (fun a w ↦ dox a w ⊆ t) (g v)}

/-- A veridical attitude's context, moreover, entails its complement's ([hofmann-2025] §2.4). -/
def knows (dox : E → W → Set W) (P : Clause W E) (v : ℕ) : Clause W E :=
  fun g ↦ {p | ∃ t, (t, p.2) ∈ P.maximal g ∧ p.1 ⊆ t ∩ sat (fun a w ↦ dox a w ⊆ t) (g v)}

/-- The declarative takes the maximal context of the clause, which the speaker's commitments `dc`
entail ([hofmann-2025] (20a), App. C (19)). -/
def dec (P : Clause W E) (dc : Set W) : Update ((ℕ → (W →. E))) :=
  {p | ∃ s, (s, p.2) ∈ P.maximal p.1 ∧ dc ⊆ s}

/-- A clause has truth set `T` if `T` is its greatest context. -/
def HasTruthSet (P : Clause W E) (T : (ℕ → (W →. E)) → Set W) : Prop :=
  ∀ g, IsGreatest (SetRel.dom (P g)) (T g)

/-- Flat update: at its truth set `A`, the clause has assigned `v` a witness of `R`, however deeply
the indefinite is embedded. -/
structure Introduces (P : Clause W E) (R : E → W → Prop) (v : ℕ) (A : Set W) : Prop where
  /-- The clause's greatest context is `A`. -/
  hasTruthSet : P.HasTruthSet fun _ ↦ A
  /-- The runs at `A` are the witnesses for `v`. -/
  mem_iff {g h : ℕ → (W →. E)} :
    (A, h) ∈ P g ↔ ∃ e, IsWitness R (witnessed R) e ∧ h = g[v ↦ e]

end Clause

/-! ### Runs of the operators -/

variable {P Q : Clause W E} {T : (ℕ → (W →. E)) → Set W} {f : Set W → Set W → Set W}

theorem mem_it : (s, h) ∈ it S v g ↔ s ⊆ sat S (g v) ∧ h = g := Iff.rfl

theorem mem_existential :
    (s, h) ∈ existential R v g ↔ ∃ e, IsWitness R s e ∧ h = g[v ↦ e] := by
  simp [existential, indefinite, commonNoun, within, IsWitness]
  grind

theorem Clause.mem_dec : g ~[P.dec dc] h ↔ ∃ s, (s, h) ∈ P.maximal g ∧ dc ⊆ s := Iff.rfl

/-! ### Truth sets -/

theorem Clause.HasTruthSet.mem_maximal (hP : P.HasTruthSet T) :
    (s, h) ∈ P.maximal g ↔ s = T g ∧ (T g, h) ∈ P g := by
  simp only [Clause.maximal, Set.mem_ofPred_eq, (hP g).maximal_iff]
  grind

theorem Clause.HasTruthSet.mem_dec (hP : P.HasTruthSet T) :
    g ~[P.dec dc] h ↔ dc ⊆ T g ∧ (T g, h) ∈ P g := by
  simp [Clause.mem_dec, hP.mem_maximal, and_comm]

theorem Clause.HasTruthSet.mem_dom_dec (hP : P.HasTruthSet T) :
    g ∈ (P.dec dc).dom ↔ dc ⊆ T g := by
  simpa [SetRel.mem_dom, hP.mem_dec] using fun _ ↦ (hP g).1

theorem Clause.HasTruthSet.mem_not (hP : P.HasTruthSet T) :
    (s, h) ∈ P.not g ↔ s = (T g)ᶜ ∧ (T g, h) ∈ P g := by
  simp [Clause.not, hP.mem_maximal, and_comm]

theorem Clause.HasTruthSet.not (hP : P.HasTruthSet T) : P.not.HasTruthSet fun g ↦ (T g)ᶜ := fun g ↦
  let ⟨k, hk⟩ := (hP g).1
  ⟨⟨k, hP.mem_not.2 ⟨rfl, hk⟩⟩, fun _ ⟨_, hk⟩ ↦ (hP.mem_not.1 hk).1.le⟩

theorem hasTruthSet_it : (it S v).HasTruthSet fun g ↦ sat S (g v) := fun g ↦
  ⟨⟨g, subset_rfl, rfl⟩, fun _ ⟨_, h, _⟩ ↦ h⟩

theorem mem_maximal_it : (s, h) ∈ (it S v).maximal g ↔ s = sat S (g v) ∧ h = g := by
  simp [hasTruthSet_it.mem_maximal, mem_it]

theorem mem_dec_it : g ~[(it S v).dec dc] h ↔ dc ⊆ sat S (g v) ∧ h = g := by
  simp [hasTruthSet_it.mem_dec, mem_it]

theorem hasTruthSet_existential : (existential R v).HasTruthSet fun _ ↦ witnessed R := fun _ ↦
  let ⟨e, he, _⟩ := exists_isWitness_sat_eq R ⊤
  ⟨⟨_, mem_existential.2 ⟨e, he, rfl⟩⟩, fun _ ⟨_, hh⟩ ↦
    let ⟨_, he, _⟩ := mem_existential.1 hh; he.subset_witnessed⟩

/-! ### Flat update -/

theorem introduces_existential : (existential R v).Introduces R v (witnessed R) :=
  ⟨hasTruthSet_existential, mem_existential⟩

/-- Flat update: negation keeps the drefs of its prejacent and complements its context. -/
theorem Clause.Introduces.not (hP : P.Introduces R v A) : P.not.Introduces R v Aᶜ :=
  ⟨hP.1.not, hP.1.mem_not.trans (and_iff_right rfl) |>.trans hP.2⟩

theorem Clause.Introduces.not_not (hP : P.Introduces R v A) : P.not.not.Introduces R v A := by
  simpa using hP.not.not

theorem Clause.Introduces.mem_dec (hP : P.Introduces R v A) :
    g ~[P.dec dc] h ↔ dc ⊆ A ∧ ∃ e, IsWitness R (witnessed R) e ∧ h = g[v ↦ e] :=
  hP.1.mem_dec.trans (and_congr_right' hP.2)

/-- The one law of flat update: an antecedent, under any number of negations, followed by any update
runs that update from a witness for the antecedent's dref. -/
theorem Clause.Introduces.mem_comp {D : Update ((ℕ → (W →. E)))} (hP : P.Introduces R v A) :
    g ~[P.dec dc ○ D] h ↔ dc ⊆ A ∧ ∃ e, IsWitness R (witnessed R) e ∧ g[v ↦ e] ~[D] h := by
  simp only [SetRel.mem_comp, hP.mem_dec]
  grind

/-- Any antecedent, under any number of negations, followed by any clause with a truth set: the
speakers commit to their contexts, the second at a witness for the antecedent's dref. -/
theorem Clause.Introduces.mem_dom_comp (hP : P.Introduces R v A) (hQ : Q.HasTruthSet T) :
    g ∈ (P.dec dc ○ Q.dec dc').dom ↔
      dc ⊆ A ∧ ∃ e, IsWitness R (witnessed R) e ∧ dc' ⊆ T g[v ↦ e] := by
  simp only [SetRel.mem_dom, hP.mem_comp, ← hQ.mem_dom_dec, exists_and_left]
  rw [exists_comm]
  simp only [exists_and_left]

theorem Clause.Introduces.mem_dom_comp_it (hP : P.Introduces R v A) :
    g ∈ (P.dec dc ○ (it S v).dec dc').dom ↔ dc ⊆ A ∧ dc' ⊆ witnessed (R ⊓ S) := by
  simp [hP.mem_dom_comp hasTruthSet_it, exists_isWitness_subset_sat_iff]

/-! ### Connectives over a pronoun -/

theorem Clause.Introduces.mem_connective_it (hP : P.Introduces R v A) :
    (s, h) ∈ Clause.connective f P (it S v) g ↔
      ∃ e, IsWitness R (witnessed R) e ∧ s = f A (sat S e) ∧ h = g[v ↦ e] := by
  simp only [Clause.connective, Set.mk_mem_stateT_map_seq, hP.1.mem_maximal, hP.2, mem_maximal_it]
  constructor
  · rintro ⟨_, _, ⟨rfl, e, he, rfl⟩, _, ⟨rfl, rfl⟩, rfl⟩
    exact ⟨e, he, by simp, rfl⟩
  · rintro ⟨e, he, rfl, rfl⟩
    exact ⟨_, _, ⟨rfl, e, he, rfl⟩, _, ⟨by simp, rfl⟩, rfl⟩

theorem Clause.Introduces.hasTruthSet_connective_it (hP : P.Introduces R v A)
    (hf : Monotone (f A)) :
    (Clause.connective f P (it S v)).HasTruthSet fun _ ↦ f A (witnessed (R ⊓ S)) := fun g ↦ by
  refine ⟨?_, fun s ⟨j, hj⟩ ↦ ?_⟩
  · obtain ⟨e, he, h⟩ := exists_isWitness_sat_eq R S
    exact ⟨_, hP.mem_connective_it.mpr ⟨e, he, by rw [h], rfl⟩⟩
  · obtain ⟨e, he, rfl, -⟩ := hP.mem_connective_it.mp hj
    exact hf (he.sat_subset.trans Set.inter_subset_right)

theorem Clause.Introduces.hasTruthSet_or_it (hP : P.Introduces R v A) :
    (P.or (it S v)).HasTruthSet fun _ ↦ A ∪ witnessed (R ⊓ S) :=
  hP.hasTruthSet_connective_it fun _ _ h ↦ Set.union_subset_union_right _ h

/-! ### Attitudes -/

/-- *`a` believes it is `S`* ([hofmann-2025] (52)): a proper name, and the attitude over a pronoun.
-/
abbrev believes (a : E) (dox : E → W → Set W) (S : E → W → Prop) (v v' : ℕ) : Clause W E :=
  properName a v' (Clause.believed dox (it S v))

theorem mem_believes (hv : v ≠ v') : (s, h) ∈ believes a dox S v v' g ↔
    s ⊆ {w | dox a w ⊆ sat S (g v)} ∧ h = g[v' ↦ PFun.lift fun _ ↦ a] := by
  simp [properName, Clause.believed, mem_maximal_it, Function.update_of_ne hv, and_comm]

theorem hasTruthSet_believes (hv : v ≠ v') :
    (believes a dox S v v').HasTruthSet fun g ↦ {w | dox a w ⊆ sat S (g v)} := fun _ ↦
  ⟨⟨_, (mem_believes hv).mpr ⟨subset_rfl, rfl⟩⟩, fun _ ⟨_, h⟩ ↦ ((mem_believes hv).mp h).1⟩

theorem mem_dec_believes (hv : v ≠ v') : g ~[(believes a dox S v v').dec dc] h ↔
    dc ⊆ {w | dox a w ⊆ sat S (g v)} ∧ h = g[v' ↦ PFun.lift fun _ ↦ a] := by
  simp [(hasTruthSet_believes hv).mem_dec, mem_believes hv]

end ICDRT
