module

public import Linglib.Syntax.HPSG.RSRL.Interpretation
public import Linglib.Syntax.HPSG.RSRL.Syntax
public import Mathlib.Logic.Function.Basic

/-!
# RSRL semantics

This file defines what a term denotes in an interpretation and what it means for an entity to
satisfy a formula. The quantifiers of a formula range over the components of the entity being
described, not over the whole universe.

An interpretation is a *model* of a grammar when every entity satisfies every description in
it. An entity satisfies a formula exactly when its image under an embedding does
(`HPSG.RSRL.Interpretation.Embedding.satisfies`), so an interpretation that embeds into a model
is a model.

## Implementation notes

`SatisfiesOn` takes the range of the quantifiers as an argument, which `Satisfies` sets to the
components. `models_iff` reduces satisfaction under every assignment to one assignment, which
makes `Models` decidable for a grammar given by a list on a finite universe.

## References

* [richter-2000]
* [richter-2024]
-/

@[expose] public section

namespace HPSG.RSRL

universe u v

variable {Srt : Type u} [PartialOrder Srt] {Sig : Signature Srt} {U : Type v}

namespace Interpretation

variable (I : Interpretation Sig U)

/-! ### Term denotation -/

/-- The entity that a term denotes at the described entity `u` under the assignment `g`, when
every attribute along the term is defined ([richter-2024], Definition 10). -/
def termDenot (g : ℕ → U) : Term Sig → U → Option U
  | .colon, u => some u
  | .var n, _ => some (g n)
  | .feat t α, u => (termDenot g t u).bind (I.A α)

variable {I} {g g' : ℕ → U} {u v : U}

@[simp] theorem termDenot_colon : I.termDenot g .colon u = some u := rfl

@[simp] theorem termDenot_var (n : ℕ) : I.termDenot g (.var n) u = some (g n) := rfl

@[simp] theorem termDenot_feat (t : Term Sig) (α : Sig.Attr) :
    I.termDenot g (t.feat α) u = (I.termDenot g t u).bind (I.A α) := rfl

/-- A term denotation depends only on the values of the variables that occur in the term. -/
theorem termDenot_congr {t : Term Sig} (h : ∀ x ∈ t.freeVars, g x = g' x) :
    I.termDenot g t u = I.termDenot g' t u := by
  induction t with
  | colon => rfl
  | var n => simp [h n (Finset.mem_singleton_self n)]
  | feat t α ih => rw [termDenot_feat, termDenot_feat, ih h]

theorem termDenot_of_isColonFree {t : Term Sig} (ht : t.IsColonFree) (u v : U) :
    I.termDenot g t u = I.termDenot g t v := by
  induction t with
  | colon => exact ht.elim
  | var n => rfl
  | feat t α ih => rw [termDenot_feat, termDenot_feat, ih ht]

theorem termDenot_path (g g' : ℕ → U) (p : Path Sig) :
    I.termDenot g (.path p) u = I.termDenot g' (.path p) u :=
  termDenot_congr (by simp)

theorem termDenot_path_cons (α : Sig.Attr) (p : Path Sig) :
    I.termDenot g (.path (α :: p)) u = (I.A α u).bind (I.termDenot g (.path p)) := by
  induction p using List.reverseRecOn with
  | nil => simp [Term.path]
  | append_singleton p β ih =>
    rw [← List.cons_append, Term.path_concat, Term.path_concat, termDenot_feat, ih,
      Option.bind_assoc]
    rfl

theorem termDenot_path_append (p q : Path Sig) :
    I.termDenot g (.path (p ++ q)) u =
      (I.termDenot g (.path p) u).bind (I.termDenot g (.path q)) := by
  induction p generalizing u with
  | nil => rfl
  | cons α p ih =>
    rw [List.cons_append, termDenot_path_cons, termDenot_path_cons, Option.bind_assoc]
    simp only [ih]

/-- Following a path from an entity is reading it in the machine of the interpretation. -/
theorem evalFrom_toPartialMoore (g : ℕ → U) (u : U) (p : Path Sig) :
    I.toPartialMoore.evalFrom u p = I.termDenot g (.path p) u := by
  induction p using List.reverseRecOn with
  | nil => rfl
  | append_singleton p α ih =>
    rw [PartialMoore.evalFrom_append_singleton, ih, Term.path_concat, termDenot_feat]
    rfl

/-- The term of a path denotes the entity that the path leads to. -/
theorem termDenot_path_eq_eval (g : ℕ → U) (u : U) (p : Path Sig) :
    I.termDenot g (.path p) u = I.eval u p :=
  (evalFrom_toPartialMoore g u p).symm

/-- The components of `u` are the entities that some path denotes at `u`
([richter-2024], Definition 11). -/
theorem isComponentOf_iff_exists_path (g : ℕ → U) :
    I.IsComponentOf u v ↔ ∃ p : Path Sig, I.termDenot g (.path p) u = some v := by
  simp only [← reaches_toPartialMoore_iff, PartialMoore.Reaches, evalFrom_toPartialMoore g]

/-- A homomorphism commutes with term denotation. -/
theorem HomClass.termDenot_comp {V : Type*} {J : Interpretation Sig V} {F : Type*}
    [FunLike F U V] [HomClass F I J] (f : F) (g : ℕ → U) (t : Term Sig) (u : U) :
    J.termDenot (f ∘ g) t (f u) = (I.termDenot g t u).map f := by
  induction t with
  | colon => rfl
  | var n => rfl
  | feat t α ih =>
    rw [termDenot_feat, termDenot_feat, ih]
    cases I.termDenot g t u <;> simp

end Interpretation

namespace Interpretation

variable (I : Interpretation Sig U)

/-! ### Satisfaction -/

/-- The entity `u` satisfies a formula under the assignment `g` with the quantifiers ranging over
`D`, an atomic formula with an undefined term being false. -/
def SatisfiesOn (D : Set U) (g : ℕ → U) (u : U) : Formula Sig → Prop
  | .sortAssign t σ => ∃ v ∈ I.termDenot g t u, I.S v ≤ σ
  | .pathEq t₁ t₂ => ∃ v ∈ I.termDenot g t₁ u, v ∈ I.termDenot g t₂ u
  | .rel ρ xs => (fun i ↦ g (xs i)) ∈ I.R ρ
  | .neg d => ¬ SatisfiesOn D g u d
  | .imp d e => SatisfiesOn D g u d → SatisfiesOn D g u e
  | .all x d => ∀ w ∈ D, SatisfiesOn D (Function.update g x w) u d

/-- The entity `u` satisfies a formula under the assignment `g` when the quantifiers range over
the components of `u` ([richter-2024], Definition 14). -/
def Satisfies (g : ℕ → U) (u : U) (d : Formula Sig) : Prop :=
  I.SatisfiesOn {w | I.IsComponentOf u w} g u d

instance decidableSatisfiesOn [Fintype U] [DecidableEq U] [DecidableLE Srt] (D : Set U)
    [DecidablePred (· ∈ D)] [∀ ρ, DecidablePred (· ∈ I.R ρ)] (g : ℕ → U) (u : U) :
    (d : Formula Sig) → Decidable (I.SatisfiesOn D g u d)
  | .sortAssign _ σ => Option.decidableExistsMem (p := (I.S · ≤ σ)) _
  | .pathEq _ t₂ => Option.decidableExistsMem (p := (· ∈ I.termDenot g t₂ u)) _
  | .rel .. => by unfold SatisfiesOn; infer_instance
  | .neg d => by
    have := decidableSatisfiesOn D g u d
    unfold SatisfiesOn; infer_instance
  | .imp d e => by
    have := decidableSatisfiesOn D g u d
    have := decidableSatisfiesOn D g u e
    unfold SatisfiesOn; infer_instance
  | .all x d => by
    have (w : U) := decidableSatisfiesOn D (Function.update g x w) u d
    unfold SatisfiesOn; infer_instance

instance decidableSatisfies [Fintype U] [DecidableEq U] [DecidableLE Srt] [Fintype Sig.Attr]
    [∀ ρ, DecidablePred (· ∈ I.R ρ)] (g : ℕ → U) (u : U) (d : Formula Sig) :
    Decidable (I.Satisfies g u d) :=
  inferInstanceAs (Decidable (I.SatisfiesOn _ g u d))

variable {I} {D : Set U} {g g' : ℕ → U} {u u' : U} {d e : Formula Sig}

@[simp] theorem satisfiesOn_sortAssign {t : Term Sig} {σ : Srt} :
    I.SatisfiesOn D g u (.sortAssign t σ) ↔ ∃ v ∈ I.termDenot g t u, I.S v ≤ σ := Iff.rfl

@[simp] theorem satisfiesOn_pathEq {t₁ t₂ : Term Sig} :
    I.SatisfiesOn D g u (.pathEq t₁ t₂) ↔ ∃ v ∈ I.termDenot g t₁ u, v ∈ I.termDenot g t₂ u :=
  Iff.rfl

@[simp] theorem satisfiesOn_rel {ρ : Sig.Rel} {xs : Fin (Sig.arity ρ) → ℕ} :
    I.SatisfiesOn D g u (.rel ρ xs) ↔ (fun i ↦ g (xs i)) ∈ I.R ρ := Iff.rfl

@[simp] theorem satisfiesOn_neg : I.SatisfiesOn D g u d.neg ↔ ¬ I.SatisfiesOn D g u d := Iff.rfl

@[simp] theorem satisfiesOn_imp :
    I.SatisfiesOn D g u (d.imp e) ↔ (I.SatisfiesOn D g u d → I.SatisfiesOn D g u e) := Iff.rfl

@[simp] theorem satisfiesOn_and :
    I.SatisfiesOn D g u (d.and e) ↔ I.SatisfiesOn D g u d ∧ I.SatisfiesOn D g u e :=
  Classical.not_imp.trans (and_congr_right fun _ ↦ not_not)

@[simp] theorem satisfiesOn_or :
    I.SatisfiesOn D g u (d.or e) ↔ I.SatisfiesOn D g u d ∨ I.SatisfiesOn D g u e :=
  or_iff_not_imp_left.symm

@[simp] theorem satisfiesOn_iff :
    I.SatisfiesOn D g u (d.iff e) ↔ (I.SatisfiesOn D g u d ↔ I.SatisfiesOn D g u e) :=
  satisfiesOn_and.trans iff_def.symm

@[simp] theorem satisfiesOn_all {x : ℕ} :
    I.SatisfiesOn D g u (.all x d) ↔ ∀ w ∈ D, I.SatisfiesOn D (Function.update g x w) u d :=
  Iff.rfl

@[simp] theorem satisfiesOn_ex {x : ℕ} :
    I.SatisfiesOn D g u (.ex x d) ↔ ∃ w ∈ D, I.SatisfiesOn D (Function.update g x w) u d := by
  simp only [Formula.ex, satisfiesOn_neg, satisfiesOn_all, not_forall, not_not, exists_prop]

@[simp] theorem satisfiesOn_top : I.SatisfiesOn D g u .top := fun _ _ ↦ ⟨_, rfl, rfl⟩

@[simp] theorem satisfiesOn_bot : ¬ I.SatisfiesOn D g u .bot := not_not_intro satisfiesOn_top

@[simp] theorem satisfiesOn_conj {ds : List (Formula Sig)} :
    I.SatisfiesOn D g u (.conj ds) ↔ ∀ d ∈ ds, I.SatisfiesOn D g u d := by
  induction ds <;> simp_all [Formula.conj]

@[simp] theorem satisfiesOn_disj {ds : List (Formula Sig)} :
    I.SatisfiesOn D g u (.disj ds) ↔ ∃ d ∈ ds, I.SatisfiesOn D g u d := by
  induction ds <;> simp_all [Formula.disj]

@[simp] theorem satisfies_sortAssign {t : Term Sig} {σ : Srt} :
    I.Satisfies g u (.sortAssign t σ) ↔ ∃ v ∈ I.termDenot g t u, I.S v ≤ σ := Iff.rfl

@[simp] theorem satisfies_pathEq {t₁ t₂ : Term Sig} :
    I.Satisfies g u (.pathEq t₁ t₂) ↔ ∃ v ∈ I.termDenot g t₁ u, v ∈ I.termDenot g t₂ u :=
  Iff.rfl

@[simp] theorem satisfies_rel {ρ : Sig.Rel} {xs : Fin (Sig.arity ρ) → ℕ} :
    I.Satisfies g u (.rel ρ xs) ↔ (fun i ↦ g (xs i)) ∈ I.R ρ := Iff.rfl

@[simp] theorem satisfies_neg : I.Satisfies g u d.neg ↔ ¬ I.Satisfies g u d := Iff.rfl

@[simp] theorem satisfies_and :
    I.Satisfies g u (d.and e) ↔ I.Satisfies g u d ∧ I.Satisfies g u e := satisfiesOn_and

@[simp] theorem satisfies_or :
    I.Satisfies g u (d.or e) ↔ I.Satisfies g u d ∨ I.Satisfies g u e := satisfiesOn_or

@[simp] theorem satisfies_imp :
    I.Satisfies g u (d.imp e) ↔ I.Satisfies g u d → I.Satisfies g u e := Iff.rfl

@[simp] theorem satisfies_iff :
    I.Satisfies g u (d.iff e) ↔ (I.Satisfies g u d ↔ I.Satisfies g u e) := satisfiesOn_iff

@[simp] theorem satisfies_conj {ds : List (Formula Sig)} :
    I.Satisfies g u (.conj ds) ↔ ∀ d ∈ ds, I.Satisfies g u d := satisfiesOn_conj

@[simp] theorem satisfies_ex {x : ℕ} : I.Satisfies g u (.ex x d) ↔
    ∃ w, I.IsComponentOf u w ∧ I.Satisfies (Function.update g x w) u d := satisfiesOn_ex

@[simp] theorem satisfies_all {x : ℕ} : I.Satisfies g u (.all x d) ↔
    ∀ w, I.IsComponentOf u w → I.Satisfies (Function.update g x w) u d := Iff.rfl

theorem satisfies_sortAssign_path {p : Path Sig} {σ : Srt} :
    I.Satisfies g u (.sortAssign (.path p) σ) ↔ I.SortAt u p σ := by
  rw [satisfies_sortAssign, termDenot_path_eq_eval, SortAt]

theorem satisfies_pathEq_path {p q : Path Sig} :
    I.Satisfies g u (.pathEq (.path p) (.path q)) ↔ I.PathEq u p q := by
  rw [satisfies_pathEq, termDenot_path_eq_eval, termDenot_path_eq_eval]
  exact ⟨fun ⟨v, hp, hq⟩ ↦ ⟨v, hp, hq⟩, fun ⟨v, hp, hq⟩ ↦ ⟨v, hp, hq⟩⟩

/-! ### Free variables -/

private theorem update_congr {x : ℕ} {s : Finset ℕ} (h : ∀ y ∈ s.erase x, g y = g' y) (w : U) :
    ∀ y ∈ s, Function.update g x w y = Function.update g' x w y := fun y hy ↦ by
  obtain rfl | hyx := eq_or_ne y x
  · simp
  · simpa [Function.update_of_ne hyx] using h y (Finset.mem_erase.2 ⟨hyx, hy⟩)

/-- Satisfaction depends only on the values of the free variables. -/
theorem satisfiesOn_congr : ∀ {g g' : ℕ → U},
    (∀ x ∈ d.freeVars, g x = g' x) → (I.SatisfiesOn D g u d ↔ I.SatisfiesOn D g' u d) := by
  induction d with
  | sortAssign t σ => intro g g' h; rw [satisfiesOn_sortAssign, termDenot_congr h]; rfl
  | pathEq t₁ t₂ =>
    intro g g' h
    rw [satisfiesOn_pathEq, termDenot_congr fun x hx ↦ h x (Finset.mem_union_left _ hx),
      termDenot_congr fun x hx ↦ h x (Finset.mem_union_right _ hx)]
    rfl
  | rel ρ xs =>
    intro g g' h
    have : (fun i ↦ g (xs i)) = fun i ↦ g' (xs i) :=
      funext fun i ↦ h _ (Finset.mem_image_of_mem xs (Finset.mem_univ i))
    rw [satisfiesOn_rel, this]; rfl
  | neg d ih => exact fun h ↦ not_congr (ih h)
  | imp d e ihd ihe =>
    exact fun h ↦ imp_congr (ihd fun x hx ↦ h x (Finset.mem_union_left _ hx))
      (ihe fun x hx ↦ h x (Finset.mem_union_right _ hx))
  | all x d ih =>
    exact fun h ↦ forall_congr' fun w ↦ imp_congr_right fun _ ↦ ih (update_congr h w)

theorem satisfies_congr (h : ∀ x ∈ d.freeVars, g x = g' x) :
    I.Satisfies g u d ↔ I.Satisfies g' u d :=
  satisfiesOn_congr h

theorem satisfies_iff_of_freeVars_eq_empty (hd : d.freeVars = ∅) (g g' : ℕ → U) :
    I.Satisfies g u d ↔ I.Satisfies g' u d :=
  satisfies_congr fun x hx ↦ by simp [hd] at hx

/-! ### Colon-free formulae -/

/-- A colon-free formula does not depend on the described entity. -/
theorem satisfiesOn_iff_of_isColonFree (hd : d.IsColonFree) :
    I.SatisfiesOn D g u d ↔ I.SatisfiesOn D g u' d := by
  induction d generalizing g with
  | sortAssign t σ => simp only [satisfiesOn_sortAssign, termDenot_of_isColonFree hd u u']
  | pathEq t₁ t₂ =>
    simp only [satisfiesOn_pathEq, termDenot_of_isColonFree hd.1 u u',
      termDenot_of_isColonFree hd.2 u u']
  | rel => exact Iff.rfl
  | neg d ih => exact not_congr (ih hd)
  | imp d e ihd ihe => exact imp_congr (ihd hd.1) (ihe hd.2)
  | all x d ih => exact forall_congr' fun w ↦ imp_congr_right fun _ ↦ ih hd

end Interpretation

namespace Interpretation

variable (I : Interpretation Sig U) {G H : Grammar Sig} {u : U} {d : Description Sig}

/-- The entities that a description describes, those that satisfy it under every assignment
([richter-2024], Definition 15). -/
def denotation (d : Description Sig) : Set U := {u | ∀ g, I.Satisfies g u d}

/-- The entities that every description of a theory describes ([richter-2024], Definition 17). -/
def theoryDenotation (θ : Set (Description Sig)) : Set U := {u | ∀ d ∈ θ, u ∈ I.denotation d}

/-- An interpretation is a model of a grammar when every principle describes every entity
([richter-2024], Definition 18). -/
def Models (G : Grammar Sig) : Prop := ∀ d ∈ G, ∀ (g : ℕ → U) (u : U), I.Satisfies g u d

variable {I}

/-- A description describes an entity exactly when the entity satisfies it under the assignment of
every variable to itself. -/
theorem mem_denotation_iff : u ∈ I.denotation d ↔ I.Satisfies (fun _ ↦ u) u d :=
  ⟨fun h ↦ h _, fun h g ↦ (satisfies_iff_of_freeVars_eq_empty d.freeVars_toFormula _ g).1 h⟩

@[simp] theorem mem_theoryDenotation {θ : Set (Description Sig)} :
    u ∈ I.theoryDenotation θ ↔ ∀ d ∈ θ, u ∈ I.denotation d := Iff.rfl

theorem models_iff_theoryDenotation_eq_univ : I.Models G ↔ I.theoryDenotation G = Set.univ := by
  simp only [Set.eq_univ_iff_forall, mem_theoryDenotation]
  exact ⟨fun h u d hd g ↦ h d hd g u, fun h d hd g u ↦ h u d hd g⟩

/-- An interpretation is a model of a grammar exactly when every entity satisfies every
principle under the assignment of every variable to that entity. -/
theorem models_iff : I.Models G ↔ ∀ d ∈ G, ∀ u, I.Satisfies (fun _ ↦ u) u d :=
  ⟨fun h d hd u ↦ h d hd _ u, fun h d hd _ u ↦ mem_denotation_iff.2 (h d hd u) _⟩

instance [Fintype U] [DecidableEq U] [DecidableLE Srt] [Fintype Sig.Attr]
    [∀ ρ, DecidablePred (· ∈ I.R ρ)] (ds : List (Description Sig)) :
    Decidable (I.Models (.ofList ds)) :=
  decidable_of_iff (∀ d ∈ ds, ∀ u, I.Satisfies (fun _ ↦ u) u d)
    ⟨fun h ↦ models_iff.2 h, fun h ↦ models_iff.1 h⟩

@[simp] theorem models_empty : I.Models ∅ := fun _ h ↦ absurd h (Set.notMem_empty _)

@[simp] theorem models_union : I.Models (G ∪ H) ↔ I.Models G ∧ I.Models H := by
  simp only [Models, Set.mem_union, or_imp, forall_and]

theorem Models.mono (hI : I.Models H) (hGH : G ⊆ H) : I.Models G :=
  fun d hd ↦ hI d (hGH hd)

/-! ### Embeddings -/

namespace Embedding

variable {V : Type*} {J : Interpretation Sig V} (f : Embedding I J) {D : Set U} {g : ℕ → U}
  {φ : Formula Sig}

/-- An entity satisfies a formula with quantifiers over `D` exactly when its image under an
embedding satisfies it with quantifiers over the image of `D`. -/
theorem satisfiesOn_image :
    J.SatisfiesOn (f '' D) (f ∘ g) (f u) φ ↔ I.SatisfiesOn D g u φ := by
  induction φ generalizing g with
  | sortAssign t σ =>
    rw [satisfiesOn_sortAssign, satisfiesOn_sortAssign, HomClass.termDenot_comp]
    cases I.termDenot g t u <;> simp
  | pathEq t₁ t₂ =>
    rw [satisfiesOn_pathEq, satisfiesOn_pathEq, HomClass.termDenot_comp,
      HomClass.termDenot_comp]
    rcases I.termDenot g t₁ u with _ | a <;> rcases I.termDenot g t₂ u with _ | b <;>
      simp [f.injective.eq_iff, eq_comm]
  | rel ρ xs => exact f.map_R (xs := fun i ↦ g (xs i))
  | neg d ih => exact not_congr ih
  | imp d e ihd ihe => exact imp_congr ihd ihe
  | all x d ih =>
    simp only [satisfiesOn_all, Set.forall_mem_image, ← ih, Function.comp_update]

/-- An entity satisfies a formula exactly when its image under an embedding does. -/
theorem satisfies : J.Satisfies (f ∘ g) (f u) φ ↔ I.Satisfies g u φ := by
  rw [Satisfies, ← HomClass.image_isComponentOf, satisfiesOn_image, Satisfies]

/-- A description describes an entity exactly when it describes its image under an embedding. -/
@[simp] theorem apply_mem_denotation : f u ∈ J.denotation d ↔ u ∈ I.denotation d := by
  rw [mem_denotation_iff, mem_denotation_iff]
  exact f.satisfies (g := fun _ ↦ u)

@[simp] theorem apply_mem_theoryDenotation {θ : Set (Description Sig)} :
    f u ∈ J.theoryDenotation θ ↔ u ∈ I.theoryDenotation θ := by
  simp only [mem_theoryDenotation, apply_mem_denotation]

/-- An interpretation that embeds into a model of a grammar is a model of it. -/
theorem models (f : Embedding I J) (hJ : J.Models G) : I.Models G :=
  fun d hd g u ↦ f.satisfies.1 (hJ d hd (f ∘ g) (f u))

/-- An interpretation onto which a model of a grammar embeds is a model of it. -/
theorem models_of_surjective (f : Embedding I J) (hf : Function.Surjective f)
    (hI : I.Models G) : J.Models G :=
  models_iff.2 fun d hd v ↦ by
    obtain ⟨u, rfl⟩ := hf v
    exact (f.satisfies (g := fun _ ↦ u)).2 (hI d hd _ u)

end Embedding

end Interpretation

/-! ### Attribute-value descriptions -/

/-- An atom holds of an entity when its path has a value of its sort there, or its two paths
lead from the entity to one entity. -/
def PathAtom.Holds (I : Interpretation Sig U) (u : U) : PathAtom Sig → Prop
  | .sort p σ => I.SortAt u p σ
  | .eq p q => I.PathEq u p q

namespace Interpretation

variable {I : Interpretation Sig U} {C D : List (Constraint Sig)} {c : Constraint Sig}
  {g : ℕ → U} {u : U}

theorem satisfies_toFormula_pathAtom {a : PathAtom Sig} :
    I.Satisfies g u a.toFormula ↔ a.Holds I u := by
  cases a
  exacts [satisfies_sortAssign_path, satisfies_pathEq_path]

theorem satisfies_body : I.Satisfies g u c.body ↔ ∀ a ∈ c.atoms, a.Holds I u := by
  unfold Constraint.body
  induction c.atoms with
  | nil => simpa [satisfies_toFormula_pathAtom] using ⟨u, rfl, rfl⟩
  | cons a as ih => simp [ih, satisfies_toFormula_pathAtom]

@[simp] theorem satisfies_toFormula :
    I.Satisfies g u c.toFormula ↔ I.S u ≤ c.sort → ∀ a ∈ c.atoms, a.Holds I u := by
  simp [Constraint.toFormula, satisfies_body]

/-- An entity satisfies the descriptions that state a list of constraints exactly when the atoms
of the constraints that its sort inherits hold of it. -/
theorem forall_satisfies_ofConstraints_iff [DecidableLE Srt] :
    (∀ d ∈ Grammar.ofConstraints C, I.Satisfies g u d) ↔
      ∀ c ∈ Constraint.inherited C (I.S u), ∀ a ∈ c.atoms, a.Holds I u := by
  simp [Constraint.inherited]

theorem models_ofConstraints_iff :
    I.Models (.ofConstraints C) ↔
      ∀ c ∈ C, ∀ u, I.S u ≤ c.sort → ∀ a ∈ c.atoms, a.Holds I u := by
  simp only [models_iff, Grammar.mem_ofList, List.forall_mem_map, Constraint.toDescription_toFormula,
    satisfies_toFormula]

theorem Models.of_append_left (hI : I.Models (.ofConstraints (C ++ D))) :
    I.Models (.ofConstraints C) := by
  rw [Grammar.ofConstraints_append, models_union] at hI
  exact hI.1

/-- In a model of a grammar, an atom of a constraint holds of each entity of the constraint's
sort. -/
theorem Models.holds (hI : I.Models (.ofConstraints C)) (hc : c ∈ C) (hu : I.S u ≤ c.sort)
    {a : PathAtom Sig} (ha : a ∈ c.atoms) : a.Holds I u :=
  models_ofConstraints_iff.1 hI c hc u hu a ha

/-- In a model of a grammar, an entity of a constraint's sort has a value of the sort `σ` at the
path `p` when the constraint says so. The constraint is found in the grammar, and the atom in
the constraint, by `decide`. -/
theorem Models.sortAt (hI : I.Models (.ofConstraints C)) (c : Constraint Sig)
    (hu : I.S u ≤ c.sort) {p : Path Sig} {σ : Srt} (hc : c ∈ C := by decide)
    (ha : .sort p σ ∈ c.atoms := by decide) : I.SortAt u p σ :=
  hI.holds hc hu ha

/-- In a model of a grammar, two paths lead from an entity of a constraint's sort to one entity
when the constraint equates them. -/
theorem Models.pathEq (hI : I.Models (.ofConstraints C)) (c : Constraint Sig)
    (hu : I.S u ≤ c.sort) {p q : Path Sig} (hc : c ∈ C := by decide)
    (ha : .eq p q ∈ c.atoms := by decide) : I.PathEq u p q :=
  hI.holds hc hu ha

end Interpretation

end HPSG.RSRL
