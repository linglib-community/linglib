module

public import Linglib.Syntax.HPSG.Interpretation
public import Mathlib.Data.Finset.Image
public import Mathlib.Logic.Function.Basic

/-!
# RSRL formulae, descriptions and grammars

This file defines the formulae of RSRL and what it means for an entity to satisfy one.

A formula says something about an entity. Its atomic parts say that a term has a given sort,
that two terms denote the same entity, or that some variables stand in a relation. The
quantifiers range over the *components* of the entity being described, not over the whole
universe.

A *description* is a formula with no free variables. A *grammar* is a set of descriptions, and
an interpretation is a *model* of a grammar when every entity satisfies every description in it
(`HPSG.RSRL.Interpretation.Models`).

## Embeddings preserve satisfaction

An entity satisfies a formula exactly when its image under an embedding does
(`HPSG.RSRL.Interpretation.Embedding.satisfies`). It follows that an interpretation that embeds
into a model is a model (`HPSG.RSRL.Interpretation.Embedding.models`), and that a model
containing an exhaustive model is exhaustive
(`HPSG.RSRL.Interpretation.Embedding.isExhaustive`).

## Implementation notes

Negation, implication and universal quantification are the primitive connectives. Conjunction,
disjunction and existential quantification are defined from them, as in mathlib's
`FirstOrder.Language.BoundedFormula`, so an induction on formulae has six cases. The lemmas
`satisfiesOn_and`, `satisfiesOn_or` and `satisfiesOn_ex` give the clauses of [richter-2024] for
the defined connectives.

As in Richter's syntax, a relation symbol applies to variables only.

`SatisfiesOn` takes the range of the quantifiers as an argument. `Satisfies` sets that range to
the components of the described entity.

A model satisfies its principles under every assignment of the variables. `models_iff` reduces
this to one assignment, which sends every variable to the described entity. This is what makes
`Models` decidable for a grammar given by a list, on a finite universe.

## References

* [richter-2000]
* [richter-2024]
-/

@[expose] public section

namespace HPSG.RSRL

universe u v

variable {Srt : Type u} [PartialOrder Srt]

/-- A formula of the description language ([richter-2024], Definition 4). -/
inductive Formula (Sig : Signature Srt) where
  /-- The sort assignment `t ∼ σ` says that `t` denotes an entity whose sort is at least as
  specific as `σ`. -/
  | sortAssign (t : Term Sig) (σ : Srt)
  /-- The path equation `t₁ ≈ t₂` says that `t₁` and `t₂` denote the same entity. -/
  | pathEq (t₁ t₂ : Term Sig)
  /-- The relational formula `ρ(x₁, …, xₙ)` says that the values of the variables stand in the
  relation `ρ`. -/
  | rel (ρ : Sig.Rel) (xs : Fin (Sig.arity ρ) → ℕ)
  /-- Negation. -/
  | neg (d : Formula Sig)
  /-- Classical implication. -/
  | imp (d e : Formula Sig)
  /-- The formula `all x d` says that `d` holds when `x` is any component of the described
  entity. -/
  | all (x : ℕ) (d : Formula Sig)

variable {Sig : Signature Srt} {U : Type v}

namespace Formula

/-- Conjunction. -/
protected def and (d e : Formula Sig) : Formula Sig := (d.imp e.neg).neg

/-- Disjunction. -/
protected def or (d e : Formula Sig) : Formula Sig := d.neg.imp e

/-- The formula `ex x d` says that `d` holds when `x` is some component of the described
entity. -/
def ex (x : ℕ) (d : Formula Sig) : Formula Sig := (all x d.neg).neg

/-- The biconditional of two formulae. -/
protected def iff (d e : Formula Sig) : Formula Sig := (d.imp e).and (e.imp d)

/-- The formula `∀ x₀ (x₀ ≈ x₀)`, which every entity satisfies, in place of a constant for
truth. -/
def top : Formula Sig := .all 0 (.pathEq (.var 0) (.var 0))

/-- The negation of `top`, which no entity satisfies. -/
def bot : Formula Sig := top.neg

/-- The conjunction of a list of formulae. -/
def conj (ds : List (Formula Sig)) : Formula Sig := ds.foldr Formula.and top

/-- The disjunction of a list of formulae. -/
def disj (ds : List (Formula Sig)) : Formula Sig := ds.foldr Formula.or bot

/-- The variables that occur free in a formula ([richter-2024], Definition 5). -/
def freeVars : Formula Sig → Finset ℕ
  | sortAssign t _ => t.freeVars
  | pathEq t₁ t₂ => t₁.freeVars ∪ t₂.freeVars
  | rel _ xs => Finset.univ.image xs
  | neg d => d.freeVars
  | imp d e => d.freeVars ∪ e.freeVars
  | all x d => d.freeVars.erase x

@[simp] theorem freeVars_and (d e : Formula Sig) :
    (d.and e).freeVars = d.freeVars ∪ e.freeVars := rfl

@[simp] theorem freeVars_or (d e : Formula Sig) : (d.or e).freeVars = d.freeVars ∪ e.freeVars := rfl

@[simp] theorem freeVars_ex (x : ℕ) (d : Formula Sig) :
    (ex x d).freeVars = d.freeVars.erase x := rfl

@[simp] theorem freeVars_iff (d e : Formula Sig) :
    (d.iff e).freeVars = d.freeVars ∪ e.freeVars := by
  simp [Formula.iff, freeVars, Finset.union_comm]

/-- A formula is colon-free when none of its terms starts at the described entity. -/
def IsColonFree : Formula Sig → Prop
  | sortAssign t _ => t.IsColonFree
  | pathEq t₁ t₂ => t₁.IsColonFree ∧ t₂.IsColonFree
  | rel _ _ => True
  | neg d | all _ d => d.IsColonFree
  | imp d e => d.IsColonFree ∧ e.IsColonFree

instance decidableIsColonFree : DecidablePred (IsColonFree (Sig := Sig))
  | sortAssign t _ => Term.decidableIsColonFree t
  | pathEq t₁ t₂ =>
    have := Term.decidableIsColonFree t₁
    have := Term.decidableIsColonFree t₂
    inferInstanceAs (Decidable (t₁.IsColonFree ∧ t₂.IsColonFree))
  | rel .. => isTrue trivial
  | neg d | all _ d => decidableIsColonFree d
  | imp d e =>
    have := decidableIsColonFree d
    have := decidableIsColonFree e
    inferInstanceAs (Decidable (d.IsColonFree ∧ e.IsColonFree))

end Formula

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

@[simp] theorem satisfies_ex {x : ℕ} : I.Satisfies g u (.ex x d) ↔
    ∃ w, I.IsComponentOf u w ∧ I.Satisfies (Function.update g x w) u d := satisfiesOn_ex

@[simp] theorem satisfies_all {x : ℕ} : I.Satisfies g u (.all x d) ↔
    ∀ w, I.IsComponentOf u w → I.Satisfies (Function.update g x w) u d := Iff.rfl

theorem SatisfiesOn.and_left (h : I.SatisfiesOn D g u (d.and e)) : I.SatisfiesOn D g u d :=
  (satisfiesOn_and.1 h).1

theorem SatisfiesOn.and_right (h : I.SatisfiesOn D g u (d.and e)) : I.SatisfiesOn D g u e :=
  (satisfiesOn_and.1 h).2

theorem SatisfiesOn.sortAssign_mono {t : Term Sig} {σ τ : Srt} (hστ : σ ≤ τ)
    (h : I.SatisfiesOn D g u (.sortAssign t σ)) : I.SatisfiesOn D g u (.sortAssign t τ) :=
  let ⟨v, hv, hσ⟩ := h; ⟨v, hv, hσ.trans hστ⟩

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

/-! ### Descriptions and grammars -/

/-- A description is a formula with no free variables ([richter-2024], Definition 6). -/
@[ext] structure Description (Sig : Signature Srt) where
  /-- The formula. -/
  toFormula : Formula Sig
  /-- The formula has no free variables. -/
  freeVars_toFormula : toFormula.freeVars = ∅ := by decide

attribute [coe] Description.toFormula
attribute [simp] Description.freeVars_toFormula

instance : Coe (Description Sig) (Formula Sig) := ⟨Description.toFormula⟩

/-- A grammar over a signature is a set of descriptions, its principles
([richter-2024], Definition 16). -/
abbrev Grammar (Sig : Signature Srt) := Set (Description Sig)

/-- The grammar whose principles are the members of a list. -/
def Grammar.ofList (ds : List (Description Sig)) : Grammar Sig := {d | d ∈ ds}

@[simp] theorem Grammar.mem_ofList {ds : List (Description Sig)} {d : Description Sig} :
    d ∈ Grammar.ofList ds ↔ d ∈ ds := Iff.rfl

@[simp] theorem Grammar.ofList_append (ds es : List (Description Sig)) :
    Grammar.ofList (ds ++ es) = Grammar.ofList ds ∪ Grammar.ofList es :=
  Set.ext fun _ ↦ List.mem_append

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

/-- A model of a grammar is exhaustive when every theory that describes some entity of some
model of the grammar describes one of its entities ([richter-2024], Definition 19). -/
structure IsExhaustive (G : Grammar Sig) : Prop where
  /-- An exhaustive model is a model. -/
  models : I.Models G
  /-- A theory with a nonempty denotation in a model has one in an exhaustive model. -/
  nonempty_theoryDenotation (θ : Set (Description Sig)) ⦃U' : Type v⦄
    (I' : Interpretation Sig U') : I'.Models G → (I'.theoryDenotation θ).Nonempty →
      (I.theoryDenotation θ).Nonempty

variable {I}

/-- An entity is described by a description exactly when it satisfies it under the assignment
of every variable to itself, since a description has no free variables. -/
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

/-- Satisfaction is invariant under embeddings: an entity satisfies a formula exactly when its
image does, since the components of the image are the images of the components. -/
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

/-- A model of a grammar that embeds onto an interpretation makes it a model. -/
theorem models_of_surjective (f : Embedding I J) (hf : Function.Surjective f)
    (hI : I.Models G) : J.Models G :=
  models_iff.2 fun d hd v ↦ by
    obtain ⟨u, rfl⟩ := hf v
    exact (f.satisfies (g := fun _ ↦ u)).2 (hI d hd _ u)

/-- A model of a grammar into which an exhaustive model embeds is exhaustive. -/
theorem isExhaustive {V : Type v} {J : Interpretation Sig V} (f : Embedding I J)
    (hI : I.IsExhaustive G) (hJ : J.Models G) : J.IsExhaustive G :=
  ⟨hJ, fun θ _ I' hI' hθ ↦
    let ⟨u, hu⟩ := hI.nonempty_theoryDenotation θ I' hI' hθ
    ⟨f u, f.apply_mem_theoryDenotation.2 hu⟩⟩

end Embedding

end Interpretation

/-! ### Constraints on sorts -/

/-- A constraint `σ ⇒ φ` requires every entity whose sort is at least as specific as `σ` to
satisfy the formula `φ`, which has no free variables. -/
structure Constraint (Sig : Signature Srt) where
  /-- The sort that the constraint applies to. -/
  sort : Srt
  /-- The formula that the entities of that sort satisfy. -/
  body : Formula Sig
  /-- The body has no free variables. -/
  freeVars_body : body.freeVars = ∅ := by decide

namespace Constraint

attribute [simp] freeVars_body

/-- The formula that states a constraint. -/
def toFormula (c : Constraint Sig) : Formula Sig := (Formula.sortAssign .colon c.sort).imp c.body

@[simp] theorem freeVars_toFormula (c : Constraint Sig) : c.toFormula.freeVars = ∅ := by
  simp [toFormula, Formula.freeVars, Term.freeVars]

/-- The description that states a constraint. -/
@[coe, simps] def toDescription (c : Constraint Sig) : Description Sig :=
  ⟨c.toFormula, c.freeVars_toFormula⟩

instance : Coe (Constraint Sig) (Description Sig) := ⟨toDescription⟩

/-- The constraints among `C` that the sort `σ` inherits, those on `σ` and on its supersorts. -/
def inherited [DecidableLE Srt] (C : List (Constraint Sig)) (σ : Srt) : List (Constraint Sig) :=
  C.filter fun c ↦ σ ≤ c.sort

end Constraint

namespace Interpretation

variable {I : Interpretation Sig U} {C : List (Constraint Sig)} {g : ℕ → U} {u : U}

@[simp] theorem satisfies_toFormula {c : Constraint Sig} :
    I.Satisfies g u c.toFormula ↔ I.S u ≤ c.sort → I.Satisfies g u c.body := by
  simp [Constraint.toFormula]

/-- An entity satisfies the descriptions that state a list of constraints exactly when it
satisfies the bodies of the constraints that its sort inherits. -/
theorem forall_satisfies_map_toDescription_iff [DecidableLE Srt] :
    (∀ d ∈ Grammar.ofList (C.map Constraint.toDescription), I.Satisfies g u d) ↔
      ∀ c ∈ Constraint.inherited C (I.S u), I.Satisfies g u c.body := by
  simp [Constraint.inherited]

theorem models_ofList_map_toDescription_iff [DecidableLE Srt] :
    I.Models (.ofList (C.map Constraint.toDescription)) ↔
      ∀ u, ∀ c ∈ Constraint.inherited C (I.S u), I.Satisfies (fun _ ↦ u) u c.body :=
  models_iff.trans
    ⟨fun h u ↦ forall_satisfies_map_toDescription_iff.1 fun d hd ↦ h d hd u,
      fun h d hd u ↦ forall_satisfies_map_toDescription_iff.2 (h u) d hd⟩

theorem Models.satisfies_body {G : Grammar Sig} (hI : I.Models G) {c : Constraint Sig}
    (hc : c.toDescription ∈ G) (hu : I.S u ≤ c.sort) : I.Satisfies g u c.body :=
  satisfies_toFormula.1 (hI _ hc g u) hu

end Interpretation

end HPSG.RSRL
