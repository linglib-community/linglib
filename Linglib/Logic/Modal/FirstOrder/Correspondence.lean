module

public import Linglib.Core.ModelTheory.Binders
public import Linglib.Logic.Modal.FirstOrder.Semantics

/-!
# The standard translation

The *standard translation* rewrites a modal formula as a first-order formula about worlds and
individuals, so that results about first-order logic apply to modal logic. A formula over a
signature `L` becomes a formula over the *correspondence language* of `L`, which has, for each
symbol of `L`, a symbol taking a world as an extra first argument, together with a binary
accessibility relation and a predicate true of individuals. Necessity becomes universal
quantification over the accessible worlds, and the quantifiers range over individuals. A Kripke
model becomes a single first-order structure whose domain contains both its worlds and its
individuals, and the translation [preserves satisfaction](##realize_st): a modal formula holds at
a world exactly when its translation holds with the current-world variable assigned that world.

## Main definitions

* `FirstOrder.Language.correspondence`: the correspondence language of a signature.
* `FirstOrder.Language.ModalStructure.correspondence`: a Kripke model as one first-order
  structure on its worlds and individuals.
* `FirstOrder.Language.ModalFormula.st`: the standard translation.
* `FirstOrder.Language.stClose`: the existential closure of the current-world variable over
  worlds.

## Implementation notes

World variables are numbered: the current world is the variable `Sum.inr k`, and necessity
quantifies the fresh variable `Sum.inr (k + 1)`. Worlds and individuals share the carrier
`W ⊕ M`, sorted by the predicate true of individuals; an atom applied to arguments of the wrong
sort is false, and a function symbol applied to them takes a default value.

## References

* [blackburn-derijke-venema-2001] — the standard translation
-/

@[expose] public section

namespace FirstOrder.Language

variable {W M Var : Type*}

/-! ### The correspondence language -/

/-- The correspondence language of `L`: an `(n + 1)`-ary symbol for each `n`-ary symbol of `L`,
whose first argument is a world, together with a predicate true of individuals and an
accessibility relation. -/
def correspondence (L : Language) : Language where
  Functions := fun n ↦ match n with
    | 0 => PEmpty
    | n + 1 => L.Functions n
  Relations := fun n ↦ match n with
    | 0 => PEmpty
    | n + 1 => L.Relations n ⊕ (match n with | 0 | 1 => PUnit | _ => PEmpty)

variable {L : Language} {n : ℕ}

abbrev corrFunc (f : L.Functions n) : L.correspondence.Functions (n + 1) := f

abbrev corrRel (R : L.Relations n) : L.correspondence.Relations (n + 1) := Sum.inl R

/-- The predicate true of individuals. -/
abbrev corrIndiv : L.correspondence.Relations 1 := Sum.inr PUnit.unit

/-- The accessibility relation symbol. -/
abbrev corrAcc : L.correspondence.Relations 2 := Sum.inr PUnit.unit

abbrev corrIndivVar (x : Var) : L.correspondence.Term (Var ⊕ ℕ) := Term.var (Sum.inl x)

abbrev corrWorldVar (k : ℕ) : L.correspondence.Term (Var ⊕ ℕ) := Term.var (Sum.inr k)

/-! ### Sorted valuations -/

/-- The assignment to individual and world variables given by an assignment `v` of
individuals and an assignment `u` of worlds. -/
def stVal (v : Var → M) (u : ℕ → W) : Var ⊕ ℕ → W ⊕ M :=
  Sum.elim (Sum.inr ∘ v) (Sum.inl ∘ u)

@[simp] theorem stVal_inl (v : Var → M) (u : ℕ → W) (x : Var) :
    stVal v u (Sum.inl x) = Sum.inr (v x) := rfl

@[simp] theorem stVal_inr (v : Var → M) (u : ℕ → W) (j : ℕ) :
    stVal v u (Sum.inr j) = Sum.inl (u j) := rfl

theorem stVal_update_indiv [DecidableEq Var] (v : Var → M) (u : ℕ → W) (x : Var) (d : M) :
    Function.update (stVal v u) (Sum.inl x) (Sum.inr d) =
      stVal (Function.update v x d) u := by
  simp only [stVal, Sum.update_elim_inl, Function.comp_update]

theorem stVal_update_world [DecidableEq Var] (v : Var → M) (u : ℕ → W) (j : ℕ) (w : W) :
    Function.update (stVal v u) (Sum.inr j) (Sum.inl w) =
      stVal v (Function.update u j w) := by
  simp only [stVal, Sum.update_elim_inr, Function.comp_update]

/-! ### The translation -/

/-- The translation of terms: a variable is unchanged, and a function symbol takes the current
world as its first argument. -/
def stTerm (k : ℕ) : L.Term Var → L.correspondence.Term (Var ⊕ ℕ)
  | .var x => corrIndivVar x
  | .func f args =>
      Term.func (corrFunc f) (Fin.cons (corrWorldVar k) fun i ↦ stTerm k (args i))

/-- The standard translation $ST_k$ [blackburn-derijke-venema-2001], with the current world
the variable `Sum.inr k`. Atoms take the current world as their first argument, necessity
quantifies the variable `Sum.inr (k + 1)` over the worlds accessible from the current one, and
the quantifiers range over individuals. -/
def ModalFormula.st [DecidableEq Var] (k : ℕ) :
    ModalFormula L Var → L.correspondence.Formula (Var ⊕ ℕ)
  | .equal t₁ t₂ => Term.equal (stTerm k t₁) (stTerm k t₂)
  | .rel R ts =>
      (corrRel R).formula (Fin.cons (corrWorldVar k) fun i ↦ stTerm k (ts i))
  | .falsum => ⊥
  | .imp φ ψ => φ.st k ⟹ ψ.st k
  | .box φ => Formula.all₁ (Sum.inr (k + 1))
      (corrAcc.formula₂ (corrWorldVar k) (corrWorldVar (k + 1)) ⟹ φ.st (k + 1))
  | .all x φ => Formula.all₁ (Sum.inl x)
      (corrIndiv.formula₁ (corrIndivVar x) ⟹ φ.st k)

/-! ### Sort-guarded sentence closure -/

/-- The existential closure of the current-world variable `Sum.inr k` over worlds,
$\exists z \, (\neg \mathrm{Indiv}(z) \land \psi)$. Without the restriction to worlds an
individual could witness the quantifier, and an individual accesses no world, so it satisfies
$\Box \bot$. -/
def stClose [DecidableEq Var] (k : ℕ) (ψ : L.correspondence.Formula (Var ⊕ ℕ)) :
    L.correspondence.Formula (Var ⊕ ℕ) :=
  Formula.ex₁ (Sum.inr k)
    ((corrIndiv.formula₁ (corrWorldVar k)).not ⊓ ψ)

theorem realize_stClose [DecidableEq Var] [L.correspondence.Structure (W ⊕ M)]
    (k : ℕ) (ψ : L.correspondence.Formula (Var ⊕ ℕ)) (val : Var ⊕ ℕ → W ⊕ M)
    (hind : ∀ z : W ⊕ M,
      Structure.RelMap (corrIndiv (L := L)) ![z] ↔ ∃ d : M, z = Sum.inr d) :
    (stClose k ψ).Realize val ↔
      ∃ w : W, ψ.Realize (Function.update val (Sum.inr k) (Sum.inl w)) := by
  simp [stClose, hind, Sum.exists]

/-! ### The encoded structure -/

variable [Inhabited M] (K : ModalStructure L W M)

/-- A Kripke model as one structure for the correspondence language on its worlds and
individuals. An atom applied to arguments of the wrong sort is false, and a function symbol
applied to them takes a default value. -/
@[instance_reducible] def ModalStructure.correspondence :
    L.correspondence.Structure (W ⊕ M) where
  funMap := fun {n} f z ↦ match n, f with
    | 0, f => f.elim
    | _ + 1, f => Sum.inr <| (z 0).elim
        (fun w ↦ K.funInterp f w fun i ↦ (z i.succ).getRight?.getD default) id
  RelMap := fun {n} r z ↦ match n, r with
    | 0, r => r.elim
    | n + 1, r => r.elim
        (fun R ↦ ∃ (w : W) (ds : Fin n → M),
          z 0 = Sum.inl w ∧ (∀ i, z i.succ = Sum.inr (ds i)) ∧
            K.relInterp R w ds)
        (fun u ↦ match n, z, u with
          | 0, z, _ => ∃ d : M, z 0 = Sum.inr d
          | 1, z, _ =>
              ∃ w₁ w₂, z 0 = Sum.inl w₁ ∧ z 1 = Sum.inl w₂ ∧ w₂ ∈ K.access w₁
          | _ + 2, _, u => u.elim)

@[simp] theorem correspondence_relMap_rel (R : L.Relations n) (z : Fin (n + 1) → W ⊕ M) :
    K.correspondence.RelMap (corrRel R) z ↔
      ∃ (w : W) (ds : Fin n → M),
        z 0 = Sum.inl w ∧ (∀ i, z i.succ = Sum.inr (ds i)) ∧
          K.relInterp R w ds :=
  Iff.rfl

@[simp] theorem correspondence_relMap_acc (z : Fin 2 → W ⊕ M) :
    K.correspondence.RelMap corrAcc z ↔
      ∃ w₁ w₂, z 0 = Sum.inl w₁ ∧ z 1 = Sum.inl w₂ ∧ w₂ ∈ K.access w₁ :=
  Iff.rfl

@[simp] theorem correspondence_relMap_indiv (z : Fin 1 → W ⊕ M) :
    K.correspondence.RelMap corrIndiv z ↔
      ∃ d : M, z 0 = Sum.inr d :=
  Iff.rfl

theorem correspondence_funMap_inl (f : L.Functions n) (w : W) (z : Fin (n + 1) → W ⊕ M)
    (ds : Fin n → M) (hz : z 0 = Sum.inl w)
    (hds : ∀ i, z i.succ = Sum.inr (ds i)) :
    K.correspondence.funMap (corrFunc f) z = Sum.inr (K.funInterp f w ds) := by
  obtain rfl : z = Fin.cons (Sum.inl w) (fun i ↦ Sum.inr (ds i)) :=
    funext fun j ↦ Fin.cases hz hds j
  rfl

/-! ### Satisfaction preservation -/

private theorem realize_stTerm {k : ℕ} {v : Var → M} {u : ℕ → W} :
    ∀ t : L.Term Var,
      (letI := K.correspondence; (stTerm k t).realize (stVal v u)) =
        Sum.inr (t.realizeAt K.interp (u k) v)
  | .var x => rfl
  | .func f args => by
    let _S := K.correspondence
    let _I := K.interp (u k)
    rw [show stTerm k (.func f args) = Term.func (corrFunc f)
        (Fin.cons (corrWorldVar k) fun i ↦ stTerm k (args i)) from rfl,
      Term.realize_func,
      correspondence_funMap_inl K f (u k) _
        (fun i ↦ (args i).realizeAt K.interp (u k) v)
        rfl
        (fun i ↦ by simpa [Fin.cons_succ] using realize_stTerm (args i))]
    rfl

/-- The standard translation preserves satisfaction: a modal formula holds at a world exactly
when its translation holds in the model's first-order structure with the current-world variable
assigned that world. -/
theorem realize_st [DecidableEq Var] {φ : ModalFormula L Var} {k : ℕ}
    {v : Var → M} {u : ℕ → W} :
    φ.Realize K (u k) v ↔
      (letI := K.correspondence; (φ.st k).Realize (stVal v u)) := by
  induction φ generalizing k v u with
  | equal t₁ t₂ => simp [ModalFormula.st, realize_stTerm K]
  | falsum => exact Iff.rfl
  | imp φ ψ ih₁ ih₂ => simp [ModalFormula.st, ← ih₁, ← ih₂]
  | box φ ih =>
    simp [ModalFormula.st, stVal_update_world, ← ih]
  | all x φ ih =>
    simp [ModalFormula.st, stVal_update_indiv, ← ih]
  | @rel n R ts =>
    simp [ModalFormula.st, realize_stTerm K, ModalStructure.relInterp, ← funext_iff]

end FirstOrder.Language
