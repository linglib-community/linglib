module

public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Linglib.Logic.Assignment
public import Linglib.Logic.Modal.FirstOrder.Semantics
public import Linglib.Core.ModelTheory.LanguageMap
public import Linglib.Logic.Team.Operations
public import Linglib.Logic.Team.Kripke

/-!
# Quantified bilateral state-based modal logic (QBSML)

QBSML ([aloni-vanormondt-2023]) is the first-order extension of BSML
([aloni-2022], [anttila-2021]). A formula is evaluated bilaterally —
supported or anti-supported — at a *state*: a finite set of *indices*
`⟨w, g⟩` pairing a world with a partial variable assignment. Quantifiers
are interpreted by extending states, disjunction by splitting them, and
the non-emptiness atom `NE` — the only source of non-classical behaviour —
by state non-emptiness.

## Main definitions

* `Index`, `State.worldProj`: indices `⟨w, g⟩` and the world projection `s↓`.
* `State.extendIndividual`, `State.extendUniversal`,
  `State.extendFunctional`: the state extensions `s[x/d]`, `s[x]`, `s[x/h]`.
* `State.modalLift`: a set of worlds, paired with one assignment.
* `Formula`: the formula language; `Formula.nec` is the derived `□`;
  `Formula.NEFree` the NE-free fragment.
* `Model`, `Model.ofMonadic`: models, as `ModalStructure`s over the monadic
  signature with constants `(Language.monadic Pred)[[Const]]`.
* `eval`, `support`, `antiSupport`: bilateral evaluation.

## Implementation notes

* The paper takes `□` primitive and derives `◇`; we invert this, so
  `eval`'s `poss` clauses match the paper's derived `◇`-clauses.
* The paper's requirement that all indices of a state share an assignment
  domain is not enforced at the type level; the state operations
  preserve it.
* Each `eval` clause is an operation on team properties applied to the
  support sets of the subformulas: the propositional and modal clauses are
  those of `Team/Operations.lean` (`Team.flat`, `Team.tensor`, `Team.ne`),
  the quantifier clauses `State.univ` and `State.exi` below. The closure
  inductions of `QBSML/Properties.lean` are folds over their lemmas.
-/

@[expose] public section

namespace QBSML

open FirstOrder

variable {W Var Domain : Type*}

/-! ### Indices -/

/-- An index is a (world, assignment) pair ([aloni-vanormondt-2023]
    Definition 4.2: `i = ⟨wᵢ, gᵢ⟩`), with `gᵢ` a `PartialAssign`. -/
abbrev Index (W Var Domain : Type*) := W × PartialAssign Var Domain

/-- The world component of an index. -/
abbrev Index.world (i : Index W Var Domain) : W := i.1

/-- The assignment component of an index. -/
abbrev Index.assign (i : Index W Var Domain) : PartialAssign Var Domain := i.2

section Update

variable [DecidableEq Var]

/-- Update an index's assignment ([aloni-vanormondt-2023] Definitions 4.3–4.4:
    `i[x/d] := ⟨wᵢ, gᵢ[x/d]⟩`, with the assignment update `gᵢ[x/d]` as
    mathlib's `Function.update`). -/
def Index.update (i : Index W Var Domain) (x : Var) (d : Domain) :
    Index W Var Domain :=
  (i.world, Function.update i.assign x ↑d)

@[simp] theorem Index.world_update (i : Index W Var Domain) (x : Var)
    (d : Domain) : (i.update x d).world = i.world := rfl

@[simp] theorem Index.assign_update (i : Index W Var Domain) (x : Var)
    (d : Domain) : (i.update x d).assign = Function.update i.assign x ↑d :=
  rfl

end Update

/-! ### The world projection -/

section WorldProj

variable [DecidableEq W]

/-- The world projection `s↓` of a state of indices: the set of worlds
    appearing in some index ([aloni-vanormondt-2023] Definition 4.10:
    `s↓ := {w | ∃g, (w, g) ∈ s}`). Frame conditions on accessibility are
    stated relative to `s↓`, so QBSML reuses BSML's notions via this
    projection. -/
def State.worldProj (s : Finset (Index W Var Domain)) : Finset W :=
  s.image Index.world

@[simp] theorem State.mem_worldProj {s : Finset (Index W Var Domain)} {w : W} :
    w ∈ State.worldProj s ↔ ∃ i ∈ s, i.world = w :=
  Finset.mem_image

theorem State.worldProj_mono {s t : Finset (Index W Var Domain)} (h : s ⊆ t) :
    State.worldProj s ⊆ State.worldProj t :=
  Finset.image_subset_image h

theorem State.worldProj_nonempty {s : Finset (Index W Var Domain)}
    (h : s.Nonempty) : (State.worldProj s).Nonempty :=
  h.image _

end WorldProj

/-! ### State extensions -/

section State

variable [DecidableEq W] [DecidableEq Var] [Fintype Var] [DecidableEq Domain]

/-- **Individual extension** `s[x/d]`: assign `x` to `d` in every index
    ([aloni-vanormondt-2023] Definition 4.5: `s[x/d] := {i[x/d] | i ∈ s}`). -/
def State.extendIndividual (s : Finset (Index W Var Domain))
    (x : Var) (d : Domain) : Finset (Index W Var Domain) :=
  s.image (fun i => i.update x d)

/-- **Universal extension** `s[x]`: extend with every domain value at `x`
    ([aloni-vanormondt-2023] Definition 4.6: `s[x] := {i[x/d] | i ∈ s, d ∈ D}`).
    Requires `[Fintype Domain]` to range over the entire domain. -/
def State.extendUniversal [Fintype Domain] (s : Finset (Index W Var Domain))
    (x : Var) : Finset (Index W Var Domain) :=
  Finset.univ.biUnion (fun d : Domain => State.extendIndividual s x d)

/-- **Functional extension** `s[x/h]`: for each `i ∈ s`, extend with values
    drawn from `h i` ([aloni-vanormondt-2023] Definition 4.7:
    `s[x/h] := {i[x/d] | i ∈ s, d ∈ h(i)}`). Interprets existential
    quantification: `∃x φ` iff `M, s[x/h] ⊨ φ` for some functional `h`. -/
def State.extendFunctional (s : Finset (Index W Var Domain))
    (x : Var) (h : Index W Var Domain → Finset Domain) :
    Finset (Index W Var Domain) :=
  s.biUnion (fun i => (h i).image (fun d => i.update x d))

/-! ### Membership characterisations -/

@[simp] theorem State.mem_extendIndividual {s : Finset (Index W Var Domain)}
    {x : Var} {d : Domain} {j : Index W Var Domain} :
    j ∈ State.extendIndividual s x d ↔ ∃ i ∈ s, i.update x d = j :=
  Finset.mem_image

@[simp] theorem State.mem_extendUniversal [Fintype Domain]
    {s : Finset (Index W Var Domain)} {x : Var} {j : Index W Var Domain} :
    j ∈ State.extendUniversal s x ↔ ∃ d, ∃ i ∈ s, i.update x d = j := by
  simp only [State.extendUniversal, Finset.mem_biUnion, Finset.mem_univ,
    true_and, State.mem_extendIndividual]

@[simp] theorem State.mem_extendFunctional {s : Finset (Index W Var Domain)}
    {x : Var} {h : Index W Var Domain → Finset Domain} {j : Index W Var Domain} :
    j ∈ State.extendFunctional s x h ↔ ∃ i ∈ s, ∃ d ∈ h i, i.update x d = j := by
  simp only [State.extendFunctional, Finset.mem_biUnion, Finset.mem_image]

/-! ### Extension algebra -/

theorem State.extendIndividual_empty (x : Var) (d : Domain) :
    State.extendIndividual (∅ : Finset (Index W Var Domain)) x d = ∅ :=
  Finset.image_empty _

theorem State.extendIndividual_union (s t : Finset (Index W Var Domain))
    (x : Var) (d : Domain) :
    State.extendIndividual (s ∪ t) x d =
      State.extendIndividual s x d ∪ State.extendIndividual t x d :=
  Finset.image_union ..

theorem State.extendIndividual_mono {s t : Finset (Index W Var Domain)}
    (x : Var) (d : Domain) (hsub : s ⊆ t) :
    State.extendIndividual s x d ⊆ State.extendIndividual t x d :=
  Finset.image_subset_image hsub

theorem State.extendUniversal_empty [Fintype Domain] (x : Var) :
    State.extendUniversal (∅ : Finset (Index W Var Domain)) x = ∅ := by
  ext j
  simp

theorem State.extendUniversal_union [Fintype Domain]
    (s t : Finset (Index W Var Domain)) (x : Var) :
    State.extendUniversal (s ∪ t) x =
      State.extendUniversal s x ∪ State.extendUniversal t x := by
  simp only [State.extendUniversal, State.extendIndividual_union,
    Finset.biUnion_union]

theorem State.extendUniversal_mono [Fintype Domain]
    {s t : Finset (Index W Var Domain)} (x : Var) (hsub : s ⊆ t) :
    State.extendUniversal s x ⊆ State.extendUniversal t x :=
  Finset.biUnion_mono fun d _ => State.extendIndividual_mono x d hsub

theorem State.extendFunctional_empty (x : Var)
    (h : Index W Var Domain → Finset Domain) :
    State.extendFunctional (∅ : Finset (Index W Var Domain)) x h = ∅ :=
  Finset.biUnion_empty

theorem State.extendFunctional_union (s t : Finset (Index W Var Domain))
    (x : Var) (h : Index W Var Domain → Finset Domain) :
    State.extendFunctional (s ∪ t) x h =
      State.extendFunctional s x h ∪ State.extendFunctional t x h :=
  Finset.union_biUnion

theorem State.extendFunctional_mono {s t : Finset (Index W Var Domain)}
    (x : Var) (h : Index W Var Domain → Finset Domain) (hsub : s ⊆ t) :
    State.extendFunctional s x h ⊆ State.extendFunctional t x h :=
  Finset.biUnion_subset_biUnion_of_subset_left _ hsub

theorem State.extendUniversal_eq_extendFunctional [Fintype Domain]
    (s : Finset (Index W Var Domain)) (x : Var) :
    State.extendUniversal s x =
      State.extendFunctional s x (fun _ => Finset.univ) := by
  ext j
  simp only [State.mem_extendUniversal, State.mem_extendFunctional,
    Finset.mem_univ, true_and]
  tauto

theorem State.extendFunctional_filter_of_update_mem [Fintype Domain]
    {s t : Finset (Index W Var Domain)} {x : Var}
    (hpar : ∀ j ∈ t, ∃ i ∈ s, ∃ d, i.update x d = j) :
    State.extendFunctional s x
      (fun i => Finset.univ.filter (fun d => i.update x d ∈ t)) = t := by
  ext j
  rw [State.mem_extendFunctional]
  constructor
  · rintro ⟨i, -, d, hd, rfl⟩
    exact (Finset.mem_filter.mp hd).2
  · intro hj
    obtain ⟨i, hi, d, rfl⟩ := hpar j hj
    exact ⟨i, hi, d, Finset.mem_filter.mpr ⟨Finset.mem_univ d, hj⟩, rfl⟩

/-! ### The quantifier clauses as operations on team properties

The universal-extension clause is the preimage of a property along `s ↦ s[x]`, and the
functional-extension clause asks for some functional, non-empty on the state, whose
extension lies in the property. These are the operations the quantifier cases of the closure
inductions in `QBSML/Properties.lean` consume, beside those of `Team/Operations.lean`. Union
closure of the functional clause needs downward closure of the property, which is why
QBSML's union closure is confined to the `NE`-free fragment. -/

/-- Universal extension `s ↦ s[x]` as a map of the bounded join-semilattice of states. -/
def State.extendUniversalHom [Fintype Domain] (x : Var) :
    SupBotHom (Finset (Index W Var Domain)) (Finset (Index W Var Domain)) where
  toFun s := State.extendUniversal s x
  map_sup' s t := State.extendUniversal_union s t x
  map_bot' := State.extendUniversal_empty x

@[simp] theorem State.extendUniversalHom_apply [Fintype Domain] (x : Var)
    (s : Finset (Index W Var Domain)) : State.extendUniversalHom x s = State.extendUniversal s x :=
  rfl

/-- The universal-extension clause: `s[x] ∈ P`. -/
def State.univ [Fintype Domain] (x : Var) (P : Team.TeamProperty (Index W Var Domain)) :
    Team.TeamProperty (Index W Var Domain) :=
  State.extendUniversalHom x ⁻¹' P

/-- The functional-extension clause: `s[x/h] ∈ P` for some `h` non-empty on `s`. -/
def State.exi (x : Var) (P : Team.TeamProperty (Index W Var Domain)) :
    Team.TeamProperty (Index W Var Domain) :=
  {s | ∃ h : Index W Var Domain → Finset Domain, (∀ i ∈ s, (h i).Nonempty) ∧
    State.extendFunctional s x h ∈ P}

section QuantifierClauses

variable {x : Var} {P : Team.TeamProperty (Index W Var Domain)} {s : Finset (Index W Var Domain)}

@[simp] theorem State.mem_univ [Fintype Domain] :
    s ∈ State.univ x P ↔ State.extendUniversal s x ∈ P := Iff.rfl

@[simp] theorem State.mem_exi :
    s ∈ State.exi x P ↔ ∃ h : Index W Var Domain → Finset Domain,
      (∀ i ∈ s, (h i).Nonempty) ∧ State.extendFunctional s x h ∈ P := Iff.rfl

theorem State.isLowerSet_univ [Fintype Domain] (hP : IsLowerSet P) :
    IsLowerSet (State.univ x P) :=
  hP.preimage (OrderHomClass.mono (State.extendUniversalHom x))

theorem State.supClosed_univ [Fintype Domain] (hP : SupClosed P) :
    SupClosed (State.univ x P) :=
  hP.preimage (State.extendUniversalHom x)

theorem State.empty_mem_univ [Fintype Domain] (hP : ∅ ∈ P) : ∅ ∈ State.univ x P :=
  by rw [State.univ, Set.mem_preimage, ← Finset.bot_eq_empty, map_bot]; exact hP

theorem State.isLowerSet_exi (hP : IsLowerSet P) : IsLowerSet (State.exi x P) := by
  rintro s t hts ⟨h, hne, hs⟩
  exact ⟨h, fun i hi ↦ hne i (hts hi), hP (State.extendFunctional_mono x h hts) hs⟩

theorem State.supClosed_exi (hP : IsLowerSet P) (hP' : SupClosed P) :
    SupClosed (State.exi x P) := by
  rintro s ⟨h_s, hne_s, hs⟩ t ⟨h_t, hne_t, ht⟩
  classical
  refine ⟨fun i ↦ if i ∈ s then h_s i else h_t i, fun i hi ↦ ?_, ?_⟩
  · by_cases his : i ∈ s
    · simpa [his] using hne_s i his
    · simpa [his] using hne_t i ((Finset.mem_union.mp hi).resolve_left his)
  · have eq1 : State.extendFunctional (s ∪ t) x (fun i ↦ if i ∈ s then h_s i else h_t i) =
        State.extendFunctional s x h_s ∪ State.extendFunctional (t \ s) x h_t := by
      rw [← Finset.union_sdiff_self_eq_union, State.extendFunctional_union]
      congr 1
      · unfold State.extendFunctional
        exact Finset.biUnion_congr rfl fun i hi ↦ by simp [hi]
      · unfold State.extendFunctional
        exact Finset.biUnion_congr rfl fun i hi ↦ by simp [(Finset.mem_sdiff.mp hi).2]
    show State.extendFunctional (s ∪ t) x _ ∈ P
    rw [eq1]
    exact hP' hs (hP (State.extendFunctional_mono x h_t Finset.sdiff_subset) ht)

theorem State.empty_mem_exi (hP : ∅ ∈ P) : ∅ ∈ State.exi x P :=
  ⟨fun _ ↦ ∅, fun _ hi ↦ absurd hi (Finset.notMem_empty _), by
    rw [State.extendFunctional_empty]; exact hP⟩

end QuantifierClauses

end State

/-! ### Modal pairing -/

section ModalLift

variable [DecidableEq W] [Fintype Var] [DecidableEq Domain]

/-- **Modal pairing** `R(wᵢ)[gᵢ]`: pair each accessible world with the
    assignment of the original index. Used in modal evaluation
    ([aloni-vanormondt-2023] Definition 4.9). -/
def State.modalLift (X : Finset W) (g : PartialAssign Var Domain) :
    Finset (Index W Var Domain) :=
  X.image (fun v => (v, g))

@[simp] theorem State.mem_modalLift {X : Finset W} {g : PartialAssign Var Domain}
    {i : Index W Var Domain} :
    i ∈ State.modalLift X g ↔ i.world ∈ X ∧ i.assign = g := by
  constructor
  · intro h
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
    exact ⟨hv, rfl⟩
  · rintro ⟨h, rfl⟩
    exact Finset.mem_image.mpr ⟨i.world, h, rfl⟩

@[simp] theorem State.modalLift_singleton (w : W)
    (g : PartialAssign Var Domain) :
    State.modalLift {w} g = {(w, g)} :=
  Finset.image_singleton ..

@[simp] theorem State.worldProj_modalLift (X : Finset W)
    (g : PartialAssign Var Domain) :
    State.worldProj (State.modalLift X g) = X := by
  ext w
  simp only [State.mem_worldProj, State.mem_modalLift]
  constructor
  · rintro ⟨i, ⟨hX, -⟩, rfl⟩
    exact hX
  · exact fun hw => ⟨(w, g), ⟨hw, rfl⟩, rfl⟩

theorem State.modalLift_worldProj_of_subset {s : Finset (Index W Var Domain)}
    {X : Finset W} {g : PartialAssign Var Domain}
    (h : s ⊆ State.modalLift X g) :
    State.modalLift (State.worldProj s) g = s := by
  ext i
  simp only [State.mem_modalLift, State.mem_worldProj]
  constructor
  · rintro ⟨⟨j, hjs, hjw⟩, hig⟩
    have : i = j :=
      Prod.ext hjw.symm (hig.trans (State.mem_modalLift.mp (h hjs)).2.symm)
    exact this ▸ hjs
  · intro his
    exact ⟨⟨i, his, rfl⟩, (State.mem_modalLift.mp (h his)).2⟩

theorem State.worldProj_subset_of_subset_modalLift
    {s : Finset (Index W Var Domain)} {X : Finset W}
    {g : PartialAssign Var Domain} (h : s ⊆ State.modalLift X g) :
    State.worldProj s ⊆ X := by
  rw [← State.worldProj_modalLift X g]
  exact State.worldProj_mono h

end ModalLift

/-! ### The formula language -/

variable {Const Pred : Type*}

/-- QBSML formula language ([aloni-vanormondt-2023] Definition 4.1),
    parameterized over variable type `Var`, constant type `Const`, and
    (monadic) predicate type `Pred`. The paper's terms `t := c | x` appear
    as the two atom constructors. `□` is not primitive — see
    `Formula.nec`. -/
inductive Formula (Var : Type*) (Const : Type*) (Pred : Type*) where
  /-- Monadic predicate applied to a variable. -/
  | pred : Pred → Var → Formula Var Const Pred
  /-- Monadic predicate applied to an individual constant. -/
  | predc : Pred → Const → Formula Var Const Pred
  /-- Non-emptiness atom: state is non-empty. -/
  | ne : Formula Var Const Pred
  /-- Bilateral negation: swap support/anti-support. -/
  | neg : Formula Var Const Pred → Formula Var Const Pred
  /-- Conjunction. -/
  | conj : Formula Var Const Pred → Formula Var Const Pred →
      Formula Var Const Pred
  /-- Split (tensor) disjunction. -/
  | disj : Formula Var Const Pred → Formula Var Const Pred →
      Formula Var Const Pred
  /-- Possibility modal. -/
  | poss : Formula Var Const Pred → Formula Var Const Pred
  /-- Existential quantifier. -/
  | exi : Var → Formula Var Const Pred → Formula Var Const Pred
  /-- Universal quantifier. -/
  | univ : Var → Formula Var Const Pred → Formula Var Const Pred
  deriving Repr

/-- Necessity, derived: `□φ := ¬◇¬φ`. [aloni-vanormondt-2023] takes `□`
    primitive and `◇ := ¬□¬` derived; we invert this, so `eval`'s `poss`
    clauses match the paper's derived `◇`-clauses and `nec` matches its
    primitive `□`. -/
def Formula.nec (φ : Formula Var Const Pred) : Formula Var Const Pred :=
  .neg (.poss (.neg φ))

/-- The NE-free fragment: formulas not containing the `NE` atom. On this
    fragment QBSML reduces to classical first-order modal logic
    ([aloni-vanormondt-2023] analogue of [anttila-2021]
    Proposition 2.2.16); see `Logic/Team/QBSML/Properties.lean`. -/
inductive Formula.NEFree : Formula Var Const Pred → Prop
  | pred (P : Pred) (x : Var) : NEFree (.pred P x)
  | predc (P : Pred) (c : Const) : NEFree (.predc P c)
  | neg {φ : Formula Var Const Pred} : NEFree φ → NEFree (.neg φ)
  | conj {φ ψ : Formula Var Const Pred} :
      NEFree φ → NEFree ψ → NEFree (.conj φ ψ)
  | disj {φ ψ : Formula Var Const Pred} :
      NEFree φ → NEFree ψ → NEFree (.disj φ ψ)
  | poss {φ : Formula Var Const Pred} : NEFree φ → NEFree (.poss φ)
  | exi (x : Var) {φ : Formula Var Const Pred} : NEFree φ → NEFree (.exi x φ)
  | univ (x : Var) {φ : Formula Var Const Pred} : NEFree φ → NEFree (.univ x φ)

/-- The derived `□φ := ¬◇¬φ` preserves NE-freeness. -/
theorem Formula.NEFree.nec {φ : Formula Var Const Pred}
    (h : φ.NEFree) : φ.nec.NEFree :=
  .neg (.poss (.neg h))

/-! ### Atom substitution -/

/-- Substitute a formula for each atom, commuting with every connective and
    quantifier (and fixing `NE`). The generic congruence machinery for
    atom-rewriting operations: an atom map whose images are bilaterally
    equivalent to the atoms is *salva veritate* (`eval_mapAtoms_iff` in
    `Logic/Team/QBSML/Properties.lean`), so each such operation — e.g.
    [yan-2023]'s reinterpretation function in `Studies/Yan2023.lean` — needs
    only its two atom lemmas. -/
def Formula.mapAtoms
    (fp : Pred → Var → Formula Var Const Pred)
    (fc : Pred → Const → Formula Var Const Pred) :
    Formula Var Const Pred → Formula Var Const Pred
  | .pred P x => fp P x
  | .predc P c => fc P c
  | .ne => .ne
  | .neg φ => .neg (φ.mapAtoms fp fc)
  | .conj φ ψ => .conj (φ.mapAtoms fp fc) (ψ.mapAtoms fp fc)
  | .disj φ ψ => .disj (φ.mapAtoms fp fc) (ψ.mapAtoms fp fc)
  | .poss φ => .poss (φ.mapAtoms fp fc)
  | .exi x φ => .exi x (φ.mapAtoms fp fc)
  | .univ x φ => .univ x (φ.mapAtoms fp fc)

theorem Formula.NEFree.mapAtoms
    {fp : Pred → Var → Formula Var Const Pred}
    {fc : Pred → Const → Formula Var Const Pred}
    (hfp : ∀ P x, (fp P x).NEFree) (hfc : ∀ P c, (fc P c).NEFree)
    {φ : Formula Var Const Pred} (h : φ.NEFree) :
    (φ.mapAtoms fp fc).NEFree := by
  induction h with
  | pred P x => exact hfp P x
  | predc P c => exact hfc P c
  | neg _ ih => exact .neg ih
  | conj _ _ ih₁ ih₂ => exact .conj ih₁ ih₂
  | disj _ _ ih₁ ih₂ => exact .disj ih₁ ih₂
  | poss _ ih => exact .poss ih
  | exi x _ ih => exact .exi x ih
  | univ x _ ih => exact .univ x ih

/-! ### Models -/

/-- A QBSML model ([aloni-vanormondt-2023] Definition 4.2:
    `M = ⟨W, D, R, I⟩`) **is** a constant-domain first-order Kripke
    structure over the monadic signature with constants: accessibility `R`
    plus the world-indexed interpretation `I`, carried as a family of
    mathlib structures (`FirstOrder.Language.ModalStructure`) — true by
    construction, not by bridge. -/
abbrev Model (W : Type*) (Domain : Type*) (Const : Type*)
    (Pred : Type*) :=
  FirstOrder.Language.ModalStructure ((Language.monadic Pred)[[Const]]) W Domain

/-- The unary relation symbol of the predicate `P`. -/
abbrev predSymb (P : Pred) : ((Language.monadic Pred)[[Const]]).Relations 1 :=
  Sum.inl P

/-- The QBSML model with accessibility `access`, constant interpretation
    `κ`, and valuation `V`. -/
def Model.ofMonadic {W Domain Const Pred : Type*} (access : W → Finset W)
    (κ : W → Const → Domain) (V : W → Pred → Domain → Prop) :
    Model W Domain Const Pred :=
  ⟨access, fun w =>
    letI := Language.monadic.structure (V w)
    letI := Language.constantsOn.structure (κ w)
    inferInstance⟩

@[simp] theorem predInterp_ofMonadic {W Domain Const Pred : Type*}
    (access : W → Finset W) (κ : W → Const → Domain)
    (V : W → Pred → Domain → Prop) (P : Pred) (w : W) (d : Domain) :
    (Model.ofMonadic access κ V).relInterp₁ (predSymb P) w d ↔ V w P d :=
  Iff.rfl

@[simp] theorem constInterp_ofMonadic {W Domain Const Pred : Type*}
    (access : W → Finset W) (κ : W → Const → Domain)
    (V : W → Pred → Domain → Prop) (c : Const) (w : W) :
    (Model.ofMonadic access κ V).constInterp ((Language.monadic Pred).con c) w = κ w c :=
  rfl

/-! ### Bilateral evaluation -/

section Evaluation

variable [DecidableEq W] [DecidableEq Var] [Fintype Var] [DecidableEq Domain]
variable [Fintype Domain]

/-- Bilateral evaluation of QBSML formulas ([aloni-vanormondt-2023]
    Definition 4.9): `eval M true φ s` is support (`M, s ⊨ φ`),
    `eval M false φ s` anti-support (`M, s ⫤ φ`). Negation flips the
    polarity, making double-negation elimination definitional. -/
def eval (M : Model W Domain Const Pred) :
    Bool → Formula Var Const Pred → Finset (Index W Var Domain) → Prop
  | true,  .pred P x, s =>
      s ∈ Team.flat fun i ↦ ∃ d : Domain, i.assign x = ↑d ∧ M.relInterp₁ (predSymb P) i.world d
  | false, .pred P x, s =>
      s ∈ Team.flat fun i ↦ ∃ d : Domain, i.assign x = ↑d ∧ ¬ M.relInterp₁ (predSymb P) i.world d
  | true,  .predc P c, s =>
      s ∈ Team.flat fun i ↦
        M.relInterp₁ (predSymb P) i.world (M.constInterp ((Language.monadic Pred).con c) i.world)
  | false, .predc P c, s =>
      s ∈ Team.flat fun i ↦
        ¬ M.relInterp₁ (predSymb P) i.world (M.constInterp ((Language.monadic Pred).con c) i.world)
  | true,  .ne, s => s ∈ Team.ne
  | false, .ne, s => s ∈ ({∅} : Team.TeamProperty (Index W Var Domain))
  | true,  .neg ψ, s => eval M false ψ s
  | false, .neg ψ, s => eval M true ψ s
  | true,  .conj φ ψ, s => eval M true φ s ∧ eval M true ψ s
  | false, .conj φ ψ, s => s ∈ Team.tensor {t | eval M false φ t} {t | eval M false ψ t}
  | true,  .disj φ ψ, s => s ∈ Team.tensor {t | eval M true φ t} {t | eval M true ψ t}
  | false, .disj φ ψ, s => eval M false φ s ∧ eval M false ψ s
  | true,  .poss ψ, s =>
      s ∈ Team.flat fun i ↦ ∃ X : Finset W, X ⊆ M.access i.world ∧ X.Nonempty ∧
        State.modalLift X i.assign ∈ {t | eval M true ψ t}
  | false, .poss ψ, s =>
      s ∈ Team.flat fun i ↦ State.modalLift (M.access i.world) i.assign ∈ {t | eval M false ψ t}
  | true,  .univ x ψ, s => s ∈ State.univ x {t | eval M true ψ t}
  | false, .univ x ψ, s => s ∈ State.exi x {t | eval M false ψ t}
  | true,  .exi x ψ, s => s ∈ State.exi x {t | eval M true ψ t}
  | false, .exi x ψ, s => s ∈ State.univ x {t | eval M false ψ t}

/-- Support: positive evaluation. -/
abbrev support (M : Model W Domain Const Pred) (φ : Formula Var Const Pred)
    (s : Finset (Index W Var Domain)) : Prop :=
  eval M true φ s

/-- Anti-support: negative evaluation. -/
abbrev antiSupport (M : Model W Domain Const Pred) (φ : Formula Var Const Pred)
    (s : Finset (Index W Var Domain)) : Prop :=
  eval M false φ s

@[simp] lemma support_neg (M : Model W Domain Const Pred)
    (φ : Formula Var Const Pred) (s : Finset (Index W Var Domain)) :
    support M (.neg φ) s ↔ antiSupport M φ s := Iff.rfl

@[simp] lemma antiSupport_neg (M : Model W Domain Const Pred)
    (φ : Formula Var Const Pred) (s : Finset (Index W Var Domain)) :
    antiSupport M (.neg φ) s ↔ support M φ s := Iff.rfl

end Evaluation

end QBSML
