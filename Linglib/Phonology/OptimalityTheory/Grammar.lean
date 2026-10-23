module

public import Linglib.Phonology.OptimalityTheory.Antimatroid

/-!
# OT grammars: the leg-set / ERC-set / antimatroid hub

In Optimality Theory the linguistically fundamental object is not a single
ranking but a **grammar**: the set of all rankings ("legs") that yield the same
optima ([prince-2002]; [prince-smolensky-1993]). A grammar has three equivalent
faces ([merchant-riggle-2016]): a **leg set** (the satisfying rankings), an
**ERC set** (its ranking conditions), and an **antimatroid**. This file makes the
grammar a first-class type, taking the leg set as its canonical identity and
exhibiting the other two faces as views.

Taking the leg set as identity makes grammar equality decidable and dissolves the
"up to entailment" hedge that the ERC-set presentation carries: two consistent ERC
sets present the *same* grammar exactly when they have the same linear extensions
(`Grammar.ofERCs_eq_iff`). The transitive-reduction ambiguity that forces
[merchant-riggle-2016] Theorem 2 to be stated up to logical equivalence becomes
literal `Grammar` equality here.

The antimatroid face (`Grammar.toAntimatroid`) has a converse — every
full-support antimatroid is some grammar's — by [dietrich-1987]'s rooted-circuit
characterization (`ERC.toAntimatroid_ofAntimatroid`,
`ERC.satisfiedBy_ofAntimatroid_toAntimatroid_iff` in `OptimalityTheory.Antimatroid`). The
feasible family is read directly off the legs and is independent of the presenting ERC set,
since `ERC.IsFeasible` depends only on the satisfying rankings.

## Main definitions

* `Grammar n` — a realizable leg set: a `Finset (Ranking (Fin n) n)` equal to the linear
  extensions of some consistent ERC set.
* `Grammar.ofERCs` — the canonical grammar of a consistent ERC set (the ERC face,
  as a constructor).
* `Grammar.feasible` / `Grammar.toAntimatroid` — the antimatroid face.

## Main results

* `Grammar.ofERCs_eq_iff` — two consistent ERC sets present the same grammar iff
  they have the same linear extensions (the entailment quotient dissolves).
* `Grammar.feasible_ofERCs` — the antimatroid family of `ofERCs E` is `ERC.IsFeasible E`.
* `Grammar.toAntimatroid_isFeasible` — the antimatroid face's feasible sets are
  exactly the prefixes of the grammar's legs.

## Categorical structure

All the structure here is the order-theoretic specialization of category theory —
the categories are *thin* (posetal), not monoidal. `(Set (Ranking (Fin n) n), ⊆)` and
`(Set (ERC (Fin n)), ⊆)` are thin categories; `subset_models_iff` exhibits `conditions`
and `models` as a **(dual) adjunction** between them. The induced monad
`grammarClosure = models ∘ conditions` is the **idempotent closure monad**, and its
algebras — the closed objects (`IsGrammarClosed`) — are exactly the grammars: a
**reflective subcategory** of ranking-space with `grammarClosure` as the reflector.
On `Grammar n` itself this lands as a `PartialOrder` (the specificity order —
on the ERC face, definitionally containment of linear-extension sets, i.e.
entailment) with a **terminal object** (`OrderTop`, the trivial
grammar) and **binary coproducts** (`superGrammar`, the super-grammar join, with
universal property `superGrammar_le`). Binary products (meets) may be empty, so the
full complete lattice lives on the closed sets, not on `Grammar`.

## References

* [merchant-riggle-2016]
* [prince-2002]
* [prince-smolensky-1993]
-/

@[expose] public section

namespace OptimalityTheory

variable {n : ℕ}

/-! ### The grammar–condition Galois connection

The leg-set / ERC-set duality is the antitone Galois connection — the
formal-concept "polarity" ([merchant-riggle-2016]; the framing is
Birkhoff / Ganter–Wille) — induced by the satisfaction relation on
`Ord(S.Con) × ERC`. `models A` collects the rankings satisfying every condition in
`A`; `conditions R` collects the conditions satisfied by every ranking in `R`.
Grammars are exactly the closed sets `models (conditions R)`, the *extents* of
this context. -/

/-- The rankings satisfying every condition in `A` (the extent polarity). -/
def models (A : Set (ERC (Fin n))) : Set (Ranking (Fin n) n) :=
  {r | ∀ α ∈ A, ERC.SatisfiedBy r α}

/-- The conditions satisfied by every ranking in `R` (the intent polarity). -/
def conditions (R : Set (Ranking (Fin n) n)) : Set (ERC (Fin n)) :=
  {α | ∀ r ∈ R, ERC.SatisfiedBy r α}

@[simp] theorem mem_models {A : Set (ERC (Fin n))} {r : Ranking (Fin n) n} :
    r ∈ models A ↔ ∀ α ∈ A, ERC.SatisfiedBy r α := Iff.rfl

@[simp] theorem mem_conditions {R : Set (Ranking (Fin n) n)} {α : ERC (Fin n)} :
    α ∈ conditions R ↔ ∀ r ∈ R, ERC.SatisfiedBy r α := Iff.rfl

theorem subset_models_iff {A : Set (ERC (Fin n))} {R : Set (Ranking (Fin n) n)} :
    R ⊆ models A ↔ A ⊆ conditions R := by
  constructor
  · intro h α hα r hr; exact h hr α hα
  · intro h r hr α hα; exact h hα r hr

theorem models_antitone : Antitone (models : Set (ERC (Fin n)) → Set (Ranking (Fin n) n)) := by
  intro A B hAB r hr α hα; exact hr α (hAB hα)

theorem conditions_antitone :
    Antitone (conditions : Set (Ranking (Fin n) n) → Set (ERC (Fin n))) := by
  intro R S hRS α hα r hr; exact hα r (hRS hr)

/-- The closure operator on ranking-space — the **reflector** onto the grammars,
i.e. the idempotent monad `models ∘ conditions` induced by the Galois adjunction.
Its fixed points (the algebras / closed objects) are exactly the grammars. -/
def grammarClosure (R : Set (Ranking (Fin n) n)) : Set (Ranking (Fin n) n) := models (conditions R)

theorem subset_grammarClosure (R : Set (Ranking (Fin n) n)) : R ⊆ grammarClosure R := by
  intro r hr α hα; exact hα r hr

theorem grammarClosure_mono :
    Monotone (grammarClosure : Set (Ranking (Fin n) n) → Set (Ranking (Fin n) n)) :=
  fun _ _ h => models_antitone (conditions_antitone h)

theorem conditions_grammarClosure (R : Set (Ranking (Fin n) n)) :
    conditions (grammarClosure R) = conditions R :=
  le_antisymm (conditions_antitone (subset_grammarClosure R)) (subset_models_iff.mp le_rfl)

theorem grammarClosure_idem (R : Set (Ranking (Fin n) n)) :
    grammarClosure (grammarClosure R) = grammarClosure R := by
  show models (conditions (grammarClosure R)) = models (conditions R)
  rw [conditions_grammarClosure]

/-- A ranking-set is **grammar-closed** iff it equals its closure — iff it is the
models of some condition set. These are the closure monad's algebras (the closed
objects of the reflective subcategory), exactly the leg sets of grammars
(`Grammar.coe_legs_isGrammarClosed`, `Grammar.exists_grammar_of_isGrammarClosed`). -/
def IsGrammarClosed (R : Set (Ranking (Fin n) n)) : Prop := grammarClosure R = R

theorem isGrammarClosed_models (A : Set (ERC (Fin n))) : IsGrammarClosed (models A) :=
  le_antisymm (models_antitone (subset_models_iff.mp le_rfl)) (subset_grammarClosure (models A))

theorem isGrammarClosed_iff_exists_models {R : Set (Ranking (Fin n) n)} :
    IsGrammarClosed R ↔ ∃ A, R = models A :=
  ⟨fun h => ⟨conditions R, h.symm⟩, by rintro ⟨A, rfl⟩; exact isGrammarClosed_models A⟩

/-! ### The closure system: meet and the super-grammar join

The closed sets form a closure system, hence a complete lattice. The **meet** of
two grammars is the intersection of their legs (`isGrammarClosed_inter`) — conjoin
their conditions (`models_union`). The **join** is `grammarClosure (R ∪ R')`, the
smallest grammar containing both: the closure of the union of legs. This is the
*super-grammar* that coarsens a typology by unioning grammars; closing the union
is exactly what guarantees the result is again a grammar. -/

theorem models_union (A B : Set (ERC (Fin n))) : models (A ∪ B) = models A ∩ models B := by
  ext r; simp only [mem_models, Set.mem_union, or_imp, forall_and, Set.mem_inter_iff]

theorem isGrammarClosed_grammarClosure (R : Set (Ranking (Fin n) n)) :
    IsGrammarClosed (grammarClosure R) := isGrammarClosed_models _

theorem isGrammarClosed_inter {R R' : Set (Ranking (Fin n) n)}
    (hR : IsGrammarClosed R) (hR' : IsGrammarClosed R') : IsGrammarClosed (R ∩ R') := by
  refine le_antisymm (Set.subset_inter ?_ ?_) (subset_grammarClosure _)
  · exact (grammarClosure_mono Set.inter_subset_left).trans hR.le
  · exact (grammarClosure_mono Set.inter_subset_right).trans hR'.le

theorem coe_linearExtensions_eq_models (E : Finset (ERC (Fin n))) :
    (↑(ERC.linearExtensions E) : Set (Ranking (Fin n) n)) = models ↑E := by
  ext r; simp [mem_models]

/-- An OT grammar is a set of rankings realizable as the linear extensions of some consistent
ERC set ([merchant-riggle-2016]). The leg set is the grammar's canonical identity; the ERC-set
and antimatroid presentations are views. -/
structure Grammar (n : ℕ) where
  /-- The grammar's legs: the rankings that select its language's optima. -/
  legs : Finset (Ranking (Fin n) n)
  /-- Every grammar is the linear-extension set of some consistent ERC set. -/
  realizable : ∃ E : Finset (ERC (Fin n)),
    (ERC.linearExtensions E).Nonempty ∧ legs = ERC.linearExtensions E

namespace Grammar

@[ext] theorem ext {G G' : Grammar n} (h : G.legs = G'.legs) : G = G' := by
  cases G; cases G'; cases h; rfl

/-- The grammar of a consistent ERC set — the ERC face, as a constructor. -/
def ofERCs (E : Finset (ERC (Fin n))) (hcons : (ERC.linearExtensions E).Nonempty) : Grammar n where
  legs := ERC.linearExtensions E
  realizable := ⟨E, hcons, rfl⟩

@[simp] theorem legs_ofERCs (E : Finset (ERC (Fin n))) (hcons : (ERC.linearExtensions E).Nonempty) :
    (ofERCs E hcons).legs = ERC.linearExtensions E := rfl

/-- A ranking belongs to a grammar when it is one of its legs. -/
instance : Membership (Ranking (Fin n) n) (Grammar n) where
  mem G r := r ∈ G.legs

@[simp] theorem mem_iff {G : Grammar n} {r : Ranking (Fin n) n} : r ∈ G ↔ r ∈ G.legs :=
  Iff.rfl

@[simp] theorem mem_ofERCs {E : Finset (ERC (Fin n))} {hcons : (ERC.linearExtensions E).Nonempty}
    {r : Ranking (Fin n) n} :
    r ∈ ofERCs E hcons ↔ ∀ α ∈ E, ERC.SatisfiedBy r α := by
  simp [mem_iff, ofERCs]

theorem legs_nonempty (G : Grammar n) : G.legs.Nonempty := by
  obtain ⟨E, hcons, hlegs⟩ := G.realizable
  exact hlegs ▸ hcons

/-! ### The ERC face: grammar equality is mutual entailment -/

/-- **The entailment quotient dissolves at the grammar level.** Two consistent ERC
sets present the same grammar iff they have the same linear extensions — iff each
entails the other. This is why the leg set, not the ERC set, is the grammar's
identity: the "logically equivalent, not literally equal" hedge of the ERC
presentation ([merchant-riggle-2016] Theorem 2) becomes literal `Grammar`
equality. -/
theorem ofERCs_eq_iff {E E' : Finset (ERC (Fin n))}
    (h : (ERC.linearExtensions E).Nonempty) (h' : (ERC.linearExtensions E').Nonempty) :
    ofERCs E h = ofERCs E' h' ↔ ERC.linearExtensions E = ERC.linearExtensions E' :=
  ⟨congrArg legs, fun hl => ext hl⟩

/-! ### The antimatroid face -/

/-- The feasible family of a grammar consists of the top segments of its legs, read directly
off the legs and independent of any ERC presentation. -/
def feasible (G : Grammar n) (S : Set (Fin n)) : Prop :=
  ∃ r : Ranking (Fin n) n, r ∈ G.legs ∧ ∃ k : Fin (n + 1), ↑(r.take k) = S

theorem feasible_ofERCs (E : Finset (ERC (Fin n))) (hcons : (ERC.linearExtensions E).Nonempty)
    (S : Set (Fin n)) :
    (ofERCs E hcons).feasible S ↔ ERC.IsFeasible ↑E S := by
  simp only [feasible, legs_ofERCs, ERC.mem_linearExtensions, ERC.IsFeasible, Finset.mem_coe]

theorem feasible_eq_isFeasible (G : Grammar n) {E : Finset (ERC (Fin n))}
    (hlegs : G.legs = ERC.linearExtensions E) : G.feasible = ERC.IsFeasible ↑E := by
  funext S
  simp only [feasible, hlegs, ERC.mem_linearExtensions, ERC.IsFeasible, Finset.mem_coe]

theorem exists_antimatroid_feasible_eq (G : Grammar n) :
    ∃ A : Antimatroid (Fin n), A.E = Set.univ ∧ A.IsFeasible = G.feasible := by
  obtain ⟨E, hcons, hlegs⟩ := G.realizable
  exact ⟨ERC.toAntimatroid _ ((ERC.linearExtensions_nonempty_iff E).mp hcons), rfl,
    (G.feasible_eq_isFeasible hlegs).symm⟩

/-- The antimatroid face of a grammar ([merchant-riggle-2016]) has the constraints as ground set
and the top segments of the legs as feasible sets. Every grammar is an antimatroid, and the
converse rests on [dietrich-1987] (`ERC.toAntimatroid_ofAntimatroid`). The axioms transfer from
the antimatroid of any ERC set realizing the grammar (`exists_antimatroid_feasible_eq`). -/
def toAntimatroid (G : Grammar n) : Antimatroid (Fin n) where
  E := Set.univ
  IsFeasible := G.feasible
  empty_feasible := by
    obtain ⟨A, -, hA⟩ := G.exists_antimatroid_feasible_eq
    exact hA ▸ A.empty_feasible
  feasible_sub := fun _ _ => Set.subset_univ _
  ground_feasible := by
    obtain ⟨A, hE, hA⟩ := G.exists_antimatroid_feasible_eq
    exact hA ▸ hE ▸ A.ground_feasible
  augmentation := by
    obtain ⟨A, hE, hA⟩ := G.exists_antimatroid_feasible_eq
    rw [← hA, ← hE]; exact A.augmentation
  removal := by
    obtain ⟨A, -, hA⟩ := G.exists_antimatroid_feasible_eq
    exact hA ▸ A.removal
  union_closed := by
    obtain ⟨A, -, hA⟩ := G.exists_antimatroid_feasible_eq
    exact hA ▸ A.union_closed

@[simp] theorem toAntimatroid_isFeasible (G : Grammar n) (S : Set (Fin n)) :
    G.toAntimatroid.IsFeasible S ↔ G.feasible S := Iff.rfl

theorem toAntimatroid_ofERCs_isFeasible (E : Finset (ERC (Fin n)))
    (hcons : (ERC.linearExtensions E).Nonempty) (S : Set (Fin n)) :
    (ofERCs E hcons).toAntimatroid.IsFeasible S ↔
      (ERC.toAntimatroid _ ((ERC.linearExtensions_nonempty_iff E).mp hcons)).IsFeasible S := by
  rw [toAntimatroid_isFeasible, feasible_ofERCs]
  exact Iff.rfl

/-! ### Grammars are exactly the nonempty closed sets -/

theorem coe_legs_isGrammarClosed (G : Grammar n) :
    IsGrammarClosed (↑G.legs : Set (Ranking (Fin n) n)) := by
  obtain ⟨E, _, hlegs⟩ := G.realizable
  rw [hlegs, coe_linearExtensions_eq_models]
  exact isGrammarClosed_models _

theorem exists_grammar_of_isGrammarClosed {R : Set (Ranking (Fin n) n)}
    (hcl : IsGrammarClosed R) (hne : R.Nonempty) :
    ∃ G : Grammar n, (↑G.legs : Set (Ranking (Fin n) n)) = R := by
  obtain ⟨E, hAeq⟩ :
      ∃ E : Finset (ERC (Fin n)), (↑E : Set (ERC (Fin n))) = conditions R := by
    refine ⟨(Set.toFinite (conditions R)).toFinset, ?_⟩
    ext α; simp
  have hReq : (↑(ERC.linearExtensions E) : Set (Ranking (Fin n) n)) = R := by
    rw [coe_linearExtensions_eq_models, hAeq]; exact hcl
  have hcons : (ERC.linearExtensions E).Nonempty := by
    obtain ⟨r, hr⟩ := hne
    rw [← hReq] at hr
    exact ⟨r, hr⟩
  exact ⟨⟨ERC.linearExtensions E, E, hcons, rfl⟩, hReq⟩

/-! ### The specificity order: grammars as a thin category

`Grammar n` is a **poset** — a thin category — under leg-set inclusion: `G ≤ G'`
means `G` is *more specific* (fewer legs, more ranking conditions). On the ERC face
`ofERCs E h ≤ ofERCs E' h'` is definitionally
`ERC.linearExtensions E ⊆ ERC.linearExtensions E'` — the entailment order, the
order side of the Galois adjunction. `grammarClosure` is the **reflector** onto
this subcategory
(grammars are its closed objects — the algebras of the idempotent closure monad).
The **terminal object** is the trivial grammar (`OrderTop`); the **coproduct** of
two grammars is their super-grammar — the closure of the union of legs. Binary
products (meets) may be empty, so the full lattice lives on the closed sets, with
`Grammar n` the nonempty part. -/

instance : PartialOrder (Grammar n) where
  le G G' := G.legs ⊆ G'.legs
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ h h' := Finset.Subset.trans h h'
  le_antisymm _ _ h h' := ext (Finset.Subset.antisymm h h')

theorem le_iff_legs {G G' : Grammar n} : G ≤ G' ↔ G.legs ⊆ G'.legs := Iff.rfl

/-- The trivial grammar has all rankings as legs and no ranking conditions (`ofERCs ∅`); it is
the terminal object of the specificity order. -/
def trivial : Grammar n := ofERCs ∅ ⟨1, by simp⟩

@[simp] theorem legs_trivial : (Grammar.trivial : Grammar n).legs = Finset.univ := by
  simp only [Grammar.trivial, legs_ofERCs, ERC.linearExtensions_empty]

instance : OrderTop (Grammar n) where
  top := trivial
  le_top G := by rw [le_iff_legs, legs_trivial]; exact Finset.subset_univ _

theorem grammarClosure_union_nonempty (G G' : Grammar n) :
    (grammarClosure (↑G.legs ∪ ↑G'.legs : Set (Ranking (Fin n) n))).Nonempty := by
  obtain ⟨r, hr⟩ := G.legs_nonempty
  exact ⟨r, subset_grammarClosure _ (Set.mem_union_left _ (Finset.mem_coe.mpr hr))⟩

/-- The **super-grammar** (the coproduct / join in the thin category of grammars):
the least grammar containing both `G` and `G'`, the closure of the union of their
legs. This is [merchant-riggle-2016]'s typology coarsening — union the legs, then
close to land back inside `Grammar`. -/
noncomputable def superGrammar (G G' : Grammar n) : Grammar n :=
  (exists_grammar_of_isGrammarClosed (isGrammarClosed_grammarClosure _)
    (grammarClosure_union_nonempty G G')).choose

theorem coe_superGrammar_legs (G G' : Grammar n) :
    (↑(superGrammar G G').legs : Set (Ranking (Fin n) n))
      = grammarClosure (↑G.legs ∪ ↑G'.legs : Set (Ranking (Fin n) n)) :=
  (exists_grammar_of_isGrammarClosed (isGrammarClosed_grammarClosure _)
    (grammarClosure_union_nonempty G G')).choose_spec

theorem le_superGrammar_left (G G' : Grammar n) : G ≤ superGrammar G G' := by
  rw [le_iff_legs, ← Finset.coe_subset, coe_superGrammar_legs]
  exact Set.Subset.trans Set.subset_union_left (subset_grammarClosure _)

theorem le_superGrammar_right (G G' : Grammar n) : G' ≤ superGrammar G G' := by
  rw [le_iff_legs, ← Finset.coe_subset, coe_superGrammar_legs]
  exact Set.Subset.trans Set.subset_union_right (subset_grammarClosure _)

theorem superGrammar_le {G G' K : Grammar n} (hG : G ≤ K) (hG' : G' ≤ K) :
    superGrammar G G' ≤ K := by
  have hK : grammarClosure (↑K.legs : Set (Ranking (Fin n) n)) = ↑K.legs :=
    coe_legs_isGrammarClosed K
  rw [le_iff_legs, ← Finset.coe_subset, coe_superGrammar_legs]
  refine Set.Subset.trans (grammarClosure_mono (Set.union_subset ?_ ?_)) hK.subset
  · exact Finset.coe_subset.mpr (le_iff_legs.mp hG)
  · exact Finset.coe_subset.mpr (le_iff_legs.mp hG')

end Grammar

end OptimalityTheory
