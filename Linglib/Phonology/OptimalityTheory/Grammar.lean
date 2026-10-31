module

public import Linglib.Phonology.OptimalityTheory.Antimatroid

/-!
# Optimality-theoretic grammars

This file defines Optimality-theoretic grammars over a fixed set of constraints. A grammar is
identified with its legs, the rankings that satisfy it, which must be the linear extensions of
some consistent set of elementary ranking conditions; as Merchant and Riggle observe, distinct
sets of conditions can present the same grammar. Grammars are partially ordered by inclusion of
their legs, and the legs of a grammar determine an antimatroid.

## Main definitions

* `models A`, `conditions R`: the rankings satisfying every ERC in `A`, and the ERCs
  satisfied by every ranking in `R`.
* `grammarClosure R`: `models (conditions R)`, a closure operator on sets of rankings, with
  `IsGrammarClosed` for its closed sets.
* `Grammar n`: a finite set of rankings equal to the linear extensions of some consistent ERC
  set; `Grammar.ofERCs E h` is the grammar of a consistent ERC set `E`.
* `Grammar.feasible`, `Grammar.toAntimatroid`: the top segments of the legs, and the
  antimatroid they form.
* `Grammar.trivial`, `Grammar.superGrammar`: the grammar with every ranking as a leg, and the
  least grammar containing two given grammars.

## Main statements

* `subset_models_iff`: `R ⊆ models A ↔ A ⊆ conditions R`.
* `isGrammarClosed_iff_exists_models`: a set of rankings is closed iff it is `models A` for
  some `A`.
* `Grammar.ofERCs_eq_iff`: two consistent ERC sets present the same grammar iff they have the
  same linear extensions.
* `Grammar.coe_legs_isGrammarClosed`, `Grammar.exists_grammar_of_isGrammarClosed`: the leg
  sets of grammars are exactly the nonempty closed sets.
* `Grammar.feasible_ofERCs`: the feasible sets of `ofERCs E h` are those of `E`.
* `Grammar.toAntimatroid_ofERCs_isFeasible`: the antimatroid of a grammar is that of any ERC set
  presenting it.
* `Grammar.superGrammar_le`: the super-grammar of `G` and `G'` is their least upper bound.

## Implementation notes

* The presenting ERC set is an argument of `Grammar.ofERCs` rather than a field of `Grammar`,
  so that equality of grammars is equality of leg sets (`Grammar.ext`) and carries no choice
  of presentation.
* `Grammar n` carries the join of the specificity order but no meet. The intersection of two
  closed sets is closed (`isGrammarClosed_inter`), but `realizable` requires a nonempty leg
  set, and the file does not show when an intersection of leg sets is nonempty.
* The axioms of `Grammar.toAntimatroid` are transported from `ERC.toAntimatroid` of any ERC
  set realizing the grammar (`Grammar.exists_antimatroid_feasible_eq`). The converse, that
  every antimatroid on all of `Fin n` is the antimatroid of a consistent set of ERCs, is
  `ERC.toAntimatroid_ofAntimatroid`, which follows Dietrich; it is not restated for `Grammar`.

## References

* [N. Merchant, J. Riggle, *OT grammars, beyond partial orders: ERC sets and antimatroids*
  (2016)][merchant-riggle-2016]
* [B. L. Dietrich, *A circuit set characterization of antimatroids* (1987)][dietrich-1987]
-/

@[expose] public section

namespace OptimalityTheory

variable {n : ℕ}

/-! ### The Galois connection between rankings and conditions

`models A` is the set of rankings satisfying every condition in `A`, and `conditions R` is
the set of conditions satisfied by every ranking in `R`. Both maps are antitone, and together
they form a Galois connection (`subset_models_iff`), so that `models ∘ conditions` is a
closure operator on sets of rankings whose closed sets are the sets of the form `models A`. -/

/-- The rankings satisfying every condition in `A`. -/
def models (A : Set (ERC (Fin n))) : Set (Ranking (Fin n) n) :=
  {r | ∀ α ∈ A, ERC.SatisfiedBy r α}

/-- The conditions satisfied by every ranking in `R`. -/
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

/-- The closure of a set of rankings: the rankings satisfying every condition that all of `R`
satisfy. It is extensive, monotone, and idempotent (`subset_grammarClosure`,
`grammarClosure_mono`, `grammarClosure_idem`). -/
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

/-- A set of rankings is *grammar-closed* when it equals its closure, equivalently when it is
`models A` for some set of conditions `A` (`isGrammarClosed_iff_exists_models`). -/
def IsGrammarClosed (R : Set (Ranking (Fin n) n)) : Prop := grammarClosure R = R

theorem isGrammarClosed_models (A : Set (ERC (Fin n))) : IsGrammarClosed (models A) :=
  le_antisymm (models_antitone (subset_models_iff.mp le_rfl)) (subset_grammarClosure (models A))

theorem isGrammarClosed_iff_exists_models {R : Set (Ranking (Fin n) n)} :
    IsGrammarClosed R ↔ ∃ A, R = models A :=
  ⟨fun h => ⟨conditions R, h.symm⟩, by rintro ⟨A, rfl⟩; exact isGrammarClosed_models A⟩

/-! ### Intersections and closures of unions

The intersection of two closed sets is closed (`isGrammarClosed_inter`), and the rankings
satisfying the union of two condition sets are those satisfying both (`models_union`). The
closure of a union of two sets is a closed set containing both (`isGrammarClosed_grammarClosure`,
`subset_grammarClosure`); among grammars it is the least such (`Grammar.superGrammar_le`). -/

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

/-- An *Optimality-theoretic grammar* over `n` constraints: a set of rankings that is the set of
linear extensions of some consistent set of ERCs. Two grammars are equal when their rankings
are (`Grammar.ext`), whichever ERC sets present them. -/
structure Grammar (n : ℕ) where
  /-- The rankings of the grammar. -/
  legs : Finset (Ranking (Fin n) n)
  /-- The legs are the linear extensions of some consistent set of ERCs. -/
  realizable : ∃ E : Finset (ERC (Fin n)),
    (ERC.linearExtensions E).Nonempty ∧ legs = ERC.linearExtensions E

namespace Grammar

@[ext] theorem ext {G G' : Grammar n} (h : G.legs = G'.legs) : G = G' := by
  cases G; cases G'; cases h; rfl

/-- The grammar whose legs are the linear extensions of a consistent set of ERCs `E`. -/
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

/-! ### Grammars presented by sets of ERCs -/

/-- Two consistent sets of ERCs present the same grammar iff they have the same linear
extensions. -/
theorem ofERCs_eq_iff {E E' : Finset (ERC (Fin n))}
    (h : (ERC.linearExtensions E).Nonempty) (h' : (ERC.linearExtensions E').Nonempty) :
    ofERCs E h = ofERCs E' h' ↔ ERC.linearExtensions E = ERC.linearExtensions E' :=
  ⟨congrArg legs, fun hl => ext hl⟩

/-! ### The antimatroid of a grammar -/

/-- A set of constraints is *feasible* for a grammar when it is the set of the top `k`
constraints of one of its legs. -/
def feasible (G : Grammar n) (S : Set (Fin n)) : Prop :=
  ∃ r : Ranking (Fin n) n, r ∈ G.legs ∧ ∃ k : Fin (n + 1), ↑(r.take k) = S

/-- The feasible sets of `ofERCs E hcons` are the feasible sets of `E`. -/
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

/-- The antimatroid of a grammar has the constraints as ground set and the feasible sets of the
grammar as feasible sets. Its axioms are those of `ERC.toAntimatroid` for any set of ERCs
presenting the grammar (`exists_antimatroid_feasible_eq`). -/
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

/-! ### Leg sets are the nonempty closed sets -/

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

/-! ### The specificity order

Grammars are ordered by inclusion of leg sets (`le_iff_legs`): `G ≤ G'` when every leg of
`G` is a leg of `G'`, so that `G` satisfies every condition that `G'` satisfies
(`conditions_antitone`). For grammars presented by sets of ERCs this is inclusion of their
linear extensions. The trivial grammar is the greatest element, and the super-grammar of two
grammars is their least upper bound. -/

instance : PartialOrder (Grammar n) where
  le G G' := G.legs ⊆ G'.legs
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ h h' := Finset.Subset.trans h h'
  le_antisymm _ _ h h' := ext (Finset.Subset.antisymm h h')

theorem le_iff_legs {G G' : Grammar n} : G ≤ G' ↔ G.legs ⊆ G'.legs := Iff.rfl

/-- The *trivial grammar*, `ofERCs ∅`, has every ranking as a leg (`legs_trivial`) and is the
greatest element of the specificity order. -/
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

/-- The *super-grammar* of `G` and `G'`: the grammar whose legs are the closure of the union of
their legs (`coe_superGrammar_legs`). It is the least upper bound of `G` and `G'` in the
specificity order (`le_superGrammar_left`, `le_superGrammar_right`, `superGrammar_le`). -/
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
