module

public import Studies.GroenendijkStokhof1991

/-!
# Charlow (2019): Where is the destructive update problem?

This file formalizes [charlow-2019], "Where is the destructive update problem?", which argues
that overwriting the value an assignment gives a variable is not a problem peculiar to dynamic
semantics. In the dynamic system of [groenendijk-stokhof-1991] two indefinites with the same
index leave only the second as a discourse referent, the first update being destroyed, at no
cost to truth conditions. The static system overwrites assignments in the same way: a
superscripted expression is a scope-taker that evaluates its scope at a shifted assignment, and
the two systems differ only in the operator `↑` that closes off the part of a sentence that does
not care about assignments, the static one discarding the shifted assignment and the dynamic one
returning it. The dynamic `↑` is the test of the static one, so the two agree on truth.

What destructive update does cost is antisymmetry: an assignment reachable from another by some
formula reaches it back, reachability being the relation of differing at finitely many
variables. That is a problem only for a negation defined by descent along an order on points.
Over states of world-assignment pairs, the negation that tests each point is distributive
whatever its prejacent, which collapses negated possibility and negated necessity, and the one
that removes the surviving points fails once points are modified. Processing a state cell by
cell, a cell being its points with one assignment, gives a possibility modal and a negation that
are distributive over assignments and not over worlds, and the negation is the pointwise one on
the updates that only change assignments.

## Main definitions

* `sup`, `pro`, `upStatic`, `upDynamic`: the superscript, the pronoun, and the two operators `↑`.
* `reachable`: reachability of an assignment from another by a formula.
* `distNeg`, `descNeg`: the pointwise negation and the negation by descent.
* `Part`, `slice`, `IsAnaphoricallyDistributive`, `anaMight`, `anaNeg`: the cells of a state,
  processing a state cell by cell, and the possibility modal and negation defined that way.

## Main results

* `mem_indefinites_iff`: the second of two coindexed indefinites overwrites the first.
* `upDynamic_eq_test`, `nonempty_upDynamic_iff`: the dynamic `↑` is the test of the static one.
* `pollyAnnaStatic_eq`, `pollyAnnaDynamic_eq`: the static and the dynamic meaning of a sentence
  with two names competing for one index.
* `reachable_iff_finite`, `reachable_symm`, `antisymmetry_fails`: reachability is differing at
  finitely many variables, so it is symmetric and no partial order.
* `isDistributive_distNeg`, `distNeg_might_eq_distNeg_must`: the pointwise negation is
  distributive and conflates the two modals.
* `isAnaphoricallyDistributive_slice`, `not_isDistributive_anaMight`, `anaNeg_image`: slicing is
  distributive over assignments only, and its negation is pointwise on anaphoric updates.

## Implementation notes

A dynamic proposition is an `Update (Assignment E)`, the paper's functions from assignments to
sets of assignments uncurried; the operators of the modular analysis are stated in the paper's
curried form, with `upDynamic_eq_test` relating the two. The paper's cells are the maximal
subsets of a state with one assignment, which are the nonempty fibres of the projection to
assignments. Descent needs an order on assignments, which total assignments do not have, so
`descNeg` is stated over any preordered type of anaphoric contexts.

## References

* [charlow-2019]
* [groenendijk-stokhof-1991]
-/

@[expose] public section

namespace Charlow2019

open DynamicSemantics DynamicSemantics.Update SetRel

/-! ### Destructive update, sections 3 and 4 -/

section DestructiveUpdate

variable {E : Type*} {P Q : E → Prop} {g h : Assignment E}

/-- *A linguist⁶ entered the room. A linguist⁶ was already there*: the outputs map the index to
a witness of the second indefinite, the value the first gave it being overwritten. -/
theorem mem_indefinites_iff (n : ℕ) :
    g ~[dexists n (test {k | P (k n)}) ○ dexists n (test {k | Q (k n)})] h ↔
      (∃ x, P x) ∧ ∃ y, Q y ∧ h = Function.update g n y := by
  constructor
  · rintro ⟨_, ⟨_, ⟨x, rfl⟩, rfl, hP⟩, _, ⟨y, rfl⟩, rfl, hQ⟩
    exact ⟨⟨x, by simpa using hP⟩, y, by simpa using hQ, Function.update_idem ..⟩
  · rintro ⟨⟨x, hP⟩, y, hQ, rfl⟩
    exact ⟨_, ⟨_, ⟨x, rfl⟩, rfl, by simpa using hP⟩, _, ⟨y, rfl⟩, by simp, by simpa using hQ⟩

theorem mem_dom_indefinites_iff (n : ℕ) :
    g ∈ (dexists n (test {k | P (k n)}) ○ dexists n (test {k | Q (k n)})).dom ↔
      (∃ x, P x) ∧ ∃ y, Q y :=
  ⟨fun ⟨_, hh⟩ ↦ let ⟨hP, y, hQ, _⟩ := (mem_indefinites_iff n).mp hh; ⟨hP, y, hQ⟩,
    fun ⟨hP, y, hQ⟩ ↦ ⟨_, (mem_indefinites_iff n).mpr ⟨hP, y, hQ, rfl⟩⟩⟩

end DestructiveUpdate

/-! ### The static/dynamic divide, section 7

A logical form is cleaved at `↑`: below it nothing looks at the assignment, above it
superscripted expressions shift the assignment and pronouns read it. The shifting is the same
in the static and the dynamic system. -/

section Divide

variable {E ρ : Type*}

/-- A superscripted individual is a scope-taker that evaluates its scope at the assignment
shifted to map its index to it. -/
def sup (n : ℕ) (x : E) (c : E → Assignment E → ρ) : Assignment E → ρ :=
  fun g ↦ c x (Function.update g n x)

/-- A pronoun passes the value of its index to its scope (18). -/
def pro (n : ℕ) (c : E → Assignment E → ρ) : Assignment E → ρ :=
  fun g ↦ c (g n) g

/-- The static `↑` returns the truth value and drops the assignment. -/
def upStatic (p : Prop) : Assignment E → Prop :=
  fun _ ↦ p

/-- The dynamic `↑` returns the assignment, conditional on the truth value. -/
def upDynamic (p : Prop) : Assignment E → Set (Assignment E) :=
  fun g ↦ {h | h = g ∧ p}

/-- The dynamic `↑` is the test of the static one. -/
theorem upDynamic_eq_test (p : Prop) :
    {i : Assignment E × Assignment E | i.2 ∈ upDynamic p i.1} = test {g | upStatic p g} := by
  ext ⟨g, h⟩
  exact ⟨fun ⟨hgh, hp⟩ ↦ ⟨hgh.symm, hp⟩, fun ⟨hgh, hp⟩ ↦ ⟨hgh.symm, hp⟩⟩

/-- A dynamic proposition built with `↑` is true where the static one is. -/
theorem nonempty_upDynamic_iff (p : Prop) (g : Assignment E) :
    (upDynamic p g).Nonempty ↔ upStatic p g :=
  ⟨fun ⟨_, _, hp⟩ ↦ hp, fun hp ↦ ⟨g, rfl, hp⟩⟩

variable (gave : E → E → E → Prop) (polly anna : E)

/-- *Polly⁵ gave Anna⁵ her₅ paper* (20), statically: `gave x y z` says `x` gave `y` the paper of
`z`. -/
def pollyAnnaStatic : Assignment E → Prop :=
  sup 5 polly fun x ↦ sup 5 anna fun y ↦ pro 5 fun z ↦ upStatic (gave x y z)

/-- *Polly⁵ gave Anna⁵ her₅ paper* (20), dynamically. -/
def pollyAnnaDynamic : Assignment E → Set (Assignment E) :=
  sup 5 polly fun x ↦ sup 5 anna fun y ↦ pro 5 fun z ↦ upDynamic (gave x y z)

/-- The static meaning (22): the pronoun is Anna, and the shifted assignment is gone. -/
theorem pollyAnnaStatic_eq :
    pollyAnnaStatic gave polly anna = fun _ ↦ gave polly anna anna := by
  funext g
  simp [pollyAnnaStatic, sup, pro, upStatic]

/-- The dynamic meaning (23): the same truth condition, with the doubly shifted assignment
returned, in which Polly's update is overwritten by Anna's. -/
theorem pollyAnnaDynamic_eq (g : Assignment E) :
    pollyAnnaDynamic gave polly anna g =
      {h | h = Function.update g 5 anna ∧ gave polly anna anna} := by
  simp [pollyAnnaDynamic, sup, pro, upDynamic]

end Divide

/-! ### Antisymmetry, section 8 -/

section Reachability

open FirstOrder DPL DPL.Formula

variable {L : Language} {E : Type*} [L.Structure E] {g h k : Assignment E}

variable (L) in
/-- An assignment is reachable from another when some formula of dynamic predicate logic takes
the one to the other (24). -/
def reachable (g h : Assignment E) : Prop :=
  ∃ φ : Formula L ℕ, g ~[φ.eval E] h

theorem reachable_refl (g : Assignment E) : reachable L g g :=
  ⟨.top, rfl⟩

theorem reachable_trans (hgh : reachable L g h) (hhk : reachable L h k) : reachable L g k := by
  obtain ⟨φ, hφ⟩ := hgh
  obtain ⟨ψ, hψ⟩ := hhk
  exact ⟨φ ⋏ ψ, h, hφ, hψ⟩

/-- The assignments reachable from one another are those that differ at finitely many
variables: a formula changes only its active quantifier variables, and resetting the variables
where two assignments differ takes the one to the other. -/
theorem reachable_iff_finite : reachable L g h ↔ {x | g x ≠ h x}.Finite := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine φ.aqv.finite_toSet.subset fun x hx ↦ ?_
    by_contra hxφ
    exact hx (GroenendijkStokhof1991.eqOn_of_eval hφ hxφ)
  · intro hfin
    refine ⟨exs hfin.toFinset.toList .top, (mem_eval_exs E _).mpr ⟨h, fun y hy ↦ ?_, rfl⟩⟩
    by_contra hne
    exact hy (by simpa using fun heq ↦ hne heq.symm)

/-- Reachability is symmetric, so it is a partial order only if it is trivial. -/
theorem reachable_symm (hgh : reachable L g h) : reachable L h g := by
  rw [reachable_iff_finite] at hgh ⊢
  simpa only [ne_comm] using hgh

/-- Antisymmetry fails: distinct assignments are reachable from one another, an overwritten
variable being overwritten again with its old value. -/
theorem antisymmetry_fails [Nontrivial E] :
    ∃ g h : Assignment E, g ≠ h ∧ reachable L g h ∧ reachable L h g := by
  obtain ⟨e₁, e₂, hne⟩ := exists_pair_ne E
  have hr : reachable L (fun _ ↦ e₁) (Function.update (fun _ ↦ e₁) 0 e₂) :=
    ⟨∃[0] .top, mem_dexists.mpr ⟨e₂, rfl⟩⟩
  exact ⟨_, _, fun heq ↦ hne (by simpa using congr_fun heq 0), hr, reachable_symm hr⟩

end Reachability

/-! ### Negation and distributivity

Over states, the possibility modal is the substrate's `CCP.might`, which is not distributive
(`CCP.might_not_isDistributive`), and the negation (28) that removes the surviving points is
`CCP.neg`. -/

section Negation

variable {S : Type*} {φ : CCP S} {s : Set S}

/-- The pointwise negation (29) keeps the points whose singleton the prejacent rejects. -/
def distNeg (φ : CCP S) : CCP S :=
  fun s ↦ {i ∈ s | φ {i} = ∅}

theorem distNeg_eq_image (φ : CCP S) : distNeg φ = (test (Update.neg (CCP.lower φ))).image := by
  funext s
  rw [image_test]
  ext i
  simp [distNeg, Set.eq_empty_iff_forall_notMem]

/-- The pointwise negation is distributive, whatever its prejacent. -/
theorem isDistributive_distNeg (φ : CCP S) : CCP.IsDistributive (distNeg φ) :=
  distNeg_eq_image φ ▸ image_isDistributive _

theorem neg_might_of_nonempty (h : (φ s).Nonempty) : CCP.neg (CCP.might φ) s = ∅ := by
  simp [CCP.neg, CCP.might, CCP.guard_pos (C := fun s ↦ (φ s).Nonempty) h]

theorem neg_might_of_eq_empty (h : φ s = ∅) : CCP.neg (CCP.might φ) s = s := by
  simp [CCP.neg, CCP.might, CCP.guard_neg (C := fun s ↦ (φ s).Nonempty) (s := s) (by simp [h])]

theorem neg_eq_self_of_disjoint (h : Disjoint s (φ s)) : CCP.neg φ s = s :=
  sdiff_eq_left.mpr h

/-- The pointwise negation conflates negated possibility and negated necessity: on an
eliminative prejacent both keep the points the prejacent rejects. -/
theorem distNeg_might_eq_distNeg_must (hφ : CCP.IsEliminative φ) :
    distNeg (CCP.might φ) = distNeg (CCP.must φ) := by
  funext s
  ext i
  have hsub : φ {i} ⊆ {i} := hφ {i}
  have key : CCP.might φ {i} = ∅ ↔ CCP.must φ {i} = ∅ := by
    rcases Set.subset_singleton_iff_eq.mp hsub with h | h <;>
      simp [CCP.might, CCP.must, CCP.guard, h, Set.eq_empty_iff_forall_notMem]
  simp only [distNeg, Set.mem_ofPred_eq, key]

end Negation

/-! ### Descent and slicing

A state is a set of points, pairs of a world and an anaphoric context. -/

section States

variable {W A : Type*} {s : Set (W × A)}

/-- The negation by descent (33) removes the points with a descendant among the outputs, a
descendant (34) having the same world and an anaphoric context above. -/
def descNeg [Preorder A] (φ : CCP (W × A)) : CCP (W × A) :=
  fun s ↦ {i ∈ s | ¬∃ i' ∈ φ s, i.1 = i'.1 ∧ i.2 ≤ i'.2}

theorem descNeg_subset_neg [Preorder A] (φ : CCP (W × A)) (s : Set (W × A)) :
    descNeg φ s ⊆ CCP.neg φ s :=
  fun i ⟨hi, hno⟩ ↦ ⟨hi, fun hφ ↦ hno ⟨i, hφ, rfl, le_rfl⟩⟩

theorem descNeg_image_subset [Preorder A] {D : Update (W × A)}
    (hD : ∀ ⦃i j⦄, i ~[D] j → i.1 = j.1 ∧ i.2 ≤ j.2) (s : Set (W × A)) :
    descNeg D.image s ⊆ s \ D.dom :=
  fun i ⟨hi, hno⟩ ↦ ⟨hi, fun ⟨j, hij⟩ ↦ hno ⟨j, ⟨i, hi, hij⟩, hD hij⟩⟩

/-- The cells of a state (35): its nonempty sets of points with one anaphoric context. -/
def Part (s : Set (W × A)) : Set (Set (W × A)) :=
  {t | t.Nonempty ∧ ∃ g, t = {i ∈ s | i.2 = g}}

/-- Slicing processes a state cell by cell. -/
def slice (ψ : CCP (W × A)) : CCP (W × A) :=
  fun s ↦ ⋃ t ∈ Part s, ψ t

/-- A transformer is anaphorically distributive (39) when it processes a state cell by
cell. -/
def IsAnaphoricallyDistributive (φ : CCP (W × A)) : Prop :=
  slice φ = φ

theorem subset_of_mem_part {t : Set (W × A)} (ht : t ∈ Part s) : t ⊆ s := by
  obtain ⟨-, g, rfl⟩ := ht
  exact Set.sep_subset _ _

theorem mem_part_of_mem {i : W × A} (hi : i ∈ s) : {j ∈ s | j.2 = i.2} ∈ Part s :=
  ⟨⟨i, hi, rfl⟩, i.2, rfl⟩

theorem part_of_mem_part {t : Set (W × A)} (ht : t ∈ Part s) : Part t = {t} := by
  obtain ⟨⟨i, hi⟩, g, rfl⟩ := ht
  ext u
  constructor
  · rintro ⟨⟨j, hj⟩, g', rfl⟩
    obtain rfl : g' = g := hj.2.symm.trans hj.1.2
    exact Set.ext fun k ↦ ⟨fun hk ↦ hk.1, fun hk ↦ ⟨hk, hk.2⟩⟩
  · rintro rfl
    exact ⟨⟨i, hi⟩, g, Set.ext fun k ↦ ⟨fun hk ↦ ⟨hk, hk.2⟩, fun hk ↦ hk.1⟩⟩

/-- Slicing is anaphorically distributive. -/
theorem isAnaphoricallyDistributive_slice (ψ : CCP (W × A)) :
    IsAnaphoricallyDistributive (slice ψ) := by
  funext s
  ext p
  simp only [slice, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨t, ht, u, hu, hp⟩
    rw [part_of_mem_part ht] at hu
    exact ⟨t, ht, hu ▸ hp⟩
  · rintro ⟨t, ht, hp⟩
    exact ⟨t, ht, t, by rw [part_of_mem_part ht]; rfl, hp⟩

theorem _root_.DynamicSemantics.CCP.IsDistributive.isAnaphoricallyDistributive
    {φ : CCP (W × A)} (hφ : CCP.IsDistributive φ) : IsAnaphoricallyDistributive φ := by
  funext s
  ext p
  simp only [slice, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨t, ht, hp⟩
    rw [hφ t] at hp
    obtain ⟨i, hi, hpi⟩ := hp
    rw [hφ s]
    exact ⟨i, subset_of_mem_part ht hi, hpi⟩
  · intro hp
    rw [hφ s] at hp
    obtain ⟨i, hi, hpi⟩ := hp
    refine ⟨_, mem_part_of_mem hi, ?_⟩
    rw [hφ]
    exact ⟨i, ⟨hi, rfl⟩, hpi⟩

/-- The possibility modal that tests each cell (36). -/
def anaMight (φ : CCP (W × A)) : CCP (W × A) :=
  slice (CCP.might φ)

/-- The negation that removes from each cell the points whose world survives in its update
(37), sameness of world (38) standing in for descent. -/
def anaNeg (φ : CCP (W × A)) : CCP (W × A) :=
  slice fun t ↦ {i ∈ t | ¬∃ i' ∈ φ t, i'.1 = i.1}

/-- The sliced modal is not distributive (40): with one anaphoric context and two worlds, one of
which verifies the prejacent, it keeps both points, and point by point it keeps one. -/
theorem not_isDistributive_anaMight :
    ∃ (W A : Type) (φ : CCP (W × A)), ¬CCP.IsDistributive (anaMight φ) := by
  refine ⟨Bool, Unit, CCP.up {i | i.1 = true}, fun hD ↦ ?_⟩
  have hmem : ((false, ()) : Bool × Unit) ∈
      anaMight (CCP.up {i | i.1 = true}) {(true, ()), (false, ())} := by
    refine Set.mem_iUnion₂.mpr ⟨_, mem_part_of_mem (i := (true, ())) (Or.inl rfl), ?_⟩
    exact ⟨⟨Or.inr rfl, rfl⟩, (true, ()), ⟨Or.inl rfl, rfl⟩, rfl⟩
  rw [hD] at hmem
  obtain ⟨i, -, hi⟩ := hmem
  obtain ⟨t, ht, hft, j, hjt, hj⟩ := Set.mem_iUnion₂.mp hi
  have hsub := subset_of_mem_part ht
  obtain rfl : j = (false, ()) := (hsub hjt).trans (hsub hft).symm
  exact Bool.false_ne_true hj

/-- On an update that only changes the anaphoric context, the sliced negation is the pointwise
one: within a cell a world identifies its point, so a surviving world is a surviving point. -/
theorem anaNeg_image {D : Update (W × A)} (hD : ∀ ⦃i j⦄, i ~[D] j → i.1 = j.1)
    (s : Set (W × A)) : anaNeg D.image s = s \ D.dom := by
  ext i
  simp only [anaNeg, slice, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨t, ht, hit, hno⟩
    exact ⟨subset_of_mem_part ht hit, fun ⟨j, hij⟩ ↦ hno ⟨j, ⟨i, hit, hij⟩, (hD hij).symm⟩⟩
  · rintro ⟨his, hno⟩
    refine ⟨_, mem_part_of_mem his, ⟨his, rfl⟩, ?_⟩
    rintro ⟨i', ⟨j, ⟨-, hj⟩, hji'⟩, hw⟩
    obtain rfl : j = i := Prod.ext ((hD hji').trans hw) hj
    exact hno ⟨i', hji'⟩

end States

end Charlow2019
