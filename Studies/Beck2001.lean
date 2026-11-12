module

public import Linglib.Data.Examples.Beck2001
public import Linglib.Data.Examples.Readers
public import Linglib.Semantics.Homogeneity.Plural
public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Semantics.Quantification.Defs
public import Linglib.Semantics.Reference.Iota
public import Mathlib.Order.SuccPred.Fin
public import Mathlib.Order.SuccPred.Relation
public import Studies.HeimLasnikMay1991
public import Studies.Sternefeld1998

/-!
# Beck (2001): Reciprocals are definites

This file formalizes the analysis of *each other* as a plural definite, *the other ones among
them*: [the largest sum of cover cells in its range that do not overlap its
contrast](##eachOther). A reciprocal sentence is a [relational plural](##cumulatedReading), and
$*$, $**$ and $***$ are [one operator on partial predicates](##pluralize), whose placement derives
four readings: [collective](##collectiveReading_eq_true_iff), [strong](##strongReading_eq_true_iff),
[weak](##weakReading_eq_true_iff) and
[situation-based weak](##situationWeakReading_eq_true_iff). The weak reading
[presupposes a plural antecedent](##weakReading_eq_undefined_iff), and its distinctness
[projects past any quantifier in the relation](##pluralize_partialScope_eq_weakReading), where
asserted distinctness [is trivial or idle](##inSitu_dichotomy).

## Implementation notes

* Pluralities are finite sets and an individual is its singleton, as in `Studies/Sternefeld1998`.
  The singular cover is `Mereology.Atom`, on which only a relation's values at singletons matter.
* A sentence denotes a `Trivalent`, and a definite in a predicate's scope goes
  through `Presupposition.presupOfReferent`.
* `Reciprocal.StrongReciprocity` asserts the plurality the strong reading presupposes, and
  `Reciprocal.WeakReciprocity` holds vacuously of the empty set, which `**` excludes.
* A situation is a finite set of the cells of its division, the case in which the closure and the
  coverage form of `***` agree. The paper gives (153) no situation analysis; `AdjacentAt` extends
  (181) to a circle.
* (115) and (225) are different trivalent operators: on a sum with a true and a false part
  `pluralize` is false and `Homogeneity.barePlural` undefined. The paper tries (225) only for
  section 6.4 and does not reconcile them.

## TODO

* Non-singular covers beyond minimal covers: subgroup readings (89), (91), (92) and (130) to (133),
  where non-overlap and non-identity come apart.
* The exception readings as closure at the covered part of the antecedent, which repairs (130a).
* The contextual definite (155a), (165) to (170); Partitioned Strong Reciprocity from situations
  (190) to (192); the scope facts (207) to (214); the cumulative homogeneity of (228).
* The Strongest Meaning Hypothesis over (219): footnote 15's split relation has Strong but not
  situation-based Weak Reciprocity, so the hypothesis can rank the two only with the support
  condition in the context.

## References

* [beck-2001]
* [heim-lasnik-may-1991]
* [sternefeld-1998]
* [sauerland-1998]
* [dalrymple-et-al-1998]
* [langendoen-1978]
* [fiengo-lasnik-1973]
* [kanski-1987]
* [schwarzschild-1996]
* [brisson-1998]
* [kratzer-1989]
* [sharvy-1980]
* [link-1983]
* [krifka-1986]
-/

@[expose] public section

namespace Beck2001

open Mereology Plurality.Cumulativity Presupposition Reciprocal

/-! ### Pluralizing a partial predicate -/

section Pluralize

variable {β : Type*} [SemilatticeSup β] {f : β → Trivalent} {x : β}

open Classical in
/-- (115): the pluralization of a partial predicate, defined of what divides into parts where the
predicate is defined and true of what divides into parts where it is true. (115) states when `*`
and `**` are undefined; the other two clauses and `***` complete it, and all three are this
operator on individuals, on pairs and on triples. -/
noncomputable def pluralize (f : β → Trivalent) : β → Trivalent :=
  Trivalent.condEvent (fun x ↦ AlgClosure (f · ≠ .undefined) x) (fun x ↦ AlgClosure (f · = .true) x)

theorem pluralize_eq_undefined_iff :
    pluralize f x = .undefined ↔ ¬ AlgClosure (f · ≠ .undefined) x := by
  simp [pluralize]

theorem pluralize_eq_true_iff : pluralize f x = .true ↔ AlgClosure (f · = .true) x := by
  simp only [pluralize, Trivalent.condEvent_eq_true_iff]
  exact and_iff_right_of_imp (algClosure_mono (fun _ h ↦ ne_of_eq_of_ne h (by decide)) _)

end Pluralize

private theorem eq_false_iff (v : Trivalent) : v = .false ↔ v ≠ .undefined ∧ v ≠ .true := by
  decide +revert

section EachOther

variable {α : Type*} [DecidableEq α] {Cov : Finset α → Prop} {x y d A : Finset α} {a b : α}
  {R : Finset α → Finset α → Prop}

/-! ### The reciprocal -/

/-- (76a): *each other* is the definite *the other ones among them*, the largest sum of cells of
the cover that are parts of the range `y` and do not overlap the contrast `x`, where there is one.
-/
noncomputable def eachOther (Cov : Finset α → Prop) (x y : Finset α) : Part (Finset α) :=
  iota {w | IsGreatest {z | AlgClosure (fun z ↦ ¬ Overlap z x ∧ z ≤ y ∧ Cov z) z} w}

theorem eachOther_dom_iff :
    (eachOther Cov x y).Dom ↔ ∃ z, ¬ Overlap z x ∧ z ≤ y ∧ Cov z := by
  refine ⟨fun h ↦ ?_, fun ⟨z, hz⟩ ↦ ?_⟩
  · obtain ⟨d, hd, -⟩ := iota_isGreatest_dom.1 h
    obtain ⟨z, hz, -⟩ := algClosure_has_base hd
    exact ⟨z, hz⟩
  · refine DirectedOn.iota_isGreatest_dom algClosure_cum.directedOn ?_ ⟨z, .base hz⟩
    rw [setOf_algClosure]
    exact ((Finset.finite_toSet y.powerset).subset fun _ h ↦ by simpa using h.2.1).supClosure

private theorem algClosure_otherAtoms_iff :
    AlgClosure (fun z ↦ ¬ Overlap z x ∧ z ≤ y ∧ Atom z) d ↔ d.Nonempty ∧ d ⊆ y \ x := by
  rw [algClosure_iff_of_subset_range_singleton fun z hz ↦
    let ⟨a, ha⟩ := atom_finset_iff.1 hz.2.2; ⟨a, ha.symm⟩]
  simp [overlap_iff_not_disjoint, atom_singleton, Finset.subset_iff, and_comm]

theorem eachOther_atom_eq_some_iff : d ∈ eachOther Atom x y ↔ d.Nonempty ∧ d = y \ x := by
  rw [eachOther, mem_iota_isGreatest]
  simp only [IsGreatest, upperBounds, Set.mem_ofPred_eq, algClosure_otherAtoms_iff]
  refine ⟨fun ⟨⟨hd, hsub⟩, hub⟩ ↦ ⟨hd, hsub.antisymm (hub ⟨hd.mono hsub, subset_rfl⟩)⟩, ?_⟩
  rintro ⟨hd, rfl⟩
  exact ⟨⟨hd, subset_rfl⟩, fun _ hz ↦ hz.2⟩

theorem eachOther_atom_dom_iff : (eachOther Atom x y).Dom ↔ (y \ x).Nonempty :=
  Part.dom_iff_mem.trans <| by
    simp only [eachOther_atom_eq_some_iff]
    exact ⟨fun ⟨_, hd, e⟩ ↦ e ▸ hd, fun h ↦ ⟨_, h, rfl⟩⟩

-- (111)
theorem eachOther_atom_singleton_of_ne (h : a ≠ b) : {b} ∈ eachOther Atom {a} {b} :=
  eachOther_atom_eq_some_iff.2 ⟨Finset.singleton_nonempty b, by
    rw [Finset.sdiff_singleton_eq_erase, Finset.erase_eq_of_notMem (by simpa using h)]⟩

-- (111)
theorem eachOther_atom_singleton_self : eachOther Atom {a} {a} = Part.none := by
  rw [Part.eq_none_iff', eachOther_atom_dom_iff]
  simp

-- (111)
theorem eachOther_atom_singleton_eq_some_iff :
    d ∈ eachOther Atom {a} {b} ↔ a ≠ b ∧ d = {b} := by
  obtain rfl | h := eq_or_ne a b
  · simp [eachOther_atom_singleton_self, Part.notMem_none]
  · simp only [ne_eq, h, not_false_eq_true, true_and]
    exact ⟨fun hd ↦ Part.mem_unique hd (eachOther_atom_singleton_of_ne h),
      fun e ↦ e ▸ eachOther_atom_singleton_of_ne h⟩

open Classical in
-- (111), (112)
theorem presupOfReferent_eachOther (P : Finset α → Prop) (a b : α) :
    presupOfReferent (eachOther Atom {a}) (fun d _ ↦ P d) ({b} : Finset α) =
      if a = b then .undefined else Trivalent.ofProp (P {b}) := by
  obtain rfl | h := eq_or_ne a b
  · simp [presupOfReferent_of_not_dom (Part.eq_none_iff'.1 eachOther_atom_singleton_self)]
  · simp [presupOfReferent_of_mem (eachOther_atom_singleton_of_ne h), h]

-- (77) as printed
theorem not_exists_isLeast_otherAtoms (h : (y \ x).Nontrivial) :
    ¬ ∃ d, IsLeast {z | AlgClosure (fun z ↦ ¬ Overlap z x ∧ z ≤ y ∧ Atom z) z} d := by
  simp only [IsLeast, lowerBounds, Set.mem_ofPred_eq, algClosure_otherAtoms_iff]
  rintro ⟨d, ⟨⟨a, ha⟩, -⟩, hlb⟩
  obtain ⟨b, hb, hne⟩ := h.exists_ne a
  exact hne (Finset.mem_singleton.1
    (hlb ⟨Finset.singleton_nonempty b, Finset.singleton_subset_iff.2 hb⟩ ha)).symm

/-- (79), after [sauerland-1998]: non-overlap excludes each member of a plural contrast, which
non-identity would let in. -/
example : {2} ∈ eachOther Atom {0, 1} ({0, 1, 2} : Finset (Fin 3)) :=
  eachOther_atom_eq_some_iff.2 ⟨by decide, by decide⟩

/-! ### The collective and the strong reading -/

/-- (84a), with the cover as in (82c): the collective reading, the relation holding of each member
of the antecedent and the group the reciprocal denotes. -/
noncomputable def collectiveReading (Cov : Finset α → Prop) (R : Finset α → Finset α → Prop)
    (A : Finset α) : Trivalent :=
  pluralize (presupOfReferent (eachOther Cov · A) fun d x ↦ Cov x ∧ R x d) A

/-- (81a): Strong Reciprocity, the collective schema with the object slot distributed over. -/
noncomputable def strongReading (Cov : Finset α → Prop) (R : Finset α → Finset α → Prop)
    (A : Finset α) : Trivalent :=
  collectiveReading Cov (fun x d ↦ AlgClosure (fun y ↦ Cov y ∧ R x y) d) A

private theorem sdiff_nonempty_of_algClosure (hA : (A : Set α).Subsingleton)
    {p : Finset α × Finset α} (hp : AlgClosure (fun p ↦ (p.2 \ p.1).Nonempty) p) (hle : p.2 ≤ A) :
    (A \ p.1).Nonempty := by
  induction hp with
  | base h => exact h.mono (Finset.sdiff_subset_sdiff hle le_rfl)
  | sum _ _ ih ih' =>
    obtain ⟨a, ha⟩ := ih (le_sup_left.trans hle)
    obtain ⟨b, hb⟩ := ih' (le_sup_right.trans hle)
    simp only [Finset.mem_sdiff] at ha hb
    obtain rfl := hA ha.1 hb.1
    exact ⟨a, by simp [ha.1, ha.2, hb.2]⟩

private theorem nontrivial_of_algClosure_sdiff_pair
    (h : AlgClosure (fun p : Finset α × Finset α ↦ (p.2 \ p.1).Nonempty) (A, A)) : A.Nontrivial :=
  Set.not_subsingleton_iff.1 fun hA ↦ by simpa using sdiff_nonempty_of_algClosure hA h le_rfl

private theorem algClosure_sdiff_pair_of_self (h : AlgClosure (fun x ↦ (A \ x).Nonempty) A) :
    AlgClosure (fun p : Finset α × Finset α ↦ (p.2 \ p.1).Nonempty) (A, A) :=
  .map (f := fun x ↦ (x, A)) (by simp) (fun _ ↦ id) h

private theorem algClosure_sdiff_self_iff :
    AlgClosure (fun x ↦ (A \ x).Nonempty) A ↔ A.Nontrivial := by
  refine ⟨fun h ↦ nontrivial_of_algClosure_sdiff_pair (algClosure_sdiff_pair_of_self h),
    fun hA ↦ algClosure_mono (fun z hz ↦ ?_) _
      ((algClosure_image_singleton ↑A A).2 ⟨hA.nonempty, subset_rfl⟩)⟩
  obtain ⟨a, -, rfl⟩ := hz
  obtain ⟨b, hb, hne⟩ := hA.exists_ne a
  exact ⟨b, by simp [hb, hne]⟩

private theorem algClosure_sdiff_pair_iff :
    AlgClosure (fun p : Finset α × Finset α ↦ (p.2 \ p.1).Nonempty) (A, A) ↔ A.Nontrivial :=
  ⟨nontrivial_of_algClosure_sdiff_pair,
    fun h ↦ algClosure_sdiff_pair_of_self (algClosure_sdiff_self_iff.2 h)⟩

theorem collectiveReading_eq_undefined_iff :
    collectiveReading Atom R A = .undefined ↔ ¬ A.Nontrivial := by
  rw [collectiveReading, pluralize_eq_undefined_iff, not_iff_not, ← algClosure_sdiff_self_iff]
  simp only [ne_eq, presupOfReferent_eq_undefined_iff, not_not, eachOther_atom_dom_iff]

theorem collectiveReading_eq_true_iff :
    collectiveReading Atom R A = .true ↔ A.Nontrivial ∧ ∀ a ∈ A, R {a} (A.erase a) := by
  have hP : {x | presupOfReferent (eachOther Atom · A) (fun d x ↦ Atom x ∧ R x d) x = .true} ⊆
      Set.range ({·} : α → Finset α) := fun x hx ↦ by
    obtain ⟨_, -, hx, -⟩ := presupOfReferent_eq_true_iff.1 hx
    obtain ⟨a, rfl⟩ := atom_finset_iff.1 hx
    exact ⟨a, rfl⟩
  have key (a : α) : presupOfReferent (eachOther Atom · A) (fun d x ↦ Atom x ∧ R x d) {a} = .true ↔
      (A.erase a).Nonempty ∧ R {a} (A.erase a) := by
    simp only [presupOfReferent_eq_true_iff, eachOther_atom_eq_some_iff,
      Finset.sdiff_singleton_eq_erase]
    exact ⟨fun ⟨_, ⟨hd, e⟩, _, hR⟩ ↦ e ▸ ⟨hd, hR⟩,
      fun ⟨hd, hR⟩ ↦ ⟨_, ⟨hd, rfl⟩, atom_singleton a, hR⟩⟩
  rw [collectiveReading, pluralize_eq_true_iff, algClosure_iff_of_subset_range_singleton hP]
  simp only [key]
  refine ⟨fun ⟨⟨a, ha⟩, h⟩ ↦ ⟨(Finset.erase_nonempty ha).1 (h a ha).1, fun a ha ↦ (h a ha).2⟩,
    fun ⟨hA, h⟩ ↦ ⟨hA.nonempty, fun a ha ↦ ⟨(Finset.erase_nonempty ha).2 hA, h a ha⟩⟩⟩

theorem strongReading_eq_undefined_iff : strongReading Atom R A = .undefined ↔ ¬ A.Nontrivial :=
  collectiveReading_eq_undefined_iff

-- (81), (10)
theorem strongReading_eq_true_iff :
    strongReading Atom R A = .true ↔ StrongReciprocity (fun a b ↦ R {a} {b}) A := by
  rw [strongReading, collectiveReading_eq_true_iff, strongReciprocity_iff]
  refine and_congr_right fun hA ↦ ?_
  have key (a : α) (ha : a ∈ A) : AlgClosure (fun y ↦ Atom y ∧ R {a} y) (A.erase a) ↔
      ∀ b ∈ A.erase a, R {a} {b} := by
    rw [algClosure_iff_of_subset_range_singleton fun z hz ↦
      let ⟨b, hb⟩ := atom_finset_iff.1 hz.1; ⟨b, hb.symm⟩]
    simp [atom_singleton, Finset.erase_nonempty ha, hA]
  refine ⟨fun h x hx y hy hxy ↦ (key x hx).1 (h x hx) y (Finset.mem_erase.2 ⟨hxy.symm, hy⟩),
    fun h a ha ↦ (key a ha).2 fun b hb ↦ ?_⟩
  obtain ⟨hne, hb⟩ := Finset.mem_erase.1 hb
  exact h ha hb hne.symm

/-! ### Relational plurals and the weak reading -/

/-- (110b), (128b): a relational plural between `A` and `B`, the cumulation of the relation between
`x` and the other ones among `y`, whose cells the second cover gives. -/
noncomputable def cumulatedReading (Cov CovY : Finset α → Prop) (R : Finset α → Finset α → Prop)
    (A B : Finset α) : Trivalent :=
  pluralize (presupOfReferent (fun p : Finset α × Finset α ↦ eachOther Cov p.1 p.2)
    fun d p ↦ Cov p.1 ∧ CovY p.2 ∧ R p.1 d) (A, B)

/-- (120a): Weak Reciprocity, the relational plural between the antecedent and itself, the range
of the reciprocal being a second occurrence of the antecedent raised by QR. -/
noncomputable def weakReading (Cov : Finset α → Prop) (R : Finset α → Finset α → Prop)
    (A : Finset α) : Trivalent :=
  cumulatedReading Cov Cov R A A

/-- A reciprocal sentence on the weak reading presupposes that its antecedent is a plurality, since
a pair can be cumulated into `⟨A, A⟩` only if `A` divides into distinct parts. -/
theorem weakReading_eq_undefined_iff : weakReading Atom R A = .undefined ↔ ¬ A.Nontrivial := by
  rw [weakReading, cumulatedReading, pluralize_eq_undefined_iff, not_iff_not,
    ← algClosure_sdiff_pair_iff]
  simp only [ne_eq, presupOfReferent_eq_undefined_iff, not_not, eachOther_atom_dom_iff]

-- (110), (128)
theorem cumulatedReading_atom_eq_true_iff {z y : Finset α} :
    cumulatedReading Atom Atom R z y = .true ↔
      z.Nonempty ∧ Set.LiftRel (fun a b ↦ R {a} {b} ∧ a ≠ b) ↑z ↑y := by
  have : (fun p : Finset α × Finset α ↦ presupOfReferent (fun p ↦ eachOther Atom p.1 p.2)
      (fun d p ↦ Atom p.1 ∧ Atom p.2 ∧ R p.1 d) p = .true) =
      Function.uncurry (Relation.Map (fun a b ↦ R {a} {b} ∧ a ≠ b) ({·}) ({·})) := by
    ext ⟨x, y⟩
    simp only [presupOfReferent_eq_true_iff, Function.uncurry]
    constructor
    · rintro ⟨d, hd, hx, hy, hR⟩
      obtain ⟨a, rfl⟩ := atom_finset_iff.1 hx
      obtain ⟨b, rfl⟩ := atom_finset_iff.1 hy
      obtain ⟨hne, rfl⟩ := eachOther_atom_singleton_eq_some_iff.1 hd
      exact ⟨a, b, ⟨hR, hne⟩, rfl, rfl⟩
    · rintro ⟨a, b, ⟨hR, hne⟩, rfl, rfl⟩
      exact ⟨_, eachOther_atom_singleton_of_ne hne, atom_singleton a, atom_singleton b, hR⟩
  rw [cumulatedReading, pluralize_eq_true_iff, ← cumulation_map_singleton, Cumulation, this]

/-- Cumulating the relation to the definite has the truth conditions of Weak Reciprocity. -/
theorem weakReading_eq_true_iff :
    weakReading Atom R A = .true ↔ A.Nonempty ∧ WeakReciprocity (fun a b ↦ R {a} {b}) A := by
  rw [weakReading, cumulatedReading_atom_eq_true_iff, weakReciprocity_iff_liftRel]

theorem weakReading_eq_false_iff :
    weakReading Atom R A = .false ↔ A.Nontrivial ∧ ¬ WeakReciprocity (fun a b ↦ R {a} {b}) A := by
  rw [eq_false_iff, ne_eq, ne_eq, weakReading_eq_undefined_iff, weakReading_eq_true_iff, not_not]
  exact and_congr_right fun hA ↦ not_congr (and_iff_right hA.nonempty)

-- (63), (130a)
theorem exists_cell_of_weakReading_eq_true (h : weakReading Cov R A = .true) (ha : a ∈ A) :
    ∃ z, Cov z ∧ z ≤ A ∧ a ∈ z := by
  rw [weakReading, cumulatedReading, pluralize_eq_true_iff] at h
  suffices ∀ {p : Finset α × Finset α}, AlgClosure (fun p ↦ presupOfReferent
      (fun p : Finset α × Finset α ↦ eachOther Cov p.1 p.2)
      (fun d p ↦ Cov p.1 ∧ Cov p.2 ∧ R p.1 d) p = .true) p →
        ∀ a ∈ p.1, ∃ z, Cov z ∧ z ≤ p.1 ∧ a ∈ z from this h a ha
  intro p hp
  induction hp with
  | @base p h =>
    obtain ⟨_, -, hc, -⟩ := presupOfReferent_eq_true_iff.1 h
    exact fun a ha ↦ ⟨p.1, hc, le_rfl, ha⟩
  | sum _ _ ih ih' =>
    intro a ha
    obtain ha | ha := Finset.mem_union.1 ha
    · obtain ⟨z, hc, hz, haz⟩ := ih a ha
      exact ⟨z, hc, hz.trans le_sup_left, haz⟩
    · obtain ⟨z, hc, hz, haz⟩ := ih' a ha
      exact ⟨z, hc, hz.trans le_sup_right, haz⟩

-- (100), (101a)
theorem compl_weakReading_pair_eq_true_iff (hab : a ≠ b) :
    (weakReading Atom R {a, b})ᶜ = .true ↔ ¬ (R {a} {b} ∧ R {b} {a}) := by
  have hnt : ({a, b} : Finset α).Nontrivial := ⟨a, by simp, b, by simp, hab⟩
  rw [Trivalent.compl_eq_true_iff, weakReading_eq_false_iff, weakReciprocity_pair,
    and_iff_right hnt]
  simp [hab]

-- (121d)
theorem weakReading_not_pair_eq_true_iff (hab : a ≠ b) :
    weakReading Atom (fun x y ↦ ¬ R x y) {a, b} = .true ↔ ¬ R {a} {b} ∧ ¬ R {b} {a} := by
  rw [weakReading_eq_true_iff, weakReciprocity_pair]
  simp [hab]

/-- (128): Sue (`0`) hates the other ones in her group, Amy (`3`) those in hers. -/
def HatesOthers (x d : Finset (Fin 6)) : Prop := (x = {0} ∧ d = {1, 2}) ∨ (x = {3} ∧ d = {4, 5})

-- (128)
theorem hatesOthers_row :
    cumulatedReading Atom (· ∈ ({{0, 1, 2}, {3, 4, 5}} : Finset (Finset (Fin 6)))) HatesOthers
      {0, 3} Finset.univ = .true ∧ .acceptable ∈ Examples.ex128a.readings.lookup "(128b)" := by
  refine ⟨?_, by decide⟩
  rw [cumulatedReading, pluralize_eq_true_iff]
  have e : (({0, 3} : Finset (Fin 6)), (Finset.univ : Finset (Fin 6))) =
      (({0} : Finset (Fin 6)), ({0, 1, 2} : Finset (Fin 6))) ⊔
        (({3} : Finset (Fin 6)), ({3, 4, 5} : Finset (Fin 6))) := by decide
  rw [e]
  exact .sum
    (.base (presupOfReferent_eq_true_iff.2 ⟨{1, 2}, eachOther_atom_eq_some_iff.2
      ⟨by decide, by decide⟩, atom_singleton 0, by simp, .inl ⟨rfl, rfl⟩⟩))
    (.base (presupOfReferent_eq_true_iff.2 ⟨{4, 5}, eachOther_atom_eq_some_iff.2
      ⟨by decide, by decide⟩, atom_singleton 3, by simp, .inr ⟨rfl, rfl⟩⟩))

/-! ### Comparison with the quantificational and the cumulative analysis -/

-- (75), (81)
theorem strongReading_eq_true_iff_eachOtherLF :
    strongReading Atom R A = .true ↔
      1 < A.card ∧ HeimLasnikMay1991.eachOtherLF A (fun a b ↦ R {a} {b}) := by
  rw [strongReading_eq_true_iff]
  refine ⟨fun h ↦ ?_, fun ⟨hc, h⟩ ↦ (HeimLasnikMay1991.eachOtherLF_iff_strongReciprocity hc _).1 h⟩
  have hc := Finset.one_lt_card_iff_nontrivial.2 (strongReciprocity_iff.1 h).1
  exact ⟨hc, (HeimLasnikMay1991.eachOtherLF_iff_strongReciprocity hc _).2 h⟩

-- p. 104
theorem strongReading_singleton (a : α) :
    strongReading Atom R {a} = .undefined ∧
      HeimLasnikMay1991.eachOtherLF {a} (fun a b ↦ R {a} {b}) :=
  ⟨strongReading_eq_undefined_iff.2 Finset.not_nontrivial_singleton,
    HeimLasnikMay1991.eachOtherLF_singleton a _⟩

-- (98), (113), (120)
theorem weakReading_eq_true_iff_wr (R : α → α → Prop) (hA : A.Nonempty) :
    weakReading Atom (Relation.Map R ({·}) ({·})) A = .true ↔
      Sternefeld1998.WR (Relation.Map R ({·}) ({·})) A := by
  rw [weakReading_eq_true_iff, Sternefeld1998.wr_map_iff R hA, and_iff_right hA]
  simp only [Sternefeld1998.map_singleton_singleton]

-- (117), (118), (119)
theorem pants_row (R : α → α → Prop) (a : α) :
    (weakReading Atom (Relation.Map R ({·}) ({·})) {a} ≠ .undefined ↔
      Examples.ex119.judgment = .acceptable) ∧
    ¬ Sternefeld1998.WR (Relation.Map R ({·}) ({·})) {a} := by
  refine ⟨iff_of_false (not_not.2 (weakReading_eq_undefined_iff.2 Finset.not_nontrivial_singleton))
    (by decide), fun h ↦ ?_⟩
  obtain ⟨y, hy, -, hne⟩ := ((Sternefeld1998.wr_map_iff R (Finset.singleton_nonempty a)).1 h).1 a
    (Finset.mem_singleton_self a)
  exact hne (Finset.mem_singleton.1 hy).symm

/-- (99): everyone likes everyone else, but Bertha (`1`) cannot stand Dave (`3`). -/
def Likes (x y : Fin 4) : Prop := x ≠ y ∧ ¬ (x = 1 ∧ y = 3)
  deriving Decidable

-- (99)
theorem likes_row :
    ¬ StrongReciprocity Likes Finset.univ ∧ WeakReciprocity Likes Finset.univ ∧
      .acceptable ∈ Examples.ex99.readings.lookup "Strong Reciprocity" := by decide

/-- (83b): each of three forks is jointly supported by the other two, and not by any one of them.
-/
def Propped (x d : Finset (Fin 3)) : Prop := ∃ a, x = {a} ∧ d = Finset.univ.erase a

-- (83b), fn. 14
theorem propped_row :
    collectiveReading Atom Propped Finset.univ = .true ∧
      strongReading Atom Propped Finset.univ ≠ .true ∧
      .acceptable ∈ Examples.ex83b.readings.lookup "collective" := by
  refine ⟨collectiveReading_eq_true_iff.2 ⟨Finset.univ_nontrivial, fun a _ ↦ ⟨a, rfl, rfl⟩⟩,
    fun h ↦ ?_, by decide⟩
  obtain ⟨a, -, hd⟩ := (strongReciprocity_iff.1 (strongReading_eq_true_iff.1 h)).2
    (Finset.mem_coe.2 (Finset.mem_univ 0)) (Finset.mem_coe.2 (Finset.mem_univ 1)) (by decide)
  simpa using congrArg Finset.card hd

-- fn. 14
theorem strongReading_ne_collectiveReading :
    strongReading Atom (fun _ _ : Finset (Fin 3) ↦ True) Finset.univ = .true ∧
      collectiveReading Atom (Relation.Map (fun _ _ : Fin 3 ↦ True) ({·}) ({·}))
        Finset.univ ≠ .true := by
  refine ⟨strongReading_eq_true_iff.2 (by decide), fun h ↦ ?_⟩
  obtain ⟨_, b, -, -, hb⟩ := (collectiveReading_eq_true_iff.1 h).2 0 (Finset.mem_univ 0)
  simpa using congrArg Finset.card hb

-- (96): without distribution over the antecedent the contrast argument stays free, and the value
-- depends on the assignment.
theorem cumulation_erase_of_free_contrast :
    Cumulation (Relation.Map (fun x y : Fin 3 ↦ y ≠ 1 ∧ x ≠ y) ({·}) ({·})) Finset.univ
        (Finset.univ.erase 1) ∧
      ¬ Cumulation (Relation.Map (fun x y : Fin 3 ↦ y ≠ 1 ∧ x ≠ y) ({·}) ({·})) Finset.univ
        (Finset.univ.erase 0) := by
  simp only [cumulation_map_singleton, Set.LiftRel, Finset.mem_coe]
  decide

/-! ### The distinct subgroups effect -/

section DistinctSubgroups

variable {γ : Type*} {Q : Quantifier γ}

/-- With distinctness asserted in situ in the scope of a quantifier, the sentence is trivially true
when the quantifier holds of the empty set, and otherwise has distinctness outside the quantifier.
-/
theorem inSitu_dichotomy (φ : α → α → γ → Prop) (hA : A.Nonempty) :
    (Q ∅ → Cumulation (Relation.Map (fun a b ↦ Q {z | a ≠ b ∧ φ a b z}) ({·}) ({·})) A A) ∧
      (¬ Q ∅ → ∀ a b, Q {z | a ≠ b ∧ φ a b z} ↔ a ≠ b ∧ Q {z | φ a b z}) :=
  ⟨fun hQ ↦ (cumulation_map_singleton _ A A).2
      ⟨hA, fun a ha ↦ ⟨a, ha, by simpa using hQ⟩, fun a ha ↦ ⟨a, ha, by simpa using hQ⟩⟩,
    fun hQ a b ↦ by obtain rfl | h := eq_or_ne a b <;> simp [*]⟩

open Classical in
/-- A quantifier over `γ` applied to a partial scope, defined where the scope is defined for every
`z`, as the Weak Kleene quantifiers are. -/
noncomputable def partialScope (Q : Quantifier γ) (g : γ → Trivalent) : Trivalent :=
  if Trivalent.IsBivalent g then Trivalent.ofProp (Q (Trivalent.posExt g)) else .undefined

theorem partialScope_presupOfReferent [Nonempty γ] {W E : Type*} (r : W → Part E)
    (s : E → W → γ → Prop) (w : W) :
    partialScope Q (fun z ↦ presupOfReferent r (fun e w ↦ s e w z) w) =
      presupOfReferent r (fun e w ↦ Q {z | s e w z}) w := by
  by_cases hd : (r w).Dom
  · obtain ⟨e, h⟩ := Part.dom_iff_mem.1 hd
    have hb : Trivalent.IsBivalent fun z ↦ presupOfReferent r (fun e w ↦ s e w z) w :=
      (Trivalent.isBivalent_iff_forall_ne_undefined _).2 fun z ↦ by
        simp [presupOfReferent_of_mem h]
    have hset :
        Trivalent.posExt (fun z ↦ presupOfReferent r (fun e w ↦ s e w z) w) = {z | s e w z} :=
      Set.ext fun z ↦ by simp [presupOfReferent_of_mem h]
    rw [partialScope, ite_eq_left hb, hset, presupOfReferent_of_mem h]
  · have hb : ¬ Trivalent.IsBivalent fun z ↦ presupOfReferent r (fun e w ↦ s e w z) w :=
      fun hb ↦ hb.ne_undefined (Classical.arbitrary γ) (presupOfReferent_of_not_dom hd)
    rw [partialScope, ite_eq_right hb, presupOfReferent_of_not_dom hd]

private theorem meetWeak_ofProp_presupOfReferent {W E : Type*} (P : Prop) [Decidable P]
    (r : W → Part E) (s : E → W → Prop) (w : W) :
    Trivalent.meetWeak (Trivalent.ofProp P) (presupOfReferent r s w) =
      presupOfReferent r (fun e w ↦ P ∧ s e w) w := by
  by_cases hd : (r w).Dom
  · obtain ⟨e, h⟩ := Part.dom_iff_mem.1 hd
    rw [presupOfReferent_of_mem h, presupOfReferent_of_mem h]
    by_cases hP : P <;> by_cases hs : s e w <;> simp [Trivalent.ofProp, hP, hs]
  · by_cases hP : P <;> simp [presupOfReferent_of_not_dom hd, Trivalent.ofProp, hP]

open Classical in
private theorem presupOfReferent_congr_scope {W E : Type*} {r : W → Part E}
    {s s' : E → W → Prop} {w : W} (h : ∀ e, s e w ↔ s' e w) :
    presupOfReferent r s w = presupOfReferent r s' w :=
  Trivalent.eq_of_eq_undefined_iff_of_eq_true_iff (by simp) (by simp [h])

open Classical in
/-- With a quantifier between the reciprocal and cumulation, the sentence is the weak reading of
the relation with the quantifier inside it, whatever the quantifier: distinctness projects to the
binders, which is the distinct subgroups effect. -/
theorem pluralize_partialScope_eq_weakReading [Nonempty γ] (Cov : Finset α → Prop)
    (Q : Quantifier γ) (φ : Finset α → Finset α → γ → Prop) (A : Finset α) :
    pluralize (fun p : Finset α × Finset α ↦
        Trivalent.meetWeak (Trivalent.ofProp (Cov p.1 ∧ Cov p.2)) (partialScope Q fun z ↦
          presupOfReferent (fun p : Finset α × Finset α ↦ eachOther Cov p.1 p.2)
            (fun d p ↦ φ p.1 d z) p)) (A, A) =
      weakReading Cov (fun x d ↦ Q {z | φ x d z}) A := by
  simp only [weakReading, cumulatedReading]
  congr 1
  funext p
  rw [partialScope_presupOfReferent (fun p : Finset α × Finset α ↦ eachOther Cov p.1 p.2)
    (fun d p z ↦ φ p.1 d z) p, meetWeak_ofProp_presupOfReferent]
  exact presupOfReferent_congr_scope fun _ ↦ and_assoc

open Classical in
-- (121c), (121d)
theorem pluralize_compl_eq_weakReading (Cov : Finset α → Prop) (R : Finset α → Finset α → Prop)
    (A : Finset α) :
    pluralize (fun p : Finset α × Finset α ↦
        Trivalent.meetWeak (Trivalent.ofProp (Cov p.1 ∧ Cov p.2))
          (presupOfReferent (fun p : Finset α × Finset α ↦ eachOther Cov p.1 p.2)
            (fun d p ↦ R p.1 d) p)ᶜ) (A, A) =
      weakReading Cov (fun x d ↦ ¬ R x d) A := by
  simp only [weakReading, cumulatedReading]
  congr 1
  funext p
  rw [← presupOfReferent_not, meetWeak_ofProp_presupOfReferent]
  exact presupOfReferent_congr_scope fun _ ↦ and_assoc

/-- (105): the scenario's introductions, the student `z` being introduced by the first of the pair
`introductions z` to the second, with `a, b, c, d` as `0, 1, 2, 3`. -/
def introductions : Fin 4 → Fin 4 × Fin 4 := ![(0, 1), (1, 0), (2, 3), (3, 2)]

-- (105) to (107)
theorem exactlyTwo_row :
    Cumulation (Relation.Map (fun a b : Fin 4 ↦ {z | a ≠ b ∧ (a, b) = introductions z}.ncard = 2)
        ({·}) ({·})) Finset.univ Finset.univ ↔
      true ∈ Examples.ex105a.verdict := by
  refine iff_of_false ?_ (by decide)
  rw [cumulation_map_singleton]
  rintro ⟨-, h, -⟩
  obtain ⟨b, -, hb⟩ := h 0 (Finset.mem_univ 0)
  have hinj : Function.Injective introductions := by decide
  have : {z | (0 : Fin 4) ≠ b ∧ (0, b) = introductions z}.ncard ≤ 1 :=
    (Set.ncard_le_one (Set.toFinite _)).2 fun z hz w hw ↦ hinj (hz.2.symm.trans hw.2)
  omega

-- (105), (108): two students in the paper's division and in one of distinct pairs only
theorem exactlyTwo_across_division :
    (Finset.univ.filter fun z ↦
      introductions z ∈ ({(0, 0), (1, 1), (2, 3), (3, 2)} : Finset (Fin 4 × Fin 4))).card = 2 ∧
    (∀ p ∈ ({(0, 1), (1, 2), (2, 3), (3, 0)} : Finset (Fin 4 × Fin 4)), p.1 ≠ p.2) ∧
    (Finset.univ.filter fun z ↦
      introductions z ∈ ({(0, 1), (1, 2), (2, 3), (3, 0)} : Finset (Fin 4 × Fin 4))).card = 2 := by
  decide

end DistinctSubgroups

/-! ### Covers: subgroups and exceptions -/

-- (54b), (54c), fn. 5
theorem algClosure_iff_of_minimal_cover (hA : A.Nonempty) (C : Finset (Finset α))
    (hcov : C.sup id = A) (hmin : ∀ D ⊆ C, D.sup id = A → D = C) (φ : Finset α → Prop) :
    AlgClosure (fun X ↦ X ∈ C ∧ φ X) A ↔ ∀ X ∈ C, φ X := by
  rw [algClosure_iff_exists_sup']
  refine ⟨fun ⟨t, _, hP, hsup⟩ X hX ↦ ?_, fun h ↦ ?_⟩
  · have : t = C := hmin t (fun y hy ↦ (hP y hy).1) (by rw [← hsup, Finset.sup'_eq_sup])
    exact (hP X (this ▸ hX)).2
  · have hne : C.Nonempty := Finset.nonempty_iff_ne_empty.2 fun hC ↦ by
      simp [hC] at hcov
      exact hA.ne_empty hcov.symm
    exact ⟨C, hne, fun y hy ↦ ⟨hy, h y hy⟩, by rw [Finset.sup'_eq_sup, hcov]⟩

/-- Fit alone is not enough for (54b) and (54c) to agree, as footnote 5 requires minimality. -/
example : ∃ (C : Finset (Finset (Fin 3))) (φ : Finset (Fin 3) → Prop),
    C.sup id = Finset.univ ∧ AlgClosure (fun X ↦ X ∈ C ∧ φ X) Finset.univ ∧ ¬ ∀ X ∈ C, φ X := by
  refine ⟨{{0, 1}, {1, 2}, {0, 2}}, (· ≠ {0, 2}), by decide, ?_, by simp⟩
  have e : (Finset.univ : Finset (Fin 3)) = {0, 1} ⊔ {1, 2} := by decide
  rw [e]
  exact .sum (.base ⟨by simp, by decide⟩) (.base ⟨by simp, by decide⟩)

private theorem Finpartition.minimal (P : Finpartition A) (D : Finset (Finset α))
    (hD : D ⊆ P.parts) (hsup : D.sup id = A) : D = P.parts := by
  refine hD.antisymm fun c hc ↦ ?_
  obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hc
  obtain ⟨X, hX, haX⟩ := Finset.mem_sup.1 (hsup ▸ P.le hc ha)
  exact P.eq_of_mem_parts hc (hD hX) ha haX ▸ hX

-- (86), (87), (88)
theorem pluralize_parts_eq_true_iff (P : Finpartition A) (hA : A.Nonempty) :
    pluralize (fun X ↦ Trivalent.ofProp (X ∈ P.parts) ⊓ strongReading Atom R X) A = .true ↔
      ∀ X ∈ P.parts, StrongReciprocity (fun a b ↦ R {a} {b}) X := by
  simp only [pluralize_eq_true_iff, Trivalent.inf_eq_true_iff, Trivalent.ofProp_eq_true_iff,
    strongReading_eq_true_iff]
  exact algClosure_iff_of_minimal_cover hA P.parts P.sup_parts (Finpartition.minimal P) _

-- (12): the existential that p. 94 calls too weak, against the salient partition of (88)
theorem partitionedStrongReciprocity_iff_exists_pluralize (hA : A.Nonempty) :
    PartitionedStrongReciprocity (fun a b ↦ R {a} {b}) A ↔ ∃ P : Finpartition A,
      pluralize (fun X ↦ Trivalent.ofProp (X ∈ P.parts) ⊓ strongReading Atom R X) A = .true :=
  exists_congr fun P ↦ (pluralize_parts_eq_true_iff P hA).symm

/-- A situation of (136), (141) and (142), given by its arrows. -/
def Stares (arrows : List (Fin 6 × Fin 6)) (x y : Fin 6) : Prop := (x, y) ∈ arrows
  deriving Decidable

/-- (136): a cycle of five pirates, the sixth staring at the first and not stared at. -/
def situation136 : List (Fin 6 × Fin 6) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (5, 0)]

/-- (141): the same cycle and a completely uninvolved sixth pirate. -/
def situation141 : List (Fin 6 × Fin 6) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]

/-- (142): everyone stares at the first pirate, who stares at the sixth. -/
def situation142 : List (Fin 6 × Fin 6) := [(0, 5), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0)]

/-- (140): the pirates the cover contains, leaving the sixth out. -/
def coveredPirates : Finset (Fin 6) := {0, 1, 2, 3, 4}

/-- Weak Reciprocity over a cover that leaves the sixth pirate out is true in the situations judged
true, and *all*, which [brisson-1998] takes to force the cover to fit, makes it false in the
situation judged false. -/
theorem pirates_rows :
    (WeakReciprocity (Stares situation136) coveredPirates ↔
      true ∈ Examples.ex135_136.verdict) ∧
    (WeakReciprocity (Stares situation141) coveredPirates ↔
      true ∈ Examples.ex135_141.verdict) ∧
    (WeakReciprocity (Stares situation141) Finset.univ ↔
      true ∈ Examples.ex143_141.verdict) := by
  decide

-- (136), (141), (142)
theorem oneWayWeak_mispredicts :
    ¬ OneWayWeakReciprocity (Stares situation141) Finset.univ ∧
      true ∈ Examples.ex135_141.verdict ∧
    OneWayWeakReciprocity (Stares situation142) Finset.univ ∧
      Examples.ex135_142.judgment = .questionable := by decide

-- (142)
theorem subset_of_weakReciprocity_situation142 {U : Finset (Fin 6)}
    (h : WeakReciprocity (Stares situation142) U) : U ⊆ {0, 5} := fun b hb ↦ by
  obtain ⟨x, -, hx, -⟩ := h.2 b hb
  have : ∀ x b, Stares situation142 x b → b ∈ ({0, 5} : Finset (Fin 6)) := by decide
  exact this x b hx

-- (130a), (136), (139), (140)
theorem weakReading_situation136 :
    weakReading (fun z ↦ Atom z ∧ z ≤ coveredPirates)
      (Relation.Map (Stares situation136) ({·}) ({·})) Finset.univ = .false := by
  refine (eq_false_iff _).2 ⟨?_, fun h ↦ ?_⟩
  · rw [weakReading, cumulatedReading, ne_eq, pluralize_eq_undefined_iff, not_not]
    have base (x y : Finset (Fin 6)) (c : Fin 6) (hc : c ∈ coveredPirates) (hx : c ∉ x)
        (hy : c ∈ y) : AlgClosure (fun p : Finset (Fin 6) × Finset (Fin 6) ↦
          presupOfReferent (fun p : Finset (Fin 6) × Finset (Fin 6) ↦
            eachOther (fun z ↦ Atom z ∧ z ≤ coveredPirates) p.1 p.2)
          (fun d p ↦ (Atom p.1 ∧ p.1 ≤ coveredPirates) ∧ (Atom p.2 ∧ p.2 ≤ coveredPirates) ∧
            Relation.Map (Stares situation136) ({·}) ({·}) p.1 d) p ≠ .undefined) (x, y) := by
      refine .base ?_
      rw [ne_eq, presupOfReferent_eq_undefined_iff, not_not, eachOther_dom_iff]
      exact ⟨{c}, overlap_iff_not_disjoint.not_left.2 (Finset.disjoint_singleton_left.2 hx),
        Finset.singleton_subset_iff.2 hy, atom_singleton c, Finset.singleton_subset_iff.2 hc⟩
    have e : ((Finset.univ : Finset (Fin 6)), (Finset.univ : Finset (Fin 6))) =
        (({1, 2, 3, 4, 5} : Finset (Fin 6)), ({0, 5} : Finset (Fin 6))) ⊔
          (({0} : Finset (Fin 6)), ({1, 2, 3, 4} : Finset (Fin 6))) := by decide
    rw [e]
    exact .sum (base _ _ 0 (by decide) (by decide) (by decide))
      (base _ _ 1 (by decide) (by decide) (by decide))
  · obtain ⟨z, ⟨-, hz⟩, -, h5⟩ := exists_cell_of_weakReading_eq_true h (Finset.mem_univ 5)
    exact absurd (hz h5) (by decide)

/-- (85): the men are hitting each other in pairs. -/
def HitsInPairs (x y : Fin 4) : Prop := x ≠ y ∧ x.val / 2 = y.val / 2
  deriving Decidable

/-- The partition of the men by a function, the salient division of a context. -/
def menBy (f : Fin 4 → ℕ) : Finpartition (Finset.univ : Finset (Fin 4)) :=
  letI : DecidableRel (Setoid.ker f).r := fun _ _ ↦ inferInstanceAs (Decidable (_ = _))
  .ofSetoid (Setoid.ker f)

-- (12), (88), p. 94: the partition that teams the men up satisfies (88), and another does not
theorem hitsInPairs_salient :
    PartitionedStrongReciprocity HitsInPairs Finset.univ ∧
    (∀ X ∈ (menBy (·.val / 2)).parts, StrongReciprocity HitsInPairs X) ∧
    ¬ ∀ X ∈ (menBy (·.val % 2)).parts, StrongReciprocity HitsInPairs X := by
  refine ⟨⟨menBy (·.val / 2), by decide⟩, by decide, by decide⟩

/-! ### Situation-based Weak Reciprocity -/

variable {τ : Type*}

/-- (180a), (193a): situation-based Weak Reciprocity, the cumulation `***` of the relation over its
situation argument as well as its two individual arguments. -/
noncomputable def situationWeakReading {σ : Type*} [SemilatticeSup σ] (Cov : Finset α → Prop)
    (CovS : σ → Prop) (R : Finset α → Finset α → σ → Prop) (A : Finset α) (s : σ) : Trivalent :=
  pluralize (presupOfReferent (fun p : Finset α × Finset α × σ ↦ eachOther Cov p.1 p.2.1)
    fun d p ↦ Cov p.1 ∧ Cov p.2.1 ∧ CovS p.2.2 ∧ R p.1 d p.2.2) (A, A, s)

/-- (193b): every relevant subsituation contains a distinct pair in the relation, and every member
of `A` takes part in a relevant subsituation in each direction. -/
def SituationWeakReciprocity (R : α → α → τ → Prop) (A : Finset α) (subs : Finset τ) : Prop :=
  (∀ t ∈ subs, ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ R a b t) ∧
    (∀ a ∈ A, ∃ t ∈ subs, ∃ b ∈ A, a ≠ b ∧ R a b t) ∧
      ∀ b ∈ A, ∃ t ∈ subs, ∃ a ∈ A, a ≠ b ∧ R a b t

instance (R : α → α → τ → Prop) [∀ a b t, Decidable (R a b t)] (A : Finset α) (subs : Finset τ) :
    Decidable (SituationWeakReciprocity R A subs) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

-- (176), (178)
private theorem algClosure_triple_iff {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (R : α → β → γ → Prop) (x : Finset α) (y : Finset β) (s : Finset γ) :
    AlgClosure (fun p : Finset α × Finset β × Finset γ ↦ ∃ a b t, R a b t ∧ p = ({a}, {b}, {t}))
        (x, y, s) ↔
      x.Nonempty ∧ (∀ t ∈ s, ∃ a ∈ x, ∃ b ∈ y, R a b t) ∧ (∀ a ∈ x, ∃ t ∈ s, ∃ b ∈ y, R a b t) ∧
        ∀ b ∈ y, ∃ t ∈ s, ∃ a ∈ x, R a b t := by
  constructor
  · suffices ∀ {p : Finset α × Finset β × Finset γ},
        AlgClosure (fun p ↦ ∃ a b t, R a b t ∧ p = ({a}, {b}, {t})) p →
          p.1.Nonempty ∧ (∀ t ∈ p.2.2, ∃ a ∈ p.1, ∃ b ∈ p.2.1, R a b t) ∧
            (∀ a ∈ p.1, ∃ t ∈ p.2.2, ∃ b ∈ p.2.1, R a b t) ∧
              ∀ b ∈ p.2.1, ∃ t ∈ p.2.2, ∃ a ∈ p.1, R a b t from this
    intro p hp
    induction hp with
    | base h =>
      obtain ⟨a, b, t, hR, rfl⟩ := h
      simpa using hR
    | sum _ _ ih ih' =>
      simp only [Prod.fst_sup, Prod.snd_sup, Finset.sup_eq_union]
      exact ⟨ih.1.mono Finset.subset_union_left, by grind, by grind, by grind⟩
  · rintro ⟨⟨a, ha⟩, hs, hx, hy⟩
    classical
    obtain ⟨t, ht, b, hb, hR⟩ := hx a ha
    let g (W : Finset (α × β × γ)) : Finset α × Finset β × Finset γ :=
      (W.image (·.1), W.image (·.2.1), W.image (·.2.2))
    let W := (x ×ˢ y ×ˢ s).filter fun q ↦ R q.1 q.2.1 q.2.2
    have hg : g W = (x, y, s) := by
      simp only [g, Prod.mk.injEq]
      refine ⟨?_, ?_, ?_⟩ <;> ext <;> simp [W] <;> grind
    rw [← hg]
    refine .map (f := g) (by simp [g, Finset.image_union]) ?_
      ((algClosure_image_singleton {q : α × β × γ | R q.1 q.2.1 q.2.2} W).2
        ⟨⟨(a, b, t), by simp [W, *]⟩, fun q hq ↦ (Finset.mem_filter.1 hq).2⟩)
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨_, _, _, hq, by simp [g]⟩

theorem situationWeakReading_eq_undefined_iff [DecidableEq τ] {CovS : Finset τ → Prop}
    {R : Finset α → Finset α → Finset τ → Prop} {s : Finset τ} :
    situationWeakReading Atom CovS R A s = .undefined ↔ ¬ A.Nontrivial := by
  rw [situationWeakReading, pluralize_eq_undefined_iff, not_iff_not, ← algClosure_sdiff_pair_iff]
  simp only [ne_eq, presupOfReferent_eq_undefined_iff, not_not, eachOther_atom_dom_iff]
  exact ⟨fun h ↦ h.map (x := (A, A, s)) (f := fun q ↦ (q.1, q.2.1)) (by simp) fun _ ↦ id,
    fun h ↦ h.map (x := (A, A)) (f := fun p ↦ (p.1, p.2, s)) (by simp) fun _ ↦ id⟩

-- (193a), (193b)
theorem situationWeakReading_eq_true_iff [DecidableEq τ]
    {R : Finset α → Finset α → Finset τ → Prop} {s : Finset τ} :
    situationWeakReading Atom Atom R A s = .true ↔
      A.Nonempty ∧ SituationWeakReciprocity (fun a b t ↦ R {a} {b} {t}) A s := by
  rw [situationWeakReading, pluralize_eq_true_iff]
  have : (fun q : Finset α × Finset α × Finset τ ↦
      presupOfReferent (fun q : Finset α × Finset α × Finset τ ↦ eachOther Atom q.1 q.2.1)
        (fun d q ↦ Atom q.1 ∧ Atom q.2.1 ∧ Atom q.2.2 ∧ R q.1 d q.2.2) q = .true) =
      fun q ↦ ∃ a b t, (a ≠ b ∧ R {a} {b} {t}) ∧ q = ({a}, {b}, {t}) := by
    ext ⟨x, y, s⟩
    simp only [presupOfReferent_eq_true_iff]
    constructor
    · rintro ⟨d, hd, hx, hy, hs, hR⟩
      obtain ⟨a, rfl⟩ := atom_finset_iff.1 hx
      obtain ⟨b, rfl⟩ := atom_finset_iff.1 hy
      obtain ⟨t, rfl⟩ := atom_finset_iff.1 hs
      obtain ⟨hne, rfl⟩ := eachOther_atom_singleton_eq_some_iff.1 hd
      exact ⟨a, b, t, ⟨hne, hR⟩, rfl⟩
    · rintro ⟨a, b, t, ⟨hne, hR⟩, he⟩
      obtain ⟨rfl, rfl, rfl⟩ : x = {a} ∧ y = {b} ∧ s = {t} := by simpa using he
      exact ⟨_, eachOther_atom_singleton_of_ne hne, atom_singleton a, atom_singleton b,
        atom_singleton t, hR⟩
  rw [this]
  exact algClosure_triple_iff (fun a b t ↦ a ≠ b ∧ R {a} {b} {t}) A A s

section Entailments

omit [DecidableEq α]

variable {R : α → α → τ → Prop} {subs : Finset τ} {S : α → α → Prop}

-- (219), fn. 15, on persistence after [kratzer-1989]
theorem SituationWeakReciprocity.weak (hpers : ∀ a b, ∀ t ∈ subs, R a b t → S a b)
    (h : SituationWeakReciprocity R A subs) : WeakReciprocity S A := by
  obtain ⟨-, hx, hy⟩ := h
  refine ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · obtain ⟨t, ht, b, hb, hne, hR⟩ := hx a ha
    exact ⟨b, hb, hpers a b t ht hR, hne⟩
  · obtain ⟨t, ht, a, ha, hne, hR⟩ := hy b hb
    exact ⟨a, ha, hpers a b t ht hR, hne⟩

-- (219), fn. 15, (iv), with support in place of what (iv) leaves out
theorem situationWeak_of_strong (h : StrongReciprocity S A)
    (hiv : ∀ t ∈ subs, ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ R a b t)
    (hsupp : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → S a b → ∃ t ∈ subs, R a b t) :
    SituationWeakReciprocity R A subs := by
  obtain ⟨hA, hS⟩ := strongReciprocity_iff.1 h
  refine ⟨hiv, fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · obtain ⟨b, hb, hne⟩ := hA.exists_ne a
    obtain ⟨t, ht, hR⟩ := hsupp a ha b hb hne.symm (hS ha hb hne.symm)
    exact ⟨t, ht, b, hb, hne.symm, hR⟩
  · obtain ⟨a, ha, hne⟩ := hA.exists_ne b
    obtain ⟨t, ht, hR⟩ := hsupp a ha b hb hne (hS ha hb hne)
    exact ⟨t, ht, a, ha, hne, hR⟩

end Entailments

end EachOther

/-- Footnote 15's counter-model: `0` relates to `1` in any nonempty situation, and `1` to `0` only
in the whole situation, which is the sum of two cells. -/
def SplitRelation (a b : Fin 2) (s : Finset (Fin 2)) : Prop :=
  (a = 0 ∧ b = 1 ∧ s.Nonempty) ∨ (a = 1 ∧ b = 0 ∧ s = Finset.univ)
  deriving Decidable

-- fn. 15, (iii), (iv)
theorem not_situationWeak_splitRelation :
    (∀ a b, ∀ s t : Finset (Fin 2), s ⊆ t → SplitRelation a b s → SplitRelation a b t) ∧
    ({0} ∪ {1} : Finset (Fin 2)) = Finset.univ ∧
    StrongReciprocity (fun a b ↦ SplitRelation a b Finset.univ) Finset.univ ∧
    (∀ t ∈ ({{0}, {1}} : Finset (Finset (Fin 2))), ∃ a ∈ Finset.univ, ∃ b ∈ Finset.univ,
      a ≠ b ∧ SplitRelation a b t) ∧
    ¬ SituationWeakReciprocity SplitRelation Finset.univ {{0}, {1}} := by
  refine ⟨?_, by decide, by decide, by decide, by decide⟩
  rintro a b s t hst (⟨rfl, rfl, hs⟩ | ⟨rfl, rfl, rfl⟩)
  · exact .inl ⟨rfl, rfl, hs.mono hst⟩
  · exact .inr ⟨rfl, rfl, Finset.univ_subset_iff.1 hst⟩

/-! ### Intermediate Reciprocity and context -/

section Line

variable {n : ℕ}

theorem intermediate_of_line {R : Fin (n + 2) → Fin (n + 2) → Prop}
    (h : ∀ i : Fin (n + 1), R i.castSucc i.succ ∧ R i.succ i.castSucc) :
    IntermediateReciprocity R Finset.univ := by
  refine intermediateReciprocity_iff.2 ⟨Finset.univ_nontrivial, fun x _ y _ hxy ↦
    transGen_of_succ_of_ne _ (fun i hi ↦ ?_) (fun i hi ↦ ?_) hxy⟩ <;>
  · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 (Fin.ne_last_of_lt hi.2)
    simp [Fin.orderSucc_castSucc, h j]

-- (181), (182), (183)
theorem SituationWeakReciprocity.intermediate {R : Fin (n + 2) → Fin (n + 2) → Fin (n + 1) → Prop}
    {S : Fin (n + 2) → Fin (n + 2) → Prop} [Std.Symm S]
    (hedge : ∀ a b t, R a b t → (a = t.castSucc ∧ b = t.succ) ∨ (a = t.succ ∧ b = t.castSucc))
    (hpers : ∀ a b t, R a b t → S a b)
    (h : SituationWeakReciprocity R Finset.univ Finset.univ) :
    IntermediateReciprocity S Finset.univ := by
  refine intermediate_of_line fun i ↦ ?_
  obtain ⟨a, -, b, -, -, hR⟩ := h.1 i (Finset.mem_univ i)
  have hS := hpers a b i hR
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hedge a b i hR
  exacts [⟨hS, symm_of S hS⟩, ⟨symm_of S hS, hS⟩]

end Line

/-- (15), (153): five individuals with each of the first four adjacent to the next. -/
def Adjacent (x y : Fin 5) : Prop := x.val + 1 = y.val ∨ y.val + 1 = x.val
  deriving Decidable

/-- Adjacency in the subsituation of the `t`-th individual and its neighbour on the circle. -/
def AdjacentAt (x y t : Fin 5) : Prop :=
  Adjacent x y ∧ ((x = t ∧ y = t + 1) ∨ (y = t ∧ x = t + 1))
  deriving Decidable

-- (14), (15), (153)
theorem adjacent_rows :
    IntermediateReciprocity Adjacent Finset.univ ∧
    (SituationWeakReciprocity AdjacentAt Finset.univ {0, 1, 2, 3} ↔
      true ∈ Examples.ex14_15.verdict) ∧
    (SituationWeakReciprocity AdjacentAt Finset.univ Finset.univ ↔
      true ∈ Examples.ex153.verdict) :=
  ⟨intermediate_of_line (by decide), by decide, by decide⟩

/-- (181): the minimal situation containing the `t`-th of five poles and its neighbour on a circle.
-/
def poleCell (t : Fin 5) : Finset (Fin 5) := {t, t + 1}

/-- Two poles are in a situation and adjacent, the situation being the sum of what it contains. -/
def AdjacentIn (a b : Fin 5) (s : Finset (Fin 5)) : Prop := a ∈ s ∧ b ∈ s ∧ Adjacent a b
  deriving Decidable

-- (178), (181), (193)
theorem situationWeakReading_gap :
    situationWeakReading Atom (· ∈ Set.range poleCell)
        (fun x y s ↦ ∃ a b, x = {a} ∧ y = {b} ∧ AdjacentIn a b s) Finset.univ Finset.univ = .true ∧
      ¬ SituationWeakReciprocity AdjacentIn Finset.univ (Finset.univ.image poleCell) := by
  constructor
  · rw [situationWeakReading, pluralize_eq_true_iff]
    have base {a b : Fin 5} (t : Fin 5) (hne : a ≠ b) (h : AdjacentIn a b (poleCell t)) :
        AlgClosure (fun q : Finset (Fin 5) × Finset (Fin 5) × Finset (Fin 5) ↦
          presupOfReferent (fun q : Finset (Fin 5) × Finset (Fin 5) × Finset (Fin 5) ↦
            eachOther Mereology.Atom q.1 q.2.1)
          (fun d q ↦ Mereology.Atom q.1 ∧ Mereology.Atom q.2.1 ∧ q.2.2 ∈ Set.range poleCell ∧
            ∃ a b, q.1 = {a} ∧ d = {b} ∧ AdjacentIn a b q.2.2) q = .true)
          ({a}, {b}, poleCell t) :=
      .base (presupOfReferent_eq_true_iff.2 ⟨{b}, eachOther_atom_singleton_of_ne hne,
        atom_singleton a, atom_singleton b, ⟨t, rfl⟩, a, b, rfl, rfl, h⟩)
    have e : ((Finset.univ : Finset (Fin 5)), (Finset.univ : Finset (Fin 5)),
        (Finset.univ : Finset (Fin 5))) =
        ((({0} : Finset (Fin 5)), ({1} : Finset (Fin 5)), poleCell 0) ⊔
          (({1} : Finset (Fin 5)), ({0} : Finset (Fin 5)), poleCell 0)) ⊔
        ((({2} : Finset (Fin 5)), ({3} : Finset (Fin 5)), poleCell 2) ⊔
          (({3} : Finset (Fin 5)), ({2} : Finset (Fin 5)), poleCell 2)) ⊔
        ((({3} : Finset (Fin 5)), ({4} : Finset (Fin 5)), poleCell 3) ⊔
          (({4} : Finset (Fin 5)), ({3} : Finset (Fin 5)), poleCell 3)) := by decide
    rw [e]
    refine .sum (.sum (.sum ?_ ?_) (.sum ?_ ?_)) (.sum ?_ ?_) <;>
      exact base _ (by decide) (by decide)
  · rintro ⟨h, -, -⟩
    obtain ⟨a, -, b, -, -, hR⟩ := h (poleCell 4) (Finset.mem_image_of_mem _ (Finset.mem_univ 4))
    revert a b
    decide

/-- (188c): one colleague uses another's class notes. -/
def UsesNotes (x y : Fin 3) : Prop := x = 0 ∧ y = 1
  deriving Decidable

/-- (188b): that colleague respects the others, and nobody respects that colleague. -/
def Respects (x y : Fin 3) : Prop := x = 0 ∧ y ≠ 0
  deriving Decidable

-- (188): the reading a salient relation would predict is true of unrespected colleagues
theorem salientRelation_row :
    StrongReciprocity (fun x y ↦ UsesNotes x y → Respects x y) Finset.univ ∧
      ¬ StrongReciprocity (fun x y ↦ UsesNotes x y → Respects y x) Finset.univ ∧
      ¬ WeakReciprocity Respects Finset.univ ∧
      .unacceptable ∈ Examples.ex188a.readings.lookup "(188d)" := by
  decide

/-! ### Homogeneity and Inclusive Alternative Ordering -/

section Alternative

variable {α : Type*} {A : Finset α}

-- (197), (198), (199), (200), fn. 12; (216) prints no distinctness
theorem weakReading_symmGen_iff [DecidableEq α] (R : α → α → Prop) (hA : A.Nonempty) :
    weakReading Mereology.Atom (Relation.Map (Relation.SymmGen R) ({·}) ({·})) A = .true ↔
      InclusiveAlternativeOrdering R A := by
  rw [weakReading_eq_true_iff, and_iff_right hA]
  simp only [Sternefeld1998.map_singleton_singleton]
  exact ⟨fun h ↦ h.oneWayWeak hA, OneWayWeakReciprocity.weak⟩

open Classical in
-- (225), (229), (230b), (230c)
theorem compl_barePlural_offDiag_iff {W : Type*} (R : α → α → W → Prop) (w : W) :
    (∀ X ⊆ A, X.Nontrivial →
        (Homogeneity.barePlural (fun p w ↦ R p.1 p.2 w) X.offDiag w)ᶜ = .true) ↔
      ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ R a b w := by
  have hX {X : Finset α} (hX : X.Nontrivial) :
      (Homogeneity.barePlural (fun p w ↦ R p.1 p.2 w) X.offDiag w)ᶜ = .true ↔
        ∀ a ∈ X, ∀ b ∈ X, a ≠ b → ¬ R a b w := by
    obtain ⟨c, hc, d, hd, hcd⟩ := id hX
    rw [Trivalent.compl_eq_true_iff, Homogeneity.barePlural, Trivalent.supervaluation_eq_false_iff,
      and_iff_right ⟨(c, d), Finset.mem_offDiag.2 ⟨hc, hd, hcd⟩⟩]
    simp only [Finset.mem_offDiag, Prod.forall, and_imp]
    exact ⟨fun h a ha b hb ↦ h a b ha hb, fun h a b ha hb ↦ h a ha b hb⟩
  refine ⟨fun h a ha b hb hab ↦ ?_, fun h X hXA hXn ↦
    (hX hXn).2 fun a ha b hb hab ↦ h a (hXA ha) b (hXA hb) hab⟩
  have hA : A.Nontrivial := ⟨a, ha, b, hb, hab⟩
  exact (hX hA).1 (h A subset_rfl hA) a ha b hb hab

-- (221), (230c): the strong interpretation needs no Inclusive Alternative Ordering
theorem forall_not_inclusiveAlternativeOrdering_iff [DecidableEq α] (R : α → α → Prop) :
    (∀ X ⊆ A, ¬ InclusiveAlternativeOrdering R X) ↔ ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ R a b := by
  refine ⟨fun h a ha b hb hab hR ↦ h {a, b} ?_ ?_, fun h X hX hI ↦ ?_⟩
  · simp [Finset.insert_subset_iff, ha, hb]
  · refine oneWayWeakReciprocity_iff.2 ⟨⟨a, by simp, b, by simp, hab⟩, fun x hx ↦ ?_⟩
    obtain rfl | rfl := Finset.mem_insert.1 hx |>.imp_right Finset.mem_singleton.1
    · exact ⟨b, by simp, hab, .inl hR⟩
    · exact ⟨a, by simp, hab.symm, .inr hR⟩
  · obtain ⟨hn, hc⟩ := oneWayWeakReciprocity_iff.1 hI
    obtain ⟨x, hx⟩ := hn.nonempty
    obtain ⟨y, hy, hne, hR⟩ := hc x hx
    obtain hR | hR := hR
    · exact h x (hX hx) y (hX hy) hne hR
    · exact h y (hX hy) x (hX hx) hne.symm hR

-- (220), (221): under *none of them* the weakest reading gives the strongest sentence, so the
-- hypothesis over Dalrymple et al.'s readings denies any relating among the group
theorem isLeast_none {I : Set (α → α → Prop)}
    (h : ∃ R ∈ I, ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ R a b) :
    IsLeast (Set.range (fun q ↦ {R | ∀ X ⊆ A, ¬ Recip q R X}) ∩ {p | (p ∩ I).Nonempty})
      {R | ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ R a b} := by
  classical
  have e : {R : α → α → Prop | ∀ X ⊆ A, ¬ Recip (.tot, .alternative) R X} =
      {R | ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ R a b} :=
    Set.ext fun R ↦ forall_not_inclusiveAlternativeOrdering_iff R
  rw [← e]
  obtain ⟨R, hRI, hR⟩ := h
  exact IsLeast.isLeast_range_inter ⟨⟨R, (forall_not_inclusiveAlternativeOrdering_iff R).2 hR,
    hRI⟩, fun q _ ↦ (by decide : ∀ q : Coverage × Direction, (.tot, .alternative) ≤ q) q⟩
    fun _ _ hq _ hR X hX hr ↦ hR X hX (recip_antitone hq hr)

end Alternative

/-- (222): four members know a fifth, who knows none of them, and they are strangers to each other.
-/
def KnowsFifth (x y : Fin 5) : Prop := x ≠ 4 ∧ y = 4
  deriving Decidable

-- (220), (222), (230)
theorem knowsFifth_row :
    (∀ X : Finset (Fin 5), X.Nonempty → ¬ WeakReciprocity KnowsFifth X) ∧
    ((∀ a ∈ Finset.univ, ∀ b ∈ Finset.univ, a ≠ b → ¬ KnowsFifth a b) ↔
      true ∈ Examples.ex220.verdict) := by
  decide

end Beck2001
