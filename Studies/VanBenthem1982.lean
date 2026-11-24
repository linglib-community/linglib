module

public import Linglib.Semantics.Delineation
public import Linglib.Semantics.Degree.CresswellDegree
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Preorder.Finite

/-!
# van Benthem (1982): Later Than Late

Van Benthem derives the comparative of an adjective from its context-dependent positive form. A
context is a finite set of individuals, and a context structure says which members of each
context count as *A* in it. Two individuals form a difference pair in a context when the first
is *A* there and the second is not, and *x is A-er than y* holds when they form a difference
pair in the context of the two of them alone.

Three principles tie the contexts together. No Reversal forbids a difference pair from being
reversed in another context, and Upward and Downward Difference keep some difference pair in
every larger context and in every smaller one that retains the pair. Under them the comparative
is transitive, irreflexive and almost-connected, and conversely every such relation is the
comparative of a context structure that meets the principles, the one whose contexts count as
*A* their members with nothing above them. A context structure under the principles is a measure
into a linear order and a standard for each context, applied to the members of the context.

## Implementation notes

A context structure is a `Delineation` whose classes classify exactly their own members, and the
principles quantify over finite classes, the paper's contexts. The substrate's consistency
constraint, `Delineation.IsMonotoneOn`, also constrains a class that lacks one of the two
entities: it asks a class that counts the lower entity as *A* to count the higher as *A* too,
which a context without the higher entity cannot do. No Reversal is therefore stated on its own.
The paper's comparative is taken at the two-membered context; its variant that quantifies over
contexts agrees with it under the principles.

The application to the temporal order, where *later than* is the comparative of *late* over
contexts of events, and the tense logic built on it are not formalized.

## References

* [van-benthem-1982]
* [kamp-1975]
-/

@[expose] public section

namespace VanBenthem1982

open Delineation

variable {I : Type*} (d : Delineation I)

/-! ### Context structures and the cross-contextual principles -/

/-- A delineation is a context structure when each context classifies exactly its own members:
those it counts as *A* are in it, and the rest of it is in the negative extension. -/
structure IsContextStructure : Prop where
  /-- What a context counts as *A* is in the context. -/
  pos_subset (c : Set I) : d c ⊆ c
  /-- The negative extension of a context is the rest of it. -/
  neg_eq (c : Set I) : d.neg c = c \ d c

/-- Two individuals form a difference pair in a context when the first is *A* in it and the second
is not. -/
def DifferencePair (c : Set I) (i j : I) : Prop := i ∈ d c ∧ j ∈ d.neg c

/-- No Reversal: no context reverses a difference pair of another. -/
def NoReversal : Prop :=
  ∀ ⦃c i j⦄, c.Finite → DifferencePair d c i j → ∀ ⦃c'⦄, c'.Finite → ¬ DifferencePair d c' j i

/-- Upward Difference: every context that contains one with a difference pair has a difference
pair. -/
def UpwardDifference : Prop :=
  ∀ ⦃c i j⦄, c.Finite → DifferencePair d c i j → ∀ ⦃c'⦄, c'.Finite → c ⊆ c' →
    ∃ i' j', DifferencePair d c' i' j'

/-- Downward Difference: every context inside one with a difference pair, and containing the
pair, has a difference pair. -/
def DownwardDifference : Prop :=
  ∀ ⦃c i j⦄, c.Finite → DifferencePair d c i j → ∀ ⦃c'⦄, c' ⊆ c → i ∈ c' → j ∈ c' →
    ∃ i' j', DifferencePair d c' i' j'

/-- *x is A-er than y* holds when in the context of the two of them `x` is *A* and `y` is not. -/
def More (x y : I) : Prop := DifferencePair d {x, y} x y

variable {d} {c : Set I} {i j k : I}

theorem IsContextStructure.mem_or_mem_neg (h : IsContextStructure d) (hi : i ∈ c) :
    i ∈ d c ∨ i ∈ d.neg c := by
  rw [h.neg_eq]
  exact (em (i ∈ d c)).imp_right fun hi' ↦ ⟨hi, hi'⟩

theorem IsContextStructure.mem_of_mem_neg (h : IsContextStructure d) (hi : i ∈ d.neg c) :
    i ∈ c := by
  rw [h.neg_eq] at hi
  exact hi.1

/-! ### The logic of the comparative -/

-- p. 195: under No Reversal and Downward Difference a difference pair stays one in its own context
theorem more_of_differencePair (h : IsContextStructure d) (hNR : NoReversal d)
    (hDD : DownwardDifference d) (hc : c.Finite) (hij : DifferencePair d c i j) : More d i j := by
  have hi : i ∈ c := h.pos_subset c hij.1
  have hj : j ∈ c := h.mem_of_mem_neg hij.2
  obtain ⟨i', j', hi', hj'⟩ := hDD hc hij (c' := {i, j})
    (Set.insert_subset hi (Set.singleton_subset_iff.2 hj)) (Set.mem_insert _ _)
    (Set.mem_insert_of_mem _ rfl)
  rcases h.pos_subset _ hi' with rfl | rfl <;> rcases h.mem_of_mem_neg hj' with rfl | rfl
  · exact absurd hj' (d.notMem_neg_of_mem hi')
  · exact ⟨hi', hj'⟩
  · exact absurd ⟨hi', hj'⟩ (hNR hc hij (Set.toFinite _))
  · exact absurd hj' (d.notMem_neg_of_mem hi')

-- p. 196: the variant of the comparative that quantifies over contexts
theorem more_iff_exists_differencePair (h : IsContextStructure d) (hNR : NoReversal d)
    (hDD : DownwardDifference d) : More d i j ↔ ∃ c : Set I, c.Finite ∧ DifferencePair d c i j :=
  ⟨fun hij ↦ ⟨{i, j}, Set.toFinite _, hij⟩,
    fun ⟨_, hc, hij⟩ ↦ more_of_differencePair h hNR hDD hc hij⟩

theorem more_irrefl (i : I) : ¬ More d i i := fun h ↦ d.notMem_neg_of_mem h.1 h.2

theorem more_asymm (hNR : NoReversal d) (hij : More d i j) : ¬ More d j i := fun hji ↦ by
  rw [More, Set.pair_comm] at hji
  exact hNR (Set.toFinite _) hij (Set.toFinite _) hji

-- p. 197: almost-connectedness, by cases on the context of the three
theorem more_cotrans (h : IsContextStructure d) (hNR : NoReversal d) (hUD : UpwardDifference d)
    (hDD : DownwardDifference d) (hij : More d i j) (k : I) : More d i k ∨ More d k j := by
  have hT : ({i, j, k} : Set I).Finite := Set.toFinite _
  obtain ⟨a, b, ha, hb⟩ := hUD (Set.toFinite _) hij hT (c' := {i, j, k})
    (Set.insert_subset (Set.mem_insert _ _)
      (Set.singleton_subset_iff.2 (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
  have key : ∀ {x y : I}, DifferencePair d {i, j, k} x y → More d x y :=
    fun hxy ↦ more_of_differencePair h hNR hDD hT hxy
  have hji : ¬ DifferencePair d {i, j, k} j i := hNR (Set.toFinite _) hij hT
  rcases h.mem_or_mem_neg (c := {i, j, k}) (i := k) (by simp) with hk | hk
  · rcases h.mem_or_mem_neg (c := {i, j, k}) (i := j) (by simp) with hj | hj
    · rcases h.mem_or_mem_neg (c := {i, j, k}) (i := i) (by simp) with hi | hi
      · have hb' := h.mem_of_mem_neg hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb'
        rcases hb' with rfl | rfl | rfl
        exacts [absurd hb (d.notMem_neg_of_mem hi), absurd hb (d.notMem_neg_of_mem hj),
          absurd hb (d.notMem_neg_of_mem hk)]
      · exact absurd ⟨hj, hi⟩ hji
    · exact .inr (key ⟨hk, hj⟩)
  · rcases h.mem_or_mem_neg (c := {i, j, k}) (i := i) (by simp) with hi | hi
    · exact .inl (key ⟨hi, hk⟩)
    · rcases h.mem_or_mem_neg (c := {i, j, k}) (i := j) (by simp) with hj | hj
      · exact absurd ⟨hj, hi⟩ hji
      · have ha' := h.pos_subset _ ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha'
        rcases ha' with rfl | rfl | rfl
        exacts [absurd hi (d.notMem_neg_of_mem ha), absurd hj (d.notMem_neg_of_mem ha),
          absurd hk (d.notMem_neg_of_mem ha)]

theorem more_trans (h : IsContextStructure d) (hNR : NoReversal d) (hUD : UpwardDifference d)
    (hDD : DownwardDifference d) (hij : More d i j) (hjk : More d j k) : More d i k :=
  (more_cotrans h hNR hUD hDD hij k).resolve_right (more_asymm hNR hjk)

/-- Under the three principles the comparative is transitive, irreflexive and almost-connected,
a strict weak order. -/
theorem isStrictWeakOrder_more (h : IsContextStructure d) (hNR : NoReversal d)
    (hUD : UpwardDifference d) (hDD : DownwardDifference d) : IsStrictWeakOrder I (More d) where
  irrefl := more_irrefl
  trans _ _ _ := more_trans h hNR hUD hDD
  incomp_trans _ b _ := fun ⟨hab, hba⟩ ⟨hbc, hcb⟩ ↦
    ⟨fun hac ↦ (more_cotrans h hNR hUD hDD hac b).elim hab hbc,
      fun hca ↦ (more_cotrans h hNR hUD hDD hca b).elim hcb hba⟩

/-! ### Every strict weak order is a comparative -/

section OfWeakOrder

variable (R : I → I → Prop)

/-- The context structure of a relation counts as *A* in a context the members that nothing in
the context stands above, its topmost indifference group. -/
def ofWeakOrder : Delineation I where
  pos c := {x | x ∈ c ∧ ∀ y ∈ c, ¬ R y x}
  neg c := {x | x ∈ c ∧ ∃ y ∈ c, R y x}
  disjoint_pos_neg _ := Set.disjoint_left.2 fun _ hx ⟨_, y, hy, hyx⟩ ↦ hx.2 y hy hyx

theorem isContextStructure_ofWeakOrder : IsContextStructure (ofWeakOrder R) where
  pos_subset _ _ hx := hx.1
  neg_eq c := Set.ext fun x ↦ by simp [ofWeakOrder]

variable {R} [IsStrictWeakOrder I R]

omit [IsStrictWeakOrder I R] in
private theorem cotrans_of_isStrictWeakOrder [IsStrictWeakOrder I R] (hij : R i j) (k : I) :
    R i k ∨ R k j := by
  by_contra hn
  obtain ⟨hik, hkj⟩ := not_or.1 hn
  by_cases hki : R k i
  · exact hkj (_root_.trans hki hij)
  by_cases hjk : R j k
  · exact hik (_root_.trans hij hjk)
  exact (IsStrictWeakOrder.incomp_trans i k j ⟨hik, hki⟩ ⟨hkj, hjk⟩).1 hij

theorem rel_of_differencePair_ofWeakOrder (hij : DifferencePair (ofWeakOrder R) c i j) :
    R i j :=
  let ⟨_, k, hk, hkj⟩ := hij.2
  (cotrans_of_isStrictWeakOrder hkj i).resolve_left (hij.1.2 k hk)

theorem exists_differencePair_ofWeakOrder (hc : c.Finite) (hi : i ∈ c) (hj : j ∈ c)
    (hij : R i j) : ∃ i' j', DifferencePair (ofWeakOrder R) c i' j' := by
  let _ := partialOrderOfSO R
  obtain ⟨m, hm, hmin⟩ := hc.exists_minimal ⟨i, hi⟩
  exact ⟨m, j, ⟨hm, fun y hy hym ↦ lt_irrefl y (lt_of_lt_of_le hym (hmin hy (le_of_lt hym)))⟩,
    hj, i, hi, hij⟩

theorem noReversal_ofWeakOrder : NoReversal (ofWeakOrder R) := fun _ _ _ _ hij _ _ hji ↦
  asymm (rel_of_differencePair_ofWeakOrder hij) (rel_of_differencePair_ofWeakOrder hji)

theorem upwardDifference_ofWeakOrder : UpwardDifference (ofWeakOrder R) :=
  fun _ _ _ _ hij _ hc' hcc' ↦ exists_differencePair_ofWeakOrder hc' (hcc' hij.1.1)
    (hcc' hij.2.1) (rel_of_differencePair_ofWeakOrder hij)

theorem downwardDifference_ofWeakOrder : DownwardDifference (ofWeakOrder R) :=
  fun _ _ _ hc hij _ hc' hi hj ↦ exists_differencePair_ofWeakOrder (hc.subset hc') hi hj
    (rel_of_differencePair_ofWeakOrder hij)

/-- Every strict weak order is the comparative of its context structure, which meets the three
principles. -/
theorem more_ofWeakOrder_iff : More (ofWeakOrder R) i j ↔ R i j := by
  refine ⟨rel_of_differencePair_ofWeakOrder, fun hij ↦ ⟨⟨Set.mem_insert _ _, ?_⟩,
    Set.mem_insert_of_mem _ rfl, i, Set.mem_insert _ _, hij⟩⟩
  rintro y (rfl | rfl)
  exacts [irrefl y, asymm hij]

end OfWeakOrder

/-! ### A context structure as a measure and a standard -/

/-- Under the three principles a context structure is given by a measure into a linear order and
a standard for each context: a context counts as *A* its members whose degree meets its standard,
and the comparative is the order of the degrees. -/
theorem exists_eq_inter_ofStandard.{u} {I : Type u} {d : Delineation I}
    (h : IsContextStructure d) (hNR : NoReversal d) (hUD : UpwardDifference d)
    (hDD : DownwardDifference d) :
    ∃ (D : Type u) (_ : LinearOrder D) (m : I → D) (σ : Set I → UpperSet D),
      (∀ c : Set I, c.Finite → d c = c ∩ ofStandard m σ c) ∧ ∀ i j, More d i j ↔ m j < m i := by
  classical
  have := isStrictWeakOrder_more h hNR hUD hDD
  refine ⟨CresswellDegree (More d), inferInstance, fun i ↦ ⟦i⟧,
    fun c ↦ upperClosure ((fun i ↦ (⟦i⟧ : CresswellDegree (More d))) '' d c),
    fun c hc ↦ Set.ext fun x ↦ ⟨fun hx ↦ ⟨h.pos_subset c hx, ⟦x⟧, ⟨x, hx, rfl⟩, le_rfl⟩, ?_⟩,
    fun i j ↦ CresswellDegree.mk_lt_mk.symm⟩
  rintro ⟨hxc, _, ⟨a, ha, rfl⟩, hle⟩
  by_contra hx
  exact not_lt.2 hle (CresswellDegree.mk_lt_mk.2
    (more_of_differencePair h hNR hDD hc ⟨ha, (h.neg_eq c).symm ▸ ⟨hxc, hx⟩⟩))

end VanBenthem1982
