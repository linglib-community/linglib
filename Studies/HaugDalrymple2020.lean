module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Dynamic.PPCDRT
public import Linglib.Semantics.Plurality.Cumulativity
public import Linglib.Semantics.Plurality.Reciprocal
public import Linglib.Logic.Trivalent.Basic

/-!
# Haug and Dalrymple (2020): Reciprocity: Anaphora, scope, and quantification

Haug and Dalrymple give a relational analysis of reciprocity in
Partial Plural Compositional DRT. The reciprocal contributes group identity with its
antecedent and pointwise distinctness ((41), `PPCDRT.reciprocityCond`); the scope
ambiguity of a reciprocal in a complement clause is the ambiguity of any plural anaphor
between group identity (`PPCDRT.groupIdentityCond`) and binding (`PPCDRT.bindingCond`)
with the matrix subject, read through the distribution of §2.3 under which the antecedent
escapes the distribution operator. The sample output states of the paper are transcribed
as plural information states (`ofRows`) and the conditions checked on them: the two
readings of the lawyers' secretary (24), (31), the narrow and wide readings of the girls'
belief (49), (51), (53), (55), the crossed reading (56), the modal (69), the mixed
construal of the Cheyenne affix (78), multiple reciprocals (85), (86), the forks (93), the
sailors (96), and the wide construal with three girls (136).
`no_low_reciprocal_under_binding` derives the empty cell of §3.3: a bound antecedent
leaves no plurality for a reciprocal inside the distribution.

The paper's relation to cumulation is stated in general. Pointwise conditions on plural
states give cumulative readings (§2.1, `cumulative_iff_exists_relCond`), with the truth
conditions of Sternefeld's cumulation operator (§4.1, `cumulation_iff_exists_relCond`).
A simple reciprocal sentence is true exactly when its antecedent is weakly reciprocal under the
verb (§2.4, `weakReciprocity_iff_exists_reciprocalDRS`), which is Sternefeld's reading (76)
(`cumulation_iff_exists_reciprocalDRS`). Without distribution, and whatever the verb, the
dependency between the antecedent and the reciprocal is weakly reciprocal
(`weakReciprocity_dep_of_reciprocityCond`), of which the forks are an instance (`forks_weak`).

Quantified antecedents (§5) get the two readings of (99), `RefSetReading` over a maximal
reciprocal subset and `MaxSetReading` over the participants, and the supervaluation truth
value of (109), `truthValue`, with `maxSetReading_of_refSetReading` for upward monotone
determiners and the street and club scenarios of §5.1–§5.2. Maximize Anaphora (128) is
`MaximizesAnaphora`; it selects the states whose dependency contains every pair the verb
allows (`maximizesAnaphora_iff`), hence Strong Reciprocity when the verb allows every pair
(`strongReciprocity_dep_iff`), the strong reading (126b) over the minimal state (126a)
(`maximize_strong`), and it maximizes multiple reciprocals pairwise (§6.2).

## Implementation notes

* Distribution is represented by the set `Δ` of a `PPCDRT.PPDRSCond`; the operators `δ`,
  `T` and `think` of (14), (46) are not defined, and each sample state is checked under
  the `Δ` its DRS induces. The `max` operator of (97) is likewise replaced by the static
  readings it yields.
* A DRS is true when some output state satisfies its conditions. `relCond` asks every state to
  value its discourse referents, which the partial introduction (6), (20) guarantees: the states
  `PPCDRT.introPartial` reaches from the empty state `{⊥}` are exactly those whose rows value
  the introduced drefs (`introPartial_comp_iff`), and truth reached from `{⊥}` agrees with truth
  at some state (`weakReciprocity_iff_exists_introPartial`).
* `ReciprocalDRS` fixes the antecedent's plurality, `∪u' = X`, as a definite antecedent does;
  (125b) has the pointwise restrictor `boy(u₁)` instead. `boysKnow` takes `X` to be the
  three boys.
* The pairs `R_u` of (127) are the dependency `PCDRT.dep`, taken antecedent first so that
  they line up with the verb's arguments; the order does not affect maximization.
* Worlds are values of the same domain as individuals, at the discourse referent `w`.
* The antecedence condition for the second reciprocal of (85b) is read with `u₂`, as the
  indices of (85a) and the state (85c) give.

## TODO

* The distribution and maximization relations `δ_u` and `max^u` of (14) and (97), so that the
  sample states are derived from the DRSs rather than transcribed; introduction, (6) and (20),
  is `PPCDRT.introPartial`.
* With the pointwise restrictor `∪u' ⊆ A` of (125b) in place of `∪u' = X`, Maximize Anaphora
  selects the states whose dependency is full on a maximal weakly reciprocal subset of `A`,
  the shape of the reference sets of §5 (`IsRefSet`).

## References

* [D. T. T. Haug and M. Dalrymple, *Reciprocity: Anaphora, scope, and quantification*
  (2020)][haug-dalrymple-2020]
* [D. T. Langendoen, *The logic of reciprocity* (1978)][langendoen-1978]
* [W. Sternefeld, *Reciprocity and cumulative predication* (1998)][sternefeld-1998]
* [S. Beck and U. Sauerland, *Cumulation is needed: A reply to Winter (2000)*
  (2000)][beck-sauerland-2000]
* [J. Dotlačil, *Reciprocals distribute over information states* (2013)][dotlacil-2013]
* [S. E. Murray, *Reflexivity and reciprocity with(out) underspecification* (2008)][murray-2008]
* [M. Križ, *Aspects of homogeneity in the semantics of natural language* (2015)][kriz-2015]
* [L. Champollion, D. Bumford and R. Henderson, *Donkeys under discussion*
  (2019)][champollion-bumford-henderson-2019]
-/

@[expose] public section

namespace HaugDalrymple2020

open PPCDRT PCDRT Reciprocal Plurality.Cumulativity

/-! ### Sample states -/

/-- The individuals and worlds of the sample states. -/
inductive Ind where
  | girl1 | girl2
  | tracy | chris | matty
  | world1 | world2 | world3
  | lawyer1 | lawyer2 | lawyer3
  | secretary1 | secretary2 | secretary3
  | picture1 | picture2 | picture3
  | fork1 | fork2 | fork3
  | sailor1 | sailor2 | sailor3
  | ship1 | ship2 | ship3
  | child1 | child2 | child3
  | boy1 | boy2 | boy3
  deriving DecidableEq, Fintype, Repr

/-- The discourse referent `u₁`. -/
abbrev u₁ : ℕ := 1
/-- The discourse referent `u₂`. -/
abbrev u₂ : ℕ := 2
/-- The discourse referent `u₃`. -/
abbrev u₃ : ℕ := 3
/-- The discourse referent `u₄`. -/
abbrev u₄ : ℕ := 4
/-- The world discourse referent `w` of §3.1. -/
abbrev w : ℕ := 5

/-- A row of a sample state, from its defined discourse referents. -/
def row {E : Type*} (l : List (ℕ × E)) : PartialAssign ℕ E :=
  fun u ↦ (l.find? (·.1 == u)).elim ⊥ fun p ↦ ↑p.2

theorem row_pair_left {E : Type*} (u v : ℕ) (a b : E) : row [(u, a), (v, b)] u = ↑a := by
  simp [row]

theorem row_pair_right {E : Type*} {u v : ℕ} (h : u ≠ v) (a b : E) :
    row [(u, a), (v, b)] v = ↑b := by
  simp [row, h]

/-- The plural information state with the given rows. -/
def ofRows (rows : List (PartialAssign ℕ Ind)) : PluralAssign ℕ Ind := {g | g ∈ rows}

section Rows

variable {rows : List (PartialAssign ℕ Ind)} {Δ : Set ℕ} {Δl : List ℕ} {u u' : ℕ}

theorem bindingCond_ofRows : bindingCond u u' (ofRows rows) Δ ↔ ∀ s ∈ rows, s u = s u' := by
  simp [bindingCond, ofRows]

theorem groupIdentityCond_ofRows (hΔ : ∀ v, v ∈ Δ ↔ v ∈ Δl) :
    groupIdentityCond u u' (ofRows rows) Δ ↔
      ∀ s ∈ rows, ∀ d : Ind, (∃ t ∈ rows, (∀ v ∈ Δl, t v = s v) ∧ t u = ↑d) ↔
        ∃ t ∈ rows, t u' = ↑d := by
  simp [groupIdentityCond, eqClass, ofRows, value, Set.ext_iff, hΔ, and_assoc]

theorem distinct_ofRows :
    (∀ s ∈ ofRows rows, ∀ a b : Ind, s u = ↑a → s u' = ↑b → a ≠ b) ↔
      ∀ s ∈ rows, ∀ a b : Ind, s u = ↑a → s u' = ↑b → a ≠ b := by
  simp [ofRows]

theorem reciprocityCond_ofRows (hΔ : ∀ v, v ∈ Δ ↔ v ∈ Δl) :
    reciprocityCond u u' (ofRows rows) Δ ↔
      (∀ s ∈ rows, ∀ d : Ind, (∃ t ∈ rows, (∀ v ∈ Δl, t v = s v) ∧ t u = ↑d) ↔
        ∃ t ∈ rows, t u' = ↑d) ∧
      ∀ s ∈ rows, ∀ a b : Ind, s u = ↑a → s u' = ↑b → a ≠ b :=
  and_congr (groupIdentityCond_ofRows hΔ) distinct_ofRows

theorem mem_dep_ofRows {a b : Ind} :
    (a, b) ∈ dep u u' (ofRows rows) ↔ ∃ s ∈ rows, s u = ↑a ∧ s u' = ↑b := by
  simp [dep, ofRows]

theorem mem_dep_eqClass_ofRows (hΔ : ∀ v, v ∈ Δ ↔ v ∈ Δl) {s : PartialAssign ℕ Ind}
    {a b : Ind} :
    (a, b) ∈ dep u u' (eqClass (ofRows rows) Δ s) ↔
      ∃ t ∈ rows, (∀ v ∈ Δl, t v = s v) ∧ t u = ↑a ∧ t u' = ↑b := by
  simp [dep, eqClass, ofRows, hΔ, and_assoc]

/-- The values of `u` summed over the `Δ`-class of `s`, as a finset. -/
def sumRows (rows : List (PartialAssign ℕ Ind)) (Δl : List ℕ) (s : PartialAssign ℕ Ind)
    (u : ℕ) : Finset Ind :=
  Finset.univ.filter fun d ↦ ∃ t ∈ rows, (∀ v ∈ Δl, t v = s v) ∧ t u = ↑d

theorem coe_sumRows (hΔ : ∀ v, v ∈ Δ ↔ v ∈ Δl) (s : PartialAssign ℕ Ind) :
    (↑(sumRows rows Δl s u) : Set Ind) =
      value u (eqClass (ofRows rows) Δ s) := by
  ext d
  simp [sumRows, value, eqClass, ofRows, hΔ, and_assoc]

theorem mem_ofRows {s : PartialAssign ℕ Ind} : s ∈ ofRows rows ↔ s ∈ rows := Iff.rfl

theorem value_ofRows : value u (ofRows rows) = ↑(sumRows rows [] (row []) u) := by
  rw [coe_sumRows (Δ := ∅) (by simp), eqClass_empty]

end Rows

/-- The collective condition `n-atoms(∪u)` of (9) under distribution holds when, in every
state, the values of `u` summed over the state's class number `n` ((27), (28b)). -/
def atomsCond (n : ℕ) (u : ℕ) : PPDRSCond Ind := fun S Δ ↦
  ∀ s ∈ S, (value u (eqClass S Δ s)).ncard = n

theorem atomsCond_ofRows {rows : List (PartialAssign ℕ Ind)} {Δ : Set ℕ} {Δl : List ℕ}
    {n u : ℕ} (hΔ : ∀ v, v ∈ Δ ↔ v ∈ Δl) :
    atomsCond n u (ofRows rows) Δ ↔ ∀ s ∈ rows, (sumRows rows Δl s u).card = n := by
  have key : ∀ s, (value u (eqClass (ofRows rows) Δ s)).ncard =
      (sumRows rows Δl s u).card :=
    fun s ↦ by rw [← coe_sumRows hΔ, Set.ncard_coe_finset]
  simp only [atomsCond, key]
  exact Iff.rfl

/-- A lexical relation as a condition ((7), (27)) holds when the state is nonempty and every
state gives `u` and `v` values that `P` relates. Distribution does not reach individual discourse
referents, so `Δ` is idle. -/
def relCond {E : Type*} (P : E → E → Prop) (u v : ℕ) : PPDRSCond E := fun S _ ↦
  S.Nonempty ∧ ∀ s ∈ S, ∃ a b : E, s u = ↑a ∧ s v = ↑b ∧ P a b

theorem relCond_ofRows {P : Ind → Ind → Prop} {rows : List (PartialAssign ℕ Ind)} {Δ : Set ℕ}
    {u v : ℕ} :
    relCond P u v (ofRows rows) Δ ↔
      rows ≠ [] ∧ ∀ s ∈ rows, ∃ a b : Ind, s u = ↑a ∧ s v = ↑b ∧ P a b :=
  and_congr ⟨fun ⟨_, hs⟩ ↦ List.ne_nil_of_mem hs, List.exists_mem_of_ne_nil _⟩ Iff.rfl

/-- Group identity read inside the distribution operator of (14), summing both sides over
the class. This is the reading under which (23b) is not representable (§2.3). -/
def distributedGroupIdentityCond (uAnaph uAnt : ℕ) : PPDRSCond Ind := fun S Δ ↦
  ∀ s ∈ S, value uAnaph (eqClass S Δ s) = value uAnt (eqClass S Δ s)

theorem distributedGroupIdentityCond_ofRows {rows : List (PartialAssign ℕ Ind)} {Δ : Set ℕ}
    {Δl : List ℕ} {u u' : ℕ} (hΔ : ∀ v, v ∈ Δ ↔ v ∈ Δl) :
    distributedGroupIdentityCond u u' (ofRows rows) Δ ↔
      ∀ s ∈ rows, ∀ d : Ind, (∃ t ∈ rows, (∀ v ∈ Δl, t v = s v) ∧ t u = ↑d) ↔
        ∃ t ∈ rows, (∀ v ∈ Δl, t v = s v) ∧ t u' = ↑d := by
  simp [distributedGroupIdentityCond, eqClass, ofRows, value, Set.ext_iff, hΔ,
    and_assoc]

/-! ### Anaphora under distribution (§2.3) -/

/-- The lawyers hired secretaries they each liked, `u₃` bound to `u₁` (24c). -/
def lawyersBound : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .lawyer1), (u₂, .secretary1), (u₃, .lawyer1)],
   row [(u₁, .lawyer2), (u₂, .secretary2), (u₃, .lawyer2)],
   row [(u₁, .lawyer3), (u₂, .secretary3), (u₃, .lawyer3)]]

/-- The lawyers hired secretaries all of them liked, `∪u₃ → ∪u₁` under `δ_{u₁}` (31c). -/
def lawyersGroup : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .lawyer1), (u₂, .secretary1), (u₃, .lawyer1)],
   row [(u₁, .lawyer1), (u₂, .secretary1), (u₃, .lawyer2)],
   row [(u₁, .lawyer1), (u₂, .secretary1), (u₃, .lawyer3)],
   row [(u₁, .lawyer2), (u₂, .secretary2), (u₃, .lawyer1)],
   row [(u₁, .lawyer2), (u₂, .secretary2), (u₃, .lawyer2)],
   row [(u₁, .lawyer2), (u₂, .secretary2), (u₃, .lawyer3)],
   row [(u₁, .lawyer3), (u₂, .secretary3), (u₃, .lawyer1)],
   row [(u₁, .lawyer3), (u₂, .secretary3), (u₃, .lawyer2)],
   row [(u₁, .lawyer3), (u₂, .secretary3), (u₃, .lawyer3)]]

private theorem mem_u₁ : ∀ v, v ∈ ({u₁} : Set ℕ) ↔ v ∈ [u₁] := by simp

private theorem mem_empty : ∀ v, v ∈ (∅ : Set ℕ) ↔ v ∈ ([] : List ℕ) := by simp

/-- Read as (24), (23a) has `they` bound by `the lawyers`, one secretary per lawyer under
`δ_{u₁}`, and no group identity under the distribution. -/
theorem lawyers_bound :
    bindingCond u₃ u₁ (ofRows lawyersBound) {u₁} ∧
      atomsCond 1 u₂ (ofRows lawyersBound) {u₁} ∧
      ¬ groupIdentityCond u₃ u₁ (ofRows lawyersBound) {u₁} := by
  rw [bindingCond_ofRows, atomsCond_ofRows mem_u₁, groupIdentityCond_ofRows mem_u₁]
  decide

/-- Read as (31), (23b) has group identity without binding and one secretary per lawyer, but fails
group identity under the distribution operator of (14) (§2.3). -/
theorem lawyers_group :
    groupIdentityCond u₃ u₁ (ofRows lawyersGroup) {u₁} ∧
      atomsCond 1 u₂ (ofRows lawyersGroup) {u₁} ∧
      ¬ bindingCond u₃ u₁ (ofRows lawyersGroup) {u₁} ∧
      ¬ atomsCond 1 u₂ (ofRows lawyersGroup) ∅ ∧
      ¬ distributedGroupIdentityCond u₃ u₁ (ofRows lawyersGroup) {u₁} := by
  rw [groupIdentityCond_ofRows mem_u₁, atomsCond_ofRows mem_u₁, bindingCond_ofRows,
    atomsCond_ofRows mem_empty, distributedGroupIdentityCond_ofRows mem_u₁]
  decide

/-! ### Cumulative readings and Weak Reciprocity (§1, §2.1, §2.4, §4.1) -/

section Cumulativity

variable {E : Type*} {P : E → E → Prop} {u v : ℕ} {S : PluralAssign ℕ E} {D : SetRel E E}

/-- The state with a row for each pair of `D`, valuing `u` and `v` as its two components, so
that its dependency between `u` and `v` is `D`. -/
def ofDep (u v : ℕ) (D : SetRel E E) : PluralAssign ℕ E :=
  (fun p ↦ row [(u, p.1), (v, p.2)]) '' D

theorem dep_ofDep (h : u ≠ v) (D : SetRel E E) : dep u v (ofDep u v D) = D := by
  ext ⟨a, b⟩
  refine ⟨?_, fun hab ↦ ⟨_, ⟨(a, b), hab, rfl⟩, row_pair_left u v a b, row_pair_right h a b⟩⟩
  rintro ⟨_, ⟨⟨a', b'⟩, hab, rfl⟩, ha, hb⟩
  change row [(u, a'), (v, b')] u = ↑a at ha
  change row [(u, a'), (v, b')] v = ↑b at hb
  rw [row_pair_left, Flat.coe_inj] at ha
  rw [row_pair_right h, Flat.coe_inj] at hb
  subst ha hb
  exact hab

theorem relCond_ofDep (h : u ≠ v) (hD : D ⊆ {p | P p.1 p.2}) (hne : D.Nonempty) :
    relCond P u v (ofDep u v D) ∅ :=
  ⟨hne.image _, by
    rintro _ ⟨⟨a, b⟩, hab, rfl⟩
    exact ⟨a, b, row_pair_left u v a b, row_pair_right h a b, hD hab⟩⟩

theorem dep_of_relCond {Δ : Set ℕ} (hS : relCond P u v S Δ) :
    dep u v S ⊆ {p | P p.1 p.2} ∧ (dep u v S).dom = value u S ∧ (dep u v S).cod = value v S := by
  obtain ⟨-, hP⟩ := hS
  refine ⟨?_, dom_dep fun s hs _ ↦ ?_, cod_dep fun s hs _ ↦ ?_⟩
  · rintro ⟨a, b⟩ ⟨s, hs, (ha : s u = ↑a), (hb : s v = ↑b)⟩
    obtain ⟨a', b', ha', hb', hab⟩ := hP s hs
    rw [ha', Flat.coe_inj] at ha
    rw [hb', Flat.coe_inj] at hb
    exact ha ▸ hb ▸ hab
  · obtain ⟨-, b, -, hb, -⟩ := hP s hs
    show s v ≠ ⊥
    simp [hb]
  · obtain ⟨a, -, ha, -, -⟩ := hP s hs
    show s u ≠ ⊥
    simp [ha]

theorem value_ofDep_left (h : u ≠ v) (D : SetRel E E) : value u (ofDep u v D) = D.dom := by
  rw [← dom_dep (v := v), dep_ofDep h]
  rintro _ ⟨p, -, rfl⟩ -
  show row _ v ≠ ⊥
  simp [row_pair_right h]

theorem value_ofDep_right (h : u ≠ v) (D : SetRel E E) : value v (ofDep u v D) = D.cod := by
  rw [← cod_dep (u := u), dep_ofDep h]
  rintro _ ⟨p, -, rfl⟩ -
  show row _ u ≠ ⊥
  simp [row_pair_left]

/-- A state satisfying `P(u, v)` relates the values of `u` and `v` cumulatively, and every
cumulative pair arises so (§2.1, (12), [beck-sauerland-2000]). -/
theorem cumulative_iff_exists_relCond (h : u ≠ v) {x y : Set E} :
    x.Nonempty ∧ Set.LiftRel P x y ↔
      ∃ S : PluralAssign ℕ E, value u S = x ∧ value v S = y ∧ relCond P u v S ∅ := by
  rw [Set.liftRel_iff_exists_dom_cod]
  constructor
  · rintro ⟨⟨a, ha⟩, D, hD, rfl, rfl⟩
    obtain ⟨b, hab⟩ := ha
    exact ⟨ofDep u v D, value_ofDep_left h D, value_ofDep_right h D, relCond_ofDep h hD ⟨_, hab⟩⟩
  · rintro ⟨S, rfl, rfl, hS⟩
    obtain ⟨hP, hdom, hcod⟩ := dep_of_relCond hS
    obtain ⟨s, hs⟩ := hS.1
    obtain ⟨a, -, ha, -⟩ := hS.2 s hs
    exact ⟨⟨a, s, hs, ha⟩, dep u v S, hP, hdom, hcod⟩

/-- By §4.1, (75), the cumulation operator `**` that [sternefeld-1998] applies to the predicate and
the pointwise conditions of Plural CDRT give the same truth conditions. -/
theorem cumulation_iff_exists_relCond [DecidableEq E] (h : u ≠ v) {x y : Finset E} :
    Cumulation (Relation.Map P ({·}) ({·})) x y ↔
      ∃ S : PluralAssign ℕ E, value u S = ↑x ∧ value v S = ↑y ∧ relCond P u v S ∅ := by
  rw [cumulation_map_singleton, ← Finset.coe_nonempty, cumulative_iff_exists_relCond h]

/-- In the DRS of a reciprocal sentence whose antecedent denotes `X`, as in (40b) and (125b),
the antecedent `u'` sums to `X`, `P` relates `u'` to the reciprocal `u` in every state, and `u`
is reciprocal to `u'` ((42)). -/
def ReciprocalDRS (P : E → E → Prop) (X : Set E) (u u' : ℕ) (S : PluralAssign ℕ E) : Prop :=
  value u' S = X ∧ relCond P u' u S ∅ ∧ reciprocityCond u u' S ∅

theorem reciprocalDRS_iff {X : Set E} {u' : ℕ} :
    ReciprocalDRS P X u u' S ↔
      value u' S = X ∧ value u S = X ∧ relCond (fun a b ↦ P a b ∧ a ≠ b) u' u S ∅ := by
  simp only [ReciprocalDRS, reciprocityCond, groupIdentityCond_empty]
  constructor
  · rintro ⟨hX, ⟨hne, hP⟩, hgi, hd⟩
    refine ⟨hX, hgi.trans hX, hne, fun s hs ↦ ?_⟩
    obtain ⟨a, b, ha, hb, hab⟩ := hP s hs
    exact ⟨a, b, ha, hb, hab, (hd s hs b a hb ha).symm⟩
  · rintro ⟨hX, hX', hne, hP⟩
    refine ⟨hX, ⟨hne, fun s hs ↦ ?_⟩, hX'.trans hX.symm, fun s hs b a hb ha ↦ ?_⟩
    · obtain ⟨a, b, ha, hb, hab, -⟩ := hP s hs
      exact ⟨a, b, ha, hb, hab⟩
    · obtain ⟨a', b', ha', hb', -, hne'⟩ := hP s hs
      rw [ha', Flat.coe_inj] at ha
      rw [hb', Flat.coe_inj] at hb
      exact ha ▸ hb ▸ hne'.symm

/-- Some state verifies the DRS of *the Xs `P` each other* exactly when `X` is weakly reciprocal
under `P` (§2.4, §1, [langendoen-1978]). -/
theorem weakReciprocity_iff_exists_reciprocalDRS {u' : ℕ} (h : u ≠ u') {X : Finset E} :
    X.Nonempty ∧ WeakReciprocity P X ↔ ∃ S, ReciprocalDRS P ↑X u u' S := by
  rw [weakReciprocity_iff_liftRel, ← Finset.coe_nonempty,
    cumulative_iff_exists_relCond h.symm]
  simp only [reciprocalDRS_iff]

/-- [sternefeld-1998]'s weak reciprocal (76) and the PPCDRT reciprocal (42) agree on simple
reciprocal sentences (§4.1). -/
theorem cumulation_iff_exists_reciprocalDRS [DecidableEq E] {u' : ℕ} (h : u ≠ u')
    {X : Finset E} :
    Cumulation (Relation.Map (fun a b ↦ P a b ∧ a ≠ b) ({·}) ({·})) X X ↔
      ∃ S, ReciprocalDRS P ↑X u u' S := by
  rw [cumulation_map_singleton, ← weakReciprocity_iff_liftRel,
    weakReciprocity_iff_exists_reciprocalDRS h]

section Truth

open SetRel

variable {u' : ℕ} {O : PluralAssign ℕ E}

/-- Introducing `u'` and then `u` at `{⊥}` ((6), (20)) reaches exactly the nonempty states defined
on `u'` and `u` alone. -/
theorem introPartial_comp_iff (h : u ≠ u') :
    ({⊥} : PluralAssign ℕ E) ~[introPartial u' ○ introPartial u] O ↔
      O.Nonempty ∧ ∀ o ∈ O, ∀ v, o v ≠ ⊥ ↔ v = u' ∨ v = u := by
  constructor
  · rintro ⟨K, ⟨-, -, hK⟩, hO, -, hback⟩
    refine ⟨hO, fun o ho v ↦ ?_⟩
    obtain ⟨k, hk, hext⟩ := hback o ho
    obtain ⟨-, hou, hko⟩ := mem_extend.1 hext
    obtain ⟨_, rfl, hext'⟩ := hK k hk
    obtain ⟨-, hku', hk'⟩ := mem_extend.1 hext'
    by_cases hvu : v = u
    · subst hvu
      exact iff_of_true hou (Or.inr rfl)
    rw [← hko v hvu]
    by_cases hvu' : v = u'
    · subst hvu'
      exact iff_of_true hku' (Or.inl rfl)
    rw [← hk' v hvu']
    simp [hvu, hvu']
  · rintro ⟨⟨o₀, ho₀⟩, hdom⟩
    have hdef : ∀ o ∈ O, o u' ≠ ⊥ ∧ o u ≠ ⊥ := fun o ho ↦
      ⟨(hdom o ho u').2 (Or.inl rfl), (hdom o ho u).2 (Or.inr rfl)⟩
    set k : PartialAssign ℕ E → PartialAssign ℕ E := fun o ↦ Function.update ⊥ u' (o u')
    have hk : ∀ o ∈ O, (⊥ : PartialAssign ℕ E) ~[extend u'] k o := fun o ho ↦
      mem_extend.2 ⟨rfl, by simpa [k] using (hdef o ho).1,
        fun v hv ↦ by simp [k, Function.update_of_ne hv]⟩
    have hko : ∀ o ∈ O, k o ~[extend u] o := fun o ho ↦ by
      refine mem_extend.2 ⟨by simp [k, Function.update_of_ne h], (hdef o ho).2, fun v hv ↦ ?_⟩
      by_cases hvu' : v = u'
      · subst hvu'
        simp [k]
      · have : o v = ⊥ := not_not.1 fun hne ↦ ((hdom o ho v).1 hne).elim hvu' hv
        simp [k, Function.update_of_ne hvu', this]
    refine ⟨k '' O, ⟨⟨_, o₀, ho₀, rfl⟩, fun i hi ↦ ?_, ?_⟩, ⟨o₀, ho₀⟩, ?_, ?_⟩
    · obtain rfl := hi
      exact ⟨_, ⟨o₀, ho₀, rfl⟩, hk o₀ ho₀⟩
    · rintro _ ⟨o, ho, rfl⟩
      exact ⟨⊥, rfl, hk o ho⟩
    · rintro _ ⟨o, ho, rfl⟩
      exact ⟨o, ho, hko o ho⟩
    · exact fun o ho ↦ ⟨k o, ⟨o, ho, rfl⟩, hko o ho⟩

/-- After introducing `u'` and `u` at `{⊥}` ((6), (20)), the DRS of *the Xs `P` each other* is
verifiable exactly when `X` is weakly reciprocal. -/
theorem weakReciprocity_iff_exists_introPartial (h : u ≠ u') {X : Finset E} :
    X.Nonempty ∧ WeakReciprocity P X ↔
      ∃ O, ({⊥} : PluralAssign ℕ E) ~[introPartial u' ○ introPartial u] O ∧
        ReciprocalDRS P ↑X u u' O := by
  rw [weakReciprocity_iff_exists_reciprocalDRS h]
  refine ⟨fun ⟨S, hS⟩ ↦ ?_, fun ⟨O, _, hO⟩ ↦ ⟨O, hO⟩⟩
  obtain ⟨hX, hX', hne, hP⟩ := reciprocalDRS_iff.1 hS
  set r : PartialAssign ℕ E → PartialAssign ℕ E := fun s v ↦ if v = u' ∨ v = u then s v else ⊥
  have hr : ∀ s v, (v = u' ∨ v = u) → r s v = s v := fun _ _ hv ↦ ite_eq_left hv
  have hval : ∀ w, (w = u' ∨ w = u) → value w (r '' S) = value w S := fun w hw ↦ by
    ext x
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, hx⟩
      exact ⟨s, hs, (hr s w hw).symm.trans hx⟩
    · rintro ⟨s, hs, hx⟩
      exact ⟨r s, ⟨s, hs, rfl⟩, (hr s w hw).trans hx⟩
  refine ⟨r '' S, (introPartial_comp_iff h).2 ⟨hne.image r, ?_⟩,
    reciprocalDRS_iff.2 ⟨(hval u' (.inl rfl)).trans hX, (hval u (.inr rfl)).trans hX',
      hne.image r, ?_⟩⟩
  · rintro _ ⟨s, hs, rfl⟩ v
    obtain ⟨a, b, ha, hb, -⟩ := hP s hs
    by_cases hv : v = u' ∨ v = u
    · rw [hr s v hv]
      refine iff_of_true ?_ hv
      rcases hv with rfl | rfl
      · rw [ha]; exact Flat.coe_ne_bot
      · rw [hb]; exact Flat.coe_ne_bot
    · simp [r, hv]
  · rintro _ ⟨s, hs, rfl⟩
    obtain ⟨a, b, ha, hb, hab⟩ := hP s hs
    exact ⟨a, b, (hr s u' (.inl rfl)).trans ha, (hr s u (.inr rfl)).trans hb, hab⟩

end Truth

/-- Without distribution, the dependency between antecedent and reciprocal is weakly reciprocal on
the antecedent's plurality, whatever the verb (§2.4, §4.5, cf. (92)). -/
theorem weakReciprocity_dep_of_reciprocityCond {u' : ℕ} {X : Finset E}
    (hdef : ∀ s ∈ S, s u ≠ ⊥ ↔ s u' ≠ ⊥) (hX : value u' S = ↑X)
    (h : reciprocityCond u u' S ∅) : WeakReciprocity (fun a b ↦ (a, b) ∈ dep u' u S) X := by
  obtain ⟨hdc, hirr⟩ := (reciprocityCond_empty_iff hdef).1 h
  have hdom : (dep u' u S).dom = ↑X := (dom_dep fun s hs ↦ (hdef s hs).2).trans hX
  have hcod : (dep u' u S).cod = ↑X := hdc ▸ hdom
  refine ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · obtain ⟨b, hab⟩ : a ∈ (dep u' u S).dom := hdom ▸ Finset.mem_coe.2 ha
    exact ⟨b, Finset.mem_coe.1 (hcod ▸ ⟨a, hab⟩), hab, fun e ↦ hirr.irrefl a (e ▸ hab)⟩
  · obtain ⟨a, hab⟩ : b ∈ (dep u' u S).cod := hcod ▸ Finset.mem_coe.2 hb
    exact ⟨a, Finset.mem_coe.1 (hdom ▸ ⟨b, hab⟩), hab, fun e ↦ hirr.irrefl b (e ▸ hab)⟩

end Cumulativity

/-! ### Reciprocal scope (§3) -/

private theorem mem_u₁w : ∀ v, v ∈ ({u₁, w} : Set ℕ) ↔ v ∈ [u₁, w] := by simp

private theorem mem_w : ∀ v, v ∈ ({w} : Set ℕ) ↔ v ∈ [w] := by simp

/-- Each girl thought "we will win", `∪u₂ → ∪u₁` under `δ_w` (49). -/
def girlsNarrow : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .girl1), (w, .world1), (u₂, .girl1)],
   row [(u₁, .girl1), (w, .world1), (u₂, .girl2)],
   row [(u₁, .girl2), (w, .world2), (u₂, .girl1)],
   row [(u₁, .girl2), (w, .world2), (u₂, .girl2)]]

/-- Each girl thought "I will win", `u₂ → u₁` (51). -/
def girlsWide : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .girl1), (w, .world1), (u₂, .girl1)],
   row [(u₁, .girl2), (w, .world2), (u₂, .girl2)]]

/-- Under the distribution induced by the attitude verb, (49) has group identity without binding and
(51) binding without group identity, the two readings of (44) (§3.1). -/
theorem win_readings :
    (groupIdentityCond u₂ u₁ (ofRows girlsNarrow) {u₁, w} ∧
        ¬ bindingCond u₂ u₁ (ofRows girlsNarrow) {u₁, w}) ∧
      bindingCond u₂ u₁ (ofRows girlsWide) {u₁, w} ∧
        ¬ groupIdentityCond u₂ u₁ (ofRows girlsWide) {u₁, w} := by
  rw [groupIdentityCond_ofRows mem_u₁w, bindingCond_ofRows, bindingCond_ofRows,
    groupIdentityCond_ofRows mem_u₁w]
  decide

/-- Each girl thought "we saw each other", the reciprocal inside the belief (53). -/
def sawNarrow : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .girl1), (w, .world1), (u₂, .girl1), (u₃, .girl2)],
   row [(u₁, .girl1), (w, .world1), (u₂, .girl2), (u₃, .girl1)],
   row [(u₁, .girl2), (w, .world2), (u₂, .girl1), (u₃, .girl2)],
   row [(u₁, .girl2), (w, .world2), (u₂, .girl2), (u₃, .girl1)]]

/-- Each girl thought "I saw her", the reciprocal and its antecedent lifted to the matrix DRS
(55). -/
def sawWide : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .girl1), (u₂, .girl1), (u₃, .girl2), (w, .world1)],
   row [(u₁, .girl2), (u₂, .girl2), (u₃, .girl1), (w, .world2)]]

/-- In the crossed reading of (56), girl1 thought girl2 saw girl1 and girl2 thought girl1
saw girl2. -/
def sawCrossed : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .girl1), (u₂, .girl2), (u₃, .girl1), (w, .world1)],
   row [(u₁, .girl2), (u₂, .girl1), (u₃, .girl2), (w, .world2)]]

/-- By §3.2, (53) satisfies (52), group identity of the pronoun and reciprocity of the
reciprocal under the distribution. -/
theorem saw_narrow :
    groupIdentityCond u₂ u₁ (ofRows sawNarrow) {u₁, w} ∧
      reciprocityCond u₃ u₂ (ofRows sawNarrow) {u₁, w} := by
  rw [groupIdentityCond_ofRows mem_u₁w, reciprocityCond_ofRows mem_u₁w]
  decide

/-- By §3.2, (55) satisfies (54), binding of the pronoun and reciprocity in the matrix. -/
theorem saw_wide :
    bindingCond u₂ u₁ (ofRows sawWide) ∅ ∧
      reciprocityCond u₃ u₂ (ofRows sawWide) ∅ := by
  rw [bindingCond_ofRows, reciprocityCond_ofRows mem_empty]
  decide

/-- By §3.3, the crossed state satisfies (56), group identity of the pronoun with reciprocity
in the matrix, but not the binding of (54). -/
theorem saw_crossed :
    groupIdentityCond u₂ u₁ (ofRows sawCrossed) ∅ ∧
      reciprocityCond u₃ u₂ (ofRows sawCrossed) ∅ ∧
      ¬ bindingCond u₂ u₁ (ofRows sawCrossed) ∅ := by
  rw [groupIdentityCond_ofRows mem_empty, reciprocityCond_ofRows mem_empty, bindingCond_ofRows]
  decide

/-- A bound antecedent cannot cooccur with a low reciprocal (§3.3). -/
theorem no_low_reciprocal_under_binding {E : Type*} {S : PluralAssign ℕ E} {Δ : Set ℕ}
    {v₁ v₂ v₃ : ℕ} (hΔ : v₁ ∈ Δ) (hb : bindingCond v₂ v₁ S Δ)
    (hr : reciprocityCond v₃ v₂ S Δ) {s : PartialAssign ℕ E} (hs : s ∈ S) {d : E}
    (hd : s v₂ = ↑d) : False := by
  have hmem : d ∈ value v₂ S := ⟨s, hs, hd⟩
  rw [← hr.1 s hs] at hmem
  obtain ⟨t, ⟨ht, hcls⟩, ht₃⟩ := hmem
  have ht₂ : t v₂ = ↑d := by rw [hb t ht, hcls v₁ hΔ, ← hb s hs, hd]
  exact hr.2 t ht d d ht₃ ht₂ rfl

/-- Example (69) distributed over two accessible worlds, with the reciprocal lifted above `◇`. -/
def beatModal : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .tracy), (u₂, .chris), (w, .world1)],
   row [(u₁, .chris), (u₂, .tracy), (w, .world1)],
   row [(u₁, .tracy), (u₂, .chris), (w, .world2)],
   row [(u₁, .chris), (u₂, .tracy), (w, .world2)]]

/-- By §3.4, with the reciprocal above the modal, every accessible world contains both
directions of `beat`, the contradiction that makes (64) strange. -/
theorem beat_modal :
    reciprocityCond u₂ u₁ (ofRows beatModal) ∅ ∧
      ∀ s ∈ beatModal,
        (Ind.tracy, Ind.chris) ∈ dep u₁ u₂ (eqClass (ofRows beatModal) {w} s) ∧
          (Ind.chris, Ind.tracy) ∈ dep u₁ u₂ (eqClass (ofRows beatModal) {w} s) := by
  rw [reciprocityCond_ofRows mem_empty]
  simp only [mem_dep_eqClass_ofRows mem_w]
  decide

/-! ### Underspecification, multiple reciprocals, subgroups, collectives (§4) -/

/-- The mixed construal of the Cheyenne affix (78c) has one child scratching herself and two
scratching each other. -/
def scratchMixed : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .child1), (u₂, .child1)],
   row [(u₁, .child2), (u₂, .child3)],
   row [(u₁, .child3), (u₂, .child2)]]

/-- By §4.2, the mixed construal satisfies the underspecified meaning (79b) but neither
reciprocity nor reflexive binding. -/
theorem scratch_mixed :
    underspecifiedCond u₂ u₁ (ofRows scratchMixed) ∅ ∧
      ¬ reciprocityCond u₂ u₁ (ofRows scratchMixed) ∅ ∧
      ¬ bindingCond u₂ u₁ (ofRows scratchMixed) ∅ := by
  rw [underspecifiedCond, groupIdentityCond_ofRows mem_empty, reciprocityCond_ofRows mem_empty,
    bindingCond_ofRows]
  decide

/-- Each girl gave the other a picture of herself, the second reciprocal anteceded by the
first (85c). -/
def picturesSecond : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .girl1), (u₂, .girl2), (u₃, .picture1), (u₄, .girl1)],
   row [(u₁, .girl2), (u₂, .girl1), (u₃, .picture2), (u₄, .girl2)]]

/-- Each girl gave the other a picture of the other, both reciprocals anteceded by the
subject (86c). -/
def picturesSubject : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .girl1), (u₂, .girl2), (u₃, .picture1), (u₄, .girl2)],
   row [(u₁, .girl2), (u₂, .girl1), (u₃, .picture2), (u₄, .girl1)]]

/-- The two readings of (84) give the second reciprocal different antecedents, and each state fails
the other's distinctness condition (§4.4). -/
theorem pictures_readings :
    (reciprocityCond u₂ u₁ (ofRows picturesSecond) ∅ ∧
        reciprocityCond u₄ u₂ (ofRows picturesSecond) ∅ ∧
        ¬ reciprocityCond u₄ u₁ (ofRows picturesSecond) ∅) ∧
      reciprocityCond u₂ u₁ (ofRows picturesSubject) ∅ ∧
        reciprocityCond u₄ u₁ (ofRows picturesSubject) ∅ ∧
        ¬ reciprocityCond u₄ u₂ (ofRows picturesSubject) ∅ := by
  rw [reciprocityCond_ofRows mem_empty, reciprocityCond_ofRows mem_empty,
    reciprocityCond_ofRows mem_empty, reciprocityCond_ofRows mem_empty,
    reciprocityCond_ofRows mem_empty, reciprocityCond_ofRows mem_empty]
  exact ⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide⟩

/-- The forks propped against each other, each on one other (93). -/
def forks : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .fork1), (u₂, .fork2)],
   row [(u₁, .fork2), (u₂, .fork3)],
   row [(u₁, .fork3), (u₂, .fork1)]]

/-- The three forks. -/
def threeForks : Finset Ind := {.fork1, .fork2, .fork3}

/-- The minimal forks state (93) is reciprocal, with a dependency weakly but not strongly reciprocal
on the three forks (§4.5). -/
theorem forks_weak :
    reciprocityCond u₂ u₁ (ofRows forks) ∅ ∧
      WeakReciprocity (fun a b ↦ (a, b) ∈ dep u₁ u₂ (ofRows forks)) threeForks ∧
      ¬ StrongReciprocity (fun a b ↦ (a, b) ∈ dep u₁ u₂ (ofRows forks)) threeForks := by
  have hr : reciprocityCond u₂ u₁ (ofRows forks) ∅ := by
    rw [reciprocityCond_ofRows mem_empty]; decide
  refine ⟨hr, weakReciprocity_dep_of_reciprocityCond (by simp only [mem_ofRows]; decide)
    (by rw [value_ofRows]; exact Finset.coe_inj.2 (by decide)) hr, ?_⟩
  rw [strongReciprocity_iff]
  simp only [mem_dep_ofRows]
  decide

/-- The sailors worked together on each other's ships (96c). -/
def sailors : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .sailor1), (u₂, .ship1), (u₃, .sailor2)],
   row [(u₁, .sailor2), (u₂, .ship2), (u₃, .sailor3)],
   row [(u₁, .sailor3), (u₂, .ship3), (u₃, .sailor1)]]

/-- By §4.6, the collective antecedent `∪u₁` of `work.together` is the group of all three
sailors while the reciprocal holds pointwise; the distinctness does no work. -/
theorem sailors_collective :
    reciprocityCond u₃ u₁ (ofRows sailors) ∅ ∧ atomsCond 3 u₁ (ofRows sailors) ∅ := by
  rw [reciprocityCond_ofRows mem_empty, atomsCond_ofRows mem_empty]
  decide

/-! ### Quantified antecedents (§5) -/

section Quantified

variable {D : Type*} [DecidableEq D]

/-- A reference set (101) is a subset of the restrictor `A` over which `R` is strongly
reciprocal (fn. 24), of the largest cardinality any such subset has, as the operator of (97)
maximizes. Maxima need not be unique (fn. 18). -/
def IsRefSet (R : D → D → Prop) (A Y : Finset D) : Prop :=
  Y ∈ A.powerset ∧ StrongReciprocity R Y ∧
    ∀ Z ∈ A.powerset, StrongReciprocity R Z → Z.card ≤ Y.card

/-- In the reference-set reading, (101) and (110a), the determiner holds of the restrictor and
a reference set. -/
def RefSetReading (Q : Finset D → Finset D → Prop) (R : D → D → Prop) (A : Finset D) :
    Prop :=
  ∃ Y ∈ A.powerset, IsRefSet R A Y ∧ Q A Y

/-- The participants (105) are the members of `A` bearing `R` to some other member. -/
def participants (R : D → D → Prop) [DecidableRel R] (A : Finset D) : Finset D :=
  A.filter fun a ↦ ∃ b ∈ A, b ≠ a ∧ R a b

/-- In the maximal-set reading, (104) and (110b), the reciprocal ranges over the whole
restrictor and the determiner holds of the restrictor and the participants. -/
def MaxSetReading (Q : Finset D → Finset D → Prop) (R : D → D → Prop) [DecidableRel R]
    (A : Finset D) : Prop :=
  Q A (participants R A)

/-- The two ranges of the reciprocal in (99). -/
inductive Range where
  | referenceSet
  | maximalSet
  deriving DecidableEq, Fintype, Repr

/-- The reading of a quantified reciprocal sentence at a range. -/
def reading (Q : Finset D → Finset D → Prop) (R : D → D → Prop) [DecidableRel R]
    (A : Finset D) : Range → Prop
  | .referenceSet => RefSetReading Q R A
  | .maximalSet => MaxSetReading Q R A

variable (Q : Finset D → Finset D → Prop) (R : D → D → Prop) [DecidableRel R] (A : Finset D)

theorem refSet_subset_participants {Y : Finset D} (h : IsRefSet R A Y) :
    Y ⊆ participants R A := by
  obtain ⟨hY, hR⟩ := strongReciprocity_iff.1 h.2.1
  intro a ha
  obtain ⟨b, hb, hab⟩ := Finset.exists_mem_ne (Finset.one_lt_card_iff_nontrivial.2 hY) a
  exact Finset.mem_filter.2
    ⟨Finset.mem_powerset.1 h.1 ha, b, Finset.mem_powerset.1 h.1 hb, hab, hR ha hb hab.symm⟩

/-- For a determiner upward monotone in its scope, the reference-set reading implies the maximal-set
reading (§5.2). -/
theorem maxSetReading_of_refSetReading (hQ : Monotone (Q A)) (h : RefSetReading Q R A) :
    MaxSetReading Q R A := by
  obtain ⟨Y, -, hY, hQY⟩ := h
  exact hQ (refSet_subset_participants R A hY) hQY

variable [DecidableRel Q]

instance : DecidablePred (reading Q R A) := fun r ↦ by
  cases r <;> unfold reading RefSetReading IsRefSet MaxSetReading <;> infer_instance

/-- A quantified reciprocal sentence is true iff true at both ranges, false iff false at both,
and neither otherwise, the supervaluation over the two precisifications (109). -/
def truthValue : SignType :=
  SignType.supervaluation {.referenceSet, .maximalSet} (reading Q R A)

theorem truthValue_true_iff :
    truthValue Q R A = 1 ↔ RefSetReading Q R A ∧ MaxSetReading Q R A := by
  unfold truthValue; rw [SignType.supervaluation_eq_one_iff]; simp [reading]

theorem truthValue_false_iff :
    truthValue Q R A = -1 ↔ ¬ RefSetReading Q R A ∧ ¬ MaxSetReading Q R A := by
  unfold truthValue; rw [SignType.supervaluation_eq_neg_one_iff]; simp [reading]

theorem truthValue_true_iff_of_monotone (hQ : Monotone (Q A)) :
    truthValue Q R A = 1 ↔ RefSetReading Q R A :=
  (truthValue_true_iff Q R A).trans
    ⟨And.left, fun h ↦ ⟨h, maxSetReading_of_refSetReading Q R A hQ h⟩⟩

theorem truthValue_false_iff_of_monotone (hQ : Monotone (Q A)) :
    truthValue Q R A = -1 ↔ ¬ MaxSetReading Q R A :=
  (truthValue_false_iff Q R A).trans
    ⟨And.right, fun h ↦ ⟨fun hr ↦ h (maxSetReading_of_refSetReading Q R A hQ hr), h⟩⟩

end Quantified

/-- The five inhabitants of the street of (100) and (102). -/
abbrev Person := Fin 5

/-- Proportional `most` holds when the scope has more than half of the restrictor. -/
def most (A B : Finset Person) : Prop := A.card < 2 * B.card

/-- Proportional `few` holds when the scope has less than half of the restrictor. -/
def few (A B : Finset Person) : Prop := 2 * B.card < A.card

/-- The first three inhabitants know each other and the other two know nobody (102). -/
def clique (a b : Person) : Prop := a ≠ b ∧ a.val < 3 ∧ b.val < 3

/-- The intermediate scenario of §5.2, in which two pairs know each other and one person knows
nobody. -/
def pairs (a b : Person) : Prop :=
  a ≠ b ∧ (a.val < 2 ∧ b.val < 2 ∨ 2 ≤ a.val ∧ a.val < 4 ∧ 2 ≤ b.val ∧ b.val < 4)

instance : DecidableRel clique := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance : DecidableRel pairs := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))
instance : DecidableRel most := fun _ _ ↦ inferInstanceAs (Decidable (_ < _))
instance : DecidableRel few := fun _ _ ↦ inferInstanceAs (Decidable (_ < _))

/-- In the clique scenario of (102), *most people know each other* is true and *few know each other*
false, and in the two-pairs scenario both are neither true nor false ((110), (111)). -/
theorem street_scenarios :
    truthValue most clique Finset.univ = 1 ∧ truthValue few clique Finset.univ = -1 ∧
      truthValue most pairs Finset.univ = 0 ∧ truthValue few pairs Finset.univ = 0 := by
  decide

/-! ### Maximize Anaphora (§6) -/

/-- A state maximizes anaphora (128) when, among the states a DRS `K` admits, its set `R_u` of
pairs (127), the dependency between antecedent and anaphor, is not properly included in another
admitted state's. -/
def MaximizesAnaphora {E : Type*} (K : PluralAssign ℕ E → Prop) (uAnaph uAnt : ℕ)
    (S : PluralAssign ℕ E) : Prop :=
  K S ∧ ∀ S', K S' → ¬ dep uAnt uAnaph S ⊂ dep uAnt uAnaph S'

section Maximize

variable {E : Type*} {P : E → E → Prop} {u u' : ℕ} {S : PluralAssign ℕ E}

theorem dep_subset_of_reciprocalDRS {X : Set E} (hS : ReciprocalDRS P X u u' S) :
    dep u' u S ⊆ {p | p.1 ∈ X ∧ p.2 ∈ X ∧ P p.1 p.2 ∧ p.1 ≠ p.2} := by
  obtain ⟨hX, hX', hrel⟩ := reciprocalDRS_iff.1 hS
  obtain ⟨hP, hdom, hcod⟩ := dep_of_relCond hrel
  exact fun p hp ↦ ⟨(hdom.trans hX).subset ⟨p.2, hp⟩, (hcod.trans hX').subset ⟨p.1, hp⟩, hP hp⟩

/-- Maximize Anaphora (§6, (128)) selects exactly the states of a reciprocal DRS whose dependency
is every pair of distinct members of `X` that `P` relates. -/
theorem maximizesAnaphora_iff (h : u ≠ u') {X : Set E} :
    MaximizesAnaphora (ReciprocalDRS P X u u') u u' S ↔ ReciprocalDRS P X u u' S ∧
      dep u' u S = {p | p.1 ∈ X ∧ p.2 ∈ X ∧ P p.1 p.2 ∧ p.1 ≠ p.2} := by
  refine ⟨fun ⟨hS, hmax⟩ ↦ ⟨hS, ?_⟩, fun ⟨hS, heq⟩ ↦ ⟨hS, fun S' hS' hlt ↦
    hlt.not_subset ((dep_subset_of_reciprocalDRS hS').trans heq.symm.subset)⟩⟩
  set F : SetRel E E := {p | p.1 ∈ X ∧ p.2 ∈ X ∧ P p.1 p.2 ∧ p.1 ≠ p.2}
  have hsub := dep_subset_of_reciprocalDRS hS
  obtain ⟨hX, hX', hrel⟩ := reciprocalDRS_iff.1 hS
  obtain ⟨-, hdom, hcod⟩ := dep_of_relCond hrel
  obtain ⟨s, hs⟩ := hrel.1
  obtain ⟨a, b, ha, hb, -⟩ := hrel.2 s hs
  have hne : F.Nonempty := ⟨(a, b), hsub ⟨s, hs, ha, hb⟩⟩
  have hFdom : F.dom = X := Set.Subset.antisymm (fun _ ⟨_, hp⟩ ↦ hp.1)
    ((hdom.trans hX).symm.subset.trans (SetRel.dom_mono hsub))
  have hFcod : F.cod = X := Set.Subset.antisymm (fun _ ⟨_, hp⟩ ↦ hp.2.1)
    ((hcod.trans hX').symm.subset.trans (SetRel.cod_mono hsub))
  have hF : ReciprocalDRS P X u u' (ofDep u' u F) := reciprocalDRS_iff.2
    ⟨(value_ofDep_left h.symm F).trans hFdom, (value_ofDep_right h.symm F).trans hFcod,
      relCond_ofDep h.symm (fun _ hp ↦ hp.2.2) hne⟩
  by_contra hneq
  exact hmax _ hF (by rw [dep_ofDep h.symm]; exact hsub.ssubset_of_ne hneq)

/-- Under Maximize Anaphora, the dependency makes `X` strongly reciprocal exactly when `P` does
(§6). -/
theorem strongReciprocity_dep_iff (h : u ≠ u') {X : Finset E}
    (hS : MaximizesAnaphora (ReciprocalDRS P ↑X u u') u u' S) :
    StrongReciprocity (fun a b ↦ (a, b) ∈ dep u' u S) X ↔ StrongReciprocity P X := by
  rw [((maximizesAnaphora_iff h).1 hS).2, strongReciprocity_iff, strongReciprocity_iff]
  exact and_congr_right fun _ ↦ forall₂_congr fun a ha ↦ forall₂_congr fun b hb ↦
    imp_congr_right fun hba ↦ ⟨fun h ↦ h.2.2.1, fun h ↦ ⟨ha, hb, h, hba⟩⟩

end Maximize

/-- The three boys of (125). -/
def boys : Finset Ind := {.boy1, .boy2, .boy3}

/-- For the three boys, (125b) makes `u₂` reciprocal to `u₁`, whose values are the boys, with
nothing known against any two of them knowing each other. -/
abbrev boysKnow : PluralAssign ℕ Ind → Prop := ReciprocalDRS (fun _ _ ↦ True) ↑boys u₂ u₁

/-- A minimal state for (125), (126a). -/
def boysMinimal : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .boy1), (u₂, .boy2)],
   row [(u₁, .boy2), (u₂, .boy3)],
   row [(u₁, .boy3), (u₂, .boy1)]]

/-- The strong reciprocal reading (126b). -/
def boysStrong : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .boy1), (u₂, .boy2)],
   row [(u₁, .boy2), (u₂, .boy3)],
   row [(u₁, .boy3), (u₂, .boy1)],
   row [(u₁, .boy1), (u₂, .boy3)],
   row [(u₁, .boy2), (u₂, .boy1)],
   row [(u₁, .boy3), (u₂, .boy2)]]

/-- By §6, the minimal state (126a) verifies (125), but Maximize Anaphora rejects it and selects
(126b), whose dependency is the strong reciprocal reading. -/
theorem maximize_strong :
    boysKnow (ofRows boysMinimal) ∧ ¬ MaximizesAnaphora boysKnow u₂ u₁ (ofRows boysMinimal) ∧
      MaximizesAnaphora boysKnow u₂ u₁ (ofRows boysStrong) ∧
      StrongReciprocity (fun a b ↦ (a, b) ∈ dep u₁ u₂ (ofRows boysStrong)) boys := by
  have hmin : boysKnow (ofRows boysMinimal) :=
    ⟨by rw [value_ofRows]; exact Finset.coe_inj.2 (by decide), by rw [relCond_ofRows]; decide,
      by rw [reciprocityCond_ofRows mem_empty]; decide⟩
  have hstr : boysKnow (ofRows boysStrong) :=
    ⟨by rw [value_ofRows]; exact Finset.coe_inj.2 (by decide), by rw [relCond_ofRows]; decide,
      by rw [reciprocityCond_ofRows mem_empty]; decide⟩
  have hMA : MaximizesAnaphora boysKnow u₂ u₁ (ofRows boysStrong) :=
    (maximizesAnaphora_iff (by decide)).2 ⟨hstr, Set.ext fun ⟨a, b⟩ ↦ by
      rw [mem_dep_ofRows]
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, true_and]
      revert a b
      decide⟩
  refine ⟨hmin, fun hm ↦ ?_, hMA, (strongReciprocity_dep_iff (by decide) hMA).2
    (strongReciprocity_iff.2 ⟨by decide, fun _ _ _ _ _ ↦ trivial⟩)⟩
  have hmem : (Ind.boy1, Ind.boy3) ∈ dep u₁ u₂ (ofRows boysMinimal) := by
    rw [((maximizesAnaphora_iff (by decide)).1 hm).2]
    exact ⟨by decide, by decide, trivial, by decide⟩
  rw [mem_dep_ofRows] at hmem
  revert hmem
  decide

/-- By §6.2, the classmates gave each other pictures of each other, each maximizing pairwise, so
that each gave a picture of herself to each of the others. -/
def classmates : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .tracy), (u₂, .chris), (u₃, .picture1), (u₄, .tracy)],
   row [(u₁, .tracy), (u₂, .matty), (u₃, .picture1), (u₄, .tracy)],
   row [(u₁, .chris), (u₂, .tracy), (u₃, .picture2), (u₄, .chris)],
   row [(u₁, .chris), (u₂, .matty), (u₃, .picture2), (u₄, .chris)],
   row [(u₁, .matty), (u₂, .tracy), (u₃, .picture3), (u₄, .matty)],
   row [(u₁, .matty), (u₂, .chris), (u₃, .picture3), (u₄, .matty)]]

/-- The three classmates. -/
def trio : Finset Ind := {.tracy, .chris, .matty}

/-- Both reciprocal relations of (134) are strongly reciprocal on the classmates, though no row
relates all three classmates (§6.2). -/
theorem classmates_pairwise :
    StrongReciprocity (fun a b ↦ (a, b) ∈ dep u₁ u₂ (ofRows classmates)) trio ∧
      StrongReciprocity (fun a b ↦ (a, b) ∈ dep u₂ u₄ (ofRows classmates)) trio ∧
      ¬ ∃ s ∈ classmates,
        s u₁ = ↑Ind.tracy ∧ s u₂ = ↑Ind.chris ∧ s u₄ = ↑Ind.matty := by
  simp only [strongReciprocity_iff, mem_dep_ofRows]
  decide

/-- In the wide construal of (135), each of Tracy, Matty and Chris believes that she praised the
two others (136). -/
def praisedWide : List (PartialAssign ℕ Ind) :=
  [row [(u₁, .chris), (u₂, .chris), (u₃, .tracy), (w, .world1)],
   row [(u₁, .chris), (u₂, .chris), (u₃, .matty), (w, .world1)],
   row [(u₁, .tracy), (u₂, .tracy), (u₃, .chris), (w, .world2)],
   row [(u₁, .tracy), (u₂, .tracy), (u₃, .matty), (w, .world2)],
   row [(u₁, .matty), (u₂, .matty), (u₃, .chris), (w, .world3)],
   row [(u₁, .matty), (u₂, .matty), (u₃, .tracy), (w, .world3)]]

/-- In the wide reading (136) the pronoun is bound, the matrix reciprocal holds, and in each girl's
world the reciprocal covers the two others (§6.3). -/
theorem praised_wide :
    bindingCond u₂ u₁ (ofRows praisedWide) ∅ ∧
      reciprocityCond u₃ u₂ (ofRows praisedWide) ∅ ∧
      ∀ s ∈ praisedWide, ∀ d,
        d ∈ sumRows praisedWide [w] s u₃ ↔ d ∈ trio ∧ ↑d ≠ s u₁ := by
  rw [bindingCond_ofRows, reciprocityCond_ofRows mem_empty]
  decide

end HaugDalrymple2020
