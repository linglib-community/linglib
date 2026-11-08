module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Linglib.Semantics.Homogeneity.Plural
public import Linglib.Semantics.Negation.Polarity
public import Linglib.Semantics.Quantification.Basic
public import Studies.Magri2014
public import Linglib.Data.Examples.TieuKrizChemla2019

/-!
# Tieu, Križ and Chemla (2019): children's homogeneity

*The trucks are blue* and *The trucks are not blue* are both neither true nor false when some but
not all of the trucks are blue, a GAP context. Tieu, Križ and Chemla test four- and five-year-old
French-speaking children on such sentences and on the *not all* implicature of *some*, against
Magri's account, on which the definite means *some* and reaches *all* by exhaustifying twice, the
*not all* implicature being a step of that computation.

A child may instead read the definite as a quantifier, existential or universal, scoping under
or over negation. Such a construal is classical, and a reading is the supervaluation over its
construals: the homogeneous reading over the existential and the universal construal, as in the
paper's statement of the supervaluation account, and the scope-ambiguous universal of
Experiment 2 over the two scopes of the universal.

## Implementation notes

A world is the set of objects with the property. Magri's account is the double strengthening of
`Studies/Magri2014`, and a participant computes the *not all* implicature exactly when *all* is
among their alternatives to *some* (`.strong ∈ A`), since the paper's argument rests on the two
inferences sharing their alternatives. A binary judgment accepts exactly the true sentences, and
Table 8's rewards 1, 0 and −1 are the three truth values. Not formalized are Table 8's
partial-truth group, which on the definite responds as the homogeneous one; the ternary coding
of the implicature trials, after Katsos and Bishop; and the statistics. In Experiment 1, 16 of 24
children were homogeneous and 8 existential, and 6 of the homogeneous children and 5 of 22 adults
lacked the implicature; in Experiment 2 the homogeneous group without the implicature had 5 of 24
children and 2 of 25 adults.

## TODO

The printed Table 2 has the universal groups accept the positive sentence in a GAP context,
against Figure 2. The printed Table 8 gives the scope-ambiguous and wide-scope universal groups
GAP rewards that contradict their definitions beside it, and fixes rows for *all* under negation
and *some* in a GAP context that no definition determines. The definitions are followed.

## References

* [tieu-kriz-chemla-2019]
* [magri-2014]
* [kriz-2016]
* [spector-2013b]
* [katsos-bishop-2011]
-/

@[expose] public section

namespace TieuKrizChemla2019

open Homogeneity Quantifier

variable {Atom : Type*} (x : Finset Atom)

/-- A GAP context is one where some but not all objects of the plurality have the property,
Figure 1. -/
def IsGap (w : Finset Atom) : Prop := (∃ a ∈ x, a ∈ w) ∧ ∃ a ∈ x, a ∉ w

/-! ### Construals -/

/-- The force of a construal of the plural definite is existential, (6), or universal, (7). -/
inductive Force where
  | existential
  | universal
  deriving DecidableEq, Fintype

/-- The determiner of a force is *some* or *every*. -/
def Force.gq : Force → Det Atom
  | .existential => Det.some
  | .universal => Det.every

/-- A construal of the definite scopes under or over sentential negation. -/
inductive Scope where
  | low
  | wide
  deriving DecidableEq, Fintype

/-- Negation at a scope takes the outer negation of a quantifier scoping under it and the inner
negation of one scoping over it. -/
def Scope.neg : Scope → Det Atom → Det Atom
  | .low, q => qᶜ
  | .wide, q => q.innerNeg

/-- A bivalent construal of the plural definite is a force with a scope relative to negation. -/
structure Construal where
  /-- The quantificational force. -/
  force : Force
  /-- The scope relative to negation. -/
  scope : Scope
  deriving DecidableEq, Fintype

/-- The quantifier a construal gives the definite at a polarity. -/
def Construal.gq (c : Construal) : Polarity → Det Atom
  | .positive => c.force.gq
  | .negative => c.scope.neg c.force.gq

/-- Under a construal, *the Xs are P* at a polarity holds at the world `w`, the objects with the
property. -/
def Construal.Holds (c : Construal) (p : Polarity) (w : Finset Atom) : Prop :=
  c.gq p (x : Set Atom) w

instance [DecidableEq Atom] (c : Construal) (p : Polarity) (w : Finset Atom) :
    Decidable (c.Holds x p w) := by
  obtain ⟨_ | _, _ | _⟩ := c <;> cases p <;>
    dsimp only [Construal.Holds, Construal.gq, Scope.neg, Force.gq, Det.compl_apply, Det.innerNeg,
      Det.every, Det.some, Set.Nonempty, Set.subset_def, Set.inter_def, Set.compl_def,
      Set.mem_ofPred_eq] <;>
    infer_instance

/-! ### Readings -/

/-- The readings a participant may assign the plural definite are the quantified readings,
among them the existential and the universal of Figure 2, the wide-scope universal of Table 8 and
the wide-scope existential of the empty fourth group; the homogeneous reading; and the universal
ambiguous in scope relative to negation, Table 8. -/
inductive Reading where
  /-- The definite as a quantifier at a scope. -/
  | quantified (c : Construal)
  /-- The definite with a truth-value gap, (1)–(2). -/
  | homogeneous
  /-- The definite as *all*, ambiguous in scope relative to negation. -/
  | scopeAmbiguous
  deriving DecidableEq

instance : Fintype Reading where
  elems := {.quantified ⟨.existential, .low⟩, .quantified ⟨.existential, .wide⟩,
    .quantified ⟨.universal, .low⟩, .quantified ⟨.universal, .wide⟩, .homogeneous,
    .scopeAmbiguous}
  complete := by rintro (⟨_ | _, _ | _⟩ | _ | _) <;> simp

/-- The construals a reading supervaluates over. The homogeneous reading is true when (8a) and
(8b) both are and false when neither is, and the scope-ambiguous one is true or false according
to where the universal takes scope. -/
def Reading.construals : Reading → Finset Construal
  | .quantified c => {c}
  | .homogeneous => {⟨.existential, .low⟩, ⟨.universal, .low⟩}
  | .scopeAmbiguous => {⟨.universal, .low⟩, ⟨.universal, .wide⟩}

theorem Reading.construals_nonempty (r : Reading) : r.construals.Nonempty := by
  rcases r with c | _ | _ <;> simp [construals]

/-- The value of the definite sentence at a polarity under a reading is the supervaluation over
the reading's construals. -/
def Reading.value [DecidableEq Atom] (r : Reading) (p : Polarity) :
    (Finset Atom → Trivalent) :=
  fun w ↦ Trivalent.supervaluation r.construals (·.Holds x p w)

/-- The values of the positive and the negative sentence in a GAP context under each reading,
Figure 2 and the group definitions of Table 8. -/
def Reading.gapPattern : Reading → Trivalent × Trivalent
  | .quantified ⟨.existential, .low⟩ => (.true, .false)
  | .quantified ⟨.existential, .wide⟩ => (.true, .true)
  | .quantified ⟨.universal, .low⟩ => (.false, .true)
  | .quantified ⟨.universal, .wide⟩ => (.false, .false)
  | .homogeneous => (.undefined, .undefined)
  | .scopeAmbiguous => (.false, .undefined)

/-- A binary judgment accepts exactly the true sentences, collapsing the intermediate reward
into the minimal one. -/
def Reading.binaryPattern (r : Reading) : Bool × Bool :=
  r.gapPattern.map (fun v ↦ decide (v = .true)) fun v ↦ decide (v = .true)

/-! ### Predictions -/

variable {x} {w : Finset Atom}

theorem Construal.holds_of_isGap (hw : IsGap x w) (c : Construal) (p : Polarity) :
    c.Holds x p w ↔ (c.force = .existential ↔ p = .positive ∨ c.scope = .wide) := by
  obtain ⟨⟨a, ha, haw⟩, b, hb, hbw⟩ := hw
  obtain ⟨_ | _, _ | _⟩ := c <;> cases p <;>
    simp [Holds, gq, Scope.neg, Force.gq, Det.innerNeg, Det.some, Det.every, Set.Nonempty,
      Set.subset_def] <;> grind

theorem Construal.holds_of_subset (hx : x.Nonempty) (hw : x ⊆ w) (c : Construal)
    (p : Polarity) : c.Holds x p w ↔ p = .positive := by
  obtain ⟨b, hb⟩ := hx
  obtain ⟨_ | _, _ | _⟩ := c <;> cases p <;>
    simp [Holds, gq, Scope.neg, Force.gq, Det.innerNeg, Det.some, Det.every, Set.Nonempty,
      Set.subset_def] <;> grind

theorem Construal.holds_of_disjoint (hx : x.Nonempty) (hw : Disjoint x w) (c : Construal)
    (p : Polarity) : c.Holds x p w ↔ p = .negative := by
  obtain ⟨b, hb⟩ := hx
  rw [Finset.disjoint_left] at hw
  obtain ⟨_ | _, _ | _⟩ := c <;> cases p <;>
    simp [Holds, gq, Scope.neg, Force.gq, Det.innerNeg, Det.some, Det.every, Set.Nonempty,
      Set.subset_def] <;> grind

section

variable [DecidableEq Atom]

/-- In a GAP context every reading takes the values of Figure 2 and Table 8. -/
theorem value_of_isGap (hw : IsGap x w) (r : Reading) :
    (r.value x .positive w, r.value x .negative w) = r.gapPattern := by
  simp only [Reading.value, Construal.holds_of_isGap hw]
  rcases r with ⟨_ | _, _ | _⟩ | _ | _ <;> decide

/-- Where every object has the property all readings make the positive sentence true and the
negative one false, as the clearly true and clearly false controls of both experiments require.
-/
theorem value_of_subset (hx : x.Nonempty) (hw : x ⊆ w) (r : Reading) :
    (r.value x .positive w, r.value x .negative w) = (.true, .false) := by
  simp only [Reading.value, Construal.holds_of_subset hx hw,
    Trivalent.supervaluation_const r.construals_nonempty]
  simp

/-- Where no object has the property all readings make the positive sentence false and the
negative one true. -/
theorem value_of_disjoint (hx : x.Nonempty) (hw : Disjoint x w) (r : Reading) :
    (r.value x .positive w, r.value x .negative w) = (.false, .true) := by
  simp only [Reading.value, Construal.holds_of_disjoint hx hw,
    Trivalent.supervaluation_const r.construals_nonempty]
  simp

@[simp] theorem value_quantified (c : Construal) (p : Polarity) (w : Finset Atom) :
    (Reading.quantified c).value x p w = .ofProp (c.Holds x p w) :=
  Trivalent.supervaluation_singleton _ c

theorem value_negative_of_low {r : Reading} (h : ∀ c ∈ r.construals, c.scope = .low)
    (w : Finset Atom) : r.value x .negative w = (r.value x .positive w)ᶜ := by
  rw [Reading.value, Reading.value, ← Trivalent.supervaluation_not _ r.construals_nonempty]
  refine Trivalent.supervaluation_congr fun c hc ↦ ?_
  obtain ⟨_ | _, _⟩ := c <;> cases h _ hc <;> rfl

/-- The homogeneous reading is the trivalent plural `barePlural`, the supervaluation over the
objects of the plurality. -/
theorem value_homogeneous (hx : x.Nonempty) :
    Reading.homogeneous.value x .positive = barePlural (· ∈ ·) x := by
  funext w
  obtain ⟨b, hb⟩ := hx
  apply Trivalent.eq_of_eq_undefined_iff_of_eq_true_iff <;>
    simp [Reading.value, Reading.construals, barePlural, Trivalent.supervaluation_eq_undefined_iff,
      Trivalent.supervaluation_eq_true_iff, Construal.Holds, Construal.gq, Force.gq, Det.some,
      Det.every, Set.Nonempty, Finset.subset_iff] <;>
    grind

end

-- (8a), (8b)
theorem isGap_iff_not_homogeneous (hx : x.Nonempty) :
    IsGap x w ↔ ¬ Homogeneous {{w | ∃ a ∈ x, a ∈ w}, {w | x ⊆ w}} w := by
  obtain ⟨b, hb⟩ := hx
  rw [homogeneous_pair]
  simp only [IsGap, Set.mem_ofPred_eq, Finset.subset_iff]
  grind

section

variable [DecidableEq Atom]

/-- A participant who reads the definite homogeneously but reverses the positive judgment to
obtain the negative one, weak negation (fn 23), responds as a universal participant. -/
theorem homogeneous_weakNegation (hx : x.Nonempty) (w : Finset Atom) :
    (Trivalent.ofProp (Reading.homogeneous.value x .positive w = .true))ᶜ =
      (Reading.quantified ⟨.universal, .low⟩).value x .negative w := by
  rw [value_homogeneous hx, value_negative_of_low (by simp [Reading.construals])]
  simp [barePlural, Construal.Holds, Construal.gq, Force.gq, Det.every,
    Trivalent.supervaluation_eq_true_iff, Finset.subset_iff]

-- (19), (20)
theorem domainRestriction_of_isGap (hw : IsGap x w) :
    Reading.homogeneous.value (x.filter (· ∈ w)) .positive w = .true ∧
      Reading.homogeneous.value (x.filter (· ∉ w)) .negative w = .true := by
  obtain ⟨⟨a, ha, haw⟩, b, hb, hbw⟩ := hw
  rw [value_negative_of_low (by simp [Reading.construals]),
    value_homogeneous ⟨a, Finset.mem_filter.2 ⟨ha, haw⟩⟩,
    value_homogeneous ⟨b, Finset.mem_filter.2 ⟨hb, hbw⟩⟩]
  simp only [barePlural, Trivalent.compl_eq_true_iff, Trivalent.supervaluation_eq_true_iff,
    Trivalent.supervaluation_eq_false_iff, Finset.mem_filter]
  exact ⟨fun _ h ↦ h.2, ⟨b, Finset.mem_filter.2 ⟨hb, hbw⟩⟩, fun _ h ↦ h.2⟩

end

/-! ### Binary and ternary judgments -/

/-- Ternary judgments separate all readings in a GAP context, Experiment 2's design. -/
theorem gapPattern_injective : Function.Injective Reading.gapPattern := by decide

/-- The four quantified readings give the four possible pairs of binary judgments in a GAP context
(Figure 2). -/
theorem binaryPattern_quantified_bijective :
    Function.Bijective fun c : Construal ↦ (Reading.quantified c).binaryPattern := by decide

/-- Binary judgments conflate the homogeneous reading and the scope-ambiguous universal with the
wide-scope universal, all three rejecting both sentences in a GAP context. -/
theorem binaryPattern_eq_wideScopeUniversal :
    ∀ r ∈ ({.homogeneous, .scopeAmbiguous} : Finset Reading),
      r.binaryPattern = (Reading.quantified ⟨.universal, .wide⟩).binaryPattern := by decide

/-! ### The implicature account -/

section Implicature

open Magri2014 (Item exh strengthened primal primalMates compl_comp_primal)
open Exhaustification

/-- A participant's Horn-mates are those of Magri's primal configuration with `A` as the
alternatives to *some*. Magri's are `{.mystery, .strong}` (`mates_primal`), with *all* among
them. -/
def mates (A : Finset Item) : Item → Finset Item :=
  Function.update primalMates .weak A

theorem mates_primal : mates {.mystery, .strong} = primalMates :=
  Function.update_eq_self _ _

section General

variable {W : Type*} {wk st : Set W} {A : Finset Item}

private theorem exh_mates_mystery : exh (mates A) (primal wk st) .mystery = wk := by
  change exhIE (primal wk st '' ↑({.weak} : Finset Item)) wk = wk
  exact exhIE_eq_self_of_forall _ _ (by simp [primal])

private theorem exh_mates_weak_of_forall (h : ∀ i ∈ A, wk ⊆ primal wk st i) :
    exh (mates A) (primal wk st) .weak = wk :=
  exhIE_eq_self_of_forall _ _ fun a ha _ ↦ by
    obtain ⟨i, hi, rfl⟩ := ha
    exact h i hi

theorem exh_mates_weak_of_notMem (hA : .strong ∉ A) : exh (mates A) (primal wk st) .weak = wk :=
  exh_mates_weak_of_forall fun i hi ↦ by
    cases i <;> first | exact subset_rfl | exact absurd hi hA

-- (10)
theorem exh_mates_weak_of_mem (hA : .strong ∈ A) (h : (wk \ st).Nonempty) :
    exh (mates A) (primal wk st) .weak = wk \ st := by
  have himg : insert wk (primal wk st '' A) = {wk, st} := by
    refine Set.insert_subset_iff.2 ⟨.inl rfl, ?_⟩ |>.antisymm
      (Set.insert_subset_insert (Set.singleton_subset_iff.2 ⟨.strong, hA, rfl⟩))
    rintro _ ⟨i, -, rfl⟩
    cases i <;> simp [primal]
  change exhIE (primal wk st '' A) wk = wk \ st
  rw [← exhIE_insert_of_subset subset_rfl
      (exhMW_nonempty (A.finite_toSet.image _) (h.mono Set.sdiff_subset)), himg,
    exhIE_pair_sdiff _ h]

-- (11), (10)
theorem strengthened_mates_mystery :
    strengthened (mates A) (primal wk st) .mystery =
      exhIE {exh (mates A) (primal wk st) .weak} wk := by
  change exhIE (exh (mates A) (primal wk st) '' ↑({.weak} : Finset Item))
    (exh (mates A) (primal wk st) .mystery) = _
  rw [Finset.coe_singleton, Set.image_singleton, exh_mates_mystery]

theorem strengthened_mates_mystery_of_notMem (hA : .strong ∉ A) :
    strengthened (mates A) (primal wk st) .mystery = wk := by
  rw [strengthened_mates_mystery, exh_mates_weak_of_notMem hA]
  exact exhIE_singleton_self wk

-- (11)
theorem strengthened_mates_mystery_of_mem (hA : .strong ∈ A) (h : st ⊆ wk) (hne : st.Nonempty) :
    strengthened (mates A) (primal wk st) .mystery = st := by
  rw [strengthened_mates_mystery]
  rcases (wk \ st).eq_empty_or_nonempty with h₁ | h₁
  · have hsub := Set.sdiff_eq_empty.1 h₁
    rw [exh_mates_weak_of_forall fun i _ ↦ by cases i <;> first | exact subset_rfl | exact hsub,
      exhIE_singleton_self]
    exact hsub.antisymm h
  · have h₂ : (wk \ (wk \ st)).Nonempty := by
      rwa [Set.sdiff_sdiff_right_self, Set.inter_eq_right.2 h]
    rw [exh_mates_weak_of_mem hA h₁, exhIE_singleton h₂, Set.sdiff_sdiff_right_self,
      Set.inter_eq_right.2 h]

theorem strengthened_mates_not_mystery (h : st ⊆ wk) :
    strengthened (mates A) (compl ∘ primal wk st) .mystery = wkᶜ := by
  rw [compl_comp_primal, strengthened_mates_mystery,
    exh_mates_weak_of_forall fun i _ ↦ by
      cases i <;> first | exact subset_rfl | exact Set.compl_subset_compl.2 h]
  exact exhIE_singleton_self _

end General

variable {A : Finset Item} {w' : Finset Atom}

variable (x) in
/-- *Some* and the definite hold where some object of the plurality has the property, the weak
pole of the scale. -/
def someWorlds : Set (Finset Atom) := {w | ∃ a ∈ x, a ∈ w}

variable (x) in
/-- *All* holds where every object of the plurality has the property, the strong pole. -/
def allWorlds : Set (Finset Atom) := {w | x ⊆ w}

@[simp] theorem mem_someWorlds : w ∈ someWorlds x ↔ ∃ a ∈ x, a ∈ w := Iff.rfl

@[simp] theorem mem_allWorlds : w ∈ allWorlds x ↔ x ⊆ w := Iff.rfl

variable [DecidableEq Atom] in
instance : DecidablePred (· ∈ someWorlds x) := fun w ↦
  inferInstanceAs (Decidable (∃ a ∈ x, a ∈ w))

variable [DecidableEq Atom] in
instance : DecidablePred (· ∈ allWorlds x) := fun w ↦
  inferInstanceAs (Decidable (x ⊆ w))

theorem allWorlds_subset_someWorlds (hx : x.Nonempty) : allWorlds x ⊆ someWorlds x :=
  fun _ hw ↦ mem_someWorlds.2 (hx.elim fun a ha ↦ ⟨a, ha, mem_allWorlds.1 hw ha⟩)

theorem isGap_iff_mem_sdiff : IsGap x w ↔ w ∈ someWorlds x \ allWorlds x := by
  simp [IsGap, Finset.subset_iff]

/-- Since the *not all* implicature is a sub-computation of homogeneity, a participant accepts
the positive definite in a GAP context exactly when they accept *some* where every object has the
property, whatever their alternatives. The homogeneous participants of both experiments who
accept *some* there contradict the account. -/
theorem definite_in_gap_iff_some_in_all (hw : IsGap x w) (hw' : x ⊆ w') :
    w ∈ strengthened (mates A) (primal (someWorlds x) (allWorlds x)) .mystery ↔
      w' ∈ exh (mates A) (primal (someWorlds x) (allWorlds x)) .weak := by
  have hx : x.Nonempty := hw.1.imp fun _ h ↦ h.1
  have hall : ¬ x ⊆ w := fun h ↦ hw.2.elim fun a ha ↦ ha.2 (h ha.1)
  by_cases hA : .strong ∈ A
  · rw [strengthened_mates_mystery_of_mem hA (allWorlds_subset_someWorlds hx)
      ⟨x, mem_allWorlds.2 subset_rfl⟩, exh_mates_weak_of_mem hA ⟨w, isGap_iff_mem_sdiff.1 hw⟩]
    simp [hw', hall]
  · have hsome : ∃ a ∈ x, a ∈ w' := hx.elim fun a ha ↦ ⟨a, ha, hw' ha⟩
    rw [strengthened_mates_mystery_of_notMem hA, exh_mates_weak_of_notMem hA]
    simp [hw.1, hsome]

variable [DecidableEq Atom] [Fintype Atom]

variable (x A) in
/-- The account's binary judgments of the positive and the negative definite at a world, for a
participant whose alternatives to *some* are `A`. -/
def implicaturePattern (w : Finset Atom) : Bool × Bool :=
  (decide (w ∈ strengthened (mates A) (primal (someWorlds x) (allWorlds x)) .mystery),
    decide (w ∈ strengthened (mates A) (compl ∘ primal (someWorlds x) (allWorlds x)) .mystery))

/-- The account predicts the existential pattern without the implicature and the homogeneous
one with it, the two groups of Table 2 it allows. -/
theorem implicaturePattern_of_isGap (hw : IsGap x w) :
    implicaturePattern x A w = (if .strong ∈ A then Reading.homogeneous
      else .quantified ⟨.existential, .low⟩).binaryPattern := by
  have hx : x.Nonempty := hw.1.imp fun _ h ↦ h.1
  have hall : ¬ x ⊆ w := fun h ↦ hw.2.elim fun a ha ↦ ha.2 (h ha.1)
  simp only [implicaturePattern, strengthened_mates_not_mystery (allWorlds_subset_someWorlds hx)]
  split_ifs with hA
  · simp [strengthened_mates_mystery_of_mem hA (allWorlds_subset_someWorlds hx)
      ⟨x, mem_allWorlds.2 subset_rfl⟩, hw.1, hall, Reading.binaryPattern, Reading.gapPattern]
  · simp [strengthened_mates_mystery_of_notMem hA, hw.1, Reading.binaryPattern,
      Reading.gapPattern]

end Implicature

end TieuKrizChemla2019
