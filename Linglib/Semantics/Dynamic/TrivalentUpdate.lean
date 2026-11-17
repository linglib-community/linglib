module

public import Linglib.Semantics.Dynamic.Update
public import Linglib.Logic.Trivalent.Pointwise
import Mathlib.Data.Fintype.Pi

/-!
# Three-valued updates

A *three-valued update* gives each transition from an input state to an output state a truth
value: the transition is true, false, or not a transition at all. [van-den-berg-1996] (ch. 2)
presents one by two relations, its *defined* transitions `⟦φ⟧ᵈ` and, among them, its *true*
transitions `⟦φ⟧⁺`; the false transitions are the remaining defined ones. Here a three-valued update
is a trivalent proposition about pairs of states, `S × S → Trivalent`, so its true, false and
undefined transitions are the extensions of `Logic/Trivalent/Pointwise.lean`, and the update with
defined transitions `d` and true transitions `t` is the conditional event of `t` on `d`.

The connectives come in two kinds. The *static* ones act on each transition separately, and are
the pointwise three-valued connectives: weak negation `−φ` is Kleene negation, which swaps the true
and the false transitions; static conjunction `φ ∩ ψ` and static disjunction `φ ∪ ψ` are the Weak
Kleene connectives; program disjunction `φ ⊕ ψ` is Belnap's disjunction; the presupposition
operator `+φ` is Beaver's, keeping the true transitions and leaving the rest undefined; and
definedness `𝒟φ` makes every defined transition true. Every unary connective that is strict in van
den Berg's sense is one of nine composites of `−`, `+` and `𝒟`, his Table 2.1.

The *dynamic* connectives compose. Sequencing `φ ∧ ψ` composes the defined transitions and the true
transitions separately, so that two copies of a two-valued relational logic sit on top of each
other; on tests it is Weak Kleene conjunction (his Aside 2.1). Closure `!φ` is the test of having a
defined and of having a true output. Strong dynamic negation `¬φ` is the weakest operator that both
complements the transitions and complements the truth value at the input (his Definitions 2.10 to
2.12), it is statically equivalent to the closed negation `−!φ` of dynamic predicate logic (his
Lemma 2.13), and it is definable from the other connectives (his Fact 3.3).

## Main definitions

* `TrivalentUpdate S`: a three-valued update on states `S`.
* `TrivalentUpdate.defined`, `TrivalentUpdate.pos`, `TrivalentUpdate.neg`: the defined, true and
  false transitions, and `TrivalentUpdate.ofDefinedTrue`: the update with given defined and true
  transitions.
* `TrivalentUpdate.DefinedAt`, `TrivalentUpdate.TrueAt`, `TrivalentUpdate.FalseAt`: the truth
  value at an input state, and `TrivalentUpdate.IsTotal`: defined at every input.
* `TrivalentUpdate.WeakEquiv`, `TrivalentUpdate.StaticEquiv`: the same true transitions, and true at
  the same inputs; strong equivalence is equality.
* `TrivalentUpdate.presup`, `TrivalentUpdate.definedness`, `TrivalentUpdate.sconj`,
  `TrivalentUpdate.sdisj`, `TrivalentUpdate.pdisj`: the static connectives `+`, `𝒟`, `∩`, `∪`,
  `⊕`; weak negation is `ᶜ`.
* `TrivalentUpdate.seq`, `TrivalentUpdate.close`, `TrivalentUpdate.dplNeg`,
  `TrivalentUpdate.dneg`: sequencing `∧`, closure `!`, the closed negation `∼ = −!`, and strong
  dynamic negation `¬`.
* `TrivalentUpdate.DynamicNegConditions`, `TrivalentUpdate.StaticNegConditions`: the minimal
  conditions on a negation.

## Main results

* `TrivalentUpdate.eq_of_defined_eq_of_pos_eq`: an update is determined by its defined and its true
  transitions.
* `Trivalent.eq_of_strict`: the strict unary truth functions are the nine of Table 2.1.
* `TrivalentUpdate.seq_assoc`: sequencing is associative.
* `TrivalentUpdate.definedness_eq_sdisj`: definedness is `φ ∪ −φ`.
* `TrivalentUpdate.seq_apply_self_of_isTest`: on tests, sequencing is Weak Kleene conjunction; only
  the first conjunct need be a test.
* `TrivalentUpdate.dneg_dynamicNegConditions`, `TrivalentUpdate.dneg_staticNegConditions`,
  `TrivalentUpdate.pos_subset_pos_dneg`, `TrivalentUpdate.neg_subset_neg_dneg`: strong dynamic
  negation is the weakest negation meeting both conditions.
* `TrivalentUpdate.staticEquiv_dneg_dplNeg`: `¬φ` and `−!φ` are true at the same inputs.
* `TrivalentUpdate.dneg_eq`: `¬φ = +−(!φ ∧ −φ) ∩ −φ`.
* `TrivalentUpdate.weakEquiv_seq_dplNeg_compl_dneg`, `TrivalentUpdate.exists_seq_dplNeg_compl_ne_dneg`:
  `−!φ ∧ −φ` has the true transitions of `¬φ` but more false ones.

## Implementation notes

Van den Berg defines each connective by its defined and its true transitions; `ofDefinedTrue`
turns such a pair into an update, and keeps only the true transitions that are defined. His
display (32) of static disjunction lists as true transitions those where either disjunct is true,
but `−(−φ ∩ −ψ)` is undefined unless both disjuncts are defined; `pos_sdisj` records the true
transitions of the definition.

## References

* [van-den-berg-1996]
* [groenendijk-stokhof-1991]
* [beaver-krahmer-2001]
* [belnap-1970]
-/

@[expose] public section

namespace Trivalent

/-- The truth functions that are strict, sending `undefined` to `undefined`, are the nine
composites of negation, Beaver's presupposition operator `· ⊔ undefined` and definedness
`a ⊔ aᶜ` listed in [van-den-berg-1996] Table 2.1, the dynamically strict unary operators that are
set-theoretic polynomials in their argument. -/
theorem eq_of_strict (f : Trivalent → Trivalent) (hf : f .undefined = .undefined) :
    f ∈ [id, compl, (fun a ↦ a ⊔ aᶜ), compl ∘ (fun a ↦ a ⊔ aᶜ),
      (· ⊔ .undefined), compl ∘ (· ⊔ .undefined), (· ⊔ .undefined) ∘ compl,
      compl ∘ (· ⊔ .undefined) ∘ compl, (· ⊔ .undefined) ∘ compl ∘ (· ⊔ .undefined)] := by
  revert f; decide

/-- The last row of Table 2.1 is never defined. -/
theorem sup_undefined_compl_sup_undefined (a : Trivalent) :
    (a ⊔ .undefined)ᶜ ⊔ .undefined = .undefined := by
  cases a <;> rfl

end Trivalent

namespace DynamicSemantics

open SetRel Trivalent

/-- A three-valued update: each transition from an input state to an output state is true, false
or undefined ([van-den-berg-1996] ch. 2 §2.1). -/
abbrev TrivalentUpdate (S : Type*) := S × S → Trivalent

namespace TrivalentUpdate

variable {S : Type*} {φ ψ χ : TrivalentUpdate S} {d t : Update S} {g h : S}

/-! ### Defined, true and false transitions -/

/-- The defined transitions `⟦φ⟧ᵈ`. -/
def defined (φ : TrivalentUpdate S) : Update S := (gapExt φ)ᶜ

/-- The true transitions `⟦φ⟧⁺`. -/
def pos (φ : TrivalentUpdate S) : Update S := posExt φ

/-- The false transitions `⟦φ⟧⁻`, the defined transitions that are not true. -/
def neg (φ : TrivalentUpdate S) : Update S := negExt φ

@[simp] theorem mem_defined : g ~[defined φ] h ↔ φ (g, h) ≠ .undefined := Iff.rfl

@[simp] theorem mem_pos : g ~[pos φ] h ↔ φ (g, h) = .true := Iff.rfl

@[simp] theorem mem_neg : g ~[neg φ] h ↔ φ (g, h) = .false := Iff.rfl

theorem pos_subset_defined (φ : TrivalentUpdate S) : pos φ ⊆ defined φ :=
  posExt_subset_compl_gapExt φ

theorem neg_subset_defined (φ : TrivalentUpdate S) : neg φ ⊆ defined φ :=
  negExt_subset_compl_gapExt φ

theorem pos_union_neg (φ : TrivalentUpdate S) : pos φ ∪ neg φ = defined φ :=
  posExt_union_negExt φ

theorem disjoint_pos_neg (φ : TrivalentUpdate S) : Disjoint (pos φ) (neg φ) :=
  disjoint_posExt_negExt φ

theorem neg_eq_defined_diff_pos (φ : TrivalentUpdate S) : neg φ = defined φ \ pos φ := by
  ext p; cases hp : φ p <;> simp [defined, pos, neg, hp]

/-- An update is determined by its defined and its true transitions. -/
theorem eq_of_defined_eq_of_pos_eq (hd : defined φ = defined ψ) (hp : pos φ = pos ψ) : φ = ψ := by
  funext p
  refine eq_of_eq_undefined_iff_of_eq_true_iff ?_ (Set.ext_iff.mp hp p)
  simpa [defined, not_iff_not] using Set.ext_iff.mp hd p

theorem eq_iff_defined_eq_and_pos_eq : φ = ψ ↔ defined φ = defined ψ ∧ pos φ = pos ψ :=
  ⟨fun h ↦ h ▸ ⟨rfl, rfl⟩, fun ⟨hd, hp⟩ ↦ eq_of_defined_eq_of_pos_eq hd hp⟩

/-- The update with defined transitions `d` whose true transitions are those of `t` in `d`: the
conditional event of `t` on `d`. -/
noncomputable def ofDefinedTrue (d t : Update S) : TrivalentUpdate S :=
  open Classical in condEvent (· ∈ d) (· ∈ t)

@[simp] theorem defined_ofDefinedTrue : defined (ofDefinedTrue d t) = d := by
  ext p; simp [defined, ofDefinedTrue]

@[simp] theorem pos_ofDefinedTrue : pos (ofDefinedTrue d t) = d ∩ t := by
  ext p; simp [pos, ofDefinedTrue]

theorem pos_ofDefinedTrue_of_subset (h : t ⊆ d) : pos (ofDefinedTrue d t) = t := by
  rw [pos_ofDefinedTrue, Set.inter_eq_right.mpr h]

@[simp] theorem ofDefinedTrue_defined_pos (φ : TrivalentUpdate S) :
    ofDefinedTrue (defined φ) (pos φ) = φ :=
  eq_of_defined_eq_of_pos_eq defined_ofDefinedTrue (pos_ofDefinedTrue_of_subset (pos_subset_defined φ))

/-! ### Truth at an input state -/

/-- `φ` is defined at `g` when some transition from `g` is defined ([van-den-berg-1996] (25)). -/
def DefinedAt (φ : TrivalentUpdate S) (g : S) : Prop := g ∈ (defined φ).dom

/-- `φ` is true at `g` when some transition from `g` is true. -/
def TrueAt (φ : TrivalentUpdate S) (g : S) : Prop := g ∈ (pos φ).dom

/-- `φ` is false at `g` when it is defined there but not true. -/
def FalseAt (φ : TrivalentUpdate S) (g : S) : Prop := DefinedAt φ g ∧ ¬TrueAt φ g

/-- `φ` is two-valued: defined at every input state. -/
def IsTotal (φ : TrivalentUpdate S) : Prop := ∀ g, DefinedAt φ g

theorem TrueAt.definedAt (h : TrueAt φ g) : DefinedAt φ g :=
  let ⟨k, hk⟩ := h; ⟨k, pos_subset_defined φ hk⟩

/-! ### Equivalences

Strong equivalence, the same defined and the same true transitions, is equality
(`eq_iff_defined_eq_and_pos_eq`). -/

/-- Weak equivalence: the same true transitions ([van-den-berg-1996] Definition 2.3). -/
def WeakEquiv (φ ψ : TrivalentUpdate S) : Prop := pos φ = pos ψ

/-- Static equivalence: true at the same input states ([van-den-berg-1996] Definition 2.3). -/
def StaticEquiv (φ ψ : TrivalentUpdate S) : Prop := ∀ g, TrueAt φ g ↔ TrueAt ψ g

theorem WeakEquiv.staticEquiv (h : WeakEquiv φ ψ) : StaticEquiv φ ψ := fun g ↦ by
  rw [TrueAt, TrueAt, h]

/-! ### Static connectives -/

@[simp] theorem defined_compl (φ : TrivalentUpdate S) : defined φᶜ = defined φ := by
  ext p; simp [defined]

@[simp] theorem pos_compl (φ : TrivalentUpdate S) : pos φᶜ = neg φ := by
  ext p; simp [pos, neg]

@[simp] theorem neg_compl (φ : TrivalentUpdate S) : neg φᶜ = pos φ := by
  ext p; simp [pos, neg]

/-- The presupposition operator `+φ` ([van-den-berg-1996] Table 2.1, (47)): Beaver's operator
pointwise, keeping the true transitions and leaving the rest undefined. -/
def presup (φ : TrivalentUpdate S) : TrivalentUpdate S := fun p ↦ φ p ⊔ .undefined

/-- Definedness `𝒟φ` ([van-den-berg-1996] Table 2.1): every defined transition is true, and the
rest stay undefined. It is excluded middle `φ ∪ −φ` (`definedness_eq_sdisj`). -/
def definedness (φ : TrivalentUpdate S) : TrivalentUpdate S := fun p ↦ φ p ⊔ (φ p)ᶜ

@[simp] theorem defined_presup (φ : TrivalentUpdate S) : defined (presup φ) = pos φ := by
  ext p; simp only [defined, pos, presup, Set.mem_compl_iff, mem_gapExt, mem_posExt]
  cases φ p <;> decide

@[simp] theorem pos_presup (φ : TrivalentUpdate S) : pos (presup φ) = pos φ := by
  ext p; simp only [pos, presup, mem_posExt]; cases φ p <;> decide

@[simp] theorem defined_definedness (φ : TrivalentUpdate S) :
    defined (definedness φ) = defined φ := by
  ext p; simp only [defined, definedness, Set.mem_compl_iff, mem_gapExt]; cases φ p <;> decide

@[simp] theorem pos_definedness (φ : TrivalentUpdate S) : pos (definedness φ) = defined φ := by
  ext p; simp only [defined, pos, definedness, Set.mem_compl_iff, mem_gapExt, mem_posExt]
  cases φ p <;> decide

/-- Static conjunction `φ ∩ ψ` ([van-den-berg-1996] Definition 3.1): Weak Kleene conjunction of
the transitions. -/
def sconj (φ ψ : TrivalentUpdate S) : TrivalentUpdate S := fun p ↦ meetWeak (φ p) (ψ p)

/-- Static disjunction `φ ∪ ψ := −(−φ ∩ −ψ)` ([van-den-berg-1996] (32)): Weak Kleene disjunction
of the transitions. -/
def sdisj (φ ψ : TrivalentUpdate S) : TrivalentUpdate S := fun p ↦ joinWeak (φ p) (ψ p)

/-- Program disjunction `φ ⊕ ψ` ([van-den-berg-1996] Aside 2.2, (52)): Belnap disjunction of the
transitions, defined where either disjunct is. -/
def pdisj (φ ψ : TrivalentUpdate S) : TrivalentUpdate S := fun p ↦ joinBelnap (φ p) (ψ p)

@[simp] theorem defined_sconj (φ ψ : TrivalentUpdate S) :
    defined (sconj φ ψ) = defined φ ∩ defined ψ := by
  ext p; cases hφ : φ p <;> cases hψ : ψ p <;> simp [defined, sconj, meetWeak, hφ, hψ]

@[simp] theorem pos_sconj (φ ψ : TrivalentUpdate S) : pos (sconj φ ψ) = pos φ ∩ pos ψ := by
  ext p; cases hφ : φ p <;> cases hψ : ψ p <;> simp [pos, sconj, meetWeak, hφ, hψ]

theorem sdisj_eq_compl_sconj_compl (φ ψ : TrivalentUpdate S) : sdisj φ ψ = (sconj φᶜ ψᶜ)ᶜ := by
  funext p; simp only [sdisj, sconj, Pi.compl_apply]; cases φ p <;> cases ψ p <;> rfl

@[simp] theorem defined_sdisj (φ ψ : TrivalentUpdate S) :
    defined (sdisj φ ψ) = defined φ ∩ defined ψ := by
  ext p; cases hφ : φ p <;> cases hψ : ψ p <;> simp [defined, sdisj, joinWeak, hφ, hψ]

/-- The true transitions of static disjunction are those where both disjuncts are defined and one
is true; [van-den-berg-1996] (32) omits the definedness. -/
@[simp] theorem pos_sdisj (φ ψ : TrivalentUpdate S) :
    pos (sdisj φ ψ) = defined φ ∩ defined ψ ∩ (pos φ ∪ pos ψ) := by
  ext p; cases hφ : φ p <;> cases hψ : ψ p <;> simp [defined, pos, sdisj, joinWeak, hφ, hψ]

/-- Definedness is excluded middle under static disjunction ([van-den-berg-1996] p. 59). -/
theorem definedness_eq_sdisj (φ : TrivalentUpdate S) : definedness φ = sdisj φ φᶜ := by
  funext p; simp only [definedness, sdisj, Pi.compl_apply]; cases φ p <;> rfl

@[simp] theorem defined_pdisj (φ ψ : TrivalentUpdate S) :
    defined (pdisj φ ψ) = defined φ ∪ defined ψ := by
  ext p; cases hφ : φ p <;> cases hψ : ψ p <;> simp [defined, pdisj, joinBelnap, hφ, hψ]

@[simp] theorem pos_pdisj (φ ψ : TrivalentUpdate S) : pos (pdisj φ ψ) = pos φ ∪ pos ψ := by
  ext p; cases hφ : φ p <;> cases hψ : ψ p <;> simp [pos, pdisj, joinBelnap, hφ, hψ]

/-! ### Sequencing -/

/-- Sequencing `φ ∧ ψ` ([van-den-berg-1996] Definition 2.1(c), (48)): the defined transitions and
the true transitions compose separately. -/
noncomputable def seq (φ ψ : TrivalentUpdate S) : TrivalentUpdate S :=
  ofDefinedTrue (defined φ ○ defined ψ) (pos φ ○ pos ψ)

@[simp] theorem defined_seq (φ ψ : TrivalentUpdate S) :
    defined (seq φ ψ) = defined φ ○ defined ψ :=
  defined_ofDefinedTrue

@[simp] theorem pos_seq (φ ψ : TrivalentUpdate S) : pos (seq φ ψ) = pos φ ○ pos ψ :=
  pos_ofDefinedTrue_of_subset (comp_subset_comp (pos_subset_defined φ) (pos_subset_defined ψ))

/-- Sequencing is associative, the source of dynamic binding ([van-den-berg-1996] p. 49). -/
theorem seq_assoc (φ ψ χ : TrivalentUpdate S) : seq (seq φ ψ) χ = seq φ (seq ψ χ) :=
  eq_of_defined_eq_of_pos_eq (by simp [comp_assoc]) (by simp [comp_assoc])

/-- A test relates each defined input only to itself. -/
def IsTest (φ : TrivalentUpdate S) : Prop := Update.IsTest (defined φ)

/-- On tests, sequencing is Weak Kleene conjunction ([van-den-berg-1996] Aside 2.1). Only the first
conjunct need be a test: a transition from `g` back to `g` through it cannot leave `g`. -/
theorem seq_apply_self_of_isTest (hφ : IsTest φ) (g : S) :
    seq φ ψ (g, g) = meetWeak (φ (g, g)) (ψ (g, g)) := by
  have hd : g ~[defined (seq φ ψ)] g ↔ g ~[defined φ] g ∧ g ~[defined ψ] g := by
    rw [defined_seq]
    refine ⟨fun ⟨k, h₁, h₂⟩ ↦ ?_, fun ⟨h₁, h₂⟩ ↦ ⟨g, h₁, h₂⟩⟩
    obtain rfl : g = k := hφ h₁
    exact ⟨h₁, h₂⟩
  have hp : g ~[pos (seq φ ψ)] g ↔ g ~[pos φ] g ∧ g ~[pos ψ] g := by
    rw [pos_seq]
    refine ⟨fun ⟨k, h₁, h₂⟩ ↦ ?_, fun ⟨h₁, h₂⟩ ↦ ⟨g, h₁, h₂⟩⟩
    obtain rfl : g = k := hφ (pos_subset_defined φ h₁)
    exact ⟨h₁, h₂⟩
  simp only [mem_defined, mem_pos] at hd hp
  revert hd hp
  generalize seq φ ψ (g, g) = a
  generalize φ (g, g) = b
  generalize ψ (g, g) = c
  cases a <;> cases b <;> cases c <;> decide

theorem IsTotal.seq (hφ : IsTotal φ) (hψ : IsTotal ψ) : IsTotal (seq φ ψ) := fun g ↦
  let ⟨k, hk⟩ := hφ g
  let ⟨h, hh⟩ := hψ k
  ⟨h, by rw [defined_seq]; exact ⟨k, hk, hh⟩⟩

theorem IsTotal.compl (hφ : IsTotal φ) : IsTotal φᶜ := fun g ↦ by
  simpa [DefinedAt] using hφ g

/-! ### Closure and negation -/

/-- Closure `!φ` ([van-den-berg-1996] Definition 2.1(f), (50)): the test of having a defined and
of having a true output. -/
noncomputable def close (φ : TrivalentUpdate S) : TrivalentUpdate S :=
  ofDefinedTrue (Update.test (defined φ).dom) (Update.test (pos φ).dom)

@[simp] theorem defined_close (φ : TrivalentUpdate S) :
    defined (close φ) = Update.test (defined φ).dom :=
  defined_ofDefinedTrue

@[simp] theorem pos_close (φ : TrivalentUpdate S) : pos (close φ) = Update.test (pos φ).dom :=
  pos_ofDefinedTrue_of_subset <| by
    rintro ⟨g, h⟩ ⟨rfl, k, hk⟩; exact ⟨rfl, k, pos_subset_defined φ hk⟩

theorem isTotal_close (hφ : IsTotal φ) : IsTotal (close φ) := fun g ↦
  ⟨g, by rw [defined_close]; exact ⟨rfl, hφ g⟩⟩

/-- The closed negation `∼φ := −!φ` of dynamic predicate logic, inside the three-valued logic
([van-den-berg-1996] Definition 2.6, Lemma 2.5). -/
noncomputable def dplNeg (φ : TrivalentUpdate S) : TrivalentUpdate S := (close φ)ᶜ

/-- Strong dynamic negation `¬φ` ([van-den-berg-1996] Definition 2.12): a transition is true when
it is a defined transition of `φ` from an input at which `φ` is not true, and false when it is a
true transition of `φ`. -/
noncomputable def dneg (φ : TrivalentUpdate S) : TrivalentUpdate S :=
  ofDefinedTrue (pos φ ∪ {p | p ∈ defined φ ∧ ¬TrueAt φ p.1})
    {p | p ∈ defined φ ∧ ¬TrueAt φ p.1}

@[simp] theorem pos_dneg (φ : TrivalentUpdate S) :
    pos (dneg φ) = {p | p ∈ defined φ ∧ ¬TrueAt φ p.1} :=
  pos_ofDefinedTrue_of_subset Set.subset_union_right

theorem defined_dneg (φ : TrivalentUpdate S) :
    defined (dneg φ) = pos φ ∪ {p | p ∈ defined φ ∧ ¬TrueAt φ p.1} :=
  defined_ofDefinedTrue

@[simp] theorem neg_dneg (φ : TrivalentUpdate S) : neg (dneg φ) = pos φ := by
  rw [neg_eq_defined_diff_pos, pos_dneg, defined_dneg]
  ext ⟨g, h⟩
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hp | hX, hn⟩
    · exact hp
    · exact absurd hX hn
  · intro hp
    exact ⟨Or.inl hp, fun ⟨_, hT⟩ ↦ hT ⟨h, hp⟩⟩

theorem definedAt_dneg_iff (φ : TrivalentUpdate S) (g : S) :
    DefinedAt (dneg φ) g ↔ DefinedAt φ g := by
  constructor
  · rintro ⟨h, hgh⟩
    rw [defined_dneg] at hgh
    rcases hgh with hp | ⟨hd, -⟩
    · exact ⟨h, pos_subset_defined φ hp⟩
    · exact ⟨h, hd⟩
  · rintro ⟨h, hd⟩
    by_cases hT : TrueAt φ g
    · obtain ⟨k, hk⟩ := hT
      exact ⟨k, by rw [defined_dneg]; exact Or.inl hk⟩
    · exact ⟨h, by rw [defined_dneg]; exact Or.inr ⟨hd, hT⟩⟩

/-- The alternative form of strong dynamic negation ([van-den-berg-1996] p. 55): true where weak
negation is true and the closed negation is true at the input. -/
theorem pos_dneg_eq_pos_compl_inter (φ : TrivalentUpdate S) :
    pos (dneg φ) = {p | p ∈ pos φᶜ ∧ p.1 ~[pos (dplNeg φ)] p.1} := by
  ext ⟨g, h⟩
  simp only [pos_dneg, dplNeg, pos_compl, neg_eq_defined_diff_pos, defined_close, pos_close,
    Set.mem_ofPred_eq, Set.mem_sdiff, Update.mem_test, true_and]
  constructor
  · rintro ⟨hd, hT⟩
    exact ⟨⟨hd, fun hp ↦ hT ⟨h, hp⟩⟩, ⟨h, hd⟩, hT⟩
  · rintro ⟨⟨hd, -⟩, -, hT⟩
    exact ⟨hd, hT⟩

/-- The dynamic conditions on a negation ([van-den-berg-1996] Definition 2.10): a true transition
of the negation is a false transition of its argument, and a false one a true one. -/
def DynamicNegConditions (N : TrivalentUpdate S → TrivalentUpdate S) : Prop :=
  ∀ φ, pos (N φ) ⊆ neg φ ∧ neg (N φ) ⊆ pos φ

/-- The static conditions on a negation ([van-den-berg-1996] Definition 2.11): where the negation
is true its argument is false, and where the negation is false its argument is true. -/
def StaticNegConditions (N : TrivalentUpdate S → TrivalentUpdate S) : Prop :=
  ∀ φ g, (TrueAt (N φ) g → FalseAt φ g) ∧ (FalseAt (N φ) g → TrueAt φ g)

theorem dneg_dynamicNegConditions : DynamicNegConditions (dneg (S := S)) := fun φ ↦ by
  refine ⟨?_, by rw [neg_dneg]⟩
  rw [pos_dneg]
  rintro ⟨g, h⟩ ⟨hd, hT⟩
  rw [neg_eq_defined_diff_pos]
  exact ⟨hd, fun hp ↦ hT ⟨h, hp⟩⟩

theorem dneg_staticNegConditions : StaticNegConditions (dneg (S := S)) := fun φ g ↦ by
  refine ⟨?_, ?_⟩
  · rintro ⟨h, hgh⟩
    rw [pos_dneg] at hgh
    exact ⟨⟨h, hgh.1⟩, hgh.2⟩
  · rintro ⟨⟨h, hgh⟩, hnT⟩
    by_contra hT
    rw [defined_dneg] at hgh
    rcases hgh with hp | hX
    · exact hT ⟨h, hp⟩
    · exact hnT ⟨h, by rw [pos_dneg]; exact hX⟩

/-- Strong dynamic negation is the weakest negation meeting both conditions
([van-den-berg-1996] p. 54): every such negation has fewer true transitions… -/
theorem pos_subset_pos_dneg {N : TrivalentUpdate S → TrivalentUpdate S}
    (hd : DynamicNegConditions N) (hs : StaticNegConditions N) (φ : TrivalentUpdate S) :
    pos (N φ) ⊆ pos (dneg φ) := by
  rintro ⟨g, h⟩ hgh
  rw [pos_dneg]
  exact ⟨neg_subset_defined φ ((hd φ).1 hgh), ((hs φ g).1 ⟨h, hgh⟩).2⟩

/-- …and fewer false ones. -/
theorem neg_subset_neg_dneg {N : TrivalentUpdate S → TrivalentUpdate S}
    (hd : DynamicNegConditions N) (φ : TrivalentUpdate S) : neg (N φ) ⊆ neg (dneg φ) := by
  rw [neg_dneg]; exact (hd φ).2

theorem isTotal_dneg (hφ : IsTotal φ) : IsTotal (dneg φ) := fun g ↦
  (definedAt_dneg_iff φ g).mpr (hφ g)

theorem definedAt_dplNeg_iff (φ : TrivalentUpdate S) (g : S) :
    DefinedAt (dplNeg φ) g ↔ DefinedAt φ g := by
  rw [DefinedAt, DefinedAt, dplNeg, defined_compl, defined_close, Update.dom_test]

theorem trueAt_dplNeg_iff (φ : TrivalentUpdate S) (g : S) :
    TrueAt (dplNeg φ) g ↔ FalseAt φ g := by
  constructor
  · rintro ⟨h, hgh⟩
    rw [dplNeg, pos_compl, neg_eq_defined_diff_pos, defined_close, pos_close] at hgh
    obtain ⟨⟨rfl, hd⟩, hn⟩ := hgh
    exact ⟨hd, fun hT ↦ hn ⟨rfl, hT⟩⟩
  · rintro ⟨hd, hT⟩
    refine ⟨g, ?_⟩
    rw [dplNeg, pos_compl, neg_eq_defined_diff_pos, defined_close, pos_close]
    exact ⟨⟨rfl, hd⟩, fun ⟨_, hT'⟩ ↦ hT hT'⟩

theorem trueAt_dneg_iff (φ : TrivalentUpdate S) (g : S) : TrueAt (dneg φ) g ↔ FalseAt φ g := by
  constructor
  · exact (dneg_staticNegConditions φ g).1
  · rintro ⟨⟨h, hd⟩, hT⟩
    exact ⟨h, by rw [pos_dneg]; exact ⟨hd, hT⟩⟩

/-- Strong dynamic negation and the closed negation are true at the same input states
([van-den-berg-1996] Lemma 2.13). -/
theorem staticEquiv_dneg_dplNeg (φ : TrivalentUpdate S) : StaticEquiv (dneg φ) (dplNeg φ) :=
  fun g ↦ (trueAt_dneg_iff φ g).trans (trueAt_dplNeg_iff φ g).symm

/-- …and false at the same input states ([van-den-berg-1996] footnote 8). -/
theorem falseAt_dneg_iff_falseAt_dplNeg (φ : TrivalentUpdate S) (g : S) :
    FalseAt (dneg φ) g ↔ FalseAt (dplNeg φ) g := by
  rw [FalseAt, FalseAt, definedAt_dneg_iff, definedAt_dplNeg_iff, staticEquiv_dneg_dplNeg φ g]

/-- Strong dynamic negation is definable from the other connectives: `¬φ = +−(!φ ∧ −φ) ∩ −φ`
([van-den-berg-1996] Fact 3.3, (51)). -/
theorem dneg_eq (φ : TrivalentUpdate S) :
    dneg φ = sconj (presup (seq (close φ) φᶜ)ᶜ) φᶜ := by
  have key : ∀ g h, g ~[neg (seq (close φ) φᶜ)] h ↔
      g ~[defined φ] h ∧ ¬(TrueAt φ g ∧ g ~[neg φ] h) := by
    intro g h
    rw [neg_eq_defined_diff_pos, defined_seq, pos_seq, defined_close, pos_close, defined_compl,
      pos_compl]
    simp only [Set.mem_sdiff, Update.mem_test_comp]
    constructor
    · rintro ⟨⟨-, hd⟩, hn⟩; exact ⟨hd, hn⟩
    · rintro ⟨hd, hn⟩; exact ⟨⟨⟨h, hd⟩, hd⟩, hn⟩
  have facts : ∀ g h, (g ~[neg φ] h ↔ g ~[defined φ] h ∧ ¬g ~[pos φ] h) ∧
      (g ~[pos φ] h → g ~[defined φ] h) ∧ (g ~[pos φ] h → TrueAt φ g) := fun g h ↦
    ⟨by rw [neg_eq_defined_diff_pos]; rfl, fun hp ↦ pos_subset_defined φ hp, fun hp ↦ ⟨h, hp⟩⟩
  refine eq_of_defined_eq_of_pos_eq ?_ ?_
  · ext ⟨g, h⟩
    rw [defined_dneg, defined_sconj, defined_presup, pos_compl, defined_compl]
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [key, (facts g h).1]
    have := (facts g h).2
    tauto
  · ext ⟨g, h⟩
    rw [pos_dneg, pos_sconj, pos_presup, pos_compl, pos_compl]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [key, (facts g h).1]
    have := (facts g h).2
    tauto

/-- The simpler `−!φ ∧ −φ` has the true transitions of `¬φ` ([van-den-berg-1996] p. 61)… -/
theorem weakEquiv_seq_dplNeg_compl_dneg (φ : TrivalentUpdate S) :
    WeakEquiv (seq (dplNeg φ) φᶜ) (dneg φ) := by
  unfold WeakEquiv
  ext ⟨g, h⟩
  rw [pos_seq, pos_compl, pos_dneg]
  constructor
  · rintro ⟨k, hk, hn⟩
    rw [dplNeg, pos_compl, neg_eq_defined_diff_pos, defined_close, pos_close] at hk
    obtain ⟨⟨rfl, -⟩, hnT⟩ := hk
    rw [neg_eq_defined_diff_pos] at hn
    exact ⟨hn.1, fun hT ↦ hnT ⟨rfl, hT⟩⟩
  · rintro ⟨hd, hT⟩
    refine ⟨g, ?_, ?_⟩
    · rw [dplNeg, pos_compl, neg_eq_defined_diff_pos, defined_close, pos_close]
      exact ⟨⟨rfl, h, hd⟩, fun ⟨_, hT'⟩ ↦ hT hT'⟩
    · rw [neg_eq_defined_diff_pos]
      exact ⟨hd, fun hp ↦ hT ⟨h, hp⟩⟩

/-- …but not its false transitions: it is false for every false transition of `φ`, even from an
input at which `φ` is true. -/
theorem exists_seq_dplNeg_compl_ne_dneg :
    ∃ φ : TrivalentUpdate Bool, seq (dplNeg φ) φᶜ ≠ dneg φ := by
  let φ : TrivalentUpdate Bool := fun p ↦ if p.2 then .true else .false
  refine ⟨φ, fun h ↦ ?_⟩
  have hT : TrueAt φ Bool.true := ⟨Bool.true, rfl⟩
  have h₁ : Bool.true ~[defined (seq (dplNeg φ) φᶜ)] Bool.false := by
    rw [defined_seq, dplNeg, defined_compl, defined_close, defined_compl]
    exact ⟨Bool.true, ⟨rfl, Bool.false, by simp [φ]⟩, by simp [φ]⟩
  have h₂ : ¬Bool.true ~[defined (dneg φ)] Bool.false := by
    rw [defined_dneg]
    rintro (hp | ⟨-, hn⟩)
    · simp [φ] at hp
    · exact hn hT
  exact h₂ (h ▸ h₁)

end TrivalentUpdate

end DynamicSemantics
