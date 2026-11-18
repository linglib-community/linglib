module

public import Linglib.Semantics.Negation.Polarity
public import Linglib.Core.Order.Flat
public import Linglib.Logic.Natural.Relation

/-!
# Implication signatures

A complement-taking operator such as *manage*, *force* or *refuse* implies something about its
complement in a positive context, in a negative context, or in both. Nairn, Condoravdi and Karttunen
classify these operators by their implication signature, the polarity of the complement each
context implies, if any: *manage* is `+/−`, since *managed to leave* implies *left* and *didn't
manage to leave* implies *didn't leave*; *force* is `+/◦`, *refuse* `−/◦`, *hesitate* `◦/+`, and
*want* `◦/◦`. Each slot is a flat value, `◦` being `⊥`, so signatures are ordered by how much they
imply.

Each implication is [an atomic
constraint](##NaturalLogic.ImplicationSignature.holds_ofPolarities_iff) of
natural logic between the claim and its complement, and a signature implies more exactly when it
[constrains more](##NaturalLogic.ImplicationSignature.constraints_subset_constraints). Its
constraints are those of one of the seven relations [unless both slots imply the same
polarity](##NaturalLogic.ImplicationSignature.exists_constraints_eq_iff); a factive `+/+` or a
counterfactive `−/−` [settles the complement whatever the
claim](##NaturalLogic.ImplicationSignature.forall_holds_constraints_factive_iff), so that its
implication survives negation as a presupposition does.

## References

* [nairn-condoravdi-karttunen-2006]
* [maccartney-manning-2009]
-/

@[expose] public section

namespace NaturalLogic

/-- The implication signature of a complement-taking operator gives the polarity of the complement
it implies in a positive context and in a negative context, `⊥` where it implies nothing. -/
@[ext]
structure ImplicationSignature where
  /-- The complement's implied polarity in a positive context. -/
  positive : Flat Polarity
  /-- The complement's implied polarity in a negative context. -/
  negative : Flat Polarity
  deriving DecidableEq, Repr

namespace ImplicationSignature

variable {s t : ImplicationSignature} {m q : Polarity}

/-- The polarity of the complement implied in a context of polarity `m`. -/
def implied (s : ImplicationSignature) : Polarity → Flat Polarity
  | .positive => s.positive
  | .negative => s.negative

@[simp] theorem implied_positive (s : ImplicationSignature) : s.implied .positive = s.positive :=
  rfl

@[simp] theorem implied_negative (s : ImplicationSignature) : s.implied .negative = s.negative :=
  rfl

theorem implied_injective : Function.Injective implied := fun _ _ h ↦
  ImplicationSignature.ext (congrFun h .positive) (congrFun h .negative)

/-- One signature is below another when every context implies less under it. -/
instance : PartialOrder ImplicationSignature :=
  PartialOrder.lift implied implied_injective

theorem le_iff : s ≤ t ↔ s.positive ≤ t.positive ∧ s.negative ≤ t.negative :=
  ⟨fun h ↦ ⟨h .positive, h .negative⟩, fun h m ↦ by cases m <;> simp [h.1, h.2]⟩

instance : DecidableLE ImplicationSignature := fun _ _ ↦ decidable_of_iff _ le_iff.symm

/-- The signature `◦/◦` implies nothing in either context. -/
instance : OrderBot ImplicationSignature where
  bot := ⟨⊥, ⊥⟩
  bot_le _ := le_iff.2 ⟨bot_le, bot_le⟩

@[simp] theorem bot_positive : (⊥ : ImplicationSignature).positive = ⊥ := rfl

@[simp] theorem bot_negative : (⊥ : ImplicationSignature).negative = ⊥ := rfl

/-! ### Implications as constraints -/

open Relation.Atom (ofPolarities ofPolarities_injective)

/-- A context of polarity `m` implying the complement of polarity `q` constrains the claim and its
complement by `Relation.Atom.ofPolarities m q`: over propositions, the claim of polarity `m` entails
the complement of polarity `q`. -/
theorem holds_ofPolarities_iff {W : Type*} {x y : Set W} :
    (ofPolarities m q).Holds x y ↔ m • x ⊆ q • y := by
  cases m <;> cases q
  · exact Iff.rfl
  · exact Set.subset_compl_iff_disjoint_right.symm
  · exact codisjoint_iff.trans Set.compl_subset_iff_union.symm
  · exact Set.compl_subset_compl.symm

/-- The constraints a signature puts on a claim and its complement, one for each context in which
it implies something. -/
def constraints (s : ImplicationSignature) : Finset Relation.Atom :=
  {a | ∃ m q : Polarity, s.implied m = q ∧ ofPolarities m q = a}

theorem mem_constraints {a : Relation.Atom} :
    a ∈ s.constraints ↔ ∃ m q : Polarity, s.implied m = q ∧ ofPolarities m q = a := by
  simp [constraints]

theorem ofPolarities_mem_constraints : ofPolarities m q ∈ s.constraints ↔ s.implied m = q := by
  simp [mem_constraints, ofPolarities_injective.eq_iff]

/-- A signature implies more than another exactly when it constrains more. -/
theorem constraints_subset_constraints : s.constraints ⊆ t.constraints ↔ s ≤ t := by
  refine ⟨fun h m ↦ ?_, fun h a ha ↦ ?_⟩
  · cases hs : s.implied m with
    | bot => exact bot_le
    | coe q =>
      exact Flat.coe_le_iff.2
        (ofPolarities_mem_constraints.1 (h (ofPolarities_mem_constraints.2 hs)))
  · obtain ⟨m, q, hs, rfl⟩ := mem_constraints.1 ha
    exact ofPolarities_mem_constraints.2 (Flat.coe_le_iff.1 (hs ▸ h m))

/-- The constraints of a signature are those of one of the seven relations exactly when its two
slots do not imply the same polarity. -/
theorem exists_constraints_eq_iff :
    (∃ R : Relation, R.constraints = s.constraints) ↔ ∀ q : Polarity, s ≠ ⟨q, q⟩ := by
  obtain ⟨_ | p, _ | n⟩ := s <;> (try cases p) <;> (try cases n) <;> decide

section Factive

variable {α : Type*} [Lattice α] [BoundedOrder α] {x y : α}

/-- The constraints of the factive signature `+/+` hold of a claim and its complement exactly when
the complement is `⊤`, whatever the claim. -/
theorem forall_holds_constraints_factive_iff :
    (∀ a ∈ (⟨↑Polarity.positive, ↑Polarity.positive⟩ : ImplicationSignature).constraints,
      a.Holds x y) ↔ y = ⊤ := by
  rw [show (⟨↑Polarity.positive, ↑Polarity.positive⟩ : ImplicationSignature).constraints =
    {.le, .codisjoint} by decide]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    Relation.Atom.Holds]
  exact ⟨fun h ↦ h.2.eq_top_of_ge h.1, fun h ↦ h ▸ ⟨le_top, codisjoint_top_right⟩⟩

/-- The constraints of the counterfactive signature `−/−` hold of a claim and its complement
exactly when the complement is `⊥`, whatever the claim. -/
theorem forall_holds_constraints_counterfactive_iff :
    (∀ a ∈ (⟨↑Polarity.negative, ↑Polarity.negative⟩ : ImplicationSignature).constraints,
      a.Holds x y) ↔ y = ⊥ := by
  rw [show (⟨↑Polarity.negative, ↑Polarity.negative⟩ : ImplicationSignature).constraints =
    {.disjoint, .ge} by decide]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    Relation.Atom.Holds]
  exact ⟨fun h ↦ h.1.eq_bot_of_ge h.2, fun h ↦ h ▸ ⟨disjoint_bot_right, bot_le⟩⟩

end Factive

end ImplicationSignature

end NaturalLogic
