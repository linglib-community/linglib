module

public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.Basic
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Order.RelClasses

/-!
# Argument selection

Dowty's argument selection principle compares two arguments of a predicate by counting. The one
with more Proto-Agent entailments is lexicalized as subject, and on a tie the one with fewer
Proto-Patient entailments; arguments with equal counts may be lexicalized either way. The
principle is thus the lexicographic order on a pair of counts, `EntailmentProfile.selectionRank`,
and `EntailmentProfile.Outranks` inherits what that order has: it is a
[strict weak order](##ArgumentStructure.EntailmentProfile.isStrictWeakOrder_outranks), so role
hierarchies are chains, and two arguments
[alternate when neither outranks the other](##ArgumentStructure.EntailmentProfile.alternates_iff).
Of two nonsubject arguments, the one with more Proto-Patient entailments is lexicalized as direct
object and the other as oblique, again a strict weak order. The principle counts entailments, so a
profile whose entailments of a cluster strictly include another's is selected over it, though a
profile may be selected over another without including its entailments.

## Implementation notes

`selectionRank` reads the Proto-Agent clause of the principle first and lets the Proto-Patient
clause decide ties, and "approximately equal" in the corollaries is read as equal.

## References

* [dowty-1991]
-/

@[expose] public section

namespace ArgumentStructure.EntailmentProfile

open scoped Finset

variable (p q r : EntailmentProfile)

/-! ### Subject selection -/

/-- The counts the selection principle compares: the number of Proto-Agent entailments and then,
in reverse, the number of Proto-Patient entailments. -/
def selectionRank : ℕ ×ₗ ℕᵒᵈ := toLex (#p.protoAgent, OrderDual.toDual #p.protoPatient)

/-- By the selection principle ([dowty-1991] (31)), `p` is lexicalized as subject over `q` when it
has strictly more Proto-Agent entailments, or as many and strictly fewer Proto-Patient
entailments. -/
def Outranks : Prop := q.selectionRank < p.selectionRank

/-- Two arguments with equal counts may be lexicalized either way ([dowty-1991] (32)). -/
def Alternates : Prop := p.selectionRank = q.selectionRank

variable {p q r}

theorem outranks_iff : Outranks p q ↔
    #q.protoAgent < #p.protoAgent ∨
      (#p.protoAgent = #q.protoAgent ∧ #p.protoPatient < #q.protoPatient) := by
  simp [Outranks, selectionRank, Prod.Lex.toLex_lt_toLex, eq_comm]

theorem alternates_iff_card :
    Alternates p q ↔ #p.protoAgent = #q.protoAgent ∧ #p.protoPatient = #q.protoPatient := by
  simp [Alternates, selectionRank]

instance : Decidable (Outranks p q) := decidable_of_iff' _ outranks_iff
instance : Decidable (Alternates p q) := decidable_of_iff' _ alternates_iff_card

instance isStrictWeakOrder_outranks : IsStrictWeakOrder EntailmentProfile Outranks :=
  haveI : IsStrictWeakOrder (ℕ ×ₗ ℕᵒᵈ)ᵒᵈ (· < ·) := isStrictWeakOrder_of_isOrderConnected
  inferInstanceAs (IsStrictWeakOrder _
    (InvImage (· < ·) fun p : EntailmentProfile ↦ OrderDual.toDual p.selectionRank))

theorem Outranks.trans (h : Outranks p q) (h' : Outranks q r) : Outranks p r := lt_trans h' h

theorem Outranks.asymm (h : Outranks p q) : ¬ Outranks q p := lt_asymm h

theorem alternates_iff : Alternates p q ↔ ¬ Outranks p q ∧ ¬ Outranks q p := by
  simp only [Outranks, Alternates, not_lt]; exact le_antisymm_iff

/-- Of two arguments one is selected as subject over the other, or they alternate. -/
theorem outranks_or_alternates_or_outranks (p q : EntailmentProfile) :
    Outranks p q ∨ Alternates p q ∨ Outranks q p :=
  (lt_trichotomy q.selectionRank p.selectionRank).imp_right (Or.imp_left Eq.symm)

theorem alternates_equivalence : Equivalence Alternates := ⟨fun _ ↦ rfl, Eq.symm, Eq.trans⟩

theorem Outranks.of_alternates_left (h : Outranks p q) (h' : Alternates p r) : Outranks r q :=
  lt_of_lt_of_eq h h'

theorem Outranks.of_alternates_right (h : Outranks p q) (h' : Alternates q r) : Outranks p r :=
  lt_of_eq_of_lt h'.symm h

theorem outranks_of_protoAgent_ssubset (h : q.protoAgent ⊂ p.protoAgent) : Outranks p q :=
  outranks_iff.2 (.inl (Finset.card_lt_card h))

theorem outranks_of_protoAgent_nonempty (hp : p.protoAgent.Nonempty) (hq : q.protoAgent = ∅) :
    Outranks p q :=
  outranks_iff.2 (.inl (by simpa [hq] using hp.card_pos))

/-! ### Object selection -/

variable (p q)

/-- Of two nonsubject arguments, the one with more Proto-Patient entailments is lexicalized as
direct object and the other as oblique ([dowty-1991] (33)). -/
def DirectObjectOver : Prop := #q.protoPatient < #p.protoPatient

/-- Two nonsubject arguments with equal Proto-Patient counts may either be direct object
([dowty-1991] (33)). -/
def EitherObject : Prop := #p.protoPatient = #q.protoPatient

instance : Decidable (DirectObjectOver p q) := inferInstanceAs (Decidable (_ < _))
instance : Decidable (EitherObject p q) := inferInstanceAs (Decidable (_ = _))

variable {p q}

instance isStrictWeakOrder_directObjectOver :
    IsStrictWeakOrder EntailmentProfile DirectObjectOver :=
  haveI : IsStrictWeakOrder ℕᵒᵈ (· < ·) := isStrictWeakOrder_of_isOrderConnected
  inferInstanceAs (IsStrictWeakOrder _
    (InvImage (· < ·) fun p : EntailmentProfile ↦ OrderDual.toDual #p.protoPatient))

theorem DirectObjectOver.trans (h : DirectObjectOver p q) (h' : DirectObjectOver q r) :
    DirectObjectOver p r :=
  lt_trans h' h

theorem eitherObject_iff :
    EitherObject p q ↔ ¬ DirectObjectOver p q ∧ ¬ DirectObjectOver q p := by
  simp only [DirectObjectOver, EitherObject, not_lt]; exact le_antisymm_iff

theorem directObjectOver_of_protoPatient_ssubset (h : q.protoPatient ⊂ p.protoPatient) :
    DirectObjectOver p q :=
  Finset.card_lt_card h

/-- An argument that alternates with another for subject may equally be direct object. -/
theorem Alternates.eitherObject (h : Alternates p q) : EitherObject p q :=
  (alternates_iff_card.1 h).2

end ArgumentStructure.EntailmentProfile
