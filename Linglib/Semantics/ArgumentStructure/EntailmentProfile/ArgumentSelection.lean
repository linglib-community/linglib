module

public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.Basic

/-!
# Argument selection

This file defines Dowty's argument selection principle and its corollaries on entailment profiles.
Of two arguments of a predicate, the one with more Proto-Agent entailments is lexicalized as
subject, and on a tie the one with fewer Proto-Patient entailments; arguments with equal counts may
be lexicalized either way. Of two nonsubject arguments, the one with more Proto-Patient
entailments is lexicalized as direct object and the other as oblique. The principle counts
entailments, so a profile whose Proto-Patient entailments strictly include another's is selected as
direct object over it, though a profile may be selected over another without including its
entailments.

## Main definitions

* `EntailmentProfile.Outranks`: the selection principle.
* `EntailmentProfile.Alternates`: the first corollary, equal counts.
* `EntailmentProfile.DirectObjectOver`, `EntailmentProfile.EitherObject`: the second corollary.

## Main results

* `EntailmentProfile.alternates_iff`: the first corollary is the failure of the principle to
  select either way.
* `EntailmentProfile.directObjectOver_of_protoPatient_ssubset`: strictly more Proto-Patient
  entailments, by inclusion, select the direct object.

## Implementation notes

`Outranks` reads the Proto-Agent clause of the principle first and lets the Proto-Patient clause
decide ties, and "approximately equal" in the corollaries is read as equal.

## References

* [dowty-1991]
-/

@[expose] public section

namespace ArgumentStructure.EntailmentProfile

open scoped Finset

variable (p q : EntailmentProfile)

/-- By the selection principle ([dowty-1991] (31)), `p` is lexicalized as subject over `q` when it
has strictly more Proto-Agent entailments, or as many and strictly fewer Proto-Patient
entailments. -/
def Outranks : Prop :=
  #q.protoAgent < #p.protoAgent ∨
    (#p.protoAgent = #q.protoAgent ∧ #p.protoPatient < #q.protoPatient)

/-- Two arguments with equal counts may be lexicalized either way ([dowty-1991] (32)). -/
def Alternates : Prop := #p.protoAgent = #q.protoAgent ∧ #p.protoPatient = #q.protoPatient

/-- Of two nonsubject arguments, the one with more Proto-Patient entailments is lexicalized as
direct object and the other as oblique ([dowty-1991] (33)). -/
def DirectObjectOver : Prop := #q.protoPatient < #p.protoPatient

/-- Two nonsubject arguments with equal Proto-Patient counts may either be direct object
([dowty-1991] (33)). -/
def EitherObject : Prop := #p.protoPatient = #q.protoPatient

instance : Decidable (Outranks p q) := inferInstanceAs (Decidable (_ ∨ _))
instance : Decidable (Alternates p q) := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable (DirectObjectOver p q) := inferInstanceAs (Decidable (_ < _))
instance : Decidable (EitherObject p q) := inferInstanceAs (Decidable (_ = _))

variable {p q}

theorem alternates_iff : Alternates p q ↔ ¬ Outranks p q ∧ ¬ Outranks q p := by
  unfold Alternates Outranks; omega

theorem alternates_self : Alternates p p := ⟨rfl, rfl⟩

theorem outranks_of_protoAgent_nonempty (hp : p.protoAgent.Nonempty) (hq : q.protoAgent = ∅) :
    Outranks p q :=
  .inl (by simpa [hq] using hp.card_pos)

theorem directObjectOver_of_protoPatient_ssubset (h : q.protoPatient ⊂ p.protoPatient) :
    DirectObjectOver p q :=
  Finset.card_lt_card h

end ArgumentStructure.EntailmentProfile
