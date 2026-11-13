module

public import Linglib.Data.Examples.Matthewson2006
public import Linglib.Data.Examples.Readers
public import Linglib.Semantics.Aspect.Viewpoint
public import Linglib.Semantics.Tense.Pronoun

/-!
# Matthewson (2006): Temporal semantics in a superficially tenseless language

A St'át'imcets sentence with no temporal marking is past or present and never future. Matthewson
gives it a silent tense, a pronoun over reference times no part of which follows the utterance
time, so that [the adverbials it accepts are the past and the present ones](##locatable_rows). The
tense is one morpheme and not a silent past beside a silent present: with one conjoined subject's
event in the past and the other's at the utterance time, [one nonfuture reference time contains
both, and no past or present one does](##tense_and_not_past_or_present_of_split). The future needs
*kelh*, which places an event after the reference time; at the utterance time [the event is to
come](##precedes_of_mem_kelh), and at a past reference time [it need not
be](##exists_kelh_not_precedes), the reading of English *would*.

## Implementation notes

* Times are intervals and an assignment gives the reference time of each index, the index `0`
  being the utterance time, as for the tenses of [kratzer-1998], whose framework the paper adopts.
* A sentence is true where its tense denotes a reference time of which the aspect phrase holds,
  the truth condition of `Definite.toTrivalent`.
* The paper gives the entry of the English past and none for the present; the present is taken to
  denote a reference time that is the utterance time.
* Both conjuncts of (16)–(18) are perfective. The one in progress has the subinterval property, so
  that a part of it lies within the reference time
  (`Aspect.HasSubintervalProperty.unbounded_subset_prfv`); the theorem takes that part as the
  event at the utterance time.
* *Kelh* is the temporal operator of (36), `Aspect.prospective`; its modality and the enclitic
  *tu7* are not represented.

## References

* [matthewson-2006]
* [kratzer-1998]
-/

@[expose] public section

namespace Matthewson2006

open Allen Aspect Set
open Tense (pronoun mem_pronoun)
open Event (τ)

variable {W T E : Type*} [LinearOrder T] [Event.TemporalTrace E (NonemptyInterval T)]
  {P Q : W → E → Prop}
  {p : W → Set (NonemptyInterval T)} {g : ℕ → NonemptyInterval T} {u : NonemptyInterval T}
  {w : W} {i : ℕ}

/-! ### The tenses -/

/-- (13): the tense of a superficially tenseless sentence denotes the reference time of its index,
defined where no part of it follows the utterance time. -/
abbrev TENSE (i : ℕ) : Definite (ℕ → NonemptyInterval T) W (NonemptyInterval T) :=
  pronoun (toSetRel endsNoLater) i 0

/-- (11): the English past denotes a reference time before the utterance time. -/
abbrev PAST (i : ℕ) : Definite (ℕ → NonemptyInterval T) W (NonemptyInterval T) :=
  pronoun (toSetRel precedes) i 0

/-- The present denotes a reference time that is the utterance time. -/
abbrev PRESENT (i : ℕ) : Definite (ℕ → NonemptyInterval T) W (NonemptyInterval T) :=
  pronoun (toSetRel Allen.eq) i 0

theorem mem_TENSE {t : NonemptyInterval T} :
    t ∈ TENSE (W := W) i g w ↔ (g i).snd ≤ (g 0).snd ∧ g i = t := by
  simp

-- (13) in the paper's words
theorem TENSE_dom_iff :
    (TENSE (W := W) i g w).Dom ↔ ∀ k ≤ g i, ¬ (g 0).Precedes k := by
  simp [NonemptyInterval.forall_le_not_precedes_iff']

-- (15)
theorem exists_mem_TENSE_prfv : (∃ t ∈ TENSE i g w, t ∈ PRFV P w) ↔
    (g i).snd ≤ (g 0).snd ∧ ∃ e, τ e ≤ g i ∧ P w e := by
  simp [mem_prfv]

-- (6): a nonfuture reference time is not after the utterance time
theorem not_precedes_of_mem_TENSE {t : NonemptyInterval T} (h : t ∈ TENSE (W := W) i g w) :
    ¬ (g 0).Precedes t := by
  obtain ⟨hle, rfl⟩ := mem_TENSE.1 h
  exact fun hlt ↦ (((g i).fst_le_snd.trans hle).not_gt hlt)

/-- With every event of one conjunct before the utterance time and every event of the other
within it (16)–(18), some nonfuture reference time contains an event of each, and no past
reference time and no present one does. -/
theorem tense_and_not_past_or_present_of_split (hi : i ≠ 0) (hP : ∃ e, P w e) (hQ : ∃ e, Q w e)
    (hP' : ∀ e, P w e → (τ e).Precedes u) (hQ' : ∀ e, Q w e → τ e ≤ u) :
    (∃ g : ℕ → NonemptyInterval T, g 0 = u ∧ ∃ t ∈ TENSE i g w, t ∈ PRFV P w ∩ PRFV Q w) ∧
      (∀ g : ℕ → NonemptyInterval T, g 0 = u → ¬ ∃ t ∈ PAST i g w, t ∈ PRFV P w ∩ PRFV Q w) ∧
      ∀ g : ℕ → NonemptyInterval T, g 0 = u →
        ¬ ∃ t ∈ PRESENT i g w, t ∈ PRFV P w ∩ PRFV Q w := by
  obtain ⟨e₁, h₁⟩ := hP
  obtain ⟨e₂, h₂⟩ := hQ
  refine ⟨⟨Function.update (fun _ ↦ u) i (τ e₁ ⊔ τ e₂), by simp [Function.update_of_ne hi.symm],
    τ e₁ ⊔ τ e₂, ?_, ⟨e₁, le_sup_left, h₁⟩, e₂, le_sup_right, h₂⟩, ?_, ?_⟩
  · simpa [Function.update_of_ne hi.symm] using
      ⟨(hP' e₁ h₁).le.trans u.fst_le_snd,
        (NonemptyInterval.le_def.1 (hQ' e₂ h₂)).2⟩
  · rintro g rfl ⟨t, ht, -, e, hle, he⟩
    obtain ⟨hlt, rfl⟩ := mem_pronoun.1 ht
    rw [mem_toSetRel, relation_mem_precedes] at hlt
    exact (((NonemptyInterval.le_def.1 (hQ' e he)).1.trans
      ((τ e).fst_le_snd.trans (NonemptyInterval.le_def.1 hle).2)).not_gt hlt)
  · rintro g rfl ⟨t, ht, ⟨e, hle, he⟩, -⟩
    obtain ⟨heq, rfl⟩ := mem_pronoun.1 ht
    rw [mem_toSetRel, relation_mem_eq] at heq
    exact ((((NonemptyInterval.le_def.1 (heq ▸ hle)).1).trans (τ e).fst_le_snd).not_gt
      (hP' e he))

/-! ### The future -/

-- (38)
theorem exists_mem_TENSE_kelh : (∃ t ∈ TENSE i g w, t ∈ prospective (PRFV P) w) ↔
    (g i).snd ≤ (g 0).snd ∧ ∃ e, (g i).Precedes (τ e) ∧ P w e := by
  simp [prospective_prfv]

/-- With the utterance time for its reference time, a sentence with *kelh* is true only of an
event after the utterance time (7). -/
theorem precedes_of_mem_kelh (h : g i = g 0) (ht : ∃ t ∈ TENSE i g w, t ∈ prospective (PRFV P) w) :
    ∃ e, (g 0).Precedes (τ e) ∧ P w e :=
  h ▸ (exists_mem_TENSE_kelh.1 ht).2

/-- With a past reference time, a sentence with *kelh* is true of an event before the utterance
time, the reading of *would* in (39). -/
theorem exists_kelh_not_precedes :
    ∃ (P : Unit → NonemptyInterval ℤ → Prop) (g : ℕ → NonemptyInterval ℤ),
      (∃ t ∈ TENSE 1 g (), t ∈ prospective (PRFV P) ()) ∧
        ∀ e, P () e → (τ e).Precedes (g 0) := by
  refine ⟨fun _ e ↦ e = .pure 1, fun n ↦ if n = 0 then .pure 2 else .pure 0,
    exists_mem_TENSE_kelh.2 ⟨by decide, .pure 1, by decide, rfl⟩, ?_⟩
  rintro e rfl
  decide

/-! ### The adverbials -/

/-- An adverbial placing the reference time before, at or after the utterance time is compatible
with the tense when some nonfuture reference time is so placed. -/
def Locatable (o : Ordering) : Prop :=
  ∃ t u : NonemptyInterval ℤ, t.snd ≤ u.snd ∧ t.position u = o

theorem locatable_iff {o : Ordering} : Locatable o ↔ o ≠ .gt := by
  cases o
  · exact iff_of_true ⟨.pure 0, .pure 1, by decide, by decide⟩ (by decide)
  · exact iff_of_true ⟨.pure 0, .pure 0, by decide, by decide⟩ (by decide)
  · refine iff_of_false ?_ (by decide)
    rintro ⟨t, u, h, hpos⟩
    exact ((t.fst_le_snd.trans h).not_gt (NonemptyInterval.position_eq_gt.1 hpos))

instance (o : Ordering) : Decidable (Locatable o) := decidable_of_iff _ locatable_iff.symm

/-- Where a row's adverbial places the reference time. -/
def adverbial (e : Datum) : Option Ordering :=
  e.parse? "adverbial" [("past", .lt), ("present", .eq), ("future", .gt)]

/-- A superficially tenseless sentence accepts the present and past adverbials of (5) and rejects
the future ones of (6). -/
theorem locatable_rows :
    Datum.Checks adverbial (fun o ↦ .ofProp (Locatable o)) Examples.all 6 := by
  decide

end Matthewson2006
