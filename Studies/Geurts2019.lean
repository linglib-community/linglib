module

public import Linglib.Discourse.Commitment.Proposition

/-!
# Geurts (2019): Communication as commitment sharing

Geurts takes a speech act to commit the speaker to the hearer to act on a proposition, a
three-place relation $C_{a,b}\,p$ closed under entailment, here the commitment proposition
`(a, b) ⊢[O] p` over a relation for each ordered pair. Common ground is mutual commitment.
Acceptance, that a commitment is one both parties are committed to, is
[a condition on the two relations](##acceptance_iff) that
[puts every commitment in the common ground](##Acceptance.committed_subset_commonGround),
[makes a shared commitment a mutual one](##Acceptance.commonGround_eq_shared) and
[turns an accepted offer into a promise](##Acceptance.committed_of_offer). Integrity, that one
is not committed to one person against what one is committed to towards another, says that
[the two commitments leave a world open](##integrity_iff), and with it
[a speaker who has made up her mind believes what she says](##Integrity.committed_self), a
private commitment being a belief or an intention.

## Implementation notes

* Mutual commitment is necessity along the transitive closure of the two relations, which is
  [every iterate of sharing](##commonGround_eq_iInter). The paper's cascade lists the alternating
  strings $C_{a,b} C_{b,a} \cdots p$; the iterates also contain repetitions such as
  $C_{a,b} C_{a,b}\,p$, which follow from the alternating ones when the relations are transitive,
  as Acceptance makes them.
* Commitment sharing is a default and is not a law here. The futurity marker of the analysis of
  questions, permissions and the telic and atelic kinds of commitment are not represented.

## References

* [geurts-2019]
-/

@[expose] public section

namespace Geurts2019

open Commitment
open ModalLogic (IsSerial)
open scoped SetRel

variable {A W : Type*} (O : A × A → SetRel W W) (a b c : A) (p : Set W)

/-- `a` and `b` share a commitment to act on `p` when each is committed to the other (p. 17). -/
def shared : Set W := (O (a, b) ∪ O (b, a)).core p

theorem shared_eq : shared O a b p = ((a, b) ⊢[O] p) ∩ ((b, a) ⊢[O] p) :=
  Set.ext fun _ ↦ ⟨fun h ↦ ⟨fun _ hv ↦ h (.inl hv), fun _ hv ↦ h (.inr hv)⟩,
    fun h _ hv ↦ hv.elim (h.1 ·) (h.2 ·)⟩

/-- `p` is common ground between `a` and `b`, who are mutually committed to act on it, when it
holds wherever a chain of their commitments to each other leads (p. 17). -/
def commonGround : Set W := (O (a, b) ∪ O (b, a)).transGen.core p

-- the cascade of p. 17
theorem commonGround_eq_iInter : commonGround O a b p = ⋂ n, (shared O a b)^[n + 1] p :=
  SetRel.core_transGen

theorem commonGround_subset_shared : commonGround O a b p ⊆ shared O a b p :=
  SetRel.core_transGen_subset_core

/-- Acceptance: a commitment of `a` to `b` is one that both are committed to (p. 19). -/
def Acceptance : Prop :=
  ∀ p, ((a, b) ⊢[O] p) ⊆
    ((a, b) ⊢[O] ((a, b) ⊢[O] p)) ∩ ((b, a) ⊢[O] ((a, b) ⊢[O] p))

/-- Acceptance says that a commitment of either party followed by one of `a` to `b` is one of
`a` to `b`. -/
theorem acceptance_iff : Acceptance O a b ↔ (O (a, b) ∪ O (b, a)) ○ O (a, b) ⊆ O (a, b) := by
  refine ⟨?_, fun h p w hw ↦ ⟨fun v hv u hu ↦ hw (h ⟨v, .inl hv, hu⟩),
    fun v hv u hu ↦ hw (h ⟨v, .inr hv, hu⟩)⟩⟩
  rintro h ⟨w, u⟩ ⟨v, hv, hu⟩
  have hw := h {x | w ~[O (a, b)] x} fun _ hx ↦ hx
  exact hv.elim (fun hv ↦ hw.1 hv hu) fun hv ↦ hw.2 hv hu

variable {O a b}

theorem Acceptance.rel_of_transGen (h : Acceptance O a b) {w v u : W}
    (hv : Relation.TransGen (fun x y ↦ x ~[O (a, b) ∪ O (b, a)] y) w v)
    (hu : v ~[O (a, b)] u) : w ~[O (a, b)] u := by
  induction hv with
  | single hv => exact (acceptance_iff O a b).1 h ⟨_, hv, hu⟩
  | tail _ hv ih => exact ih ((acceptance_iff O a b).1 h ⟨_, hv, hu⟩)

/-- Under Acceptance a commitment is common ground: `a` and `b` are mutually committed to
`a`'s being committed (p. 19). -/
theorem Acceptance.committed_subset_commonGround (h : Acceptance O a b) :
    ((a, b) ⊢[O] p) ⊆ commonGround O a b ((a, b) ⊢[O] p) :=
  fun _ hw _ hv _ hu ↦ hw (h.rel_of_transGen hv hu)

theorem Acceptance.rel_union_of_transGen (h : Acceptance O a b) (h' : Acceptance O b a)
    {w v : W} (hv : Relation.TransGen (fun x y ↦ x ~[O (a, b) ∪ O (b, a)] y) w v) :
    w ~[O (a, b) ∪ O (b, a)] v := by
  induction hv with
  | single hv => exact hv
  | tail _ hv ih =>
    exact Or.elim hv (fun hv ↦ .inl ((acceptance_iff O a b).1 h ⟨_, ih, hv⟩))
      fun hv ↦ .inr ((acceptance_iff O b a).1 h' ⟨_, Or.symm ih, hv⟩)

/-- Under Acceptance a shared commitment is a mutual one (p. 19). -/
theorem Acceptance.commonGround_eq_shared (h : Acceptance O a b) (h' : Acceptance O b a) :
    commonGround O a b p = shared O a b p :=
  (commonGround_subset_shared O a b p).antisymm
    fun _ hw _ hv ↦ hw (h.rel_union_of_transGen h' hv)

/-- An offer commits `a` to `p` on condition that `b` commits to it, and by Acceptance `a` is
committed to `p` once `b` is (p. 9). -/
theorem Acceptance.committed_of_offer (h : Acceptance O b a) :
    ((a, b) ⊢[O] (((b, a) ⊢[O] p)ᶜ ∪ p)) ∩ ((b, a) ⊢[O] p) ⊆ ((a, b) ⊢[O] p) :=
  fun _ hw _ hv ↦ (hw.1 hv).resolve_left fun hn ↦ hn ((h p hw.2).2 hv)

-- p. 9 without Acceptance: `a` is committed to nothing, `b` exactly to the facts
theorem exists_offer_not_committed :
    ∃ (O : Bool × Bool → SetRel Bool Bool) (p : Set Bool),
      ¬ ((false, true) ⊢[O] (((true, false) ⊢[O] p)ᶜ ∪ p)) ∩ ((true, false) ⊢[O] p) ⊆
        ((false, true) ⊢[O] p) := by
  let O : Bool × Bool → SetRel Bool Bool := fun k ↦ {q | k.1 = true → q.1 = q.2}
  have h₁ : false ∈ ((true, false) ⊢[O] {false}) := fun v hv ↦ (hv rfl).symm
  have h₂ : false ∈ ((false, true) ⊢[O] (((true, false) ⊢[O] {false})ᶜ ∪ {false})) := by
    rintro (_ | _) -
    · exact .inr rfl
    · exact .inl fun hc ↦ Bool.false_ne_true (hc (b := true) fun _ ↦ rfl).symm
  exact ⟨O, {false}, fun h ↦
    Bool.false_ne_true (h ⟨h₂, h₁⟩ (b := true) fun e ↦ nomatch e).symm⟩

variable (O a b)

/-- Integrity: what `a` is committed to towards `b`, `a` is not committed against towards `c`
(p. 25). Consistency is the case `c = b` and Sincerity the case `c = a`. -/
def Integrity : Prop :=
  ∀ p, ((a, b) ⊢[O] p) ⊆ ((a, c) ⊢[O] pᶜ)ᶜ

/-- Integrity says that `a`'s commitments to `b` and to `c` leave a common world open. -/
theorem integrity_iff : Integrity O a b c ↔ IsSerial (O (a, b) ∩ O (a, c)) := by
  refine ⟨fun h ↦ ⟨fun w ↦ ?_⟩, fun hs p w hw hc ↦ ?_⟩
  · by_contra hne
    exact h {v | w ~[O (a, b)] v} (fun _ hv ↦ hv) fun v hv hR ↦ hne ⟨v, hR, hv⟩
  · obtain ⟨v, hR, hT⟩ := hs.serial w
    exact hc hT (hw hR)

-- Consistency
theorem integrity_self_iff : Integrity O a b b ↔ IsSerial (O (a, b)) := by
  rw [integrity_iff, Set.inter_self]

-- p. 25: consistent commitments to two people may conflict
theorem exists_integrity_self_not_integrity :
    ∃ O : Bool × Bool → SetRel Bool Bool, (∀ a b, Integrity O a b b) ∧
      ¬ Integrity O true false true :=
  ⟨fun k ↦ {p | p.2 = k.2}, fun a b ↦ (integrity_self_iff _ a b).2 ⟨fun _ ↦ ⟨b, rfl⟩⟩, fun h ↦
    let ⟨_, h₁, h₂⟩ := ((integrity_iff _ _ _ _).1 h).serial false
    Bool.false_ne_true (h₁.symm.trans h₂)⟩

variable {O a b}

-- p. 26: with Sincerity, `C_{a,b} p` and `C_{a,a} p ∨ C_{a,a} ¬p` give `C_{a,a} p`
theorem Integrity.committed_self (h : Integrity O a b a) :
    ((a, b) ⊢[O] p) ∩ (((a, a) ⊢[O] p) ∪ ((a, a) ⊢[O] pᶜ)) ⊆ ((a, a) ⊢[O] p) :=
  fun _ hw ↦ hw.2.elim id fun hc ↦ absurd hc (h p hw.1)

end Geurts2019
