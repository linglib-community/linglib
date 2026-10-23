module

public import Mathlib.Logic.Relation
public import Linglib.Core.Order.Concept

/-!
# Brandom 1994: deontic scorekeeping

Brandom models assertion by deontic scorekeeping. Each interlocutor attributes commitments and
entitlements to every interlocutor, and a claim's content is its role in committive inference,
permissive inference and incompatibility, two claims being incompatible when commitment to one
precludes entitlement to the other.

Represented by its incompatibles, a content is a concept of the incompatibility relation: the
concept order is incompatibility entailment and a negation has the orthocomplement content. A
scorecard records acknowledged commitments and prima facie entitlements, and the deontic statuses
are its closure under a role. Read back off that scorekeeping, a role confers commitment
entailment and preclusion. The role is coherent, so that entitlement passes along commitment
entailment, exactly when the preclusion it confers is its own incompatibility.

## Main definitions

* `InferentialRole`: committive inference, permissive inference and incompatibility.
* `InferentialRole.content`, `InferentialRole.IsNegation`: content and negation.
* `Scorecard.Committed`, `Scorecard.Entitled`: the deontic statuses a scorecard settles.
* `InferentialRole.CommitmentEntails`, `InferentialRole.Precludes`: the relations scorekeeping
  confers.
* `Score`, `assert`, `challenge`, `defer`, `disavow`: the scorekeeping moves.

## Main statements

* `Scorecard.Entitled.of_commitmentEntails`: in a coherent role commitment entailment preserves
  entitlement.
* `InferentialRole.coherent_iff_precludes_eq`: coherence is incompatibility as scorekeeping
  confers it.
* `InferentialRole.IsNegation.content_eq_compl`: a negation's content is the orthocomplement.
* `barn_entitled`: entitlement to each of two incompatible claims, with commitment to neither.

## Implementation notes

* Claims are an arbitrary type; `InferentialRole.ofWorlds` is a possible-worlds interpretation.
* Inferences have one premise; the auxiliary premises the book allows are not modelled.
* A scorecard stores outright attributions only, so a disavowal reinstates what it had defeated.

## References

* [brandom-1994]
* [brandom-1983]
-/

@[expose] public section

open Relation

namespace Brandom1994

variable {P : Type*}

/-! ### Inferential roles -/

/-- The broadly inferential role of claims consists of committive inference, permissive inference
and incompatibility (pp. 168–169, 188). Incompatibility is assumed symmetric throughout (p. 674
n. 39). -/
structure InferentialRole (P : Type*) where
  /-- Commitment to the premise is commitment to the conclusion. -/
  committive : P → P → Prop
  /-- Entitlement to the premise entitles one to the conclusion unless an incompatible commitment
  defeats it. -/
  permissive : P → P → Prop
  /-- Commitment to the first claim precludes entitlement to the second. -/
  incompatible : P → P → Prop
  /-- Incompatibility is mutual. -/
  incompatible_symm : Std.Symm incompatible

namespace InferentialRole

variable (R : InferentialRole P) {p q r n : P}

instance : Std.Symm R.incompatible := R.incompatible_symm

/-- The content of a claim, represented by the claims incompatible with it (p. 160), is the concept
of the incompatibility relation that the claim generates. -/
abbrev content (p : P) : Concept P P R.incompatible := .ofObject R.incompatible p

theorem content_le_iff {c : Concept P P R.incompatible} : R.content p ≤ c ↔ p ∈ c :=
  Concept.ofObjects_le_iff.trans Set.singleton_subset_iff

theorem mem_content_self (p : P) : p ∈ R.content p :=
  R.content_le_iff.1 le_rfl

/-- A claim is in the content of `p` when it incompatibility-entails `p`, that is, when everything
incompatible with `p` is incompatible with it (p. 160). -/
theorem mem_content_iff : q ∈ R.content p ↔ ∀ ⦃r⦄, R.incompatible p r → R.incompatible q r := by
  change q ∈ (R.content p).extent ↔ _
  simp [mem_lowerPolar_iff, mem_upperPolar_iff]

theorem mem_compl_content_iff : q ∈ (R.content p)ᶜ ↔ R.incompatible p q := by
  change q ∈ (R.content p).intent ↔ _
  simp [mem_upperPolar_iff]

/-- A role is coherent when committive inference is incompatibility entailment, so that if `p`
commitment-entails `q`, anything incompatible with `q` is incompatible with `p` (p. 673 n. 27). -/
def Coherent : Prop := ∀ ⦃p q⦄, R.committive p q → R.content p ≤ R.content q

variable {R}

theorem Coherent.incompatible (hR : R.Coherent) (hpq : R.committive p q)
    (hqr : R.incompatible q r) : R.incompatible p r :=
  (R.mem_content_iff.1 <| R.content_le_iff.1 (hR hpq)) hqr

theorem Coherent.content_le (hR : R.Coherent) (h : ReflTransGen R.committive p q) :
    R.content p ≤ R.content q := by
  induction h with
  | refl => exact le_rfl
  | tail _ hqr ih => exact ih.trans (hR hqr)

variable (R)

/-- A negation of `p` is a minimal incompatible of `p`, a claim incompatible with `p` that
everything incompatible with `p` commitment-entails (p. 673 n. 23). -/
def IsNegation (p n : P) : Prop :=
  R.incompatible p n ∧ ∀ ⦃r⦄, R.incompatible p r → ReflTransGen R.committive r n

variable {R}

/-- In a coherent role a negation has the orthocomplement of the claim's content. -/
theorem IsNegation.content_eq_compl (hR : R.Coherent) (h : R.IsNegation p n) :
    R.content n = (R.content p)ᶜ := by
  refine SetLike.ext fun r ↦ ⟨fun hr ↦ ?_, fun hr ↦ ?_⟩
  · exact R.mem_compl_content_iff.2 <| symm <| R.mem_content_iff.1 hr (symm h.1)
  · exact hR.content_le (h.2 (R.mem_compl_content_iff.1 hr)) (R.mem_content_self r)

theorem IsNegation.incompatible_iff (hR : R.Coherent) (h : R.IsNegation p n) :
    R.incompatible p r ↔ R.content r ≤ R.content n := by
  rw [h.content_eq_compl hR, content_le_iff, mem_compl_content_iff]

theorem IsNegation.content_eq (hR : R.Coherent) {n' : P} (h : R.IsNegation p n)
    (h' : R.IsNegation p n') : R.content n = R.content n' :=
  (h.content_eq_compl hR).trans (h'.content_eq_compl hR).symm

/-! ### Possible-worlds roles -/

variable {W : Type*}

/-- A possible-worlds interpretation makes committive inference the inclusion of truth sets and
incompatibility their disjointness (p. 169). Truth conditions alone license no merely permissive
inference. -/
def ofWorlds (ι : P → Set W) : InferentialRole P where
  committive p q := ι p ⊆ ι q
  permissive _ _ := False
  incompatible p q := Disjoint (ι p) (ι q)
  incompatible_symm := ⟨fun _ _ h ↦ h.symm⟩

theorem coherent_ofWorlds (ι : P → Set W) : (ofWorlds ι).Coherent := fun _ _ (h : ι _ ⊆ ι _) ↦
  (content_le_iff _).2 <| (mem_content_iff _).2 fun _ (hr : Disjoint _ _) ↦ hr.mono_left h

theorem content_le_content_ofWorlds_id_iff {p q : Set W} :
    (ofWorlds id).content p ≤ (ofWorlds id).content q ↔ p ⊆ q :=
  ⟨fun h ↦ Set.disjoint_compl_right_iff_subset.1 <|
    (mem_content_iff _).1 ((content_le_iff _).1 h) (disjoint_compl_right (a := q)),
    fun h ↦ coherent_ofWorlds id h⟩

theorem isNegation_ofWorlds_id_compl (p : Set W) : (ofWorlds id).IsNegation p pᶜ :=
  ⟨disjoint_compl_right (a := p), fun _ (h : Disjoint p _) ↦
    .single (Set.subset_compl_iff_disjoint_left.2 h)⟩

end InferentialRole

/-! ### Scorecards -/

/-- A scorecard records what one scorekeeper attributes to one interlocutor outright (pp.
190–191). -/
structure Scorecard (P : Type*) where
  /-- The commitments the interlocutor has acknowledged by avowing them. -/
  acknowledged : Set P
  /-- The claims the interlocutor is entitled to without inference, by default or by deferral. -/
  primaFacie : Set P

namespace Scorecard

variable (R : InferentialRole P) (c : Scorecard P) {p q r : P}

/-- An interlocutor is committed to whatever follows by committive inference from an acknowledged
commitment, whether or not they acknowledge it (p. 194). -/
def Committed (q : P) : Prop := ∃ p ∈ c.acknowledged, ReflTransGen R.committive p q

/-- Entitlement to `q` is precluded by a commitment to something incompatible with it. -/
def Precluded (q : P) : Prop := ∃ r, c.Committed R r ∧ R.incompatible r q

/-- Entitlement is the closure the scorekeeping procedure prescribes (p. 191, p. 675 n. 44). It
holds of the prima facie entitlements, their committive consequences, and the permissive
consequences of entitled commitments, each unless precluded. -/
inductive Entitled : P → Prop
  | primaFacie {p : P} : p ∈ c.primaFacie → ¬ c.Precluded R p → Entitled p
  | committive {p q : P} : Entitled p → R.committive p q → ¬ c.Precluded R q → Entitled q
  | permissive {p q : P} : Entitled p → c.Committed R p → R.permissive p q → ¬ c.Precluded R q →
      Entitled q

/-- Avowing `p` acknowledges the commitment and, by default, the entitlement (p. 177). -/
def avow (p : P) : Scorecard P := ⟨insert p c.acknowledged, insert p c.primaFacie⟩

variable {R c}

theorem committed_of_mem (h : p ∈ c.acknowledged) : c.Committed R p := ⟨p, h, .refl⟩

/-- Committive inference preserves commitment (p. 186). -/
theorem Committed.of_committive (h : c.Committed R p) (hpq : R.committive p q) :
    c.Committed R q :=
  let ⟨r, hr, hrp⟩ := h; ⟨r, hr, hrp.tail hpq⟩

theorem Entitled.not_precluded (h : c.Entitled R p) : ¬ c.Precluded R p := by
  cases h <;> assumption

/-- Commitment to one of two incompatible claims precludes entitlement to the other (p. 160). -/
theorem not_entitled_of_incompatible (hr : c.Committed R r) (h : R.incompatible r p) :
    ¬ c.Entitled R p :=
  fun hp ↦ hp.not_precluded ⟨r, hr, h⟩

/-- In a coherent role committive inference preserves entitlement, since whatever precludes the
conclusion precludes the premise (p. 673 n. 27, p. 674 n. 43). -/
theorem Entitled.of_committive (hR : R.Coherent) (h : c.Entitled R p) (hpq : R.committive p q) :
    c.Entitled R q :=
  h.committive hpq fun ⟨r, hr, hrq⟩ ↦ h.not_precluded ⟨r, hr, symm (hR.incompatible hpq (symm hrq))⟩

/-- Inference spreads entitlement but does not originate it (p. 176), so every entitlement descends
along committive and permissive inference from a prima facie one. -/
theorem Entitled.exists_primaFacie (h : c.Entitled R p) :
    ∃ q ∈ c.primaFacie, ReflTransGen (R.committive ⊔ R.permissive) q p := by
  induction h with
  | primaFacie hp _ => exact ⟨_, hp, .refl⟩
  | committive _ hpq _ ih => obtain ⟨r, hr, h⟩ := ih; exact ⟨r, hr, h.tail (.inl hpq)⟩
  | permissive _ _ hpq _ ih => obtain ⟨r, hr, h⟩ := ih; exact ⟨r, hr, h.tail (.inr hpq)⟩

theorem not_entitled_of_primaFacie_eq_empty (h : c.primaFacie = ∅) : ¬ c.Entitled R p := fun hp ↦
  let ⟨_, hq, _⟩ := hp.exists_primaFacie; (h ▸ hq : _ ∈ (∅ : Set P))

/-- An avowal is attributed entitlement by default, unless an incompatible commitment defeats it
(p. 177). -/
theorem entitled_avow_iff : (c.avow p).Entitled R p ↔ ¬ (c.avow p).Precluded R p :=
  ⟨Entitled.not_precluded, .primaFacie (Set.mem_insert p _)⟩

end Scorecard

/-! ### Conferral -/

namespace InferentialRole

variable (R : InferentialRole P) {p q r : P}

/-- Scorekeeping by `R` treats the inference from `p` to `q` as good, so that `p` commitment-entails
`q`, when every scorecard committed to `p` is committed to `q` (p. 186). -/
def CommitmentEntails (p q : P) : Prop := ∀ c : Scorecard P, c.Committed R p → c.Committed R q

/-- Scorekeeping by `R` treats commitment to `p` as precluding entitlement to `q` when every
scorecard committed to `p` withholds entitlement to `q` (p. 186). -/
def Precludes (p q : P) : Prop := ∀ c : Scorecard P, c.Committed R p → ¬ c.Entitled R q

theorem commitmentEntails_eq : R.CommitmentEntails = ReflTransGen R.committive := by
  ext p q
  refine ⟨fun h ↦ ?_, fun h c ⟨r, hr, hrp⟩ ↦ ⟨r, hr, hrp.trans h⟩⟩
  obtain ⟨r, rfl, hrq⟩ := h ⟨{p}, ∅⟩ (Scorecard.committed_of_mem rfl)
  exact hrq

theorem precludes_eq : R.Precludes = Relation.Comp (ReflTransGen R.committive) R.incompatible := by
  ext p q
  refine ⟨fun h ↦ ?_, fun ⟨r, hpr, hrq⟩ c ⟨s, hs, hsp⟩ ↦
    Scorecard.not_entitled_of_incompatible ⟨s, hs, hsp.trans hpr⟩ hrq⟩
  by_contra hq
  exact h ⟨{p}, {q}⟩ (Scorecard.committed_of_mem rfl)
    (.primaFacie rfl fun ⟨r, ⟨s, hs, hsr⟩, hrq⟩ ↦ hq ⟨r, hs ▸ hsr, hrq⟩)

/-- A role is coherent exactly when its incompatibility is the one its own scorekeeping confers. -/
theorem coherent_iff_precludes_eq : R.Coherent ↔ R.Precludes = R.incompatible := by
  rw [precludes_eq]
  refine ⟨fun hR ↦ funext₂ fun p q ↦ propext ⟨fun ⟨r, hpr, hrq⟩ ↦
    R.mem_content_iff.1 (R.content_le_iff.1 (hR.content_le hpr)) hrq, fun h ↦ ⟨p, .refl, h⟩⟩,
    fun h p q hpq ↦ R.content_le_iff.2 <| R.mem_content_iff.2 fun r hqr ↦ ?_⟩
  exact (congrFun₂ h p r).mp ⟨q, .single hpq, hqr⟩

variable {R} in
/-- The relations scorekeeping confers are coherent, since whatever a commitment-consequence
precludes, its premise precludes (p. 673 n. 27). -/
theorem Precludes.of_commitmentEntails (hpq : R.CommitmentEntails p q) (hqr : R.Precludes q r) :
    R.Precludes p r :=
  fun c hp ↦ hqr c (hpq c hp)

end InferentialRole

/-- In a coherent role entitlement is inherited by whatever a claim commitment-entails (p. 674
n. 43). -/
theorem Scorecard.Entitled.of_commitmentEntails {R : InferentialRole P} {c : Scorecard P} {p q : P}
    (hR : R.Coherent) (h : c.Entitled R p) (hpq : R.CommitmentEntails p q) : c.Entitled R q := by
  rw [InferentialRole.commitmentEntails_eq] at hpq
  induction hpq with
  | refl => exact h
  | tail _ hqr ih => exact ih.of_committive hR hqr

/-! ### The barn -/

/-- The claims of the barn example (p. 675 n. 44). -/
inductive Barn
  | smoke | rain | fire | noFire

/-- Smoke is inductive evidence of fire and rain of no fire; fire and no fire are incompatible. -/
def barnRole : InferentialRole Barn where
  committive _ _ := False
  permissive
    | .smoke, .fire | .rain, .noFire => True
    | _, _ => False
  incompatible
    | .fire, .noFire | .noFire, .fire => True
    | _, _ => False
  incompatible_symm := ⟨fun a b ↦ by cases a <;> cases b <;> simp⟩

/-- Having observed smoke and rain, one acknowledges both, by default entitled. -/
def barnCard : Scorecard Barn := ⟨{.smoke, .rain}, {.smoke, .rain}⟩

/-- One may be entitled to each of two incompatible claims while committed to neither (p. 675
n. 44); committing to one of them defeats entitlement to the other. -/
theorem barn_entitled :
    barnCard.Entitled barnRole .fire ∧ barnCard.Entitled barnRole .noFire ∧
      ¬ barnCard.Committed barnRole .fire ∧ ¬ barnCard.Committed barnRole .noFire ∧
      ¬ (barnCard.avow .fire).Entitled barnRole .noFire := by
  have committed {c : Scorecard Barn} {q} : c.Committed barnRole q ↔ q ∈ c.acknowledged :=
    ⟨fun ⟨p, hp, h⟩ ↦ (reflTransGen_iff_eq fun _ h ↦ h).1 h ▸ hp, Scorecard.committed_of_mem⟩
  have unprecluded (q) : ¬ barnCard.Precluded barnRole q := by
    rintro ⟨r, hr, h⟩
    rw [committed] at hr
    rcases hr with rfl | rfl <;> cases q <;> exact h
  have entitled {p q} (hp : p ∈ barnCard.acknowledged) (hpq : barnRole.permissive p q) :
      barnCard.Entitled barnRole q :=
    .permissive (.primaFacie hp (unprecluded p)) (Scorecard.committed_of_mem hp) hpq (unprecluded q)
  refine ⟨entitled (.inl rfl) trivial, entitled (.inr rfl) trivial, ?_, ?_,
    Scorecard.not_entitled_of_incompatible (Scorecard.committed_of_mem (.inl rfl)) trivial⟩ <;>
  · rw [committed]; rintro (h | h) <;> cases h

theorem exists_entitled_committive_not_entitled :
    ∃ (R : InferentialRole Bool) (c : Scorecard Bool),
      c.Entitled R true ∧ R.committive true false ∧ ¬ c.Entitled R false := by
  let R : InferentialRole Bool :=
    ⟨fun p q ↦ p ∧ ¬ q, fun _ _ ↦ False, fun p q ↦ ¬ p ∧ ¬ q, ⟨fun _ _ h ↦ h.symm⟩⟩
  have hf : (⟨{true}, {true}⟩ : Scorecard Bool).Committed R false :=
    ⟨true, rfl, .single (by simp [R])⟩
  exact ⟨R, ⟨{true}, {true}⟩, .primaFacie rfl fun ⟨_, _, h⟩ ↦ by simp [R] at h, by simp [R],
    Scorecard.not_entitled_of_incompatible hf (by simp [R])⟩

/-! ### Scorekeeping -/

/-- A score holds the scorecard `s k i` that each scorekeeper `k` keeps on each interlocutor `i`, so
scorekeeping is doubly perspectival (p. 185). -/
abbrev Score (I P : Type*) := I → I → Scorecard P

variable {I : Type*} [DecidableEq I] (R : InferentialRole P) (s : Score I P) {a b k : I} {p q : P}

/-- When `b` asserts `p`, every scorekeeper attributes to `b` the commitment and, by default,
entitlement to it (pp. 177, 186). -/
def assert (b : I) (p : P) : Score I P := fun k ↦ Function.update (s k) b ((s k b).avow p)

/-- When `a`'s claim `q` challenges `b`'s claim `p`, a scorekeeper who takes `a` to be entitled to
`q` withholds default entitlement to `p` from `b` and leaves the commitment standing (p. 193). -/
def challenge (a : I) (q : P) (b : I) (p : P) : Score I P := fun k ↦
  Function.update (s k) b
    ⟨(s k b).acknowledged, {r ∈ (s k b).primaFacie | (s k a).Entitled R q → r ≠ p}⟩

/-- When `a` defers to `b` concerning `p`, `a` acknowledges `p`, and a scorekeeper who takes `b` to
be entitled to `p` takes `a` to inherit the entitlement by testimony (pp. 175, 192). -/
def defer (a b : I) (p : P) : Score I P := fun k ↦
  Function.update (s k) a
    ⟨insert p (s k a).acknowledged, {r | r ∈ (s k a).primaFacie ∨ r = p ∧ (s k b).Entitled R p}⟩

/-- When `b` disavows `p`, scorekeepers cease to attribute to `b` the acknowledged commitment
(p. 192). -/
def disavow (b : I) (p : P) : Score I P := fun k ↦
  Function.update (s k) b ⟨(s k b).acknowledged \ {p}, (s k b).primaFacie⟩

@[simp] theorem assert_self : assert s b p k b = (s k b).avow p := by simp [assert]

@[simp] theorem acknowledged_challenge (i : I) :
    (challenge R s a q b p k i).acknowledged = (s k i).acknowledged := by
  by_cases h : i = b <;> simp [challenge, h]

/-- A challenged assertion with no other support is a commitment without entitlement (pp. 177–178).
Once a scorekeeper takes the challenger to be entitled to the challenge, it attributes to the
asserter the commitment and no entitlement at all. -/
theorem challenge_committed_not_entitled (hb : (s k b).primaFacie = ∅) {q' : P}
    (ha : (assert s b p k a).Entitled R q) :
    (challenge R (assert s b p) a q b p k b).Committed R p ∧
      ¬ (challenge R (assert s b p) a q b p k b).Entitled R q' := by
  refine ⟨Scorecard.committed_of_mem (by simp [Scorecard.avow]), ?_⟩
  refine Scorecard.not_entitled_of_primaFacie_eq_empty (Set.eq_empty_of_forall_notMem fun r hr ↦ ?_)
  simp only [challenge, Function.update_self, assert_self, Scorecard.avow, hb] at hr
  exact hr.2 ha (Set.mem_singleton_iff.1 (by simpa using hr.1))

/-- Deferral passes on the entitlement the scorekeeper attributes to the source (p. 175). -/
theorem entitled_defer (hb : (s k b).Entitled R p) (hp : ¬ (defer R s a b p k a).Precluded R p) :
    (defer R s a b p k a).Entitled R p :=
  .primaFacie (by simp [defer, hb]) hp

/-- Deferral to a source the scorekeeper takes to be unentitled confers no entitlement, since others
cannot inherit an entitlement the asserter does not possess (p. 171). -/
theorem not_entitled_defer (hb : ¬ (s k b).Entitled R p) (ha : (s k a).primaFacie = ∅) :
    ¬ (defer R s a b p k a).Entitled R q :=
  Scorecard.not_entitled_of_primaFacie_eq_empty <| by simp [defer, hb, ha]

/-- A disavowal of `p` fails while a premise committing `b` to `p` stays acknowledged (pp.
192–193). -/
theorem committed_disavow {q r : P} (hq : q ∈ (s k b).acknowledged) (hqp : q ≠ p)
    (h : ReflTransGen R.committive q r) : (disavow s b p k b).Committed R r :=
  ⟨q, by simp [disavow, hq, hqp], h⟩

end Brandom1994
