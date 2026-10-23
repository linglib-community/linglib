module

public import Linglib.Semantics.Exhaustification.Disjunctive
public import Linglib.Semantics.Exhaustification.Antiexhaustive
public import Studies.Haspelmath1997
public import Linglib.Data.Examples.Chierchia2006
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.FinCases

/-!
# Chierchia (2006): Broaden your views

Chierchia treats every polarity-sensitive item as an existential that activates domain
alternatives, Kadmon and Landman's domain widening. An enrichment operation factors the
alternatives into meaning, and an implicature-freezing operator σ locks the result in place.
The items differ in two respects, (94): the size of their alternatives, large subdomains (MAX)
enriched by the even-like `evenEnrich` or every subdomain that stands a chance (MIN) enriched by
the antiexhaustive `oMinus`, and whether σ presupposes proper strengthening. Pure
negative-polarity items (*mai*, *ever*) are MAX; *any* is MIN with the plain σ; Italian
*qualsiasi* is MIN with the presuppositional σ; the existential free-choice items (*irgendein*,
*uno N qualsiasi*) add the uniqueness implicature of their indefinite morphology, after Kratzer
and Shimoyama.

## Main definitions

* `evenEnrich`, `oMinus`: the even-like enrichment `E`, (108b), and the antiexhaustive enrichment
  `O⁻` of a domain-dependent proposition, (108c).
* `exactlyOne`, `atLeastTwo`: the exhaustified indefinite, (81b), and its scalar alternative.
* `Profile`, `Freezer`: the parameters of (94), with the plain and the strong σ of (72).
* `Profile.Felicitous`: a logical form is felicitous when σ admits its output and the sentence is
  consistent.
* `Available`, `Excluded`: some admissible model makes a reading felicitous, or none does.

## Main results

* `evenEnrich_eq_or_eq_empty`, `evenEnrich_disj_eq_empty`, `evenEnrich_image_antitone_eq`: `E` is
  vacuous or contradictory; it is contradictory at the existential and vacuous under negation,
  (47)–(53).
* `oMinus_biUnion`, `oMinus_biUnion_eq_inter_sInter`: `O⁻` gives an existential universal force
  over its domain, (63), and there agrees with the simpler (62).
* `oMinus_antitone_eq`, `not_oMinus_ssubset_of_antitone`: under negation the
  free-choice implicature vanishes, so *qualunque* has no negative-polarity construal, (65)–(72).
* `oMinus_biUnion_eq_empty_of_isActualist`: an episodic universal over a widened domain is never
  true, (67).
* `exh_atLeastTwo_eq_exactlyOne`, `oMinus_exactlyOne_eq_empty`: `O` against the scalar
  alternative yields uniqueness, (81), and an existential free-choice item is then contradictory
  in an episodic sentence, (82).
* `oMinus_core_biUnion_subset`, `oMinus_core_exactlyOne_subset`,
  `card_le_one_of_forall_mem_core_exactlyOne`: under a necessity modal `O⁻` yields free choice,
  (93d) and (117), while letting the whole domain be an antecedent would leave room for a single
  doctor only, (118).
* `judgedReadings_predicted`, `judgedSentences_predicted`: every judgment in the paper's rows
  follows from the item's profile.

## Implementation notes

Propositions are sets of worlds, and "stronger relative to the common ground" in (50a) is
entailment. A domain is a finite set of possible witnesses, the widened domain of (57b), so
(61b)'s alternatives are those over its nonempty subdomains; large alternatives are taken to be
the proper ones. As in (95), a formula is a function from domains to propositions. `oMinus`
follows (108c) rather than (62): relating only alternatives over disjoint subdomains keeps the
whole domain from being an antecedent, which the appendix requires to avoid (118). A scalar
item's uniqueness implicature is added where it strengthens, by the selection of the strongest
enriched meaning in (110), which yields the `some_D` of (91) under negation.

σ and the recursion of appendix A3 are not represented; a reading is a logical form placing σ
among the environment's operators, as in (64)–(65), (91) and (93). The future and the imperative
are treated as necessity modals and the generic as a positive context without an actuality
condition, since the paper computes none of them beyond (55), (71) and §2. Subtrigging enters
as a domain anchored to the actual individuals, (68c). A reading marked `??` or worse is
predicted excluded and one marked at most `?` available, so the dispreferences of (10e), (10g)
and (93b) are not derived. Rows rescued by a covert modal, (4), (8a) and (89), or by
intervention, (86)–(87), carry a `device` feature and are set aside.

## TODO

* The intervention effect (86)–(87), a DP between σ and the item, is a syntactic stipulation in
  the paper and is not formalized.
* The paper excludes the scoped-out logical form (74b) without subtrigging only "by whatever
  rules out *I read any book*"; an actualist scope that presupposes rather than entails
  actuality would derive it.

## References

* [chierchia-2006]
* [kadmon-landman-1993]
* [kratzer-shimoyama-2002]
* [haspelmath-1997]
-/

@[expose] public section

namespace Chierchia2006

open Exhaustification Indefinite

/-! ### The lexicon of polarity-sensitive items, (94) -/

/-- An item activates as alternatives either the large subdomains, (46), or every subdomain that
stands a chance, (56) and (61b). -/
inductive DomainAlternatives where
  | max
  | min
  deriving DecidableEq, Repr

/-- The implicature-freezing operator σ comes plain or strong; the strong one presupposes that
the enrichment properly strengthens what it freezes, (72). -/
inductive Freezer where
  | plain
  | strong
  deriving DecidableEq, Repr

/-- A polarity-sensitive item in (94) is fixed by the size of its domain alternatives, whether
indefinite morphology adds scalar alternatives, (78), and the freezing operator it selects. -/
structure Profile where
  alternatives : DomainAlternatives
  scalar : Bool
  freezer : Freezer
  deriving DecidableEq, Repr

/-- The pure negative-polarity items *mai*, *ever* and *alcuno* are σ[D-MAX]. -/
def pureNPI : Profile := ⟨.max, false, .plain⟩

/-- *Any* is σ[D-MIN], a negative-polarity item under negation and a universal free-choice item
elsewhere. -/
def npiFci : Profile := ⟨.min, false, .plain⟩

/-- The pure universal free-choice items *qualsiasi* and *qualunque* select the strong σ over MIN
alternatives. -/
def pureFci : Profile := ⟨.min, false, .strong⟩

/-- German *irgendein* is σ[MIN, SCAL], an existential free-choice item with negative-polarity
uses. -/
def existentialNpiFci : Profile := ⟨.min, true, .plain⟩

/-- Italian *uno N qualsiasi* selects the strong σ over MIN alternatives and carries scalar
alternatives. -/
def existentialPureFci : Profile := ⟨.min, true, .strong⟩

variable {W E : Type*}

/-! ### Even-like enrichment of large alternatives, §4 -/

section Even

/-- Even-like enrichment `E`, (50a) and (108b), keeps the prejacent where it is at least as strong
as every alternative. -/
def evenEnrich (C : Set (Set W)) (p : Set W) : Set W := {w | w ∈ p ∧ ∀ q ∈ C, p ⊆ q}

theorem evenEnrich_subset (C : Set (Set W)) (p : Set W) : evenEnrich C p ⊆ p := fun _ h ↦ h.1

/-- The even-like implicature is a condition on the alternatives, not on the world: enrichment
is vacuous or a contradiction. -/
theorem evenEnrich_eq_or_eq_empty (C : Set (Set W)) (p : Set W) :
    evenEnrich C p = p ∨ evenEnrich C p = ∅ := by
  by_cases h : ∀ q ∈ C, p ⊆ q
  · exact .inl (Set.ext fun w ↦ ⟨fun hw ↦ hw.1, fun hw ↦ ⟨hw, h⟩⟩)
  · exact .inr (Set.eq_empty_of_forall_notMem fun _ hw ↦ h hw.2)

theorem evenEnrich_eq_empty_of_not_subset {C : Set (Set W)} {p q : Set W} (hq : q ∈ C)
    (h : ¬ p ⊆ q) : evenEnrich C p = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hw ↦ h (hw.2 q hq)

/-- Even-like enrichment of a pure negative-polarity item's existential is a contradiction
(47)–(48). -/
theorem evenEnrich_disj_eq_empty {D S : Finset E} {P : E → Set W} {C : Set (Set W)}
    (hS : (⋃ x ∈ S, P x) ∈ C) {a : E} {w : W} (ha : a ∈ D) (hPa : w ∈ P a)
    (hSw : ∀ x ∈ S, w ∉ P x) : evenEnrich C (⋃ x ∈ D, P x) = ∅ :=
  evenEnrich_eq_empty_of_not_subset hS fun h ↦
    let ⟨x, hx, hPx⟩ := Set.mem_iUnion₂.1 (h (Set.mem_biUnion ha hPa))
    hSw x hx hPx

/-- Under an antitone embedding, even-like enrichment of the embedded prejacent is vacuous, (49) and
(53). -/
theorem evenEnrich_image_antitone_eq {C : Set W → Set W} (hC : Antitone C) {A : Set (Set W)}
    {p : Set W} (hA : ∀ q ∈ A, q ⊆ p) : evenEnrich (C '' A) (C p) = C p :=
  Set.Subset.antisymm (evenEnrich_subset _ _)
    fun _ hw ↦ ⟨hw, by rintro _ ⟨q, hq, rfl⟩; exact hC (hA q hq)⟩

/-- If even-like enrichment strictly strengthens a proposition, it yields the contradiction, so pure
negative-polarity items select the plain σ (footnote 33). -/
theorem eq_empty_of_evenEnrich_ssubset {C : Set (Set W)} {p : Set W}
    (h : evenEnrich C p ⊂ p) : evenEnrich C p = ∅ :=
  (evenEnrich_eq_or_eq_empty C p).resolve_left fun heq ↦ ssubset_irrefl p (by rwa [heq] at h)

end Even

/-! ### Existential free-choice items, §6 and appendix A4 -/

section Existential

variable (P : E → Set W) {D S : Finset E}

/-- The exhaustified indefinite `exactlyOne P S` of (81b) holds where exactly one member of `S` is
a witness. -/
def exactlyOne (S : Finset E) : Set W := {w | ∃! x, x ∈ S ∧ w ∈ P x}

/-- `atLeastTwo P S` holds where two members of `S` are witnesses, the next row of the scale
in (79c). -/
def atLeastTwo (S : Finset E) : Set W := {w | ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ w ∈ P x ∧ w ∈ P y}

/-- Exhaustifying the existential against its scalar alternative yields the exhaustified
indefinite, (81a)–(81b), provided some world has a witness but not two. -/
theorem exh_atLeastTwo_eq_exactlyOne (h : ¬ (⋃ x ∈ S, P x) ⊆ atLeastTwo P S) :
    exh {atLeastTwo P S} (⋃ x ∈ S, P x) = exactlyOne P S := by
  ext w
  simp only [mem_exh, Set.mem_singleton_iff, forall_eq, imp_iff_not h]
  simp only [Set.mem_iUnion, exists_prop, exactlyOne, atLeastTwo, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨x, hx, hPx⟩, h2⟩
    exact ⟨x, ⟨hx, hPx⟩, fun y ⟨hy, hPy⟩ ↦ by_contra fun hyx ↦ h2 ⟨y, hy, x, hx, hyx, hPy, hPx⟩⟩
  · rintro ⟨x, ⟨hx, hPx⟩, hu⟩
    exact ⟨⟨x, hx, hPx⟩, fun ⟨y, hy, z, hz, hyz, hPy, hPz⟩ ↦
      hyz ((hu y ⟨hy, hPy⟩).trans (hu z ⟨hz, hPz⟩).symm)⟩

/-- With two possible witnesses, the uniqueness and free-choice implicatures clash, so an episodic
existential free-choice item is contradictory (82). -/
theorem oMinus_exactlyOne_eq_empty (hD : 1 < D.card) : oMinus (exactlyOne P) D = ∅ := by
  classical
  refine Set.eq_empty_of_forall_notMem fun w ⟨⟨x, ⟨_, hPx⟩, hu⟩, h⟩ ↦ ?_
  obtain ⟨b, hb, hbx⟩ := Finset.exists_mem_ne hD x
  obtain ⟨y, ⟨hy, hPy⟩, -⟩ := h {x} (by simpa) {b} (by simpa) (by simp) (by simp)
    (Finset.disjoint_singleton.2 hbx.symm) ⟨x, ⟨by simp, hPx⟩, fun z hz ↦ by simpa using hz.1⟩
  rw [Finset.mem_singleton] at hy
  exact hbx (hy ▸ hu y ⟨hy ▸ hb, hPy⟩)

section Necessity

variable {R : SetRel W W} {w : W}

/-- Under a necessity modal, the uniqueness and free-choice implicatures rule out any proper
subdomain being necessary (117c). -/
theorem notMem_core_exactlyOne (hw : w ∈ R.dom)
    (h : w ∈ oMinus (fun S ↦ R.core (exactlyOne P S)) D) (hS : S ⊂ D) (hS' : S.Nonempty) :
    w ∉ R.core (exactlyOne P S) := by
  classical
  intro hcore
  have hT := h.2 S hS.subset (D \ S) Finset.sdiff_subset hS'
    (Finset.sdiff_nonempty.2 hS.not_subset) Finset.disjoint_sdiff hcore
  obtain ⟨v, hv⟩ := hw
  obtain ⟨x, ⟨hx, hPx⟩, -⟩ := hcore hv
  obtain ⟨y, ⟨hy, hPy⟩, -⟩ := hT hv
  obtain ⟨_, -, hz⟩ := h.1 hv
  obtain ⟨hyD, hyS⟩ := Finset.mem_sdiff.1 hy
  exact hyS ((hz x ⟨hS.subset hx, hPx⟩).trans (hz y ⟨hyD, hPy⟩).symm ▸ hx)

/-- Under a necessity modal, every member of a domain of two or more is a witness in some accessible
world (117d), (93d). -/
theorem oMinus_core_exactlyOne_subset (hD : 1 < D.card) :
    oMinus (fun S ↦ R.core (exactlyOne P S)) D ∩ R.dom ⊆ ⋂ a ∈ D, R.preimage (P a) := by
  classical
  refine fun w ⟨h, hw⟩ ↦ Set.mem_iInter₂.2 fun a ha ↦ ?_
  have hne : (D.erase a).Nonempty :=
    Finset.card_pos.1 (by rw [Finset.card_erase_of_mem ha]; omega)
  have hnot := notMem_core_exactlyOne P hw h (Finset.erase_ssubset ha) hne
  simp only [SetRel.mem_core, not_forall] at hnot
  obtain ⟨v, hv, hnot⟩ := hnot
  obtain ⟨z, ⟨hz, hPz⟩, hu⟩ := h.1 hv
  by_cases hza : z = a
  · exact ⟨v, hza ▸ hPz, hv⟩
  · exact absurd ⟨z, ⟨Finset.mem_erase.2 ⟨hza, hz⟩, hPz⟩,
      fun y hy ↦ hu y ⟨Finset.mem_of_mem_erase hy.1, hy.2⟩⟩ hnot

/-- If every nonempty subdomain is necessarily witnessed by exactly one member, the domain has at
most one member (118). -/
theorem card_le_one_of_forall_mem_core_exactlyOne (hw : w ∈ R.dom)
    (h : ∀ T ⊆ D, T.Nonempty → w ∈ R.core (exactlyOne P T)) : D.card ≤ 1 := by
  refine Finset.card_le_one.2 fun a ha b hb ↦ ?_
  obtain ⟨v, hv⟩ := hw
  obtain ⟨x, ⟨hx, hPa⟩, -⟩ := h {a} (by simpa) (by simp) hv
  obtain ⟨y, ⟨hy, hPb⟩, -⟩ := h {b} (by simpa) (by simp) hv
  obtain ⟨_, -, hz⟩ := h D le_rfl ⟨a, ha⟩ hv
  rw [Finset.mem_singleton] at hx hy
  subst hx hy
  exact (hz x ⟨ha, hPa⟩).trans (hz y ⟨hb, hPb⟩).symm

end Necessity

/-- In the model of (85) the evaluation world `0` accesses the two other worlds. -/
def accessible : SetRel (Fin 3) (Fin 3) := {p | p.1 = 0 ∧ p.2 ≠ 0}

/-- Doctor `d` is married exactly in world `d + 1`, the distribution of (85). -/
def married (d : Fin 2) : Set (Fin 3) := {d.succ}

/-- Two doctors, each married in one accessible world, satisfy the enriched statement under a
possibility modal, the rescue of (84)–(85). -/
theorem zero_mem_oMinus_preimage_exactlyOne_married :
    0 ∈ oMinus (fun S ↦ accessible.preimage (exactlyOne married S)) .univ := by
  have key (T : Finset (Fin 2)) (hT : T.Nonempty) :
      0 ∈ accessible.preimage (exactlyOne married T) :=
    let ⟨d, hd⟩ := hT
    ⟨d.succ, ⟨d, ⟨hd, rfl⟩, fun _ hy ↦ (Fin.succ_injective _ hy.2).symm⟩, rfl, d.succ_ne_zero⟩
  exact ⟨key _ Finset.univ_nonempty, fun _ _ T _ _ hT _ _ ↦ key T hT⟩

/-- The same distribution satisfies the enriched statement under a necessity modal, (115)–(117):
no single doctor is necessary, so the free-choice implicature holds vacuously. -/
theorem zero_mem_oMinus_core_exactlyOne_married :
    0 ∈ oMinus (fun S ↦ accessible.core (exactlyOne married S)) .univ := by
  refine ⟨fun v hv ↦ ?_, fun S _ T _ _ ⟨d, hd⟩ hST h ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := Fin.exists_succ_eq.2 hv.2
    exact ⟨x, ⟨Finset.mem_univ x, rfl⟩, fun _ hy ↦ (Fin.succ_injective _ hy.2).symm⟩
  · obtain ⟨x, ⟨hx, hdx⟩, -⟩ := h (b := d.succ) ⟨rfl, d.succ_ne_zero⟩
    obtain rfl := Fin.succ_injective _ hdx
    exact absurd hd (Finset.disjoint_left.1 hST hx)

/-- On the same model, asserting every alternative under the necessity modal fails, (118). -/
theorem not_forall_zero_mem_core_exactlyOne_married :
    ¬ ∀ T ⊆ .univ, T.Nonempty → 0 ∈ accessible.core (exactlyOne married T) := fun h ↦
  absurd (card_le_one_of_forall_mem_core_exactlyOne married
    (show 0 ∈ accessible.dom from ⟨1, rfl, by decide⟩) h) (by decide)

end Existential

/-! ### The distribution of the items, (94) -/

section Distribution

variable {p : Profile} {P : E → Set W} {D : Finset E}

/-- The plain σ admits every enrichment, and the strong σ one that properly strengthens the
statement it freezes, (72). -/
def Freezer.Admits : Freezer → Set W → Set W → Prop
  | .plain, _, _ => True
  | .strong, s, q => s ⊂ q

theorem Freezer.admits_of_strong (f : Freezer) {s q : Set W} (h : Freezer.strong.Admits s q) :
    f.Admits s q := by
  cases f
  · trivial
  · exact h

/-- Large alternatives trigger even-like enrichment, (108b), and alternatives that stand a chance
trigger antiexhaustive enrichment, (108c). -/
def DomainAlternatives.enrich : DomainAlternatives → (Finset E → Set W) → Finset E → Set W
  | .max, F, D => evenEnrich (F '' {S | S ⊂ D ∧ S.Nonempty}) (F D)
  | .min, F, D => oMinus F D

theorem exactlyOne_subset_biUnion (S : Finset E) : exactlyOne P S ⊆ ⋃ x ∈ S, P x :=
  fun _ ⟨_, ⟨hx, hPx⟩, _⟩ ↦ Set.mem_biUnion hx hPx

open Classical in
/-- Under the operator `C` an item says that some member of the domain is a witness, and a
scalar item adds the uniqueness implicature, (81b), where that makes its statement under `C`
stronger, since (110) selects the strongest enriched meaning. -/
noncomputable def Profile.statement (p : Profile) (C : Set W → Set W) (P : E → Set W) :
    Finset E → Set W :=
  if p.scalar ∧ ∀ S, C (exactlyOne P S) ⊆ C (⋃ x ∈ S, P x) then exactlyOne P
  else fun S ↦ ⋃ x ∈ S, P x

theorem Profile.statement_of_scalar {C : Set W → Set W} (hs : p.scalar) (hC : Monotone C) :
    p.statement C P = exactlyOne P := by
  unfold Profile.statement
  split_ifs with h
  · rfl
  · exact absurd ⟨hs, fun S ↦ hC (exactlyOne_subset_biUnion S)⟩ h

theorem Profile.statement_of_not_scalar {C : Set W → Set W} (hs : p.scalar = false) :
    p.statement C P = fun S ↦ ⋃ x ∈ S, P x := by
  unfold Profile.statement
  split_ifs with h
  · simp [hs] at h
  · rfl

/-- Under an antitone operator a scalar item's statement is the plain existential, the
`some_D` of (91). -/
theorem Profile.statement_antitone {C : Set W → Set W} (hC : Antitone C) (S : Finset E) :
    C (p.statement C P S) = C (⋃ x ∈ S, P x) := by
  unfold Profile.statement
  split_ifs with h
  · exact (h.2 S).antisymm (hC (exactlyOne_subset_biUnion S))
  · rfl

/-- A logical form places σ among the operators of an item's environment. `freeze outer inner`
freezes the implicature between the operator `outer` above σ and `inner` below it, and
`scopedOut C` freezes it over the item scoped out of `C`, (74b). -/
inductive LF (W : Type*) where
  | freeze (outer inner : Set W → Set W)
  | scopedOut (C : Set W → Set W)

/-- `p.prejacent P lf` is the proposition σ freezes in `lf`, as a function of the domain. -/
noncomputable def Profile.prejacent (p : Profile) (P : E → Set W) : LF W → Finset E → Set W
  | .freeze _ inner, S => inner (p.statement inner P S)
  | .scopedOut C, S => p.statement id (fun a ↦ C (P a)) S

@[simp] theorem Profile.prejacent_freeze (outer inner : Set W → Set W) :
    p.prejacent P (.freeze outer inner) = fun S ↦ inner (p.statement inner P S) := rfl

@[simp] theorem Profile.prejacent_scopedOut (C : Set W → Set W) :
    p.prejacent P (.scopedOut C) = p.statement id (fun a ↦ C (P a)) := rfl

/-- σ's output enriches the prejacent with the item's domain alternatives. -/
noncomputable def Profile.frozen (p : Profile) (P : E → Set W) (D : Finset E) (lf : LF W) :
    Set W :=
  p.alternatives.enrich (p.prejacent P lf) D

/-- The sentence applies the operator above σ to its output. -/
noncomputable def Profile.sentence (p : Profile) (P : E → Set W) (D : Finset E) :
    LF W → Set W
  | .freeze outer inner => outer (p.frozen P D (.freeze outer inner))
  | .scopedOut C => p.frozen P D (.scopedOut C)

/-- A logical form is felicitous when σ admits its output and the sentence is consistent. -/
def Profile.Felicitous (p : Profile) (P : E → Set W) (D : Finset E) (lf : LF W) : Prop :=
  p.freezer.Admits (p.frozen P D lf) (p.prejacent P lf D) ∧ (p.sentence P D lf).Nonempty

/-- Under an antitone operator below σ the strong σ cannot freeze, so *qualunque* and *uno N
qualsiasi* lack a negative-polarity construal (70)–(72), (90b). -/
theorem not_felicitous_freeze_of_antitone {outer inner : Set W → Set W}
    (hmin : p.alternatives = .min) (hstrong : p.freezer = .strong) (hC : Antitone inner) :
    ¬ p.Felicitous P D (.freeze outer inner) := by
  rintro ⟨h, -⟩
  have hpre : p.prejacent P (.freeze outer inner) = fun S ↦ inner (⋃ x ∈ S, P x) :=
    funext (Profile.statement_antitone hC)
  simp only [Profile.frozen, hmin, hstrong, hpre, DomainAlternatives.enrich,
    Freezer.Admits] at h
  exact not_oMinus_ssubset_of_antitone P hC h

/-- Freezing σ directly over a scalar item's statement is infelicitous by the clash of (82), so
*irgendwas* under *könnte* has no universal reading (footnote 42). -/
theorem not_felicitous_freeze_id_of_scalar {outer : Set W → Set W}
    (hmin : p.alternatives = .min) (hs : p.scalar) (hD : 1 < D.card) (hout : outer ∅ = ∅) :
    ¬ p.Felicitous P D (.freeze outer id) := by
  rintro ⟨-, h⟩
  simp only [Profile.sentence, Profile.frozen, Profile.prejacent_freeze, hmin,
    DomainAlternatives.enrich, Profile.statement_of_scalar hs monotone_id, id_eq,
    oMinus_exactlyOne_eq_empty P hD, hout] at h
  exact Set.not_nonempty_empty h

/-- In an episodic sentence with an actualist scope and a widened domain the universal reading
of a non-scalar item is never true, (67). -/
theorem not_felicitous_freeze_id_id_of_isActualist {actual : W → Set E}
    (hmin : p.alternatives = .min) (hs : p.scalar = false) (hP : IsActualist actual P)
    (hD : D.Nonempty) (hwide : ∀ w, ∃ a ∈ D, a ∉ actual w) :
    ¬ p.Felicitous P D (.freeze id id) := by
  rintro ⟨-, h⟩
  simp only [Profile.sentence, Profile.frozen, Profile.prejacent_freeze, hmin,
    DomainAlternatives.enrich, Profile.statement_of_not_scalar hs, id_eq,
    oMinus_biUnion_eq_empty_of_isActualist P hP hD hwide] at h
  exact Set.not_nonempty_empty h

/-- A model of an item's context supplies an accessibility relation, the scope, the domain of
possible witnesses, and the individuals that exist at each world. -/
structure Model (W E : Type*) where
  R : SetRel W W
  P : E → Set W
  D : Finset E
  actual : W → Set E

/-- The paper distinguishes universal and existential readings, (10) and (93), and the rhetorical
and negative-polarity construals under negation, (64)–(65). -/
inductive Reading where
  | universal
  | existential
  | rhetorical
  | negativePolarity
  deriving DecidableEq, Repr

/-- An environment is the context an item occurs in in one of the paper's examples. -/
inductive Environment where
  | episodic
  | episodicSubtrigged
  | negation
  | negationSubtrigged
  | future
  | imperative
  | possibility
  | necessity
  | generic
  | negationNecessity
  deriving DecidableEq, Repr

/-- `env.lfs m r` lists the logical forms that yield the reading `r`. Negation over σ is the
rhetorical reading, (64b),
(69b), (91a), and σ over negation the negative-polarity one, (65a), (70a), (91c), as is σ over
an item scoped out of negation, (75b). A modal over σ gives the universal reading, (93a), and σ
over the modal the existential one, (84a), (93c). In a positive context σ gives the universal,
(63) and (71). -/
def Environment.lfs (m : Model W E) : Environment → Reading → List (LF W)
  | .episodic, .universal | .episodicSubtrigged, .universal | .generic, .universal =>
    [.freeze id id]
  | .negation, .rhetorical | .negationSubtrigged, .rhetorical => [.freeze (·ᶜ) id]
  | .negation, .negativePolarity => [.freeze id (·ᶜ)]
  | .negationSubtrigged, .negativePolarity => [.freeze id (·ᶜ), .scopedOut (·ᶜ)]
  | .possibility, .universal => [.freeze m.R.preimage id]
  | .possibility, .existential => [.freeze id m.R.preimage]
  | .future, .universal | .imperative, .universal | .necessity, .universal =>
    [.freeze m.R.core id]
  | .future, .existential | .imperative, .existential | .necessity, .existential =>
    [.freeze id m.R.core]
  | .negationNecessity, .rhetorical => [.freeze (·ᶜ) m.R.core]
  | .negationNecessity, .negativePolarity => [.freeze id fun q ↦ (m.R.core q)ᶜ]
  | _, _ => []

/-- A model is admissible for an environment when it meets the paper's standing assumptions: two
possible witnesses, (82); a serial accessibility relation under a modal; and in an episodic
sentence an actualist scope over a domain widened beyond the actual individuals, (67b), unless
subtrigging anchors it to them, (68c). -/
def Environment.Admissible (m : Model W E) : Environment → Prop
  | .episodic | .negation =>
    1 < m.D.card ∧ IsActualist m.actual m.P ∧ ∀ w, ∃ a ∈ m.D, a ∉ m.actual w
  | .episodicSubtrigged | .negationSubtrigged =>
    1 < m.D.card ∧ IsActualist m.actual m.P ∧ ∃ w, ∀ a ∈ m.D, a ∈ m.actual w
  | .generic => 1 < m.D.card
  | _ => 1 < m.D.card ∧ ∀ w, w ∈ m.R.dom

/-- A reading is available to an item when some admissible model makes one of its logical forms
felicitous. -/
def Available (p : Profile) (env : Environment) (r : Reading) : Prop :=
  ∃ (W E : Type) (m : Model W E), env.Admissible m ∧
    ∃ lf ∈ env.lfs m r, p.Felicitous m.P m.D lf

/-- A reading is excluded for an item when no admissible model makes any of its logical forms
felicitous. -/
def Excluded (p : Profile) (env : Environment) (r : Reading) : Prop :=
  ∀ (W E : Type) (m : Model W E), env.Admissible m → ∀ lf ∈ env.lfs m r,
    ¬ p.Felicitous m.P m.D lf

theorem excluded_negation_negativePolarity (hmin : p.alternatives = .min)
    (hstrong : p.freezer = .strong) : Excluded p .negation .negativePolarity := by
  rintro W E m - lf hlf
  simp only [Environment.lfs, List.mem_singleton] at hlf
  exact hlf ▸ not_felicitous_freeze_of_antitone hmin hstrong
    fun _ _ h ↦ Set.compl_subset_compl.2 h

theorem excluded_negationNecessity_negativePolarity (hmin : p.alternatives = .min)
    (hstrong : p.freezer = .strong) : Excluded p .negationNecessity .negativePolarity := by
  rintro W E m - lf hlf
  simp only [Environment.lfs, List.mem_singleton] at hlf
  exact hlf ▸ not_felicitous_freeze_of_antitone hmin hstrong
    fun _ _ h ↦ Set.compl_subset_compl.2 (SetRel.core_subset_core h)

theorem excluded_possibility_universal (hmin : p.alternatives = .min) (hs : p.scalar) :
    Excluded p .possibility .universal := by
  rintro W E m ⟨hD, -⟩ lf hlf
  simp only [Environment.lfs, List.mem_singleton] at hlf
  exact hlf ▸ not_felicitous_freeze_id_of_scalar hmin hs hD SetRel.preimage_empty_right

theorem excluded_episodic_of_scalar (hmin : p.alternatives = .min) (hs : p.scalar)
    (r : Reading) : Excluded p .episodic r := by
  rintro W E m ⟨hD, -⟩ lf hlf
  cases r <;> simp only [Environment.lfs, List.mem_singleton, List.not_mem_nil] at hlf
  exact hlf ▸ not_felicitous_freeze_id_of_scalar hmin hs hD rfl

theorem excluded_episodicSubtrigged_of_scalar (hmin : p.alternatives = .min) (hs : p.scalar)
    (r : Reading) : Excluded p .episodicSubtrigged r := by
  rintro W E m ⟨hD, -⟩ lf hlf
  cases r <;> simp only [Environment.lfs, List.mem_singleton, List.not_mem_nil] at hlf
  exact hlf ▸ not_felicitous_freeze_id_of_scalar hmin hs hD rfl

theorem excluded_episodic_of_not_scalar (hmin : p.alternatives = .min) (hs : p.scalar = false)
    (r : Reading) : Excluded p .episodic r := by
  rintro W E m ⟨hD, hP, hwide⟩ lf hlf
  cases r <;> simp only [Environment.lfs, List.mem_singleton, List.not_mem_nil] at hlf
  exact hlf ▸ not_felicitous_freeze_id_id_of_isActualist hmin hs hP
    (Finset.card_pos.1 (by omega)) hwide

end Distribution

/-! ### Models of the available readings -/

section Witnesses

/-- `modalModel` is a serial frame for the modal environments. From world `0` the two doctors are
married in different accessible worlds, the distribution of (85); world `3` sees only a world
where doctor `0` is married, world `5` only world `4`, where both are, and world `6` only
itself, where neither is. -/
def modalModel : Model (Fin 7) (Fin 2) where
  R := {p | p ∈ ({(0, 1), (0, 2), (1, 1), (2, 2), (3, 1), (4, 4), (5, 4), (6, 6)} : Finset _)}
  P d := {w | (d, w) ∈ ({(0, 1), (0, 4), (1, 2), (1, 4)} : Finset _)}
  D := .univ
  actual _ := .univ

/-- `widenedModel` is an episodic model with a widened domain: doctor `1` exists at no world, and
doctor `0` is a witness at world `true` only. -/
def widenedModel : Model Bool (Fin 2) where
  R := ∅
  P d := {w | d = 0 ∧ w = true}
  D := .univ
  actual _ := {0}

/-- `anchoredModel` is an episodic model anchored by subtrigging: both doctors exist at every
world, both are witnesses at world `0`, only doctor `0` at world `1`, and neither at world
`2`. -/
def anchoredModel : Model (Fin 3) (Fin 2) where
  R := ∅
  P d := {w | (d, w) ∈ ({(0, 0), (0, 1), (1, 0)} : Finset _)}
  D := .univ
  actual _ := .univ

variable {W E : Type*} {p : Profile} {P : E → Set W}

theorem Profile.statement_id (hs : p.scalar) : p.statement id P = exactlyOne P :=
  p.statement_of_scalar hs monotone_id

theorem Profile.statement_core {R : SetRel W W} (hs : p.scalar) :
    p.statement R.core P = exactlyOne P :=
  p.statement_of_scalar hs fun _ _ ↦ SetRel.core_subset_core

theorem Profile.statement_preimage {R : SetRel W W} (hs : p.scalar) :
    p.statement R.preimage P = exactlyOne P :=
  p.statement_of_scalar hs SetRel.preimage_mono

theorem Profile.compl_statement_compl (S : Finset E) :
    (p.statement (·ᶜ) P S)ᶜ = (⋃ x ∈ S, P x)ᶜ :=
  p.statement_antitone (fun _ _ h ↦ Set.compl_subset_compl.2 h) S

theorem Profile.compl_core_statement {R : SetRel W W} (S : Finset E) :
    (R.core (p.statement (fun q ↦ (R.core q)ᶜ) P S))ᶜ = (R.core (⋃ x ∈ S, P x))ᶜ :=
  p.statement_antitone (C := fun q ↦ (R.core q)ᶜ)
    (fun _ _ h ↦ Set.compl_subset_compl.2 (SetRel.core_subset_core h)) S

theorem Profile.felicitous_freeze {D : Finset E} {outer inner : Set W → Set W} {v w : W}
    (hmin : p.alternatives = .min)
    (hv : v ∈ inner (p.statement inner P D))
    (hv' : v ∉ oMinus (fun S ↦ inner (p.statement inner P S)) D)
    (hw : w ∈ outer (oMinus (fun S ↦ inner (p.statement inner P S)) D)) :
    p.Felicitous P D (.freeze outer inner) := by
  refine ⟨p.freezer.admits_of_strong ?_, w, ?_⟩ <;>
    simp only [Profile.frozen, Profile.sentence, Profile.prejacent_freeze, hmin,
      DomainAlternatives.enrich]
  · exact ⟨fun _ h ↦ h.1, fun h ↦ hv' (h hv)⟩
  · exact hw

theorem Profile.felicitous_scopedOut {D : Finset E} {C : Set W → Set W} {v w : W}
    (hmin : p.alternatives = .min)
    (hv : v ∈ p.statement id (fun a ↦ C (P a)) D)
    (hv' : v ∉ oMinus (p.statement id fun a ↦ C (P a)) D)
    (hw : w ∈ oMinus (p.statement id fun a ↦ C (P a)) D) :
    p.Felicitous P D (.scopedOut C) := by
  refine ⟨p.freezer.admits_of_strong ?_, w, ?_⟩ <;>
    simp only [Profile.frozen, Profile.sentence, Profile.prejacent_scopedOut, hmin,
      DomainAlternatives.enrich]
  · exact ⟨fun _ h ↦ h.1, fun h ↦ hv' (h hv)⟩
  · exact hw

private theorem forall_mem_powerset_univ {q : Finset (Fin 2) → Prop} :
    (∀ S ∈ (Finset.univ : Finset (Fin 2)).powerset, q S) ↔ q ∅ ∧ q {0} ∧ q {1} ∧ q .univ := by
  rw [show (Finset.univ : Finset (Fin 2)).powerset = {∅, {0}, {1}, .univ} by decide]
  simp

/-- Decides a fact about one of the finite models. -/
local macro "model_fact" : tactic => `(tactic| (
  simp only [Profile.statement_of_not_scalar, Profile.statement_id, Profile.statement_core,
    Profile.statement_preimage, Profile.compl_statement_compl, Profile.compl_core_statement,
    SetRel.mem_core, SetRel.mem_preimage, SetRel.mem_dom, Set.mem_iUnion, exists_prop, exactlyOne,
    forall_mem_powerset_univ,
    ExistsUnique, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iInter, id_eq, Finset.mem_univ,
    modalModel, widenedModel, anchoredModel]
  and_intros <;> decide))

theorem available_possibility_existential (hmin : p.alternatives = .min) :
    Available p .possibility .existential := by
  refine ⟨Fin 7, Fin 2, modalModel, ⟨by decide, by model_fact⟩, _, List.mem_singleton_self _,
    Profile.felicitous_freeze (v := 3) (w := 0) hmin ?_
      (notMem_oMinus_of_singleton (Finset.mem_univ 0) (Finset.mem_univ 1) (by decide) ?_ ?_)
      (mem_oMinus_of_forall_subset ?_ ?_)⟩
  all_goals obtain ⟨_, _ | _, _⟩ := p <;> model_fact

theorem available_possibility_universal (hmin : p.alternatives = .min)
    (hs : p.scalar = false) : Available p .possibility .universal := by
  obtain ⟨_, _, _⟩ := p
  obtain rfl := hs
  refine ⟨Fin 7, Fin 2, modalModel, ⟨by decide, by model_fact⟩, _, List.mem_singleton_self _,
    Profile.felicitous_freeze (v := 1) (w := 5) hmin (by model_fact)
      (notMem_oMinus_of_singleton (Finset.mem_univ 0) (Finset.mem_univ 1) (by decide)
        (by model_fact) (by model_fact))
      ⟨4, mem_oMinus_of_forall_subset (by model_fact) (by model_fact), by model_fact⟩⟩

theorem felicitous_core_existential (hmin : p.alternatives = .min) :
    p.Felicitous modalModel.P modalModel.D (.freeze id modalModel.R.core) := by
  refine Profile.felicitous_freeze (v := 3) (w := 0) hmin ?_
    (notMem_oMinus_of_singleton (Finset.mem_univ 0) (Finset.mem_univ 1) (by decide) ?_ ?_)
    (mem_oMinus_of_forall_ne ?_ ?_)
  all_goals obtain ⟨_, _ | _, _⟩ := p <;> model_fact

theorem felicitous_core_universal (hmin : p.alternatives = .min) (hs : p.scalar = false) :
    p.Felicitous modalModel.P modalModel.D (.freeze modalModel.R.core id) := by
  obtain ⟨a, _, f⟩ := p
  obtain rfl := hs
  have h4 : (4 : Fin 7) ∈ oMinus (fun S ↦ id (Profile.statement ⟨a, false, f⟩ id modalModel.P S))
      modalModel.D := mem_oMinus_of_forall_subset (by model_fact) (by model_fact)
  refine Profile.felicitous_freeze (v := 1) (w := 5) hmin (by model_fact)
    (notMem_oMinus_of_singleton (Finset.mem_univ 0) (Finset.mem_univ 1) (by decide)
      (by model_fact) (by model_fact)) fun b hb ↦ ?_
  obtain rfl : b = 4 := by revert b; model_fact
  exact h4

theorem available_future_existential (hmin : p.alternatives = .min) :
    Available p .future .existential :=
  ⟨Fin 7, Fin 2, modalModel, ⟨by decide, by model_fact⟩, _, List.mem_singleton_self _,
    felicitous_core_existential hmin⟩

theorem available_imperative_existential (hmin : p.alternatives = .min) :
    Available p .imperative .existential :=
  ⟨Fin 7, Fin 2, modalModel, ⟨by decide, by model_fact⟩, _, List.mem_singleton_self _,
    felicitous_core_existential hmin⟩

theorem available_necessity_existential (hmin : p.alternatives = .min) :
    Available p .necessity .existential :=
  ⟨Fin 7, Fin 2, modalModel, ⟨by decide, by model_fact⟩, _, List.mem_singleton_self _,
    felicitous_core_existential hmin⟩

theorem available_future_universal (hmin : p.alternatives = .min) (hs : p.scalar = false) :
    Available p .future .universal :=
  ⟨Fin 7, Fin 2, modalModel, ⟨by decide, by model_fact⟩, _, List.mem_singleton_self _,
    felicitous_core_universal hmin hs⟩

theorem available_imperative_universal (hmin : p.alternatives = .min) (hs : p.scalar = false) :
    Available p .imperative .universal :=
  ⟨Fin 7, Fin 2, modalModel, ⟨by decide, by model_fact⟩, _, List.mem_singleton_self _,
    felicitous_core_universal hmin hs⟩

theorem available_necessity_universal (hmin : p.alternatives = .min) (hs : p.scalar = false) :
    Available p .necessity .universal :=
  ⟨Fin 7, Fin 2, modalModel, ⟨by decide, by model_fact⟩, _, List.mem_singleton_self _,
    felicitous_core_universal hmin hs⟩

theorem available_negation_rhetorical (hmin : p.alternatives = .min) :
    Available p .negation .rhetorical := by
  refine ⟨Bool, Fin 2, widenedModel, ⟨by decide, by unfold IsActualist; model_fact, by model_fact⟩,
    _, List.mem_singleton_self _, Profile.felicitous_freeze (v := true) (w := true) hmin ?_
      (notMem_oMinus_of_singleton (Finset.mem_univ 0) (Finset.mem_univ 1) (by decide) ?_ ?_)
      (notMem_oMinus_of_singleton (Finset.mem_univ 0) (Finset.mem_univ 1) (by decide) ?_ ?_)⟩
  all_goals obtain ⟨_, _ | _, _⟩ := p <;> model_fact

theorem available_negation_negativePolarity (hmin : p.alternatives = .min)
    (hplain : p.freezer = .plain) : Available p .negation .negativePolarity := by
  refine ⟨Bool, Fin 2, widenedModel, ⟨by decide, by unfold IsActualist; model_fact, by model_fact⟩,
    _, List.mem_singleton_self _, by simp [Freezer.Admits, hplain], false, ?_⟩
  simp only [Profile.sentence, Profile.frozen, Profile.prejacent_freeze, hmin,
    DomainAlternatives.enrich]
  exact mem_oMinus_of_forall_subset (by model_fact) (by model_fact)

theorem available_negationNecessity_rhetorical (hmin : p.alternatives = .min) :
    Available p .negationNecessity .rhetorical := by
  refine ⟨Fin 7, Fin 2, modalModel, ⟨by decide, by model_fact⟩, _, List.mem_singleton_self _,
    Profile.felicitous_freeze (v := 3) (w := 3) hmin ?_
      (notMem_oMinus_of_singleton (Finset.mem_univ 0) (Finset.mem_univ 1) (by decide) ?_ ?_)
      (notMem_oMinus_of_singleton (Finset.mem_univ 0) (Finset.mem_univ 1) (by decide) ?_ ?_)⟩
  all_goals obtain ⟨_, _ | _, _⟩ := p <;> model_fact

theorem available_negationNecessity_negativePolarity (hmin : p.alternatives = .min)
    (hplain : p.freezer = .plain) : Available p .negationNecessity .negativePolarity := by
  refine ⟨Fin 7, Fin 2, modalModel, ⟨by decide, by model_fact⟩, _, List.mem_singleton_self _,
    by simp [Freezer.Admits, hplain], 6, ?_⟩
  simp only [Profile.sentence, Profile.frozen, Profile.prejacent_freeze, hmin,
    DomainAlternatives.enrich]
  exact mem_oMinus_of_forall_subset (by model_fact) (by model_fact)

theorem available_negationSubtrigged_rhetorical (hmin : p.alternatives = .min)
    (hs : p.scalar = false) : Available p .negationSubtrigged .rhetorical := by
  obtain ⟨_, _, _⟩ := p
  obtain rfl := hs
  exact ⟨Fin 3, Fin 2, anchoredModel, ⟨by decide, by unfold IsActualist; model_fact,
    by model_fact⟩, _, List.mem_singleton_self _,
    Profile.felicitous_freeze (v := 1) (w := 1) hmin (by model_fact)
      (notMem_oMinus_of_singleton (Finset.mem_univ 0) (Finset.mem_univ 1) (by decide)
        (by model_fact) (by model_fact))
      (notMem_oMinus_of_singleton (Finset.mem_univ 0) (Finset.mem_univ 1) (by decide)
        (by model_fact) (by model_fact))⟩

theorem available_negationSubtrigged_negativePolarity (hmin : p.alternatives = .min)
    (hs : p.scalar = false) : Available p .negationSubtrigged .negativePolarity := by
  obtain ⟨_, _, _⟩ := p
  obtain rfl := hs
  exact ⟨Fin 3, Fin 2, anchoredModel, ⟨by decide, by unfold IsActualist; model_fact,
    by model_fact⟩, _, List.mem_cons_of_mem _ (List.mem_singleton_self _),
    Profile.felicitous_scopedOut (v := 1) (w := 2) hmin (by model_fact)
      (notMem_oMinus_of_singleton (Finset.mem_univ 1) (Finset.mem_univ 0) (by decide)
        (by model_fact) (by model_fact))
      (mem_oMinus_of_forall_subset (by model_fact) (by model_fact))⟩

theorem felicitous_anchored_universal (hmin : p.alternatives = .min) (hs : p.scalar = false) :
    p.Felicitous anchoredModel.P anchoredModel.D (.freeze id id) := by
  obtain ⟨_, _, _⟩ := p
  obtain rfl := hs
  exact Profile.felicitous_freeze (v := 1) (w := 0) hmin (by model_fact)
    (notMem_oMinus_of_singleton (Finset.mem_univ 0) (Finset.mem_univ 1) (by decide)
      (by model_fact) (by model_fact))
    (mem_oMinus_of_forall_subset (by model_fact) (by model_fact))

theorem available_episodicSubtrigged_universal (hmin : p.alternatives = .min)
    (hs : p.scalar = false) : Available p .episodicSubtrigged .universal :=
  ⟨Fin 3, Fin 2, anchoredModel, ⟨by decide, by unfold IsActualist; model_fact, by model_fact⟩,
    _, List.mem_singleton_self _, felicitous_anchored_universal hmin hs⟩

theorem available_generic_universal (hmin : p.alternatives = .min) (hs : p.scalar = false) :
    Available p .generic .universal :=
  ⟨Fin 3, Fin 2, anchoredModel, show 1 < anchoredModel.D.card by decide, _,
    List.mem_singleton_self _, felicitous_anchored_universal hmin hs⟩

end Witnesses

/-! ### The rows -/

/-- `Profile.ofKey s` is the profile that the row key `s` names. -/
def Profile.ofKey : String → Option Profile
  | "npiFci" => some npiFci
  | "pureFci" => some pureFci
  | "existentialNpiFci" => some existentialNpiFci
  | "existentialPureFci" => some existentialPureFci
  | _ => none

/-- `Environment.ofKey s` is the environment that the row key `s` names. -/
def Environment.ofKey : String → Option Environment
  | "episodic" => some .episodic
  | "episodicSubtrigged" => some .episodicSubtrigged
  | "negation" => some .negation
  | "negationSubtrigged" => some .negationSubtrigged
  | "future" => some .future
  | "imperative" => some .imperative
  | "possibility" => some .possibility
  | "necessity" => some .necessity
  | "generic" => some .generic
  | "negationNecessity" => some .negationNecessity
  | _ => none

/-- `Reading.ofKey s` is the reading that the row key `s` names. -/
def Reading.ofKey : String → Option Reading
  | "universal" => some .universal
  | "existential" => some .existential
  | "rhetorical" => some .rhetorical
  | "negativePolarity" => some .negativePolarity
  | _ => none

/-- `judgedReadings` parses each judged reading of a row that needs no covert device into the
item's profile, the environment, the reading and its judgment. -/
def judgedReadings : List (Profile × Environment × Reading × Judgment) :=
  Examples.all.flatMap fun e ↦
    if e.feature? "device" = none then
      ((e.feature? "item").bind Profile.ofKey).toList.flatMap fun p ↦
        ((e.feature? "environment").bind Environment.ofKey).toList.flatMap fun env ↦
          e.readings.filterMap fun rj ↦ (Reading.ofKey rj.1).map fun r ↦ (p, env, r, rj.2)
    else []

/-- `judgedSentences` parses each row that needs no covert device and judges the sentence as a
whole. -/
def judgedSentences : List (Profile × Environment × Judgment) :=
  Examples.all.flatMap fun e ↦
    if e.feature? "device" = none ∧ e.readings = [] then
      ((e.feature? "item").bind Profile.ofKey).toList.flatMap fun p ↦
        ((e.feature? "environment").bind Environment.ofKey).toList.map fun env ↦
          (p, env, e.judgment)
    else []

/-- Proves that a reading is available from the lemmas above. -/
local macro "available" : tactic => `(tactic| first
  | exact available_possibility_existential rfl
  | exact available_possibility_universal rfl rfl
  | exact available_future_existential rfl
  | exact available_imperative_existential rfl
  | exact available_necessity_existential rfl
  | exact available_future_universal rfl rfl
  | exact available_imperative_universal rfl rfl
  | exact available_necessity_universal rfl rfl
  | exact available_negation_rhetorical rfl
  | exact available_negation_negativePolarity rfl rfl
  | exact available_negationNecessity_rhetorical rfl
  | exact available_negationNecessity_negativePolarity rfl rfl
  | exact available_negationSubtrigged_rhetorical rfl rfl
  | exact available_negationSubtrigged_negativePolarity rfl rfl
  | exact available_episodicSubtrigged_universal rfl rfl
  | exact available_generic_universal rfl rfl)

/-- Proves that a reading is excluded from the lemmas above. -/
local macro "excluded" : tactic => `(tactic| first
  | exact excluded_negation_negativePolarity rfl rfl
  | exact excluded_negationNecessity_negativePolarity rfl rfl
  | exact excluded_possibility_universal rfl rfl
  | exact excluded_episodic_of_scalar rfl rfl _
  | exact excluded_episodicSubtrigged_of_scalar rfl rfl _
  | exact excluded_episodic_of_not_scalar rfl rfl _)

/-- Every judged reading is predicted: a reading the paper marks `??` or worse is excluded, and
one it marks at most `?` is available. -/
theorem judgedReadings_predicted : ∀ x ∈ judgedReadings,
    (x.2.2.2 ≤ .questionable → Excluded x.1 x.2.1 x.2.2.1) ∧
      (.marginal ≤ x.2.2.2 → Available x.1 x.2.1 x.2.2.1) := by
  intro x hx
  fin_cases hx <;> dsimp only <;>
    first
    | exact ⟨fun h ↦ absurd h (by decide), fun _ ↦ by available⟩
    | exact ⟨fun _ ↦ by excluded, fun h ↦ absurd h (by decide)⟩

/-- Every sentence judged as a whole is predicted: one the paper marks `??` or worse has every
reading excluded, and one it marks at most `?` has a reading available. -/
theorem judgedSentences_predicted : ∀ x ∈ judgedSentences,
    (x.2.2 ≤ .questionable → ∀ r, Excluded x.1 x.2.1 r) ∧
      (.marginal ≤ x.2.2 → ∃ r, Available x.1 x.2.1 r) := by
  intro x hx
  fin_cases hx <;> dsimp only <;>
    first
    | exact ⟨fun h ↦ absurd h (by decide), fun _ ↦ ⟨.rhetorical, by available⟩⟩
    | exact ⟨fun _ r ↦ by excluded, fun h ↦ absurd h (by decide)⟩

theorem Profile.alternatives_of_ofKey {s : String} {p : Profile} (h : p ∈ Profile.ofKey s) :
    p.alternatives = .min := by
  unfold Profile.ofKey at h
  split at h <;> simp_all <;> subst h <;> rfl

/-- Under a necessity modal, the existential reading is available to the items of the covert-modal
rows (4), (8a), (89). -/
theorem covertModal_available : ∀ e ∈ Examples.all, e.feature? "device" = some "covertModal" →
    ∀ p ∈ (e.feature? "item").bind Profile.ofKey, Available p .necessity .existential :=
  fun _ _ _ _ hp ↦
    let ⟨_, _, h⟩ := Option.mem_bind_iff.1 hp
    available_necessity_existential (Profile.alternatives_of_ofKey h)

/-! ### Double duty on the implicational map -/

theorem any_double_duty :
    ∃ e ∈ Haspelmath1997.english,
      .directNeg ∈ e.functions ∧ .freeChoice ∈ e.functions := by
  decide

theorem italian_separates_uses :
    ∀ e ∈ Haspelmath1997.italian,
      (.directNeg ∈ e.functions → .freeChoice ∉ e.functions) ∧
        (.freeChoice ∈ e.functions →
          .directNeg ∉ e.functions ∧ .indirectNeg ∉ e.functions) := by
  decide

end Chierchia2006
