module

public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Basic
public import Linglib.Logic.Modal.Basic
public import Linglib.Semantics.Exhaustification.Pointwise
public import Linglib.Semantics.Exhaustification.InnocentInclusion

/-!
# Domain alternatives of a modalized existential

This file defines the modal profile of an existential claim `∃ x ∈ D, Q x` evaluated under
a Kripke accessibility relation, and the subdomain alternatives whose exhaustification
strengthens it. `FreeChoice` holds when every member of the domain is a witness in some
accessible world and `ModalVariation` when the witnesses vary across the accessible worlds;
`subdomainAlternatives` lists the subdomains an item competes with — every nonempty proper subdomain
for a domain widener, the singletons for an anti-singleton item — and `AntiExhaustivity S`
is the negation of the pre-exhaustified alternative for `S`: if `S` is possible, so is the
rest of the domain. Negating the pre-exhaustified singleton alternatives yields Modal
Variation and negating all proper ones yields Free Choice.

## Main definitions

* `claim`, `witnesses` — the existential over a subdomain and its
  witnesses at a world.
* `FreeChoice`, `ModalVariation`, `Uniqueness` — the modal
  components.
* `subdomainAlternatives` — the singleton or proper subdomain alternatives.
* `AntiExhaustivity` — the negated pre-exhaustified alternative, for a singleton the negated
  exhaustification against the other members (`antiExhaustivity_singleton_iff`).
* `RealizesWitnessSets` — every set of witnesses is possible at some world.

## Main results

* `notMem_exhIE_subdomain_iff` — anti-exhaustivity is the negated innocent pre-exhaustification
  against every subdomain alternative, in a model realizing every set of witnesses.
* `exh_subdomain_eq_empty` — without innocent exclusion that pre-exhaustification is
  contradictory.
* `exhIEII_singletons_eq_freeChoice` — innocent exclusion and inclusion yields free choice.

## References

* [kratzer-shimoyama-2002]
* [alonso-ovalle-menendez-benito-2010]
* [chierchia-2013]
* [fox-2007]
* [bar-lev-fox-2020]
-/

@[expose] public section

namespace Exhaustification

open ModalLogic SetRel

variable {W E : Type*} (R : SetRel W W) (w : W) (D : Finset E) (Q : W → E → Prop)

/-- The existential claim over the subdomain `S` says that some member of `S` is a witness. -/
def claim (S : Finset E) (v : W) : Prop := ∃ x ∈ S, Q v x

/-- Free Choice holds when every member of the domain is a witness in some accessible world. -/
def FreeChoice : Prop := ∀ x ∈ D, ◇[R] (Q · x) w

section Witnesses

variable [∀ v, DecidablePred (Q v)]

/-- The witnesses of the existential claim at `v`. -/
def witnesses (v : W) : Finset E := D.filter (Q v ·)

/-- Modal Variation holds when the witnesses vary across the accessible worlds. -/
def ModalVariation : Prop :=
  ∃ v, w ~[R] v ∧ ∃ v', w ~[R] v' ∧ witnesses D Q v ≠ witnesses D Q v'

/-- Uniqueness holds when each accessible world has at most one witness. -/
def Uniqueness : Prop := □[R] (fun v => (witnesses D Q v).card ≤ 1) w

theorem claim_iff_witnesses_nonempty (v : W) :
    claim Q D v ↔ (witnesses D Q v).Nonempty := by
  simp [claim, witnesses, Finset.Nonempty]

theorem modalVariation_of_two (hU : Uniqueness R w D Q) {a b : E} (ha : a ∈ D) (hb : b ∈ D)
    (hab : a ≠ b) (pa : ◇[R] (Q · a) w) (pb : ◇[R] (Q · b) w) : ModalVariation R w D Q := by
  obtain ⟨v, hv, hqa⟩ := pa
  obtain ⟨v', hv', hqb⟩ := pb
  refine ⟨v, hv, v', hv', fun h => ?_⟩
  have hb' : b ∈ witnesses D Q v := h ▸ Finset.mem_filter.2 ⟨hb, hqb⟩
  exact hab (Finset.card_le_one.1 (hU v hv) a (Finset.mem_filter.2 ⟨ha, hqa⟩) b hb')

theorem modalVariation_of_freeChoice (hU : Uniqueness R w D Q) (hD : 1 < D.card)
    (h : FreeChoice R w D Q) : ModalVariation R w D Q :=
  let ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hD
  modalVariation_of_two R w D Q hU ha hb hab (h a ha) (h b hb)

theorem not_modalVariation_of_box_empty (h : □[R] (fun v => witnesses D Q v = ∅) w) :
    ¬ ModalVariation R w D Q :=
  fun ⟨v, hv, v', hv', hne⟩ => hne ((h v hv).trans (h v' hv').symm)

end Witnesses

/-! ### Exhaustification in a model realizing every set of witnesses

When every set of witnesses is possible at some world, the characterizations of innocent exclusion
and inclusion by verified alternatives compute the exhaustified readings of a modalized existential.
Against the possibility of each member, innocent exclusion is vacuous (`exhIE_singletons_eq`) and
innocent inclusion yields free choice without pre-exhaustification
(`exhIEII_singletons_eq_freeChoice`). -/

/-- A model realizes every set of witnesses when each nonempty set of members of the domain is
the set of possible witnesses at some world. -/
def RealizesWitnessSets : Prop :=
  ∀ L ⊆ D, L.Nonempty → ∃ v, ∀ x ∈ D, ◇[R] (Q · x) v ↔ x ∈ L

section Witnessing

variable {R D Q}

theorem diamond_claim_iff {S : Finset E} {v : W} :
    ◇[R] (claim Q S) v ↔ ∃ x ∈ S, ◇[R] (Q · x) v :=
  ⟨fun ⟨u, hu, x, hx, hq⟩ ↦ ⟨x, hx, u, hu, hq⟩, fun ⟨x, hx, u, hu, hq⟩ ↦ ⟨u, hu, x, hx, hq⟩⟩

private theorem exists_single_witness (h : RealizesWitnessSets R D Q) {x : E} (hx : x ∈ D) :
    ∃ v, ∀ y ∈ D, ◇[R] (Q · y) v ↔ y = x :=
  (h {x} (Finset.singleton_subset_iff.2 hx) ⟨x, by simp⟩).imp fun _ hv y hy ↦
    (hv y hy).trans Finset.mem_singleton

theorem sUnion_minimal_singletons (h : RealizesWitnessSets R D Q) :
    ⋃₀ {M | Minimal (· ∈ Preorder.satisfied (· ∈ ·) ((fun x ↦ {v | ◇[R] (Q · x) v}) '' ↑D) ''
      {v | ◇[R] (claim Q D) v}) M} = (fun x ↦ {v | ◇[R] (Q · x) v}) '' ↑D := by
  refine Set.Subset.antisymm (fun a ⟨_, ⟨⟨_, _, rfl⟩, _⟩, ha⟩ ↦ ha.1) ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨v, hv⟩ := exists_single_witness h hx
  have hvx : ◇[R] (Q · x) v := (hv x hx).2 rfl
  refine ⟨_, ⟨⟨v, diamond_claim_iff.2 ⟨x, hx, hvx⟩, rfl⟩, ?_⟩, ⟨⟨x, hx, rfl⟩, hvx⟩⟩
  rintro _ ⟨u, hu, rfl⟩ hle a ⟨⟨t, ht, hta⟩, hva⟩
  subst hta
  obtain ⟨y, hyD, hyu⟩ := diamond_claim_iff.1 hu
  obtain rfl := (hv y hyD).1 (hle ⟨⟨y, hyD, rfl⟩, hyu⟩).2
  obtain rfl := (hv t ht).1 hva
  exact ⟨⟨t, ht, rfl⟩, hyu⟩

theorem exhIE_singletons_eq (h : RealizesWitnessSets R D Q) :
    exhIE ((fun x ↦ {v | ◇[R] (Q · x) v}) '' ↑D) {v | ◇[R] (claim Q D) v} =
      {v | ◇[R] (claim Q D) v} := by
  ext w
  rw [mem_exhIE_iff_subset_sUnion, sUnion_minimal_singletons h]
  exact ⟨And.left, fun hw ↦ ⟨hw, fun a ha ↦ ha.1⟩⟩

/-- Against the possibility of each member, innocent exclusion and inclusion strengthens the
possibility of the claim exactly to free choice, without pre-exhaustification. -/
theorem exhIEII_singletons_eq_freeChoice (h : RealizesWitnessSets R D Q) (hD : D.Nonempty) :
    exhIEII ((fun x ↦ {v | ◇[R] (Q · x) v}) '' ↑D) {v | ◇[R] (claim Q D) v} =
      {w | FreeChoice R w D Q} := by
  set B : E → Set W := fun x ↦ {v | ◇[R] (Q · x) v}
  have hcell : ∀ w, w ∈ cell (B '' ↑D) {v | ◇[R] (claim Q D) v} ↔ FreeChoice R w D Q := by
    intro w
    rw [mem_cell_iff, sUnion_minimal_singletons h]
    constructor
    · rintro ⟨-, hw⟩ x hx
      have : B x ∈ Preorder.satisfied (· ∈ ·) (B '' ↑D) w := by rw [hw]; exact ⟨x, hx, rfl⟩
      exact this.2
    · intro hw
      obtain ⟨x, hx⟩ := hD
      refine ⟨diamond_claim_iff.2 ⟨x, hx, hw x hx⟩, Set.Subset.antisymm (fun a ha ↦ ha.1) ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, hw y hy⟩
  obtain ⟨v, hv⟩ := h D subset_rfl hD
  rw [exhIEII_eq_cell_of_cell_nonempty _ _ ⟨v, (hcell v).2 fun x hx ↦ (hv x hx).2 hx⟩]
  exact Set.ext hcell

end Witnessing

/-! ### Subdomain alternatives -/

/-- Which subdomains of the domain an item competes with. -/
inductive Subdomains
  /-- Every nonempty proper subdomain, for a domain widener. -/
  | proper
  /-- The singleton subdomains, for an anti-singleton item. -/
  | singletons
  deriving DecidableEq

variable [DecidableEq E]

/-- The subdomain alternatives of `D`. -/
def subdomainAlternatives : Subdomains → Finset E → Finset (Finset E)
  | .singletons, D => D.image ({·})
  | .proper, D => Finset.Ioo ∅ D

theorem subdomainAlternatives_singletons_subset (hD : 1 < D.card) :
    subdomainAlternatives .singletons D ⊆ subdomainAlternatives .proper D := by
  intro S hS
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hS
  refine Finset.mem_Ioo.2 ⟨Finset.empty_ssubset.2 (Finset.singleton_nonempty a),
    Finset.ssubset_iff_subset_ne.2 ⟨Finset.singleton_subset_iff.2 ha, fun h => ?_⟩⟩
  simp [← h] at hD

/-- The negated pre-exhaustified alternative for `S`: if `S` is possible, so is the rest
of the domain. -/
def AntiExhaustivity (S : Finset E) : Prop :=
  ◇[R] (claim Q S) w → ◇[R] (claim Q (D \ S)) w

/-- For a singleton, anti-exhaustivity negates the possibility of its member exhaustified against
the possibility of each other member of the domain. -/
theorem antiExhaustivity_singleton_iff {a : E} (ha : a ∈ D) :
    AntiExhaustivity R w D Q {a} ↔ ¬ exhAgainst (· ≠ ·) (fun x : D ↦ ◇[R] (Q · x) w) ⟨a, ha⟩ := by
  simp only [AntiExhaustivity, exhAgainst, claim, Diamond, Finset.mem_singleton, exists_eq_left,
    Finset.mem_sdiff, not_and, not_forall, not_not, Subtype.forall, ne_eq, Subtype.mk.injEq]
  exact ⟨fun h hv ↦ let ⟨v, hv', x, ⟨hx, hxa⟩, hq⟩ := h hv; ⟨x, hx, fun h ↦ hxa h.symm, v, hv', hq⟩,
    fun h hv ↦ let ⟨x, hx, hxa, v, hv', hq⟩ := h hv; ⟨v, hv', x, ⟨hx, fun h ↦ hxa h.symm⟩, hq⟩⟩

theorem exists_singleton_of_diamond (h : ◇[R] (claim Q D) w) :
    ∃ S ∈ subdomainAlternatives .singletons D, ◇[R] (claim Q S) w :=
  let ⟨v, hv, a, ha, hqa⟩ := h
  ⟨{a}, Finset.mem_image_of_mem _ ha, v, hv, a, Finset.mem_singleton_self a, hqa⟩

theorem two_of_singletons (h : ◇[R] (claim Q D) w)
    (hs : ∀ S ∈ subdomainAlternatives .singletons D, AntiExhaustivity R w D Q S) :
    ∃ a ∈ D, ∃ b ∈ D, a ≠ b ∧ ◇[R] (Q · a) w ∧ ◇[R] (Q · b) w := by
  obtain ⟨v, hv, a, ha, hqa⟩ := h
  obtain ⟨v', hv', b, hb, hqb⟩ :=
    hs {a} (Finset.mem_image_of_mem _ ha) ⟨v, hv, a, Finset.mem_singleton_self a, hqa⟩
  obtain ⟨hbD, hba⟩ := Finset.mem_sdiff.1 hb
  exact ⟨a, ha, b, hbD, fun h => hba (h ▸ Finset.mem_singleton_self a), ⟨v, hv, hqa⟩,
    ⟨v', hv', hqb⟩⟩

theorem modalVariation_of_singletons [∀ v, DecidablePred (Q v)] (hU : Uniqueness R w D Q)
    (h : ◇[R] (claim Q D) w)
    (hs : ∀ S ∈ subdomainAlternatives .singletons D, AntiExhaustivity R w D Q S) :
    ModalVariation R w D Q :=
  let ⟨_, ha, _, hb, hab, pa, pb⟩ := two_of_singletons R w D Q h hs
  modalVariation_of_two R w D Q hU ha hb hab pa pb

theorem modalVariation_of_box [∀ v, DecidablePred (Q v)] (hw : ∃ v, w ~[R] v)
    (h : □[R] (claim Q D) w)
    (hc : ∀ S ∈ subdomainAlternatives .singletons D, ¬ □[R] (claim Q S) w) :
    ModalVariation R w D Q := by
  obtain ⟨v, hv⟩ := hw
  obtain ⟨a, ha, hqa⟩ := h v hv
  have := hc {a} (Finset.mem_image_of_mem _ ha)
  simp only [Box, claim, Finset.mem_singleton, exists_eq_left, not_forall] at this
  obtain ⟨v', hv', hna⟩ := this
  exact ⟨v, hv, v', hv', fun h =>
    hna (Finset.mem_filter.1 (h ▸ Finset.mem_filter.2 ⟨ha, hqa⟩ : a ∈ witnesses D Q v')).2⟩

theorem freeChoice_of_proper (h : ◇[R] (claim Q D) w)
    (hs : ∀ S ∈ subdomainAlternatives .proper D, AntiExhaustivity R w D Q S) :
    FreeChoice R w D Q := by
  intro a ha
  by_contra hna
  obtain ⟨v, hv, x, hx, hqx⟩ := h
  have hxa : x ≠ a := fun h => hna ⟨v, hv, h ▸ hqx⟩
  have hS : D.erase a ∈ subdomainAlternatives .proper D := by
    exact Finset.mem_Ioo.2 ⟨Finset.empty_ssubset.2 ⟨x, Finset.mem_erase.2 ⟨hxa, hx⟩⟩,
      Finset.erase_ssubset ha⟩
  obtain ⟨v', hv', y, hy, hqy⟩ := hs _ hS ⟨v, hv, x, Finset.mem_erase.2 ⟨hxa, hx⟩, hqx⟩
  obtain ⟨-, hy'⟩ := Finset.mem_sdiff.1 hy
  have : y = a := by
    by_contra hya
    exact hy' (Finset.mem_erase.2 ⟨hya, (Finset.mem_sdiff.1 hy).1⟩)
  exact hna ⟨v', hv', this ▸ hqy⟩

/-! ### Pre-exhaustified subdomain alternatives

Innocently pre-exhaustifying the possibility of a subdomain against every subdomain alternative
denies the rest of the domain, so negating it is anti-exhaustivity (`notMem_exhIE_subdomain_iff`)
and negating them all yields free choice (`freeChoice_of_forall_notMem_exhIE`). Without innocent
exclusion the pre-exhaustification is contradictory (`exh_subdomain_eq_empty`). -/

section Rich

variable {R w D Q} {S₀ : Finset E}

theorem mem_subdomainAlternatives_proper {S : Finset E} :
    S ∈ subdomainAlternatives .proper D ↔ S ⊆ D ∧ S.Nonempty ∧ S ≠ D := by
  rw [subdomainAlternatives, Finset.mem_Ioo, Finset.empty_ssubset, Finset.ssubset_iff_subset_ne]
  tauto

theorem singleton_mem_subdomainAlternatives_proper (hS₀ : S₀ ∈ subdomainAlternatives .proper D)
    {y : E} (hy : y ∈ D) : {y} ∈ subdomainAlternatives .proper D := by
  obtain ⟨hsub, ⟨x, hx⟩, hne⟩ := mem_subdomainAlternatives_proper.1 hS₀
  refine mem_subdomainAlternatives_proper.2 ⟨Finset.singleton_subset_iff.2 hy, ⟨y, by simp⟩, ?_⟩
  rintro rfl
  exact hne (Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.2
    ((Finset.mem_singleton.1 (hsub hx)) ▸ hx)))

theorem mem_exhIE_subdomain_iff (h : RealizesWitnessSets R D Q)
    (hS₀ : S₀ ∈ subdomainAlternatives .proper D) :
    w ∈ exhIE ((fun S ↦ {v | ◇[R] (claim Q S) v}) '' ↑(subdomainAlternatives .proper D))
        {v | ◇[R] (claim Q S₀) v} ↔
      ◇[R] (claim Q S₀) w ∧ ¬ ◇[R] (claim Q (D \ S₀)) w := by
  set A : Finset E → Set W := fun S ↦ {v | ◇[R] (claim Q S) v}
  set P : Set (Finset E) := ↑(subdomainAlternatives .proper D)
  have hP : ∀ {S}, S ∈ P → S ⊆ D := fun h ↦ (mem_subdomainAlternatives_proper.1 h).1
  have hS₀D := hP hS₀
  have hAsing : ∀ {y v}, y ∈ D → ◇[R] (Q · y) v →
      A {y} ∈ Preorder.satisfied (· ∈ ·) (A '' P) v := fun {y} {_} hy hyv ↦
    ⟨⟨{y}, singleton_mem_subdomainAlternatives_proper hS₀ hy, rfl⟩,
      diamond_claim_iff.2 ⟨_, Finset.mem_singleton_self _, hyv⟩⟩
  have key : ∀ S ∈ P, A S ∈ ⋃₀ {M | Minimal (· ∈ Preorder.satisfied (· ∈ ·) (A '' P) '' A S₀) M} ↔
      ∃ x ∈ S, x ∈ S₀ := by
    intro S hS
    constructor
    · rintro ⟨_, ⟨⟨v, hvφ, rfl⟩, hmin⟩, -, hvS⟩
      obtain ⟨y, hyS₀, hyv⟩ := diamond_claim_iff.1 hvφ
      obtain ⟨u, hu⟩ := exists_single_witness h (hS₀D hyS₀)
      have huφ : u ∈ A S₀ := diamond_claim_iff.2 ⟨y, hyS₀, (hu y (hS₀D hyS₀)).2 rfl⟩
      have hle := hmin ⟨u, huφ, rfl⟩ fun a ⟨⟨T, hT, hTa⟩, hua⟩ ↦ by
        subst hTa
        obtain ⟨z, hzT, hzu⟩ := diamond_claim_iff.1 hua
        obtain rfl := (hu z (hP hT hzT)).1 hzu
        exact ⟨⟨T, hT, rfl⟩, diamond_claim_iff.2 ⟨z, hzT, hyv⟩⟩
      obtain ⟨z, hzS, hzu⟩ := diamond_claim_iff.1 (hle ⟨⟨S, hS, rfl⟩, hvS⟩).2
      obtain rfl := (hu z (hP hS hzS)).1 hzu
      exact ⟨z, hzS, hyS₀⟩
    · rintro ⟨x, hxS, hxS₀⟩
      obtain ⟨v, hv⟩ := exists_single_witness h (hS₀D hxS₀)
      have hvx : ◇[R] (Q · x) v := (hv x (hS₀D hxS₀)).2 rfl
      refine ⟨_, ⟨⟨v, diamond_claim_iff.2 ⟨x, hxS₀, hvx⟩, rfl⟩, ?_⟩,
        ⟨⟨S, hS, rfl⟩, diamond_claim_iff.2 ⟨x, hxS, hvx⟩⟩⟩
      rintro _ ⟨u, hu, rfl⟩ hle a ⟨⟨T, hT, hTa⟩, hva⟩
      subst hTa
      obtain ⟨y, hyS₀, hyu⟩ := diamond_claim_iff.1 hu
      obtain ⟨z, hz, hzv⟩ := diamond_claim_iff.1 (hle (hAsing (hS₀D hyS₀) hyu)).2
      rw [Finset.mem_singleton] at hz
      subst hz
      obtain rfl := (hv z (hS₀D hyS₀)).1 hzv
      obtain ⟨t, htT, htv⟩ := diamond_claim_iff.1 hva
      obtain rfl := (hv t (hP hT htT)).1 htv
      exact ⟨⟨T, hT, rfl⟩, diamond_claim_iff.2 ⟨t, htT, hyu⟩⟩
  rw [mem_exhIE_iff_subset_sUnion]
  refine and_congr Iff.rfl ⟨fun hw hd ↦ ?_, fun hw ↦ ?_⟩
  · obtain ⟨z, hz, hzw⟩ := diamond_claim_iff.1 hd
    obtain ⟨hzD, hzS₀⟩ := Finset.mem_sdiff.1 hz
    obtain ⟨x, hx, hxS₀⟩ := (key {z} (singleton_mem_subdomainAlternatives_proper hS₀ hzD)).1
      (hw (hAsing hzD hzw))
    exact hzS₀ (Finset.mem_singleton.1 hx ▸ hxS₀)
  · rintro _ ⟨⟨T, hT, rfl⟩, hwT⟩
    refine (key T hT).2 ?_
    obtain ⟨z, hzT, hzw⟩ := diamond_claim_iff.1 hwT
    exact ⟨z, hzT, not_not.1 fun hz ↦
      hw (diamond_claim_iff.2 ⟨z, Finset.mem_sdiff.2 ⟨hP hT hzT, hz⟩, hzw⟩)⟩

/-- Negating the innocent pre-exhaustification of a proper subdomain is its anti-exhaustivity,
in a model realizing every set of witnesses. -/
theorem notMem_exhIE_subdomain_iff (h : RealizesWitnessSets R D Q)
    (hS₀ : S₀ ∈ subdomainAlternatives .proper D) :
    w ∉ exhIE ((fun S ↦ {v | ◇[R] (claim Q S) v}) '' ↑(subdomainAlternatives .proper D))
        {v | ◇[R] (claim Q S₀) v} ↔ AntiExhaustivity R w D Q S₀ := by
  rw [mem_exhIE_subdomain_iff h hS₀, AntiExhaustivity]
  tauto

theorem freeChoice_of_forall_notMem_exhIE (h : RealizesWitnessSets R D Q)
    (hw : ◇[R] (claim Q D) w)
    (hs : ∀ S ∈ subdomainAlternatives .proper D,
      w ∉ exhIE ((fun S ↦ {v | ◇[R] (claim Q S) v}) '' ↑(subdomainAlternatives .proper D))
        {v | ◇[R] (claim Q S) v}) :
    FreeChoice R w D Q :=
  freeChoice_of_proper R w D Q hw fun S hS ↦ (notMem_exhIE_subdomain_iff h hS).1 (hs S hS)

/-- Exhaustifying the possibility of a subdomain with two members against every subdomain
alternative without innocent exclusion is contradictory, in a model realizing every set of
witnesses. -/
theorem exh_subdomain_eq_empty (h : RealizesWitnessSets R D Q)
    (hS₀ : S₀ ∈ subdomainAlternatives .proper D) (h2 : 1 < S₀.card) :
    exh ((fun S ↦ {v | ◇[R] (claim Q S) v}) '' ↑(subdomainAlternatives .proper D))
      {v | ◇[R] (claim Q S₀) v} = ∅ := by
  set A : Finset E → Set W := fun S ↦ {v | ◇[R] (claim Q S) v}
  have hS₀D := (mem_subdomainAlternatives_proper.1 hS₀).1
  refine Set.not_nonempty_iff_eq_empty.1 fun hne ↦ ?_
  obtain ⟨_, ⟨v, hvφ, rfl⟩, hleast⟩ := exh_nonempty_iff.1 hne
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 h2
  obtain ⟨z, hzS₀, hzv⟩ := diamond_claim_iff.1 hvφ
  have hz : A {z} ∈ Preorder.satisfied (· ∈ ·) (A '' ↑(subdomainAlternatives .proper D)) v :=
    ⟨⟨{z}, singleton_mem_subdomainAlternatives_proper hS₀ (hS₀D hzS₀), rfl⟩,
      diamond_claim_iff.2 ⟨z, Finset.mem_singleton_self z, hzv⟩⟩
  have only : ∀ t ∈ S₀, z = t := fun t ht ↦ by
    obtain ⟨u, hu⟩ := exists_single_witness h (hS₀D ht)
    obtain ⟨z', hz', hz'u⟩ := diamond_claim_iff.1
      (hleast ⟨u, diamond_claim_iff.2 ⟨t, ht, (hu t (hS₀D ht)).2 rfl⟩, rfl⟩ hz).2
    rw [Finset.mem_singleton] at hz'
    exact hz' ▸ (hu z' (hz' ▸ hS₀D hzS₀)).1 hz'u
  exact hxy ((only x hx).symm.trans (only y hy))

end Rich

/-! ### Decidability -/

section Decidable

variable [Fintype W] [∀ v v', Decidable (v ~[R] v')] [∀ v, DecidablePred (Q v)]

instance (S : Finset E) (v : W) : Decidable (claim Q S v) :=
  inferInstanceAs (Decidable (∃ x ∈ S, _))

instance : Decidable (FreeChoice R w D Q) := inferInstanceAs (Decidable (∀ x ∈ D, _))

instance [DecidableEq W] : Decidable (ModalVariation R w D Q) :=
  inferInstanceAs (Decidable (∃ v, w ~[R] v ∧ ∃ v', w ~[R] v' ∧ _ ≠ _))

instance : Decidable (Uniqueness R w D Q) := inferInstanceAs (Decidable (□[R] _ w))

instance (S : Finset E) : Decidable (AntiExhaustivity R w D Q S) :=
  inferInstanceAs (Decidable (_ → _))

end Decidable

end Exhaustification
