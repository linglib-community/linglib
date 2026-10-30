module

public import Linglib.Semantics.Alternatives.Relevance
public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Linglib.Semantics.Focus.Particles
public import Linglib.Semantics.Presupposition.Context
public import Linglib.Semantics.Quantification.Exceptive
public import Linglib.Data.Examples.Crnic2026b

/-!
# Crnič (2026): On the variable strength of *only*

Crnič analyses *only* as two operators over focus alternatives. *Only* asserts that no relevant
innocently excludable alternative holds, and a presuppositional `exh` above it presupposes that
the excludable alternatives of the *only*-sentence are false, so the positive inference of *only*
varies with the domain of `exh`. Unpruned, the sentence is [Horn's entry](##exhOnly_eq_only);
pruned to one alternative outside the domain of *only*, it is [the weak
entry](##exhOnly_singleton_eq). For an atomic prejacent [only the full domain satisfies the
Weakening Constraint](##weakening_iff), so pruning surfaces where the full domain [leaves the
assertion uninformative](##table_2). Unpruned, the analysis of exceptives is [von Fintel's least
exception set](##pex_but_no_eq_one_iff).

## Implementation notes

* A world is the set of atoms that hold, the guests at the party or the ranks Gal holds, so the
  alternative that every atom of the plurality `X` holds is the interval `Set.Ici X`. Focus
  alternatives and resource domains are sets of pluralities, and the domain of `exh` is the set of
  pluralities its alternatives are built on.
* `only` and `exhOnly` exclude innocently, through `Exhaustification.excludesIE`. In these models
  the prejacent's own world falsifies every alternative the prejacent does not entail, so innocent
  exclusion is exclusion (`Exhaustification.excludesIE_eq_excludes`).
* `pex` is the partial entry (9), undefined where its presupposition fails. Under the Strong
  Kleene `Exhaustification.pexIE` of [bassi-delpinal-sauerland-2021], which is false wherever its
  prejacent is, *Not only Gal was at the party* would not presuppose that Gal was there.
* The Weakening Constraint ranges over domains of excludable alternatives, as the resolutions
  (41b) and (50b) are written. Read literally, (56) compares a domain with every larger set of
  alternatives, and a domain lacking a non-excludable alternative fails it, since adding one
  changes nothing (`exhOnly_inter_excludable`).
* Relevance over the context is `Alternatives.IsAllowableRestriction` over the subtype of the
  context, with each *only*-alternative restricted to it by preimage (`onlyCtx`).
* The ranking (58) of Informativity, `Presupposition.PostAccommodationInformative`, over Weakening
  is read off the constraints each domain satisfies; the accommodation operator of (56) is
  `posSupport`.

## Errata

* (6b) and (32c) give the excludable alternatives of *Gal was at the party* as those about
  individuals disjoint from Gal. With the plural alternatives of (12), every alternative other
  than the prejacent is excludable, *Gal and Tal were at the party* among them
  (`isInnocentlyExcludable_Ici_iff`, `isInnocentlyExcludable_galTal`); the exhaustive inference
  is unaffected.
* (110b) fails with the plural alternatives of (12), on which the strong presupposition (13)
  rests; [crnic-2026a] shows that singular ones give a weak presupposition. *Someone but Gal* has
  the excludable alternative *someone but everyone except Gal*, that Gal was there
  (`isInnocentlyExcludable_but_some`), so `exh` in (109) is not vacuous and the Economy Constraint
  (108) does not exclude (107) (`judgment_107`).
* (40), (56) and (58) do not single out the resolution (41) of *Gal is only a grad student*:
  pruning to *only [postdoc]* satisfies and violates the same constraints, and under negation
  conveys that Gal is a professor (`pruned_postdoc`). The closure of relevance under the Boolean
  operations, set aside in fn. 3, does single it out, but only computed over the context: there
  (41) is the one informative pruning that is an allowable restriction in the sense of
  [fox-katzir-2011] (`isAllowableRestriction_onlyCtx_iff`), while over all worlds pruning to
  *only [non-academic]* and *only [postdoc]* is allowable too
  (`isAllowableRestriction_only_ranks`).

## TODO

* The sufficiency modal constructions of §3.4, the embedded exhaustification of §3.5, the
  integrated rivals of §4, the conjunctive closure of fn. 4, and the exceptives of §5.2–5.3.

## References

* [crnic-2026b]
* [crnic-2024]
* [crnic-2026a]
* [horn-1969]
* [horn-1996]
* [bassi-delpinal-sauerland-2021]
* [crnic-chemla-fox-2015]
* [doron-wehbe-2022]
* [von-fintel-1993]
* [rooth-1992]
* [fox-katzir-2011]
-/

@[expose] public section

namespace Crnic2026b

open Exhaustification Set

/-! ### Pluralities and the distributed *only* -/

section Distributed

variable {α : Type*} (F C R : Set (Finset α))

/-- (8): *only*, over the focus alternatives `F` with resource domain `C`, asserts that no
relevant innocently excludable alternative holds. -/
def only (X : Finset α) : Set (Finset α) :=
  excludesIE (Ici '' F) (Ici X) (Ici '' C)

variable (S : Finset α → Set (Finset α)) in
open Classical in
/-- (9): `exh` over a sentence `S X` whose focus alternatives are `S Y` for `Y ∈ F` presupposes
that those built on the pluralities in its domain `R` that are innocently excludable are false,
and asserts `S X`. -/
noncomputable def pex (X : Finset α) : Finset α → SignType :=
  (excludesIE (S '' F) (S X) (S '' R)).indicator fun w ↦ SignType.ofProp (w ∈ S X)

/-- (10): `exh` over the *only*-sentence. -/
noncomputable abbrev exhOnly (X : Finset α) : Finset α → SignType := pex F R (only F C) X

variable {F C} in
theorem mem_exh_Ici (X : Finset α) : X ∈ exh (Ici '' F) (Ici X) :=
  ⟨mem_Ici.2 le_rfl, by rintro _ ⟨Z, -, rfl⟩ hZ; exact Ici_subset_Ici.2 hZ⟩

variable {F} in
-- (6b)
theorem isInnocentlyExcludable_Ici_iff {X Y : Finset α} (hY : Y ∈ F) :
    IsInnocentlyExcludable (Ici '' F) (Ici X) (Ici Y) ↔ ¬ Y ⊆ X := by
  rw [isInnocentlyExcludable_iff_not_subset ⟨X, mem_exh_Ici X⟩ (mem_image_of_mem _ hY),
    Ici_subset_Ici]

variable {F C} {X Y w : Finset α}

theorem mem_only : w ∈ only F C X ↔ ∀ Z ∈ F ∩ C, Z ⊆ w → Z ⊆ X := by
  simp only [only, excludesIE_eq_excludes ⟨X, mem_exh_Ici X⟩, mem_excludes,
    ← image_inter Ici_injective, forall_mem_image, mem_Ici, Ici_subset_Ici]

theorem mem_only_of_subset (hC : C ⊆ F) : w ∈ only F C X ↔ ∀ Z ∈ C, Z ⊆ w → Z ⊆ X := by
  rw [mem_only, inter_eq_right.2 hC]

theorem only_eq_excludes (hC : C ⊆ F) : only F C X = excludes (Ici '' C) (Ici X) := by
  ext w
  simp [mem_only_of_subset hC]

theorem self_mem_only : X ∈ only F C X := mem_only.2 fun _ _ h ↦ h

theorem only_subset_only_iff : only F C X ⊆ only F C Y ↔ X ∈ only F C Y :=
  ⟨fun h ↦ h self_mem_only, fun h _ hw ↦ mem_only.2 fun Z hZ hZw ↦
    mem_only.1 h Z hZ (mem_only.1 hw Z hZ hZw)⟩

theorem mem_exh_only : X ∈ exh (only F C '' F) (only F C X) :=
  ⟨self_mem_only, by rintro _ ⟨Y, -, rfl⟩ hY; exact only_subset_only_iff.2 hY⟩

-- (12b)
theorem isInnocentlyExcludable_only_iff (hY : Y ∈ F) :
    IsInnocentlyExcludable (only F C '' F) (only F C X) (only F C Y) ↔ X ∉ only F C Y := by
  rw [isInnocentlyExcludable_iff_not_subset ⟨X, mem_exh_only⟩ (mem_image_of_mem _ hY),
    only_subset_only_iff]

open Classical in
theorem exhOnly_eq_indicator (hR : R ⊆ F) : exhOnly F C R X =
    {w | ∀ Y ∈ R, w ∈ only F C Y → X ∈ only F C Y}.indicator
      fun w ↦ SignType.ofProp (w ∈ only F C X) := by
  rw [exhOnly, pex, excludesIE_eq_excludes ⟨X, mem_exh_only⟩, inter_eq_right.2 (image_mono hR)]
  congr 1
  ext w
  simp [only_subset_only_iff]

theorem exhOnly_ne_zero_iff (hR : R ⊆ F) :
    exhOnly F C R X w ≠ 0 ↔ ∀ Y ∈ R, w ∈ only F C Y → X ∈ only F C Y := by
  simp [exhOnly_eq_indicator R hR]

theorem exhOnly_eq_one_iff (hR : R ⊆ F) :
    exhOnly F C R X w = 1 ↔ (∀ Y ∈ R, w ∈ only F C Y → X ∈ only F C Y) ∧ w ∈ only F C X := by
  simp [exhOnly_eq_indicator R hR]

theorem exhOnly_eq_neg_one_iff (hR : R ⊆ F) :
    exhOnly F C R X w = -1 ↔ (∀ Y ∈ R, w ∈ only F C Y → X ∈ only F C Y) ∧ w ∉ only F C X := by
  simp [exhOnly_eq_indicator R hR]

variable (F C) in
/-- The pluralities on which the excludable alternatives of the *only*-sentence are built. -/
def excludable (X : Finset α) : Set (Finset α) := {Y ∈ F | X ∉ only F C Y}

-- (32): the domain of `exh` matters only through its excludable alternatives
theorem exhOnly_inter_excludable (hR : R ⊆ F) :
    exhOnly F C (R ∩ excludable F C X) X = exhOnly F C R X := by
  rw [exhOnly_eq_indicator _ (inter_subset_left.trans hR), exhOnly_eq_indicator R hR]
  congr 1
  ext w
  exact ⟨fun h Y hY hw ↦ by_contra fun hX ↦ hX (h Y ⟨hY, hR hY, hX⟩ hw),
    fun h Y hY ↦ h Y hY.1⟩

-- (13): with the alternatives for everyone but an atom of the prejacent, `exh` presupposes it
theorem forall_mem_only_iff [Fintype α] [DecidableEq α] (hC : C ⊆ F)
    (hsingle : ∀ x ∈ X, {x} ∈ C) (hco : ∀ x ∈ X, Finset.univ.erase x ∈ F) :
    (∀ Y ∈ F, w ∈ only F C Y → X ∈ only F C Y) ↔ X ⊆ w := by
  refine ⟨fun h x hx ↦ by_contra fun hxw ↦ ?_,
    fun hXw Y _ hw ↦ mem_only.2 fun Z hZ hZX ↦ mem_only.1 hw Z hZ (hZX.trans hXw)⟩
  have hw : w ∈ only F C (Finset.univ.erase x) := mem_only.2 fun Z _ hZw ↦
    Finset.subset_erase.2 ⟨Finset.subset_univ Z, fun hxZ ↦ hxw (hZw hxZ)⟩
  exact Finset.notMem_erase x _ (mem_only.1 (h _ (hco x hx) hw) {x} ⟨hC (hsingle x hx),
    hsingle x hx⟩ (Finset.singleton_subset_iff.2 hx) (Finset.mem_singleton_self x))

/-- Without pruning, `exh` over the *only*-sentence presupposes the prejacent, and the sentence is
the entry of [horn-1969] for *only* on the entailment scale, (13). -/
theorem exhOnly_eq_only [Fintype α] [DecidableEq α] (hX : X ∈ C) (hC : C ⊆ F)
    (hsingle : ∀ x ∈ X, {x} ∈ C) (hco : ∀ x ∈ X, Finset.univ.erase x ∈ F) :
    exhOnly F C F X = Focus.Particles.only (· ⊆ ·) (Ici '' C) (Ici X) := by
  rw [Focus.Particles.only_subset_eq (mem_image_of_mem _ hX), exhOnly_eq_indicator F subset_rfl,
    only_eq_excludes hC]
  congr 1
  ext w
  exact forall_mem_only_iff hC hsingle hco

open Classical in
/-- Pruning the domain of `exh` to one alternative outside the domain of *only* leaves the
presupposition that some alternative in the domain of *only* holds, the weak entry of
[horn-1996], (44), (54), (82). -/
theorem exhOnly_singleton_eq (hX : X ∈ C) (hC : C ⊆ F) (hY : Y ∈ F) (h : ∀ Z ∈ C, ¬ Z ⊆ Y) :
    exhOnly F C {Y} X = (⋃₀ (Ici '' C)).indicator
      fun w ↦ SignType.ofProp (w ∈ excludes (Ici '' C) (Ici X)) := by
  rw [exhOnly_eq_indicator _ (singleton_subset_iff.2 hY), only_eq_excludes hC]
  congr 1
  have hXY : X ∉ only F C Y := fun hm ↦ h X hX ((mem_only_of_subset hC).1 hm X hX subset_rfl)
  ext w
  simp only [mem_ofPred_eq, mem_singleton_iff, forall_eq]
  rw [imp_iff_not hXY, mem_only_of_subset hC]
  simp only [not_forall, exists_prop, sUnion_image, mem_iUnion₂, mem_Ici]
  exact ⟨fun ⟨Z, hZ, hZw, _⟩ ↦ ⟨Z, hZ, hZw⟩, fun ⟨Z, hZ, hZw⟩ ↦ ⟨Z, hZ, hZw, h Z hZ⟩⟩

/-! ### The Weakening Constraint -/

variable (F C) in
/-- (56): the domain `R` of `exh` satisfies the Weakening Constraint when every larger domain of
excludable alternatives conveys more after accommodation. -/
def Weakening (X : Finset α) : Prop :=
  ∀ R', R ⊂ R' → R' ⊆ excludable F C X →
    ¬ posSupport (exhOnly F C R X) ⊆ posSupport (exhOnly F C R' X)

theorem posSupport_exhOnly {x : α} (hR : R.Nonempty) (hRE : R ⊆ excludable F C {x}) :
    posSupport (exhOnly F C R {x}) = Ici {x} ∩ only F C {x} := by
  ext w
  rw [mem_posSupport, exhOnly_eq_one_iff R (hRE.trans (sep_subset _ _)), mem_inter_iff]
  refine and_congr_left fun hw ↦ ⟨fun h ↦ by_contra fun hxw ↦ ?_,
    fun hxw Y _ hwY ↦ mem_only.2 fun Z hZ hZx ↦ mem_only.1 hwY Z hZ (hZx.trans hxw)⟩
  obtain ⟨Y, hY⟩ := hR
  refine (hRE hY).2 (h Y hY (mem_only.2 fun Z hZ hZw ↦ ?_))
  obtain rfl | rfl := Finset.subset_singleton_iff.1 (mem_only.1 hw Z hZ hZw)
  exacts [Finset.empty_subset _, absurd hZw hxw]

/-- For an atomic prejacent every nonempty domain of excludable alternatives conveys the same
after accommodation, so the Weakening Constraint admits the full domain alone, (55), (57). -/
theorem weakening_iff {x : α} (hR : R.Nonempty) (hRE : R ⊆ excludable F C {x}) :
    Weakening F C R {x} ↔ R = excludable F C {x} := by
  refine ⟨fun h ↦ by_contra fun hne ↦ h _ (hRE.ssubset_of_ne hne) subset_rfl ?_, ?_⟩
  · rw [posSupport_exhOnly R hR hRE, posSupport_exhOnly _ (hR.mono hRE) subset_rfl]
  · rintro rfl R' hlt hR'
    exact absurd (hlt.trans_subset hR') (ssubset_irrefl _)

end Distributed

/-! ### Exceptives -/

section Exceptive

variable {α : Type*} {F : Set (Finset α)} {A X w : Finset α}

open Quantifier Quantifier.Det

/-- (103b), (109): the determiner `Q` over the restrictor `A` minus the excepted plurality `X`. -/
def but (Q : Det α) (A X : Finset α) : Set (Finset α) := {w | Q (↑A \ ↑X) ↑w}

-- (102): *no `A` but `X`* is *only* over the pluralities within the restrictor
theorem but_no_eq_only (hF : ∀ a ∈ A, {a} ∈ F) : but no A X = only F {Z ∈ F | Z ⊆ A} X := by
  ext w
  rw [mem_only_of_subset (sep_subset _ _)]
  simp only [but, mem_ofPred_eq, no, and_imp]
  exact ⟨fun h Z _ hZA hZw a ha ↦ by_contra fun haX ↦ h ⟨hZA ha, haX⟩ (hZw ha),
    fun h a ⟨haA, haX⟩ haw ↦ haX (h {a} (hF a haA) (Finset.singleton_subset_iff.2 haA)
      (Finset.singleton_subset_iff.2 haw) (Finset.mem_singleton_self a))⟩

/-- Without pruning, `exh` over *no `A` but `X`* is true exactly where `X` is the exception set of
[von-fintel-1993], given that `X` lies within the restrictor, (102)–(106), (114). -/
theorem pex_but_no_eq_one_iff [Fintype α] [DecidableEq α]
    (hF : ∀ Z : Finset α, Z.Nonempty → Z ∈ F) (hXA : X ⊆ A)
    (hco : ∀ x ∈ X, (Finset.univ.erase x).Nonempty) :
    pex F F (but no A) X w = 1 ↔ Exceptive.IsExceptionSet no (A : Set α) X w := by
  have hsingle : ∀ x ∈ X, {x} ∈ {Z ∈ F | Z ⊆ A} := fun x hx ↦
    ⟨hF _ (Finset.singleton_nonempty x), Finset.singleton_subset_iff.2 (hXA hx)⟩
  rw [show but no A = only F {Z ∈ F | Z ⊆ A} from funext fun _ ↦
    but_no_eq_only fun a _ ↦ hF _ (Finset.singleton_nonempty a)]
  change exhOnly F {Z ∈ F | Z ⊆ A} F X w = 1 ↔ _
  rw [exhOnly_eq_one_iff F subset_rfl, forall_mem_only_iff (sep_subset _ _) hsingle
    fun x hx ↦ hF _ (hco x hx), mem_only_of_subset (sep_subset _ _),
    Exceptive.isExceptionSet_no_iff, Set.ext_iff]
  simp only [Set.inf_eq_inter, Set.mem_inter_iff, Finset.mem_coe, mem_sep_iff]
  refine ⟨fun ⟨hXw, h⟩ a ↦ ⟨fun ⟨haA, haw⟩ ↦ h {a} ⟨hF _ (Finset.singleton_nonempty a),
      Finset.singleton_subset_iff.2 haA⟩ (Finset.singleton_subset_iff.2 haw)
      (Finset.mem_singleton_self a), fun haX ↦ ⟨hXA haX, hXw haX⟩⟩,
    fun h ↦ ⟨fun a ha ↦ ((h a).2 ha).2, fun Z ⟨_, hZA⟩ hZw a ha ↦ (h a).1 ⟨hZA ha, hZw ha⟩⟩⟩

section Someone

variable [Fintype α] [DecidableEq α] {g : α}

theorem but_some_univ_erase : but Det.some Finset.univ (Finset.univ.erase g) = Ici {g} := by
  ext w
  refine ⟨fun ⟨x, ⟨_, hx⟩, hxw⟩ ↦ ?_, fun hg ↦ ⟨g, ⟨Finset.mem_univ g, by simp⟩,
    hg (Finset.mem_singleton_self g)⟩⟩
  rw [show x = g by simpa using hx] at hxw
  exact Finset.singleton_subset_iff.2 hxw

-- (110b) with the plural alternatives of (12): *someone but everyone except `g`* is excludable
theorem isInnocentlyExcludable_but_some (hF : Finset.univ.erase g ∈ F) :
    IsInnocentlyExcludable (but Det.some Finset.univ '' F) (but Det.some Finset.univ {g})
      (Ici {g}) := by
  have ha : Ici {g} ∈ but Det.some Finset.univ '' F := ⟨_, hF, but_some_univ_erase⟩
  rw [isInnocentlyExcludable_iff_exhMW_subset_compl _ _ _ ha]
  rintro u ⟨hu, hmin⟩ hgu
  refine hmin ⟨u.erase g, ?_, fun q hq hqv ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨x, ⟨-, hx⟩, hxu⟩ := hu
    exact ⟨x, ⟨Finset.mem_univ x, hx⟩,
      Finset.mem_erase.2 ⟨fun h ↦ hx (h ▸ Finset.mem_singleton_self g), hxu⟩⟩
  · obtain ⟨X, -, rfl⟩ := hq
    obtain ⟨x, hx, hxv⟩ := hqv
    exact ⟨x, hx, Finset.mem_of_mem_erase hxv⟩
  · exact Finset.notMem_erase g u (h _ ha hgu (Finset.mem_singleton_self g))

theorem exhIE_but_some_ne {a : α} (hag : a ≠ g) (hF : Finset.univ.erase g ∈ F) :
    exhIE (but Det.some Finset.univ '' F) (but Det.some Finset.univ {g}) ≠
      but Det.some Finset.univ {g} := by
  intro h
  have hw : ({g, a} : Finset α) ∈ but Det.some Finset.univ {g} :=
    ⟨a, ⟨Finset.mem_univ a, by simpa using hag⟩, by simp⟩
  exact (isInnocentlyExcludable_but_some hF).exhIE_subset_compl (h.ge hw) (by simp)

end Someone

end Exceptive

/-! ### The party -/

section Party

/-- The guests of (1) and (50). -/
inductive Guest
  | gal | tal | sal | charlie
  deriving DecidableEq, Fintype

open Guest

/-- The focus alternatives to *Gal*, every plurality of guests ([rooth-1992]). -/
def party : Set (Finset Guest) := {X | X.Nonempty}

/-- (50a): the domain of *only*, the singular alternatives for Gal, Tal and Sal. -/
def partyOnly : Set (Finset Guest) := {{gal}, {tal}, {sal}}

theorem partyOnly_subset : partyOnly ⊆ party := by
  rintro _ (rfl | rfl | rfl) <;> exact Finset.singleton_nonempty _

-- (6b): *Gal and Tal were at the party* is excludable
theorem isInnocentlyExcludable_galTal :
    IsInnocentlyExcludable (Ici '' party) (Ici {gal}) (Ici {gal, tal}) :=
  (isInnocentlyExcludable_Ici_iff (Finset.insert_nonempty _ _)).2 (by decide)

-- (1), (13)
theorem exhOnly_gal : exhOnly party partyOnly party {gal} =
    Focus.Particles.only (· ⊆ ·) (Ici '' partyOnly) (Ici {gal}) :=
  exhOnly_eq_only (by simp [partyOnly]) partyOnly_subset (by simp [partyOnly])
    (by simp only [Finset.mem_singleton, forall_eq]; exact ⟨tal, by decide⟩)

-- (50)–(54)
open Classical in
theorem exhOnly_charlie : exhOnly party partyOnly {{charlie}} {gal} =
    (⋃₀ (Ici '' partyOnly)).indicator
      fun w ↦ SignType.ofProp (w ∈ excludes (Ici '' partyOnly) (Ici {gal})) :=
  exhOnly_singleton_eq (by simp [partyOnly]) partyOnly_subset (Finset.singleton_nonempty _)
    (by rintro _ (rfl | rfl | rfl) <;> decide)

theorem mem_excludable_party {Y : Finset Guest} :
    Y ∈ excludable party partyOnly {gal} ↔ Y.Nonempty ∧ gal ∉ Y := by
  rw [excludable, mem_sep_iff, mem_only_of_subset partyOnly_subset]
  simp [partyOnly, party]

-- Table 1, (48), (57)
theorem table_1 :
    Presupposition.PostAccommodationInformative univ (exhOnly party partyOnly party {gal}) ∧
    Weakening party partyOnly (excludable party partyOnly {gal}) {gal} ∧
    ¬ Weakening party partyOnly {{charlie}} {gal} := by
  have hE : {tal} ∈ excludable party partyOnly {gal} := mem_excludable_party.2 (by decide)
  have hC : {charlie} ∈ excludable party partyOnly {gal} := mem_excludable_party.2 (by decide)
  refine ⟨Presupposition.postAccommodationInformative_iff.2 ⟨{gal, tal}, mem_univ _, ?_⟩,
    (weakening_iff _ ⟨_, hE⟩ subset_rfl).2 rfl, fun h ↦ ?_⟩
  · rw [exhOnly_gal, Focus.Particles.only_eq_neg_one_iff]
    simp [partyOnly]
  · have := ((weakening_iff _ (singleton_nonempty _) (singleton_subset_iff.2 hC)).1 h).ge hE
    simp at this

-- (107)–(110)
theorem judgment_107 : Examples.ex_107.judgment = .unacceptable ∧
    exhIE (but Quantifier.Det.some Finset.univ '' party)
        (but Quantifier.Det.some Finset.univ {gal}) ≠
      but Quantifier.Det.some Finset.univ {gal} :=
  ⟨rfl, exhIE_but_some_ne (a := tal) (by decide) ⟨tal, by decide⟩⟩

end Party

/-! ### The academic ladder -/

section Ladder

/-- The ranks of (36): grad student, postdoc, professor and non-academic. -/
inductive Rank
  | grad | postdoc | professor | nonAcademic
  deriving DecidableEq, Fintype

open Rank

/-- (36a): the focus alternatives to *grad student*. -/
def ranks : Set (Finset Rank) := {{grad}, {postdoc}, {professor}, {nonAcademic}}

/-- (41a): the domain of *only*, the academic ladder. -/
def ladder : Set (Finset Rank) := {{grad}, {postdoc}, {professor}}

/-- Gal holds at most one rank. -/
def oneRank : Set (Finset Rank) := {w | w.card ≤ 1}

instance : DecidablePred (· ∈ oneRank) := fun w ↦ inferInstanceAs (Decidable (w.card ≤ 1))

theorem mem_ranks {Y : Finset Rank} :
    Y ∈ ranks ↔ Y = {grad} ∨ Y = {postdoc} ∨ Y = {professor} ∨ Y = {nonAcademic} := Iff.rfl

theorem singleton_subset_ranks (r : Rank) : {{r}} ⊆ ranks :=
  singleton_subset_iff.2 (by cases r <;> simp [mem_ranks])

theorem ladder_subset : ladder ⊆ ranks := by
  rintro _ (rfl | rfl | rfl) <;> simp [ranks]

theorem mem_only_ladder {X w : Finset Rank} : w ∈ only ranks ladder X ↔
    (grad ∈ w → grad ∈ X) ∧ (postdoc ∈ w → postdoc ∈ X) ∧ (professor ∈ w → professor ∈ X) := by
  rw [mem_only_of_subset ladder_subset]
  simp [ladder]

theorem excludable_ranks :
    excludable ranks ladder {grad} = {{postdoc}, {professor}, {nonAcademic}} := by
  ext Y
  rw [excludable, mem_sep_iff, mem_only_ladder]
  simp only [ranks, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨rfl | rfl | rfl | rfl, h⟩ <;> simp_all
  · rintro (rfl | rfl | rfl) <;> simp

/-- Table 2: for *Gal is only a grad student*, the presupposition of the unpruned domain entails the
assertion, (39), (40), while pruning to *only [non-academic]* leaves the presupposition that Gal is
an academic, which does not, at the cost of the Weakening Constraint, (41)–(44). -/
theorem table_2 :
    ¬ Presupposition.PostAccommodationInformative oneRank (exhOnly ranks ladder ranks {grad}) ∧
    Presupposition.PostAccommodationInformative oneRank
      (exhOnly ranks ladder {{nonAcademic}} {grad}) ∧
    ¬ Weakening ranks ladder {{nonAcademic}} {grad} := by
  refine ⟨?_, ?_, fun h ↦ ?_⟩
  · rw [Presupposition.postAccommodationInformative_iff]
    simp [exhOnly_eq_neg_one_iff _ subset_rfl, mem_only_ladder, mem_ranks, oneRank]
    decide
  · rw [Presupposition.postAccommodationInformative_iff]
    simp [exhOnly_eq_neg_one_iff _ (singleton_subset_ranks _), mem_only_ladder, oneRank]
    decide
  · have := ((weakening_iff _ (singleton_nonempty _) (by simp [excludable_ranks])).1 h).ge
      (show {postdoc} ∈ excludable ranks ladder {grad} by simp [excludable_ranks])
    simp at this

-- Pruning to *only [postdoc]* satisfies and violates the constraints (41) does, and under negation
-- conveys that Gal is a professor where (41) conveys that she is a postdoc or a professor
theorem pruned_postdoc :
    Presupposition.PostAccommodationInformative oneRank
      (exhOnly ranks ladder {{postdoc}} {grad}) ∧
    ¬ Weakening ranks ladder {{postdoc}} {grad} ∧ ∀ w ∈ oneRank,
      (-exhOnly ranks ladder {{nonAcademic}} {grad} w = 1 ↔ w = {postdoc} ∨ w = {professor}) ∧
      (-exhOnly ranks ladder {{postdoc}} {grad} w = 1 ↔ w = {professor}) := by
  refine ⟨?_, fun h ↦ ?_, ?_⟩
  · rw [Presupposition.postAccommodationInformative_iff]
    simp [exhOnly_eq_neg_one_iff _ (singleton_subset_ranks _), mem_only_ladder, oneRank]
    decide
  · have := ((weakening_iff _ (singleton_nonempty _) (by simp [excludable_ranks])).1 h).ge
      (show {nonAcademic} ∈ excludable ranks ladder {grad} by simp [excludable_ranks])
    simp at this
  · simp [neg_eq_iff_eq_neg, exhOnly_eq_neg_one_iff _ (singleton_subset_ranks _), mem_only_ladder,
      oneRank]
    decide

/-! ### Relevance closed under the Boolean operations -/

/-- The *only*-alternatives of (37), restricted to the context. -/
def onlyCtx (r : Rank) : Set oneRank := Subtype.val ⁻¹' only ranks ladder {r}

@[simp] theorem mem_onlyCtx {r : Rank} {w : oneRank} :
    w ∈ onlyCtx r ↔ (grad ∈ w.1 → grad = r) ∧ (postdoc ∈ w.1 → postdoc = r) ∧
      (professor ∈ w.1 → professor = r) := by
  simp [onlyCtx, mem_only_ladder]

theorem onlyCtx_subset_onlyCtx_iff {q r : Rank} :
    onlyCtx q ⊆ onlyCtx r ↔ q = r ∨ q = nonAcademic := by
  rw [Set.subset_def]
  simp only [mem_onlyCtx]
  cases q <;> cases r <;> decide

theorem onlyCtx_injective : Function.Injective onlyCtx := fun q r h ↦ by
  have hq := onlyCtx_subset_onlyCtx_iff.1 h.le
  have hr := onlyCtx_subset_onlyCtx_iff.1 h.ge
  grind

theorem onlyCtx_nonAcademic_eq_inter {r : Rank} (hr : r = postdoc ∨ r = professor) :
    onlyCtx nonAcademic = onlyCtx grad ∩ onlyCtx r := by
  ext w
  obtain rfl | rfl := hr <;> simp only [mem_onlyCtx, mem_inter_iff] <;> revert w <;> decide

theorem exh_onlyCtx_eq_compl {q r : Rank} (h : [q, r] = [postdoc, professor] ∨
    [q, r] = [professor, postdoc]) :
    exh (onlyCtx '' {grad, nonAcademic, r}) (onlyCtx q) =
      (onlyCtx grad ∪ onlyCtx nonAcademic ∪ onlyCtx r)ᶜ := by
  ext w
  obtain h | h := h <;> simp only [List.cons.injEq, and_true] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    simp [onlyCtx_subset_onlyCtx_iff] <;> revert w <;> decide

theorem not_exhaustivelyRelevant_onlyCtx {q : Rank} (hq : q = postdoc ∨ q = professor) :
    ¬ Alternatives.ExhaustivelyRelevant (onlyCtx '' {grad, nonAcademic}) (onlyCtx q) := by
  obtain rfl | rfl := hq
  · refine Alternatives.not_exhaustivelyRelevant_of_separates (u := ⟨{postdoc}, by decide⟩)
      (v := ⟨{professor}, by decide⟩) ?_ ?_ ?_ <;>
      simp [mem_exh, onlyCtx_subset_onlyCtx_iff]
  · refine Alternatives.not_exhaustivelyRelevant_of_separates (u := ⟨{professor}, by decide⟩)
      (v := ⟨{postdoc}, by decide⟩) ?_ ?_ ?_ <;>
      simp [mem_exh, onlyCtx_subset_onlyCtx_iff]

-- fn. 3: over the context, of the informative prunings of (35) only (41) is allowable
theorem isAllowableRestriction_onlyCtx_iff {R : Set Rank}
    (hR : R = {nonAcademic} ∨ R = {postdoc} ∨ R = {professor} ∨ R = {nonAcademic, postdoc} ∨
      R = {nonAcademic, professor}) :
    Alternatives.IsAllowableRestriction (range onlyCtx) (onlyCtx '' insert grad R)
      (onlyCtx grad) ↔ R = {nonAcademic} := by
  open Alternatives BooleanSubalgebra in
  have hER (q : Rank) (hq : q ∉ insert grad R)
      (h : ExhaustivelyRelevant (onlyCtx '' insert grad R) (onlyCtx q)) :
      ¬ IsAllowableRestriction (range onlyCtx) (onlyCtx '' insert grad R) (onlyCtx grad) :=
    fun hA ↦ hA.2 _ ⟨⟨q, rfl⟩, by rwa [onlyCtx_injective.mem_set_image]⟩ h
  have hna (r : Rank) (hr : r = postdoc ∨ r = professor) :
      ExhaustivelyRelevant (onlyCtx '' {grad, r}) (onlyCtx nonAcademic) := by
    have hexh : exh (onlyCtx '' {grad, r}) (onlyCtx nonAcademic) = onlyCtx nonAcademic :=
      exh_eq_self (by rintro _ ⟨q, -, rfl⟩; exact onlyCtx_subset_onlyCtx_iff.2 (.inr rfl))
    rw [ExhaustivelyRelevant, hexh, onlyCtx_nonAcademic_eq_inter hr]
    change onlyCtx grad ⊓ onlyCtx r ∈ _
    exact inf_mem (subset_closure (mem_image_of_mem _ (by simp)))
      (subset_closure (mem_image_of_mem _ (by simp)))
  have hcompl (q r : Rank) (h : [q, r] = [postdoc, professor] ∨ [q, r] = [professor, postdoc]) :
      ExhaustivelyRelevant (onlyCtx '' {grad, nonAcademic, r}) (onlyCtx q) := by
    rw [ExhaustivelyRelevant, exh_onlyCtx_eq_compl h]
    change (onlyCtx grad ⊔ onlyCtx nonAcademic ⊔ onlyCtx r)ᶜ ∈ _
    have hmem (r' : Rank) (h : r' ∈ ({grad, nonAcademic, r} : Set Rank)) :
        onlyCtx r' ∈ closure (onlyCtx '' {grad, nonAcademic, r}) :=
      subset_closure (mem_image_of_mem _ h)
    exact compl_mem (sup_mem (sup_mem (hmem _ (by simp)) (hmem _ (by simp))) (hmem _ (by simp)))
  rcases hR with rfl | rfl | rfl | rfl | rfl
  · refine iff_of_true ⟨mem_image_of_mem _ (mem_insert _ _), ?_⟩ rfl
    rintro _ ⟨⟨q, rfl⟩, hq⟩
    rw [onlyCtx_injective.mem_set_image] at hq
    exact not_exhaustivelyRelevant_onlyCtx (by cases q <;> simp_all)
  · exact iff_of_false (hER nonAcademic (by simp) (hna postdoc (.inl rfl))) (by simp)
  · exact iff_of_false (hER nonAcademic (by simp) (hna professor (.inr rfl))) (by simp)
  · refine iff_of_false (hER professor (by simp) (hcompl professor postdoc (.inr rfl))) ?_
    intro h
    have := h.subset (show postdoc ∈ ({nonAcademic, postdoc} : Set Rank) by simp)
    simp at this
  · refine iff_of_false (hER postdoc (by simp) (hcompl postdoc professor (.inl rfl))) ?_
    intro h
    have := h.subset (show professor ∈ ({nonAcademic, professor} : Set Rank) by simp)
    simp at this

theorem only_ladder_subset_iff {q r : Rank} :
    only ranks ladder {q} ⊆ only ranks ladder {r} ↔ q = r ∨ q = nonAcademic := by
  rw [Set.subset_def]
  simp only [mem_only_ladder, Finset.mem_singleton]
  cases q <;> cases r <;> decide

-- over all worlds, the closure also admits pruning to *only [non-academic]* and *only [postdoc]*
theorem isAllowableRestriction_only_ranks :
    Alternatives.IsAllowableRestriction (range fun r ↦ only ranks ladder {r})
      ((fun r ↦ only ranks ladder {r}) '' {grad, nonAcademic, postdoc})
      (only ranks ladder {grad}) := by
  refine ⟨mem_image_of_mem _ (by simp), ?_⟩
  rintro _ ⟨⟨q, rfl⟩, hq⟩
  have hinj : Function.Injective fun r : Rank ↦ only ranks ladder {r} := fun q r h ↦ by
    have hq := only_ladder_subset_iff.1 h.le
    have hr := only_ladder_subset_iff.1 h.ge
    grind
  rw [hinj.mem_set_image] at hq
  obtain rfl : q = professor := by cases q <;> simp_all
  refine Alternatives.not_exhaustivelyRelevant_of_separates (u := {professor})
    (v := {grad, postdoc}) ?_ ?_ ?_ <;>
    simp [mem_exh, only_ladder_subset_iff, mem_only_ladder]

end Ladder
