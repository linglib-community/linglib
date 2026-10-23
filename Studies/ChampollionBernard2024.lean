module

public import Linglib.Logic.Truthmaker.Exclusion
public import Mathlib.Tactic.FinCases

/-!
# Champollion and Bernard (2024): Negation and modality in unilateral truthmaker semantics

Champollion and Bernard give a unilateral truthmaker semantics in which negation comes from a
primitive exclusion relation between events rather than from a second set of falsifiers. Two
events conflict when a part of one excludes a part of the other (`Truthmaker.Conflict`), and an
event is possible when it does not conflict with itself (`Truthmaker.possible`, Lemma 4.1), so
possibility, which Fine takes as primitive, is derived. The worlds are the maximal possible
events. Under the axioms of Harmony and Rashōmon, the latter Plebani, Rosella and Saitta's
Possible Fusion, a world conflicts with every event it does not contain (`conflict_of_not_le`,
Theorem 8.4). An event verifies the negation of `φ` when it fuses, for each verifier of `φ`, an
event excluding a part of that verifier (`neg`). Every world then contains a verifier of exactly
one of `φ` and its negation (`mem_upperClosure_neg_iff`, Theorems 9.2–9.4), so `φ` paired with its
negation is exclusive and exhaustive in Fine's sense (`exclusive_mk_neg`, `exhaustive_mk_neg`).

The paper departs from Fine in admitting emergent exclusion, where an event excludes the fusion of
two events without conflicting with either. Such an event verifies `¬(P ∧ Q)` but not `¬P ∨ ¬Q`
(`mem_neg_sups_diff`), as the third egg's being in a basket with room for two does
(`eggs_mem_neg_sups_diff`). The two sides of de Morgan's law still hold at the same worlds
(`mem_upperClosure_neg_sups_iff`). Emergent exclusion is exactly the failure of a state that
conflicts with a fusion to conflict with one of its members
(`Truthmaker.forall_exists_conflict_iff`). Fine's Downward Exclusion rules it out
(`Truthmaker.DownwardExclusion.exists_conflict`), and under it his negation obeys the law exactly
(`Truthmaker.exclusionaryNeg_iSups`). Under Fine's Upward Exclusion the paper's negation is
contained in Fine's exclusive negation (`neg_subset_exclusiveNeg`), Rashōmon is Fine's second
condition on classical exclusion (`possibleFusion_iff_exists_le_excl`), and the paper's axioms make
exclusion classical (`classicalExclusion_possible`). Cumulativity of exclusion adds the further
verifiers of `¬(P ∧ Q)` that Ciardelli, Zhang and Champollion's counterfactual data call for
(`neg_sups_neg_subset`). In the canonical frame a literal excludes its mirror image. There the
derived possibility is Fine's consistency (`Truthmaker.Canonical.possible_excl`), negation recovers
Fine's falsifiers (`neg_ver_atom`, `neg_ver_conj_atom`), and the axioms hold.

## Implementation notes

The paper takes events to form a complete distributive lattice. No proof here uses
distributivity. Symmetry of exclusion is needed only for Plenitude, which the paper states with
the event before the world while Harmony puts the world first. The paper's paraphrase of Fine's
third condition on classical exclusion speaks of a possible state where Fine has an impossible
one. Occurrence (Theorems 8.1–8.2), the definitions of necessity, and the results about a formula
language (Theorems 9.8–9.9) are not formalized.

## References

* [L. Champollion and T. Bernard, *Negation and modality in unilateral truthmaker semantics*
  (2024)][champollion-bernard-2024]
* [K. Fine, *A Theory of Truthmaker Content I: Conjunction, Disjunction and Negation*
  (2017)][fine-2017a]
* [M. Plebani, G. Rosella and V. Saitta, *Truthmakers, Incompatibility, and Modality*
  (2022)][plebani-rosella-saitta-2022]
* [I. Ciardelli, L. Zhang and L. Champollion, *Two switches in the theory of counterfactuals: A
  study of truth conditionality and minimal change* (2018)][ciardelli-zhang-champollion-2018]
-/

@[expose] public section

open SetFamily Truthmaker

namespace ChampollionBernard2024

variable {E : Type*} [CompleteLattice E] {excl : E → E → Prop}

/-! ### Worlds and the axioms on exclusion -/

variable (excl) in
/-- Cosmopolitanism (axiom 19), Fine's W-space condition, holds when every possible event is part
of a world, a maximal possible event. -/
def Cosmopolitan : Prop :=
  ∀ e ∈ possible excl, ∃ w, e ≤ w ∧ Maximal (· ∈ possible excl) w

variable (excl) in
/-- Harmony (axiom 20) holds when every event that coheres with a world is possible. -/
def Harmony : Prop :=
  ∀ ⦃w e : E⦄, Maximal (· ∈ possible excl) w → ¬ Conflict excl w e → e ∈ possible excl

/-- An event is possible exactly when it coheres with some world (Theorem 8.3). -/
theorem mem_possible_iff_exists_world [Std.Symm excl] (hC : Cosmopolitan excl)
    (hH : Harmony excl) {e : E} :
    e ∈ possible excl ↔ ∃ w, ¬ Conflict excl e w ∧ Maximal (· ∈ possible excl) w := by
  refine ⟨fun he ↦ ?_, fun ⟨w, hc, hw⟩ ↦ hH hw fun h ↦ hc h.symm⟩
  obtain ⟨w, hew, hw⟩ := hC e he
  exact ⟨w, fun hc ↦ hw.prop (hc.mono hew le_rfl), hw⟩

/-- A world conflicts with every event it does not contain (Theorem 8.4). -/
theorem conflict_of_not_le (hH : Harmony excl) (hR : PossibleFusion excl) {w e : E}
    (hw : Maximal (· ∈ possible excl) w) (he : ¬ e ≤ w) : Conflict excl w e := by
  by_contra hc
  exact he (le_sup_right.trans (hw.le_of_ge (hR hw.prop (hH hw hc) hc) le_sup_left))

/-! ### Negation -/

variable (excl) in
/-- An event verifies the negation of `φ` when it is the fusion of the values of a function
sending each verifier of `φ` to an event that excludes some part of it (defs. 28–29). -/
def neg (φ : Set E) : Set E :=
  {e | ∃ h : E → E, (∀ f ∈ φ, ∃ g ≤ f, excl (h f) g) ∧ sSup (h '' φ) = e}

theorem neg_singleton (f : E) : neg excl {f} = {e | ∃ g ≤ f, excl e g} := by
  ext e
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [Set.image_singleton, sSup_singleton]
    exact hh f rfl
  · intro hg
    exact ⟨fun _ ↦ e, fun f' hf' ↦ Set.mem_singleton_iff.1 hf' ▸ hg, by simp⟩

/-- No possible event contains both a verifier of `φ` and a verifier of its negation. The paper
states this for worlds (Theorem 9.4). -/
theorem not_mem_upperClosure_neg {φ : Set E} {s : E} (hs : s ∈ possible excl)
    (hφ : s ∈ upperClosure φ) : s ∉ upperClosure (neg excl φ) := by
  intro hn
  obtain ⟨_, ⟨h, hh, rfl⟩, hle⟩ := mem_upperClosure.1 hn
  obtain ⟨f, hf, hfs⟩ := mem_upperClosure.1 hφ
  obtain ⟨g, hgf, hx⟩ := hh f hf
  exact hs ⟨h f, (le_sSup (Set.mem_image_of_mem h hf)).trans hle, g, hgf.trans hfs, hx⟩

/-- Every world contains a verifier of `φ` or a verifier of its negation (Theorem 9.3). -/
theorem mem_upperClosure_or_neg (hH : Harmony excl) (hR : PossibleFusion excl) {w : E}
    (hw : Maximal (· ∈ possible excl) w) (φ : Set E) :
    w ∈ upperClosure φ ∨ w ∈ upperClosure (neg excl φ) := by
  refine or_iff_not_imp_left.2 fun hφ ↦ ?_
  have : ∀ f, ∃ e, f ∈ φ → e ≤ w ∧ ∃ g ≤ f, excl e g := fun f ↦ by
    by_cases hf : f ∈ φ
    · obtain ⟨e, hew, g, hgf, hx⟩ :=
        conflict_of_not_le hH hR hw fun hfw ↦ hφ (mem_upperClosure.2 ⟨f, hf, hfw⟩)
      exact ⟨e, fun _ ↦ ⟨hew, g, hgf, hx⟩⟩
    · exact ⟨⊥, fun h ↦ absurd h hf⟩
  choose h hh using this
  exact mem_upperClosure.2 ⟨sSup (h '' φ), ⟨h, fun f hf ↦ (hh f hf).2, rfl⟩,
    sSup_le (Set.forall_mem_image.2 fun f hf ↦ (hh f hf).1)⟩

/-- A world contains a verifier of the negation of `φ` exactly when it contains no verifier of
`φ` (Theorem 9.2). -/
theorem mem_upperClosure_neg_iff (hH : Harmony excl) (hR : PossibleFusion excl) {w : E}
    (hw : Maximal (· ∈ possible excl) w) {φ : Set E} :
    w ∈ upperClosure (neg excl φ) ↔ w ∉ upperClosure φ :=
  ⟨fun hn hφ ↦ not_mem_upperClosure_neg hw.prop hφ hn,
    (mem_upperClosure_or_neg hH hR hw φ).resolve_left⟩

theorem exclusive_mk_neg (φ : Set E) : (BilProp.mk φ (neg excl φ)).Exclusive (possible excl) :=
  BilProp.exclusive_iff.2 fun _ hs hφ ↦ not_mem_upperClosure_neg hs hφ

theorem exhaustive_mk_neg (hC : Cosmopolitan excl) (hH : Harmony excl) (hR : PossibleFusion excl)
    (φ : Set E) : (BilProp.mk φ (neg excl φ)).Exhaustive (possible excl) :=
  (BilProp.exhaustive_iff hC).2 fun _ hw ↦ mem_upperClosure_or_neg hH hR hw φ

/-! ### Emergent exclusion and de Morgan's law -/

theorem not_mem_regularClosure_excluders {P : Set E} {s : E}
    (hc : ∀ p ∈ P, ¬ Conflict excl s p) : s ∉ regularClosure {r | ∃ p ∈ P, excl r p} :=
  fun ⟨hs, _⟩ ↦
    let ⟨r, ⟨p, hp, hx⟩, hrs⟩ := mem_upperClosure.1 hs
    hc p hp ⟨r, hrs, p, le_rfl, hx⟩

/-- An event that excludes `p ⊔ q` while cohering with `p` and with `q` verifies `¬(P ∧ Q)` but not
`¬P ∨ ¬Q`, where `P` is verified by `p` alone and `Q` by `q` alone (§7). -/
theorem mem_neg_sups_diff {p q s : E} (hs : excl s (p ⊔ q)) (hp : ¬ Conflict excl s p)
    (hq : ¬ Conflict excl s q) : s ∈ neg excl ({p} ⊻ {q}) \ (neg excl {p} ∪ neg excl {q}) := by
  rw [Set.singleton_sups_singleton, neg_singleton, neg_singleton, neg_singleton]
  refine ⟨⟨p ⊔ q, le_rfl, hs⟩, ?_⟩
  rintro (⟨g, hg, hx⟩ | ⟨g, hg, hx⟩)
  · exact hp ⟨s, le_rfl, g, hg, hx⟩
  · exact hq ⟨s, le_rfl, g, hg, hx⟩

/-- The two sides of de Morgan's law `¬(φ ∧ ψ) ⇔ ¬φ ∨ ¬ψ` hold at the same worlds (§9). -/
theorem mem_upperClosure_neg_sups_iff (hH : Harmony excl) (hR : PossibleFusion excl) {w : E}
    (hw : Maximal (· ∈ possible excl) w) (φ ψ : Set E) :
    w ∈ upperClosure (neg excl (φ ⊻ ψ)) ↔ w ∈ upperClosure (neg excl φ ∪ neg excl ψ) := by
  rw [upperClosure_union, UpperSet.mem_inf_iff, mem_upperClosure_neg_iff hH hR hw,
    mem_upperClosure_neg_iff hH hR hw, mem_upperClosure_neg_iff hH hR hw, upperClosure_sups,
    UpperSet.mem_sup_iff, not_and_or]

/-- If exclusion is cumulative, the fusion of a verifier of `¬P` with a verifier of `¬Q` verifies
`¬(P ∧ Q)`, for `P` verified by `p` alone and `Q` by `q` alone (§8, fn. 27). -/
theorem neg_sups_neg_subset
    (hCum : ∀ ⦃e e' f f' : E⦄, excl e e' → excl f f' → excl (e ⊔ f) (e' ⊔ f')) (p q : E) :
    neg excl {p} ⊻ neg excl {q} ⊆ neg excl ({p} ⊻ {q}) := by
  rw [Set.singleton_sups_singleton, neg_singleton, neg_singleton, neg_singleton]
  rintro _ ⟨e, ⟨g, hgp, he⟩, f, ⟨g', hgq, hf⟩, rfl⟩
  exact ⟨g ⊔ g', sup_le_sup hgp hgq, hCum he hf⟩

/-! ### Comparison with Fine's unilateral semantics -/

theorem neg_subset_exclusiveNeg (hU : UpwardExclusion excl) (φ : Set E) :
    neg excl φ ⊆ exclusiveNeg excl φ := by
  rintro _ ⟨h, hh, rfl⟩
  exact sSup_image_mem_exclusiveNeg fun f hf ↦
    let ⟨_, hgf, hx⟩ := hh f hf
    hU hx hgf

/- Fine's exclusive negation also admits the fusion of two excluders of one verifier. -/
example : ∃ excl : Set (Fin 3) → Set (Fin 3) → Prop, UpwardExclusion excl ∧
    ({0, 1} : Set (Fin 3)) ∈ exclusiveNeg excl {{2}} \ neg excl {{2}} := by
  refine ⟨fun a b ↦ (a = {0} ∨ a = {1}) ∧ 2 ∈ b, fun _ _ _ ⟨ha, hb⟩ hle ↦ ⟨ha, hle hb⟩,
    ⟨{{0}, {1}}, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro _ (rfl | rfl)
    · exact ⟨{2}, rfl, .inl rfl, rfl⟩
    · exact ⟨{2}, rfl, .inr rfl, rfl⟩
  · rintro _ rfl
    exact ⟨{0}, .inl rfl, .inl rfl, rfl⟩
  · rw [sSup_pair]
    ext x
    simp [or_comm]
  · rw [neg_singleton]
    rintro ⟨g, _, h | h, _⟩
    · have := Set.ext_iff.1 h 1
      simp at this
    · have := Set.ext_iff.1 h 0
      simp at this

/-- Under Upward Exclusion, Rashōmon is Fine's second condition on classical exclusion over the
derived possibility, that two possible events with an impossible fusion have a part of the first
that excludes the second (fn. 21). -/
theorem possibleFusion_iff_exists_le_excl (hU : UpwardExclusion excl) :
    PossibleFusion excl ↔ ∀ ⦃s t : E⦄, s ∈ possible excl → t ∈ possible excl →
      s ⊔ t ∉ possible excl → ∃ s' ≤ s, excl s' t := by
  refine ⟨fun hR s t hs ht hst ↦ hU.conflict_iff.1 ?_, fun h s hs t ht hc ↦ ?_⟩
  · by_contra hc
    exact hst (hR hs ht hc)
  · by_contra hst
    obtain ⟨s', hs', hx⟩ := h hs ht hst
    exact hc ⟨s', hs', t, le_rfl, hx⟩

theorem classicalExclusion_possible (hU : UpwardExclusion excl) (hC : Cosmopolitan excl)
    (hH : Harmony excl) (hR : PossibleFusion excl) : ClassicalExclusion excl (possible excl) where
  sup_not_mem _ _ := sup_not_mem_possible
  exists_le_excl := (possibleFusion_iff_exists_le_excl hU).1 hR
  exists_excl t ht s hs := by
    obtain ⟨w, hsw, hw⟩ := hC s hs
    obtain ⟨w', hw', hx⟩ := hU.conflict_iff.1 (by_contra fun hc ↦ ht (hH hw hc))
    exact ⟨w', hx, (possible excl).lower (sup_le hsw hw') hw.prop⟩

/-! ### The basket with room for two eggs -/

/-- In a basket with room for two of the eggs `0`, `1` and `2`, the event of egg `i`'s being in
the basket excludes the event of the other two eggs' being in it, and conversely (§6). -/
def eggsExcl (s t : Set (Fin 3)) : Prop :=
  ∃ i, s = {i} ∧ t = {i}ᶜ ∨ s = {i}ᶜ ∧ t = {i}

private theorem compl_singleton_not_subset_singleton (i j : Fin 3) :
    ¬ ({i}ᶜ : Set (Fin 3)) ⊆ {j} := by
  simp only [Set.subset_def, Set.mem_compl_iff, Set.mem_singleton_iff]
  revert i j
  decide

theorem not_conflict_eggsExcl (i j : Fin 3) : ¬ Conflict eggsExcl {i} {j} := by
  rintro ⟨_, h₁, _, h₂, k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact compl_singleton_not_subset_singleton k j h₂
  · exact compl_singleton_not_subset_singleton k i h₁

/-- The third egg's being in the basket verifies *egg 1 and egg 2 are not both in the basket* but
not *either egg 1 or egg 2 is not in the basket* (§7). -/
theorem eggs_mem_neg_sups_diff :
    ({2} : Set (Fin 3)) ∈
      neg eggsExcl ({{0}} ⊻ {{1}}) \ (neg eggsExcl {{0}} ∪ neg eggsExcl {{1}}) :=
  mem_neg_sups_diff ⟨2, .inl ⟨rfl, by ext x; fin_cases x <;> simp⟩⟩ (not_conflict_eggsExcl 2 0)
    (not_conflict_eggsExcl 2 1)

/-! ### The canonical frame -/

section Canonical

open Truthmaker.Canonical

variable {α : Type*}

theorem neg_ver_atom (a : α) : neg Canonical.excl (atom a).ver = (atom a).fal := by
  rw [ver_atom, fal_atom, neg_singleton]
  ext e
  constructor
  · rintro ⟨_, hg, x, rfl, rfl⟩
    obtain rfl : x = (a, false) := by
      simpa using congrArg mirror (Set.singleton_subset_singleton.1 hg)
    rfl
  · rintro rfl
    exact ⟨{(a, true)}, le_rfl, (a, false), rfl, rfl⟩

/-- In the canonical frame the negation of a conjunction of two atoms is verified exactly by the
denial of either atom, its falsifiers in Fine's bilateral semantics, so de Morgan's law holds
exactly there (§9). -/
theorem neg_ver_conj_atom (a b : α) :
    neg Canonical.excl ((atom a).conj (atom b)).ver = ((atom a).conj (atom b)).fal := by
  rw [BilProp.ver_conj, BilProp.fal_conj, ver_atom, ver_atom, fal_atom, fal_atom,
    Set.singleton_sups_singleton, neg_singleton]
  ext e
  constructor
  · rintro ⟨_, hg, x, rfl, rfl⟩
    rcases Set.singleton_subset_iff.1 hg with h | h
    · obtain rfl : x = (a, false) := by
        simpa using congrArg mirror (Set.mem_singleton_iff.1 h)
      exact .inl rfl
    · obtain rfl : x = (b, false) := by
        simpa using congrArg mirror (Set.mem_singleton_iff.1 h)
      exact .inr rfl
  · rintro (rfl | rfl)
    · exact ⟨{(a, true)}, Set.singleton_subset_iff.2 (.inl rfl), (a, false), rfl, rfl⟩
    · exact ⟨{(b, true)}, Set.singleton_subset_iff.2 (.inr rfl), (b, false), rfl, rfl⟩

theorem harmony_canonicalExcl : Harmony (Canonical.excl (α := α)) := by
  intro w e hw hc
  rw [possible_excl] at hw ⊢
  intro x hx hx'
  rcases mem_or_mirror_mem_of_maximal hw x with hxw | hxw
  · exact hc (conflict_excl_iff.2 ⟨x, hxw, hx'⟩)
  · exact hc (conflict_excl_iff.2 ⟨mirror x, hxw, by rwa [mirror_mirror]⟩)

theorem cosmopolitan_canonicalExcl : Cosmopolitan (Canonical.excl (α := α)) := by
  unfold Cosmopolitan
  rw [possible_excl]
  exact fun _ ↦ exists_le_maximal_possible

theorem mk_neg_ver_atom (a : α) :
    BilProp.mk (atom a).ver (neg Canonical.excl (atom a).ver) = atom a := by
  rw [neg_ver_atom]

/- Fine's classicality of the canonical atoms follows from the exclusion axioms. -/
example (a : α) : (atom a).Exclusive Canonical.possible :=
  possible_excl ▸ mk_neg_ver_atom a ▸ exclusive_mk_neg _

example (a : α) : (atom a).Exhaustive Canonical.possible :=
  possible_excl ▸ mk_neg_ver_atom a ▸
    exhaustive_mk_neg cosmopolitan_canonicalExcl harmony_canonicalExcl
      possibleFusion_excl _

end Canonical

end ChampollionBernard2024
